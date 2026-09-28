# PORT-V434 — state during lap 3 (2026-09-28)

`lake build` reached **1597/1599** after the first four W9 fixes (lap start: 1594).
Cleared this lap, each verified by `lake env lean -M 12000 -j 2 <file>` exiting 0:
`ACA/EpsProg`, `ACA/OmegaJumpDepth`, `Ramified/UpperBound`, `ACA/OmegaJumpUpperBound`.

Still open (no `.olean` yet): `Ramified/DescentBetaAux4` (exit 137, W9 in `step2` and
`descentOne`), and behind it `Ramified/{DescentBetaAux5,DescentBetaAux6,DescentBeta,
FefermanSchutte,SemiformalUpper}`, not yet reached.

## The lap-3 finding: **W9 — it is the KERNEL, not the elaborator**

`lake env lean -M 9000 -j 2 --profile OrdinalAnalysis/ACA/EpsProg.lean` turns the silent
exit-137 into named, per-declaration errors and keeps going:

```
OrdinalAnalysis/ACA/EpsProg.lean:1217:8: error: (kernel) excessive memory consumption detected
OrdinalAnalysis/ACA/EpsProg.lean:1694:8: error: (kernel) excessive memory consumption detected
…  elaboration 199ms · tactic execution 9.48s · type checking 33.7s
```

So the file **elaborates fine**; two declarations (`goodAllTI`, `epsProg`) blow up in kernel
type checking, and they still blow at `-M 15000`.  This is a *different* family from
W5b/W7 (diverging `simp`), and truncation-bisect is the wrong tool for it — `-M` localises
every offender in one run.

### Root cause, pinned by bisecting the split

After lifting each `have` of `goodAllTI` to a `private theorem`, the surviving offender was

```lean
private theorem goodAllTI_branchB : PSeq ACA [∼(goodBSO (&0) (&1)), allTI (&0), ∼(belowPsi (&1))] :=
  goodAllTI_hall2          -- >10 GB, in the kernel, on this ONE defeq
```

i.e. a **single defeq** `∼(goodBSO s g) ≟ ∀¹∀¹ (goodBNegBody …)`.  `Semiformula.neg` is a
structural recursion, so the kernel (which has no `smartUnfolding`/equation lemmas — it
reduces `brecOn` directly) pushes `∼` *through the whole concrete coded formula*
(`precSOv`/`baseSO`/`epsSO`/`addSO`, each a `toSOAt segWitness (…)` of a blueprint code).
v4.34's `Bounding`-generalised hierarchy made those codes bigger, so what the v4.33 kernel
survived it no longer does.

### The two fixes, in order of preference

1. **Never let the kernel push a recursive syntax function through a concrete code.**
   State the unfolding as a lemma proved by `rw` with DeMorgan/neg lemmas *at variable
   subformulas* (`Semiformula.neg_exs₁`, `LogicalConnective.DeMorgan.and`), then `rw` with it:
   `neg_goodBSO` in `ACA/EpsProg.lean`.  This is fix-shape 2 of lap 2, now known to apply to
   the KERNEL as well as the elaborator.
2. **Split the declaration.**  The kernel's whnf cache is per-declaration; lifting each `have`
   of a long `PSeq` assembly to a `private theorem` with its sequent spelled out cut the peak
   by an order of magnitude and localises what is left.

Done this lap in `ACA/EpsProg.lean`:
`goodAllTI` → `goodAllTI_{branchA,hmain,hor1,hor2,hor3,hall1,hall2,branchB}` + `neg_goodBSO`;
`epsProg` → `epsProg_{hyp,cover,hGamma0,hStepC,hStepE,hStepG}`.

## Next attack

1. Finish `ACA/EpsProg.lean` under `-M 10000`; then the same `-M` probe on
   `ACA/OmegaJumpDepth.lean` (83 lines, two `emb_univCl_of_closed (by simp […])`
   `freeVariables` read-offs — may be a W5c elaborator runaway instead) and
   `Ramified/UpperBound.lean` (330 lines; `simp [Prog, below, precAt, precBelowR, precCode₁R,
   lvlOf_lMap_toLRA]` inside `ramified_upper_bound` is the W5b-shaped suspect).
2. Then whole-repo `lake build`; expect one more wave as the unlocked dependents
   (`ACA/OmegaJumpInduction`, `ACA/OmegaJumpProg`, `ACA/UpperBound`,
   `Ramified/{FefermanSchutte,LimitTheorem,CopyR}`) are reached.
3. Then `lake env lean scripts/AxiomCheck.lean` (frozen, 538 guards).
4. Only once both are green: create `PORT-V434-GREEN.md`, delete `PORT-REF-gi-Compat.lean.txt`.

## Box notes

* ~19 GB RAM, no `-j` on Lake 5 — never two `lake build`s at once.  Verify green from scalars
  in their own call: `grep -c 'Build completed successfully'` (want 1), `grep -cE '^error'` (0).
* `lake env lean -M <MB>` is the diagnostic of choice; `--profile`'s `type checking` vs
  `tactic execution` line says which family (W9 vs W5b/W7) you are in.
* Never `lake update`, never `lake exe cache get`, never push.
