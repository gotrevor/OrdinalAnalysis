# HANDOFF 2026-09-28 — PORT-V434 lap 3 — **GREEN**

**Branch** `v4.34`   **HEAD** `3ad159b`   **Working tree clean.**   **Status: both gates green; stop sentinel signalled and confirmed honored.**

```
$ taskset -c 0-2 lake build           → Build completed successfully (1599 jobs).   rc 0
$ lake env lean scripts/AxiomCheck.lean → (only the manifest warning)                rc 0
```

Verified twice, from a clean tree, with nothing else running, and read from scalars in their
own call (`grep -c 'Build completed successfully'` = 1, `grep -cE '^error'` = 0).
`PORT-V434-GREEN.md` is written; `PORT-REF-gi-Compat.lean.txt` is deleted.
`src/`: zero `sorry`, zero `admit`, zero declared `axiom`; `scripts/AxiomCheck.lean` untouched.

## What this lap found: **W9 / W9b** — the kernel, not the elaborator

Lap 2 left three OOM-killed modules and assumed more of the W5c/W7 `simp`-runaway family.
That was wrong in kind.  `lake env lean -M 9000 -j 2 --profile ACA/EpsProg.lean` showed
`elaboration 199 ms · tactic execution 9.5 s · type checking 33.7 s` and two *named*
per-declaration errors: the files **elaborate fine** and die in kernel type checking.

Root cause, isolated to single defeqs by splitting and `sorry`-bisecting: on v4.34 the kernel
(no `smartUnfolding`, no equation lemmas — it reduces `brecOn` directly) blows up whenever it
is asked to reduce a **structural recursion on syntax at a concrete coded formula**.  The
`Bounding`-generalised hierarchy made every code bigger, so what v4.33 survived, v4.34 does not.

| where | the recursion the kernel was asked to run | fix |
|---|---|---|
| `ACA/EpsProg.goodAllTI_branchB` | `Semiformula.neg` through `goodBSO` | `neg_goodBSO` (`neg_exs₁` + `DeMorgan.and` at a variable) |
| `ACA/EpsProg.epsProg_key` | `neg` through `tiSO` / `belowSOX` | `DeMorgan.or`, `neg_all₁` instead of `rfl`/`show` |
| `ACA/OmegaJumpDepth` (both theorems) | `toSOAt`/`toSOAtB` through the tower matrix | `toSOAt_all₂`/`toSOAt_all₃` at a variable matrix |
| `Ramified/UpperBound.eval_precCode₁R_model` | `Semiformula.Eval` through `precDef₁` | `eval_arR_model`, the same step at a variable `σ` |
| `ACA/OmegaJumpUpperBound.epsJump_plus` | `neg_exs₂` and `SecondOrder.Rew.app` through `IsOmegaJump` | `rw [Semiformula.neg_exs₂]`, `rw [SecondOrder.Rew.app_exs₁ …]` |
| `Ramified/DescentBetaAux4.{step2,descentOne}` | **W9b**: `rank` through a concrete formula, forced by a `set` local | `rw [hμdef]` / `rw [hρdef]` before the `exact` |

Plus, as a second lever, splitting long `PSeq`/`DerLt` assemblies into `private theorem`s (the
kernel's whnf cache is per-declaration): `goodAllTI` → 8 pieces, `epsProg` → 8, `epsJump_plus`
→ 5.  That alone cut the peak by an order of magnitude and localised what was left.

### The probe that made all of this cheap

```
lake env lean -M <MB> -j 2 --profile <file>        # names every offending declaration, keeps going
lake env lean -M <MB> -j 2 -D maxHeartbeats=<n> …  # when the memory exception escapes uncaught
```

`-M` turns the silent `exit 137` into `<file>:<line>:<col>: error: (kernel) excessive memory
consumption detected` per declaration; `--profile`'s `type checking` vs `tactic execution`
line says whether you are in W9 or in the W5b/W7 elaborator family.  `-D maxHeartbeats` is
needed when the blow-up aborts the process (`libc++abi: … memory_exception … at 'interpreter'`,
rc 134) instead of producing a message.  Truncation-bisect is now the fallback, not the first
move; inside a declaration, `sorry`-bisecting the argument blocks pinned two 60-line proofs to
one bullet each in three runs.

## Next steps

1. **Host**: push `v4.34` and open the PR against `MaxWellApexLab/OrdinalAnalysis`.
2. **Host**: point goodstein-independence's `require` at it for `gentzen_upper_bound`.
3. Nothing is open in this repo.  `PENDING_WORK.md` lists only optional tidy-ups.

## Box notes (unchanged, still true)

* ~19 GB RAM, no `-j` on Lake 5 → cap with `taskset -c 0-2 lake build`.  A 4-worker build
  OOM-killed `DescentBetaAux4` transiently this lap; 3 workers was clean.
* Verify green from scalars in their own call, never from a piped/`tail`-ed log.
* Never `lake update`, never `lake exe cache get`, never push.
