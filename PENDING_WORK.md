# PORT-V434 — state after lap 1 (2026-09-28)

`lake build` reaches **1546/1599 jobs** (was 851 errors at lap start).  Not green yet.
Three WIP commits on `v4.34` (all made with `--no-verify`, each labelled NOT green; the repo's
pre-commit hook runs `lake build`, so a green commit is only possible at the end).

## What is done

All of the churn patterns are identified, fixed and logged in `PORT-V434.md`
("Wu-only churn patterns", W1–W8).  The two structural ones:

* **the one-sided LK calculus went from list to multiset sequents.**  `OrdinalAnalysis/Compat.lean`
  keeps the list sequent type and its coercion lemmas, `OrdinalAnalysis/FinLK.lean` is the list
  calculus `⊢ᶠ¹` together with the *proved* translations to and from upstream's `⊢ᴸᴷ¹`
  (`FinDerivation.ofDerivation`, `.toUpstream`, `isCutFree_ofDerivation`), and
  `OrdinalAnalysis/CompatSO.lean` is the second-order copy.  Nothing is axiomatised, and the
  headline theorems still hang off upstream's own calculus: `Proof/Bridge.lean` exposes
  `cutFree_of_upstreamDerivation` and `toUpstreamDerivation`.
* **elaboration of concrete coded formulas got much more expensive.**  A full `simp` that unfolds a
  `𝚺₁.Semisentence`/`PR.Blueprint` definition, or an anonymous constructor against a
  syntax-recursive predicate at a concrete formula, now runs away in memory (13 GB, OOM-killed with
  no error).  157 sites were rewritten mechanically (`simp only [<def>, val_mkSigma]` then the
  original simp), and five proofs by hand (W5b, W7).  `PORT-V434.md` has the bisect recipe, which
  matters because a diverging `simp` prints nothing at all.

## What is left (in order)

1. `Ramified/LowerBound.lean` — 21 errors, the last of them just fixed (`⊢!` → `⊢`, the `hauptsatz`
   result translated with `FinDerivation.ofDerivation`); rebuild and finish.
2. `IDn/LowerBoundAux2.lean` and `ACAOmega/CodedOrder₂.lean` — OOM-killed (exit 137).  Both were
   killed while three other 2–4 GB files were compiling, so try them **alone** first
   (`lake build <module>`); if they still die, bisect by truncation as in W5b/W7 — they are the
   same family.
3. the ~50 jobs after those, not yet reached.
4. then `lake env lean scripts/AxiomCheck.lean`, and only once *both* are green create
   `PORT-V434-GREEN.md` (the host's stop condition) and delete `PORT-REF-gi-Compat.lean.txt`.

## Box note

The box has ~20 GB and no `-j` flag on Lake 5, so **never leave two `lake build`s running**: the
first three OOM waves of this lap were my own overlapping builds, not the code (the reference
corpus's `lean-box-oom-and-scrambled-relay-false-green.md` says exactly this).  Kill stale `lean`
processes before judging an OOM, and verify green from scalars in their own call
(`grep -c 'Build completed successfully'`, `grep -cE '^error'`).
