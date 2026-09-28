# DIRECTION — OrdinalAnalysis v4.34 port

## CURRENT DIRECTIVE  (set on review lap 3, 2026-09-28; altitude laps are its only writers)

**Objective — MET on lap 3.**  `lake build` reports `Build completed successfully (1599 jobs)`
and `lake env lean scripts/AxiomCheck.lean` exits 0 with all 538 guards matching.
`PORT-V434-GREEN.md` records both, `PORT-REF-gi-Compat.lean.txt` is deleted.

**Mandated next move.**  Stop.  The port's objective is complete; the only remaining work is
upstream-facing (push + PR) and the box never pushes.  Do **not** invent side quests inside
this repo.  If a further lap runs anyway: re-verify both gates from scalars in their own call
before touching anything, and confine changes to the tidy-ups listed in `PENDING_WORK.md`.

**Forbidden drift.**  No `lake update`, no `lake exe cache get`, no manifest/lakefile edit, no
module-system conversion, no push, no new `axiom`, no weakening of a guarded statement, no
reformatting of Wu's declarations.  Never declare green off a piped/`tail`-ed log.

**Why.**  This port is a gift PR to upstream (Wu) *and* the prerequisite for
goodstein-independence to `require` `gentzen_upper_bound`.  The repo has zero `sorry` and zero
math axioms; "green with the statements frozen" was the whole deliverable, and it is achieved.

### Directive history
* 2026-09-28 (lap 3, review): first directive recorded.  Direction from lap 2 KEPT (three OOM
  modules remain, same W5c/W7 family); the one correction is the diagnostic method —
  `lean -M` / `--profile` replaces truncation-bisect as the first move.
* 2026-09-28 (lap 3, close): objective MET — both gates green, `PORT-V434-GREEN.md` written.
  The W5c/W7 guess was wrong in kind: every remaining failure was **W9**, a *kernel* blow-up.
