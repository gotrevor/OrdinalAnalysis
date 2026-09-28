# DIRECTION — OrdinalAnalysis v4.34 port

## CURRENT DIRECTIVE  (set on review lap 3, 2026-09-28; altitude laps are its only writers)

**Objective.** `lake build` green for the whole `OrdinalAnalysis` target **and**
`lake env lean scripts/AxiomCheck.lean` green (538 `#guard_msgs`-guarded `#print axioms`,
every one a trust-base list), with every guarded statement byte-identical to v4.33.
Then, and only then, `PORT-V434-GREEN.md`.

**Mandated next move.** Clear the remaining OOM-killed modules, hardest-first by unlock size:
`ACA/EpsProg` (2127 lines, unlocks `ACA/OmegaJumpProg` + `ACA/UpperBound`), then
`Ramified/UpperBound` (unlocks `FefermanSchutte`, `LimitTheorem`, `CopyR`), then
`ACA/OmegaJumpDepth` (83 lines, unlocks `ACA/OmegaJumpInduction`).
**Localise with `lake env lean -M <MB> -j 1 <file>`, not by truncation-bisect** — Lean's
`-M` turns the exit-137 kill into a *named* `maximum memory` error at the offending
declaration, and `--profile` names the slow one even when it survives.  Truncation bisecting
cost lap 2 an hour; it is now the fallback, not the first move.

**Forbidden drift.** No `lake update`, no `lake exe cache get`, no manifest/lakefile edit, no
module-system conversion, no push, no new `axiom`, no weakening of a guarded statement, no
reformatting of Wu's declarations.  Do not declare green off a piped/`tail`-ed log.

**Why.** This port is a gift PR to upstream (Wu) *and* the prerequisite for
goodstein-independence to `require` `gentzen_upper_bound`.  The repo has **zero** `sorry`
and **zero** math axioms; the only debt is toolchain churn, so "green" is the whole deliverable
and any statement drift would silently destroy the thing being ported.

### Directive history
* 2026-09-28 (lap 3, review): first directive recorded.  Direction from lap 2 KEPT (three OOM
  modules remain, same W5c/W7 family); the one correction is the diagnostic method —
  `lean -M` / `--profile` replaces truncation-bisect as the first move.
