# STATUS — OrdinalAnalysis-v434 📊

**Wu's ordinal-analysis library, ported from Foundation `8c6a5c0`/mathlib v4.33 to Foundation `bde9bc28`/mathlib v4.34.** · **Build**: 🟢 green (1599 jobs) + AxiomCheck green · **Updated**: lap 3 · 2026-09-28 · `0146b9c`

## Where it stands

**The port is done.**  `lake build` reports `Build completed successfully (1599 jobs)` and
`lake env lean scripts/AxiomCheck.lean` exits 0 with all **538** `#guard_msgs`-guarded
`#print axioms` matching their frozen lists.  `src/` has zero `sorry`, zero `admit` and zero
declared `axiom`; no guarded statement was touched.  The remaining work is upstream-facing:
hand the diff to `MaxWellApexLab/OrdinalAnalysis` as a PR, and let goodstein-independence
`require` `gentzen_upper_bound`.

## What's happened (newest first)

* **2026-09-28 (lap 3, grind)** — **GREEN.**  1594 → 1599/1599 and AxiomCheck clean.  Six
  modules cleared (`ACA/EpsProg`, `ACA/OmegaJumpDepth`, `Ramified/UpperBound`,
  `ACA/OmegaJumpUpperBound`, `Ramified/DescentBetaAux4`, and the wave behind them), all one
  new failure family: **W9**, a *kernel* (not elaborator) memory blow-up whenever a structural
  recursion on syntax is forced at a concrete coded formula.  `PORT-V434-GREEN.md` written.
* **2026-09-28 (lap 3, review)** — direction KEPT; recorded `DIRECTION.md` + this file. One method
  correction: diagnose the OOM modules with `lake env lean -M <MB> --profile`, which names the
  diverging declaration, instead of truncation-bisecting (which cost lap 2 an hour).
* **2026-09-28 (lap 2)** — 1553 → 1595/1599. Cleared 14 modules; added churn patterns W5c, W7b, W7c
  and the three fix shapes (`simp only` + per-substitution `have`s; `rfl` lemma stated *at a
  variable*; `rw`-only `freeVariables` read-off).
* **2026-09-28 (lap 1)** — 851 errors → 1553/1599. Foundation `LO`→`FFL` rename, the list→multiset
  LK sequent split (`Compat.lean`/`FinLK.lean`/`CompatSO.lean` keep the list calculus and *prove*
  the translations both ways), `Tarski.Structure`, `∀⁰`→`∀¹`, `Bounding.HierarchySymbol`,
  `⊢!`→`⊢`. Patterns W1–W8 logged in `PORT-V434.md`.

## Outstanding

### Short-term
Nothing blocking.  `PORT-V434-GREEN.md` exists; `PORT-REF-gi-Compat.lean.txt` deleted.

### Long-term
* Hand the diff to upstream `MaxWellApexLab/OrdinalAnalysis` as a PR (the box never pushes).
* Point goodstein-independence's `require` at this branch for `gentzen_upper_bound`.
* Optional, not required by the brief: the `private theorem` splits introduced for W9 are
  upstream-friendly but could be tidied into named sections if Wu prefers.

### To completion
Done.  Both gates green, statements frozen, no mathematical debt.

## Axiom ledger

This repo is unusual: the fidelity spine is already closed, and the port must not disturb it.

| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `Gentzen.UpperBound.gentzen_upper_bound` | unconditional | `[propext, Classical.choice, Quot.sound]` | 🟢 trust base only |
| `Gentzen.Epsilon1LowerBound.epsilon1_lower_bound` | unconditional | `[propext, Classical.choice, Quot.sound]` | 🟢 trust base only |
| `IDn.idn_theorem_final`, `IDn.idn_analysis`, `IDn.idlt_analysis` | unconditional | `[propext, Classical.choice, Quot.sound]` | 🟢 trust base only |
| `ACAOmega.OmegaDerivable₂.secondCutElimination` (+ `_epsilon`, `_ev_Gamma0`) | unconditional | `[propext, Classical.choice, Quot.sound]` | 🟢 trust base only |
| `Ramified.ramified_theorem` / Feferman–Schütte | unconditional | `[propext, Classical.choice, Quot.sound]` | 🟢 trust base only (re-verified green) |
| all 538 `#guard_msgs` targets | — | trust base (some a strict subset) | 🟢 |

**Math-axiom count (🟢+🟡+🟠): 0.** No `native_decide`, no `partial def`, no cited axiom anywhere
in `src/`. The *only* open risk is that the port silently changes a guarded statement — which is
exactly what `AxiomCheck.lean` being frozen and `#guard_msgs`-checked is there to prevent.

## Pointers
`PORT-V434-GREEN.md` · `PORT-V434.md` (brief + churn log W1–W9b) · newest `HANDOFF-2026-09-28-lap2.md` · `PENDING_WORK.md` · `DIRECTION.md`
