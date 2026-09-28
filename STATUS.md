# STATUS — OrdinalAnalysis-v434 📊

**Wu's ordinal-analysis library, ported from Foundation `8c6a5c0`/mathlib v4.33 to Foundation `bde9bc28`/mathlib v4.34.** · **Build**: 🔴 not green — 1594/1599 jobs, 3 modules OOM-killed (exit 137) · **Updated**: lap 3 · 2026-09-28 · `e1fc3e9`

## Where it stands

The port is a pure *toolchain-churn* job: the mathematics is finished and byte-frozen. `src/` has
**zero `sorry`** and **zero `axiom`**, and `scripts/AxiomCheck.lean` pins 538 headline declarations
to trust-base-only `#print axioms` lists with `#guard_msgs`. Lap 1 took the build from 851 errors to
1553/1599 jobs; lap 2 to 1595/1599. What remains is one recurring failure family — the v4.34
elaborator unfolds definitions *through concrete coded formulas*, so a `simp`/anonymous-constructor
that used to close a goal now diverges and the module is OOM-killed with **no error message**.
Three modules are still in that state: `ACA/EpsProg`, `Ramified/UpperBound`, `ACA/OmegaJumpDepth`.

## What's happened (newest first)

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

### Short-term (mirrors PENDING_WORK top)
1. `OrdinalAnalysis/ACA/EpsProg.lean` (2127 lines) — OOM at 272 s. Unlocks `ACA/OmegaJumpProg`, `ACA/UpperBound`.
2. `OrdinalAnalysis/Ramified/UpperBound.lean` (330 lines) — OOM at 153 s. Unlocks `Ramified/{FefermanSchutte,LimitTheorem,CopyR}`.
3. `OrdinalAnalysis/ACA/OmegaJumpDepth.lean` (83 lines) — OOM at 66 s; almost certainly the two
   `emb_univCl_of_closed (by simp […])` `freeVariables` read-offs (W5c). Unlocks `ACA/OmegaJumpInduction`.
4. Expect one or two further waves: each cleared module exposes its dependents' own runaways.

### Long-term
* `lake env lean scripts/AxiomCheck.lean` green (frozen; 538 guards).
* `PORT-V434-GREEN.md` (the host's stop condition) + delete `PORT-REF-gi-Compat.lean.txt`.
* Hand the diff to upstream `MaxWellApexLab/OrdinalAnalysis` as a PR; unblock
  goodstein-independence's `require` on `gentzen_upper_bound`.

### To completion
Green `lake build` + green AxiomCheck. No mathematical debt exists to pay off.

## Axiom ledger

This repo is unusual: the fidelity spine is already closed, and the port must not disturb it.

| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `Gentzen.UpperBound.gentzen_upper_bound` | unconditional | `[propext, Classical.choice, Quot.sound]` | 🟢 trust base only |
| `Gentzen.Epsilon1LowerBound.epsilon1_lower_bound` | unconditional | `[propext, Classical.choice, Quot.sound]` | 🟢 trust base only |
| `IDn.idn_theorem_final`, `IDn.idn_analysis`, `IDn.idlt_analysis` | unconditional | `[propext, Classical.choice, Quot.sound]` | 🟢 trust base only |
| `ACAOmega.OmegaDerivable₂.secondCutElimination` (+ `_epsilon`, `_ev_Gamma0`) | unconditional | `[propext, Classical.choice, Quot.sound]` | 🟢 trust base only |
| `Ramified.ramified_theorem` / Feferman–Schütte | unconditional | (guarded; currently unbuildable — module OOM) | 🟢 expected trust base; **re-verify when green** |
| all 538 `#guard_msgs` targets | — | trust base (some a strict subset) | 🟢 |

**Math-axiom count (🟢+🟡+🟠): 0.** No `native_decide`, no `partial def`, no cited axiom anywhere
in `src/`. The *only* open risk is that the port silently changes a guarded statement — which is
exactly what `AxiomCheck.lean` being frozen and `#guard_msgs`-checked is there to prevent.

## Pointers
`PORT-V434.md` (brief + churn log W1–W8) · newest `HANDOFF-2026-09-28-lap2.md` · `PENDING_WORK.md` · `DIRECTION.md`
