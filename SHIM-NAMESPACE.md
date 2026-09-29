# SHIM-NAMESPACE: get OrdinalAnalysis's compat shims out of Foundation's namespaces

Treadmill brief, branch `v4.34-port` (the clean v4.34 port of KT. Wu's repo, on Trevor's fork).  The
box never pushes.  Leave this file in place; the host strips process notes before any PR.

## Why

The v4.34 port restored Foundation's old spellings with three shims, `OrdinalAnalysis/Compat.lean`,
`CompatArith.lean`, `CompatSO.lean`, and they declare into **Foundation's own namespaces**
(`namespace FFL.FirstOrder.Arithmetic`, `FFL.FirstOrder`, `FFL.SecondOrder`) plus unnamed global
notations (`𝚺₀`, `𝚷₀`, `𝚫₀`, `𝚺₁`, `𝚷₁`, `𝚫₁`, ...).  Any other project with its own Foundation
shim then cannot import OrdinalAnalysis: goodstein-independence's shim declares the same
`FFL.FirstOrder.Arithmetic.Hierarchy`, `FFL.FirstOrder.Arithmetic.DeltaZero` and the same notations,
and the import fails with
`environment already contains 'FFL.FirstOrder.Arithmetic.«term𝚷₀»' from OrdinalAnalysis.CompatArith`.

A library should not add names to a dependency's namespace.

## Objective

1. `scripts/coexist-check.sh` exits 0 (prints `coexist-check: OK`).  It is red today.
2. `lake build` green (whole repo).
3. `lake env lean scripts/AxiomCheck.lean` passes unchanged (every guard `[propext, Classical.choice, Quot.sound]`).

Then commit, and only then create `SHIM-COEXIST-GREEN.md` with the last lines of all three runs;
commit it; `box done`.

## How

- Move every shim declaration out of `FFL.*` into a namespace this repo owns (e.g.
  `OrdinalAnalysis.Compat...`), and make the shim notations `scoped` in that namespace (or give them
  `(name := ...)` and scope them), so importing OrdinalAnalysis adds **no** declaration or unscoped
  notation under `FFL.*`.
- Then fix call sites: add `open OrdinalAnalysis.Compat` / `open scoped ...` where the old names are
  used, or spell the upstream name directly.  Prefer the smallest diff.
- **Also check non-shim files**: any other declaration this repo makes inside `namespace FFL...`
  (e.g. in `FinLK.lean`) is the same problem; move it too.  `grep -rn '^namespace FFL' OrdinalAnalysis`
  should end up empty or justified in the handoff.

## Rules

- **Frozen:** `scripts/AxiomCheck.lean`, `scripts/CoexistShim.lean`, `scripts/CoexistCheck.lean`,
  `scripts/coexist-check.sh`, and every statement AxiomCheck guards.
- Stay non-module.  Never add an `axiom`; never edit lakefile/manifest; no network.
- Commit green checkpoints as you go.
