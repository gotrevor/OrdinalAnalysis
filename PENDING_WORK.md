# PORT-V434 — state after lap 2 (2026-09-28)

`lake build` reaches **1597/1599 jobs**.  Not green yet: exactly two modules remain, both
OOM-killed (exit 137) *alone*, i.e. genuine runaways, not build concurrency:

* `OrdinalAnalysis/Gentzen/InternalEpsMonoCode.lean`
* `OrdinalAnalysis/Gentzen/InternalVeblenCode.lean`

## Closed this lap

* `Ramified/LowerBound.lean` — a lap-1 sed had eaten the `replay_of_provable` header line;
  restored, plus `set d' := FinDerivation.ofDerivation …` (a `have` forgets the body, so
  `isCutFree_ofDerivation` no longer typechecked against `d'`).
* `IDn/LowerBoundAux2.lean` — **W7b**, new: an anonymous constructor in the *structurally
  recursive* `noXN_DF`/`noXN_wForm` proofs unfolds `NoXN` through a concrete coded formula and
  OOMs the whole file (even a `#check` after it dies).  Added `noXN_and`/`noXN_all` (`Iff.rfl`,
  variable subformulas) and used `.mpr` at each node.
* `ACAOmega/CodedOrder₂.lean`, `ACAOmega/Gamma0Order₂.lean` — **W5c**: `simp [precSeg₀, h]` for a
  `freeVariables` read-off → spelled `rw [precSeg₀, …freeVariables_and, …, Finset.union_empty]`.
* `Gentzen/Epsilon1UpperBound.lean` (`map_succ_body`), `Gentzen/VeblenTower.lean`
  (`map_towerZero_body`, `map_towerSucc_body`), `Gentzen/VeblenSuccStep.lean`
  (`map_succGeneral_body`) — **W7c**: the `lMap`-body family; `simp only [… lMap_all,
  HomClass.map_or/neg/and, lMap_subst]` + one `have` per substitution vector + one `rw`.
* `Ramified/{TransfiniteLower,SemiformalLower,DescentBetaAux2}.lean` — W8 leftovers
  (`rintro ⟨h⟩` → `intro h`, drop `obtain ⟨h⟩ := h`).

## Next attack

1. Bisect the two remaining files by truncation.  **Read `$?` of an *unpiped* `lake env lean`** —
   piping into `tail` hides the kill, and a `sorry`-truncated variant that prints no
   "declaration uses 'sorry'" warning was killed, not accepted (this cost an hour of this lap).
   Expect the same two shapes: a full `simp` unfolding a `𝚺₁.Semisentence`/`PR.Blueprint`, or an
   anonymous constructor / `Iff.rfl` against a concrete coded formula.
2. Then `lake build` whole repo, then `lake env lean scripts/AxiomCheck.lean` (frozen).
3. Only once both are green: create `PORT-V434-GREEN.md` (host stop condition), delete
   `PORT-REF-gi-Compat.lean.txt`, commit.

## Box note

~20 GB RAM, no `-j` on Lake 5 — never two `lake build`s at once.  Verify green from scalars in
their own call: `grep -c 'Build completed successfully'` (want 1), `grep -cE '^error'` (want 0).
