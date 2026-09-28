# HANDOFF 2026-09-28 — PORT-V434 lap 2

**Branch** `v4.34`   **HEAD** `4273516`   **Working tree clean.**
**Status: NOT green, but close** — `lake build` reaches **1595/1599 jobs** (lap start: 1553).
Follow `PORT-V434.md`; its "Wu-only churn patterns" section (W1–W8, plus W5c/W7b/W7c added this
lap) is the migration log this port exists to produce, and it is current.

## What closed this lap (each verified by its own `lake build <module>`)

| module | cause |
|---|---|
| `Ramified/LowerBound` | a lap-1 sed had eaten the `replay_of_provable` **header line**; also `have d' := …` forgets the body, so `isCutFree_ofDerivation` no longer typechecked → `set d' := … with hd'` |
| `IDn/LowerBoundAux2` | **W7b** (new): anonymous constructors in the structurally recursive `noXN_DF`/`noXN_wForm` unfold `NoXN` through a concrete coded formula and OOM the whole file → `noXN_and`/`noXN_all` (`Iff.rfl`, *variable* subformulas) |
| `ACAOmega/CodedOrder₂`, `ACAOmega/Gamma0Order₂` | **W5c**: `freeVariables` read-off by `simp [<def>, h]` → spelled `rw [<def>, freeVariables_and, …, Finset.union_empty]` |
| `Gentzen/Epsilon1UpperBound`, `Gentzen/VeblenTower`, `Gentzen/VeblenSuccStep`, `Gentzen/InternalEpsMonoCode`, `Gentzen/InternalVeblenCode` | **W7c**: the `map_…_body` `lMap` family |
| `Gentzen/ProgStep` | `concrete_progCover`'s bare `simp` → spelled evaluation `simp only` + `push_neg` |
| `ACA/TowerInduction` | `freeVariables_jumpX` (W5c), `towerStepTI_inst`'s `simp [Rew.q_subst]`, **and** a `show` unfolding `thetaAt` at a *concrete* term → `thetaAt_eq`/`thetaInner_eq` stated at a variable |
| `Ramified/{TransfiniteLower,SemiformalLower,DescentBetaAux2}` | W8 leftovers (`rintro ⟨h⟩` → `intro h`, drop `obtain ⟨h⟩ := h`) |

### The three fix shapes, now proven repeatedly

1. `simp [<def>, …]` over a concrete coded formula → `simp only [<def>, Semiformula.lMap_all /
   eval_all, LogicalConnective.HomClass.map_or/neg/and, Semiformula.lMap_subst]`, then one
   `have hwᵢ : (Semiterm.lMap toLX ∘ ![…]) = ![…]` per substitution vector (entries `rfl`, numerals
   `lMap_numeral`), then a single `rw [hw₁, …]`.
2. a `show` (or `exact ⟨…⟩`) that asks the elaborator to unfold a definition **at a concrete term**
   → state the unfolding as a `rfl` lemma **at a variable** and `rw` with it
   (`thetaAt_eq`, `thetaInner_eq`, `noXN_and`, `noXN_all`).
3. a `freeVariables` / `NoXN` read-off → take the syntax steps by `rw` only; any `simp` that
   revisits the concrete formula runs away (a `simp only` with the right lemmas is NOT enough —
   `freeVariables_jumpX` still died until every step was an explicit `rw`).

## Next steps, in order

1. Three modules remain, each OOM-killed (exit 137) when built **alone**, all previously
   unreachable and all the same family:
   `ACA/OmegaJumpDepth`, `ACA/EpsProg`, `Ramified/UpperBound`.
   Bisect each by truncation, then apply shape 1/2/3 above.
2. Expect one or two further waves: clearing a module unlocks the next ~5 jobs, which have their
   own runaways. 1599 is the total.
3. Then `lake env lean scripts/AxiomCheck.lean` (frozen; every guarded headline must still print
   `[propext, Classical.choice, Quot.sound]`).
4. **Only when `lake build` and AxiomCheck are both green**: create `PORT-V434-GREEN.md` with the
   last lines of each run (that file existing is the host's stop condition, so creating it early is
   a false claim), delete `PORT-REF-gi-Compat.lean.txt`, commit.

## Bisect discipline (cost an hour this lap)

* `lake env lean f | tail` **hides the kill** — `$?` is `tail`'s. Read `$?` of the *unpiped*
  command, redirecting to a file.
* A `sorry`-truncated variant that prints **no** "declaration uses `sorry`" warning was **killed,
  not accepted**. Silence is not success.
* Truncating a file mid-declaration gives "unexpected end of input"/"unsolved goals" — those rc=1s
  are artifacts, not findings; cut at declaration boundaries.
* ~20 GB RAM and no `-j` on Lake 5: never two `lake build`s at once. Verify green from scalars in
  their own call: `grep -c 'Build completed successfully'` (want 1), `grep -cE '^error'` (want 0).
* Never `lake update`, never `lake exe cache get`, never push.
