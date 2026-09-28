# PORT-V434: OrdinalAnalysis (Wu) v4.33.0 → v4.34.0

Treadmill brief, branch `v4.34` on Trevor's fork `gotrevor/OrdinalAnalysis` (the box never pushes).
Upstream is `MaxWellApexLab/OrdinalAnalysis` (Wu); this port is a gift to them AND the prerequisite
for goodstein-independence to `require` Wu's `gentzen_upper_bound` (the lower half of Wainer's
classification).  g-i is already on v4.34 with Foundation `bde9bc28`, so this port pins the same
Foundation.

The mechanical part is done by `lean-bump` on the host (uncommitted in the tree, keep it):
`lean-toolchain` = v4.34.0, `lake-manifest.json` adopted from the `~/.lake-base/4.34.0` store
(Foundation `bde9bc28` = FFL master 2026-09-27, mathlib `5ed29652` = v4.34.0).  `.lake/packages` is
pre-built; there is no network, so **never** run `lake update` or `lake exe cache get`, and never
edit the manifest or lakefile.

## Objective

`lake build` green (whole repo, default target `OrdinalAnalysis`) **and**
`lake env lean scripts/AxiomCheck.lean` passing with every guarded headline still
`[propext, Classical.choice, Quot.sound]`, statements unchanged.  Then commit, log, and **only then**
create `PORT-V434-GREEN.md` holding the last lines of the green `lake build` and of the AxiomCheck
run (the host's stop condition is that file existing; creating it early is a false claim), commit
it, `box done`.

## Where the breakage is

First host build (2026-09-28): 851+ errors, first wave = `bad import 'Foundation.FirstOrder.Basic.CutFree'` (module gone at `bde9bc28`) in `OrdinalAnalysis/Basic.lean`, `Proof/CutRank.lean`, cascading.  Deps replay green from the store (1019/1594 jobs).

Wu was on Foundation `8c6a5c0` (namespace `LO`, 319 files `open LO`/`LO.FirstOrder`), mathlib
v4.33.0.  This is the **same Foundation churn goodstein-independence just ported through**
(`b47cf44` → `bde9bc28`); its full symptom → fix log is copied below, and its `Compat.lean` shim is
at `PORT-REF-gi-Compat.lean.txt` (reference only, delete before the final commit).  Expect
patterns 1-3 (`LO` → `FFL`, `Tarski.Structure`, `∀⁰` → `∀¹`) to account for most first-wave errors.

Wu's `CodedNotation.lean` uses `𝚺₁.Semisentence` and Foundation's arithmetization heavily; see
patterns 4-9.

Work bottom-up through the import graph: fix imports first, then build again (the first wave hides
the rest).  Find moved names under `.lake/packages/Foundation/` and `.lake/packages/mathlib/`.

## Rules

- **Frozen:** `scripts/AxiomCheck.lean` (its guarded names and expected axiom lists) and the
  statements of every declaration it guards.  Fix proofs, imports and helper lemmas; never weaken a
  headline.
- **Stay non-module.**  Do not convert files to the `module` system; that is a separate decision.
- Prefer one `OrdinalAnalysis/Compat.lean` shim (aliases, notation, small proved lemmas) over
  rewriting many call sites.  Never add an `axiom`.
- Keep the diff minimal and upstream-friendly: this goes to Wu as a PR, so no reformatting, no
  renames of Wu's own declarations, no new docs beyond this brief.
- `native_decide`, deprecation warnings and `set_option maxHeartbeats` bumps are fine.
- Commit green checkpoints as you go.

## Log (required: the migration playbook is built from it)

Append NEW patterns (ones not in g-i's list below) under "Wu-only churn patterns", one line each:
**symptom → fix → example site**, old and new identifiers exact.

### Wu-only churn patterns

W1. `unknown namespace FFL.FirstOrder.Derivation`, then a cascade of "Unknown identifier" for
   *every* later name in the file → an `open A B C` line fails **as a whole** when one of its
   namespaces is gone, so one bad namespace hides a hundred real errors.  Fix the `open` first and
   rebuild before reading anything else.  `FFL.FirstOrder.Derivation` →
   `FFL.FirstOrder.LK.Derivation`, `FFL.FirstOrder.Arithmetic.HierarchySymbol` →
   `FFL.FirstOrder.Bounding.HierarchySymbol` → `OrdinalAnalysis/Proof/CutRank.lean:18`,
   `OrdinalAnalysis/Gentzen/InternalONote.lean:15`.
   NB `FFL.FirstOrder.Derivation` still *exists* when `LK/Hauptsatz.lean` is imported (it declares
   `FFL.FirstOrder.Derivation.Canonical`), so the same `open` line errors in one file and not
   another.

W2. **the one-sided LK calculus went from list to multiset sequents.**
   `Sequent L = List (Proposition L)` → `LK.Sequent L = Multiset (Proposition L)`, and the single
   subset rule `contraction : Derivation Δ → Δ ⊆ Γ → Derivation Γ` split into `weakening`
   (`⊢ Γ → ⊢ Γ + ⦃φ⦄`) and a two-into-one `contraction` (`⊢ Γ + ⦃φ, φ⦄ → ⊢ Γ + ⦃φ⦄`).  This is not
   a rename: the ordinal analysis is a recursion that reads the principal formula off the *head* of
   the sequent, and `BoundedDerivable`/`OmegaDerivable`/`IDerivable`/`ACA.Derivation` are all
   indexed by list sequents.  Fix, in three parts:
   * `OrdinalAnalysis/Compat.lean` keeps the list sequent type (`FFL.FirstOrder.Sequent`,
     `Sequent.embed`, `Sequent.newVar`) and the list `shifts`, spelled `Γˡ⁺` because upstream's `Γ⁺`
     is `scoped` and a `List` coerces to a `Multiset` (so sharing the token makes every `⊢ᴸᴷ¹ Γ`
     genuinely ambiguous, not resolvable-by-elaboration).  It also proves the coercion lemmas
     (`coe_sequent_cons/cons₂/append/lshifts/tilde/embed`) and `provable_iff_list` — upstream's
     `Theory.Proof.provable_iff` now returns a *multiset* of axioms.
   * `OrdinalAnalysis/FinLK.lean` is the list-sequent calculus itself (`FinDerivation`, `⊢ᶠ¹`,
     `IsCutFree`), taken verbatim from Foundation `8c6a5c0`, **plus the two translations**
     `FinDerivation.ofDerivation : ⊢ᴸᴷ¹ Δ → (Γ : Sequent L) → ↑Γ = Δ → ⊢ᶠ¹ Γ` and
     `FinDerivation.toUpstream : ⊢ᶠ¹ Γ → Nonempty (⊢ᴸᴷ¹ ↑Γ)`, and
     `isCutFree_ofDerivation`.  Both translations are proved, not assumed: `weakening` and
     `contraction` become the subset rule, and the subset rule becomes upstream's
     `Structural.ofSubset` (whose `Multiset.Traversal` arguments come from
     `Multiset.Traversal.ofList`).  `ofDerivation` must be `noncomputable` (`Multiset.toList` is).
   * the entry points translate: `Proof/Bridge.lean` gains `cutFree_of_upstreamDerivation` and
     `toUpstreamDerivation`, and `ID1/Embed.lean`/`IDn/Embed.lean` insert
     `FinDerivation.ofDerivation d₀ _ rfl` after `provable_iff_list`.  So the headline theorems are
     still theorems about upstream's own `⊢ᴸᴷ¹`.
   The same story for `FFL.SecondOrder`: `OrdinalAnalysis/CompatSO.lean` keeps the list
   `SecondOrder.Sequent` with `shift₀`/`shift₁`, and `ACA/LK.lean`'s `toFull` became a
   `Nonempty`-valued theorem translating into `⊢ᴸᴷ²` (upstream's second-order `cut` splits the
   context, so ACA's shared-context `cut` needs one `ofSubset` to contract `Γ + Γ` back to `Γ`).

W3. `instance foo (Γ) : Γ-Function₁ f` no longer elaborates ("typeclass instance problem is stuck,
   `Tarski.Structure ?m V`") → the hierarchy symbols are now parameterised by the bounding set, so
   the auto-bound `(Γ)` leaves the language undetermined.  Annotate it:
   `(Γ : HierarchySymbol)` (26 sites) → `OrdinalAnalysis/Gentzen/InternalONote.lean:48`.

W4. `Definable.ball_le` etc. resolve into `Bounding.HierarchySymbol.Definable` (which is what the
   bare `Definable` now means), so a `Compat` alias in `Arithmetic.HierarchySymbol.Definable` does
   *not* catch them → spell the new name at the call site:
   `Definable.ball_le` → `Definable.arithmetic_ball_le` → `.../InternalONote.lean:334`.

W5b. **`simp [<a PR.Blueprint>]` now diverges** -- 13 GB of elaboration and an OOM kill on a
   178-line file, with no error to read.  With the hierarchy generalised, unfolding the blueprint
   *inside* a full `simp` no longer closes the `𝚺ᴬ₁.DefinedFunction` goal, and the default simp set
   loops on the residue.  Fix: unfold first, then simp --
   `simp only [<blueprint>, Bounding.HierarchySymbol.Semiformula.val_mkSigma]` followed by the
   original `simp [...]` (13 s).  Five sites: `Gentzen/CodedNotation.lean:41`,
   `Gentzen/VeblenTower.lean:52`, `Gentzen/JumpArithmetic.lean:65`,
   `Gentzen/InternalVebCover.lean:110`, `Gentzen/InternalVNoteJump.lean:823`.
   The `…Table.blueprint` (`Fixpoint`) sites in `Gentzen/InternalONote.lean` are unaffected.
   **The same divergence hits the read-off lemmas of any `𝚺₁.Semisentence` built with `.mkSigma`**:
   `theorem eval_fooDef : fooDef.val.Evalb v ↔ …  := by simp [fooDef, …]` no longer terminates
   (>10 GB), for the same reason -- unfolding `fooDef` inside a full `simp` leaves the `Hierarchy`
   side proof in the term and the default simp set explores it.  Same fix, applied to 21 sites by
   script: `simp only [fooDef, Bounding.HierarchySymbol.Semiformula.val_mkSigma]` then the original
   `simp [rest]` (`ID1/Internal/Codes.lean:1257` is the smallest example: hang → 23 s).
   Diagnosis recipe, since a diverging `simp` prints nothing: truncate the file at declaration
   boundaries into a scratch copy and `lake env lean` each prefix to localise, then replace the
   tactic by `simp only [<blueprint>]` so the *unsolved goal* is printed.

W7. **anonymous constructors and `simp` against a *concrete* formula term run away in memory.**
   A predicate defined by recursion on formula syntax (`IDn/Theory.lean`'s `PositiveIn`,
   `LevelBounded`) used to accept `exact ⟨h₁, h₂, trivial⟩` at a concrete `DF F ix (j+1)`; the
   elaborator now unfolds the predicate *through* the concrete formula (including `∼`, `🡒`, and the
   `lMap` inside it) and never comes back -- `IDn/Theorem.lean` died at 12.7 GB with no error.
   Fix: name the sequent shape with `show` and take the recursion steps with the existing
   `positiveIn_and`/`_all`/`_or`/`_exs` (+ `Semiformula.imp_eq`,
   `LogicalConnective.DeMorgan.and`/`.or`) simp lemmas, which are stated with *variable*
   subformulas and so are cheap.  197 s OOM → 8 s → `IDn/Theorem.lean:106,127,145,160`.
   Same root cause, same remedy, for `simp [<a code def>, …]` where the def expands into blueprint
   machinery: keep the big formula opaque and rewrite with small `have`s instead
   (`Gentzen/JumpArithmetic.lean:146`, `map_iterZero_body`).

W8. `T ⊢! σ` no longer parses as provability (it elaborates the sentence at `Bool`) → upstream
   collapsed the two entailment notations: `⊢!` was `Entailment.Prf` (the *type* of proofs) and
   `⊢` was `Provable` (the Prop); now there is only `⊢` = `Entailment.Entails : Prop`.  So
   `h : T ⊢! σ` becomes `h : T ⊢ σ`, and the `⟨h⟩`/`rintro ⟨h⟩` wrappers that turned a proof into
   a `Provable` go away → `Ramified/InfTools.lean`, `Ramified/LowerBound.lean` (15 sites).

W5. `WellFoundedRelation.wf` survives (`(measure f).wf.induction` still works); it is only
   `WellFoundedLT`/`IsWellFounded` that lost their wrapper → don't blanket-rewrite `.wf`.

W6. my own sed hazard: `Derivation.` → `LK.Derivation.` must **not** touch `ACA/`,
   where `Derivation` is `OrdinalAnalysis.ACA.Derivation` (it has a `wk` constructor, which
   Foundation's never had — a good tell).

### Reference: goodstein-independence's churn log (same Foundation jump)

#### Foundation (`b47cf44` → `bde9bc28`)

1. `unknown namespace LO` / every `LO.*` name unknown → Foundation's root namespace was renamed
   `LO` → `FFL`; mechanical `LO.` → `FFL.` and `open LO` → `open FFL` across 55 files →
   `GoodsteinPA/ToFoundation/Compat.lean:31`.
2. `Structure` / `Struc` unknown (`invalid binder annotation`, `Tarski.Structure ... is stuck`) →
   the semantics class moved into the `Tarski` namespace: `FFL.FirstOrder.Structure` →
   `FFL.FirstOrder.Tarski.Structure`; likewise `Structure.add_eq_of_lang`,
   `Structure.mul_eq_of_lang`, `Structure.numeral_eq_numeral` →
   `Tarski.Structure.*` → `GoodsteinPA/ToFoundation/Compat.lean`, `GoodsteinPA/ReadoffValueGate.lean:131`.
3. `expected token` at `∀⁰ `/`∃⁰ `/`∀⁰* ` → the first-order quantifier notations are now
   `∀¹ `/`∃¹ `/`∀¹* ` (the superscript numbers the *order*).  685 sites: shimmed, not rewritten —
   `prefix:64 "∀⁰ " => FFL.FirstOrder.UnivQuantifier.all` etc. in `Compat.lean`.
4. `Arithmetic.Hierarchy` unknown → the arithmetical hierarchy was generalised to
   `FFL.FirstOrder.Bounding.Hierarchy ℬ Γ s φ` over a bounding-relation set `ℬ`; the arithmetical
   case is `ℬ[<, L]`.  Shimmed as `abbrev Arithmetic.Hierarchy` + `export` of the lemmas we use
   (`rew exs and_iff or_iff imp_iff sigma_of_sigma_ex`), plus `abbrev DeltaZero` → `Compat.lean`.
   Note `Hierarchy.rew`'s derivation argument is anonymous, so `h.rew _` must become
   `Arithmetic.Hierarchy.rew _ h` → `GoodsteinPA/ReadoffValueGate.lean:432`.
5. `Hierarchy` gained a `bounded` (`ℬ.Closure`) constructor and `ball`/`bexs` now carry
   `R ∈ ℬ` → case-analysis proofs need the extra case and `R = op(<)` inversion →
   `GoodsteinPA/ReadoffValueGate.lean:376` (`sigma1_all_inv`).
6. `𝚺₁`, `Γ-[n]` unknown (`expected token`) → renamed to `𝚺ᴬ₁`, `Γᴬ-[n]` and made `scoped`;
   old spellings restored as global notations in `Compat.lean`.
7. `Γ-Function₃ f via φ` unknown → those notations are `scoped` in `FFL.FirstOrder.Bounding`;
   add `open scoped FFL.FirstOrder.Bounding` → `GoodsteinPA/ToFoundation/FvSubst.lean:21`,
   `GoodsteinPA/Internal.lean`.
8. `FFL.FirstOrder.Arithmetic.HierarchySymbol` unknown → `FFL.FirstOrder.Bounding.HierarchySymbol`
   (and `HierarchySymbol.Semiformula.ball` now takes `hR : R ∈ ℬ`; the arithmetical wrapper is
   `Semiformula.arithmetic_ball` / `val_arithmetic_ball`) → `GoodsteinPA/Kreisel/Statement.lean`.
9. `InductionOnHierarchy.least_number` → `InductionOnBroadHierarchy.least_number`;
   `Definable.ball_le` → `Definable.arithmetic_ball_le` → `GoodsteinPA/Internal.lean:246,473`.
10. `ProvablyProperOn.ofProperOn` → `Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn`
    → `GoodsteinPA/Kreisel/Statement.lean:298`.
11. `Theory.consistent` is now a `𝚷₁.Sentence`; `↑T.consistent` no longer elaborates in an
    implication — use `T.consistent.val` → `GoodsteinPA/Kreisel/Statement.lean:274`.
12. `DeMorgan.neg` → `TildeInvolutive.tilde_involutive` → `GoodsteinPA/Zinfty/Cut.lean:620`.
13. `Derivation2` → `LK2.Derivation` (notation `T ⟹₂ Γ`, scoped); old name restored as an
    `abbrev` in `Compat.lean` → `GoodsteinPA/Zef2TC/Embedding.lean:53`.
14. moved modules: `Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Functions` →
    `Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions`
    (`GoodsteinPA/ToFoundation/FvSubst.lean:16`); `Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1`
    → `Foundation.FirstOrder.Incompleteness.Definability` (`GoodsteinPA/Kreisel/Statement.lean:3`).
15. **content change, not a rename:** PA⁻'s `addEqOfLt` is now
    `∀ x y, x < y → ∃ z <⁺ y, x + z = y` (bounded), so its body is a *conjunction*
    `z < y+1 ⋏ x + z = y`.  The `Zef2TC` derivation for it grew an `andI` node over two
    `trueRel` leaves and the ordinal tower moved up one rung (`ofNat 6` at the root) →
    `GoodsteinPA/Zef2TC/Axm.lean:budgetedEmbedsV3_addEqOfLt`.

#### mathlib v4.31 → v4.34 / Lean core

16. `IsWellFounded α r` deprecated → the class is now `WellFounded r` itself (`attribute [class]`),
    `IsWellFounded.rank`/`rank_lt_of_rel`/`induction` → `WellFounded.*`, and
    `WellFoundedLT α` is `@WellFounded α (·<·)`, so `⟨wf⟩` anonymous constructors must drop the
    brackets → `GoodsteinPA/ToMathlib/Ordinal/WellFoundedRank.lean`,
    `GoodsteinPA/ToMathlib/Hardy/Comparison.lean:16`, `GoodsteinPA/ToMathlib/Ordinal/Epsilon0.lean:110`.
17. **`rw` now checks the target is type-correct at `implicit` transparency.**  A bare anonymous
    constructor in a position of a `def`-wrapped subtype (`ℕ+ = PNat`, `NONote`) elaborates to a
    `Subtype.mk` at the *unfolded* type and fails that check ("not type-correct under the
    `implicit` transparency level"), so `rw`/`simp` stop matching.  Fix: `show ℕ+ from ⟨n, h⟩`
    (resp. `show NONote from ⟨x, h⟩`).  `attribute [reducible] PNat` is refused (not declared
    locally) → `GoodsteinPA/ToMathlib/Goodstein/Domination/Growth.lean`, `.../LowerBound.lean`,
    `.../Ordinal/Epsilon0.lean:125`, `.../ONote/Computability.lean:322`.
    Same root cause when a `simp` lemma keyed on `ℕ+` will not fire: instantiate it by hand
    (`have h_NF := NF_oadd_iff (n := show ℕ+ from ⟨…⟩)`) → `.../ONote/Computability.lean:331`.
18. **the kernel refuses `Nat.pow` with a >32-bit exponent.**  Typechecking a proof mentioning
    `2 ^ (2 ^ 2 ^ 16)` now fails; keep the tower behind an opaque local
    (`obtain ⟨k, hk⟩ : ∃ k, k = 2 ^ (2 ^ 16) := ⟨_, rfl⟩`) →
    `GoodsteinPA/ToMathlib/Goodstein/Domination/BaseCases.lean:594,603`.
19. `Nat.Subtype.denumerable` is `@[no_expose]`, so in module mode `Denumerable.ofEquiv_ofNat`
    can no longer relate `Denumerable.ofNat ↥s` to the *increasing* enumeration
    `Nat.Subtype.ofNat s` — the bridge is unprovable downstream.  Fix: build the coding equiv
    from `Nat.Subtype.ofNat` directly (`codeEnum`, `natCode := Equiv.ofBijective …`, now
    `noncomputable`), which makes the monotonicity read-off `rfl`-close →
    `GoodsteinPA/ToMathlib/Ordinal/Epsilon0.lean:199`, `.../ONote/Computability.lean:enc_strictMono`.
20. `simp` no longer unfolds `n ∈ Nat.rfind p` → use `Nat.mem_rfind` explicitly →
    `GoodsteinPA/ToMathlib/ONote/Computability.lean:rfind_nthNF`.
21. `ORingStructure.zero_eq_zero` gone as a `Semiterm`-level simp lemma; the `0`-operator read-off
    is `rfl` → `GoodsteinPA/Encoding.lean:goodsteinSentence_faithful`.
22. `PNat.add_coe`-style goals: state the arithmetic at `ℕ` (`((x + y : ℕ+) : ℕ) = …`) rather than
    at `ℕ+` so `omega` sees it → `GoodsteinPA/OperatorZeh/Examples.lean:51`.
23. **build-gate note:** `lake env lean <file>` sees *all* oleans, `lake build` restricts to the
    module's declared imports; a file can pass the former and fail the latter (e.g.
    `Structure.numeral_eq_numeral` in `Encoding.lean`).  Trust `lake build`.
24. Deprecations that are warnings only (left alone): `Ordinal.opow_succ` → `opow_add_one`,
    `dif_pos/dif_neg/if_neg` → `dite_eq_*`/`ite_eq_*`, `haveI` → `have` style linter.

