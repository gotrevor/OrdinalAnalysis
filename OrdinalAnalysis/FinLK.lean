/-
  # The finitary calculus on *list* sequents, and its translation from upstream

  Upstream `Foundation` reshaped its one-sided LK calculus between `8c6a5c0`
  (which this development was written against) and `bde9bc28`: sequents became
  multisets, and the single subset rule
  `contraction : Derivation Δ → Δ ⊆ Γ → Derivation Γ` split into `weakening`
  plus a two-into-one `contraction`.

  The embeddings in `Gentzen/Embed.lean`, `ID1/Embed.lean`, `IDn/Embed.lean` and
  `Ramified/Embed.lean` are structural recursions that read the principal formula
  off the *head* of the sequent and produce an infinitary derivation of the
  head-wise translated sequent.  Multisets have no head, so the shape of those
  recursions is tied to list sequents.

  `FinDerivation` is therefore the list-sequent calculus those recursions run on,
  and `FinDerivation.ofDerivation` **translates upstream's derivations into it**:
  a `weakening` or a `contraction` node becomes the subset rule, and every other
  rule is copied with the premise's sequent transported along the multiset
  equality.  Nothing here is assumed -- the translation is a total function and
  `ofDerivation_isCutFree` shows it preserves cut-freeness -- so the theorems
  downstream are still theorems *about upstream's `⊢ᴸᴷ¹`*: the entry points take
  a `⊢ᴸᴷ¹` and translate.
-/
import OrdinalAnalysis.Compat

namespace OrdinalAnalysis

open FFL FFL.FirstOrder

variable {L : Language}

/-- Derivation for one-sided `LK` on list sequents (`Foundation` `8c6a5c0`'s
`Derivation`, verbatim). -/
inductive FinDerivation : Sequent L → Type _
  | identity {k : ℕ} (r : L.Rel k) (v) : FinDerivation [.rel r v, .nrel r v]
  | cut {φ : Proposition L} {Γ Δ : Sequent L} :
      FinDerivation (φ :: Γ) → FinDerivation ((∼φ) :: Δ) → FinDerivation (Γ ++ Δ)
  | contraction {Δ Γ : Sequent L} : FinDerivation Δ → Δ ⊆ Γ → FinDerivation Γ
  | verum : FinDerivation [(⊤ : Proposition L)]
  | or {φ ψ : Proposition L} {Γ : Sequent L} :
      FinDerivation (φ :: ψ :: Γ) → FinDerivation (φ ⋎ ψ :: Γ)
  | and {φ : Proposition L} {Γ : Sequent L} {ψ : Proposition L} :
      FinDerivation (φ :: Γ) → FinDerivation (ψ :: Γ) → FinDerivation (φ ⋏ ψ :: Γ)
  | all {Γ : Sequent L} {φ : Semiproposition L 1} :
      FinDerivation (Rewriting.free φ :: Γˡ⁺) → FinDerivation ((∀¹ φ) :: Γ)
  | exs {φ : Semiproposition L 1} {t : SyntacticTerm L} {Γ : Sequent L} :
      FinDerivation (φ/[t] :: Γ) → FinDerivation ((∃¹ φ) :: Γ)

@[inherit_doc] prefix:45 "⊢ᶠ¹ " => FinDerivation

namespace FinDerivation

/-- Transport along an equality of sequents. -/
protected abbrev cast {Γ Δ : Sequent L} (d : ⊢ᶠ¹ Δ) (e : Δ = Γ := by simp) : ⊢ᶠ¹ Γ := e ▸ d

/-- The subset rule, under its `Foundation` `8c6a5c0` name. -/
def contra {Δ Γ : Sequent L} (d : ⊢ᶠ¹ Δ) (h : Δ ⊆ Γ := by simp) : ⊢ᶠ¹ Γ := d.contraction h

/-- Cut freeness. -/
inductive IsCutFree : {Γ : Sequent L} → ⊢ᶠ¹ Γ → Prop
  | identity {k : ℕ} (r : L.Rel k) (v) : IsCutFree (identity r v)
  | verum : IsCutFree verum
  | or {φ ψ : Proposition L} {Γ : Sequent L} {d : ⊢ᶠ¹ φ :: ψ :: Γ} :
      IsCutFree d → IsCutFree d.or
  | and {φ ψ : Proposition L} {Γ : Sequent L} {dφ : ⊢ᶠ¹ φ :: Γ} {dψ : ⊢ᶠ¹ ψ :: Γ} :
      IsCutFree dφ → IsCutFree dψ → IsCutFree (dφ.and dψ)
  | all {φ : Semiproposition L 1} {Γ : Sequent L} {d : ⊢ᶠ¹ Rewriting.free φ :: Γˡ⁺} :
      IsCutFree d → IsCutFree d.all
  | exs {φ : Semiproposition L 1} {Γ : Sequent L} (t) {d : ⊢ᶠ¹ φ/[t] :: Γ} :
      IsCutFree d → IsCutFree d.exs
  | contraction {Δ Γ : Sequent L} {d : ⊢ᶠ¹ Δ} (ss : Δ ⊆ Γ) :
      IsCutFree d → IsCutFree (d.contraction ss)

attribute [simp] IsCutFree.identity IsCutFree.verum

variable {Γ Δ : Sequent L}

@[simp] lemma isCutFree_or_iff {φ ψ : Proposition L} {d : ⊢ᶠ¹ φ :: ψ :: Γ} :
    IsCutFree d.or ↔ IsCutFree d := ⟨by rintro ⟨⟩; assumption, .or⟩

@[simp] lemma isCutFree_and_iff {φ ψ : Proposition L} {dφ : ⊢ᶠ¹ φ :: Γ} {dψ : ⊢ᶠ¹ ψ :: Γ} :
    IsCutFree (dφ.and dψ) ↔ IsCutFree dφ ∧ IsCutFree dψ :=
  ⟨by rintro ⟨⟩; constructor <;> assumption, by intro ⟨hφ, hψ⟩; exact hφ.and hψ⟩

@[simp] lemma isCutFree_all_iff {φ : Semiproposition L 1} {d : ⊢ᶠ¹ Rewriting.free φ :: Γˡ⁺} :
    IsCutFree d.all ↔ IsCutFree d := ⟨by rintro ⟨⟩; assumption, .all⟩

@[simp] lemma isCutFree_exs_iff {φ : Semiproposition L 1} {t : SyntacticTerm L}
    {d : ⊢ᶠ¹ φ/[t] :: Γ} : IsCutFree d.exs ↔ IsCutFree d :=
  ⟨by rintro ⟨⟩; assumption, .exs t⟩

@[simp] lemma isCutFree_contraction_iff {d : ⊢ᶠ¹ Δ} {ss : Δ ⊆ Γ} :
    IsCutFree (d.contraction ss) ↔ IsCutFree d := ⟨by rintro ⟨⟩; assumption, .contraction _⟩

@[simp] lemma IsCutFree.cast {d : ⊢ᶠ¹ Γ} {e : Γ = Δ} :
    IsCutFree (FinDerivation.cast d e) ↔ IsCutFree d := by rcases e; rfl

@[simp] lemma IsCutFree.not_cut {φ : Proposition L} (dp : ⊢ᶠ¹ φ :: Γ) (dn : ⊢ᶠ¹ (∼φ) :: Δ) :
    ¬IsCutFree (dp.cut dn) := by
  intro h
  refine h.rec
    (motive := fun {_} d _ =>
      match d with
      | .cut _ _ => False
      | _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp

/-! ### The translation from upstream's multiset calculus -/

private lemma mem_of_rep {Γ : Sequent L} {Δ : LK.Sequent L}
    (h : (Γ : LK.Sequent L) = Δ) {φ : Proposition L} (hφ : φ ∈ Δ) : φ ∈ Γ := by
  rw [← h] at hφ; simpa using hφ

/-- **Upstream's derivations translate into the list calculus.**  Every
`weakening` and `contraction` node becomes an instance of the subset rule. -/
noncomputable def ofDerivation : {Δ : LK.Sequent L} → (d : ⊢ᴸᴷ¹ Δ) → (Γ : Sequent L) →
    (Γ : LK.Sequent L) = Δ → ⊢ᶠ¹ Γ
  | _, LK.Derivation.identity r v, Γ, hΓ =>
      (identity r v).contraction (by
        intro φ hφ
        rcases List.mem_cons.mp hφ with rfl | hφ
        · exact mem_of_rep hΓ (by simp)
        · rcases List.mem_cons.mp hφ with rfl | hφ
          · exact mem_of_rep hΓ (by simp)
          · simp at hφ)
  | _, LK.Derivation.verum, Γ, hΓ =>
      verum.contraction (by
        intro φ hφ
        rcases List.mem_cons.mp hφ with rfl | hφ
        · exact mem_of_rep hΓ (by simp)
        · simp at hφ)
  | _, @LK.Derivation.weakening _ Γ₀ φ d, Γ, hΓ =>
      (ofDerivation d Γ₀.toList (by simp)).contraction (by
        intro ψ hψ
        exact mem_of_rep hΓ (by simp; left; simpa using hψ))
  | _, @LK.Derivation.contraction _ Γ₀ φ d, Γ, hΓ =>
      (ofDerivation d (Γ₀ + ⦃φ, φ⦄).toList (by simp)).contraction (by
        intro ψ hψ
        have : ψ ∈ Γ₀ + ⦃φ, φ⦄ := by simpa using hψ
        refine mem_of_rep hΓ ?_
        simp only [Multiset.mem_add] at this ⊢
        rcases this with h | h
        · exact Or.inl h
        · simp_all)
  | _, @LK.Derivation.or _ Γ₀ φ ψ d, Γ, hΓ =>
      have ih : ⊢ᶠ¹ φ :: ψ :: Γ₀.toList :=
        ofDerivation d (φ :: ψ :: Γ₀.toList) (by
          simp only [coe_sequent_cons₂, Multiset.coe_toList])
      ih.or.contraction (by
        intro χ hχ
        rcases List.mem_cons.mp hχ with rfl | hχ
        · exact mem_of_rep hΓ (by simp)
        · exact mem_of_rep hΓ (by simp [(by simpa using hχ : χ ∈ Γ₀)]))
  | _, @LK.Derivation.and _ Γ₀ φ ψ dp dq, Γ, hΓ =>
      have ihp : ⊢ᶠ¹ φ :: Γ₀.toList :=
        ofDerivation dp (φ :: Γ₀.toList) (by
          simp only [coe_sequent_cons, Multiset.coe_toList])
      have ihq : ⊢ᶠ¹ ψ :: Γ₀.toList :=
        ofDerivation dq (ψ :: Γ₀.toList) (by
          simp only [coe_sequent_cons, Multiset.coe_toList])
      (ihp.and ihq).contraction (by
        intro χ hχ
        rcases List.mem_cons.mp hχ with rfl | hχ
        · exact mem_of_rep hΓ (by simp)
        · exact mem_of_rep hΓ (by simp [(by simpa using hχ : χ ∈ Γ₀)]))
  | _, @LK.Derivation.all _ Γ₀ φ d, Γ, hΓ =>
      have ih : ⊢ᶠ¹ Rewriting.free φ :: (Γ₀.toList)ˡ⁺ :=
        ofDerivation d (Rewriting.free φ :: (Γ₀.toList)ˡ⁺) (by
          simp only [coe_sequent_cons, coe_sequent_lshifts, Multiset.coe_toList])
      ih.all.contraction (by
        intro χ hχ
        rcases List.mem_cons.mp hχ with rfl | hχ
        · exact mem_of_rep hΓ (by simp)
        · exact mem_of_rep hΓ (by simp [(by simpa using hχ : χ ∈ Γ₀)]))
  | _, @LK.Derivation.exs _ Γ₀ φ t d, Γ, hΓ =>
      have ih : ⊢ᶠ¹ φ/[t] :: Γ₀.toList :=
        ofDerivation d (φ/[t] :: Γ₀.toList) (by
          simp only [coe_sequent_cons, Multiset.coe_toList])
      ih.exs.contraction (by
        intro χ hχ
        rcases List.mem_cons.mp hχ with rfl | hχ
        · exact mem_of_rep hΓ (by simp)
        · exact mem_of_rep hΓ (by simp [(by simpa using hχ : χ ∈ Γ₀)]))
  | _, @LK.Derivation.cut _ Γ₀ φ Δ₀ dp dn, Γ, hΓ =>
      have ihp : ⊢ᶠ¹ φ :: Γ₀.toList :=
        ofDerivation dp (φ :: Γ₀.toList) (by
          simp only [coe_sequent_cons, Multiset.coe_toList])
      have ihn : ⊢ᶠ¹ (∼φ) :: Δ₀.toList :=
        ofDerivation dn ((∼φ) :: Δ₀.toList) (by
          simp only [coe_sequent_cons, Multiset.coe_toList])
      (ihp.cut ihn).contraction (by
        intro χ hχ
        rcases List.mem_append.mp hχ with h | h
        · exact mem_of_rep hΓ (by simp [(by simpa using h : χ ∈ Γ₀)])
        · exact mem_of_rep hΓ (by simp [(by simpa using h : χ ∈ Δ₀)]))

/-- **The translation preserves cut freeness.** -/
theorem isCutFree_ofDerivation :
    ∀ {Δ : LK.Sequent L} {d : ⊢ᴸᴷ¹ Δ}, LK.Derivation.IsCutFree d →
      ∀ (Γ : Sequent L) (hΓ : (Γ : LK.Sequent L) = Δ), IsCutFree (ofDerivation d Γ hΓ) := by
  intro Δ d h
  induction h with
  | identity r v => intro Γ hΓ; exact (IsCutFree.identity r v).contraction _
  | verum => intro Γ hΓ; exact IsCutFree.verum.contraction _
  | @or φ ψ Γ₀ d _ ih => intro Γ hΓ; exact ((ih _ _).or).contraction _
  | @and φ Γ₀ ψ dφ dψ _ _ ihφ ihψ =>
      intro Γ hΓ; exact ((ihφ _ _).and (ihψ _ _)).contraction _
  | @all Γ₀ φ d _ ih => intro Γ hΓ; exact ((ih _ _).all).contraction _
  | @exs Γ₀ φ t d _ ih => intro Γ hΓ; exact ((ih _ _).exs t).contraction _
  | @contraction Γ₀ φ d _ ih => intro Γ hΓ; exact (ih _ _).contraction _
  | @weakening Γ₀ d φ _ ih => intro Γ hΓ; exact (ih _ _).contraction _

/-! ### Back into upstream's multiset calculus -/

open Classical in
/-- **Every list-calculus derivation is an upstream one.**  The subset rule is
discharged by upstream's `Structural.ofSubset`, so nothing is assumed here
either; the two calculi derive the same sequents. -/
theorem toUpstream : ∀ {Γ : Sequent L}, ⊢ᶠ¹ Γ → Nonempty (⊢ᴸᴷ¹ (Γ : LK.Sequent L)) := by
  intro Γ d
  induction d with
  | identity r v =>
      exact ⟨LK.Derivation.cast (LK.Derivation.identity r v) (coe_sequent_pair _ _).symm⟩
  | verum => exact ⟨LK.Derivation.cast LK.Derivation.verum (coe_sequent_singleton _).symm⟩
  | @cut φ Γ₀ Δ₀ _ _ ihp ihn =>
      refine ⟨?_⟩
      have dp : ⊢ᴸᴷ¹ (Γ₀ : LK.Sequent L) + ⦃φ⦄ :=
        LK.Derivation.cast ihp.some (coe_sequent_cons φ Γ₀)
      have dn : ⊢ᴸᴷ¹ (Δ₀ : LK.Sequent L) + ⦃∼φ⦄ :=
        LK.Derivation.cast ihn.some (coe_sequent_cons (∼φ) Δ₀)
      exact LK.Derivation.cast (dp.cut dn) (coe_sequent_append _ _).symm
  | @contraction Δ₀ Γ₀ _ ss ih =>
      exact ih.map fun d =>
        Structural.ofSubset (Multiset.Traversal.ofList Δ₀) (Multiset.Traversal.ofList Γ₀) d
          (Multiset.subset_iff.mpr fun φ hφ => by simpa using ss (by simpa using hφ))
  | @or φ ψ Γ₀ _ ih =>
      refine ih.map fun d => ?_
      have d' : ⊢ᴸᴷ¹ (Γ₀ : LK.Sequent L) + ⦃φ, ψ⦄ :=
        LK.Derivation.cast d (coe_sequent_cons₂ φ ψ Γ₀)
      exact LK.Derivation.cast d'.or (coe_sequent_cons _ _).symm
  | @and φ Γ₀ ψ _ _ ihp ihq =>
      refine ⟨?_⟩
      have dp : ⊢ᴸᴷ¹ (Γ₀ : LK.Sequent L) + ⦃φ⦄ :=
        LK.Derivation.cast ihp.some (coe_sequent_cons φ Γ₀)
      have dq : ⊢ᴸᴷ¹ (Γ₀ : LK.Sequent L) + ⦃ψ⦄ :=
        LK.Derivation.cast ihq.some (coe_sequent_cons ψ Γ₀)
      exact LK.Derivation.cast (dp.and dq) (coe_sequent_cons _ _).symm
  | @all Γ₀ φ _ ih =>
      refine ih.map fun d => ?_
      have d' : ⊢ᴸᴷ¹ ((Γ₀ : LK.Sequent L))⁺ + ⦃Rewriting.free φ⦄ :=
        LK.Derivation.cast d (by rw [coe_sequent_cons, coe_sequent_lshifts])
      exact LK.Derivation.cast d'.all (coe_sequent_cons _ _).symm
  | @exs φ t Γ₀ _ ih =>
      refine ih.map fun d => ?_
      have d' : ⊢ᴸᴷ¹ (Γ₀ : LK.Sequent L) + ⦃φ/[t]⦄ :=
        LK.Derivation.cast d (coe_sequent_cons _ Γ₀)
      exact LK.Derivation.cast (d'.exs (t := t)) (coe_sequent_cons _ _).symm

end FinDerivation

end OrdinalAnalysis
