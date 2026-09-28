/-
  # `OrdinalAnalysis.Compat` -- list sequents over `Foundation`'s current syntax

  Upstream `Foundation` reshaped its one-sided LK calculus between `8c6a5c0`
  (which this development was written against) and `bde9bc28`: `Sequent L` went
  from `List (Proposition L)` to `Multiset (Proposition L)` (renamed
  `LK.Sequent`), and `Rewriting.shifts` moved with it.

  The ordinal analysis here is an induction over *sequent syntax*: the inversion
  lemmas, the cut-reduction steps and the ordinal assignment all read the
  principal formula off the head of the sequent, and `BoundedDerivable` /
  `OmegaDerivable` are indexed by list sequents throughout.  Multisets have no
  head, so that is not a rename one can chase through call sites.

  This file therefore keeps the *list* sequent type and the list `shifts`
  operation -- verbatim from `Foundation` `8c6a5c0` -- while everything else
  (formulas, rewriting, derivations, theories, provability) hangs off upstream
  directly.  The bridge files translate between the two sequent shapes, so the
  audit surface is still upstream's own `⊢ᴸᴷ¹`.

  Only the notation has to change: upstream's `Γ⁺` is `scoped` in
  `FFL.FirstOrder`, so the list version is spelled `Γˡ⁺`.
-/
import Foundation.FirstOrder.LK.CutFree

namespace FFL.FirstOrder

variable {L : Language}

/-- A sequent of the one-sided calculus analysed here: a *list* of propositions
(upstream now uses a multiset; see the module docstring). -/
abbrev Sequent (L : Language) := List (Proposition L)

/-- `Rewriting.shifts` for list sequents: shift every free variable of every
formula in the list. -/
def Rewriting.lshifts {F : ℕ → Type*} {n : ℕ} [LCWQ F] [Rewriting L ℕ F ℕ F]
    (Γ : List (F n)) : List (F n) := Γ.map Rewriting.shift

@[inherit_doc] postfix:max "ˡ⁺" => FFL.FirstOrder.Rewriting.lshifts

namespace Rewriting

variable {F : ℕ → Type*} {n : ℕ} [LCWQ F] [Rewriting L ℕ F ℕ F]

@[simp] lemma lshifts_nil : ([] : List (F n))ˡ⁺ = [] := rfl

@[simp] lemma lshifts_cons (φ : F n) (Γ : List (F n)) :
    (φ :: Γ)ˡ⁺ = shift φ :: Γˡ⁺ := by simp [lshifts]

@[simp] lemma lshifts_append (Γ Δ : List (F n)) : (Γ ++ Δ)ˡ⁺ = Γˡ⁺ ++ Δˡ⁺ := by
  simp [lshifts]

@[simp] lemma lshifts_neg (Γ : List (F n)) : (∼Γ)ˡ⁺ = ∼(Γˡ⁺) := by
  simp only [lshifts, List.tilde_def, List.map_map]
  exact List.map_congr_left fun _ _ ↦ by simp

@[simp] lemma mem_lshifts_iff {φ : F n} {Γ : List (F n)} :
    φ ∈ Γˡ⁺ ↔ ∃ ψ ∈ Γ, shift ψ = φ := by simp [lshifts]

lemma lshifts_subset {Γ Δ : List (F n)} (h : Γ ⊆ Δ) : Γˡ⁺ ⊆ Δˡ⁺ :=
  List.map_subset _ h

end Rewriting

namespace Sequent

open Semiformula

/-- A fresh free variable for the sequent. -/
def newVar (Γ : Sequent L) : ℕ := (Γ.map Semiformula.fvSup).foldr max 0

lemma not_fvar?_newVar {φ : Proposition L} {Γ : Sequent L} (h : φ ∈ Γ) :
    ¬FVar? φ Γ.newVar :=
  not_fvar?_of_lt_fvSup φ
    (by simp only [newVar]; exact List.le_max_of_le (List.mem_map_of_mem h) (by simp))

@[simp] lemma lcHom_comm {ξ : Type*} {Γ : List (Formula L ξ)}
    (f : Formula L ξ →ˡᶜ Proposition L) : (∼Γ).map f = ∼Γ.map f := by
  simp [List.tilde_def]

/-- The sequent contains a formula together with its negation. -/
def IsClosed (Γ : Sequent L) : Prop := ∃ φ ∈ Γ, ∼φ ∈ Γ

/-- Embed a list of sentences as a sequent. -/
def embed (Γ : List (Sentence L)) : Sequent L := List.map Rewriting.emb Γ

@[simp] lemma embed_nil : embed ([] : List (Sentence L)) = [] := rfl

@[simp] lemma embed_cons {φ : Sentence L} {Γ : List (Sentence L)} :
    embed (φ :: Γ) = (↑φ :: embed Γ) := rfl

@[simp] lemma embed_append (Γ Δ : List (Sentence L)) :
    embed (Γ ++ Δ) = embed Γ ++ embed Δ := by simp [embed]

@[simp] lemma embed_shift (Γ : List (Sentence L)) : (embed Γ)ˡ⁺ = embed Γ := by
  simp [embed, Rewriting.lshifts]

end Sequent

end FFL.FirstOrder

/-! ### Bridging list sequents and upstream's multiset sequents

`Foundation`'s derivations are indexed by multiset sequents, the calculi analysed
here by list sequents.  These are the coercion lemmas that translate between the
two, plus the membership bookkeeping the bridge files need. -/

namespace FFL.FirstOrder

variable {L : Language}

@[simp] lemma coe_sequent_cons (φ : Proposition L) (Γ : Sequent L) :
    ((φ :: Γ : Sequent L) : LK.Sequent L) = (Γ : LK.Sequent L) + ⦃φ⦄ := by
  rw [show ((φ :: Γ : Sequent L) : LK.Sequent L) = φ ::ₘ (Γ : LK.Sequent L) from rfl,
    ← Multiset.singleton_add]
  exact Multiset.add_comm _ _

@[simp] lemma coe_sequent_append (Γ Δ : Sequent L) :
    ((Γ ++ Δ : Sequent L) : LK.Sequent L) = (Γ : LK.Sequent L) + (Δ : LK.Sequent L) := by
  simp

@[simp] lemma coe_sequent_lshifts (Γ : Sequent L) :
    ((Γˡ⁺ : Sequent L) : LK.Sequent L) = ((Γ : LK.Sequent L))⁺ := by
  simp [Rewriting.lshifts, Rewriting.shifts]

/-- Upstream derivation of the multiset underlying a *list* sequent.  This is
the shape the bridge files use: the derivation is upstream's, the sequent is
written as a list. -/
abbrev ListDerivation (Γ : FFL.FirstOrder.Sequent L) : Type _ :=
  ⊢ᴸᴷ¹ ((Γ : FFL.FirstOrder.Sequent L) : LK.Sequent L)

@[inherit_doc] notation:45 "⊢ᴸᴷˡ " Γ => FFL.FirstOrder.ListDerivation Γ

/-- Every multiset sequent has a list representative. -/
lemma exists_list_rep (Δ : LK.Sequent L) : ∃ Γ : Sequent L, (Γ : LK.Sequent L) = Δ :=
  ⟨Δ.toList, by simp⟩

end FFL.FirstOrder

namespace FFL.FirstOrder.LawfulSyntacticRewriting

variable {L : Language} {n : ℕ} {S : ℕ → Type*} [LCWQ S] [SyntacticRewriting L S S]
  [LawfulSyntacticRewriting L S]

open FFL.FirstOrder.Rewriting

/-- List analogue of upstream's `mem_shifts_iff`. -/
@[simp] lemma mem_lshifts_iff {φ : S n} {Γ : List (S n)} :
    Rewriting.shift φ ∈ Γˡ⁺ ↔ φ ∈ Γ := by
  simp only [lshifts, List.mem_map]
  exact ⟨fun ⟨ψ, hψ, e⟩ ↦ shift_injective e ▸ hψ, fun h ↦ ⟨φ, h, rfl⟩⟩


/-- List analogue of upstream's `shifts_ss`. -/
@[simp] lemma lshifts_ss (Γ Δ : List (S n)) : Γˡ⁺ ⊆ Δˡ⁺ ↔ Γ ⊆ Δ := by
  constructor
  · intro h φ hφ
    have : Rewriting.shift φ ∈ Δˡ⁺ := h (mem_lshifts_iff.mpr hφ)
    exact mem_lshifts_iff.mp this
  · exact Rewriting.lshifts_subset

end FFL.FirstOrder.LawfulSyntacticRewriting

namespace FFL.FirstOrder

variable {L : Language}

@[simp] lemma coe_sequent_cons₂ (φ ψ : Proposition L) (Γ : Sequent L) :
    ((φ :: ψ :: Γ : Sequent L) : LK.Sequent L) = (Γ : LK.Sequent L) + ⦃φ, ψ⦄ := by
  rw [coe_sequent_cons, coe_sequent_cons]
  show (Γ : LK.Sequent L) + ⦃ψ⦄ + ⦃φ⦄ = _
  rw [show (⦃φ, ψ⦄ : LK.Sequent L) = ⦃ψ⦄ + ⦃φ⦄ from by
    simp [Multiset.add_comm]]
  abel

lemma coe_sequent_pair (φ ψ : Proposition L) :
    (([φ, ψ] : Sequent L) : LK.Sequent L) = ⦃φ, ψ⦄ := by
  simpa using coe_sequent_cons₂ φ ψ []

lemma coe_sequent_singleton (φ : Proposition L) :
    (([φ] : Sequent L) : LK.Sequent L) = ⦃φ⦄ := by
  simpa using coe_sequent_cons φ []

end FFL.FirstOrder

/-! ### `provable_iff` with a list of axioms

Upstream's `Theory.Proof.provable_iff` now hands back a *multiset* of axioms and
a multiset sequent.  This is the same statement with the list sequents used here;
it is proved from upstream's, not assumed. -/

namespace FFL.FirstOrder

variable {L : Language}

@[simp] lemma coe_sequent_tilde (Γ : Sequent L) :
    ((∼Γ : Sequent L) : LK.Sequent L) = ∼((Γ : LK.Sequent L)) := by
  simp [List.tilde_def, Multiset.tilde_def]

@[simp] lemma coe_sequent_embed (Γ : List (Sentence L)) :
    ((Sequent.embed Γ : Sequent L) : LK.Sequent L)
      = LK.Sequent.embed ((Γ : Multiset (Sentence L))) := by
  simp [Sequent.embed, LK.Sequent.embed]

namespace Theory.Proof

variable {T : Theory L} {φ : Sentence L}

/-- `provable_iff` with the axioms as a list and a list sequent. -/
lemma provable_iff_list :
    T ⊢ φ ↔ ∃ Γ : List (Sentence L), (∀ ψ ∈ Γ, ψ ∈ T) ∧
      Nonempty (⊢ᴸᴷ¹ (((φ : Proposition L) :: ∼Sequent.embed Γ : Sequent L) : LK.Sequent L)) := by
  rw [provable_iff]
  constructor
  · rintro ⟨Γ, hΓ, ⟨d⟩⟩
    refine ⟨Γ.toList, fun ψ hψ ↦ hΓ ψ (by simpa using hψ), ⟨?_⟩⟩
    refine LK.Derivation.cast d ?_
    rw [coe_sequent_cons, coe_sequent_tilde, coe_sequent_embed, Multiset.coe_toList]
    exact (add_comm _ _)
  · rintro ⟨Γ, hΓ, ⟨d⟩⟩
    refine ⟨(Γ : Multiset (Sentence L)), fun ψ hψ ↦ hΓ ψ (by simpa using hψ), ⟨?_⟩⟩
    refine LK.Derivation.cast d ?_
    rw [coe_sequent_cons, coe_sequent_tilde, coe_sequent_embed]
    exact (add_comm _ _)

end Theory.Proof

end FFL.FirstOrder
