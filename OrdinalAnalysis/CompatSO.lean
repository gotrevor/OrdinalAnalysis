/-
  # `OrdinalAnalysis.CompatSO` -- list sequents for the second-order calculus

  The first-order story of `Compat.lean`, repeated for `Foundation`'s
  second-order syntax: between `8c6a5c0` and `bde9bc28` upstream's
  `SecondOrder.Sequent` became `SecondOrder.LK.Sequent`, a *multiset*.

  `ACA/LK.lean`'s restricted calculus (arithmetical comprehension only) is a
  list-sequent calculus, and every inversion and reduction lemma of `ACAOmega`
  reads its principal formula off the head of the sequent.  So the list sequent
  type and its two shift operations live here, verbatim from `8c6a5c0`, together
  with the coercions into upstream's multiset sequents; `ACA/LK.lean`'s `toFull`
  translates the calculus itself.
-/
import Foundation.SecondOrder.LK.Basic
import OrdinalAnalysis.Compat

open FFL FFL.SecondOrder
open FFL.FirstOrder (Language)

namespace OrdinalAnalysis.Compat.SecondOrder

variable {L : Language}

/-- A second-order sequent: a *list* of propositions (upstream now uses a
multiset; see the module docstring). -/
abbrev Sequent (L : Language) := List (Proposition L)

namespace Sequent

/-- Shift the free first-order variables of every formula in the sequent. -/
def shift₀ (Γ : Sequent L) : Sequent L := Γ.map Semiproposition.shift₀

@[simp] lemma shift₀_nil : shift₀ ([] : Sequent L) = [] := rfl

@[simp] lemma shift₀_cons (φ : Proposition L) (Γ : Sequent L) :
    shift₀ (φ :: Γ) = Semiproposition.shift₀ φ :: shift₀ Γ := rfl

/-- Shift the free second-order variables of every formula in the sequent. -/
def shift₁ (Γ : Sequent L) : Sequent L := Γ.map Semiproposition.shift₁

@[simp] lemma shift₁_nil : shift₁ ([] : Sequent L) = [] := rfl

@[simp] lemma shift₁_cons (φ : Proposition L) (Γ : Sequent L) :
    shift₁ (φ :: Γ) = Semiproposition.shift₁ φ :: shift₁ Γ := rfl

@[simp] lemma tilde_nil : ∼([] : Sequent L) = [] := rfl

@[simp] lemma tilde_cons (φ : Proposition L) (Γ : Sequent L) :
    ∼(φ :: Γ) = ∼φ :: ∼Γ := rfl

/-! ### Coercions into upstream's multiset sequents -/

@[simp] lemma coe_cons (φ : Proposition L) (Γ : Sequent L) :
    ((φ :: Γ : Sequent L) : LK.Sequent L) = (Γ : LK.Sequent L) + ⦃φ⦄ := by
  rw [show ((φ :: Γ : Sequent L) : LK.Sequent L) = φ ::ₘ (Γ : LK.Sequent L) from rfl,
    ← Multiset.singleton_add]
  exact Multiset.add_comm _ _

@[simp] lemma coe_cons₂ (φ ψ : Proposition L) (Γ : Sequent L) :
    ((φ :: ψ :: Γ : Sequent L) : LK.Sequent L) = (Γ : LK.Sequent L) + ⦃φ, ψ⦄ := by
  rw [coe_cons, coe_cons]
  show (Γ : LK.Sequent L) + ⦃ψ⦄ + ⦃φ⦄ = _
  rw [show (⦃φ, ψ⦄ : LK.Sequent L) = ⦃ψ⦄ + ⦃φ⦄ from by simp [Multiset.add_comm]]
  abel

lemma coe_pair (φ ψ : Proposition L) :
    (([φ, ψ] : Sequent L) : LK.Sequent L) = ⦃φ, ψ⦄ := by simpa using coe_cons₂ φ ψ []

lemma coe_singleton (φ : Proposition L) :
    (([φ] : Sequent L) : LK.Sequent L) = ⦃φ⦄ := by simpa using coe_cons φ []

@[simp] lemma coe_shift₀ (Γ : Sequent L) :
    ((shift₀ Γ : Sequent L) : LK.Sequent L) = LK.Sequent.shift₀ ((Γ : LK.Sequent L)) := by
  simp [shift₀, LK.Sequent.shift₀]

@[simp] lemma coe_shift₁ (Γ : Sequent L) :
    ((shift₁ Γ : Sequent L) : LK.Sequent L) = LK.Sequent.shift₁ ((Γ : LK.Sequent L)) := by
  simp [shift₁, LK.Sequent.shift₁]

end Sequent

end OrdinalAnalysis.Compat.SecondOrder
