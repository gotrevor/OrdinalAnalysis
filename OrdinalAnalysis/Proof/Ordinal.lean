/-
  Ordinal assignment to LK derivations.

  Foundation's `FinDerivation.height` is a natural number, which is enough to
  induct on but not enough to survive cut reduction: eliminating a cut can
  multiply the height, so ℕ-height is not a decreasing measure.  The ordinal
  assigned here is: successor at every unary rule, natural sum at every binary
  rule.  The natural sum is essential — ordinary ordinal addition is not
  commutative, so it would let one premise of a cut absorb the other.
-/
import OrdinalAnalysis.FinLK
import OrdinalAnalysis.Ordinal.NaturalSum
import OrdinalAnalysis.Proof.CutRank

namespace OrdinalAnalysis

open FFL FFL.FirstOrder OrdinalAnalysis.FinDerivation OrdinalAnalysis.Compat OrdinalAnalysis.Compat.FirstOrder

variable {L : Language}

/-- The ordinal height of a derivation, as a notation below `ε₀`. -/
def ord {Δ : Sequent L} : ⊢ᶠ¹ Δ → ONote
  | FinDerivation.identity _ _ => 0
  | FinDerivation.verum => 0
  | FinDerivation.cut dp dn => nadd (ord dp) (ord dn) + 1
  | FinDerivation.contraction d _ => ord d + 1
  | FinDerivation.or d => ord d + 1
  | FinDerivation.and dp dq => nadd (ord dp) (ord dq) + 1
  | FinDerivation.all d => ord d + 1
  | FinDerivation.exs d => ord d + 1

@[simp] theorem ord_identity {k : ℕ} (r : L.Rel k) (v) :
    ord (FinDerivation.identity r v) = 0 := by simp [ord]

@[simp] theorem ord_verum :
    ord (FinDerivation.verum : ⊢ᶠ¹ ([⊤] : Sequent L)) = 0 := by simp [ord]

@[simp] theorem ord_or {φ ψ : Proposition L} {Γ : Sequent L} (d : ⊢ᶠ¹ φ :: ψ :: Γ) :
    ord d.or = ord d + 1 := by simp [ord]

@[simp] theorem ord_contraction {Δ Γ : Sequent L} (d : ⊢ᶠ¹ Δ) (ss : Δ ⊆ Γ) :
    ord (d.contraction ss) = ord d + 1 := by simp [ord]

@[simp] theorem ord_and {φ ψ : Proposition L} {Γ : Sequent L}
    (dp : ⊢ᶠ¹ φ :: Γ) (dq : ⊢ᶠ¹ ψ :: Γ) :
    ord (dp.and dq) = nadd (ord dp) (ord dq) + 1 := by simp [ord]

@[simp] theorem ord_cut {φ : Proposition L} {Γ Δ : Sequent L}
    (dp : ⊢ᶠ¹ φ :: Γ) (dn : ⊢ᶠ¹ ∼φ :: Δ) :
    ord (dp.cut dn) = nadd (ord dp) (ord dn) + 1 := by simp [ord]

/-- Every derivation is assigned a normal-form notation, so `repr (ord d)` is a
genuine ordinal. -/
instance ord_nf {Δ : Sequent L} : ∀ d : ⊢ᶠ¹ Δ, ONote.NF (ord d)
  | FinDerivation.identity _ _ => by rw [ord_identity]; infer_instance
  | FinDerivation.verum => by rw [ord_verum]; infer_instance
  | FinDerivation.cut dp dn => by
      rw [ord_cut]; have := ord_nf dp; have := ord_nf dn; infer_instance
  | FinDerivation.contraction d _ => by
      rw [ord_contraction]; have := ord_nf d; infer_instance
  | FinDerivation.or d => by rw [ord_or]; have := ord_nf d; infer_instance
  | FinDerivation.and dp dq => by
      rw [ord_and]; have := ord_nf dp; have := ord_nf dq; infer_instance
  | FinDerivation.all d => by simp only [ord]; have := ord_nf d; infer_instance
  | FinDerivation.exs d => by simp only [ord]; have := ord_nf d; infer_instance

end OrdinalAnalysis
