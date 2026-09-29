/-
  The tower's zero and successor laws, lifted to the second-order syntax
  without reference to any set — the arithmetic half of the tower-depth
  induction for the columns of an omega-jump.

  `Gentzen/VeblenTower.lean`'s `Tower(u, k, c)` (a tower of `omega`-exponentials
  of height `k` over `c`) never mentions the fresh predicate `X`, so its zero
  and successor laws (`concrete_towerZero`, `concrete_towerSucc`) lift to `ACA`
  at *any* `toSOAtB` witness, in particular `segWitness`
  (`ACA/TI.lean`'s arithmetical placeholder, already used by
  `ACA/TowerInduction.lean`'s own `towerSO`/`omegaPowSO`, which this file
  reuses unchanged).

  These are the tower laws of the tower-depth induction along the columns of an
  omega-jump `Y`: with `Z = column_0 Y`, the induction on the tower depth `d` for
  `theta(d) := forall c u (Tower(u, d, c) -> TIupto(c, column_d Y) ->
  TIupto(u, column_0 Y))` needs no second-order quantifier inside `theta` at
  all (unlike `ACA/TowerInduction.lean`'s `∀²X TI(c, X)`, since `column_d Y` is
  a single already-given set for each `d`, not a universally quantified one).
  The induction itself is carried out in `ACA/OmegaJumpInduction.lean`, inside
  `PA[X]` with the step condition of the omega-jump as a hypothesis.
-/
import OrdinalAnalysis.ACA.OmegaJumpExt
import OrdinalAnalysis.ACA.TowerInduction

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open FFL FFL.SecondOrder OrdinalAnalysis.Compat OrdinalAnalysis.Compat.SecondOrder
open FFL.SecondOrder.Semiformula
open FFL.SecondOrder.Semiproposition
open scoped FFL.FirstOrder OrdinalAnalysis.Compat.FirstOrder
open OrdinalAnalysis.Gentzen (LX XRel Xat toLX paLX)
open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁)
open OrdinalAnalysis.Gentzen.CodedVeblenJump (addCode₁ omegaPowCode₁)

/-! ### `toSOAt` through the outer quantifiers

**W9.**  `exact h` at the end of each theorem below used to close the goal by
definitional unfolding of `toSOAt`/`toSOAtB` — a structural recursion on the
formula — *at a concrete coded formula*.  The elaborator does that in
milliseconds; the v4.34 kernel needs >14 GB for it.  Stating the two or three
`∀¹`-steps as `rfl` lemmas at a **variable** matrix keeps the recursion folded. -/

private theorem toSOAt_all₂ {n : ℕ} (χ : FirstOrder.Semiformula LX ℕ (n + 2)) :
    toSOAt segWitness (∀¹ (∀¹ χ)) = ∀¹ (∀¹ (toSOAtB segWitness χ)) := by
  show toSOAtB segWitness (∀¹ (∀¹ χ)) = _
  rw [toSOAtB_all, toSOAtB_all]

private theorem toSOAt_all₃ {n : ℕ} (χ : FirstOrder.Semiformula LX ℕ (n + 3)) :
    toSOAt segWitness (∀¹ (∀¹ (∀¹ χ))) = ∀¹ (∀¹ (∀¹ (toSOAtB segWitness χ))) := by
  show toSOAtB segWitness (∀¹ (∀¹ (∀¹ χ))) = _
  rw [toSOAtB_all, toSOAtB_all, toSOAtB_all]

/-! ### The tower's zero and successor laws, lifted (no `X` involved) -/

theorem towerZero_lifted :
    Provable ACA
      (∀¹ (∀¹ (toSOAtB segWitness
        (∼(Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
            (#0 : FirstOrder.Semiterm LX ℕ 2) ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 2) #1) ⋎
          (“#0 = #1” : FirstOrder.Semiformula LX ℕ 2))))) := by
  have h := lift_paLX₀ segWitness arith_segWitness Gentzen.VeblenTower.concrete_towerZero
  unfold Gentzen.VeblenTower.towerZeroStatement at h
  have hfv : (Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
      (#0 : FirstOrder.Semiterm LX ℕ 2) ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 2) #1).freeVariables
        = ∅ :=
    TowerSyntax.freeVariables_towerAt (by simp) (by simp) (by simp)
  have hfvEq : (“#0 = #1” : FirstOrder.Semiformula LX ℕ 2).freeVariables = ∅ := by
    rw [FirstOrder.Semiformula.Operator.eq_def, FirstOrder.Semiformula.freeVariables_rel]
    decide
  rw [TowerSyntax.emb_univCl_of_closed (by simp [hfv, hfvEq]), toSOAt_all₂] at h
  exact h

/-- The matrix of the successor law is closed.  **W9**: the `freeVariables` read-off is
spelled with `rw`, and pulled out of `towerSucc_lifted` so that the kernel checks it on
its own (an inline `by simp` here costs >12 GB *in the kernel*). -/
private theorem freeVariables_towerSuccBody :
    ((∼(Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
        (#0 : FirstOrder.Semiterm LX ℕ 3) (‘(#1 + 1)’ : FirstOrder.Semiterm LX ℕ 3) #2) ⋎
      (∃¹ (Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
          (#0 : FirstOrder.Semiterm LX ℕ 4) #2 #3 ⋏
        Gentzen.omegaPowAt omegaPowCode₁ (#1 : FirstOrder.Semiterm LX ℕ 4) #0))) :
      FirstOrder.Semiformula LX ℕ 3).freeVariables = ∅ := by
  have hfv1 : FirstOrder.Semiformula.freeVariables (Gentzen.VeblenTower.towerAt
      Gentzen.VeblenTower.towerCode₁
      (#0 : FirstOrder.Semiterm LX ℕ 3) (‘(#1 + 1)’ : FirstOrder.Semiterm LX ℕ 3) #2) = ∅ :=
    TowerSyntax.freeVariables_towerAt (by simp) (by simp) (by simp)
  have hfv2 : FirstOrder.Semiformula.freeVariables (Gentzen.VeblenTower.towerAt
      Gentzen.VeblenTower.towerCode₁
      (#0 : FirstOrder.Semiterm LX ℕ 4) #2 #3) = ∅ :=
    TowerSyntax.freeVariables_towerAt (by simp) (by simp) (by simp)
  have hfv3 : FirstOrder.Semiformula.freeVariables (Gentzen.omegaPowAt omegaPowCode₁
      (#1 : FirstOrder.Semiterm LX ℕ 4) #0) = ∅ :=
    TowerSyntax.freeVariables_omegaPowAt (by simp) (by simp)
  rw [FirstOrder.Semiformula.freeVariables_or, FirstOrder.Semiformula.freeVariables_not, hfv1,
    FirstOrder.Semiformula.freeVariables_exs, FirstOrder.Semiformula.freeVariables_and,
    hfv2, hfv3, Finset.union_empty, Finset.union_empty]

private theorem freeVariables_towerSuccAll :
    ((∀¹ (∀¹ (∀¹ (∼(Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
        (#0 : FirstOrder.Semiterm LX ℕ 3) (‘(#1 + 1)’ : FirstOrder.Semiterm LX ℕ 3) #2) ⋎
      (∃¹ (Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
          (#0 : FirstOrder.Semiterm LX ℕ 4) #2 #3 ⋏
        Gentzen.omegaPowAt omegaPowCode₁ (#1 : FirstOrder.Semiterm LX ℕ 4) #0)))))) :
      FirstOrder.Semiformula LX ℕ 0).freeVariables = ∅ := by
  rw [FirstOrder.Semiformula.freeVariables_all, FirstOrder.Semiformula.freeVariables_all,
    FirstOrder.Semiformula.freeVariables_all]
  exact freeVariables_towerSuccBody

theorem towerSucc_lifted :
    Provable ACA
      (∀¹ (∀¹ (∀¹ (toSOAtB segWitness
        (∼(Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
            (#0 : FirstOrder.Semiterm LX ℕ 3) (‘(#1 + 1)’ : FirstOrder.Semiterm LX ℕ 3) #2) ⋎
          (∃¹ (Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
              (#0 : FirstOrder.Semiterm LX ℕ 4) #2 #3 ⋏
            Gentzen.omegaPowAt omegaPowCode₁ (#1 : FirstOrder.Semiterm LX ℕ 4) #0))))))) := by
  have h := lift_paLX₀ segWitness arith_segWitness
    Gentzen.VeblenTower.concrete_towerSucc
  unfold Gentzen.VeblenTower.towerSuccStatement at h
  rw [TowerSyntax.emb_univCl_of_closed freeVariables_towerSuccAll, toSOAt_all₃] at h
  exact h

end OrdinalAnalysis.ACA
