/-
  # `OrdinalAnalysis.CompatArith` -- the old spellings of the arithmetical hierarchy

  Upstream `Foundation` generalised the arithmetical hierarchy to an arbitrary
  bounding-relation set `ℬ` (`FFL.FirstOrder.Bounding.Hierarchy ℬ Γ s φ`), the
  arithmetical case being `ℬ[<, ℒₒᵣ]`.  With that, the hierarchy-symbol
  notations were re-keyed to carry an `ᴬ` (`𝚺₁` → `𝚺ᴬ₁`, `Γ-[n]` → `Γᴬ-[n]`)
  and made `scoped`, and `Arithmetic.HierarchySymbol` moved to
  `Bounding.HierarchySymbol`.

  Every entry below is a definitional alias or a `notation`, so nothing is
  assumed: the old spellings denote exactly the same terms as before.
-/
import Foundation.FirstOrder.Arithmetic.Schemata
import Foundation.FirstOrder.Arithmetic.HFS

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace OrdinalAnalysis.Compat.FirstOrder.Arithmetic

/-- The hierarchy symbols of *arithmetic*: upstream's `Bounding.HierarchySymbol`
at the arithmetical bounding `ℬ[<, ℒₒᵣ]`. -/
abbrev HierarchySymbol := FFL.FirstOrder.Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]

namespace HierarchySymbol

namespace Definable
export FFL.FirstOrder.Bounding.HierarchySymbol.Definable
  (comp₁ comp₂ comp₃ comp₄ comp₅)

/- Upstream renamed the bounded-quantifier definability lemmas, marking the
arithmetical bounding: `ball_lt`/`ball_le`/`bexs_lt`/`bexs_le` →
`arithmetic_*`. -/
export FFL.FirstOrder.Bounding.HierarchySymbol.Definable
  (arithmetic_ball_lt arithmetic_ball_le arithmetic_bexs_lt arithmetic_bexs_le)

alias ball_lt := arithmetic_ball_lt
alias ball_le := arithmetic_ball_le
alias bexs_lt := arithmetic_bexs_lt
alias bexs_le := arithmetic_bexs_le
end Definable

namespace IsDefinedByWithParam
export FFL.FirstOrder.Bounding.HierarchySymbol.IsDefinedByWithParam (df)
end IsDefinedByWithParam

end HierarchySymbol

/- The old, global spellings `𝚺₀`/`𝚺₁`/… of the hierarchy symbols, which
upstream renamed `𝚺ᴬ₀`/`𝚺ᴬ₁`/… and made `scoped`.

NB: do **not** also restore the general `Γ-[n]`.  Upstream's `Γ-[ℬ, n]` is in
scope wherever the `-Function₁ … via …` notations are (they share the
`FFL.FirstOrder.Bounding` scope), so a second `-[` notation makes every
hierarchy term ambiguous and the elaborator explores both readings at every
nesting level -- `Gentzen/CodedNotation.lean` went from seconds to >13 GB of
elaboration before being OOM-killed.  The `Γ-[m]` call sites are spelled
`Γᴬ-[m]` instead. -/
scoped notation "𝚺₀" => (@FFL.FirstOrder.Bounding.HierarchySymbol.mk _ ℬ[<, ℒₒᵣ] 𝚺 0)
scoped notation "𝚷₀" => (@FFL.FirstOrder.Bounding.HierarchySymbol.mk _ ℬ[<, ℒₒᵣ] 𝚷 0)
scoped notation "𝚫₀" => (@FFL.FirstOrder.Bounding.HierarchySymbol.mk _ ℬ[<, ℒₒᵣ] 𝚫 0)
scoped notation "𝚺₁" => (@FFL.FirstOrder.Bounding.HierarchySymbol.mk _ ℬ[<, ℒₒᵣ] 𝚺 1)
scoped notation "𝚷₁" => (@FFL.FirstOrder.Bounding.HierarchySymbol.mk _ ℬ[<, ℒₒᵣ] 𝚷 1)
scoped notation "𝚫₁" => (@FFL.FirstOrder.Bounding.HierarchySymbol.mk _ ℬ[<, ℒₒᵣ] 𝚫 1)

/-- The old name of the arithmetical hierarchy predicate. -/
abbrev Hierarchy {L : Language} [L.LT] {ξ : Type*} {n : ℕ}
    (Γ : Polarity) (s : ℕ) (φ : Semiformula L ξ n) : Prop :=
  FFL.FirstOrder.Bounding.Hierarchy ℬ[<, L] Γ s φ

/-- The old name of `Hierarchy 𝚺 0`. -/
abbrev DeltaZero {L : Language} [L.LT] {ξ : Type*} {n : ℕ} (φ : Semiformula L ξ n) : Prop :=
  Hierarchy 𝚺 0 φ

namespace Hierarchy
export FFL.FirstOrder.Bounding.Hierarchy
  (rew exs and_iff or_iff imp_iff sigma_of_sigma_ex)
end Hierarchy

end OrdinalAnalysis.Compat.FirstOrder.Arithmetic
