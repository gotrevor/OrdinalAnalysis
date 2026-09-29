/-
  The bridge between Foundation's concrete derivations and the ordinal-indexed
  ones.

  Both directions are needed and neither is deep.

  Forwards, every concrete derivation carries an ordinal height and a cut rank,
  so it can be replayed in the indexed calculus.  This is what lets a theorem of
  a first-order theory — obtained through Foundation's `provable_iff`, which
  turns `T ⊢ φ` into a derivation of `φ` together with negated axioms — be fed
  into cut elimination and come back with a bound.

  Backwards, an indexed derivation forgets its ordinal and its rank and becomes
  a concrete one.  That direction is what makes Foundation's semantics apply to
  everything proved here: soundness, the standard model, and the arithmetic
  hierarchy all live on `Derivation`, and none of them has to be redeveloped.

  The height assigned here is deliberately *not* Foundation's `height : ℕ`.
  Contraction is free — the indexed calculus lets a subset weaken without
  raising the bound — and branching rules take the natural sum rather than the
  maximum, which is what the reduction lemma consumes.
-/
import OrdinalAnalysis.FinLK
import OrdinalAnalysis.Proof.CutElimination
import OrdinalAnalysis.Proof.CutRank
import OrdinalAnalysis.Ordinal.Notation

namespace OrdinalAnalysis

open FFL FFL.FirstOrder OrdinalAnalysis.FinDerivation OrdinalAnalysis.Compat OrdinalAnalysis.Compat.FirstOrder

variable {L : Language}

/-- The ordinal height of a concrete derivation, in any notation system.

Contraction costs nothing, because the indexed calculus absorbs it into the
subset side condition; every other rule pays a successor above the natural sum
of its premises.

The target used to be `NONote`.  It is an arbitrary `[OrdinalNotation O]`
because the replay of `Gentzen/Embed.lean` feeds the infinitary calculus, whose
heights were generalised in `Omega/Calculus.lean`, and the results above `ε₀`
need to replay into a larger notation system.  Taking `O := NONote` — which is
what `BoundedDerivable` below forces, its index still being `NONote` — gives
back exactly the old function, `OrdinalNotation.ofNat 0` being `(0 : NONote)`
and `OrdinalNotation.succ`/`nadd` the `NONote` ones by definition. -/
def ordN {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
    {Δ : Sequent L} : ⊢ᶠ¹ Δ → O
  | FinDerivation.identity _ _ => OrdinalNotation.ofNat 0
  | FinDerivation.verum => OrdinalNotation.ofNat 0
  | FinDerivation.contraction d _ => ordN d
  | FinDerivation.or d => OrdinalNotation.succ (ordN d)
  | FinDerivation.and dp dq => OrdinalNotation.succ (OrdinalNotation.nadd (ordN dp) (ordN dq))
  | FinDerivation.all d => OrdinalNotation.succ (ordN d)
  | FinDerivation.exs d => OrdinalNotation.succ (ordN d)
  | FinDerivation.cut dp dn => OrdinalNotation.succ (OrdinalNotation.nadd (ordN dp) (ordN dn))

namespace BoundedDerivable

/-- **Forwards.**  Every concrete derivation is an indexed one, at its own
height and its own cut rank. -/
theorem ofDerivation {Δ : Sequent L} :
    ∀ d : ⊢ᶠ¹ Δ, BoundedDerivable (cutRank d) (ordN d) Δ
  | FinDerivation.identity rl v => .identity rl v
  | FinDerivation.verum => .verum
  | FinDerivation.contraction d ss => by
      exact .contraction ss (ofDerivation d)
  | FinDerivation.or d => by
      refine .or (NONote.lt_succ _) ?_
      simpa [cutRank] using ofDerivation d
  | FinDerivation.and dp dq => by
      refine .and (NONote.lt_succ_of_le (NONote.le_nadd_left _ _))
        (NONote.lt_succ_of_le (NONote.le_nadd_right _ _)) ?_ ?_
      · exact (ofDerivation dp).mono_rank (by simp [cutRank])
      · exact (ofDerivation dq).mono_rank (by simp [cutRank])
  | FinDerivation.all d => by
      refine .all (NONote.lt_succ _) ?_
      simpa [cutRank] using ofDerivation d
  | FinDerivation.exs d => by
      exact .exs _ (NONote.lt_succ _) (by simpa [cutRank] using ofDerivation d)
  | FinDerivation.cut dp dn => by
      refine .cut ?_ (NONote.lt_succ_of_le (NONote.le_nadd_left _ _))
        (NONote.lt_succ_of_le (NONote.le_nadd_right _ _))
        ((ofDerivation dp).mono_rank (by simp [cutRank]))
        ((ofDerivation dn).mono_rank (by simp [cutRank]))
      simp only [cutRank]
      omega

/-- **Backwards.**  An indexed derivation forgets its ordinal and its rank.

This is what makes Foundation's semantics available: soundness, the standard
model, and everything built on `Derivation` transfers without redevelopment. -/
theorem toDerivation {r : ℕ} :
    ∀ {α : NONote} {Γ : Sequent L}, BoundedDerivable r α Γ → Nonempty (⊢ᶠ¹ Γ) := by
  intro α Γ h
  induction h with
  | identity rl v => exact ⟨FinDerivation.identity rl v⟩
  | verum => exact ⟨FinDerivation.verum⟩
  | or _ _ ih => exact ih.map FinDerivation.or
  | and _ _ _ _ ihp ihq => exact ⟨FinDerivation.and ihp.some ihq.some⟩
  | all _ _ ih => exact ih.map FinDerivation.all
  | exs t _ _ ih => exact ih.map FinDerivation.exs
  | contraction ss _ ih => exact ih.map (fun d => FinDerivation.contraction d ss)
  | cut _ _ _ _ _ ihp ihn => exact ⟨FinDerivation.cut ihp.some ihn.some⟩

/-- The headline corollary: every concrete derivation has a cut-free indexed
counterpart, at a height bounded by an explicit tower of `ω`-powers over its
own height — and that bound is below `ε₀`, because `NONote` is the type of
notations below `ε₀`. -/
theorem cutFree_of_derivation {Δ : Sequent L} (d : ⊢ᶠ¹ Δ) :
    BoundedDerivable 0 (NONote.omegaTower (cutRank d) (ordN d)) Δ :=
  cutElimination _ (ofDerivation d)

/-! ### The same two directions, against upstream's calculus

`FinDerivation` is the list-sequent calculus of `FinLK.lean`; upstream's
`⊢ᴸᴷ¹` has multiset sequents.  `FinDerivation.ofDerivation` and
`FinDerivation.toUpstream` translate, so these two wrappers are the statements
above phrased directly for upstream's derivations. -/

/-- **Forwards, from upstream.**  Every derivation of `Foundation`'s own `⊢ᴸᴷ¹`
has a cut-free indexed counterpart below `ε₀`, on any list representing its end
sequent. -/
theorem cutFree_of_upstreamDerivation {Δ : FFL.FirstOrder.LK.Sequent L}
    (d : ⊢ᴸᴷ¹ Δ) (Γ : Sequent L) (hΓ : (Γ : FFL.FirstOrder.LK.Sequent L) = Δ) :
    BoundedDerivable 0
      (NONote.omegaTower (cutRank (FinDerivation.ofDerivation d Γ hΓ))
        (ordN (FinDerivation.ofDerivation d Γ hΓ))) Γ :=
  cutFree_of_derivation _

/-- **Backwards, into upstream.**  An indexed derivation yields a derivation of
`Foundation`'s own `⊢ᴸᴷ¹`, which is what makes upstream's semantics apply. -/
theorem toUpstreamDerivation {r : ℕ} {α : NONote} {Γ : Sequent L}
    (h : BoundedDerivable r α Γ) :
    Nonempty (⊢ᴸᴷ¹ ((Γ : Sequent L) : FFL.FirstOrder.LK.Sequent L)) :=
  (toDerivation h).elim fun d => FinDerivation.toUpstream d

end BoundedDerivable

end OrdinalAnalysis
