import NCG.Grand.GlobalWellFoundednessExact
import NCG.Grand.PredictiveActionClosureExact
import NCG.Grand.AssemblyRectangularStoppingFrontExact
import NCG.Grand.ContextualRenewalAssociativityExact
import NCG.Grand.PositiveFirstReturnRenewalExact
import NCG.Grand.FiniteWellFoundedScreenRankExact
import NCG.Grand.SourceAnchoredCofinalExact

/-!
# Source-anchored predictive-action alternatives

This module completes the two finite compiler statements whose earlier
formalizations stopped at fixed-screen recurrence.  The first theorem adds the
literal sixth, cofinal-escape branch to the global well-foundedness
alternative.  The second performs the five-anchor failure dispatch and uses
the exact finite recurrence theorem to exclude an infinite nonterminal
history on the passing branch.
-/

namespace NCG
namespace SourceAnchoredPredictiveActionAlternative

open GlobalWellFoundedness
open PredictiveClosure

variable {V : Type*} (step : V → V → Prop)

/-- The complete W1--W6 finite/cofinal alternative.  `CofinalClosed` is the
conclusion supplied by the source-anchored divergent-margin theorem, while
`hescape` records its exact failure witness: a marked history escaping every
certified screen. -/
theorem global_well_foundedness_with_cofinal_escape [Finite V] (source : V)
    (Bellman Holo Anc Circ Sep Flat : V → Prop)
    (Margin Screen Joint CofinalClosed CofinalEscape : Prop)
    (hclassify : ∀ y, IsRecurrent step y → Reaches step source y →
      (Bellman y ∨ Holo y ∨ Anc y) ∨ (Circ y ∨ Sep y ∨ Flat y))
    (hescape : ¬ CofinalClosed → CofinalEscape) :
    (∃ y, Reaches step source y ∧ IsRecurrent step y) ∧
      (((∀ y, IsRecurrent step y → Reaches step source y →
            Bellman y ∨ Holo y ∨ Anc y) ∧
          Margin ∧ Screen ∧ Joint ∧ CofinalClosed) ∨
        (∃ y, IsRecurrent step y ∧ Reaches step source y ∧ Circ y) ∨
        (∃ y, IsRecurrent step y ∧ Reaches step source y ∧ Sep y) ∨
        (∃ y, IsRecurrent step y ∧ Reaches step source y ∧ Flat y) ∨
        (¬Margin ∨ ¬Screen ∨ ¬Joint) ∨ CofinalEscape) := by
  classical
  refine ⟨exists_recurrent_reachable step source, ?_⟩
  by_cases hall : ∀ y, IsRecurrent step y → Reaches step source y →
      Bellman y ∨ Holo y ∨ Anc y
  · by_cases hM : Margin
    · by_cases hS : Screen
      · by_cases hJ : Joint
        · by_cases hC : CofinalClosed
          · exact Or.inl ⟨hall, hM, hS, hJ, hC⟩
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hescape hC)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr hJ))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl hS))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl hM)))))
  · obtain ⟨y, hy⟩ := not_forall.mp hall
    obtain ⟨hrec, hy⟩ := Classical.not_imp.mp hy
    obtain ⟨hreach, hbad⟩ := Classical.not_imp.mp hy
    rcases hclassify y hrec hreach with hgood | hfail
    · exact absurd hgood hbad
    · rcases hfail with hCirc | hSep | hFlat
      · exact Or.inr (Or.inl ⟨y, hrec, hreach, hCirc⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨y, hrec, hreach, hSep⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨y, hrec, hreach, hFlat⟩)))

/-- Complete five-anchor predictive-action compiler.  On the passing branch
the finite head has no strict recurrent cycle, hence the exact recurrence
theorem excludes every infinite nonterminal walk.  Failure of the five
physical anchors is converted, in manuscript order, into the corresponding
source-native witness; an independently retained cofinal escape is the sixth
possible output. -/
theorem source_anchored_predictive_action_closure [Finite V]
    (Tight ActionComplete FirstReturn LocalClosed CofinalClosed : Prop)
    (RemoteFuture ContextMemory LongExcursion Circulation
      UnpaidBoundary CofinalEscape : Prop)
    (hremote : ¬ Tight → RemoteFuture)
    (hcontext : ¬ ActionComplete → ContextMemory)
    (hlong : ¬ FirstReturn → LongExcursion)
    (hcirc : ¬ LocalClosed → Circulation)
    (hboundary : ¬ CofinalClosed → UnpaidBoundary ∨ CofinalEscape)
    (hclosed : LocalClosed → ∀ v : V, ¬ Relation.TransGen step v v) :
    (¬ ∃ w : ℕ → V, IsWalk step w) ∨
      RemoteFuture ∨ ContextMemory ∨ LongExcursion ∨ Circulation ∨
        UnpaidBoundary ∨ CofinalEscape := by
  classical
  by_cases hT : Tight
  · by_cases hA : ActionComplete
    · by_cases hF : FirstReturn
      · by_cases hL : LocalClosed
        · by_cases hC : CofinalClosed
          · exact Or.inl (no_infinite_history_of_closed step (hclosed hL))
          · rcases hboundary hC with hB | hE
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hB)))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hE)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hcirc hL)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (hlong hF))))
    · exact Or.inr (Or.inr (Or.inl (hcontext hA)))
  · exact Or.inr (Or.inl (hremote hT))

end SourceAnchoredPredictiveActionAlternative
end NCG

