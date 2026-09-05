import NCG.Grand.OperatorGraphResolventEulerFunctionalCalculus

/-!
# Reference-shift independence of graph-resolvent heat operators

The heat operator reconstructed from a positive graph resolvent does not depend
on which positive resolvent shift is used as the reference.  Both candidate
operators are norm limits of the same implicit-Euler sequence.
-/

namespace NCG.VaryingHilbert

open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The canonical heat operator obtained from the graph resolvent family is
independent of the positive reference shift. -/
theorem operatorGraphResolventHeat_eq_of_referenceShifts
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F) (R : ℝ → E →L[ℂ] E)
    (hequation : ∀ lam, 0 < lam → ∀ f,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (b c t : ℝ) (hb : 0 < b) (hc : 0 < c) (ht : 0 < t) :
    operatorGraphResolventHeat (R b) b t =
      operatorGraphResolventHeat (R c) c t := by
  exact tendsto_nhds_unique
    (tendsto_scaled_operatorGraphResolvent_succ_pow_heat
      D A R hequation b t hb ht)
    (tendsto_scaled_operatorGraphResolvent_succ_pow_heat
      D A R hequation c t hc ht)

end NCG.VaryingHilbert
