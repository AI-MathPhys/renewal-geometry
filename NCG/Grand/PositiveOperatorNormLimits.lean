/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Norm limits of positive operators

Operator-norm convergence preserves pointwise quadratic-form nonnegativity.  Consequently, once
symmetry of the limit is known, positivity passes to the limit.  Uniform operator-norm bounds
also pass to the limit by continuity of the norm.
-/

open Filter Topology

noncomputable section

namespace NCG.OperatorLimits

universe u v

variable {I : Type u} {E : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A norm limit of eventually positive operators is positive once symmetry of the limit is
known. -/
theorem isPositive_of_tendsto_of_isSymmetric
    {l : Filter I} [NeBot l] (T : I → E →L[ℂ] E) (Tlim : E →L[ℂ] E)
    (hT : Tendsto T l (nhds Tlim))
    (hlimSymmetric : LinearMap.IsSymmetric Tlim.toLinearMap)
    (hpositive : ∀ᶠ i in l, (T i).IsPositive) :
    Tlim.IsPositive := by
  refine ⟨hlimSymmetric, fun x ↦ ?_⟩
  have heval : Tendsto (fun i ↦ T i x) l (nhds (Tlim x)) :=
    ((continuous_id.clm_apply continuous_const).tendsto Tlim).comp hT
  have hquad : Tendsto
      (fun i ↦ RCLike.re (inner ℂ (T i x) x)) l
      (nhds (RCLike.re (inner ℂ (Tlim x) x))) := by
    have hcontinuous : Continuous
        (fun y : E ↦ RCLike.re (inner ℂ y x)) := by fun_prop
    exact (hcontinuous.tendsto (Tlim x)).comp heval
  exact ge_of_tendsto hquad (hpositive.mono fun i hi ↦ hi.re_inner_nonneg_left x)

/-- An eventual uniform operator-norm bound passes to an operator-norm limit. -/
theorem norm_le_of_tendsto
    {l : Filter I} [NeBot l] (T : I → E →L[ℂ] E) (Tlim : E →L[ℂ] E)
    (hT : Tendsto T l (nhds Tlim)) (bound : ℝ)
    (hbound : ∀ᶠ i in l, ‖T i‖ ≤ bound) :
    ‖Tlim‖ ≤ bound :=
  le_of_tendsto hT.norm hbound

end NCG.OperatorLimits
