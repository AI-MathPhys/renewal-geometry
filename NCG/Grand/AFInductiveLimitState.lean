/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PreCStarDirectLimitState

/-!
# States and GNS representations on AF inductive limits

This file packages the application-level conclusions of the analytic part of
`thm:AF-limit-state` from the Gran-Tensor manuscript.  For an isometric directed system of
normed complex pre-C-star algebras, a compatible family of stage states has a unique extension
to the completed inductive limit.  The associated GNS representation is contractive.

Finite-dimensional C-star stages are the intended AF specialization; none of the proofs below
uses finite dimensionality.
-/

open scoped ComplexOrder

noncomputable section

namespace NCG.PreCStarDirectLimit.CompatibleState

universe u v

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A : ι → Type v}
variable [∀ i, NormedRing (A i)] [∀ i, StarRing (A i)] [∀ i, CStarRing (A i)]
variable [∀ i, NormedAlgebra ℂ (A i)] [∀ i, StarModule ℂ (A i)]
variable {f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j}
variable [DirectedSystem A (fun i j hij ↦ f i j hij)] [IsometricSystem f]

variable (ω : CompatibleState f)

/-- The completed state agrees with the prescribed state on every stage. -/
@[simp]
theorem completionPositiveLinearMap_of (i : ι) (x : A i) :
    ω.completionPositiveLinearMap (completionOf f i x) = ω.state i x := by
  rw [completionPositiveLinearMap, completionOf_apply,
    NCG.PreCStarState.completionPositiveLinearMap_apply,
    NCG.PreCStarState.completionCLM_coe, toPreCStarState_of]

/-- A state on the completed inductive limit is determined by all of its finite-stage
restrictions. -/
theorem completionPositiveLinearMap_unique
    (φ : Completion f →ₚ[ℂ] ℂ)
    (hφ : ∀ i (x : A i), φ (completionOf f i x) = ω.state i x) :
    φ = ω.completionPositiveLinearMap := by
  have hfun : (φ : Completion f → ℂ) = ω.completionPositiveLinearMap := by
    apply UniformSpace.Completion.ext
    · fun_prop
    · fun_prop
    · intro a
      obtain ⟨i, x, rfl⟩ :=
        DirectLimit.exists_eq_mk (fun i j hij ↦ f i j hij) a
      exact hφ i x |>.trans (ω.completionPositiveLinearMap_of i x).symm
  apply DFunLike.ext _ _
  exact congrFun hfun

private theorem norm_leftMulMapPreGNS_le
    (a : Completion f) :
    ‖ω.completionPositiveLinearMap.leftMulMapPreGNS a‖ ≤ ‖a‖ := by
  unfold PositiveLinearMap.leftMulMapPreGNS
  apply LinearMap.mkContinuous_norm_le
  exact norm_nonneg a

set_option backward.isDefEq.respectTransparency false in
/-- The GNS representation of the completed inductive limit is contractive, hence each
represented observable is bounded by its C-star norm. -/
theorem norm_completionGNSRepresentation_apply_le (a : Completion f) :
    ‖ω.completionGNSRepresentation a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      apply isClosed_le
      · fun_prop
      · fun_prop
  | ih z =>
      simp only [completionGNSRepresentation,
        NCG.PreCStarState.completionGNSRepresentation,
        PositiveLinearMap.gnsStarAlgHom_apply]
      change
        ‖ω.toPreCStarState.completionPositiveLinearMap.gnsNonUnitalStarAlgHom a
            (z : ω.toPreCStarState.completionPositiveLinearMap.GNS)‖ ≤
          ‖a‖ * ‖(z : ω.toPreCStarState.completionPositiveLinearMap.GNS)‖
      rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
      simp only [UniformSpace.Completion.norm_coe]
      change @LE.le ℝ Real.instPreorder.toLE
        ‖ω.completionPositiveLinearMap.leftMulMapPreGNS a z‖ (‖a‖ * ‖z‖)
      exact (ω.completionPositiveLinearMap.leftMulMapPreGNS a).le_opNorm z |>.trans <|
        mul_le_mul_of_nonneg_right (ω.norm_leftMulMapPreGNS_le a) (norm_nonneg z)

end NCG.PreCStarDirectLimit.CompatibleState
