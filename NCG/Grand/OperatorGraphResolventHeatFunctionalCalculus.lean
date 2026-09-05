/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphResolventPositivity
import NCG.Grand.ResolventEulerMultiplierContinuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Heat functional calculus from one weak graph resolvent

A positive-shift weak graph resolvent is positive and self-adjoint, with spectrum contained in
`[0,b⁻¹]`.  The continuous one-resolvent heat multiplier can therefore be applied through the
bounded continuous functional calculus.  The transformed Euler powers converge to this heat
operator in operator norm at the same dimension-free inverse-square-root rate as the scalar
estimate.
-/

open Set

noncomputable section

namespace NCG.VaryingHilbert

universe v w

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The real spectrum of a positive weak graph resolvent at shift `b` lies in `[0,b⁻¹]`. -/
theorem operatorGraphResolvent_realSpectrum_subset_Icc
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (b : ℝ) (hb : 0 < b) (R : E →L[ℂ] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A b f (R f)) :
    spectrum ℝ R ⊆ Set.Icc 0 b⁻¹ := by
  by_cases hE : Nontrivial E
  · letI := hE
    have hpos : 0 ≤ R := (ContinuousLinearMap.nonneg_iff_isPositive R).2
      (operatorGraphResolvent_isPositive D A b hb.le R hequation)
    have hnorm : ‖R‖ ≤ b⁻¹ := by
      simpa [one_div] using operatorGraphResolvent_opNorm_le_inv D A R b hb hequation
    intro r hr
    constructor
    · exact spectrum_nonneg_of_nonneg hpos hr
    · exact (Real.le_norm_self r).trans
        ((spectrum.norm_le_norm_of_mem hr).trans hnorm)
  · haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    simp

/-- The heat operator constructed from one positive-shift weak graph resolvent. -/
def operatorGraphResolventHeat
    (R : E →L[ℂ] E) (b t : ℝ) : E →L[ℂ] E :=
  cfc (NCG.ImplicitEuler.resolventHeatMultiplier b t) R

/-- The fixed-order Euler operator constructed from one reference resolvent. -/
def operatorGraphResolventEuler
    (R : E →L[ℂ] E) (b t : ℝ) (k : ℕ) : E →L[ℂ] E :=
  cfc (fun r ↦ NCG.ImplicitEuler.resolventEulerRoot b t k r ^ k) R

/-- One-resolvent Euler functional calculus converges to the one-resolvent heat operator in
operator norm, uniformly over the entire spectrum. -/
theorem norm_operatorGraphResolventEuler_sub_heat_le_inv_sqrt
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (b t : ℝ) (hb : 0 < b) (ht : 0 < t) (k : ℕ) (hk : 0 < k)
    (R : E →L[ℂ] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A b f (R f)) :
    ‖operatorGraphResolventEuler R b t k - operatorGraphResolventHeat R b t‖ ≤
      (Real.sqrt (k : ℝ))⁻¹ := by
  have hspectrum := operatorGraphResolvent_realSpectrum_subset_Icc
    D A b hb R hequation
  have hself : IsSelfAdjoint R :=
    (operatorGraphResolvent_isSymmetric D A b R hequation).isSelfAdjoint
  have hEulerCont : ContinuousOn
      (fun r ↦ NCG.ImplicitEuler.resolventEulerRoot b t k r ^ k)
      (spectrum ℝ R) :=
    (NCG.ImplicitEuler.continuousOn_resolventEulerRoot_pow b t k hb ht hk).mono
      hspectrum
  have hHeatCont : ContinuousOn
      (NCG.ImplicitEuler.resolventHeatMultiplier b t) (spectrum ℝ R) :=
    (NCG.ImplicitEuler.continuousOn_resolventHeatMultiplier b t hb ht).mono
      hspectrum
  rw [operatorGraphResolventEuler, operatorGraphResolventHeat,
    ← cfc_sub _ _ R hEulerCont hHeatCont]
  apply norm_cfc_le (by positivity)
  intro r hr
  rw [Real.norm_eq_abs]
  exact NCG.ImplicitEuler.abs_resolventEulerRoot_pow_sub_heat_le_inv_sqrt
    b t r k ht hk (hspectrum hr).1 (hspectrum hr).2

end NCG.VaryingHilbert
