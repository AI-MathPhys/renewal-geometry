/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphResolventHeatFunctionalCalculus

/-!
# Positive-time semigroup structure of the one-resolvent heat calculus

The heat multipliers multiply under addition of positive times.  Bounded continuous functional
calculus transfers this identity to the canonical graph-resolvent heat operators.  The same
spectral representation gives the contraction bound.
-/

open Set

noncomputable section

namespace NCG.ImplicitEuler

/-- The one-resolvent heat multiplier converts addition of times into multiplication. -/
theorem resolventHeatMultiplier_add
    (b t u r : ℝ) :
    resolventHeatMultiplier b (t + u) r =
      resolventHeatMultiplier b t r * resolventHeatMultiplier b u r := by
  by_cases hr : r = 0
  · simp [resolventHeatMultiplier, hr]
  · simp only [resolventHeatMultiplier, hr, if_false, ← Real.exp_add]
    congr 1
    ring

/-- At positive time the one-resolvent heat multiplier has absolute value at most one throughout
the positive reference-resolvent interval. -/
theorem abs_resolventHeatMultiplier_le_one
    (b t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) (hrb : r ≤ b⁻¹) :
    |resolventHeatMultiplier b t r| ≤ 1 := by
  by_cases hrZero : r = 0
  · simp [resolventHeatMultiplier, hrZero]
  · have hrPos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrZero)
    have henergy : 0 ≤ r⁻¹ - b := resolventEnergy_nonneg hrPos hrb
    rw [resolventHeatMultiplier, if_neg hrZero, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht henergy))

end NCG.ImplicitEuler

namespace NCG.VaryingHilbert

universe v w

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Canonical heat operators constructed from one weak graph resolvent form a semigroup at
positive times. -/
theorem operatorGraphResolventHeat_mul
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (b t u : ℝ) (hb : 0 < b) (ht : 0 < t) (hu : 0 < u)
    (R : E →L[ℂ] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A b f (R f)) :
    operatorGraphResolventHeat R b t * operatorGraphResolventHeat R b u =
      operatorGraphResolventHeat R b (t + u) := by
  have hspectrum := operatorGraphResolvent_realSpectrum_subset_Icc
    D A b hb R hequation
  have hself : IsSelfAdjoint R :=
    (operatorGraphResolvent_isSymmetric D A b R hequation).isSelfAdjoint
  have htCont : ContinuousOn
      (NCG.ImplicitEuler.resolventHeatMultiplier b t) (spectrum ℝ R) :=
    (NCG.ImplicitEuler.continuousOn_resolventHeatMultiplier b t hb ht).mono hspectrum
  have huCont : ContinuousOn
      (NCG.ImplicitEuler.resolventHeatMultiplier b u) (spectrum ℝ R) :=
    (NCG.ImplicitEuler.continuousOn_resolventHeatMultiplier b u hb hu).mono hspectrum
  rw [operatorGraphResolventHeat, operatorGraphResolventHeat,
    operatorGraphResolventHeat, ← cfc_mul _ _ R htCont huCont]
  apply cfc_congr
  intro r hr
  exact (NCG.ImplicitEuler.resolventHeatMultiplier_add b t u r).symm

/-- Every positive-time canonical graph-resolvent heat operator is a contraction. -/
theorem norm_operatorGraphResolventHeat_le_one
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t)
    (R : E →L[ℂ] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A b f (R f)) :
    ‖operatorGraphResolventHeat R b t‖ ≤ 1 := by
  have hspectrum := operatorGraphResolvent_realSpectrum_subset_Icc
    D A b hb R hequation
  rw [operatorGraphResolventHeat]
  apply norm_cfc_le (by positivity)
  intro r hr
  rw [Real.norm_eq_abs]
  exact NCG.ImplicitEuler.abs_resolventHeatMultiplier_le_one
    b t r ht (hspectrum hr).1 (hspectrum hr).2

/-- Positive-time canonical graph-resolvent heat operators are contractions without a separate
continuity premise. -/
theorem norm_operatorGraphResolventHeat_le_one_of_pos
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (b t : ℝ) (hb : 0 < b) (ht : 0 < t)
    (R : E →L[ℂ] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A b f (R f)) :
    ‖operatorGraphResolventHeat R b t‖ ≤ 1 := by
  exact norm_operatorGraphResolventHeat_le_one D A b t hb ht.le R hequation

end NCG.VaryingHilbert
