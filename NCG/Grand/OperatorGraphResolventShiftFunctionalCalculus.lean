/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphSecondResolventIdentity
import NCG.Grand.OperatorGraphResolventHeatFunctionalCalculus

/-!
# Every positive graph resolvent from one reference resolvent

For a nonnegative operator graph, one positive-shift weak resolvent determines every other
positive-shift resolvent through the real continuous functional calculus.  The denominator is
strictly positive on the reference spectrum, and the weak source-transform identity supplies the
operator cancellation needed to identify the rational functional calculus with the actual weak
resolvent.
-/

open Set

noncomputable section

namespace NCG.VaryingHilbert

universe v w

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The scalar denominator transporting the reference shift `b` to the shift `a` is strictly
positive on the spectrum of the reference resolvent. -/
theorem operatorGraphResolvent_shiftDenominator_pos
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (R : ℝ → E →L[ℂ] E)
    (hequation : ∀ lam, 0 < lam → ∀ f : E,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    {r : ℝ} (hr : r ∈ spectrum ℝ (R b)) :
    0 < 1 + (a - b) * r := by
  have hrIcc := operatorGraphResolvent_realSpectrum_subset_Icc
    D A b hb (R b) (hequation b hb)
  have hr0 : 0 ≤ r := (hrIcc hr).1
  have hrb : r ≤ b⁻¹ := (hrIcc hr).2
  have hbr : b * r ≤ 1 := by
    calc
      b * r ≤ b * b⁻¹ := mul_le_mul_of_nonneg_left hrb hb.le
      _ = 1 := by simp [hb.ne']
  have hone : 0 ≤ 1 - b * r := sub_nonneg.mpr hbr
  by_cases hrZero : r = 0
  · simp [hrZero]
  · have hrPos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrZero)
    have har : 0 < a * r := mul_pos ha hrPos
    nlinarith

/-- Every positive-shift weak graph resolvent is the rational real continuous-functional-calculus
transform `r ↦ r / (1 + (a - b) r)` of one fixed positive-shift resolvent. -/
theorem operatorGraphResolvent_eq_cfc_shiftTransform
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (R : ℝ → E →L[ℂ] E)
    (hequation : ∀ lam, 0 < lam → ∀ f : E,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    R a = cfc (fun r : ℝ ↦ r / (1 + (a - b) * r)) (R b) := by
  let q : ℝ → ℝ := fun r ↦ 1 + (a - b) * r
  have hself : IsSelfAdjoint (R b) :=
    (operatorGraphResolvent_isSymmetric D A b (R b) (hequation b hb)).isSelfAdjoint
  have hqCont : ContinuousOn q (spectrum ℝ (R b)) := by
    fun_prop
  have hidCont : ContinuousOn (fun r : ℝ ↦ r) (spectrum ℝ (R b)) :=
    continuous_id.continuousOn
  have hqNe : ∀ r ∈ spectrum ℝ (R b), q r ≠ 0 := by
    intro r hr
    exact ne_of_gt (operatorGraphResolvent_shiftDenominator_pos
      D A R hequation a b ha hb hr)
  have hqCfc : cfc q (R b) = 1 + (a - b) • R b := by
    rw [show q = (fun r : ℝ ↦ 1 + (a - b) * r) from rfl]
    rw [cfc_const_add 1 (fun r : ℝ ↦ (a - b) * r) (R b),
      cfc_const_mul_id (a - b) (R b) hself]
    simp
  have hqUnit : IsUnit (1 + (a - b) • R b) := by
    rw [← hqCfc]
    exact isUnit_cfc q (R b) hqCont hself hqNe
  have hproduct : R a * (1 + (a - b) • R b) = R b := by
    rw [ContinuousLinearMap.mul_def]
    apply ContinuousLinearMap.ext
    intro f
    simpa only [ContinuousLinearMap.comp_apply, add_apply, one_apply_eq_self,
      smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      operatorGraphResolvent_sourceTransform D A R hequation a b ha hb f
  rw [cfc_map_div (fun r : ℝ ↦ r) q (R b) hqNe hidCont hqCont hself,
    cfc_id' ℝ (R b) hself, hqCfc]
  exact (Ring.eq_mul_inverse_iff_mul_eq _ _ _ hqUnit).2 hproduct

end NCG.VaryingHilbert
