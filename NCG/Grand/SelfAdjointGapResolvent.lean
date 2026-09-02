/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BanachAlgebraResolventStability
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# Resolvent bounds from a real self-adjoint spectral gap

The reciprocal multiplier in real functional calculus identifies the
resolvent and gives the sharp inverse-distance norm bound.
-/

noncomputable section

namespace NCG.ResolventStability

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- If every real spectral value is at least `distance` from `z`, then `z`
is a resolvent point and its resolvent norm is at most `distance⁻¹`. -/
theorem real_mem_resolventSet_and_norm_resolvent_le_inv_of_gap
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (z distance : ℝ) (hdistance : 0 < distance)
    (hgap : ∀ x ∈ spectrum ℝ A, distance ≤ |z - x|) :
    z ∈ resolventSet ℝ A ∧ ‖resolvent A z‖ ≤ distance⁻¹ := by
  let f : ℝ → ℝ := fun x => (z - x)⁻¹
  have hne : ∀ x ∈ spectrum ℝ A, z - x ≠ 0 := by
    intro x hx hzx
    have := hgap x hx
    rw [hzx, abs_zero] at this
    linarith
  have hf : ContinuousOn f (spectrum ℝ A) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    exact hne
  let R : H →L[ℂ] H := cfc f A
  have hshift : algebraMap ℝ (H →L[ℂ] H) z - A =
      cfc (fun x : ℝ => z - x) A := by
    rw [cfc_sub, cfc_const, cfc_id']
  have hleft : (algebraMap ℝ (H →L[ℂ] H) z - A) * R = 1 := by
    rw [hshift]
    change cfc (fun x : ℝ => z - x) A * cfc f A = 1
    rw [← cfc_mul (fun x : ℝ => z - x) f A (by fun_prop) hf]
    rw [← cfc_const_one ℝ A]
    apply cfc_congr
    intro x hx
    dsimp only [f]
    exact mul_inv_cancel₀ (hne x hx)
  have hright : R * (algebraMap ℝ (H →L[ℂ] H) z - A) = 1 := by
    rw [hshift]
    change cfc f A * cfc (fun x : ℝ => z - x) A = 1
    rw [← cfc_mul f (fun x : ℝ => z - x) A hf (by fun_prop)]
    rw [← cfc_const_one ℝ A]
    apply cfc_congr
    intro x hx
    dsimp only [f]
    exact inv_mul_cancel₀ (hne x hx)
  have hunit : IsUnit (algebraMap ℝ (H →L[ℂ] H) z - A) := by
    refine ⟨{
      val := algebraMap ℝ (H →L[ℂ] H) z - A
      inv := R
      val_inv := hleft
      inv_val := hright }, rfl⟩
  have hresolvent : resolvent A z = R := by
    rw [resolvent]
    calc
      Ring.inverse (algebraMap ℝ (H →L[ℂ] H) z - A) =
          Ring.inverse (algebraMap ℝ (H →L[ℂ] H) z - A) * 1 := by rw [mul_one]
      _ = Ring.inverse (algebraMap ℝ (H →L[ℂ] H) z - A) *
          ((algebraMap ℝ (H →L[ℂ] H) z - A) * R) := by rw [hleft]
      _ = (Ring.inverse (algebraMap ℝ (H →L[ℂ] H) z - A) *
          (algebraMap ℝ (H →L[ℂ] H) z - A)) * R := by rw [mul_assoc]
      _ = R := by rw [Ring.inverse_mul_cancel _ hunit, one_mul]
  constructor
  · exact hunit
  · rw [hresolvent]
    apply norm_cfc_le (inv_nonneg.mpr hdistance.le)
    intro x hx
    dsimp only [f]
    rw [norm_inv, Real.norm_eq_abs]
    exact (inv_le_inv₀ hdistance (lt_of_lt_of_le hdistance (hgap x hx))).mpr
      (hgap x hx)

end NCG.ResolventStability
