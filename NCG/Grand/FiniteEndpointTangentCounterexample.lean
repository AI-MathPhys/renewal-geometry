/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Full-support endpoint laws do not determine a tangent

Concrete two-point probability paths for `cth:GT-secant-no-tangent`.
-/

open Finset

namespace NCG
namespace FiniteEndpointTangentCounterexample

/-- The manuscript's linear interpolation between its two endpoint laws. -/
noncomputable def linearLaw (δ t : ℝ) : Fin 2 → ℝ :=
  ![1 / 2 + δ * t, 1 / 2 - δ * t]

/-- A curved interpolation with the same endpoints.  Choosing the manuscript
perturbation parameter `η=δ` makes full support transparent on `[0,1]`. -/
noncomputable def curvedLaw (δ t : ℝ) : Fin 2 → ℝ :=
  ![1 / 2 + δ * t + δ * (t * (1 - t)),
    1 / 2 - δ * t - δ * (t * (1 - t))]

theorem linearLaw_probability {δ t : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ < 1 / 4)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (∀ i, 0 < linearLaw δ t i) ∧ ∑ i, linearLaw δ t i = 1 := by
  constructor
  · intro i
    fin_cases i
    · simp [linearLaw]
      positivity
    · simp [linearLaw]
      have hprod : δ * t ≤ δ := mul_le_of_le_one_right hδ₀.le ht₁
      linarith
  · norm_num [linearLaw, Fin.sum_univ_two]

theorem curvedLaw_probability {δ t : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ < 1 / 4)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (∀ i, 0 < curvedLaw δ t i) ∧ ∑ i, curvedLaw δ t i = 1 := by
  have hx₀ : 0 ≤ t * (2 - t) := mul_nonneg ht₀ (by linarith)
  have hx₁ : t * (2 - t) ≤ 1 := by
    nlinarith [sq_nonneg (t - 1)]
  have hprod : δ * (t * (2 - t)) ≤ δ :=
    mul_le_of_le_one_right hδ₀.le hx₁
  constructor
  · intro i
    fin_cases i
    · simp [curvedLaw]
      nlinarith [mul_nonneg hδ₀.le ht₀,
        mul_nonneg ht₀ (by linarith : 0 ≤ 1 - t)]
    · simp [curvedLaw]
      nlinarith
  · simp [curvedLaw, Fin.sum_univ_two]
    ring

/-- `cth:GT-secant-no-tangent`, with full support, normalization, common
endpoints, and distinct initial derivatives all stated explicitly. -/
theorem full_support_same_endpoints_distinct_tangents
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ < 1 / 4) :
    (∀ t, 0 ≤ t → t ≤ 1 →
      (∀ i, 0 < linearLaw δ t i) ∧ ∑ i, linearLaw δ t i = 1)
    ∧ (∀ t, 0 ≤ t → t ≤ 1 →
      (∀ i, 0 < curvedLaw δ t i) ∧ ∑ i, curvedLaw δ t i = 1)
    ∧ linearLaw δ 0 = curvedLaw δ 0
    ∧ linearLaw δ 1 = curvedLaw δ 1
    ∧ HasDerivAt (fun t ↦ linearLaw δ t 0) δ 0
    ∧ HasDerivAt (fun t ↦ curvedLaw δ t 0) (2 * δ) 0
    ∧ δ ≠ 2 * δ := by
  refine ⟨fun t ht₀ ht₁ ↦ linearLaw_probability hδ₀ hδ₁ ht₀ ht₁,
    fun t ht₀ ht₁ ↦ curvedLaw_probability hδ₀ hδ₁ ht₀ ht₁,
    ?_, ?_, ?_, ?_, by linarith⟩
  · funext i
    fin_cases i <;> simp [linearLaw, curvedLaw]
  · funext i
    fin_cases i <;> simp [linearLaw, curvedLaw]
  · simpa [linearLaw] using
      ((hasDerivAt_id (0 : ℝ)).const_mul δ).const_add (1 / 2)
  · have hcurve : HasDerivAt (fun t : ℝ => t * (1 - t)) 1 0 := by
      have h := (hasDerivAt_id (0 : ℝ)).mul
        ((hasDerivAt_id (0 : ℝ)).const_sub 1)
      norm_num at h
      exact h
    have hlinear := ((hasDerivAt_id (0 : ℝ)).const_mul δ).const_add (1 / 2)
    have hperturb := hcurve.const_mul δ
    have h := hlinear.add hperturb
    have hfun : ((fun x : ℝ => 1 / 2 + δ * id x)
        + fun y : ℝ => δ * (y * (1 - y))) =
        fun t : ℝ => 1 / 2 + δ * t + δ * (t * (1 - t)) := by
      funext t
      simp [Pi.add_apply]
    rw [hfun] at h
    have hval : δ * 1 + δ * 1 = 2 * δ := by ring
    rw [hval] at h
    simpa [curvedLaw] using h

end FiniteEndpointTangentCounterexample
end NCG
