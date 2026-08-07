/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact field-tightness and mass-escape alternative
  (`thm:field-tightness-alternative`,
  Gran-Tensor manuscript)

* `field_tightness_alternative`:
  (i) the spectral comparison `1_{|x|>R} ≤ 2x²/(x²+R²)`
      (so `Θ_F(R) ≤ 2·Ξ_F(R)` after applying the states);
  (ii) the window monotonicity
      `x²/(x²+S²) ≤ R²/(R²+S²)` for `|x| ≤ R`
      (so `Ξ_F(S) ≤ Θ_F(R) + R²/(R²+S²)`);
  (iii) the boxed equivalence
      `Θ_F(R) → 0 ↔ Ξ_F(R) → 0` for the transferred
      profiles.

The mass-escape witness on the failing branch and the
moment-sufficiency remark are the manuscript's spectral
packaging over these bounds.
-/

namespace NCG

/-- `thm:field-tightness-alternative`. -/
theorem field_tightness_alternative :
    -- (i) spectral indicator comparison
    (∀ x R : ℝ, 0 < R → R < |x| →
      (1 : ℝ) ≤ 2 * x ^ 2 / (x ^ 2 + R ^ 2))
    -- (ii) window monotonicity below the threshold
    ∧ (∀ x R S : ℝ, 0 < R → 0 < S → |x| ≤ R →
        x ^ 2 / (x ^ 2 + S ^ 2) ≤ R ^ 2 / (R ^ 2 + S ^ 2))
    -- (iii) the boxed tightness equivalence
    ∧ (∀ θ ξ : ℝ → ℝ, (∀ R, 0 ≤ θ R) → (∀ R, 0 ≤ ξ R) →
        (∀ R, 0 < R → θ R ≤ 2 * ξ R) →
        (∀ R S, 0 < R → R ≤ S →
          ξ S ≤ θ R + R ^ 2 / (R ^ 2 + S ^ 2)) →
        (Filter.Tendsto θ Filter.atTop (nhds 0)
          ↔ Filter.Tendsto ξ Filter.atTop (nhds 0))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x R hR hRx
    have hx2 : R ^ 2 < x ^ 2 := by
      nlinarith [sq_abs x, abs_nonneg x]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · intro x R S hR hS hxR
    have hx2 : x ^ 2 ≤ R ^ 2 := by
      nlinarith [sq_abs x, abs_nonneg x]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg S]
  · intro θ ξ hθnn hξnn hθle hbound
    constructor
    · intro hθ
      rw [Metric.tendsto_atTop] at hθ ⊢
      intro ε hε
      obtain ⟨N₁, hN₁⟩ := hθ (ε / 2) (by positivity)
      set Rv := max N₁ 1 with hRv
      have hRpos : (0 : ℝ) < Rv :=
        lt_of_lt_of_le one_pos (le_max_right _ _)
      have hθR : θ Rv < ε / 2 := by
        have h := hN₁ Rv (le_max_left _ _)
        rwa [Real.dist_eq, sub_zero,
          abs_of_nonneg (hθnn Rv)] at h
      refine ⟨max Rv (Rv * Real.sqrt (2 / ε)), ?_⟩
      intro S hS
      have hSR : Rv ≤ S := le_trans (le_max_left _ _) hS
      have hSs : Rv * Real.sqrt (2 / ε) ≤ S :=
        le_trans (le_max_right _ _) hS
      have hS0 : 0 < S := lt_of_lt_of_le hRpos hSR
      have hsq : Rv ^ 2 * (2 / ε) ≤ S ^ 2 := by
        have h1 : (Rv * Real.sqrt (2 / ε)) ^ 2 ≤ S ^ 2 :=
          pow_le_pow_left₀ (by positivity) hSs 2
        rwa [mul_pow, Real.sq_sqrt
          (by positivity : (0 : ℝ) ≤ 2 / ε)] at h1
      have hsq' : 2 * Rv ^ 2 ≤ ε * S ^ 2 := by
        have h2 := mul_le_mul_of_nonneg_right hsq hε.le
        have h3 : Rv ^ 2 * (2 / ε) * ε = 2 * Rv ^ 2 := by
          field_simp
        rw [h3] at h2
        linarith
      have htail : Rv ^ 2 / (Rv ^ 2 + S ^ 2) ≤ ε / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [sq_nonneg Rv]
      have hb := hbound Rv S hRpos hSR
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hξnn S)]
      calc ξ S ≤ θ Rv + Rv ^ 2 / (Rv ^ 2 + S ^ 2) := hb
        _ < ε / 2 + ε / 2 := by
            apply add_lt_add_of_lt_of_le hθR htail
        _ = ε := by ring
    · intro hξ
      have h2ξ : Filter.Tendsto (fun R => 2 * ξ R)
          Filter.atTop (nhds 0) := by
        simpa using hξ.const_mul 2
      apply squeeze_zero'
        (Filter.Eventually.of_forall hθnn) ?_ h2ξ
      filter_upwards [Filter.eventually_gt_atTop 0]
        with R hR
      exact hθle R hR

end NCG
