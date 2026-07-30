/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Constant-rate geometry and the optical metric
  (GR_emergence, WKB-phase cluster)

* `phiRate_strictMonoOn` (`lem:constant-rate-energy`): the Lagrangian
  energy density `φ(s) = (1-s/c²)^{-1/2} - 1` is strictly increasing
  on `[0, c²)`;
* `constant_speed_of_conserved_energy`
  (`thm:constant-rate-geodesics`): at constant rate `λ > 0`, a
  trajectory with conserved energy `E = λ φ(g(v,v))` has constant
  `g`-speed — energy conservation (Beltrami, the disclosed
  variational interface) plus strict monotonicity of `φ` force
  `g(v,v)` constant, which is the geometric-exactness mechanism;
* `optical_metric_expansion` (`cor:optical-metric`): the
  near-coincidence Taylor bound
  `|1 - √(1-s/c²) - s/(2c²)| ≤ s²/(2c⁴)` on `0 ≤ s ≤ c²/2`, so the
  leading Lagrangian is the optical metric `(λ/c²) g` with an
  explicit quadratic error.  The conformal Ricci conversion law is
  the standard identity cited to Wald/Besse (curvature-tensor
  layer, disclosed).
-/

namespace NCG

open Real

/-- The rate energy profile `φ(s) = (1-s/c²)^{-1/2} - 1`. -/
noncomputable def phiRate (c s : ℝ) : ℝ :=
  (Real.sqrt (1 - s / c ^ 2))⁻¹ - 1

/-- `lem:constant-rate-energy`: `φ` is strictly increasing on
`[0, c²)`. -/
theorem phiRate_strictMonoOn {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (phiRate c) (Set.Ico 0 (c ^ 2)) := by
  intro s hs t ht hst
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hs1 : 0 < 1 - t / c ^ 2 := by
    rw [sub_pos, div_lt_one hc2]
    exact ht.2
  have hs2 : 1 - t / c ^ 2 < 1 - s / c ^ 2 := by
    have hdiv : s / c ^ 2 < t / c ^ 2 := by
      apply div_lt_div_of_pos_right hst hc2
    linarith
  have hsq1 : 0 < Real.sqrt (1 - t / c ^ 2) := Real.sqrt_pos.mpr hs1
  have hsq2 : Real.sqrt (1 - t / c ^ 2) < Real.sqrt (1 - s / c ^ 2) :=
    Real.sqrt_lt_sqrt hs1.le hs2
  unfold phiRate
  have h : 1 / Real.sqrt (1 - s / c ^ 2)
      < 1 / Real.sqrt (1 - t / c ^ 2) :=
    div_lt_div_of_pos_left one_pos hsq1 hsq2
  simp only [one_div] at h
  linarith

/-- `thm:constant-rate-geodesics` (mechanism): at constant rate
`λ > 0`, conservation of the Beltrami energy `E = λ φ(g(v,v))`
forces the `g`-speed to be constant along the trajectory. -/
theorem constant_speed_of_conserved_energy {c lam : ℝ} (hc : 0 < c)
    (hlam : 0 < lam) {speed : ℝ → ℝ}
    (hrange : ∀ t, speed t ∈ Set.Ico 0 (c ^ 2))
    (hconserved : ∀ t, lam * phiRate c (speed t)
      = lam * phiRate c (speed 0)) :
    ∀ t, speed t = speed 0 := by
  intro t
  have h := hconserved t
  have hφ : phiRate c (speed t) = phiRate c (speed 0) :=
    mul_left_cancel₀ hlam.ne' h
  exact (phiRate_strictMonoOn hc).injOn (hrange t) (hrange 0) hφ

/-- `cor:optical-metric` (expansion): the exact quadratic error of
the optical-metric approximation,
`|1 - √(1-s/c²) - s/(2c²)| ≤ s²/(2c⁴)` for `0 ≤ s ≤ c²/2`. -/
theorem optical_metric_expansion {c s : ℝ} (hc : 0 < c)
    (hs0 : 0 ≤ s) (hs : s ≤ c ^ 2 / 2) :
    |1 - Real.sqrt (1 - s / c ^ 2) - s / (2 * c ^ 2)|
      ≤ s ^ 2 / (2 * c ^ 4) := by
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  set u : ℝ := s / c ^ 2 with hu
  have hu0 : 0 ≤ u := by positivity
  have hu2 : u ≤ 1 / 2 := by
    rw [hu, div_le_div_iff₀ hc2 (by norm_num)]
    linarith
  have hupos : 0 ≤ 1 - u := by linarith
  have hs_eq : s / (2 * c ^ 2) = u / 2 := by
    rw [hu]
    ring
  have hs2_eq : s ^ 2 / (2 * c ^ 4) = u ^ 2 / 2 := by
    rw [hu]
    field_simp
  rw [hs_eq, hs2_eq, abs_le]
  have hsq_le : Real.sqrt (1 - u) ≤ 1 - u / 2 := by
    rw [show (1 : ℝ) - u / 2 = Real.sqrt ((1 - u / 2) ^ 2) from
      (Real.sqrt_sq (by linarith)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hsq_ge : 1 - u / 2 - u ^ 2 / 2 ≤ Real.sqrt (1 - u) := by
    rcases le_or_gt (1 - u / 2 - u ^ 2 / 2) 0 with h | h
    · linarith [Real.sqrt_nonneg (1 - u)]
    · rw [show (1 : ℝ) - u / 2 - u ^ 2 / 2
        = Real.sqrt ((1 - u / 2 - u ^ 2 / 2) ^ 2) from
        (Real.sqrt_sq (by linarith)).symm]
      apply Real.sqrt_le_sqrt
      nlinarith
  constructor
  · linarith
  · linarith

end NCG
