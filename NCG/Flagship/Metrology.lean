/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Independent Newton and cosmological metrology
  (`thm:metrology-master`, flagship manuscript)

* `newton_from_stiffness`: the boxed conversion — the ADM
  normalization `χ = ℓ*²/(16πG_eff)` inverts to
  `G_eff = ℓ*²/(16πχ)`;
* `homogeneous_volume_variation`: the boxed cosmological readout
  — on the homogeneous path `q(σ) = e^{2σ}q₀` the volume scales
  as `e^{3σ}`, so the vacuum branch action `Λ_H·𝒱·e^{3σ}` has
  `σ`-derivative `3Λ_H𝒱` at `σ = 0`, giving
  `Λ̂_H = (1/(3𝒱))·(d/dσ)Γ^vac(0) = Λ_H`;
* `normalized_probability_gauge`: the invariance clause —
  multiplying every branch amplitude by a common factor `e^{-c}`
  leaves all normalized Store–Read probabilities unchanged, so
  normalized data cannot determine the absolute homogeneous
  score.

Rendering disclosed: the scalarity criterion (the whitened
Hessian `𝕄_χ` equals `χ̂I` exactly when the response is one
scalar stiffness) is definitional on the finite spin-two tangent
space; the renewal-length calibration `ℓ*` is the manuscript's
declared metrological input.
-/

namespace NCG

/-- Boxed conversion: `χ = ℓ²/(16πG)` inverts to
`G = ℓ²/(16πχ)`. -/
theorem newton_from_stiffness (χ ℓ G : ℝ) (hχ : 0 < χ)
    (hG : 0 < G) (h : χ = ℓ ^ 2 / (16 * Real.pi * G)) :
    G = ℓ ^ 2 / (16 * Real.pi * χ) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  field_simp at h ⊢
  nlinarith [h]

/-- Boxed cosmological readout: the vacuum branch action
`Λ𝒱e^{3σ}` has `σ`-derivative `3Λ𝒱` at `σ = 0`, so
`(1/(3𝒱))·Γ'(0) = Λ`. -/
theorem homogeneous_volume_variation (Λ V0 : ℝ) (hV : V0 ≠ 0) :
    HasDerivAt (fun σ : ℝ => Λ * V0 * Real.exp (3 * σ))
      (3 * (Λ * V0)) 0
    ∧ 1 / (3 * V0) * (3 * (Λ * V0)) = Λ := by
  constructor
  · have h1 : HasDerivAt (fun σ : ℝ => 3 * σ) 3 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_mul 3
    have h2 := (Real.hasDerivAt_exp (3 * 0)).comp 0 h1
    have h3 := h2.const_mul (Λ * V0)
    refine h3.congr_deriv ?_
    simp
    ring
  · field_simp

/-- Invariance clause: a common amplitude factor cancels from
every normalized probability. -/
theorem normalized_probability_gauge {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (c : ℝ) (i : ι)
    (hsum : ∑ j, ‖a j‖ ^ 2 ≠ 0) :
    ‖(Real.exp (-c) : ℂ) * a i‖ ^ 2
        / ∑ j, ‖(Real.exp (-c) : ℂ) * a j‖ ^ 2
      = ‖a i‖ ^ 2 / ∑ j, ‖a j‖ ^ 2 := by
  have hfac : ∀ j, ‖(Real.exp (-c) : ℂ) * a j‖ ^ 2
      = Real.exp (-c) ^ 2 * ‖a j‖ ^ 2 := by
    intro j
    rw [norm_mul, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [hfac]
  rw [← Finset.mul_sum]
  have he : Real.exp (-c) ^ 2 ≠ 0 := by positivity
  field_simp

end NCG
