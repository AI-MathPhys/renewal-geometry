/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Rapid switching is not included
  (`prop:supp-law-switching`, `eq:supp-law-dispersion`;
  emergent-spacetime manuscript)

The flat scalar corner mode of a law `B = σ I` is an oscillator
`q'' = -Ω² q` with `Ω_{σ,h}(k)² = ℓ_h(k) (1 + σ h² ℓ_h(k))`
(`eq:supp-law-dispersion`).  Holding a law for a quarter period transfers
`(q, q')` by the matrix `[[0, Ω⁻¹], [-Ω, 0]]`; the two-step product of two
such transfers is `diag(-Ω₁/Ω₂, -Ω₂/Ω₁)`, whose eigenvalue modulus ratio
stays away from one at the ultraviolet corner `h² ℓ = 12` when
`σ₁ ≠ σ₂`, and repeated switching amplifies the mode exponentially in the
number of cycles, i.e. like `exp(cT/h)` on a slab of length `T` with
`O(h)` cycles.

* `oscillatorSolution`, `oscillatorVelocity`: the explicit oscillator
  trajectory with data `(q₀, p₀)`; it solves `q'' = -Ω² q`
  (`oscillatorSolution_hasDerivAt`, `oscillatorVelocity_hasDerivAt`).
* `quarterPeriodTransfer`: the matrix `[[0, Ω⁻¹], [-Ω, 0]]`; it is the
  quarter-period state map of the oscillator
  (`quarterPeriodTransfer_mulVec`).
* `quarterPeriodTransfer_two_step`: the two-law product is
  `diag(-Ω₁/Ω₂, -Ω₂/Ω₁)`, with eigenvalues `-Ω₁/Ω₂` and its reciprocal
  (`two_step_hasEigenvalue`, `two_step_hasEigenvalue_reciprocal`).
* `cornerFrequencySq`, `corner_frequency_ratio_sq`,
  `corner_frequency_ratio_ne_one`: the dispersion relation and the corner
  ratio `Ω₁²/Ω₂² = (1 + 12σ₁)/(1 + 12σ₂) ≠ 1` for `σ₁ ≠ σ₂`.
* `two_step_pow_entry_abs`, `switching_amplification`: after `n` switching
  cycles the diagonal entries have modulus `(Ω₁/Ω₂)^{±n}`, and with
  `n ≥ T/(Kh)` cycles of duration `≤ Kh` this is at least
  `exp((log ρ / K) · T/h)` with `ρ = max(Ω₁/Ω₂, Ω₂/Ω₁) > 1`.

The only step of the paper's proof left informal is the identification of the
resolved corner mode with a scalar oscillator; uniqueness of the oscillator
trajectory is not needed because the transfer matrix is defined from the
explicit solution.
-/

open scoped BigOperators Matrix

namespace RenewalGeometry

/-- The oscillator trajectory `q(t) = q₀ cos(Ω t) + (p₀/Ω) sin(Ω t)` of
`q'' = -Ω² q` with data `(q₀, p₀)`. -/
noncomputable def oscillatorSolution (Ω q₀ p₀ t : ℝ) : ℝ :=
  q₀ * Real.cos (Ω * t) + p₀ / Ω * Real.sin (Ω * t)

/-- The velocity `q'(t) = -q₀ Ω sin(Ω t) + p₀ cos(Ω t)`. -/
noncomputable def oscillatorVelocity (Ω q₀ p₀ t : ℝ) : ℝ :=
  -q₀ * Ω * Real.sin (Ω * t) + p₀ * Real.cos (Ω * t)

theorem hasDerivAt_cos_mul (Ω t : ℝ) :
    HasDerivAt (fun t => Real.cos (Ω * t)) (-Real.sin (Ω * t) * Ω) t := by
  have := (Real.hasDerivAt_cos (Ω * t)).comp t ((hasDerivAt_id t).const_mul Ω)
  simpa using this

theorem hasDerivAt_sin_mul (Ω t : ℝ) :
    HasDerivAt (fun t => Real.sin (Ω * t)) (Real.cos (Ω * t) * Ω) t := by
  have := (Real.hasDerivAt_sin (Ω * t)).comp t ((hasDerivAt_id t).const_mul Ω)
  simpa using this

/-- `q' = oscillatorVelocity`. -/
theorem oscillatorSolution_hasDerivAt (Ω q₀ p₀ t : ℝ) (hΩ : Ω ≠ 0) :
    HasDerivAt (oscillatorSolution Ω q₀ p₀) (oscillatorVelocity Ω q₀ p₀ t) t := by
  have h := ((hasDerivAt_cos_mul Ω t).const_mul q₀).add
    ((hasDerivAt_sin_mul Ω t).const_mul (p₀ / Ω))
  refine h.congr_deriv ?_
  unfold oscillatorVelocity
  field_simp
  ring

/-- `q'' = -Ω² q`: the trajectory is the flat scalar oscillator. -/
theorem oscillatorVelocity_hasDerivAt (Ω q₀ p₀ t : ℝ) :
    HasDerivAt (oscillatorVelocity Ω q₀ p₀)
      (-Ω ^ 2 * oscillatorSolution Ω q₀ p₀ t) t := by
  have h := ((hasDerivAt_sin_mul Ω t).const_mul (-q₀ * Ω)).add
    ((hasDerivAt_cos_mul Ω t).const_mul p₀)
  refine h.congr_deriv ?_
  unfold oscillatorSolution
  by_cases hΩ : Ω = 0
  · subst hΩ; ring
  · field_simp
    ring

theorem oscillatorSolution_zero (Ω q₀ p₀ : ℝ) :
    oscillatorSolution Ω q₀ p₀ 0 = q₀ := by
  simp [oscillatorSolution]

theorem oscillatorVelocity_zero (Ω q₀ p₀ : ℝ) :
    oscillatorVelocity Ω q₀ p₀ 0 = p₀ := by
  simp [oscillatorVelocity]

/-- A quarter period `π / (2Ω)`. -/
noncomputable def quarterPeriod (Ω : ℝ) : ℝ := Real.pi / (2 * Ω)

/-- The quarter-period transfer matrix `[[0, Ω⁻¹], [-Ω, 0]]`. -/
noncomputable def quarterPeriodTransfer (Ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, Ω⁻¹; -Ω, 0]

/-- Holding the law `Ω` for a quarter period maps the state `(q₀, p₀)` by
the transfer matrix. -/
theorem quarterPeriodTransfer_mulVec (Ω q₀ p₀ : ℝ) (hΩ : Ω ≠ 0) :
    quarterPeriodTransfer Ω *ᵥ ![q₀, p₀] =
      ![oscillatorSolution Ω q₀ p₀ (quarterPeriod Ω),
        oscillatorVelocity Ω q₀ p₀ (quarterPeriod Ω)] := by
  have harg : Ω * quarterPeriod Ω = Real.pi / 2 := by
    unfold quarterPeriod; field_simp
  unfold oscillatorSolution oscillatorVelocity
  rw [harg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  unfold quarterPeriodTransfer
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The two-step product of two quarter-period transfers is the diagonal
matrix `diag(-Ω₁/Ω₂, -Ω₂/Ω₁)`. -/
theorem quarterPeriodTransfer_two_step (Ω₁ Ω₂ : ℝ) :
    quarterPeriodTransfer Ω₂ * quarterPeriodTransfer Ω₁ =
      Matrix.diagonal ![-(Ω₁ / Ω₂), -(Ω₂ / Ω₁)] := by
  unfold quarterPeriodTransfer
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] <;> ring

/-- `-Ω₁/Ω₂` is an eigenvalue of the two-step product. -/
theorem two_step_hasEigenvalue (Ω₁ Ω₂ : ℝ) :
    Module.End.HasEigenvalue
      (Matrix.toLin' (quarterPeriodTransfer Ω₂ * quarterPeriodTransfer Ω₁))
      (-(Ω₁ / Ω₂)) := by
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := Pi.single (0 : Fin 2) (1 : ℝ)) ?_
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.toLin'_apply, quarterPeriodTransfer_two_step,
      Matrix.diagonal_mulVec_single]
    ext i
    fin_cases i <;> simp
  · intro h
    have := congrFun h 0
    simp at this

/-- Its reciprocal `-Ω₂/Ω₁` is the other eigenvalue. -/
theorem two_step_hasEigenvalue_reciprocal (Ω₁ Ω₂ : ℝ) :
    Module.End.HasEigenvalue
      (Matrix.toLin' (quarterPeriodTransfer Ω₂ * quarterPeriodTransfer Ω₁))
      (-(Ω₂ / Ω₁)) := by
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := Pi.single (1 : Fin 2) (1 : ℝ)) ?_
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.toLin'_apply, quarterPeriodTransfer_two_step,
      Matrix.diagonal_mulVec_single]
    ext i
    fin_cases i <;> simp
  · intro h
    have := congrFun h 1
    simp at this

/-- The two eigenvalues are reciprocal. -/
theorem two_step_eigenvalues_reciprocal (Ω₁ Ω₂ : ℝ) (h₁ : Ω₁ ≠ 0)
    (h₂ : Ω₂ ≠ 0) : (-(Ω₁ / Ω₂)) * (-(Ω₂ / Ω₁)) = 1 := by
  field_simp

/-- The corner-mode dispersion `Ω_{σ,h}(k)² = ℓ (1 + σ h² ℓ)`
(`eq:supp-law-dispersion`). -/
def cornerFrequencySq (σ ℓ h : ℝ) : ℝ := ℓ * (1 + σ * h ^ 2 * ℓ)

/-- At the ultraviolet corner `h² ℓ = 12` the squared frequency ratio is
`(1 + 12σ₁)/(1 + 12σ₂)`. -/
theorem corner_frequency_ratio_sq (σ₁ σ₂ ℓ h : ℝ) (hℓ : ℓ ≠ 0)
    (hcorner : h ^ 2 * ℓ = 12) (h₂ : 1 + 12 * σ₂ ≠ 0) :
    cornerFrequencySq σ₁ ℓ h / cornerFrequencySq σ₂ ℓ h =
      (1 + 12 * σ₁) / (1 + 12 * σ₂) := by
  unfold cornerFrequencySq
  have e₁ : σ₁ * h ^ 2 * ℓ = 12 * σ₁ := by rw [mul_assoc, hcorner]; ring
  have e₂ : σ₂ * h ^ 2 * ℓ = 12 * σ₂ := by rw [mul_assoc, hcorner]; ring
  rw [e₁, e₂]
  field_simp

/-- For distinct scalar marks in the admissible interval
(`1 + 12σᵢ > 0`) the corner frequency ratio is separated from one. -/
theorem corner_frequency_ratio_ne_one (σ₁ σ₂ ℓ h : ℝ) (hℓ : ℓ ≠ 0)
    (hcorner : h ^ 2 * ℓ = 12) (h₁ : 0 < 1 + 12 * σ₁) (h₂ : 0 < 1 + 12 * σ₂)
    (hne : σ₁ ≠ σ₂) :
    cornerFrequencySq σ₁ ℓ h / cornerFrequencySq σ₂ ℓ h ≠ 1 := by
  rw [corner_frequency_ratio_sq σ₁ σ₂ ℓ h hℓ hcorner h₂.ne']
  intro heq
  rw [div_eq_one_iff_eq h₂.ne'] at heq
  exact hne (by linarith)

/-- The frequency ratio itself: `Ω₁/Ω₂ = √((1+12σ₁)/(1+12σ₂)) ≠ 1`. -/
theorem corner_frequency_sqrt_ratio_ne_one (σ₁ σ₂ ℓ h : ℝ) (hℓ : 0 < ℓ)
    (hcorner : h ^ 2 * ℓ = 12) (h₁ : 0 < 1 + 12 * σ₁) (h₂ : 0 < 1 + 12 * σ₂)
    (hne : σ₁ ≠ σ₂) :
    Real.sqrt (cornerFrequencySq σ₁ ℓ h) / Real.sqrt (cornerFrequencySq σ₂ ℓ h)
      ≠ 1 := by
  intro heq
  apply corner_frequency_ratio_ne_one σ₁ σ₂ ℓ h hℓ.ne' hcorner h₁ h₂ hne
  have hpos₂ : 0 < cornerFrequencySq σ₂ ℓ h := by
    unfold cornerFrequencySq
    have : σ₂ * h ^ 2 * ℓ = 12 * σ₂ := by rw [mul_assoc, hcorner]; ring
    rw [this]; positivity
  have hpos₁ : 0 < cornerFrequencySq σ₁ ℓ h := by
    unfold cornerFrequencySq
    have : σ₁ * h ^ 2 * ℓ = 12 * σ₁ := by rw [mul_assoc, hcorner]; ring
    rw [this]; positivity
  rw [← Real.sqrt_div hpos₁.le] at heq
  have := congrArg (fun x => x ^ 2) heq
  simp only [Real.sq_sqrt (div_nonneg hpos₁.le hpos₂.le)] at this
  simpa using this

/-- After `n` switching cycles the state map is `diag((-Ω₁/Ω₂)^n, (-Ω₂/Ω₁)^n)`,
whose diagonal entries have modulus `(Ω₁/Ω₂)^n` and `(Ω₂/Ω₁)^n`. -/
theorem two_step_pow_entry_abs (Ω₁ Ω₂ : ℝ) (h₁ : 0 < Ω₁) (h₂ : 0 < Ω₂)
    (n : ℕ) :
    |((quarterPeriodTransfer Ω₂ * quarterPeriodTransfer Ω₁) ^ n) 0 0| =
        (Ω₁ / Ω₂) ^ n ∧
    |((quarterPeriodTransfer Ω₂ * quarterPeriodTransfer Ω₁) ^ n) 1 1| =
        (Ω₂ / Ω₁) ^ n := by
  rw [quarterPeriodTransfer_two_step, Matrix.diagonal_pow]
  simp only [Matrix.diagonal_apply_eq]
  constructor
  · simp only [Pi.pow_apply, Matrix.cons_val_zero, abs_pow, abs_neg]
    rw [abs_of_pos (div_pos h₁ h₂)]
  · simp only [Pi.pow_apply, Matrix.cons_val_one, Matrix.head_cons, abs_pow, abs_neg]
    rw [abs_of_pos (div_pos h₂ h₁)]

/-- The larger modulus `ρ = max(Ω₁/Ω₂, Ω₂/Ω₁)` exceeds one when the two
frequencies differ. -/
theorem switching_modulus_gt_one (Ω₁ Ω₂ : ℝ) (h₁ : 0 < Ω₁) (h₂ : 0 < Ω₂)
    (hne : Ω₁ ≠ Ω₂) : 1 < max (Ω₁ / Ω₂) (Ω₂ / Ω₁) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact lt_max_of_lt_right ((one_lt_div h₁).mpr h)
  · exact lt_max_of_lt_left ((one_lt_div h₂).mpr h)

/-- `exp(cT/h)` amplification: `n ≥ T/(Kh)` switching cycles (each of
duration at most `Kh`, filling a slab of length `T`) amplify the corner mode
by at least `exp((log ρ / K) · T/h)` with `ρ > 1`. -/
theorem switching_amplification (ρ T K h : ℝ) (hρ : 1 < ρ) (hK : 0 < K)
    (hh : 0 < h) (n : ℕ) (hn : T / (K * h) ≤ n) :
    Real.exp (Real.log ρ / K * (T / h)) ≤ ρ ^ n := by
  have hlog : 0 < Real.log ρ := Real.log_pos hρ
  have hρpos : 0 < ρ := by linarith
  rw [← Real.exp_log hρpos, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have : Real.log ρ / K * (T / h) = Real.log ρ * (T / (K * h)) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hn hlog.le

end RenewalGeometry
