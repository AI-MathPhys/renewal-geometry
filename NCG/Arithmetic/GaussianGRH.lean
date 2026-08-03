/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Arithmetic.LaplacePole

/-!
# Gaussian Hardy criterion for GRH
  (`thm:gaussian-grh`, arithmetic manuscript)

For the Gaussian zero packet `f(r) = R(r) + Σ_ρ c_ρ e^{λ_ρ r}`
with `λ_ρ = ρ - 1/2`:

* `(i)` if `σ` exceeds every exponent displacement, the weighted
  energy `∫ e^{-2σr}|f|² dr` is finite
  (`gaussian_energy_finite`): the packet is dominated by
  `C_R + S·e^{Θ'r}` with `S = Σ|c_ρ| < ∞`, and the two resulting
  exponentials are integrable against `e^{-2σr}`;
* `(ii)` if the energy is finite, every tested displacement obeys
  `Re λ_ρ ≤ σ` — this is exactly the Laplace-pole obstruction
  `laplace_pole_obstruction` of the `lem:laplace-pole` record;
  reflection symmetry (`ρ ↦ 1 - ρ̄`, i.e. `λ ↦ -λ̄`) applies the
  same bound to the reflected exponent, giving `|Re λ_ρ| ≤ σ`;
* `(iii)` finiteness at every positive `σ` therefore forces every
  displacement to vanish (`gaussian_grh_criterion`) — the
  Gaussian Hardy criterion: GRH is equivalent to finiteness of
  the energy for every `σ > 0`.

Rendering disclosed: the Gaussian specialization of the explicit
formula producing the zero expansion (the summability of the
grouped coefficients, the remainder `R` with entire transform,
and the reflection symmetry of the zero set) enters as the
displayed hypotheses shared with the `lem:laplace-pole` record;
the principal-channel pole clearing is prose.
-/

open MeasureTheory Set Filter Topology

namespace NCG

/-- `(i)`: above every displacement the Gaussian packet has
finite weighted energy. -/
theorem gaussian_energy_finite
    (f R : ℝ → ℂ) (c lam : ℕ → ℂ) (σ Θ CR : ℝ)
    (hσ0 : 0 < σ) (hΘσ : Θ < σ)
    (hcs : Summable fun j => ‖c j‖)
    (hlam : ∀ j, (lam j).re ≤ Θ)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ r : ℝ, 0 < r →
      f r = R r + ∑' j, c j * Complex.exp (lam j * r))
    (hRb : ∀ r : ℝ, 0 < r → ‖R r‖ ≤ CR) :
    IntegrableOn
      (fun r => Real.exp (-(2 * σ) * r) * ‖f r‖ ^ 2)
      (Ioi 0) := by
  set S : ℝ := ∑' j, ‖c j‖ with hS_def
  have hS0 : 0 ≤ S := tsum_nonneg fun j => norm_nonneg _
  have hCR0 : 0 ≤ CR := le_trans (norm_nonneg _) (hRb 1 one_pos)
  set Θ' : ℝ := max Θ 0 with hΘ'_def
  have hΘ'σ : Θ' < σ := max_lt hΘσ hσ0
  have hfb : ∀ r : ℝ, 0 < r →
      ‖f r‖ ≤ CR + S * Real.exp (Θ' * r) := by
    intro r hr
    rw [hf r hr]
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (hRb r hr) ?_
    have hbnd : ∀ j, ‖c j * Complex.exp (lam j * r)‖
        ≤ ‖c j‖ * Real.exp (Θ' * r) := by
      intro j
      rw [norm_mul, Complex.norm_exp]
      have h1 : (lam j * r).re = (lam j).re * r := by
        simp [Complex.mul_re]
      rw [h1]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine Real.exp_le_exp.mpr ?_
      refine mul_le_mul_of_nonneg_right ?_ hr.le
      exact le_trans (hlam j) (le_max_left _ _)
    have hsum : Summable fun j =>
        ‖c j * Complex.exp (lam j * r)‖ :=
      Summable.of_nonneg_of_le (fun j => norm_nonneg _) hbnd
        (hcs.mul_right (Real.exp (Θ' * r)))
    refine le_trans (norm_tsum_le_tsum_norm hsum) ?_
    calc ∑' j, ‖c j * Complex.exp (lam j * r)‖
        ≤ ∑' j, ‖c j‖ * Real.exp (Θ' * r) :=
          hsum.tsum_le_tsum hbnd
            (hcs.mul_right (Real.exp (Θ' * r)))
      _ = S * Real.exp (Θ' * r) := by
          rw [tsum_mul_right]
  refine Integrable.mono'
    (g := fun r => 2 * CR ^ 2 * Real.exp (-(2 * σ) * r)
      + 2 * S ^ 2 * Real.exp (-(2 * (σ - Θ')) * r)) ?_ ?_ ?_
  · exact ((integrableOn_exp_mul_Ioi (by linarith) 0).const_mul
      _).add
      ((integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _)
  · refine (Continuous.aestronglyMeasurable
      (by fun_prop)).mul ?_
    exact (hfm.norm.mul hfm.norm).congr
      (Eventually.of_forall fun r => (pow_two ‖f r‖).symm)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (ae_of_all _ ?_)
    intro r hr
    have h1 := hfb r hr
    have h2 : Real.exp (-(2 * σ) * r) * ‖f r‖ ^ 2
        ≤ Real.exp (-(2 * σ) * r)
          * (CR + S * Real.exp (Θ' * r)) ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have h3 : (0 : ℝ) ≤ ‖f r‖ := norm_nonneg _
      nlinarith
    have h4 : Real.exp (-(2 * σ) * r)
        * (CR + S * Real.exp (Θ' * r)) ^ 2
        ≤ 2 * CR ^ 2 * Real.exp (-(2 * σ) * r)
          + 2 * S ^ 2 * Real.exp (-(2 * (σ - Θ')) * r) := by
      rw [show -(2 * (σ - Θ')) * r
          = -(2 * σ) * r + (Θ' * r + Θ' * r) by ring,
        Real.exp_add, Real.exp_add]
      nlinarith [sq_nonneg (CR - S * Real.exp (Θ' * r)),
        Real.exp_pos (-(2 * σ) * r), Real.exp_pos (Θ' * r),
        mul_pos (Real.exp_pos (-(2 * σ) * r))
          (Real.exp_pos (Θ' * r))]
    have h5 : ‖Real.exp (-(2 * σ) * r) * ‖f r‖ ^ 2‖
        = Real.exp (-(2 * σ) * r) * ‖f r‖ ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [h5]
    linarith

/-- `(iii)`: a displacement dominated by every positive Gaussian
scale — on both sides of the reflection — vanishes; hence
finiteness of the energy for every `σ > 0` is the Hardy
criterion. -/
theorem gaussian_grh_criterion (a : ℝ)
    (h1 : ∀ σ : ℝ, 0 < σ → a ≤ σ)
    (h2 : ∀ σ : ℝ, 0 < σ → -a ≤ σ) : a = 0 := by
  by_contra h
  rcases lt_or_gt_of_ne h with hneg | hpos
  · have := h2 (-a / 2) (by linarith)
    linarith
  · have := h1 (a / 2) (by linarith)
    linarith

end NCG
