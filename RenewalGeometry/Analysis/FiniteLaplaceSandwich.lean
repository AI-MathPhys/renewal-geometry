/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The low-temperature Laplace sandwich on a finite grid

For a finite nonempty index set `s` of cardinality `m`, a cost `f : ι → ℝ` and a temperature
`ε > 0`, the *normalized soft minimum*
`softMin ε s f = -ε log (m⁻¹ ∑_{i ∈ s} exp (-f i / ε))`
is the free energy of the uniform (probability-normalized) grid average of the Boltzmann
weights.  It satisfies the elementary Laplace sandwich

* `le_softMin`: if `L ≤ f i` for every `i ∈ s`, then `L ≤ softMin ε s f`;
* `softMin_le`: for every `i₀ ∈ s`, `softMin ε s f ≤ f i₀ + ε log m`;

so that `min_s f ≤ softMin ε s f ≤ min_s f + ε log m`.  The normalization by `m⁻¹` is what
makes the lower bound free of an entropy term: with the unnormalized counting sum one only has
`min_s f − ε log m ≤ −ε log ∑ exp(−f/ε) ≤ min_s f`.

This is the finite-grid Laplace estimate used for `eq:supp-finite-block-error`
(`thm:main-no-blocking-attractor`, emergent-spacetime manuscript).
-/

namespace RenewalGeometry.FiniteLaplace

open Real

variable {ι : Type*}

/-- The normalized soft minimum `-ε log (m⁻¹ ∑_{i∈s} exp(-f i/ε))`, `m = #s`. -/
noncomputable def softMin (ε : ℝ) (s : Finset ι) (f : ι → ℝ) : ℝ :=
  -ε * Real.log (((s.card : ℝ))⁻¹ * ∑ i ∈ s, Real.exp (-f i / ε))

/-- The grid average of Boltzmann weights is positive on a nonempty grid. -/
theorem average_pos (ε : ℝ) {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    0 < ((s.card : ℝ))⁻¹ * ∑ i ∈ s, Real.exp (-f i / ε) := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  exact mul_pos (inv_pos.2 hc) (Finset.sum_pos (fun i _ => Real.exp_pos _) hs)

/-- **Lower Laplace bound.**  If `L ≤ f i` on the grid, then `L ≤ softMin ε s f`. -/
theorem le_softMin {ε : ℝ} (hε : 0 < ε) {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) {L : ℝ}
    (hL : ∀ i ∈ s, L ≤ f i) : L ≤ softMin ε s f := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hsum : ∑ i ∈ s, Real.exp (-f i / ε) ≤ s.card * Real.exp (-L / ε) := by
    have : ∑ i ∈ s, Real.exp (-f i / ε) ≤ ∑ _i ∈ s, Real.exp (-L / ε) := by
      refine Finset.sum_le_sum fun i hi => Real.exp_le_exp.2 ?_
      have := hL i hi
      rw [div_le_div_iff_of_pos_right hε]; linarith
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have havg : ((s.card : ℝ))⁻¹ * ∑ i ∈ s, Real.exp (-f i / ε) ≤ Real.exp (-L / ε) := by
    rw [inv_mul_le_iff₀ hc]; exact hsum
  have hlog : Real.log (((s.card : ℝ))⁻¹ * ∑ i ∈ s, Real.exp (-f i / ε)) ≤ -L / ε := by
    have := Real.log_le_log (average_pos ε hs f) havg
    rwa [Real.log_exp] at this
  unfold softMin
  have : -L ≥ ε * Real.log (((s.card : ℝ))⁻¹ * ∑ i ∈ s, Real.exp (-f i / ε)) := by
    have h2 := mul_le_mul_of_nonneg_left hlog hε.le
    rwa [mul_div_cancel₀ _ hε.ne'] at h2
  linarith

/-- **Upper Laplace bound.**  For every grid point `i₀ ∈ s`,
`softMin ε s f ≤ f i₀ + ε log #s`. -/
theorem softMin_le {ε : ℝ} (hε : 0 < ε) {s : Finset ι} (f : ι → ℝ) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    softMin ε s f ≤ f i₀ + ε * Real.log s.card := by
  have hs : s.Nonempty := ⟨i₀, hi₀⟩
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hsum : Real.exp (-f i₀ / ε) ≤ ∑ i ∈ s, Real.exp (-f i / ε) :=
    Finset.single_le_sum (f := fun i => Real.exp (-f i / ε)) (fun i _ => (Real.exp_pos _).le) hi₀
  have havg : ((s.card : ℝ))⁻¹ * Real.exp (-f i₀ / ε)
      ≤ ((s.card : ℝ))⁻¹ * ∑ i ∈ s, Real.exp (-f i / ε) :=
    mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hc.le)
  have hlog := Real.log_le_log (mul_pos (inv_pos.2 hc) (Real.exp_pos _)) havg
  rw [Real.log_mul (inv_pos.2 hc).ne' (Real.exp_pos _).ne', Real.log_inv, Real.log_exp] at hlog
  unfold softMin
  have h2 := mul_le_mul_of_nonneg_left hlog hε.le
  have : ε * (-Real.log s.card + -f i₀ / ε) = -ε * Real.log s.card - f i₀ := by
    field_simp; ring
  rw [this] at h2
  linarith

/-- **Laplace sandwich** `L ≤ softMin ε s f ≤ f i₀ + ε log #s`. -/
theorem softMin_sandwich {ε : ℝ} (hε : 0 < ε) {s : Finset ι} (f : ι → ℝ) {L : ℝ}
    (hL : ∀ i ∈ s, L ≤ f i) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    L ≤ softMin ε s f ∧ softMin ε s f ≤ f i₀ + ε * Real.log s.card :=
  ⟨le_softMin hε ⟨i₀, hi₀⟩ f hL, softMin_le hε f hi₀⟩

/-- The soft minimum is the free energy of the grid average: `exp (-softMin/ε)` is the
average of the Boltzmann weights. -/
theorem exp_neg_softMin_div {ε : ℝ} (hε : ε ≠ 0) {s : Finset ι} (hs : s.Nonempty)
    (f : ι → ℝ) :
    Real.exp (-softMin ε s f / ε) = ((s.card : ℝ))⁻¹ * ∑ i ∈ s, Real.exp (-f i / ε) := by
  unfold softMin
  rw [show -(-ε * Real.log (((s.card : ℝ))⁻¹ * ∑ i ∈ s, Real.exp (-f i / ε))) / ε
      = Real.log (((s.card : ℝ))⁻¹ * ∑ i ∈ s, Real.exp (-f i / ε)) by field_simp,
    Real.exp_log (average_pos ε hs f)]

end RenewalGeometry.FiniteLaplace
