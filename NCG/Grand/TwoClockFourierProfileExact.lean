/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TwoClockLimitExact
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Fourier-profile lifting for the singular two-clock limit

The modewise limits in `TwoClockLimitExact` are lifted here to an arbitrary
absolutely summable Fourier profile.  The carrier vectors are allowed to depend
on the cutoff.  This is important for the manuscript observable `Φ_N(f)`: one
compares two coefficient multipliers on the same cutoff carrier, rather than
assuming that the cutoff Fourier vectors themselves converge.
-/

open Filter Real NormedSpace
open scoped Topology

namespace NCG
namespace TwoClock

variable {K E A : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A cutoff Fourier synthesis with scalar multiplier `m`. -/
noncomputable def fourierProfile (c : K → ℂ) (v : A → K → E)
    (m : A → K → ℝ) (n : A) : E :=
  ∑' k, c k • ((m n k : ℂ) • v n k)

/-- Dominated Fourier lifting.  Pointwise convergence of real multipliers,
uniform multiplier bounds, and an absolutely summable coefficient envelope
imply convergence of the complete cutoff-dependent Fourier synthesis. -/
theorem fourierProfile_tendsto_of_modewise {𝓕 : Filter A}
    (c : K → ℂ) (v : A → K → E) (m : A → K → ℝ) (limit : K → ℝ)
    (bound : K → ℝ)
    (hsum : Summable fun k => 2 * (‖c k‖ * bound k))
    (hbound : ∀ k, 0 ≤ bound k)
    (hv : ∀ n k, ‖v n k‖ ≤ bound k)
    (hmode : ∀ k, Tendsto (fun n => m n k) 𝓕 (𝓝 (limit k)))
    (hmul : ∀ᶠ n in 𝓕, ∀ k, |m n k| ≤ 1)
    (hlimit : ∀ k, |limit k| ≤ 1) :
    Tendsto (fun n => fourierProfile c v m n -
      ∑' k, c k • ((limit k : ℂ) • v n k)) 𝓕 (𝓝 0) := by
  let term : A → K → E := fun n k =>
    c k • (((m n k - limit k : ℝ) : ℂ) • v n k)
  have hterm : ∀ k, Tendsto (fun n => term n k) 𝓕 (𝓝 0) := by
    intro k
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hdif : Tendsto (fun n => m n k - limit k) 𝓕 (𝓝 0) := by
      simpa using (hmode k).sub (tendsto_const_nhds :
        Tendsto (fun _ : A => limit k) 𝓕 (𝓝 (limit k)))
    have hscalar : Tendsto (fun n => |m n k - limit k|) 𝓕 (𝓝 0) := by
      simpa [Function.comp_def] using
        ((continuous_abs : Continuous (fun x : ℝ => |x|)).tendsto 0).comp hdif
    have hupper : Tendsto (fun n => ‖c k‖ * (|m n k - limit k| * bound k))
        𝓕 (𝓝 0) := by
      simpa using (hscalar.mul_const (bound k)).const_mul ‖c k‖
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hupper
    filter_upwards with n
    simp only [term, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hv n k) (abs_nonneg _)) (norm_nonneg _)
  have hdom : ∀ᶠ n in 𝓕, ∀ k, ‖term n k‖ ≤ 2 * (‖c k‖ * bound k) := by
    filter_upwards [hmul] with n hn k
    simp only [term, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have hd : |m n k - limit k| ≤ 2 := by
      calc
        |m n k - limit k| ≤ |m n k| + |limit k| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (hn k) (hlimit k)
        _ = 2 := by norm_num
    calc
      ‖c k‖ * (|m n k - limit k| * ‖v n k‖)
          ≤ ‖c k‖ * (|m n k - limit k| * bound k) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hv n k) (abs_nonneg _))
              (norm_nonneg _)
      _ ≤ ‖c k‖ * (2 * bound k) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hd (hbound k))
              (norm_nonneg _)
      _ = 2 * (‖c k‖ * bound k) := by ring
  have ht := tendsto_tsum_of_dominated_convergence hsum hterm hdom
  have hsumM : ∀ᶠ n in 𝓕, Summable fun k =>
      c k • ((m n k : ℂ) • v n k) := by
    filter_upwards [hmul] with n hn
    apply Summable.of_norm_bounded hsum
    intro k
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖c k‖ * (|m n k| * ‖v n k‖)
          ≤ ‖c k‖ * (1 * ‖v n k‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hn k) (norm_nonneg _))
              (norm_nonneg _)
      _ ≤ ‖c k‖ * (1 * bound k) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hv n k) zero_le_one)
              (norm_nonneg _)
      _ ≤ 2 * (‖c k‖ * bound k) := by
            have hp : 0 ≤ ‖c k‖ * bound k :=
              mul_nonneg (norm_nonneg _) (hbound k)
            nlinarith
  have hsumL : ∀ n, Summable fun k =>
      c k • ((limit k : ℂ) • v n k) := by
    intro n
    apply Summable.of_norm_bounded hsum
    intro k
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖c k‖ * (|limit k| * ‖v n k‖)
          ≤ ‖c k‖ * (1 * ‖v n k‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hlimit k) (norm_nonneg _))
              (norm_nonneg _)
      _ ≤ ‖c k‖ * (1 * bound k) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hv n k) zero_le_one)
              (norm_nonneg _)
      _ ≤ 2 * (‖c k‖ * bound k) := by
            have hp : 0 ≤ ‖c k‖ * bound k :=
              mul_nonneg (norm_nonneg _) (hbound k)
            nlinarith
  have heq : (fun n => fourierProfile c v m n -
      ∑' k, c k • ((limit k : ℂ) • v n k)) =ᶠ[𝓕]
      fun n => ∑' k, term n k := by
    filter_upwards [hsumM] with n hMn
    rw [fourierProfile, ← hMn.tsum_sub (hsumL n)]
    apply tsum_congr
    intro k
    simp only [term]
    module
  simpa only [tsum_zero] using ht.congr' heq.symm

/-! ### The complete fast-clock Fourier profile -/

/-- The exact cutoff multiplier on the fast clock. -/
noncomputable def fastMultiplier (lam kappa : ℕ → ℝ) (σ : ℝ)
    (a : Fin 3 → ℝ) (N : ℕ) : ℝ :=
  Real.exp (-(σ / kappa N) *
    (22 * lam N / 15 + 4 * kappa N * (N : ℝ) ^ 2 *
      ∑ j : Fin 3, Real.sin (π * a j / N) ^ 2))

/-- The continuum heat multiplier of a fixed Fourier mode. -/
noncomputable def heatMultiplier (σ : ℝ) (a : Fin 3 → ℝ) : ℝ :=
  Real.exp (-σ * (4 * π ^ 2 * ∑ j : Fin 3, (a j) ^ 2))

/-- **Fast-clock field limit.**  Every absolutely summable Fourier profile
converges, in the norm of the cutoff observable carrier, to its heat-evolved
profile.  The carrier modes may vary with `N`. -/
theorem fast_clock_fourierProfile
    (lam kappa : ℕ → ℝ) (σ : ℝ) (freq : K → Fin 3 → ℝ)
    (c : K → ℂ) (v : ℕ → K → E) (bound : K → ℝ)
    (hσ : 0 ≤ σ) (hlam : ∀ N, 0 ≤ lam N) (hκ : ∀ N, 0 < kappa N)
    (hratio : Tendsto (fun N => lam N / kappa N) atTop (𝓝 0))
    (hsum : Summable fun k => 2 * (‖c k‖ * bound k))
    (hbound : ∀ k, 0 ≤ bound k) (hv : ∀ N k, ‖v N k‖ ≤ bound k) :
    Tendsto (fun N =>
      fourierProfile c v (fun N k => fastMultiplier lam kappa σ (freq k) N) N -
        ∑' k, c k • ((heatMultiplier σ (freq k) : ℂ) • v N k))
      atTop (𝓝 0) := by
  apply fourierProfile_tendsto_of_modewise c v
    (fun N k => fastMultiplier lam kappa σ (freq k) N)
    (fun k => heatMultiplier σ (freq k)) bound hsum hbound hv
  · intro k
    exact fast_clock_multiplier lam kappa (freq k) σ hκ hratio
  · exact Eventually.of_forall fun N k => by
      rw [fastMultiplier, abs_of_pos (Real.exp_pos _), ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hrate : 0 ≤ 22 * lam N / 15 +
          4 * kappa N * (N : ℝ) ^ 2 *
            ∑ j : Fin 3, Real.sin (π * freq k j / N) ^ 2 := by
        have hsin : 0 ≤ ∑ j : Fin 3,
            Real.sin (π * freq k j / N) ^ 2 :=
          Finset.sum_nonneg fun j _ => sq_nonneg _
        have hrenew : 0 ≤ 22 * lam N / 15 :=
          div_nonneg (mul_nonneg (by norm_num) (hlam N)) (by norm_num)
        exact add_nonneg hrenew
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hκ N).le)
            (sq_nonneg _)) hsin)
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (div_nonneg hσ (hκ N).le)) hrate
  · intro k
    rw [heatMultiplier, abs_of_pos (Real.exp_pos _), ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hsq : 0 ≤ ∑ j : Fin 3, (freq k j) ^ 2 := by positivity
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ)
      (mul_nonneg (show 0 ≤ 4 * π ^ 2 by positivity) hsq)

/-! ### The complete slow-clock Fourier profile -/

/-- The exact cutoff multiplier on the slow renewal clock. -/
noncomputable def slowMultiplier (lam kappa : ℕ → ℝ) (s : ℝ)
    (a : Fin 3 → ℝ) (N : ℕ) : ℝ :=
  Real.exp (-(s / lam N) *
    (22 * lam N / 15 + 4 * kappa N * (N : ℝ) ^ 2 *
      ∑ j : Fin 3, Real.sin (π * a j / N) ^ 2))

/-- Only the spatial mean survives on the slow clock. -/
noncomputable def slowLimit (s : ℝ) (a : Fin 3 → ℝ) : ℝ :=
  if a = 0 then Real.exp (-22 * s / 15) else 0

private theorem sum_sq_pos_of_ne_zero (a : Fin 3 → ℝ) (ha : a ≠ 0) :
    0 < ∑ j : Fin 3, (a j) ^ 2 := by
  rw [Fin.sum_univ_three]
  have h0 := sq_nonneg (a 0)
  have h1 := sq_nonneg (a 1)
  have h2 := sq_nonneg (a 2)
  by_contra h
  have hsum : (a 0) ^ 2 + (a 1) ^ 2 + (a 2) ^ 2 = 0 := by
    exact le_antisymm (not_lt.mp h) (by positivity)
  have ha0 : a 0 = 0 := by nlinarith [sq_nonneg (a 0)]
  have ha1 : a 1 = 0 := by nlinarith [sq_nonneg (a 1)]
  have ha2 : a 2 = 0 := by nlinarith [sq_nonneg (a 2)]
  apply ha
  funext j
  fin_cases j <;> assumption

/-- **Slow-clock field limit.**  Every absolutely summable Fourier profile
collapses to its zero-frequency (spatial mean) profile with the scalar renewal
factor `exp (-22s/15)`; all nonzero modes vanish in carrier norm. -/
theorem slow_clock_fourierProfile
    (lam kappa : ℕ → ℝ) (s : ℝ) (freq : K → Fin 3 → ℝ)
    (c : K → ℂ) (v : ℕ → K → E) (bound : K → ℝ)
    (hs : 0 < s) (hlam : ∀ N, 0 < lam N) (hκ : ∀ N, 0 ≤ kappa N)
    (hratio : Tendsto (fun N => kappa N / lam N) atTop atTop)
    (hsum : Summable fun k => 2 * (‖c k‖ * bound k))
    (hbound : ∀ k, 0 ≤ bound k) (hv : ∀ N k, ‖v N k‖ ≤ bound k) :
    Tendsto (fun N =>
      fourierProfile c v (fun N k => slowMultiplier lam kappa s (freq k) N) N -
        ∑' k, c k • ((slowLimit s (freq k) : ℂ) • v N k))
      atTop (𝓝 0) := by
  apply fourierProfile_tendsto_of_modewise c v
    (fun N k => slowMultiplier lam kappa s (freq k) N)
    (fun k => slowLimit s (freq k)) bound hsum hbound hv
  · intro k
    by_cases hz : freq k = 0
    · have heq : (fun N => slowMultiplier lam kappa s (freq k) N) =
          fun _ => Real.exp (-22 * s / 15) := by
        funext N
        simp only [slowMultiplier, hz, Pi.zero_apply, mul_zero, zero_div,
          Real.sin_zero]
        congr 1
        field_simp [(hlam N).ne']
        ring
      rw [heq]
      simp [slowLimit, hz]
    · rw [slowLimit, if_neg hz]
      exact slow_clock_nonzero_multiplier lam kappa (freq k) s hs hlam hratio
        (sum_sq_pos_of_ne_zero (freq k) hz)
  · exact Eventually.of_forall fun N k => by
      rw [slowMultiplier, abs_of_pos (Real.exp_pos _), ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hsin : 0 ≤ ∑ j : Fin 3,
          Real.sin (π * freq k j / N) ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      have hrenew : 0 ≤ 22 * lam N / 15 :=
        div_nonneg (mul_nonneg (by norm_num) (hlam N).le) (by norm_num)
      have hrate : 0 ≤ 22 * lam N / 15 +
          4 * kappa N * (N : ℝ) ^ 2 *
            ∑ j : Fin 3, Real.sin (π * freq k j / N) ^ 2 :=
        add_nonneg hrenew
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hκ N))
            (sq_nonneg _)) hsin)
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (div_nonneg hs.le (hlam N).le)) hrate
  · intro k
    by_cases hz : freq k = 0
    · rw [slowLimit, if_pos hz, abs_of_pos (Real.exp_pos _), ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      calc
        -22 * s / 15 = -(22 * s / 15) := by ring
        _ ≤ 0 := neg_nonpos.mpr (show 0 ≤ 22 * s / 15 from
          div_nonneg (mul_nonneg (show 0 ≤ (22 : ℝ) by norm_num) hs.le)
            (show 0 ≤ (15 : ℝ) by norm_num))
    · simp [slowLimit, hz]

end TwoClock
end NCG
