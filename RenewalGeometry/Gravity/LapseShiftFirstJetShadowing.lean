/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.LapseShiftClockTest

/-!
# First-jet harmonic shadowing forces the lapse--shift clock rate to vanish
(`prop:supp-exact-clock-test`, `eq:supp-exact-rate-necessary`; emergent-spacetime
manuscript)

This file formalizes the geometric step of the paper's proof that was left as the
hypothesis `hl` of `lapse_shift_clock_condition` in
`RenewalGeometry.Gravity.LapseShiftClockTest`, and composes the two.

Along a regulator family `i ↦ (N_i, β_i, γ_i)` (exact-action ADM data) and
`i ↦ (N'_i, β'_i)` (small harmonic ADM data with the same spatial metric `γ_i` and the
same lapse `N = 1` and shift `β = 0` at the initial cut `t₀`):

* `first_jet_shadowing_lapse_shift_rate` (**step (ii)**): if the initial first time
  derivatives of `g₀₀` and `g₀ᵢ` of the exact metric shadow those of the harmonic
  metric (differences `→ 0`), the harmonic first jet is small (`∂ₜN' → 0`,
  `∂ₜβ' → 0`), and the spatial metrics are uniformly coercive at the initial cut
  (`c‖x‖² ≤ ⟨x, γ_i x⟩`, `c > 0`), then `∂ₜ N_i → 0` and `∂ₜ β_i^j → 0`.  The proof
  uses the ADM identities `∂ₜ g₀₀ = −2 ∂ₜ N`, `∂ₜ g₀ᵢ = γ_{ij} ∂ₜ β^j`
  (`admMetric00_hasDerivAt`, `admMetric0i_hasDerivAt`) and Cauchy--Schwarz.
* `clock_test_of_first_jet_shadowing` (**step (iii)**, `eq:supp-exact-rate-necessary`):
  combining with the graded rate norm `eq:supp-exact-rate-norm` and the
  identification `‖λ_t‖² = (∂ₜN)² + Σ_j (∂ₜβ^j)²` of the multiplier rate with the
  lapse--shift first jet, one gets `a⁻¹‖(u_a)_A‖ → 0` and `a⁻²‖(u_a)_W‖ → 0`.

What remains an interface: the identification of `λ_t` with the lapse--shift first
jet of the exact-action metric and the graded norm identity are hypotheses
(`hlam`, `hnorm`); they belong to the exact-action multiplier structure
(`thm:supp-exact-time-sources`, grading `S_a`), not formalized here.
-/

open scoped BigOperators Topology
open Filter

namespace RenewalGeometry

/-- Squared Euclidean norm on `Fin 3 → ℝ`. -/
def sumSq (x : Fin 3 → ℝ) : ℝ := ∑ j, x j ^ 2

theorem sumSq_nonneg (x : Fin 3 → ℝ) : 0 ≤ sumSq x :=
  Finset.sum_nonneg fun j _ => sq_nonneg (x j)

/-- Coercivity plus Cauchy--Schwarz: if `c ‖x‖² ≤ ⟨x, M x⟩` then `c² ‖x‖² ≤ ‖M x‖²`. -/
theorem sumSq_le_of_coercive (c : ℝ) (hc : 0 < c) (M : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (hcoer : c * sumSq x ≤ ∑ j, x j * (∑ k, M j k * x k)) :
    c ^ 2 * sumSq x ≤ sumSq (fun j => ∑ k, M j k * x k) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (fun j => ∑ k, M j k * x k)
  have hS := sumSq_nonneg x
  have h0 : 0 ≤ c * sumSq x := mul_nonneg hc.le hS
  have hsq : (c * sumSq x) ^ 2 ≤ sumSq x * sumSq (fun j => ∑ k, M j k * x k) := by
    calc (c * sumSq x) ^ 2 ≤ (∑ j, x j * (∑ k, M j k * x k)) ^ 2 := by
          exact pow_le_pow_left₀ h0 hcoer 2
      _ ≤ (∑ j, x j ^ 2) * ∑ j, (∑ k, M j k * x k) ^ 2 := hcs
      _ = sumSq x * sumSq (fun j => ∑ k, M j k * x k) := rfl
  rcases hS.lt_or_eq with hpos | hzero
  · have : c ^ 2 * sumSq x * sumSq x ≤ sumSq (fun j => ∑ k, M j k * x k) * sumSq x := by
      nlinarith [hsq]
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]
    simp [sumSq_nonneg]

/-- If `‖x_i‖² → 0` then each coordinate `x_i j → 0`. -/
theorem tendsto_coord_of_sumSq {ι : Type*} (l : Filter ι) (x : ι → Fin 3 → ℝ)
    (h : Tendsto (fun i => sumSq (x i)) l (𝓝 0)) (j : Fin 3) :
    Tendsto (fun i => x i j) l (𝓝 0) := by
  have hsqrt : Tendsto (fun i => Real.sqrt (sumSq (x i))) l (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h
    rw [Real.sqrt_zero] at this
    exact this
  refine squeeze_zero_norm (fun i => ?_) hsqrt
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (fun k _ => sq_nonneg (x i k)) (Finset.mem_univ j)

/-- **Step (ii)**: first-jet shadowing of a small harmonic metric with matched initial
lapse, shift and spatial metric forces the exact-action lapse--shift clock rate
`(∂ₜN, ∂ₜβ)` to vanish along the family. -/
theorem first_jet_shadowing_lapse_shift_rate {ι : Type*} (l : Filter ι) (t₀ : ℝ)
    (N N' : ι → ℝ → ℝ) (β β' : ι → ℝ → Fin 3 → ℝ) (γ : ι → ℝ → Fin 3 → Fin 3 → ℝ)
    (N₁ N₁' : ι → ℝ) (β₁ β₁' : ι → Fin 3 → ℝ) (γ₁ : ι → Fin 3 → Fin 3 → ℝ)
    (hN : ∀ i, HasDerivAt (N i) (N₁ i) t₀) (hN' : ∀ i, HasDerivAt (N' i) (N₁' i) t₀)
    (hβ : ∀ i j, HasDerivAt (fun t => β i t j) (β₁ i j) t₀)
    (hβ' : ∀ i j, HasDerivAt (fun t => β' i t j) (β₁' i j) t₀)
    (hγ : ∀ i j k, HasDerivAt (fun t => γ i t j k) (γ₁ i j k) t₀)
    (hN0 : ∀ i, N i t₀ = 1) (hN0' : ∀ i, N' i t₀ = 1)
    (hβ0 : ∀ i j, β i t₀ j = 0) (hβ0' : ∀ i j, β' i t₀ j = 0)
    (c : ℝ) (hc : 0 < c)
    (hcoer : ∀ i (x : Fin 3 → ℝ), c * sumSq x ≤ ∑ j, x j * (∑ k, γ i t₀ j k * x k))
    (hshadow00 : Tendsto (fun i => deriv (admMetric00 (N i) (γ i) (β i)) t₀
      - deriv (admMetric00 (N' i) (γ i) (β' i)) t₀) l (𝓝 0))
    (hshadow0i : ∀ j, Tendsto (fun i => deriv (admMetric0i (γ i) (β i) j) t₀
      - deriv (admMetric0i (γ i) (β' i) j) t₀) l (𝓝 0))
    (hsmallN : Tendsto N₁' l (𝓝 0)) (hsmallβ : ∀ j, Tendsto (fun i => β₁' i j) l (𝓝 0)) :
    Tendsto N₁ l (𝓝 0) ∧ ∀ j, Tendsto (fun i => β₁ i j) l (𝓝 0) := by
  -- lapse: `∂ₜ g₀₀ = −2 ∂ₜ N` for both metrics
  have h00 : ∀ i, deriv (admMetric00 (N i) (γ i) (β i)) t₀
      - deriv (admMetric00 (N' i) (γ i) (β' i)) t₀ = -2 * (N₁ i - N₁' i) := by
    intro i
    rw [(admMetric00_hasDerivAt (N i) (γ i) (β i) (N₁ i) (γ₁ i) (β₁ i) t₀ (hN i) (hγ i) (hβ i)
        (hN0 i) (hβ0 i)).deriv,
      (admMetric00_hasDerivAt (N' i) (γ i) (β' i) (N₁' i) (γ₁ i) (β₁' i) t₀ (hN' i) (hγ i)
        (hβ' i) (hN0' i) (hβ0' i)).deriv]
    ring
  have hNdiff : Tendsto (fun i => N₁ i - N₁' i) l (𝓝 0) := by
    have h := hshadow00.const_mul (-1 / 2)
    simp only [mul_zero] at h
    refine h.congr fun i => ?_
    rw [h00 i]
    ring
  have hNlim : Tendsto N₁ l (𝓝 0) := by
    have := hNdiff.add hsmallN
    simp only [add_zero] at this
    refine this.congr fun i => ?_
    ring
  -- shift: `∂ₜ g₀ⱼ = γ_{jk} ∂ₜ β^k` for both metrics
  have h0i : ∀ i j, deriv (admMetric0i (γ i) (β i) j) t₀ - deriv (admMetric0i (γ i) (β' i) j) t₀
      = ∑ k, γ i t₀ j k * (β₁ i k - β₁' i k) := by
    intro i j
    rw [(admMetric0i_hasDerivAt (γ i) (β i) (γ₁ i) (β₁ i) t₀ (hγ i) (hβ i) (hβ0 i) j).deriv,
      (admMetric0i_hasDerivAt (γ i) (β' i) (γ₁ i) (β₁' i) t₀ (hγ i) (hβ' i) (hβ0' i) j).deriv,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  -- the image `γ (∂ₜβ − ∂ₜβ')` tends to zero in squared norm
  have hT : Tendsto (fun i => sumSq (fun j => ∑ k, γ i t₀ j k * (β₁ i k - β₁' i k))) l (𝓝 0) := by
    have h : ∀ j, Tendsto (fun i => (∑ k, γ i t₀ j k * (β₁ i k - β₁' i k)) ^ 2) l (𝓝 0) := by
      intro j
      have := ((hshadow0i j).congr fun i => h0i i j).pow 2
      simpa using this
    have := tendsto_finsetSum Finset.univ fun j _ => h j
    simpa [sumSq] using this
  -- coercivity transfers this to `∂ₜβ − ∂ₜβ'`
  have hS : Tendsto (fun i => sumSq (fun k => β₁ i k - β₁' i k)) l (𝓝 0) := by
    have hbound : ∀ i, sumSq (fun k => β₁ i k - β₁' i k)
        ≤ (1 / c ^ 2) * sumSq (fun j => ∑ k, γ i t₀ j k * (β₁ i k - β₁' i k)) := by
      intro i
      have := sumSq_le_of_coercive c hc (γ i t₀) (fun k => β₁ i k - β₁' i k) (hcoer i _)
      have hc2 : 0 < c ^ 2 := by positivity
      calc sumSq (fun k => β₁ i k - β₁' i k)
          = (c ^ 2 * sumSq (fun k => β₁ i k - β₁' i k)) / c ^ 2 := by field_simp
        _ ≤ sumSq (fun j => ∑ k, γ i t₀ j k * (β₁ i k - β₁' i k)) / c ^ 2 :=
            div_le_div_of_nonneg_right this hc2.le
        _ = (1 / c ^ 2) * sumSq (fun j => ∑ k, γ i t₀ j k * (β₁ i k - β₁' i k)) := by ring
    have hlim := hT.const_mul (1 / c ^ 2)
    simp only [mul_zero] at hlim
    exact squeeze_zero (fun i => sumSq_nonneg _) hbound hlim
  refine ⟨hNlim, fun j => ?_⟩
  have hdiff := tendsto_coord_of_sumSq l (fun i k => β₁ i k - β₁' i k) hS j
  have := hdiff.add (hsmallβ j)
  simp only [add_zero] at this
  refine this.congr fun i => ?_
  ring

/-- **`prop:supp-exact-clock-test`**, composed form (`eq:supp-exact-rate-necessary`): under
first-jet shadowing of a small harmonic metric (as in
`first_jet_shadowing_lapse_shift_rate`), the graded rate norm `eq:supp-exact-rate-norm`
(`hnorm`) and the identification of the multiplier rate with the lapse--shift first jet
`‖λ_t‖² = (∂ₜN)² + Σ_j (∂ₜβ^j)²` (`hlam`) force `a⁻¹‖(u_a)_A‖ → 0` and `a⁻²‖(u_a)_W‖ → 0`.
No assumption on the electric coefficient enters. -/
theorem clock_test_of_first_jet_shadowing {ι : Type*} (l : Filter ι) (t₀ : ℝ)
    (N N' : ι → ℝ → ℝ) (β β' : ι → ℝ → Fin 3 → ℝ) (γ : ι → ℝ → Fin 3 → Fin 3 → ℝ)
    (N₁ N₁' : ι → ℝ) (β₁ β₁' : ι → Fin 3 → ℝ) (γ₁ : ι → Fin 3 → Fin 3 → ℝ)
    (hN : ∀ i, HasDerivAt (N i) (N₁ i) t₀) (hN' : ∀ i, HasDerivAt (N' i) (N₁' i) t₀)
    (hβ : ∀ i j, HasDerivAt (fun t => β i t j) (β₁ i j) t₀)
    (hβ' : ∀ i j, HasDerivAt (fun t => β' i t j) (β₁' i j) t₀)
    (hγ : ∀ i j k, HasDerivAt (fun t => γ i t j k) (γ₁ i j k) t₀)
    (hN0 : ∀ i, N i t₀ = 1) (hN0' : ∀ i, N' i t₀ = 1)
    (hβ0 : ∀ i j, β i t₀ j = 0) (hβ0' : ∀ i j, β' i t₀ j = 0)
    (c : ℝ) (hc : 0 < c)
    (hcoer : ∀ i (x : Fin 3 → ℝ), c * sumSq x ≤ ∑ j, x j * (∑ k, γ i t₀ j k * x k))
    (hshadow00 : Tendsto (fun i => deriv (admMetric00 (N i) (γ i) (β i)) t₀
      - deriv (admMetric00 (N' i) (γ i) (β' i)) t₀) l (𝓝 0))
    (hshadow0i : ∀ j, Tendsto (fun i => deriv (admMetric0i (γ i) (β i) j) t₀
      - deriv (admMetric0i (γ i) (β' i) j) t₀) l (𝓝 0))
    (hsmallN : Tendsto N₁' l (𝓝 0)) (hsmallβ : ∀ j, Tendsto (fun i => β₁' i j) l (𝓝 0))
    (a nA nW nl : ι → ℝ)
    (hlam : ∀ i, nl i ^ 2 = N₁ i ^ 2 + sumSq (β₁ i))
    (hnorm : ∀ i, nl i ^ 2 = (a i)⁻¹ ^ 2 * nA i ^ 2 + (a i)⁻¹ ^ 4 * nW i ^ 2) :
    Tendsto (fun i => (a i)⁻¹ * nA i) l (𝓝 0) ∧
    Tendsto (fun i => (a i)⁻¹ ^ 2 * nW i) l (𝓝 0) := by
  obtain ⟨hNlim, hβlim⟩ := first_jet_shadowing_lapse_shift_rate l t₀ N N' β β' γ N₁ N₁' β₁ β₁'
    γ₁ hN hN' hβ hβ' hγ hN0 hN0' hβ0 hβ0' c hc hcoer hshadow00 hshadow0i hsmallN hsmallβ
  -- `‖λ_t‖² → 0`, hence `‖λ_t‖ → 0`
  have hsq : Tendsto (fun i => nl i ^ 2) l (𝓝 0) := by
    have hβsq : Tendsto (fun i => sumSq (β₁ i)) l (𝓝 0) := by
      have := tendsto_finsetSum Finset.univ fun j _ => (hβlim j).pow 2
      simpa [sumSq] using this
    have := (hNlim.pow 2).add hβsq
    simp only [add_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at this
    exact this.congr fun i => (hlam i).symm
  have hl : Tendsto nl l (𝓝 0) := by
    have hsqrt : Tendsto (fun i => Real.sqrt (nl i ^ 2)) l (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hsq
      rw [Real.sqrt_zero] at this
      exact this
    refine squeeze_zero_norm (fun i => ?_) hsqrt
    rw [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
  exact lapse_shift_clock_condition l a nA nW nl hnorm hl

end RenewalGeometry
