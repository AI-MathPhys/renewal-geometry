/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ExactMultiplierGradingClockTest

/-!
# The necessary lapse--shift clock test in the grid norm on growing site sets
  (`prop:supp-exact-clock-test`, `eq:supp-exact-rate-norm`, `eq:supp-exact-rate-necessary`;
  emergent-spacetime manuscript)

`RenewalGeometry.Gravity.ExactMultiplierGradingClockTest.exact_clock_test` proves the clock test
on a *fixed* finite site set with per-site convergence.  Along a cutoff family the site set
`V_h` grows (`#V_h = h⁻³`), and the paper's norms are the grid norms
`‖v‖_h² = h³ Σ_{x ∈ V_h} |v(x)|²`; per-site convergence does not sum over growing site sets.
This file proves the statement in that generality:

* the site types `V i` depend on the regulator index `i` (any filter `l`), with cell weights
  `w i > 0` (the paper's `h³`); `gridNorm w v = √w ‖v‖` is the grid norm on the multiplier space
  `EuclideanSpace ℝ (V i × Fin 4)`, so `gridNorm (w i) λ² = w i Σ_x ((∂ₜN_x)² + |∂ₜβ_x|²)`
  (`gridNorm_lapseShiftJet_sq`);
* `site_jet_sq_le` — the per-site ADM estimate at `N = 1`, `β = 0`:
  `(∂ₜN)² + |∂ₜβ|² ≤ ½ (Δ∂ₜg₀₀)² + 2c⁻² Σ_j (Δ∂ₜg₀ⱼ)² + 2((∂ₜN')² + |∂ₜβ'|²)`, from
  `∂ₜg₀₀ = -2∂ₜN`, `∂ₜg₀ᵢ = γᵢⱼ∂ₜβʲ` and the uniform coercivity `γ ⪰ c`;
* `lapseShiftJet_gridNorm_tendsto_zero` — first-jet shadowing **in the grid norm**
  (`w Σ_x (Δ∂ₜg₀₀)² → 0`, `w Σ_x Σ_j (Δ∂ₜg₀ⱼ)² → 0`) of a harmonic metric whose lapse--shift first
  jet is small in the grid norm forces `‖λ_t‖_h → 0`;
* `AmplitudeGrading.rate_norm_grid` — `eq:supp-exact-rate-norm` in the grid norm;
* `exact_clock_test_grid` — **`prop:supp-exact-clock-test`**: for every family of active/weak
  gradings `G i` of the (index-dependent) multiplier spaces,
  `a⁻¹ ‖(u_a)_A‖_h → 0` and `a⁻² ‖(u_a)_W‖_h → 0`.

The coercivity constant `c` is uniform in the index and the sites, as the paper's fixed chart
provides.  A non-vacuity instance with growing site sets `V i = Fin (i + 1)` and weights
`w i = (i + 1)⁻¹` is `exact_clock_test_grid_nonvacuous`.
-/

open scoped BigOperators Topology
open Filter

namespace RenewalGeometry

/-- The grid norm `‖v‖_h = √w ‖v‖` (`w = h³` the cell volume). -/
noncomputable def gridNorm {E : Type*} [NormedAddCommGroup E] (w : ℝ) (v : E) : ℝ :=
  Real.sqrt w * ‖v‖

theorem gridNorm_sq {E : Type*} [NormedAddCommGroup E] {w : ℝ} (hw : 0 ≤ w) (v : E) :
    gridNorm w v ^ 2 = w * ‖v‖ ^ 2 := by
  unfold gridNorm; rw [mul_pow, Real.sq_sqrt hw]

/-- `‖(∂ₜN, ∂ₜβ)‖_h² = w Σ_x ((∂ₜN_x)² + |∂ₜβ_x|²)`. -/
theorem gridNorm_lapseShiftJet_sq {V : Type*} [Fintype V] {w : ℝ} (hw : 0 ≤ w)
    (N₁ : V → ℝ) (β₁ : V → Fin 3 → ℝ) :
    gridNorm w (lapseShiftJet N₁ β₁) ^ 2 = w * ∑ x, (N₁ x ^ 2 + sumSq (β₁ x)) := by
  rw [gridNorm_sq hw, lapseShiftJet_norm_sq]

/-- **`eq:supp-exact-rate-norm` in the grid norm**:
`‖λ_t‖_h² = a⁻² ‖(u_a)_A‖_h² + a⁻⁴ ‖(u_a)_W‖_h²`. -/
theorem AmplitudeGrading.rate_norm_grid {Λ : Type*} [NormedAddCommGroup Λ]
    [InnerProductSpace ℝ Λ] (G : AmplitudeGrading Λ) {w : ℝ} (hw : 0 ≤ w) (a : ℝ) (ha : a ≠ 0)
    (lt : Λ) :
    gridNorm w lt ^ 2 = a⁻¹ ^ 2 * gridNorm w (G.activePart (G.normalizedSource a lt)) ^ 2 +
      a⁻¹ ^ 4 * gridNorm w (G.weakPart (G.normalizedSource a lt)) ^ 2 := by
  rw [gridNorm_sq hw, gridNorm_sq hw, gridNorm_sq hw, G.rate_norm a ha lt]
  ring

theorem sumSq_add_le (u v : Fin 3 → ℝ) : sumSq (u + v) ≤ 2 * sumSq u + 2 * sumSq v := by
  unfold sumSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (u j - v j)]

/-- **Per-site ADM estimate.**  At an instant with `N = N' = 1`, `β = β' = 0` and a shared
coercive spatial metric `γ ⪰ c`,
`(∂ₜN)² + |∂ₜβ|² ≤ ½ (Δ∂ₜg₀₀)² + 2c⁻² Σ_j (Δ∂ₜg₀ⱼ)² + 2((∂ₜN')² + |∂ₜβ'|²)`. -/
theorem site_jet_sq_le (t₀ : ℝ) (N N' : ℝ → ℝ) (β β' : ℝ → Fin 3 → ℝ)
    (γ : ℝ → Fin 3 → Fin 3 → ℝ) (N₁ N₁' : ℝ) (β₁ β₁' : Fin 3 → ℝ) (γ₁ : Fin 3 → Fin 3 → ℝ)
    (hN : HasDerivAt N N₁ t₀) (hN' : HasDerivAt N' N₁' t₀)
    (hβ : ∀ j, HasDerivAt (fun t => β t j) (β₁ j) t₀)
    (hβ' : ∀ j, HasDerivAt (fun t => β' t j) (β₁' j) t₀)
    (hγ : ∀ j k, HasDerivAt (fun t => γ t j k) (γ₁ j k) t₀)
    (hN0 : N t₀ = 1) (hN0' : N' t₀ = 1) (hβ0 : ∀ j, β t₀ j = 0) (hβ0' : ∀ j, β' t₀ j = 0)
    (c : ℝ) (hc : 0 < c) (hcoer : ∀ y : Fin 3 → ℝ, c * sumSq y ≤ ∑ j, y j * (∑ k, γ t₀ j k * y k)) :
    N₁ ^ 2 + sumSq β₁ ≤
      1 / 2 * (deriv (admMetric00 N γ β) t₀ - deriv (admMetric00 N' γ β') t₀) ^ 2 +
      2 / c ^ 2 * ∑ j, (deriv (admMetric0i γ β j) t₀ - deriv (admMetric0i γ β' j) t₀) ^ 2 +
      2 * (N₁' ^ 2 + sumSq β₁') := by
  have h00 : deriv (admMetric00 N γ β) t₀ - deriv (admMetric00 N' γ β') t₀ = -2 * (N₁ - N₁') := by
    rw [(admMetric00_hasDerivAt N γ β N₁ γ₁ β₁ t₀ hN hγ hβ hN0 hβ0).deriv,
      (admMetric00_hasDerivAt N' γ β' N₁' γ₁ β₁' t₀ hN' hγ hβ' hN0' hβ0').deriv]
    ring
  have h0i : ∀ j, deriv (admMetric0i γ β j) t₀ - deriv (admMetric0i γ β' j) t₀
      = ∑ k, γ t₀ j k * (β₁ k - β₁' k) := by
    intro j
    rw [(admMetric0i_hasDerivAt γ β γ₁ β₁ t₀ hγ hβ hβ0 j).deriv,
      (admMetric0i_hasDerivAt γ β' γ₁ β₁' t₀ hγ hβ' hβ0' j).deriv, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  -- lapse part
  have hNb : N₁ ^ 2 ≤ 1 / 2 * (deriv (admMetric00 N γ β) t₀ - deriv (admMetric00 N' γ β') t₀) ^ 2
      + 2 * N₁' ^ 2 := by
    rw [h00]; nlinarith [sq_nonneg (N₁ - 2 * N₁')]
  -- shift part: coercivity
  have hcs := sumSq_le_of_coercive c hc (γ t₀) (fun k => β₁ k - β₁' k) (hcoer _)
  have hsum0i : sumSq (fun j => ∑ k, γ t₀ j k * (β₁ k - β₁' k))
      = ∑ j, (deriv (admMetric0i γ β j) t₀ - deriv (admMetric0i γ β' j) t₀) ^ 2 := by
    unfold sumSq; exact Finset.sum_congr rfl fun j _ => by rw [h0i j]
  have hdiff : sumSq (fun k => β₁ k - β₁' k) ≤
      1 / c ^ 2 * ∑ j, (deriv (admMetric0i γ β j) t₀ - deriv (admMetric0i γ β' j) t₀) ^ 2 := by
    rw [← hsum0i]
    have hc2 : 0 < c ^ 2 := by positivity
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc2]
    linarith
  have hβb : sumSq β₁ ≤ 2 * sumSq (fun k => β₁ k - β₁' k) + 2 * sumSq β₁' := by
    have := sumSq_add_le (fun k => β₁ k - β₁' k) β₁'
    have heq : (fun k => β₁ k - β₁' k) + β₁' = β₁ := by funext k; simp
    rwa [heq] at this
  have : 2 / c ^ 2 = 2 * (1 / c ^ 2) := by ring
  rw [this]
  nlinarith

/-- **First-jet shadowing in the grid norm forces `‖λ_t‖_h → 0`** on index-dependent site sets
`V i` with cell weights `w i > 0`. -/
theorem lapseShiftJet_gridNorm_tendsto_zero {ι : Type*} (l : Filter ι) (t₀ : ℝ)
    (V : ι → Type*) [∀ i, Fintype (V i)] (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (N N' : (i : ι) → V i → ℝ → ℝ) (β β' : (i : ι) → V i → ℝ → Fin 3 → ℝ)
    (γ : (i : ι) → V i → ℝ → Fin 3 → Fin 3 → ℝ)
    (N₁ N₁' : (i : ι) → V i → ℝ) (β₁ β₁' : (i : ι) → V i → Fin 3 → ℝ)
    (γ₁ : (i : ι) → V i → Fin 3 → Fin 3 → ℝ)
    (hN : ∀ i x, HasDerivAt (N i x) (N₁ i x) t₀)
    (hN' : ∀ i x, HasDerivAt (N' i x) (N₁' i x) t₀)
    (hβ : ∀ i x j, HasDerivAt (fun t => β i x t j) (β₁ i x j) t₀)
    (hβ' : ∀ i x j, HasDerivAt (fun t => β' i x t j) (β₁' i x j) t₀)
    (hγ : ∀ i x j k, HasDerivAt (fun t => γ i x t j k) (γ₁ i x j k) t₀)
    (hN0 : ∀ i x, N i x t₀ = 1) (hN0' : ∀ i x, N' i x t₀ = 1)
    (hβ0 : ∀ i x j, β i x t₀ j = 0) (hβ0' : ∀ i x j, β' i x t₀ j = 0)
    (c : ℝ) (hc : 0 < c)
    (hcoer : ∀ i x (y : Fin 3 → ℝ), c * sumSq y ≤ ∑ j, y j * (∑ k, γ i x t₀ j k * y k))
    (hshadow00 : Tendsto (fun i => w i * ∑ x, (deriv (admMetric00 (N i x) (γ i x) (β i x)) t₀
      - deriv (admMetric00 (N' i x) (γ i x) (β' i x)) t₀) ^ 2) l (𝓝 0))
    (hshadow0i : Tendsto (fun i => w i * ∑ x, ∑ j, (deriv (admMetric0i (γ i x) (β i x) j) t₀
      - deriv (admMetric0i (γ i x) (β' i x) j) t₀) ^ 2) l (𝓝 0))
    (hsmall : Tendsto (fun i => w i * ∑ x, (N₁' i x ^ 2 + sumSq (β₁' i x))) l (𝓝 0)) :
    Tendsto (fun i => gridNorm (w i) (lapseShiftJet (N₁ i) (β₁ i))) l (𝓝 0) := by
  set S00 := fun i => w i * ∑ x, (deriv (admMetric00 (N i x) (γ i x) (β i x)) t₀
      - deriv (admMetric00 (N' i x) (γ i x) (β' i x)) t₀) ^ 2
  set S0i := fun i => w i * ∑ x, ∑ j, (deriv (admMetric0i (γ i x) (β i x) j) t₀
      - deriv (admMetric0i (γ i x) (β' i x) j) t₀) ^ 2
  set Ss := fun i => w i * ∑ x, (N₁' i x ^ 2 + sumSq (β₁' i x))
  have hbound : ∀ i, gridNorm (w i) (lapseShiftJet (N₁ i) (β₁ i)) ^ 2
      ≤ 1 / 2 * S00 i + 2 / c ^ 2 * S0i i + 2 * Ss i := by
    intro i
    rw [gridNorm_lapseShiftJet_sq (hw i).le]
    have hsite : ∀ x, N₁ i x ^ 2 + sumSq (β₁ i x) ≤
        1 / 2 * (deriv (admMetric00 (N i x) (γ i x) (β i x)) t₀
          - deriv (admMetric00 (N' i x) (γ i x) (β' i x)) t₀) ^ 2 +
        2 / c ^ 2 * ∑ j, (deriv (admMetric0i (γ i x) (β i x) j) t₀
          - deriv (admMetric0i (γ i x) (β' i x) j) t₀) ^ 2 +
        2 * (N₁' i x ^ 2 + sumSq (β₁' i x)) := fun x =>
      site_jet_sq_le t₀ (N i x) (N' i x) (β i x) (β' i x) (γ i x) (N₁ i x) (N₁' i x) (β₁ i x)
        (β₁' i x) (γ₁ i x) (hN i x) (hN' i x) (hβ i x) (hβ' i x) (hγ i x) (hN0 i x) (hN0' i x)
        (hβ0 i x) (hβ0' i x) c hc (hcoer i x)
    calc w i * ∑ x, (N₁ i x ^ 2 + sumSq (β₁ i x))
        ≤ w i * ∑ x, (1 / 2 * (deriv (admMetric00 (N i x) (γ i x) (β i x)) t₀
          - deriv (admMetric00 (N' i x) (γ i x) (β' i x)) t₀) ^ 2 +
          2 / c ^ 2 * ∑ j, (deriv (admMetric0i (γ i x) (β i x) j) t₀
            - deriv (admMetric0i (γ i x) (β' i x) j) t₀) ^ 2 +
          2 * (N₁' i x ^ 2 + sumSq (β₁' i x))) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hsite x) (hw i).le
      _ = 1 / 2 * S00 i + 2 / c ^ 2 * S0i i + 2 * Ss i := by
          simp only [S00, S0i, Ss]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.mul_sum]
          ring
  have hlim : Tendsto (fun i => 1 / 2 * S00 i + 2 / c ^ 2 * S0i i + 2 * Ss i) l (𝓝 0) := by
    have := ((hshadow00.const_mul (1 / 2)).add (hshadow0i.const_mul (2 / c ^ 2))).add
      (hsmall.const_mul 2)
    simpa using this
  have hsq : Tendsto (fun i => gridNorm (w i) (lapseShiftJet (N₁ i) (β₁ i)) ^ 2) l (𝓝 0) :=
    squeeze_zero (fun i => sq_nonneg _) hbound hlim
  have hnn : ∀ i, 0 ≤ gridNorm (w i) (lapseShiftJet (N₁ i) (β₁ i)) := fun i =>
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun i => ?_
  simp only [Function.comp_apply]
  exact Real.sqrt_sq (hnn i)

/-- **`prop:supp-exact-clock-test`** (`eq:supp-exact-rate-necessary`) on growing site sets, in the
grid norm.  Along a regulator family `i` (filter `l`) with site sets `V i`, cell weights
`w i > 0` and amplitudes `a i ≠ 0`: if the exact-action ADM metric shadows a small harmonic
metric in the initial first time derivative of `g₀₀`, `g₀ᵢ` in the grid norm, with the same
lapse `N = 1`, shift `β = 0` and spatial metric at the initial cut, uniformly coercive spatial
metric and harmonic lapse--shift first jet small in the grid norm, then for every family of
active/weak gradings `G i`, with `λ_t = (∂ₜN, ∂ₜβ)` and `u_a = S_a λ_t`,
`a⁻¹ ‖(u_a)_A‖_h → 0` and `a⁻² ‖(u_a)_W‖_h → 0`.  No electric coefficient enters. -/
theorem exact_clock_test_grid {ι : Type*} (l : Filter ι) (t₀ : ℝ)
    (V : ι → Type*) [∀ i, Fintype (V i)] (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (N N' : (i : ι) → V i → ℝ → ℝ) (β β' : (i : ι) → V i → ℝ → Fin 3 → ℝ)
    (γ : (i : ι) → V i → ℝ → Fin 3 → Fin 3 → ℝ)
    (N₁ N₁' : (i : ι) → V i → ℝ) (β₁ β₁' : (i : ι) → V i → Fin 3 → ℝ)
    (γ₁ : (i : ι) → V i → Fin 3 → Fin 3 → ℝ)
    (hN : ∀ i x, HasDerivAt (N i x) (N₁ i x) t₀)
    (hN' : ∀ i x, HasDerivAt (N' i x) (N₁' i x) t₀)
    (hβ : ∀ i x j, HasDerivAt (fun t => β i x t j) (β₁ i x j) t₀)
    (hβ' : ∀ i x j, HasDerivAt (fun t => β' i x t j) (β₁' i x j) t₀)
    (hγ : ∀ i x j k, HasDerivAt (fun t => γ i x t j k) (γ₁ i x j k) t₀)
    (hN0 : ∀ i x, N i x t₀ = 1) (hN0' : ∀ i x, N' i x t₀ = 1)
    (hβ0 : ∀ i x j, β i x t₀ j = 0) (hβ0' : ∀ i x j, β' i x t₀ j = 0)
    (c : ℝ) (hc : 0 < c)
    (hcoer : ∀ i x (y : Fin 3 → ℝ), c * sumSq y ≤ ∑ j, y j * (∑ k, γ i x t₀ j k * y k))
    (hshadow00 : Tendsto (fun i => w i * ∑ x, (deriv (admMetric00 (N i x) (γ i x) (β i x)) t₀
      - deriv (admMetric00 (N' i x) (γ i x) (β' i x)) t₀) ^ 2) l (𝓝 0))
    (hshadow0i : Tendsto (fun i => w i * ∑ x, ∑ j, (deriv (admMetric0i (γ i x) (β i x) j) t₀
      - deriv (admMetric0i (γ i x) (β' i x) j) t₀) ^ 2) l (𝓝 0))
    (hsmall : Tendsto (fun i => w i * ∑ x, (N₁' i x ^ 2 + sumSq (β₁' i x))) l (𝓝 0))
    (G : (i : ι) → AmplitudeGrading (EuclideanSpace ℝ (V i × Fin 4)))
    (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    Tendsto (fun i => (a i)⁻¹ * gridNorm (w i)
      ((G i).activePart ((G i).normalizedSource (a i) (lapseShiftJet (N₁ i) (β₁ i))))) l (𝓝 0) ∧
    Tendsto (fun i => (a i)⁻¹ ^ 2 * gridNorm (w i)
      ((G i).weakPart ((G i).normalizedSource (a i) (lapseShiftJet (N₁ i) (β₁ i))))) l (𝓝 0) := by
  have hl := lapseShiftJet_gridNorm_tendsto_zero l t₀ V w hw N N' β β' γ N₁ N₁' β₁ β₁' γ₁
    hN hN' hβ hβ' hγ hN0 hN0' hβ0 hβ0' c hc hcoer hshadow00 hshadow0i hsmall
  exact lapse_shift_clock_condition l a
    (fun i => gridNorm (w i)
      ((G i).activePart ((G i).normalizedSource (a i) (lapseShiftJet (N₁ i) (β₁ i)))))
    (fun i => gridNorm (w i)
      ((G i).weakPart ((G i).normalizedSource (a i) (lapseShiftJet (N₁ i) (β₁ i)))))
    (fun i => gridNorm (w i) (lapseShiftJet (N₁ i) (β₁ i)))
    (fun i => (G i).rate_norm_grid (hw i).le (a i) (ha i) _) hl

/-- **Non-vacuity** with growing site sets: `V i = Fin (i + 1)`, `w i = (i+1)⁻¹`, exact and
harmonic metrics with lapse `N = 1 + t/(i+1)`, shift `β = 0`, `γ = I` (`c = 1`), amplitude
`a i = (i+1)⁻¹`; all hypotheses of `exact_clock_test_grid` hold. -/
example : True := by
  have hε : Tendsto (fun i : ℕ => (1 / ((i : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  have _h := exact_clock_test_grid atTop 0 (fun i : ℕ => Fin (i + 1))
    (fun i => 1 / ((i : ℝ) + 1)) (fun i => by positivity)
    (fun i _ t => 1 + t * (1 / ((i : ℝ) + 1))) (fun i _ t => 1 + t * (1 / ((i : ℝ) + 1)))
    (fun _ _ _ _ => 0) (fun _ _ _ _ => 0)
    (fun _ _ _ j k => if j = k then 1 else 0)
    (fun i _ => 1 / ((i : ℝ) + 1)) (fun i _ => 1 / ((i : ℝ) + 1))
    (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ _ => 0)
    (fun i _ => by simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (1 / ((i : ℝ) + 1))).const_add 1)
    (fun i _ => by simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (1 / ((i : ℝ) + 1))).const_add 1)
    (fun _ _ _ => hasDerivAt_const _ _) (fun _ _ _ => hasDerivAt_const _ _)
    (fun _ _ _ _ => hasDerivAt_const _ _)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    1 one_pos
    (fun _ _ y => by simp [sumSq, sq])
    (by simp) (by simp)
    (by
      refine hε.congr fun i => ?_
      simp only [sumSq, Pi.zero_apply]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
        add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp)
    (fun _ => ⟨⊥⟩) (fun i => 1 / ((i : ℝ) + 1)) (fun i => by positivity)
  trivial

end RenewalGeometry
