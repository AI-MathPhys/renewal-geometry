/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.StripHolomorphicFourierDecay

/-!
# Logarithmic Sobolev upgrade for strip-analytic sources (`lem:log-source-upgrade`)

Generic infrastructure (no renewal notions) for `lem:log-source-upgrade` of the
Einstein–Standard-Model action-closure manuscript: a source `f(t,x)` on `Q = I × 𝕋^d` that
extends holomorphically in the spatial variables to a strip of width `a/K`, bounded there by `A`,
and has `‖f‖_{L²(Q)} ≤ ε`, obeys
`‖f‖_{L²_t H^j_x} ≤ C_j ε K^j [1 + log(2 + C_j A K^{j+d}/ε)]^j`
(`d = 3` gives the manuscript's `K^{j+3}`).

* `hasSum_exp_neg_abs`, `tsum_exp_neg_abs_le`: `Σ_{m ∈ ℤ} e^{-c|m|} = (1+e^{-c})/(1-e^{-c}) ≤ 4/c`
  for `0 < c ≤ 1`.
* `one_add_pow_mul_exp_le`: `(1+L)^p e^{-γL/2} ≤ 2 (2/γ)^p p!` for `0 < γ ≤ 1`.
* `sobWeight_le_linf`: `⟨n⟩² ≤ 4π² d (1 + |n|_∞)²`.
* `tsum_weight_exp_le` (**lattice tail sum**):
  `Σ_{n ∈ ℤ^d} ⟨n⟩^{2j} e^{-γ|n|_∞} ≤ M_{j,d} γ^{-(2j+d)}` (product bound via
  `TorusSobolev.summable_pi_prod`).
* `coeffSobSq_le_split` (**frequency split**): if `|c(n)| ≤ A e^{-γ|n|_∞}` then for every threshold
  `B`, `‖c‖²_{H^j} ≤ (1 + 4π² d B²)^j ‖c‖²_{ℓ²} + A² e^{-γB} M_{j,d} γ^{-(2j+d)}`.
* `lintegral_sobSq_le_split`: the space-time (`L²_t H^j_x`) version, any finite measure of times.
* `sobSq_zero_eq_integral_continuous`: Parseval for continuous functions.
* **`log_source_upgrade`** (`eq:log-source-upgrade`): the statement of `lem:log-source-upgrade`
  with explicit dependence of the constant (on `j`, `d`, `a` and the time measure only), for
  `ε > 0`; **`log_source_upgrade_zero`**: the case `ε = 0` (the right side is zero).

Rendering: unit torus `𝕋^d = UnitAddTorus d`, period `1` (the manuscript's period-`2π` box is the
dilation `x ↦ 2πx`; a strip of width `a/K` there is a strip of width `a/(2πK)` here, and the
`L²`/`H^j` norms change by fixed factors absorbed in `C_j`); `H^j` is the Fourier norm with weight
`⟨n⟩^{2j} = (1 + 4π²|n|²)^j` of `TorusSobolevEmbedding`; the holomorphy hypothesis is required
along every coordinate line through every real point (implied by the manuscript's extension in
the three spatial variables); the time slab is any finite measure space (e.g. `[0,T]`).
-/

open Complex MeasureTheory Filter Topology Set UnitAddTorus
open scoped Real BigOperators ENNReal Nat

namespace RenewalGeometry.AnalyticSourceUpgrade

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

noncomputable section

open TorusSobolev StripFourier

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ### One-dimensional exponential sums -/

/-- `Σ_{m ∈ ℤ} e^{-c|m|} = (1 + e^{-c})/(1 - e^{-c})`. -/
theorem hasSum_exp_neg_abs {c : ℝ} (hc : 0 < c) :
    HasSum (fun m : ℤ => Real.exp (-(c * |(m : ℝ)|)))
      ((1 - Real.exp (-c))⁻¹ + Real.exp (-c) * (1 - Real.exp (-c))⁻¹) := by
  set r := Real.exp (-c) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    have h := Real.exp_lt_exp.mpr (show -c < 0 by linarith)
    rwa [Real.exp_zero] at h
  have h1 : HasSum (fun n : ℕ => Real.exp (-(c * |((n : ℤ) : ℝ)|))) (1 - r)⁻¹ := by
    have : (fun n : ℕ => Real.exp (-(c * |((n : ℤ) : ℝ)|))) = fun n => r ^ n := by
      funext n
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n), hr, ← Real.exp_nat_mul]
      ring_nf
    rw [this]; exact hasSum_geometric_of_lt_one hr0 hr1
  have h2 : HasSum (fun n : ℕ => Real.exp (-(c * |((-((n : ℤ) + 1) : ℤ) : ℝ)|)))
      (r * (1 - r)⁻¹) := by
    have : (fun n : ℕ => Real.exp (-(c * |((-((n : ℤ) + 1) : ℤ) : ℝ)|))) =
        fun n => r * r ^ n := by
      funext n
      have hn : ((-((n : ℤ) + 1) : ℤ) : ℝ) = -((n : ℝ) + 1) := by push_cast; ring
      rw [hn, abs_neg, abs_of_nonneg (by positivity), ← pow_succ', hr, ← Real.exp_nat_mul]
      push_cast; ring_nf
    rw [this]; exact (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
  exact h1.of_nat_of_neg_add_one h2

/-- `Σ_{m ∈ ℤ} e^{-c|m|} ≤ 4/c` for `0 < c ≤ 1`. -/
theorem tsum_exp_neg_abs_le {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Summable (fun m : ℤ => Real.exp (-(c * |(m : ℝ)|))) ∧
      ∑' m : ℤ, Real.exp (-(c * |(m : ℝ)|)) ≤ 4 / c := by
  have h := hasSum_exp_neg_abs hc
  refine ⟨h.summable, ?_⟩
  rw [h.tsum_eq]
  set r := Real.exp (-c) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hrle : r * (1 + c) ≤ 1 := by
    have h1 := Real.add_one_le_exp c
    have h2 : r * Real.exp c = 1 := by rw [hr, ← Real.exp_add]; simp
    nlinarith
  have hpos : c / 2 ≤ 1 - r := by nlinarith
  have hpos' : 0 < 1 - r := by linarith
  rw [show (1 - r)⁻¹ + r * (1 - r)⁻¹ = (1 + r) / (1 - r) by field_simp,
    div_le_div_iff₀ hpos' hc]
  have hr1 : r ≤ 1 := by nlinarith
  nlinarith

/-- `(1+L)^p e^{-γL/2} ≤ 2 (2/γ)^p p!` for `0 < γ ≤ 1`, `L ≥ 0`. -/
theorem one_add_pow_mul_exp_le {γ L : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hL : 0 ≤ L) (p : ℕ) :
    (1 + L) ^ p * Real.exp (-(γ * L / 2)) ≤ 2 * (2 / γ) ^ p * p ! := by
  set x := γ * (1 + L) / 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have h1 := Real.pow_div_factorial_le_exp x hx0 p
  have hfac : (0 : ℝ) < p ! := by exact_mod_cast Nat.factorial_pos p
  have h2 : x ^ p ≤ p ! * Real.exp x := by
    rw [div_le_iff₀ hfac] at h1; linarith
  have h3 : (1 + L) ^ p = (2 / γ) ^ p * x ^ p := by
    rw [← mul_pow]; congr 1; rw [hx]; field_simp
  have h4 : Real.exp x * Real.exp (-(γ * L / 2)) = Real.exp (γ / 2) := by
    rw [← Real.exp_add]; congr 1; rw [hx]; ring
  have h5 : Real.exp (γ / 2) ≤ 2 := by
    have e1 : Real.exp (γ / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
    have e2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have e3 := Real.exp_one_lt_d9
    have e4 : 0 < Real.exp (1 / 2) := Real.exp_pos _
    nlinarith
  have hg : 0 ≤ (2 / γ) ^ p := by positivity
  calc (1 + L) ^ p * Real.exp (-(γ * L / 2))
      = (2 / γ) ^ p * x ^ p * Real.exp (-(γ * L / 2)) := by rw [h3]
    _ ≤ (2 / γ) ^ p * (p ! * Real.exp x) * Real.exp (-(γ * L / 2)) := by gcongr
    _ = (2 / γ) ^ p * p ! * Real.exp (γ / 2) := by rw [← h4]; ring
    _ ≤ (2 / γ) ^ p * p ! * 2 := by gcongr
    _ = 2 * (2 / γ) ^ p * p ! := by ring

/-! ### The lattice tail sum -/

theorem sum_sq_le_linf (n : d → ℤ) :
    ∑ i, ((n i : ℝ)) ^ 2 ≤ Fintype.card d * (linfNorm n : ℝ) ^ 2 := by
  have h : ∀ i, ((n i : ℝ)) ^ 2 ≤ (linfNorm n : ℝ) ^ 2 := by
    intro i
    have h1 : ((n i).natAbs : ℝ) ≤ linfNorm n := by exact_mod_cast natAbs_le_linfNorm n i
    have h2 : |((n i : ℝ))| ≤ linfNorm n := by
      rw [← Int.cast_abs, ← Nat.cast_natAbs]; exact_mod_cast h1
    exact sq_le_sq' (by linarith [neg_abs_le ((n i : ℝ)), abs_nonneg ((n i : ℝ))])
      (le_trans (le_abs_self _) h2)
  calc ∑ i, ((n i : ℝ)) ^ 2 ≤ ∑ _i : d, (linfNorm n : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem sum_abs_le_linf (n : d → ℤ) :
    ∑ i, |((n i : ℝ))| ≤ Fintype.card d * (linfNorm n : ℝ) := by
  have h : ∀ i, |((n i : ℝ))| ≤ linfNorm n := by
    intro i
    have h1 : ((n i).natAbs : ℝ) ≤ linfNorm n := by exact_mod_cast natAbs_le_linfNorm n i
    rw [← Int.cast_abs, ← Nat.cast_natAbs]; exact_mod_cast h1
  calc ∑ i, |((n i : ℝ))| ≤ ∑ _i : d, (linfNorm n : ℝ) := Finset.sum_le_sum fun i _ => h i
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- `1 + 4π²|n|² ≤ 1 + 4π² d |n|_∞²`. -/
theorem sobWeight_le_linf_sq (n : d → ℤ) :
    sobWeight n ≤ 1 + 4 * π ^ 2 * (Fintype.card d * (linfNorm n : ℝ) ^ 2) := by
  unfold sobWeight
  have := sum_sq_le_linf n
  have hp : 0 ≤ 4 * π ^ 2 := by positivity
  nlinarith

/-- `⟨n⟩² ≤ 4π² d (1 + |n|_∞)²` (`d ≥ 1`). -/
theorem sobWeight_le_linf [Nonempty d] (n : d → ℤ) :
    sobWeight n ≤ 4 * π ^ 2 * Fintype.card d * (1 + (linfNorm n : ℝ)) ^ 2 := by
  have h := sobWeight_le_linf_sq n
  have hD : (1 : ℝ) ≤ Fintype.card d := by exact_mod_cast Fintype.card_pos
  have hpi := four_pi_sq_ge_one
  have hL : (0 : ℝ) ≤ linfNorm n := Nat.cast_nonneg _
  have h1 : 1 ≤ 4 * π ^ 2 * Fintype.card d := by nlinarith
  nlinarith [sq_nonneg (linfNorm n : ℝ)]

/-- The constant `M_{j,d}` of the lattice tail sum. -/
def tailConst (j D : ℕ) : ℝ :=
  (4 * π ^ 2 * D) ^ j * 2 * 4 ^ j * ((2 * j) ! : ℝ) * (8 * D) ^ D

theorem tailConst_nonneg (j D : ℕ) : 0 ≤ tailConst j D := by
  unfold tailConst; positivity

/-- **Lattice tail sum**: `Σ_{n ∈ ℤ^d} ⟨n⟩^{2j} e^{-γ|n|_∞} ≤ M_{j,d} γ^{-(2j+d)}` for
`0 < γ ≤ 1`. -/
theorem tsum_weight_exp_le [Nonempty d] {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (j : ℕ) :
    Summable (fun n : d → ℤ => sobWeight n ^ j * Real.exp (-(γ * linfNorm n))) ∧
      ∑' n : d → ℤ, sobWeight n ^ j * Real.exp (-(γ * linfNorm n)) ≤
        tailConst j (Fintype.card d) * (1 / γ) ^ (2 * j + Fintype.card d) := by
  set D := Fintype.card d with hDdef
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast Fintype.card_pos
  set c : ℝ := γ / (2 * D) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]; linarith
  obtain ⟨hs1, ht1⟩ := tsum_exp_neg_abs_le hc0 hc1
  obtain ⟨hsP, htP⟩ := summable_pi_prod (fun (_ : d) (m : ℤ) => Real.exp (-(c * |(m : ℝ)|)))
    (fun _ _ => (Real.exp_pos _).le) (fun _ => hs1)
  set K0 : ℝ := (4 * π ^ 2 * D) ^ j * (2 * (2 / γ) ^ (2 * j) * ((2 * j) ! : ℝ))
  have hK0 : 0 ≤ K0 := by positivity
  have hpt : ∀ n : d → ℤ, sobWeight n ^ j * Real.exp (-(γ * linfNorm n)) ≤
      K0 * ∏ i, Real.exp (-(c * |((n i : ℤ) : ℝ)|)) := by
    intro n
    set L : ℝ := (linfNorm n : ℝ)
    have hL : 0 ≤ L := Nat.cast_nonneg _
    have hw := sobWeight_le_linf n
    have hw0 := (sobWeight_pos n).le
    have hsplit : Real.exp (-(γ * L)) = Real.exp (-(γ * L / 2)) * Real.exp (-(γ * L / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have hprod : Real.exp (-(γ * L / 2)) ≤ ∏ i, Real.exp (-(c * |((n i : ℤ) : ℝ)|)) := by
      rw [← Real.exp_sum, Real.exp_le_exp, Finset.sum_neg_distrib, ← Finset.mul_sum,
        neg_le_neg_iff]
      have := sum_abs_le_linf n
      rw [hc]
      calc γ / (2 * D) * ∑ i, |((n i : ℝ))| ≤ γ / (2 * D) * (D * L) := by gcongr
        _ = γ * L / 2 := by field_simp
    have hwj : sobWeight n ^ j ≤ (4 * π ^ 2 * D) ^ j * (1 + L) ^ (2 * j) := by
      calc sobWeight n ^ j ≤ (4 * π ^ 2 * D * (1 + L) ^ 2) ^ j := pow_le_pow_left₀ hw0 hw j
        _ = _ := by rw [mul_pow, ← pow_mul]
    have hE := one_add_pow_mul_exp_le hγ hγ1 hL (2 * j)
    calc sobWeight n ^ j * Real.exp (-(γ * L))
        = (sobWeight n ^ j * Real.exp (-(γ * L / 2))) * Real.exp (-(γ * L / 2)) := by
          rw [hsplit]; ring
      _ ≤ ((4 * π ^ 2 * D) ^ j * (1 + L) ^ (2 * j) * Real.exp (-(γ * L / 2))) *
            ∏ i, Real.exp (-(c * |((n i : ℤ) : ℝ)|)) := by
          gcongr
      _ ≤ K0 * ∏ i, Real.exp (-(c * |((n i : ℤ) : ℝ)|)) := by
          gcongr
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hE (by positivity)
  have hsum : Summable (fun n : d → ℤ => sobWeight n ^ j * Real.exp (-(γ * linfNorm n))) :=
    Summable.of_nonneg_of_le (fun n => by have := (sobWeight_pos n).le; positivity) hpt
      (hsP.mul_left K0)
  refine ⟨hsum, ?_⟩
  calc ∑' n : d → ℤ, sobWeight n ^ j * Real.exp (-(γ * linfNorm n))
      ≤ ∑' n : d → ℤ, K0 * ∏ i, Real.exp (-(c * |((n i : ℤ) : ℝ)|)) :=
        Summable.tsum_le_tsum hpt hsum (hsP.mul_left K0)
    _ = K0 * ∑' n : d → ℤ, ∏ i, Real.exp (-(c * |((n i : ℤ) : ℝ)|)) := tsum_mul_left
    _ ≤ K0 * ∏ _i : d, (4 / c) := by
        gcongr
        exact htP.trans (Finset.prod_le_prod (fun _ _ => tsum_nonneg fun _ => (Real.exp_pos _).le)
          fun _ _ => ht1)
    _ = tailConst j D * (1 / γ) ^ (2 * j + D) := by
        rw [Finset.prod_const, Finset.card_univ, ← hDdef]
        simp only [K0, tailConst, hc]
        have hγ' : γ ≠ 0 := hγ.ne'
        have hD' : (D : ℝ) ≠ 0 := by positivity
        have h4 : (2:ℝ)^(2*j) = 4^j := by rw [pow_mul]; norm_num
        have h8 : (4 / (γ / (2 * D))) = 8 * D * (1/γ) := by field_simp; ring
        rw [h8, div_eq_mul_one_div 2 γ, mul_pow 2 (1 / γ), h4, mul_pow (8 * (D : ℝ)) (1 / γ),
          pow_add]
        ring

/-! ### The frequency split -/

/-- **Frequency split** for coefficients with exponential decay: if `|c(n)| ≤ A e^{-γ|n|_∞}`,
`0 < γ ≤ 1`, then `c ∈ H^j` for every `j` and, for every threshold `B`,
`‖c‖²_{H^j} ≤ (1 + 4π² d B²)^j ‖c‖²_{ℓ²} + A² e^{-γB} M_{j,d} γ^{-(2j+d)}`. -/
theorem coeffSobSq_le_split [Nonempty d] (c : (d → ℤ) → ℂ) {A γ B : ℝ} (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ A * Real.exp (-(γ * linfNorm n))) (j : ℕ) :
    CoeffMemH (j : ℝ) c ∧ Summable (fun n => ‖c n‖ ^ 2) ∧
      coeffSobSq (j : ℝ) c ≤ (1 + 4 * π ^ 2 * (Fintype.card d * B ^ 2)) ^ j * ∑' n, ‖c n‖ ^ 2 +
        A ^ 2 * Real.exp (-(γ * B)) *
          (tailConst j (Fintype.card d) * (1 / γ) ^ (2 * j + Fintype.card d)) := by
  have hA : 0 ≤ A := by
    have h := hc 0
    have := norm_nonneg (c 0)
    by_contra hA; push_neg at hA
    have : A * Real.exp (-(γ * linfNorm (0 : d → ℤ))) < 0 := mul_neg_of_neg_of_pos hA (Real.exp_pos _)
    linarith
  obtain ⟨hS, hT⟩ := tsum_weight_exp_le (d := d) hγ hγ1 j
  set g : (d → ℤ) → ℝ := fun n => sobWeight n ^ j * Real.exp (-(γ * linfNorm n))
  set W : ℝ := (1 + 4 * π ^ 2 * (Fintype.card d * B ^ 2)) ^ j
  have hsq : ∀ n, ‖c n‖ ^ 2 ≤ A ^ 2 * Real.exp (-(γ * linfNorm n)) * Real.exp (-(γ * linfNorm n)) := by
    intro n
    have := hc n
    calc ‖c n‖ ^ 2 ≤ (A * Real.exp (-(γ * linfNorm n))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := by ring
  have hL2 : Summable (fun n => ‖c n‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hS.mul_left (A ^ 2))
    refine (hsq n).trans ?_
    have h1 : Real.exp (-(γ * linfNorm n)) ≤ 1 := Real.exp_le_one_iff.mpr
      (by have : (0 : ℝ) ≤ linfNorm n := Nat.cast_nonneg _; nlinarith)
    have h2 : 1 ≤ sobWeight n ^ j := one_le_pow₀ (one_le_sobWeight n)
    have h3 := Real.exp_pos (-(γ * linfNorm n))
    calc A ^ 2 * Real.exp (-(γ * ↑(linfNorm n))) * Real.exp (-(γ * ↑(linfNorm n)))
        ≤ A ^ 2 * 1 * Real.exp (-(γ * ↑(linfNorm n))) := by gcongr
      _ ≤ A ^ 2 * (sobWeight n ^ j * Real.exp (-(γ * ↑(linfNorm n)))) := by
          rw [mul_one]; gcongr; nlinarith
  have hpt : ∀ n, sobWeight n ^ (j : ℝ) * ‖c n‖ ^ 2 ≤
      W * ‖c n‖ ^ 2 + A ^ 2 * Real.exp (-(γ * B)) * g n := by
    intro n
    rw [Real.rpow_natCast]
    set L : ℝ := (linfNorm n : ℝ)
    have hL : 0 ≤ L := Nat.cast_nonneg _
    have hw0 := (sobWeight_pos n).le
    have hg0 : 0 ≤ A ^ 2 * Real.exp (-(γ * B)) * g n := by
      have := (sobWeight_pos n).le; positivity
    by_cases hLB : L ≤ B
    · have hw : sobWeight n ≤ 1 + 4 * π ^ 2 * (Fintype.card d * B ^ 2) := by
        have := sobWeight_le_linf_sq n
        have h2 : L ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hL hLB 2
        have hp : 0 ≤ 4 * π ^ 2 * (Fintype.card d : ℝ) := by positivity
        nlinarith
      have : sobWeight n ^ j * ‖c n‖ ^ 2 ≤ W * ‖c n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hw0 hw j) (by positivity)
      linarith
    · push_neg at hLB
      have hexp : Real.exp (-(γ * L)) ≤ Real.exp (-(γ * B)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have h1 : sobWeight n ^ j * ‖c n‖ ^ 2 ≤ A ^ 2 * Real.exp (-(γ * B)) * g n := by
        calc sobWeight n ^ j * ‖c n‖ ^ 2
            ≤ sobWeight n ^ j * (A ^ 2 * Real.exp (-(γ * L)) * Real.exp (-(γ * L))) := by
              gcongr; exact hsq n
          _ ≤ sobWeight n ^ j * (A ^ 2 * Real.exp (-(γ * B)) * Real.exp (-(γ * L))) := by
              gcongr
          _ = A ^ 2 * Real.exp (-(γ * B)) * g n := by simp only [g, L]; ring
      have : 0 ≤ W * ‖c n‖ ^ 2 := by positivity
      linarith
  have hsumR : Summable (fun n => W * ‖c n‖ ^ 2 + A ^ 2 * Real.exp (-(γ * B)) * g n) :=
    (hL2.mul_left W).add (hS.mul_left _)
  have hmem : CoeffMemH (j : ℝ) c :=
    Summable.of_nonneg_of_le (coeffSobSq_term_nonneg _ _) hpt hsumR
  refine ⟨hmem, hL2, ?_⟩
  calc coeffSobSq (j : ℝ) c = ∑' n, sobWeight n ^ (j : ℝ) * ‖c n‖ ^ 2 := rfl
    _ ≤ ∑' n, (W * ‖c n‖ ^ 2 + A ^ 2 * Real.exp (-(γ * B)) * g n) :=
        Summable.tsum_le_tsum hpt hmem hsumR
    _ = W * ∑' n, ‖c n‖ ^ 2 + A ^ 2 * Real.exp (-(γ * B)) * ∑' n, g n := by
        rw [Summable.tsum_add (hL2.mul_left W) (hS.mul_left _), tsum_mul_left, tsum_mul_left]
    _ ≤ _ := by
        have : 0 ≤ A ^ 2 * Real.exp (-(γ * B)) := by positivity
        gcongr

/-! ### Space-time split and Parseval -/

/-- Parseval for continuous functions on `𝕋^d`: `Σ_n |F̂(n)|² = ∫ |F|²`. -/
theorem sobSq_zero_eq_integral_continuous (F : C(UnitAddTorus d, ℂ)) :
    sobSq 0 (⇑F) = ∫ x, ‖F x‖ ^ 2 := by
  have h1 : sobSq 0 (⇑F) = sobSq 0 (⇑(F.toLp 2 volume ℂ)) := by
    unfold sobSq; congr 1; funext n; exact (mFourierCoeff_toLp F n).symm
  rw [h1, sobSq_zero_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume F] with x hx
  rw [hx]

/-- **Space-time frequency split** (`L²_t H^j_x`, any measure space of times): if every slice
`f(t)` has `|f̂(t,n)| ≤ A e^{-γ|n|_∞}`, then each `f(t) ∈ H^j` and
`∫ ‖f(t)‖²_{H^j} ≤ (1 + 4π² d B²)^j ∫ ‖f(t)‖²_{L²} + μ(I) A² e^{-γB} M_{j,d} γ^{-(2j+d)}`. -/
theorem lintegral_sobSq_le_split [Nonempty d] {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → UnitAddTorus d → ℂ) {A γ B : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hc : ∀ t n, ‖mFourierCoeff (f t) n‖ ≤ A * Real.exp (-(γ * linfNorm n))) (j : ℕ) :
    (∀ t, MemH (j : ℝ) (f t)) ∧
      ∫⁻ t, ENNReal.ofReal (sobSq (j : ℝ) (f t)) ∂μ ≤
        ENNReal.ofReal ((1 + 4 * π ^ 2 * (Fintype.card d * B ^ 2)) ^ j) *
            ∫⁻ t, ENNReal.ofReal (sobSq 0 (f t)) ∂μ +
          μ univ * ENNReal.ofReal (A ^ 2 * Real.exp (-(γ * B)) *
            (tailConst j (Fintype.card d) * (1 / γ) ^ (2 * j + Fintype.card d))) := by
  refine ⟨fun t => (coeffSobSq_le_split (B := B) _ hγ hγ1 (hc t) j).1, ?_⟩
  set W : ℝ := (1 + 4 * π ^ 2 * (Fintype.card d * B ^ 2)) ^ j
  set R : ℝ := A ^ 2 * Real.exp (-(γ * B)) *
    (tailConst j (Fintype.card d) * (1 / γ) ^ (2 * j + Fintype.card d))
  have hW : 0 ≤ W := by positivity
  have hR : 0 ≤ R := by have := tailConst_nonneg j (Fintype.card d); positivity
  have hpt : ∀ t, ENNReal.ofReal (sobSq (j : ℝ) (f t)) ≤
      ENNReal.ofReal W * ENNReal.ofReal (sobSq 0 (f t)) + ENNReal.ofReal R := by
    intro t
    obtain ⟨-, -, h⟩ := coeffSobSq_le_split (B := B) (mFourierCoeff (f t)) hγ hγ1 (hc t) j
    have h0 : sobSq 0 (f t) = ∑' n, ‖mFourierCoeff (f t) n‖ ^ 2 := coeffSobSq_zero _
    rw [← ENNReal.ofReal_mul hW, ← ENNReal.ofReal_add (mul_nonneg hW (sobSq_nonneg _ _)) hR, h0]
    exact ENNReal.ofReal_le_ofReal h
  calc ∫⁻ t, ENNReal.ofReal (sobSq (j : ℝ) (f t)) ∂μ
      ≤ ∫⁻ t, (ENNReal.ofReal W * ENNReal.ofReal (sobSq 0 (f t)) + ENNReal.ofReal R) ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal W * ∫⁻ t, ENNReal.ofReal (sobSq 0 (f t)) ∂μ + μ univ * ENNReal.ofReal R := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const, mul_comm (ENNReal.ofReal R)]

theorem strip_mono {b b' : ℝ} (h : b ≤ b') : strip b ⊆ strip b' := fun _ hz =>
  lt_of_lt_of_le hz h

/-- The coefficient decay delivered by the strip hypothesis of `lem:log-source-upgrade`, at the
reduced width `a' = min a 1` (so that `γ = a'/K ≤ 1`). -/
theorem coeff_decay_of_strip [Nonempty d] (F : C(UnitAddTorus d, ℂ)) {a A K : ℝ} (ha : 0 < a)
    (hK : 1 ≤ K)
    (hext : ∀ x i, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (strip (a / (2 * π * K))) ∧
        (∀ s : ℝ, G s = F (x + lineShift i s)) ∧ ∀ z ∈ strip (a / (2 * π * K)), ‖G z‖ ≤ A)
    (n : d → ℤ) :
    ‖mFourierCoeff F n‖ ≤ A * Real.exp (-((min a 1 / K) * linfNorm n)) := by
  have hK0 : 0 < K := by linarith
  have ha' : 0 < min a 1 := lt_min ha one_pos
  have hsub : min a 1 / (2 * π * K) ≤ a / (2 * π * K) :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
  have hb : 0 < min a 1 / (2 * π * K) := by positivity
  have h := norm_mFourierCoeff_le_of_strip F hb (fun x i => by
    obtain ⟨G, hG1, hG2, hG3⟩ := hext x i
    exact ⟨G, hG1.mono (strip_mono hsub), hG2, fun z hz => hG3 z (strip_mono hsub hz)⟩) n
  have he : 2 * π * (min a 1 / (2 * π * K)) * (linfNorm n : ℝ) = min a 1 / K * linfNorm n := by
    field_simp
  rwa [he] at h

/-- **`lem:log-source-upgrade`** (`eq:log-source-upgrade`), `ε > 0`.  Fix `a > 0`, an integer
`j`, and a finite measure `μ` of times (the slab `I`).  There is `C = C_{j,d,a,μ(I)} > 0` such that
for every family of continuous slices `f(t) : 𝕋^d → ℂ` that extend holomorphically along every
coordinate line to the strip of width `a/K` (period-`2π` units; `a/(2πK)` on the unit torus),
bounded there by `A ≥ 0`, with `K ≥ 1` and `‖f‖²_{L²(Q)} = ∫_I ∫_{𝕋^d} |f|² ≤ ε²`, every slice is in
`H^j` and
`‖f‖²_{L²_t H^j_x} ≤ (C ε K^j [1 + log(2 + C A K^{j+d}/ε)]^j)²`. -/
theorem log_source_upgrade [Nonempty d] {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {a : ℝ} (ha : 0 < a) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : α → C(UnitAddTorus d, ℂ)) (A K ε : ℝ), 0 ≤ A → 1 ≤ K → 0 < ε →
      (∀ t x i, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (strip (a / (2 * π * K))) ∧
        (∀ s : ℝ, G s = f t (x + lineShift i s)) ∧ ∀ z ∈ strip (a / (2 * π * K)), ‖G z‖ ≤ A) →
      ∫⁻ t, ENNReal.ofReal (∫ x, ‖f t x‖ ^ 2) ∂μ ≤ ENNReal.ofReal (ε ^ 2) →
      (∀ t, MemH (j : ℝ) (f t)) ∧
        ∫⁻ t, ENNReal.ofReal (sobSq (j : ℝ) (f t)) ∂μ ≤
          ENNReal.ofReal ((C * ε * K ^ j *
            (1 + Real.log (2 + C * A * K ^ (j + Fintype.card d) / ε)) ^ j) ^ 2) := by
  set D := Fintype.card d with hD
  set a' := min a 1 with ha'def
  have ha' : 0 < a' := lt_min ha one_pos
  have ha'1 : a' ≤ 1 := min_le_right _ _
  set T : ℝ := (μ univ).toReal
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  set M := tailConst j D
  have hM : 0 ≤ M := tailConst_nonneg j D
  set X : ℝ := T * M * (1 / a') ^ (2 * j + D)
  have hX : 0 ≤ X := by positivity
  set C₀ : ℝ := Real.sqrt X + 1
  set C₁ : ℝ := 1 + 16 * π ^ 2 * D / a' ^ 2
  have hC₁ : 1 ≤ C₁ := by
    have : 0 ≤ 16 * π ^ 2 * (D : ℝ) / a' ^ 2 := by positivity
    linarith
  set C₂ : ℝ := Real.sqrt (C₁ ^ j + 1)
  have hC₀ : 0 < C₀ := by positivity
  refine ⟨max C₀ C₂, lt_of_lt_of_le hC₀ (le_max_left _ _), ?_⟩
  intro f A K ε hA hK hε hext hL2
  set C := max C₀ C₂
  have hK0 : 0 < K := by linarith
  set Y : ℝ := 2 + C * A * K ^ (j + D) / ε
  have hY : 2 ≤ Y := by
    have : 0 ≤ C * A * K ^ (j + D) / ε := by
      have : 0 ≤ C := le_trans hC₀.le (le_max_left _ _)
      positivity
    linarith
  set Λ : ℝ := 1 + Real.log Y
  have hΛ : 1 ≤ Λ := by have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ Y); linarith
  set γ : ℝ := a' / K
  have hγ0 : 0 < γ := by positivity
  have hγ1 : γ ≤ 1 := by rw [div_le_one hK0]; linarith
  set B : ℝ := 2 * K * Λ / a'
  have hγB : γ * B = 2 * Λ := by simp only [γ, B]; field_simp
  have hc : ∀ t n, ‖mFourierCoeff (f t) n‖ ≤ A * Real.exp (-(γ * linfNorm n)) :=
    fun t n => coeff_decay_of_strip (f t) ha hK (hext t) n
  obtain ⟨hmem, hsplit⟩ := lintegral_sobSq_le_split μ (fun t => ⇑(f t)) (B := B) hγ0 hγ1 hc j
  refine ⟨hmem, hsplit.trans ?_⟩
  have h0 : ∫⁻ t, ENNReal.ofReal (sobSq 0 (⇑(f t))) ∂μ ≤ ENNReal.ofReal (ε ^ 2) := by
    simp_rw [sobSq_zero_eq_integral_continuous]; exact hL2
  have hμ : μ univ = ENNReal.ofReal T := (ENNReal.ofReal_toReal (measure_ne_top μ univ)).symm
  set W : ℝ := (1 + 4 * π ^ 2 * (D * B ^ 2)) ^ j
  set R : ℝ := A ^ 2 * Real.exp (-(γ * B)) * (M * (1 / γ) ^ (2 * j + D))
  have hW : 0 ≤ W := by positivity
  have hR : 0 ≤ R := by positivity
  -- the real inequality
  have hKΛ : 1 ≤ K * Λ := by nlinarith
  have hWb : W ≤ C₁ ^ j * (K * Λ) ^ (2 * j) := by
    have hbase : 1 + 4 * π ^ 2 * (D * B ^ 2) ≤ C₁ * (K * Λ) ^ 2 := by
      have hB2 : B ^ 2 = 4 * (K * Λ) ^ 2 / a' ^ 2 := by simp only [B]; field_simp; ring
      rw [hB2]
      have h1 : (1 : ℝ) ≤ (K * Λ) ^ 2 := one_le_pow₀ hKΛ
      have e : 4 * π ^ 2 * (D * (4 * (K * Λ) ^ 2 / a' ^ 2)) =
          16 * π ^ 2 * D / a' ^ 2 * (K * Λ) ^ 2 := by field_simp; ring
      rw [e]; simp only [C₁]; nlinarith
    calc W ≤ (C₁ * (K * Λ) ^ 2) ^ j := pow_le_pow_left₀ (by positivity) hbase j
      _ = C₁ ^ j * (K * Λ) ^ (2 * j) := by rw [mul_pow, ← pow_mul, mul_comm 2 j]
  have hexpΛ : C₀ * A * K ^ (j + D) ≤ ε * Real.exp Λ := by
    have h1 : Real.exp Λ = Real.exp 1 * Y := by
      simp only [Λ]; rw [Real.exp_add, Real.exp_log (by linarith)]
    have h2 : C * A * K ^ (j + D) ≤ ε * Y := by
      simp only [Y]; rw [mul_add, mul_div_cancel₀ _ hε.ne']; nlinarith
    have h3 : C₀ * A * K ^ (j + D) ≤ C * A * K ^ (j + D) := by
      gcongr; exact le_max_left _ _
    have h4 : ε * Y ≤ ε * Real.exp Λ := by
      rw [h1]; have := Real.add_one_le_exp 1
      have : Y ≤ Real.exp 1 * Y := by nlinarith
      exact mul_le_mul_of_nonneg_left this hε.le
    linarith
  have hTR : T * R ≤ ε ^ 2 := by
    set E : ℝ := Real.exp (-(2 * Λ))
    have hE : 0 ≤ E := (Real.exp_pos _).le
    have hEE : Real.exp Λ ^ 2 * E = 1 := by
      simp only [E]; rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have hsq : (C₀ * A * K ^ (j + D)) ^ 2 ≤ (ε * Real.exp Λ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hexpΛ 2
    have h1 : C₀ ^ 2 * (A ^ 2 * K ^ (2 * j + 2 * D) * E) ≤ ε ^ 2 := by
      have e1 : C₀ ^ 2 * (A ^ 2 * K ^ (2 * j + 2 * D) * E) = (C₀ * A * K ^ (j + D)) ^ 2 * E := by
        rw [show 2 * j + 2 * D = (j + D) * 2 by ring, pow_mul]; ring
      have e2 : (ε * Real.exp Λ) ^ 2 * E = ε ^ 2 := by rw [mul_pow, mul_assoc, hEE, mul_one]
      rw [e1, ← e2]; exact mul_le_mul_of_nonneg_right hsq hE
    have hXC : X ≤ C₀ ^ 2 := by
      have := Real.sq_sqrt hX
      have : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
      simp only [C₀]; nlinarith
    have hKp : K ^ (2 * j + D) ≤ K ^ (2 * j + 2 * D) := pow_le_pow_right₀ hK (by omega)
    have eR : T * R = X * (K ^ (2 * j + D) * (A ^ 2 * E)) := by
      simp only [R, X, E, γ]; rw [hγB]
      rw [one_div_div, div_pow, one_div_pow, div_eq_mul_one_div (K ^ (2 * j + D))]; ring
    rw [eR]
    calc X * (K ^ (2 * j + D) * (A ^ 2 * E))
        ≤ C₀ ^ 2 * (K ^ (2 * j + 2 * D) * (A ^ 2 * E)) := by gcongr
      _ = C₀ ^ 2 * (A ^ 2 * K ^ (2 * j + 2 * D) * E) := by ring
      _ ≤ ε ^ 2 := h1
  have hfinal : W * ε ^ 2 + T * R ≤ (C * ε * K ^ j * Λ ^ j) ^ 2 := by
    have hKΛj : 1 ≤ (K * Λ) ^ (2 * j) := one_le_pow₀ hKΛ
    have hC2 : C₁ ^ j + 1 ≤ C ^ 2 := by
      have h1 : C₂ ^ 2 = C₁ ^ j + 1 := Real.sq_sqrt (by positivity)
      have h2 : C₂ ≤ C := le_max_right _ _
      have h3 : 0 ≤ C₂ := Real.sqrt_nonneg _
      nlinarith
    have e : (C * ε * K ^ j * Λ ^ j) ^ 2 = C ^ 2 * (K * Λ) ^ (2 * j) * ε ^ 2 := by
      rw [show 2 * j = j * 2 by ring, pow_mul, mul_pow]; ring
    rw [e]
    have hε2 : 0 ≤ ε ^ 2 := by positivity
    calc W * ε ^ 2 + T * R ≤ C₁ ^ j * (K * Λ) ^ (2 * j) * ε ^ 2 + ε ^ 2 := by
          gcongr
      _ ≤ C₁ ^ j * (K * Λ) ^ (2 * j) * ε ^ 2 + (K * Λ) ^ (2 * j) * ε ^ 2 := by
          gcongr; nlinarith
      _ = (C₁ ^ j + 1) * (K * Λ) ^ (2 * j) * ε ^ 2 := by ring
      _ ≤ C ^ 2 * (K * Λ) ^ (2 * j) * ε ^ 2 := by gcongr
  calc ENNReal.ofReal W * ∫⁻ t, ENNReal.ofReal (sobSq 0 (⇑(f t))) ∂μ + μ univ * ENNReal.ofReal R
      ≤ ENNReal.ofReal W * ENNReal.ofReal (ε ^ 2) + ENNReal.ofReal T * ENNReal.ofReal R := by
        rw [hμ]; gcongr
    _ = ENNReal.ofReal (W * ε ^ 2 + T * R) := by
        rw [← ENNReal.ofReal_mul hW, ← ENNReal.ofReal_mul hT,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfinal

/-- **`lem:log-source-upgrade`, the case `ε = 0`** ("the right side is interpreted as zero"):
a strip-analytic source with vanishing `L²(Q)` norm has vanishing `L²_t H^j_x` norm. -/
theorem log_source_upgrade_zero [Nonempty d] {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {a A K : ℝ} (ha : 0 < a) (hK : 1 ≤ K) (j : ℕ)
    (f : α → C(UnitAddTorus d, ℂ))
    (hext : ∀ t x i, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (strip (a / (2 * π * K))) ∧
        (∀ s : ℝ, G s = f t (x + lineShift i s)) ∧ ∀ z ∈ strip (a / (2 * π * K)), ‖G z‖ ≤ A)
    (hL2 : ∫⁻ t, ENNReal.ofReal (∫ x, ‖f t x‖ ^ 2) ∂μ = 0) :
    ∫⁻ t, ENNReal.ofReal (sobSq (j : ℝ) (f t)) ∂μ = 0 := by
  have hK0 : 0 < K := by linarith
  set γ : ℝ := min a 1 / K
  have hγ0 : 0 < γ := div_pos (lt_min ha one_pos) hK0
  have hγ1 : γ ≤ 1 := by rw [div_le_one hK0]; linarith [min_le_right a 1]
  have hc : ∀ t n, ‖mFourierCoeff (f t) n‖ ≤ A * Real.exp (-(γ * linfNorm n)) :=
    fun t n => coeff_decay_of_strip (f t) ha hK (hext t) n
  have h0 : ∫⁻ t, ENNReal.ofReal (sobSq 0 (⇑(f t))) ∂μ = 0 := by
    simp_rw [sobSq_zero_eq_integral_continuous]; exact hL2
  set Q : ℝ := A ^ 2 * (tailConst j (Fintype.card d) * (1 / γ) ^ (2 * j + Fintype.card d))
  have hbound : ∀ B : ℝ, ∫⁻ t, ENNReal.ofReal (sobSq (j : ℝ) (f t)) ∂μ ≤
      μ univ * ENNReal.ofReal (Q * Real.exp (-(γ * B))) := by
    intro B
    have h := (lintegral_sobSq_le_split μ (fun t => ⇑(f t)) (B := B) hγ0 hγ1 hc j).2
    rw [h0, mul_zero, zero_add] at h
    refine h.trans (le_of_eq ?_)
    congr 2; simp only [Q]; ring
  have ht : Tendsto (fun B : ℝ => μ univ * ENNReal.ofReal (Q * Real.exp (-(γ * B)))) atTop
      (𝓝 (μ univ * ENNReal.ofReal 0)) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr (measure_ne_top μ univ))
    refine ENNReal.tendsto_ofReal ?_
    have : Tendsto (fun B : ℝ => Real.exp (-(γ * B))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hγ0)
    simpa using this.const_mul Q
  rw [ENNReal.ofReal_zero, mul_zero] at ht
  exact le_antisymm (ge_of_tendsto' ht hbound) bot_le

/-! ### Non-vacuity -/

/-- Non-vacuity of `log_source_upgrade`: the hypotheses hold for the constant source `f ≡ 1` on
`𝕋³` over a one-point time set (`A = K = ε = 1`, any `a > 0`). -/
example : ∃ C : ℝ, 0 < C ∧
    ∫⁻ _t, ENNReal.ofReal (sobSq ((1 : ℕ) : ℝ) ⇑(ContinuousMap.const (UnitAddTorus (Fin 3)) (1 : ℂ)))
        ∂(Measure.dirac ()) ≤
      ENNReal.ofReal ((C * 1 * 1 ^ 1 * (1 + Real.log (2 + C * 1 * 1 ^ (1 + 3) / 1)) ^ 1) ^ 2) := by
  obtain ⟨C, hC, hmain⟩ := log_source_upgrade (d := Fin 3) (Measure.dirac ()) (a := 1) one_pos 1
  refine ⟨C, hC, ?_⟩
  have h := (hmain (fun _ : Unit => ContinuousMap.const (UnitAddTorus (Fin 3)) (1 : ℂ)) 1 1 1
    zero_le_one le_rfl one_pos (fun t x i => ⟨fun _ => 1, differentiableOn_const _,
      fun s => rfl, fun z _ => by simp⟩) ?_).2
  · simpa using h
  · rw [lintegral_dirac]
    simp

end

end RenewalGeometry.AnalyticSourceUpgrade
