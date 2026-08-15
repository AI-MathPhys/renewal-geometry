/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact completed-private renewal law
  (`thm:completed-private-renewal`)

The concrete completed-private Store packet has direct-return
count `D` with `P(D = d) = (4/5)(1/5)^d` and private duration
`L` with `P(L = 2+n) = (2/3)(1/3)^n`, independent by the strong
Markov property.  For the interarrival `W = D + L` this file
proves, exactly:

* `sum_antidiagonal_pD_pL` / `law_add`: the mass function
  `P(W = n) = 4(3^{1-n} - 5^{1-n})` for `n ≥ 2` (convolution at
  the pmf level, and at the measure level for independent
  `ℕ`-valued random variables);
* `hasSum_wpmf`: normalization;
* `wpmf_pgf`: the generating function
  `E[z^W] = 8z²/((5-z)(3-z))` for `|z| < 3`;
* `wpmf_mean` / `wpmf_variance`: `E W = 11/4`,
  `Var W = 17/16`;
* `tailProb_eq` / `tailProb_le`: the tail identity
  `P(W > N) = 6·3^{-N} - 5·5^{-N} ≤ 6·3^{-N}` for `N ≥ 1`;
* `renewal_count_tendsto`: the deterministic renewal inversion
  — partial sums with increments `≥ 1` and Cesàro limit `m > 0`
  have counting function `N_t/t → 1/m`;
* `completed_private_renewal_law`: the almost-sure renewal law
  `N_t/t → 4/11` for iid interarrivals with the completed-
  private law, via the strong law of large numbers.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace NCG
namespace CompletedPrivateRenewal

/-- Direct hub-edge return count law: `P(D = d) = (4/5)(1/5)^d`. -/
noncomputable def pD (d : ℕ) : ℝ := (4 / 5) * (1 / 5) ^ d

/-- Private duration law: `P(L = 2+n) = (2/3)(1/3)^n`. -/
noncomputable def pL (l : ℕ) : ℝ :=
  if 2 ≤ l then (2 / 3) * (1 / 3) ^ (l - 2) else 0

/-- The interarrival mass function
`P(W = n) = 4(3^{1-n} - 5^{1-n})` for `n ≥ 2`. -/
noncomputable def wpmf (n : ℕ) : ℝ :=
  if 2 ≤ n then
    4 * ((1 / 3) ^ (n - 1) - (1 / 5 : ℝ) ^ (n - 1)) else 0

theorem wpmf_add_two (m : ℕ) :
    wpmf (m + 2)
      = 4 * ((1 / 3) ^ (m + 1) - (1 / 5 : ℝ) ^ (m + 1)) := by
  simp [wpmf]

theorem wpmf_nonneg (n : ℕ) : 0 ≤ wpmf n := by
  unfold wpmf
  split
  · have h : ((1 : ℝ) / 5) ^ (n - 1) ≤ (1 / 3) ^ (n - 1) := by
      gcongr
      norm_num
    nlinarith
  · exact le_refl 0

/-- Convolution of the two geometric laws gives the boxed mass
function. -/
theorem sum_antidiagonal_pD_pL (n : ℕ) :
    (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      pD kl.1 * pL kl.2) = wpmf n := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- no mass below 2
    have hz : ∀ i ∈ Finset.range (n + 1),
        pD i * pL (n - i) = 0 := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have : ¬ 2 ≤ n - i := by omega
      simp [pL, this]
    rw [Finset.sum_congr rfl hz, Finset.sum_const,
      smul_zero]
    have : ¬ 2 ≤ n := by omega
    simp [wpmf, this]
  · -- only `i ≤ n - 2` contributes
    have hsub : Finset.range (n - 1)
        ⊆ Finset.range (n + 1) := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    rw [← Finset.sum_subset hsub (by
      intro i hi1 hi2
      have hi1' := Finset.mem_range.mp hi1
      simp only [Finset.mem_range] at hi2
      have : ¬ 2 ≤ n - i := by omega
      simp [pL, this])]
    have hterm : ∀ i ∈ Finset.range (n - 1),
        pD i * pL (n - i)
        = (8 / 15) * ((1 / 5) ^ i
            * (1 / 3 : ℝ) ^ (n - 2 - i)) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have h2 : 2 ≤ n - i := by omega
      have h3 : n - i - 2 = n - 2 - i := by omega
      rw [pD, pL, if_pos h2, h3]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hgeom : (∑ i ∈ Finset.range (n - 1),
        (1 / 5) ^ i * (1 / 3 : ℝ) ^ (n - 2 - i))
        = (15 / 2) * ((1 / 3) ^ (n - 1)
            - (1 / 5 : ℝ) ^ (n - 1)) := by
      have h := geom_sum₂_mul (R := ℝ) (1 / 5) (1 / 3)
        (n - 1)
      have hxy : ((1 : ℝ) / 5) - 1 / 3 ≠ 0 := by norm_num
      have h2 : (∑ i ∈ Finset.range (n - 1),
          (1 / 5) ^ i * (1 / 3 : ℝ) ^ (n - 2 - i))
          = ((1 / 5) ^ (n - 1) - (1 / 3 : ℝ) ^ (n - 1))
            / (1 / 5 - 1 / 3) := by
        rw [eq_div_iff hxy]
        exact h
      rw [h2]
      have h5 : ((1 : ℝ) / 5) - 1 / 3 = -(2 / 15) := by
        norm_num
      rw [h5]
      field_simp
      ring
    rw [hgeom, wpmf, if_pos hn]
    ring

/-! ### Series identities for the interarrival law -/

/-- Lift a `HasSum` for the shifted sequence to the full
sequence when the first two terms vanish. -/
theorem hasSum_of_shift {g : ℕ → ℝ} {S : ℝ}
    (h : HasSum (fun m => g (m + 2)) S)
    (h0 : g 0 = 0) (h1 : g 1 = 0) : HasSum g S := by
  have h2 := (hasSum_nat_add_iff (f := g) 2).mp h
  rw [Finset.sum_range_succ, Finset.sum_range_one, h0, h1,
    add_zero, add_zero] at h2
  exact h2

theorem wpmf_zero : wpmf 0 = 0 := by simp [wpmf]
theorem wpmf_one : wpmf 1 = 0 := by simp [wpmf]

/-- Shifted linear-geometric sum:
`∑ (m+1) r^m = 1/(1-r)²`. -/
theorem hasSum_succ_mul_geometric {r : ℝ} (hr : |r| < 1) :
    HasSum (fun m : ℕ => ((m : ℝ) + 1) * r ^ m)
      (1 / (1 - r) ^ 2) := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) 1 (by rwa [Real.norm_eq_abs])
  have hval : (1 : ℝ) / (1 - r) ^ (1 + 1)
      = 1 / (1 - r) ^ 2 := by norm_num
  rw [hval] at h
  refine h.congr_fun fun m => ?_
  push_cast [Nat.choose_one_right]
  ring

/-- Shifted quadratic-geometric sum:
`∑ (m+2)(m+1) r^m = 2/(1-r)³`. -/
theorem hasSum_succ_succ_mul_geometric {r : ℝ}
    (hr : |r| < 1) :
    HasSum (fun m : ℕ => ((m : ℝ) + 2) * ((m : ℝ) + 1)
      * r ^ m) (2 / (1 - r) ^ 3) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) 2 (by rwa [Real.norm_eq_abs])).mul_left 2
  have hval : (2 : ℝ) * (1 / (1 - r) ^ (2 + 1))
      = 2 / (1 - r) ^ 3 := by ring
  rw [hval] at h
  refine h.congr_fun fun m => ?_
  have hnat : (m + 2).choose 2 * 2 = (m + 2) * (m + 1) := by
    rw [Nat.choose_two_right,
      show m + 2 - 1 = m + 1 from rfl]
    exact Nat.div_mul_cancel
      (by simpa [Nat.mul_comm] using
        (Nat.even_mul_succ_self (m + 1)).two_dvd)
  have hr : (((m + 2).choose 2 : ℕ) : ℝ) * 2
      = ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
    exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) hnat
  rw [← hr]
  ring

/-- **Normalization**: the interarrival law has total mass
one. -/
theorem hasSum_wpmf : HasSum wpmf 1 := by
  refine hasSum_of_shift ?_ wpmf_zero wpmf_one
  have h3 : HasSum (fun m : ℕ => (4 / 3) * (1 / 3 : ℝ) ^ m)
      2 := by
    have h := (hasSum_geometric_of_lt_one (r := (1/3 : ℝ))
      (by norm_num) (by norm_num)).mul_left (4 / 3)
    norm_num at h
    exact h
  have h5 : HasSum (fun m : ℕ => (4 / 5) * (1 / 5 : ℝ) ^ m)
      1 := by
    have h := (hasSum_geometric_of_lt_one (r := (1/5 : ℝ))
      (by norm_num) (by norm_num)).mul_left (4 / 5)
    norm_num at h
    exact h
  have h := h3.sub h5
  norm_num at h
  refine h.congr_fun fun m => ?_
  rw [wpmf_add_two]
  ring

/-- **The probability generating function**:
`E[z^W] = 8z²/((5-z)(3-z))` for `|z| < 3`. -/
theorem wpmf_pgf (z : ℝ) (hz : |z| < 3) :
    ∑' n : ℕ, wpmf n * z ^ n
      = 8 * z ^ 2 / ((5 - z) * (3 - z)) := by
  have hz3 : |z / 3| < 1 := by
    rw [abs_div]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 3)]
    · exact (div_lt_one (by norm_num)).mpr hz
  have hz5 : |z / 5| < 1 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 5)]
    exact (div_lt_one (by norm_num)).mpr
      (lt_trans hz (by norm_num))
  have h3ne : (3 : ℝ) - z ≠ 0 := by
    rcases abs_lt.mp hz with ⟨_, h⟩
    linarith
  have h5ne : (5 : ℝ) - z ≠ 0 := by
    rcases abs_lt.mp hz with ⟨_, h⟩
    linarith
  have h3 : HasSum (fun m : ℕ =>
      (4 / 3) * z ^ 2 * (z / 3 : ℝ) ^ m)
      ((4 / 3) * z ^ 2 * (1 - z / 3)⁻¹) :=
    (hasSum_geometric_of_abs_lt_one hz3).mul_left _
  have h5 : HasSum (fun m : ℕ =>
      (4 / 5) * z ^ 2 * (z / 5 : ℝ) ^ m)
      ((4 / 5) * z ^ 2 * (1 - z / 5)⁻¹) :=
    (hasSum_geometric_of_abs_lt_one hz5).mul_left _
  have h := h3.sub h5
  have hfun : HasSum (fun n : ℕ => wpmf n * z ^ n)
      ((4 / 3) * z ^ 2 * (1 - z / 3)⁻¹
        - (4 / 5) * z ^ 2 * (1 - z / 5)⁻¹) := by
    refine hasSum_of_shift ?_ (by simp [wpmf_zero])
      (by simp [wpmf_one])
    refine h.congr_fun fun m => ?_
    rw [wpmf_add_two]
    field_simp
    ring
  rw [hfun.tsum_eq]
  field_simp
  ring

/-- **The mean**: `E W = 11/4`. -/
theorem wpmf_mean :
    ∑' n : ℕ, (n : ℝ) * wpmf n = 11 / 4 := by
  have hkey : ∀ r : ℝ, |r| < 1 →
      HasSum (fun m : ℕ => ((m : ℝ) + 2) * r ^ (m + 1))
        (r * (1 / (1 - r) ^ 2 + (1 - r)⁻¹)) := by
    intro r hr
    have h1 := hasSum_succ_mul_geometric hr
    have h2 := hasSum_geometric_of_abs_lt_one hr
    have h := (h1.add h2).mul_left r
    refine h.congr_fun fun m => ?_
    ring
  have h3 := (hkey (1/3) (by norm_num)).mul_left 4
  have h5 := (hkey (1/5) (by norm_num)).mul_left 4
  have h := h3.sub h5
  have hval : (4 : ℝ) * ((1/3) * (1 / (1 - 1/3) ^ 2
      + (1 - 1/3 : ℝ)⁻¹))
      - 4 * ((1/5) * (1 / (1 - 1/5) ^ 2
        + (1 - 1/5 : ℝ)⁻¹)) = 11 / 4 := by
    norm_num
  rw [hval] at h
  have hfun : HasSum (fun n : ℕ => (n : ℝ) * wpmf n)
      (11 / 4) := by
    refine hasSum_of_shift ?_ (by simp [wpmf_zero])
      (by simp [wpmf_one])
    refine h.congr_fun fun m => ?_
    rw [wpmf_add_two]
    push_cast
    ring
  exact hfun.tsum_eq

/-- The second factorial moment: `E[W(W-1)] = 47/8`. -/
theorem wpmf_second_factorial :
    ∑' n : ℕ, (n : ℝ) * ((n : ℝ) - 1) * wpmf n
      = 47 / 8 := by
  have hkey : ∀ r : ℝ, |r| < 1 →
      HasSum (fun m : ℕ =>
        ((m : ℝ) + 2) * ((m : ℝ) + 1) * r ^ (m + 1))
        (r * (2 / (1 - r) ^ 3)) := by
    intro r hr
    have h := (hasSum_succ_succ_mul_geometric hr).mul_left r
    refine h.congr_fun fun m => ?_
    ring
  have h3 := (hkey (1/3) (by norm_num)).mul_left 4
  have h5 := (hkey (1/5) (by norm_num)).mul_left 4
  have h := h3.sub h5
  have hval : (4 : ℝ) * ((1/3) * (2 / (1 - 1/3) ^ 3))
      - 4 * ((1/5) * (2 / (1 - 1/5 : ℝ) ^ 3)) = 47 / 8 := by
    norm_num
  rw [hval] at h
  have hfun : HasSum (fun n : ℕ =>
      (n : ℝ) * ((n : ℝ) - 1) * wpmf n) (47 / 8) := by
    refine hasSum_of_shift ?_ (by simp [wpmf_zero])
      (by simp [wpmf_one])
    refine h.congr_fun fun m => ?_
    rw [wpmf_add_two]
    push_cast
    ring
  exact hfun.tsum_eq

/-- Summability of the centered square series. -/
theorem summable_wpmf_poly (a b c : ℝ) :
    Summable (fun n : ℕ =>
      (a * ((n:ℝ) * ((n:ℝ) - 1)) + b * (n:ℝ) + c)
        * wpmf n) := by
  have h2 : Summable (fun n : ℕ =>
      (n : ℝ) * ((n : ℝ) - 1) * wpmf n) := by
    have := wpmf_second_factorial
    by_contra hcon
    rw [tsum_eq_zero_of_not_summable hcon] at this
    norm_num at this
  have h1 : Summable (fun n : ℕ => (n : ℝ) * wpmf n) := by
    have := wpmf_mean
    by_contra hcon
    rw [tsum_eq_zero_of_not_summable hcon] at this
    norm_num at this
  have h0 : Summable wpmf := hasSum_wpmf.summable
  have := ((h2.mul_left a).add (h1.mul_left b)).add
    (h0.mul_left c)
  refine this.congr fun n => ?_
  ring

/-- **The variance**: `Var W = 17/16`. -/
theorem wpmf_variance :
    ∑' n : ℕ, ((n : ℝ) - 11 / 4) ^ 2 * wpmf n
      = 17 / 16 := by
  have h2 : Summable (fun n : ℕ =>
      (n : ℝ) * ((n : ℝ) - 1) * wpmf n) := by
    have := wpmf_second_factorial
    by_contra hcon
    rw [tsum_eq_zero_of_not_summable hcon] at this
    norm_num at this
  have h1 : Summable (fun n : ℕ => (n : ℝ) * wpmf n) := by
    have := wpmf_mean
    by_contra hcon
    rw [tsum_eq_zero_of_not_summable hcon] at this
    norm_num at this
  have h0 : Summable wpmf := hasSum_wpmf.summable
  have hcongr : ∀ n : ℕ,
      ((n : ℝ) - 11 / 4) ^ 2 * wpmf n
      = (n : ℝ) * ((n : ℝ) - 1) * wpmf n
        + (-9 / 2) * ((n : ℝ) * wpmf n)
        + (121 / 16) * wpmf n := by
    intro n
    ring
  rw [tsum_congr hcongr]
  rw [(h2.add ((h1.mul_left (-9/2)))).tsum_add
    (h0.mul_left (121/16)), h2.tsum_add
    (h1.mul_left (-9/2)), tsum_mul_left, tsum_mul_left,
    wpmf_second_factorial, wpmf_mean, hasSum_wpmf.tsum_eq]
  norm_num

/-- The tail probability `P(W > N)`. -/
noncomputable def tailProb (N : ℕ) : ℝ :=
  ∑' k : ℕ, wpmf (N + 1 + k)

/-- **The tail identity**:
`P(W > N) = 6·3^{-N} - 5·5^{-N}` for `N ≥ 1`. -/
theorem tailProb_eq (N : ℕ) (hN : 1 ≤ N) :
    tailProb N
      = 6 * (1 / 3 : ℝ) ^ N - 5 * (1 / 5 : ℝ) ^ N := by
  have h3 : HasSum (fun k : ℕ =>
      (4 * (1 / 3 : ℝ) ^ N) * (1 / 3) ^ k)
      ((4 * (1 / 3 : ℝ) ^ N) * (1 - 1/3)⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num)
      (by norm_num)).mul_left _
  have h5 : HasSum (fun k : ℕ =>
      (4 * (1 / 5 : ℝ) ^ N) * (1 / 5) ^ k)
      ((4 * (1 / 5 : ℝ) ^ N) * (1 - 1/5)⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num)
      (by norm_num)).mul_left _
  have h := h3.sub h5
  have hfun : HasSum (fun k : ℕ => wpmf (N + 1 + k))
      ((4 * (1 / 3 : ℝ) ^ N) * (1 - 1/3)⁻¹
        - (4 * (1 / 5 : ℝ) ^ N) * (1 - 1/5)⁻¹) := by
    refine h.congr_fun fun k => ?_
    have h2 : 2 ≤ N + 1 + k := by omega
    have hidx : N + 1 + k - 1 = N + k := by omega
    rw [wpmf, if_pos h2, hidx, pow_add, pow_add]
    ring
  rw [tailProb, hfun.tsum_eq]
  field_simp
  ring

/-- **The tail bound**: `P(W > N) ≤ 6·3^{-N}`. -/
theorem tailProb_le (N : ℕ) (hN : 1 ≤ N) :
    tailProb N ≤ 6 * (1 / 3 : ℝ) ^ N := by
  rw [tailProb_eq N hN]
  have : 0 ≤ 5 * (1 / 5 : ℝ) ^ N := by positivity
  linarith

/-! ### Summability export -/

theorem summable_id_mul_wpmf :
    Summable (fun n : ℕ => (n : ℝ) * wpmf n) := by
  have h := wpmf_mean
  by_contra hcon
  rw [tsum_eq_zero_of_not_summable hcon] at h
  norm_num at h

/-! ### The measure-level interarrival law -/

/-- **Measure-level convolution**: independent `ℕ`-valued
`D`, `L` with the packet laws give `P(D + L = n) = wpmf n`. -/
theorem law_add {Ω : Type} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (D L : Ω → ℕ) (hD : Measurable D) (hL : Measurable L)
    (hindep : IndepFun D L μ)
    (hlawD : ∀ d, (μ {ω | D ω = d}).toReal = pD d)
    (hlawL : ∀ l, (μ {ω | L ω = l}).toReal = pL l) (n : ℕ) :
    (μ {ω | D ω + L ω = n}).toReal = wpmf n := by
  have hset : {ω | D ω + L ω = n}
      = ⋃ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
          (D ⁻¹' {kl.1} ∩ L ⁻¹' {kl.2}) := by
    ext ω
    constructor
    · intro h
      refine Set.mem_iUnion.mpr ⟨(D ω, L ω), ?_⟩
      refine Set.mem_iUnion.mpr
        ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr h, rfl, rfl⟩
    · intro h
      obtain ⟨kl, h1⟩ := Set.mem_iUnion.mp h
      obtain ⟨hmem, hd, hl⟩ := Set.mem_iUnion.mp h1
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
        at hd hl
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hmem
      rw [Set.mem_setOf_eq, hd, hl]
      exact hsum
  have hdisj : (↑(Finset.HasAntidiagonal.antidiagonal n)
        : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun kl => D ⁻¹' {kl.1} ∩ L ⁻¹' {kl.2}) := by
    intro p _ q _ hpq
    refine Set.disjoint_left.mpr ?_
    rintro ω ⟨hd1, hl1⟩ ⟨hd2, hl2⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
      at hd1 hl1 hd2 hl2
    refine hpq ?_
    have h1 : p.1 = q.1 := by rw [← hd1, ← hd2]
    have h2 : p.2 = q.2 := by rw [← hl1, ← hl2]
    exact Prod.ext h1 h2
  have hmeasset : ∀ kl ∈
      Finset.HasAntidiagonal.antidiagonal n,
      MeasurableSet (D ⁻¹' {kl.1} ∩ L ⁻¹' {kl.2}) :=
    fun kl _ => (hD (measurableSet_singleton _)).inter
      (hL (measurableSet_singleton _))
  rw [hset, measure_biUnion_finset hdisj hmeasset,
    ENNReal.toReal_sum (fun kl _ => measure_ne_top μ _),
    ← sum_antidiagonal_pD_pL n]
  refine Finset.sum_congr rfl fun kl _ => ?_
  rw [hindep.measure_inter_preimage_eq_mul {kl.1} {kl.2}
    (measurableSet_singleton _) (measurableSet_singleton _),
    ENNReal.toReal_mul]
  have hD' : (μ (D ⁻¹' {kl.1})).toReal = pD kl.1 :=
    hlawD kl.1
  have hL' : (μ (L ⁻¹' {kl.2})).toReal = pL kl.2 :=
    hlawL kl.2
  rw [hD', hL']

/-! ### Deterministic renewal inversion -/

/-- The renewal counting function: the greatest `k ≤ t` with
`s k ≤ t`. -/
noncomputable def renewalCount (s : ℕ → ℝ) (t : ℕ) : ℕ :=
  Nat.findGreatest (fun k => s k ≤ (t : ℝ)) t

/-- **Deterministic renewal inversion**: partial sums with
increments `≥ 1` and Cesàro limit `m > 0` have counting
function `N_t / t → 1/m`. -/
theorem renewal_count_tendsto (s : ℕ → ℝ) (m : ℝ)
    (hm : 0 < m) (hs0 : s 0 = 0)
    (hstep : ∀ k, s k + 1 ≤ s (k + 1))
    (hlim : Tendsto (fun k : ℕ => s k / k) atTop (𝓝 m)) :
    Tendsto (fun t : ℕ => (renewalCount s t : ℝ) / t)
      atTop (𝓝 m⁻¹) := by
  classical
  have hk_le : ∀ k : ℕ, (k : ℝ) ≤ s k := by
    intro k
    induction k with
    | zero => simp [hs0]
    | succ k ih =>
      have h := hstep k
      push_cast
      linarith
  have hs_le : ∀ t : ℕ, s (renewalCount s t) ≤ t := by
    intro t
    exact Nat.findGreatest_spec
      (P := fun k => s k ≤ (t : ℝ)) (Nat.zero_le t)
      (by rw [hs0]; positivity)
  have ht_lt : ∀ t : ℕ,
      (t : ℝ) < s (renewalCount s t + 1) := by
    intro t
    by_cases hle : renewalCount s t + 1 ≤ t
    · exact not_le.mp (Nat.findGreatest_is_greatest
        (Nat.lt_succ_self _) hle)
    · have h1 : t < renewalCount s t + 1 := by omega
      calc (t : ℝ) < ((renewalCount s t + 1 : ℕ) : ℝ) := by
            exact_mod_cast h1
        _ ≤ s (renewalCount s t + 1) := by
            have h2 := hk_le (renewalCount s t + 1)
            push_cast at h2 ⊢
            linarith
  have hN_atTop : Tendsto (fun t => renewalCount s t)
      atTop atTop := by
    refine tendsto_atTop.mpr fun K => ?_
    filter_upwards [eventually_ge_atTop K,
      eventually_ge_atTop ⌈s K⌉₊] with t ht1 ht2
    refine Nat.le_findGreatest ht1 ?_
    calc s K ≤ (⌈s K⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ t := by exact_mod_cast ht2
  have hcastN : Tendsto
      (fun t => ((renewalCount s t : ℕ) : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN_atTop
  have hNpos : ∀ᶠ t : ℕ in atTop,
      1 ≤ renewalCount s t :=
    hN_atTop.eventually_ge_atTop 1
  have hglim : Tendsto (fun t => s (renewalCount s t)
      / (renewalCount s t : ℝ)) atTop (𝓝 m) :=
    hlim.comp hN_atTop
  have hglim1 : Tendsto (fun t => s (renewalCount s t + 1)
      / ((renewalCount s t : ℝ) + 1)) atTop (𝓝 m) := by
    have h := hlim.comp
      ((tendsto_add_atTop_nat 1).comp hN_atTop)
    refine h.congr fun t => ?_
    simp only [Function.comp_apply]
    push_cast
    ring
  have hfrac : Tendsto (fun t =>
      ((renewalCount s t : ℝ) + 1)
        / (renewalCount s t : ℝ)) atTop (𝓝 1) := by
    have hinv : Tendsto
        (fun t => ((renewalCount s t : ℝ))⁻¹) atTop
        (𝓝 0) := hcastN.inv_tendsto_atTop
    have h1 : Tendsto (fun t =>
        1 + ((renewalCount s t : ℝ))⁻¹) atTop
        (𝓝 (1 + 0)) := tendsto_const_nhds.add hinv
    rw [add_zero] at h1
    refine Tendsto.congr' ?_ h1
    filter_upwards [hNpos] with t ht
    have hNne : ((renewalCount s t : ℝ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by omega)
    field_simp
  have hupper : Tendsto (fun t =>
      s (renewalCount s t + 1) / (renewalCount s t : ℝ))
      atTop (𝓝 m) := by
    have h := hglim1.mul hfrac
    rw [mul_one] at h
    refine Tendsto.congr' ?_ h
    filter_upwards [hNpos] with t ht
    have hNne : ((renewalCount s t : ℝ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by omega)
    field_simp
  have hsq : Tendsto (fun t : ℕ =>
      (t : ℝ) / (renewalCount s t : ℝ)) atTop (𝓝 m) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hglim hupper ?_ ?_
    · filter_upwards [hNpos] with t ht
      have hc : (0 : ℝ) < (renewalCount s t : ℝ) := by
        exact_mod_cast (by omega : 0 < renewalCount s t)
      gcongr
      exact hs_le t
    · filter_upwards [hNpos] with t ht
      have hc : (0 : ℝ) < (renewalCount s t : ℝ) := by
        exact_mod_cast (by omega : 0 < renewalCount s t)
      gcongr
      exact (ht_lt t).le
  have hinv := hsq.inv₀ (ne_of_gt hm)
  refine hinv.congr fun t => ?_
  rw [inv_div]

/-! ### The almost-sure renewal law -/

/-- **The almost-sure renewal law**: for iid interarrivals
with the completed-private law, `N_t / t → 4/11` almost
surely. -/
theorem completed_private_renewal_law
    {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (W : ℕ → Ω → ℕ) (hmeas : ∀ j, Measurable (W j))
    (hpos : ∀ j ω, 1 ≤ W j ω)
    (hindep : Pairwise fun i j => IndepFun (W i) (W j) μ)
    (hident : ∀ j, IdentDistrib (W j) (W 0) μ μ)
    (hlaw : ∀ n, (μ {ω | W 0 ω = n}).toReal = wpmf n) :
    ∀ᵐ ω ∂μ, Tendsto (fun t : ℕ =>
      (renewalCount (fun k => ∑ j ∈ Finset.range k,
        (W j ω : ℝ)) t : ℝ) / t) atTop (𝓝 (4 / 11)) := by
  classical
  have mcast : Measurable (fun n : ℕ => (n : ℝ)) :=
    measurable_from_top
  have hν : ∀ n : ℕ,
      (μ.map (W 0)) {n} = ENNReal.ofReal (wpmf n) := by
    intro n
    rw [Measure.map_apply (hmeas 0)
      (measurableSet_singleton n)]
    have hpre : W 0 ⁻¹' {n} = {ω | W 0 ω = n} := rfl
    rw [hpre, ← hlaw n,
      ENNReal.ofReal_toReal (measure_ne_top μ _)]
  have hcast : AEStronglyMeasurable (fun n : ℕ => (n : ℝ))
      (μ.map (W 0)) := mcast.aestronglyMeasurable
  have hintv : Integrable (fun n : ℕ => (n : ℝ))
      (μ.map (W 0)) := by
    refine ⟨hcast, ?_⟩
    rw [hasFiniteIntegral_def]
    have hlint : ∫⁻ n : ℕ, ‖(n : ℝ)‖ₑ ∂(μ.map (W 0))
        = ∑' n : ℕ, ENNReal.ofReal
            ((n : ℝ) * wpmf n) := by
      rw [lintegral_countable']
      refine tsum_congr fun n => ?_
      rw [hν n, Real.enorm_eq_ofReal (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
    rw [hlint, ← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (by positivity)
        (wpmf_nonneg n)) summable_id_mul_wpmf]
    exact ENNReal.ofReal_lt_top
  have hint : Integrable (fun ω => (W 0 ω : ℝ)) μ :=
    (integrable_map_measure hcast
      (hmeas 0).aemeasurable).mp hintv
  have hmean : ∫ ω, (W 0 ω : ℝ) ∂μ = 11 / 4 := by
    have h1 : ∫ ω, (W 0 ω : ℝ) ∂μ
        = ∫ n : ℕ, (n : ℝ) ∂(μ.map (W 0)) :=
      (integral_map (hmeas 0).aemeasurable hcast).symm
    rw [h1, integral_countable hintv]
    have h2 : ∀ n : ℕ,
        (μ.map (W 0)).real {n} • (n : ℝ)
        = (n : ℝ) * wpmf n := by
      intro n
      rw [Measure.real, hν n,
        ENNReal.toReal_ofReal (wpmf_nonneg n),
        smul_eq_mul, mul_comm]
    rw [tsum_congr h2, wpmf_mean]
  have hXindep : Pairwise (Function.onFun
      (fun f g => IndepFun f g μ)
      (fun j ω => (W j ω : ℝ))) := fun i j hij =>
    (hindep hij).comp mcast mcast
  have hXident : ∀ j, IdentDistrib
      (fun ω => (W j ω : ℝ))
      (fun ω => (W 0 ω : ℝ)) μ μ :=
    fun j => (hident j).comp mcast
  have hslln := strong_law_ae
    (fun j ω => (W j ω : ℝ)) hint hXindep hXident
  filter_upwards [hslln] with ω hω
  rw [hmean] at hω
  have hlim : Tendsto (fun k : ℕ =>
      (∑ j ∈ Finset.range k, (W j ω : ℝ)) / k) atTop
      (𝓝 (11 / 4)) := by
    refine hω.congr fun k => ?_
    rw [smul_eq_mul, inv_mul_eq_div]
  have hstep : ∀ k,
      (∑ j ∈ Finset.range k, (W j ω : ℝ)) + 1
      ≤ ∑ j ∈ Finset.range (k + 1), (W j ω : ℝ) := by
    intro k
    rw [Finset.sum_range_succ]
    have h1 : (1 : ℝ) ≤ (W k ω : ℝ) := by
      exact_mod_cast hpos k ω
    linarith
  have h := renewal_count_tendsto
    (fun k => ∑ j ∈ Finset.range k, (W j ω : ℝ))
    (11 / 4) (by norm_num) (by simp) hstep hlim
  rw [show ((11 : ℝ) / 4)⁻¹ = 4 / 11 from
    by norm_num] at h
  exact h

end CompletedPrivateRenewal
end NCG
