/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicGridInterpolation

/-!
# Sampling, aliasing and difference consistency on the periodic grid
  (`lem:supp-open-interpolation`, `eq:supp-open-sampling-estimate`,
  `eq:supp-open-difference-consistency`; emergent-spacetime manuscript, supplement)

Quantitative consistency between the periodic grid `(ℤ/N)³` (mesh `h = 1/N`) and the unit torus
`𝕋³ = UnitAddTorus (Fin 3)`, for the trigonometric interpolant `𝓘_h` (`interp`, signed frequency
cube), grid sampling `𝒮_h` (`sample`) and `𝒫_h = 𝓘_h 𝒮_h` (`proj`).  All Sobolev norms are
squared: `‖f‖²_{H^r} = trigSobSq r f = Σ_n W_r(n)|f̂(n)|²` with `W_r(n) = Σ_{|α|≤r} |(2πin)^α|²`, and
the grid norms `‖u‖²_{r,h} = sobSq r u`.  Every constant is independent of `N`.

* Weights: `bracket_pow_le_trigWeight`, `trigWeight_le_bracket` (`W_s ≍ ⟨n⟩^{2s}`),
  `summable_inv_bracket_sq` (`Σ_{ℤ³} ⟨n⟩^{-4} < ∞`), and Cauchy–Schwarz for series
  `norm_tsum_sq_le`; an `H^s` function, `s ≥ 2`, has summable coefficients
  (`summable_of_trigWeight`).
* `aliasEquiv`: the aliasing decomposition `ℤ³ ≃ (ℤ/N)³ × ℤ³`, `(k, ℓ) ↦ k̃ + Nℓ`.
* `hasSum_dft_sample` (**aliasing formula**): for continuous `u` with summable coefficients the
  grid coefficient of `𝒮_h u` at `k` is `Σ_ℓ û(k̃ + Nℓ)`.
* `sampling_error` (`eq:supp-open-sampling-estimate`, with the `h^j`, `H^{r+j}` refinement):
  for `r + j ≥ 2`, `‖𝒫_h u - u‖²_{H^r} ≤ C h^{2j} ‖u‖²_{H^{r+j}}`; `sampling_stable` (`r ≥ 2`):
  `‖𝒫_h u‖²_{H^r} ≤ C ‖u‖²_{H^r}`.
* `specD`, `hasDerivAt_interp_line`: `𝓘_h(specD_i u)` is the coordinate derivative `∂_i 𝓘_h u`.
* `difference_consistency_Dp`, `_Dm`, `_D0` (`eq:supp-open-difference-consistency`):
  `‖𝓘_h D u_h - ∂_i 𝓘_h u_h‖²_{H^r} ≤ (π²/4)^{r+2} h² ‖u_h‖²_{r+2,h}` for `D = D_i^±, D_i⁰`, from the
  symbol bound `|e^{iθ} - 1 - iθ| ≤ θ²` on `|θ| ≤ π` (`norm_exp_I_mul_sub_one_sub_le`).
* `trigSobSq_interp_mul_le`: uniform continuum product algebra on interpolants (`s ≥ 2`).
* `product_consistency` (`eq:supp-open-product-consistency`, `r ≥ 1`):
  `‖𝓘_h(u_h w_h) - (𝓘_h u_h)(𝓘_h w_h)‖²_{H^r} ≤ C h² ‖u_h‖²_{r+1,h} ‖w_h‖²_{r+1,h}`, via
  `𝓘_h(u_h w_h) = 𝒫_h[(𝓘_h u_h)(𝓘_h w_h)]`.

Scope: complex-valued fields and every `N ≥ 1` (the manuscript's odd grid is `N = 2m + 1`);
`u ∈ H^{r+j}` is rendered as a continuous function with `Σ W_{r+j}|û|² < ∞` (for `r + j ≥ 2`
continuity is the Sobolev embedding).  The analytic composition estimate
`eq:supp-open-composition-consistency` and the time-differentiated versions are not covered here.
-/

open Finset ComplexConjugate UnitAddTorus
open scoped BigOperators Real

namespace RenewalGeometry.PeriodicGridSobolev

namespace Sampling

open LatticeTorusPlancherel

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ### The Japanese bracket and the trigonometric weights -/

/-- The squared Japanese bracket `⟨n⟩² = 1 + Σ_i n_i²` of an integer frequency. -/
noncomputable def bracket (n : Fin 3 → ℤ) : ℝ := 1 + ∑ i, ((n i : ℤ) : ℝ) ^ 2

theorem one_le_bracket (n : Fin 3 → ℤ) : 1 ≤ bracket n := by
  unfold bracket
  have : 0 ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  linarith

theorem bracket_pos (n : Fin 3 → ℤ) : 0 < bracket n := lt_of_lt_of_le one_pos (one_le_bracket n)

theorem sq_le_bracket (n : Fin 3 → ℤ) (i : Fin 3) : ((n i : ℤ) : ℝ) ^ 2 ≤ bracket n := by
  unfold bracket
  have := single_le_sum (f := fun j => ((n j : ℤ) : ℝ) ^ 2) (fun _ _ => sq_nonneg _) (mem_univ i)
  linarith

theorem one_le_two_pi_sq : (1 : ℝ) ≤ (2 * π) ^ 2 := by
  have := Real.pi_gt_three
  nlinarith

theorem tsymSq_nonneg (α : Fin 3 → ℕ) (n : Fin 3 → ℤ) : 0 ≤ tsymSq α n := by
  unfold tsymSq; positivity

theorem trigWeight_nonneg (s : ℕ) (n : Fin 3 → ℤ) : 0 ≤ trigWeight s n :=
  sum_nonneg fun α _ => tsymSq_nonneg α n

theorem tsymSq_le (α : Fin 3 → ℕ) (n : Fin 3 → ℤ) :
    tsymSq α n ≤ ((2 * π) ^ 2 * bracket n) ^ deg α := by
  have hc : ∀ i, (2 * π * (n i : ℝ)) ^ 2 ≤ (2 * π) ^ 2 * bracket n := by
    intro i
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (sq_le_bracket n i) (sq_nonneg _)
  have hB0 : 0 ≤ (2 * π) ^ 2 * bracket n := mul_nonneg (sq_nonneg _) (bracket_pos n).le
  rw [tsymSq, deg, pow_add, pow_add]
  exact mul_le_mul (mul_le_mul (pow_le_pow_left₀ (sq_nonneg _) (hc 0) _)
    (pow_le_pow_left₀ (sq_nonneg _) (hc 1) _) (by positivity) (pow_nonneg hB0 _))
    (pow_le_pow_left₀ (sq_nonneg _) (hc 2) _) (by positivity)
    (mul_nonneg (pow_nonneg hB0 _) (pow_nonneg hB0 _))

/-- Upper comparison `W_s(n) ≤ #{|α| ≤ s} ((2π)² ⟨n⟩²)^s`. -/
theorem trigWeight_le_bracket (s : ℕ) (n : Fin 3 → ℤ) :
    trigWeight s n ≤ ((multiIndices s).card : ℝ) * ((2 * π) ^ 2 * bracket n) ^ s := by
  have hB : 1 ≤ (2 * π) ^ 2 * bracket n := by
    have := one_le_bracket n
    nlinarith [one_le_two_pi_sq]
  unfold trigWeight
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun α hα => (tsymSq_le α n).trans ?_
  exact pow_le_pow_right₀ hB (mem_multiIndices.mp hα)

theorem deg_single (i : Fin 3) (s : ℕ) : deg (Pi.single i s : Fin 3 → ℕ) = s := by
  fin_cases i <;> simp [deg]

theorem tsymSq_single (i : Fin 3) (s : ℕ) (n : Fin 3 → ℤ) :
    tsymSq (Pi.single i s) n = ((2 * π * n i) ^ 2) ^ s := by
  fin_cases i <;> simp [tsymSq]

theorem tsymSq_zero (n : Fin 3 → ℤ) : tsymSq 0 n = 1 := by simp [tsymSq]

theorem tsymSq_le_trigWeight {s : ℕ} {α : Fin 3 → ℕ} (h : deg α ≤ s) (n : Fin 3 → ℤ) :
    tsymSq α n ≤ trigWeight s n :=
  single_le_sum (f := fun β => tsymSq β n) (fun β _ => tsymSq_nonneg β n)
    (mem_multiIndices.mpr h)

theorem one_le_trigWeight (s : ℕ) (n : Fin 3 → ℤ) : 1 ≤ trigWeight s n := by
  have := tsymSq_le_trigWeight (s := s) (α := 0) (by simp [deg]) n
  rwa [tsymSq_zero] at this

theorem trigWeight_pos (s : ℕ) (n : Fin 3 → ℤ) : 0 < trigWeight s n :=
  lt_of_lt_of_le one_pos (one_le_trigWeight s n)

theorem coord_pow_le_trigWeight (s : ℕ) (n : Fin 3 → ℤ) (i : Fin 3) :
    (((n i : ℤ) : ℝ) ^ 2) ^ s ≤ trigWeight s n := by
  have h := tsymSq_le_trigWeight (s := s) (α := Pi.single i s) (by rw [deg_single]) n
  rw [tsymSq_single] at h
  refine le_trans ?_ h
  refine pow_le_pow_left₀ (sq_nonneg _) ?_ _
  rw [mul_pow]
  have := sq_nonneg ((n i : ℤ) : ℝ)
  nlinarith [one_le_two_pi_sq]

/-- Lower comparison `⟨n⟩^{2s} ≤ 4^s W_s(n)`. -/
theorem bracket_pow_le_trigWeight (s : ℕ) (n : Fin 3 → ℤ) :
    bracket n ^ s ≤ 4 ^ s * trigWeight s n := by
  set a : ℝ := ((n 0 : ℤ) : ℝ) ^ 2
  set b : ℝ := ((n 1 : ℤ) : ℝ) ^ 2
  set c : ℝ := ((n 2 : ℤ) : ℝ) ^ 2
  set m : ℝ := max 1 (max a (max b c))
  have hbr : bracket n = 1 + a + b + c := by
    simp [bracket, Fin.sum_univ_three, a, b, c]; ring
  have hm1 : 1 ≤ m := le_max_left _ _
  have ha : a ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
  have hb : b ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hc : c ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hle : bracket n ≤ 4 * m := by rw [hbr]; linarith
  have hmT : m ^ s ≤ trigWeight s n := by
    rcases max_choice 1 (max a (max b c)) with h | h
    · rw [show m = 1 from h, one_pow]; exact one_le_trigWeight s n
    · rw [show m = _ from h]
      rcases max_choice a (max b c) with h' | h'
      · rw [h']; exact coord_pow_le_trigWeight s n 0
      · rw [h']
        rcases max_choice b c with h'' | h''
        · rw [h'']; exact coord_pow_le_trigWeight s n 1
        · rw [h'']; exact coord_pow_le_trigWeight s n 2
  calc bracket n ^ s ≤ (4 * m) ^ s :=
        pow_le_pow_left₀ (le_trans zero_le_one (one_le_bracket n)) hle s
    _ = 4 ^ s * m ^ s := mul_pow _ _ _
    _ ≤ 4 ^ s * trigWeight s n := by gcongr

/-! ### Summability over `ℤ³` -/

/-- `(1 + 16|n|²)` on integer vectors. -/
noncomputable def zWeight (n : Fin 3 → ℤ) : ℝ := 1 + 16 * ∑ i, ((n i : ℤ) : ℝ) ^ 2

theorem one_le_zWeight (n : Fin 3 → ℤ) : 1 ≤ zWeight n := by
  unfold zWeight
  have : 0 ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  linarith

theorem inv_zWeight_sq_le (n : Fin 3 → ℤ) : (zWeight n ^ 2)⁻¹ ≤ ∏ i, w1d (n i) := by
  have hS := one_le_zWeight n
  have hai : ∀ i, (1 + 16 * ((n i : ℤ) : ℝ) ^ 2) ^ ((2 : ℝ) / 3) ≤
      zWeight n ^ ((2 : ℝ) / 3) := by
    intro i
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    unfold zWeight
    have : ((n i : ℤ) : ℝ) ^ 2 ≤ ∑ j, ((n j : ℤ) : ℝ) ^ 2 :=
      single_le_sum (f := fun j => ((n j : ℤ) : ℝ) ^ 2) (fun _ _ => sq_nonneg _) (mem_univ i)
    linarith
  unfold w1d
  rw [prod_inv_distrib]
  apply inv_anti₀ (by positivity)
  calc ∏ i, (1 + 16 * ((n i : ℤ) : ℝ) ^ 2) ^ ((2 : ℝ) / 3)
      ≤ ∏ _i : Fin 3, zWeight n ^ ((2 : ℝ) / 3) :=
        prod_le_prod (fun _ _ => by positivity) (fun i _ => hai i)
    _ = zWeight n ^ 2 := by
        rw [prod_const, card_univ, Fintype.card_fin, ← Real.rpow_mul_natCast (by linarith)]
        norm_num

theorem sum_prod_w1d_le (s : Finset (Fin 3 → ℤ)) :
    ∑ n ∈ s, ∏ i, w1d (n i) ≤ c1 ^ 3 := by
  classical
  set T : Fin 3 → Finset ℤ := fun i => s.image (fun n => n i)
  have hsub : s ⊆ Fintype.piFinset T := by
    intro n hn
    rw [Fintype.mem_piFinset]
    intro i
    exact mem_image_of_mem _ hn
  calc ∑ n ∈ s, ∏ i, w1d (n i) ≤ ∑ n ∈ Fintype.piFinset T, ∏ i, w1d (n i) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => prod_nonneg fun _ _ => w1d_nonneg _)
    _ = ∏ i, ∑ t ∈ T i, w1d t := (Finset.prod_univ_sum T (fun _ t => w1d t)).symm
    _ ≤ ∏ _i : Fin 3, c1 := prod_le_prod (fun _ _ => sum_nonneg fun _ _ => w1d_nonneg _)
        (fun i _ => summable_w1d.sum_le_tsum _ (fun _ _ => w1d_nonneg _))
    _ = c1 ^ 3 := by simp

theorem summable_prod_w1d : Summable fun n : Fin 3 → ℤ => ∏ i, w1d (n i) :=
  summable_of_sum_le (fun _ => prod_nonneg fun _ _ => w1d_nonneg _) sum_prod_w1d_le

theorem tsum_prod_w1d_le : ∑' n : Fin 3 → ℤ, ∏ i, w1d (n i) ≤ c1 ^ 3 :=
  tsum_le_of_sum_le' (by have := c1_nonneg; positivity) sum_prod_w1d_le

theorem inv_bracket_sq_le (n : Fin 3 → ℤ) : (bracket n ^ 2)⁻¹ ≤ 256 * ∏ i, w1d (n i) := by
  have h1 : zWeight n ≤ 16 * bracket n := by
    unfold zWeight bracket; linarith
  have hz := one_le_zWeight n
  have hb := one_le_bracket n
  calc (bracket n ^ 2)⁻¹ = 256 * ((16 * bracket n) ^ 2)⁻¹ := by
        rw [mul_pow]; field_simp; norm_num
    _ ≤ 256 * (zWeight n ^ 2)⁻¹ := by
        gcongr
    _ ≤ 256 * ∏ i, w1d (n i) := by gcongr; exact inv_zWeight_sq_le n

/-- `Σ_{n ∈ ℤ³} ⟨n⟩^{-4}` converges. -/
theorem summable_inv_bracket_sq : Summable fun n : Fin 3 → ℤ => (bracket n ^ 2)⁻¹ :=
  Summable.of_nonneg_of_le (fun n => by have := bracket_pos n; positivity)
    inv_bracket_sq_le (summable_prod_w1d.mul_left 256)

theorem tsum_inv_bracket_sq_le : ∑' n : Fin 3 → ℤ, (bracket n ^ 2)⁻¹ ≤ 256 * c1 ^ 3 := by
  calc ∑' n : Fin 3 → ℤ, (bracket n ^ 2)⁻¹ ≤ ∑' n : Fin 3 → ℤ, 256 * ∏ i, w1d (n i) :=
        Summable.tsum_le_tsum inv_bracket_sq_le summable_inv_bracket_sq
          (summable_prod_w1d.mul_left 256)
    _ = 256 * ∑' n : Fin 3 → ℤ, ∏ i, w1d (n i) := tsum_mul_left
    _ ≤ 256 * c1 ^ 3 := by gcongr; exact tsum_prod_w1d_le

/-! ### Cauchy–Schwarz for weighted series -/

/-- Cauchy–Schwarz for series: if `‖a_i‖² ≤ b_i c_i` with `b, c ≥ 0` summable, then `a` is
summable and `‖Σ a‖² ≤ (Σ b)(Σ c)`. -/
theorem norm_tsum_sq_le {ι : Type*} (a : ι → ℂ) (b c : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i, 0 ≤ c i) (habc : ∀ i, ‖a i‖ ^ 2 ≤ b i * c i) (sb : Summable b)
    (sc : Summable c) : Summable a ∧ ‖∑' i, a i‖ ^ 2 ≤ (∑' i, b i) * ∑' i, c i := by
  have hpt : ∀ i, ‖a i‖ ≤ Real.sqrt (b i) * Real.sqrt (c i) := by
    intro i
    rw [← Real.sqrt_mul (hb i)]
    exact Real.le_sqrt_of_sq_le (habc i)
  have hpt2 : ∀ i, ‖a i‖ ≤ (b i + c i) / 2 := by
    intro i
    refine (hpt i).trans ?_
    have := Real.sq_sqrt (hb i); have := Real.sq_sqrt (hc i)
    nlinarith [sq_nonneg (Real.sqrt (b i) - Real.sqrt (c i))]
  have sa : Summable fun i => ‖a i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hpt2 ((sb.add sc).div_const 2)
  refine ⟨sa.of_norm, ?_⟩
  set K := Real.sqrt (∑' i, b i) * Real.sqrt (∑' i, c i)
  have hK : 0 ≤ K := by positivity
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, ‖a i‖ ≤ K := by
    intro s
    calc ∑ i ∈ s, ‖a i‖ ≤ ∑ i ∈ s, Real.sqrt (b i) * Real.sqrt (c i) :=
          sum_le_sum fun i _ => hpt i
      _ ≤ Real.sqrt (∑ i ∈ s, b i) * Real.sqrt (∑ i ∈ s, c i) :=
          Real.sum_sqrt_mul_sqrt_le s hb hc
      _ ≤ K := mul_le_mul (Real.sqrt_le_sqrt (sb.sum_le_tsum s (fun i _ => hb i)))
          (Real.sqrt_le_sqrt (sc.sum_le_tsum s (fun i _ => hc i))) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
  have h1 : ‖∑' i, a i‖ ≤ K :=
    (norm_tsum_le_tsum_norm sa).trans (tsum_le_of_sum_le' hK hfin)
  have h2 : K ^ 2 = (∑' i, b i) * ∑' i, c i := by
    rw [mul_pow, Real.sq_sqrt (tsum_nonneg hb), Real.sq_sqrt (tsum_nonneg hc)]
  rw [← h2]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2


/-! ### The aliasing decomposition `ℤ³ ≃ (ℤ/N)³ × ℤ³` -/

variable {N : ℕ} [NeZero N]

/-- An integer frequency reduced modulo `N`. -/
def zcast (N : ℕ) (n : Fin 3 → ℤ) : Grid N := fun i => (n i : ZMod N)

theorem zcast_freq_add (k : Grid N) (ℓ : Fin 3 → ℤ) :
    zcast N (fun i => freq i k + (N : ℤ) * ℓ i) = k := by
  funext i
  simp only [zcast, freq]
  push_cast
  simp

theorem dvd_sub_freq_zcast (n : Fin 3 → ℤ) (i : Fin 3) :
    (N : ℤ) ∣ n i - freq i (zcast N n) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [zcast, freq]
  push_cast
  simp

/-- The aliasing decomposition: every integer frequency is uniquely `k̃ + N ℓ` with `k̃` in the
signed frequency cube of the grid frequency `k` and `ℓ ∈ ℤ³`. -/
def aliasEquiv (N : ℕ) [NeZero N] : Grid N × (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) where
  toFun p := fun i => freq i p.1 + (N : ℤ) * p.2 i
  invFun n := (zcast N n, fun i => (n i - freq i (zcast N n)) / N)
  left_inv := by
    rintro ⟨k, ℓ⟩
    have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
    refine Prod.ext (zcast_freq_add k ℓ) (funext fun i => ?_)
    simp only
    rw [zcast_freq_add k ℓ, add_sub_cancel_left, Int.mul_ediv_cancel_left _ hN]
  right_inv := by
    intro n
    funext i
    simp only
    rw [Int.mul_ediv_cancel' (dvd_sub_freq_zcast n i), add_sub_cancel]

theorem aliasEquiv_apply (k : Grid N) (ℓ : Fin 3 → ℤ) (i : Fin 3) :
    aliasEquiv N (k, ℓ) i = freq i k + (N : ℤ) * ℓ i := rfl

theorem aliasEquiv_zero (k : Grid N) : aliasEquiv N (k, 0) = freqVec k := by
  funext i; simp [aliasEquiv_apply, freqVec]

theorem zcast_aliasEquiv (k : Grid N) (ℓ : Fin 3 → ℤ) : zcast N (aliasEquiv N (k, ℓ)) = k :=
  zcast_freq_add k ℓ

theorem freqVec_eq_aliasEquiv_iff (k k₁ : Grid N) (ℓ : Fin 3 → ℤ) :
    freqVec k₁ = aliasEquiv N (k, ℓ) ↔ k₁ = k ∧ ℓ = 0 := by
  rw [← aliasEquiv_zero, (aliasEquiv N).injective.eq_iff, Prod.mk.injEq]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩

/-- Summing over the aliasing decomposition. -/
theorem sum_tsum_aliasEquiv {H : (Fin 3 → ℤ) → ℝ} (hH : Summable H) :
    ∑ k : Grid N, ∑' ℓ, H (aliasEquiv N (k, ℓ)) = ∑' n, H n := by
  have hs : Summable fun p : Grid N × (Fin 3 → ℤ) => H (aliasEquiv N p) :=
    (Equiv.summable_iff (aliasEquiv N)).mpr hH
  rw [← Equiv.tsum_eq (aliasEquiv N) H, hs.tsum_prod' (fun k => hs.prod_factor k), tsum_fintype]

theorem summable_comp_aliasEquiv {H : (Fin 3 → ℤ) → ℝ} (hH : Summable H) (k : Grid N) :
    Summable fun ℓ => H (aliasEquiv N (k, ℓ)) :=
  ((Equiv.summable_iff (aliasEquiv N)).mpr hH).prod_factor k

/-! ### Grid sampling and the aliasing formula -/

theorem norm_latticeChar (k x : Grid N) : ‖latticeChar k x‖ = 1 := by
  unfold latticeChar
  rw [norm_prod]
  exact Finset.prod_eq_one fun i _ => by rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

theorem mFourier_samplePt_eq (n : Fin 3 → ℤ) (x : Grid N) :
    mFourier n (samplePt x) = latticeChar (zcast N n) x := by
  simp only [mFourier, ContinuousMap.coe_mk, latticeChar, samplePt, zcast]
  refine prod_congr rfl fun i _ => ?_
  rw [fourier_coe_apply]
  have e : (n i : ZMod N) * x i = (((n i * ((x i).val : ℤ) : ℤ) : ZMod N)) := by
    push_cast
    simp
  rw [e, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- Orthogonality of the grid characters: `dft(e_{k₁}) = δ_{k₁ k}`. -/
theorem dft_latticeChar (k₁ k : Grid N) :
    dft (fun x => latticeChar k₁ x) k = if k₁ = k then 1 else 0 := by
  have hn : ((N : ℂ) ^ 3) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne N))
  unfold dft
  have hrow : ∀ x : Grid N, conj (latticeChar k x) • latticeChar k₁ x =
      latticeChar x (k₁ - k) := by
    intro x
    rw [smul_eq_mul, latticeChar_sub_right x k₁ k, latticeChar_comm x k₁, latticeChar_comm x k]
    ring
  simp only [hrow]
  have hsum := sum_latticeChar (d := 3) (n := N) (k₁ - k)
  have hcomm : ∑ x : Grid N, latticeChar x (k₁ - k) = ∑ ℓ : Grid N, latticeChar ℓ (k₁ - k) := rfl
  rw [hcomm, hsum]
  by_cases h : k₁ = k
  · subst h; simp [hn]
  · simp [sub_ne_zero.mpr h, h]

/-- Grid sampling `𝒮_h u(x) = u(x/N)`. -/
noncomputable def sample (N : ℕ) [NeZero N] (f : UnitAddTorus (Fin 3) → ℂ) : Grid N → ℂ :=
  fun x => f (samplePt x)

/-- The sampling projector `𝒫_h = 𝓘_h 𝒮_h`. -/
noncomputable def proj (N : ℕ) [NeZero N] (f : UnitAddTorus (Fin 3) → ℂ) :
    C(UnitAddTorus (Fin 3), ℂ) :=
  interp (sample N f)

/-- **Aliasing formula.**  For a continuous `u` with summable Fourier coefficients, the grid
Fourier coefficient of the samples at `k` is `Σ_{ℓ ∈ ℤ³} û(k̃ + Nℓ)`. -/
theorem hasSum_dft_sample (f : C(UnitAddTorus (Fin 3), ℂ)) (hf : Summable (mFourierCoeff ⇑f))
    (k : Grid N) :
    HasSum (fun ℓ => mFourierCoeff ⇑f (aliasEquiv N (k, ℓ))) (dft (sample N ⇑f) k) := by
  have hs : ∀ x, sample N f x = ∑' n, mFourierCoeff f n * latticeChar (zcast N n) x := by
    intro x
    show f (samplePt x) = _
    rw [← (hasSum_mFourier_series_apply_of_summable hf (samplePt x)).tsum_eq]
    simp only [smul_eq_mul, mFourier_samplePt_eq]
  have hsumm : ∀ x : Grid N, Summable fun n => conj (latticeChar k x) *
      (mFourierCoeff f n * latticeChar (zcast N n) x) := by
    intro x
    refine Summable.of_norm_bounded hf.norm (fun n => ?_)
    rw [norm_mul, norm_mul]
    have h1 : ‖conj (latticeChar k x)‖ = 1 := by
      rw [Complex.norm_conj]; exact norm_latticeChar k x
    have h2 : ‖latticeChar (zcast N n) x‖ = 1 := norm_latticeChar _ x
    rw [h1, h2]; simp
  have hdft : dft (sample N f) k =
      ∑' n, mFourierCoeff f n * (if zcast N n = k then 1 else 0) := by
    simp_rw [← dft_latticeChar]
    unfold dft
    simp only [hs, smul_eq_mul]
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun x _ => hsumm x), ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [Finset.mul_sum]
    exact sum_congr rfl fun x _ => by ring
  set F : (Fin 3 → ℤ) → ℂ := fun n => mFourierCoeff f n * (if zcast N n = k then 1 else 0)
  have hsupp : Function.support F ⊆ Set.range fun ℓ => aliasEquiv N (k, ℓ) := by
    intro n hn
    have hk : zcast N n = k := by
      by_contra h
      exact hn (by simp [F, h])
    refine ⟨((aliasEquiv N).symm n).2, ?_⟩
    have : (aliasEquiv N).symm n = (k, ((aliasEquiv N).symm n).2) := by
      refine Prod.ext ?_ rfl
      rw [← hk]; rfl
    simp only
    rw [← this, Equiv.apply_symm_apply]
  have hinj : Function.Injective fun ℓ => aliasEquiv N (k, ℓ) := by
    intro ℓ ℓ₁ h
    have := (aliasEquiv N).injective h
    exact (Prod.mk.inj this).2
  have heq : ∑' ℓ, F (aliasEquiv N (k, ℓ)) = ∑' n, F n := hinj.tsum_eq hsupp
  have hF : ∀ ℓ, F (aliasEquiv N (k, ℓ)) = mFourierCoeff f (aliasEquiv N (k, ℓ)) := by
    intro ℓ; simp [F, zcast_aliasEquiv]
  have hsum : Summable fun ℓ => mFourierCoeff ⇑f (aliasEquiv N (k, ℓ)) :=
    (((Equiv.summable_iff (aliasEquiv N)).mpr hf).prod_factor k)
  rw [hsum.hasSum_iff, hdft, ← heq]
  exact tsum_congr fun ℓ => (hF ℓ).symm

/-- Fourier coefficients of `𝒫_h u` in the aliasing coordinates. -/
theorem mFourierCoeff_proj_aliasEquiv (f : UnitAddTorus (Fin 3) → ℂ) (k : Grid N)
    (ℓ : Fin 3 → ℤ) :
    mFourierCoeff ⇑(proj N f) (aliasEquiv N (k, ℓ)) =
      if ℓ = 0 then dft (sample N f) k else 0 := by
  rw [proj, mFourierCoeff_interp]
  simp_rw [freqVec_eq_aliasEquiv_iff]
  by_cases hℓ : ℓ = 0
  · simp [hℓ]
  · simp [hℓ]

/-- Fourier coefficients are additive on continuous functions. -/
theorem mFourierCoeff_sub (F G : C(UnitAddTorus (Fin 3), ℂ)) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(F - G) n = mFourierCoeff ⇑F n - mFourierCoeff ⇑G n := by
  rw [← mFourierCoeff_toLp, ← mFourierCoeff_toLp F, ← mFourierCoeff_toLp G,
    ← mFourierBasis_repr, ← mFourierBasis_repr, ← mFourierBasis_repr, map_sub, map_sub]
  rfl


/-! ### Weight bounds along the aliasing decomposition -/

theorem sq_le_sq_freq_add (k : Grid N) (ℓ : Fin 3 → ℤ) (i : Fin 3) :
    ((N : ℝ) ^ 2 / 4) * ((ℓ i : ℤ) : ℝ) ^ 2 ≤ ((freq i k : ℝ) + N * ℓ i) ^ 2 := by
  have hk := abs_freq_le i k
  set x : ℝ := ((freq i k : ℤ) : ℝ)
  set L : ℝ := ((ℓ i : ℤ) : ℝ)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rcases eq_or_ne (ℓ i) 0 with h0 | h0
  · have : L = 0 := by simp [L, h0]
    rw [this]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    positivity
  · have hL : 1 ≤ |L| := by
      have : (1 : ℤ) ≤ |ℓ i| := Int.one_le_abs h0
      simp only [L]; exact_mod_cast this
    have htri : |(N : ℝ) * L| ≤ |x + N * L| + |x| := by
      have := abs_sub (x + N * L) x
      simpa using this
    rw [abs_mul, abs_of_nonneg hN] at htri
    have hge : (N : ℝ) * |L| / 2 ≤ |x + N * L| := by nlinarith
    have h0' : 0 ≤ (N : ℝ) * |L| / 2 := by positivity
    calc ((N : ℝ) ^ 2 / 4) * L ^ 2 = ((N : ℝ) * |L| / 2) ^ 2 := by rw [← sq_abs L]; ring
      _ ≤ |x + N * L| ^ 2 := pow_le_pow_left₀ h0' hge 2
      _ = (x + N * L) ^ 2 := sq_abs _

theorem one_le_sum_sq_of_ne_zero {ℓ : Fin 3 → ℤ} (hℓ : ℓ ≠ 0) :
    1 ≤ ∑ i, ((ℓ i : ℤ) : ℝ) ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, ℓ i ≠ 0 := by
    by_contra h; push Not at h; exact hℓ (funext h)
  have h1 : (1 : ℝ) ≤ ((ℓ i : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ ℓ i ^ 2 := by
      have := Int.one_le_abs hi
      nlinarith [sq_abs (ℓ i)]
    exact_mod_cast this
  exact h1.trans (single_le_sum (f := fun j => ((ℓ j : ℤ) : ℝ) ^ 2) (fun _ _ => sq_nonneg _)
    (mem_univ i))

theorem bracket_aliasEquiv_ge (k : Grid N) (ℓ : Fin 3 → ℤ) :
    ((N : ℝ) ^ 2 / 4) * ∑ i, ((ℓ i : ℤ) : ℝ) ^ 2 ≤ bracket (aliasEquiv N (k, ℓ)) := by
  unfold bracket
  rw [mul_sum]
  have : ∑ i, ((N : ℝ) ^ 2 / 4) * ((ℓ i : ℤ) : ℝ) ^ 2 ≤
      ∑ i, (((aliasEquiv N (k, ℓ)) i : ℤ) : ℝ) ^ 2 := by
    refine sum_le_sum fun i _ => ?_
    rw [aliasEquiv_apply]
    push_cast
    exact sq_le_sq_freq_add k ℓ i
  linarith

theorem bracket_aliasEquiv_ge_bracket (k : Grid N) {ℓ : Fin 3 → ℤ} (hℓ : ℓ ≠ 0) :
    ((N : ℝ) ^ 2 / 8) * bracket ℓ ≤ bracket (aliasEquiv N (k, ℓ)) := by
  have h1 := one_le_sum_sq_of_ne_zero hℓ
  have h2 := bracket_aliasEquiv_ge k ℓ
  have hN : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
  unfold bracket at *
  nlinarith

theorem bracket_aliasEquiv_ge_sq (k : Grid N) {ℓ : Fin 3 → ℤ} (hℓ : ℓ ≠ 0) :
    (N : ℝ) ^ 2 / 4 ≤ bracket (aliasEquiv N (k, ℓ)) := by
  have h1 := one_le_sum_sq_of_ne_zero hℓ
  have h2 := bracket_aliasEquiv_ge k ℓ
  have hN : 0 ≤ (N : ℝ) ^ 2 / 4 := by positivity
  nlinarith

theorem bracket_freqVec_le (k : Grid N) : bracket (freqVec k) ≤ 2 * (N : ℝ) ^ 2 := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hi : ∀ i, ((freqVec k i : ℤ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 / 4 := by
    intro i
    have := abs_freq_le i k
    have h0 : 0 ≤ |(freq i k : ℝ)| := abs_nonneg _
    have : |(freq i k : ℝ)| ≤ N / 2 := by linarith
    calc ((freqVec k i : ℤ) : ℝ) ^ 2 = |(freq i k : ℝ)| ^ 2 := by simp [freqVec]
      _ ≤ (N / 2 : ℝ) ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = (N : ℝ) ^ 2 / 4 := by ring
  unfold bracket
  rw [Fin.sum_univ_three]
  have := hi 0; have := hi 1; have := hi 2
  nlinarith

/-- Weight on the signed cube: `W_r(k̃) ≤ C_r N^{2r}`. -/
theorem trigWeight_freqVec_le (r : ℕ) (k : Grid N) :
    trigWeight r (freqVec k) ≤
      ((multiIndices r).card : ℝ) * (8 * π ^ 2) ^ r * ((N : ℝ) ^ 2) ^ r := by
  have hb : (2 * π) ^ 2 * bracket (freqVec k) ≤ 8 * π ^ 2 * (N : ℝ) ^ 2 := by
    calc (2 * π) ^ 2 * bracket (freqVec k) ≤ (2 * π) ^ 2 * (2 * (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (bracket_freqVec_le k) (sq_nonneg _)
      _ = 8 * π ^ 2 * (N : ℝ) ^ 2 := by ring
  calc trigWeight r (freqVec k)
      ≤ ((multiIndices r).card : ℝ) * ((2 * π) ^ 2 * bracket (freqVec k)) ^ r :=
        trigWeight_le_bracket r (freqVec k)
    _ ≤ ((multiIndices r).card : ℝ) * (8 * π ^ 2 * (N : ℝ) ^ 2) ^ r :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀
          (mul_nonneg (sq_nonneg _) (bracket_pos _).le) hb r) (Nat.cast_nonneg _)
    _ = _ := by rw [mul_pow]; ring

/-- Folded weights: for `s ≥ 2` and `ℓ ≠ 0`,
`W_s(k̃ + Nℓ)⁻¹ ≤ 32^s N^{-2s} ⟨ℓ⟩^{-4}`. -/
theorem inv_trigWeight_aliasEquiv_le {s : ℕ} (hs : 2 ≤ s) (k : Grid N) {ℓ : Fin 3 → ℤ}
    (hℓ : ℓ ≠ 0) :
    (trigWeight s (aliasEquiv N (k, ℓ)))⁻¹ ≤
      32 ^ s * (((N : ℝ) ^ 2) ^ s)⁻¹ * (bracket ℓ ^ 2)⁻¹ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hX : 0 < (N : ℝ) ^ 2 := by positivity
  set B := bracket (aliasEquiv N (k, ℓ))
  set b := bracket ℓ
  have hb1 := one_le_bracket ℓ
  have hB := bracket_aliasEquiv_ge_bracket k hℓ
  have hW := bracket_pow_le_trigWeight s (aliasEquiv N (k, ℓ))
  have hWpos := trigWeight_pos s (aliasEquiv N (k, ℓ))
  have hbpow : b ^ 2 ≤ b ^ s := pow_le_pow_right₀ hb1 hs
  have hlow : ((N : ℝ) ^ 2 / 8) ^ s * b ^ 2 ≤ B ^ s := by
    calc ((N : ℝ) ^ 2 / 8) ^ s * b ^ 2 ≤ ((N : ℝ) ^ 2 / 8) ^ s * b ^ s := by gcongr
      _ = ((N : ℝ) ^ 2 / 8 * b) ^ s := (mul_pow _ _ _).symm
      _ ≤ B ^ s := pow_le_pow_left₀ (by positivity) hB s
  have hfin : ((N : ℝ) ^ 2 / 8) ^ s * b ^ 2 ≤ 4 ^ s * trigWeight s (aliasEquiv N (k, ℓ)) :=
    hlow.trans hW
  rw [inv_le_comm₀ hWpos (by positivity)]
  rw [mul_inv, mul_inv, inv_inv, inv_inv]
  have e : ((32 : ℝ) ^ s)⁻¹ * ((N : ℝ) ^ 2) ^ s * b ^ 2 =
      (((N : ℝ) ^ 2 / 8) ^ s * b ^ 2) / 4 ^ s := by
    rw [div_pow, show (32 : ℝ) = 4 * 8 by norm_num, mul_pow]
    field_simp
  rw [e, div_le_iff₀ (by positivity)]
  linarith

/-- Tail weights: for `ℓ ≠ 0`, `W_r(k̃ + Nℓ) ≤ C N^{-2j} W_{r+j}(k̃ + Nℓ)`. -/
theorem trigWeight_aliasEquiv_tail_le (r j : ℕ) (k : Grid N) {ℓ : Fin 3 → ℤ} (hℓ : ℓ ≠ 0) :
    trigWeight r (aliasEquiv N (k, ℓ)) ≤
      ((multiIndices r).card : ℝ) * ((2 * π) ^ 2) ^ r * 4 ^ (r + j) * 4 ^ j *
        (((N : ℝ) ^ 2) ^ j)⁻¹ * trigWeight (r + j) (aliasEquiv N (k, ℓ)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set n := aliasEquiv N (k, ℓ)
  set B := bracket n
  have hB0 : 0 < B := bracket_pos n
  have hBN : (N : ℝ) ^ 2 / 4 ≤ B := bracket_aliasEquiv_ge_sq k hℓ
  have h1 := trigWeight_le_bracket r n
  have h2 := bracket_pow_le_trigWeight (r + j) n
  have hBj : ((N : ℝ) ^ 2 / 4) ^ j ≤ B ^ j := pow_le_pow_left₀ (by positivity) hBN j
  have hBr : B ^ r = B ^ (r + j) / B ^ j := by
    rw [pow_add]; field_simp
  have hBr' : B ^ r ≤ 4 ^ (r + j) * trigWeight (r + j) n * (4 ^ j * (((N : ℝ) ^ 2) ^ j)⁻¹) := by
    rw [hBr, div_eq_mul_inv]
    refine mul_le_mul h2 ?_ (inv_pos.mpr (pow_pos hB0 j)).le
      (mul_nonneg (by positivity) (trigWeight_nonneg _ _))
    have e : (((N : ℝ) ^ 2 / 4) ^ j)⁻¹ = 4 ^ j * (((N : ℝ) ^ 2) ^ j)⁻¹ := by
      rw [div_pow]; field_simp
    exact (inv_anti₀ (by positivity) hBj).trans (le_of_eq e)
  calc trigWeight r n ≤ ((multiIndices r).card : ℝ) * ((2 * π) ^ 2 * B) ^ r := h1
    _ = ((multiIndices r).card : ℝ) * ((2 * π) ^ 2) ^ r * B ^ r := by rw [mul_pow]; ring
    _ ≤ ((multiIndices r).card : ℝ) * ((2 * π) ^ 2) ^ r *
          (4 ^ (r + j) * trigWeight (r + j) n * (4 ^ j * (((N : ℝ) ^ 2) ^ j)⁻¹)) := by
        gcongr
    _ = _ := by ring

/-- `Σ_n W_s(n)⁻¹ < ∞` for `s ≥ 2`. -/
theorem inv_trigWeight_le (s : ℕ) (hs : 2 ≤ s) (n : Fin 3 → ℤ) :
    (trigWeight s n)⁻¹ ≤ 4 ^ s * (bracket n ^ 2)⁻¹ := by
  have hW := bracket_pow_le_trigWeight s n
  have hb := one_le_bracket n
  have hWpos := trigWeight_pos s n
  have h2 : bracket n ^ 2 ≤ bracket n ^ s := pow_le_pow_right₀ hb hs
  rw [inv_le_comm₀ hWpos (by positivity), mul_inv, inv_inv]
  rw [inv_mul_le_iff₀ (by positivity)]
  linarith

theorem summable_inv_trigWeight (s : ℕ) (hs : 2 ≤ s) :
    Summable fun n : Fin 3 → ℤ => (trigWeight s n)⁻¹ :=
  Summable.of_nonneg_of_le (fun n => (inv_pos.mpr (trigWeight_pos s n)).le)
    (inv_trigWeight_le s hs) (summable_inv_bracket_sq.mul_left _)

/-- An `H^s` function, `s ≥ 2`, has absolutely summable Fourier coefficients. -/
theorem summable_of_trigWeight {s : ℕ} (hs : 2 ≤ s) {c : (Fin 3 → ℤ) → ℂ}
    (hc : Summable fun n => trigWeight s n * ‖c n‖ ^ 2) : Summable c :=
  (norm_tsum_sq_le c (fun n => (trigWeight s n)⁻¹) (fun n => trigWeight s n * ‖c n‖ ^ 2)
    (fun n => (inv_pos.mpr (trigWeight_pos s n)).le) (fun n => by
      have := trigWeight_pos s n; positivity)
    (fun n => by
      have := trigWeight_pos s n
      rw [← mul_assoc, inv_mul_cancel₀ this.ne', one_mul])
    (summable_inv_trigWeight s hs) hc).1


/-! ### The quantitative sampling estimate -/

/-- Coefficients of the aliasing error at the retained frequencies: the folded tail. -/
theorem hasSum_mFourierCoeff_proj_sub_zero (f : C(UnitAddTorus (Fin 3), ℂ))
    (hf : Summable (mFourierCoeff ⇑f)) (k : Grid N) :
    HasSum (fun ℓ => if ℓ = 0 then 0 else mFourierCoeff ⇑f (aliasEquiv N (k, ℓ)))
      (mFourierCoeff ⇑(proj N ⇑f - f) (aliasEquiv N (k, 0))) := by
  rw [mFourierCoeff_sub, mFourierCoeff_proj_aliasEquiv, if_pos rfl]
  have h := (hasSum_dft_sample f hf k).update 0 0
  have e : Function.update (fun ℓ => mFourierCoeff ⇑f (aliasEquiv N (k, ℓ))) 0 0 =
      fun ℓ => if ℓ = 0 then 0 else mFourierCoeff ⇑f (aliasEquiv N (k, ℓ)) := by
    funext ℓ; rw [Function.update_apply]
  rw [e] at h
  have h2 : dft (sample N ⇑f) k - mFourierCoeff ⇑f (aliasEquiv N (k, 0)) =
      0 - mFourierCoeff ⇑f (aliasEquiv N (k, 0)) + dft (sample N ⇑f) k := by ring
  rw [h2]
  exact h

theorem mFourierCoeff_proj_sub_ne (f : C(UnitAddTorus (Fin 3), ℂ)) (k : Grid N)
    {ℓ : Fin 3 → ℤ} (hℓ : ℓ ≠ 0) :
    mFourierCoeff ⇑(proj N ⇑f - f) (aliasEquiv N (k, ℓ)) =
      -mFourierCoeff ⇑f (aliasEquiv N (k, ℓ)) := by
  rw [mFourierCoeff_sub, mFourierCoeff_proj_aliasEquiv, if_neg hℓ, zero_sub]

/-- **Quantitative sampling estimate** (`eq:supp-open-sampling-estimate`, error half, with the
`h^j`, `H^{r+j}` refinement).  For integers `r, j` with `r + j ≥ 2` there is `C`, independent of
the mesh, such that for every `N` and every continuous `u ∈ H^{r+j}(𝕋³)`,
`‖𝒫_h u - u‖²_{H^r} ≤ C h^{2j} ‖u‖²_{H^{r+j}}` (`h = 1/N`). -/
theorem sampling_error (r j : ℕ) (hrj : 2 ≤ r + j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (f : C(UnitAddTorus (Fin 3), ℂ)),
      Summable (fun n => trigWeight (r + j) n * ‖mFourierCoeff ⇑f n‖ ^ 2) →
      Summable (fun n => trigWeight r n * ‖mFourierCoeff ⇑(proj N ⇑f - f) n‖ ^ 2) ∧
      trigSobSq r ⇑(proj N ⇑f - f) ≤
        C * (((N : ℝ) ^ 2) ^ j)⁻¹ * trigSobSq (r + j) ⇑f := by
  set card := ((multiIndices r).card : ℝ)
  set C1 := card * (8 * π ^ 2) ^ r * 32 ^ (r + j) * (256 * c1 ^ 3)
  set C2 := card * ((2 * π) ^ 2) ^ r * 4 ^ (r + j) * 4 ^ j
  have hcard : 0 ≤ card := Nat.cast_nonneg _
  have hC1 : 0 ≤ C1 := by have := c1_nonneg; positivity
  have hC2 : 0 ≤ C2 := by positivity
  refine ⟨2 * (C1 + C2), by positivity, fun N _ f hf => ?_⟩
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set X : ℝ := (N : ℝ) ^ 2 with hXdef
  have hX : 0 < X := by positivity
  set ε : ℝ := (X ^ j)⁻¹ with hεdef
  have hε : 0 ≤ ε := by positivity
  set e := aliasEquiv N
  set û := mFourierCoeff ⇑f
  have hûsum : Summable û := summable_of_trigWeight hrj hf
  set G : Grid N × (Fin 3 → ℤ) → ℝ := fun p => trigWeight (r + j) (e p) * ‖û (e p)‖ ^ 2
    with hGdef
  have hG0 : ∀ p, 0 ≤ G p := fun p => mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _)
  have hGs : Summable G := (Equiv.summable_iff e).mpr hf
  set A := trigSobSq (r + j) ⇑f
  have hA : ∑' p, G p = A := Equiv.tsum_eq e (fun n => trigWeight (r + j) n * ‖û n‖ ^ 2)
  set Gk : Grid N → ℝ := fun k => ∑' ℓ, G (k, ℓ)
  have hGk : ∑ k, Gk k = A := by
    rw [← hA, hGs.tsum_prod' (fun k => hGs.prod_factor k), tsum_fintype]
  set c : (Fin 3 → ℤ) → ℂ := mFourierCoeff ⇑(proj N ⇑f - f)
  set E : Grid N × (Fin 3 → ℤ) → ℝ := fun p => trigWeight r (e p) * ‖c (e p)‖ ^ 2
  have hE0 : ∀ p, 0 ≤ E p := fun p => mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _)
  set H : Grid N × (Fin 3 → ℤ) → ℝ := fun p => if p.2 = 0 then Gk p.1 else 0
  set D : Grid N × (Fin 3 → ℤ) → ℝ := fun p => (C1 + C2) * ε * (G p + H p)
  -- the retained frequencies: folded tail
  have hE_zero : ∀ k, E (k, 0) ≤ C1 * ε * Gk k := by
    intro k
    set a : (Fin 3 → ℤ) → ℂ := fun ℓ => if ℓ = 0 then 0 else û (e (k, ℓ))
    set b : (Fin 3 → ℤ) → ℝ := fun ℓ => if ℓ = 0 then 0 else (trigWeight (r + j) (e (k, ℓ)))⁻¹
    set cc : (Fin 3 → ℤ) → ℝ := fun ℓ => if ℓ = 0 then 0 else G (k, ℓ)
    have hb0 : ∀ ℓ, 0 ≤ b ℓ := by
      intro ℓ; by_cases h : ℓ = 0
      · simp [b, h]
      · simp only [b, if_neg h]; exact (inv_pos.mpr (trigWeight_pos _ _)).le
    have hcc0 : ∀ ℓ, 0 ≤ cc ℓ := by
      intro ℓ; by_cases h : ℓ = 0
      · simp [cc, h]
      · simp only [cc, if_neg h]; exact hG0 _
    have hbbound : ∀ ℓ, b ℓ ≤ 32 ^ (r + j) * (X ^ (r + j))⁻¹ * (bracket ℓ ^ 2)⁻¹ := by
      intro ℓ; by_cases h : ℓ = 0
      · simp only [b, if_pos h]; have := bracket_pos ℓ; positivity
      · simp only [b, if_neg h]; exact inv_trigWeight_aliasEquiv_le hrj k h
    have hbs : Summable b := Summable.of_nonneg_of_le hb0 hbbound
      (summable_inv_bracket_sq.mul_left _)
    have hccbound : ∀ ℓ, cc ℓ ≤ G (k, ℓ) := by
      intro ℓ; by_cases h : ℓ = 0
      · simp only [cc, if_pos h]; exact hG0 _
      · simp [cc, h]
    have hccs : Summable cc := Summable.of_nonneg_of_le hcc0 hccbound (hGs.prod_factor k)
    have habc : ∀ ℓ, ‖a ℓ‖ ^ 2 ≤ b ℓ * cc ℓ := by
      intro ℓ; by_cases h : ℓ = 0
      · simp [a, b, cc, h]
      · simp only [a, b, cc, if_neg h, hGdef]
        have := trigWeight_pos (r + j) (e (k, ℓ))
        rw [← mul_assoc, inv_mul_cancel₀ this.ne', one_mul]
    obtain ⟨-, hCS⟩ := norm_tsum_sq_le a b cc hb0 hcc0 habc hbs hccs
    have hcoef : c (e (k, 0)) = ∑' ℓ, a ℓ :=
      (hasSum_mFourierCoeff_proj_sub_zero f hûsum k).tsum_eq.symm
    have hsb : ∑' ℓ, b ℓ ≤ 32 ^ (r + j) * (X ^ (r + j))⁻¹ * (256 * c1 ^ 3) := by
      calc ∑' ℓ, b ℓ ≤ ∑' ℓ, 32 ^ (r + j) * (X ^ (r + j))⁻¹ * (bracket ℓ ^ 2)⁻¹ :=
            hbs.tsum_le_tsum hbbound (summable_inv_bracket_sq.mul_left _)
        _ = 32 ^ (r + j) * (X ^ (r + j))⁻¹ * ∑' ℓ, (bracket ℓ ^ 2)⁻¹ := tsum_mul_left
        _ ≤ _ := by gcongr; exact tsum_inv_bracket_sq_le
    have hscc : ∑' ℓ, cc ℓ ≤ Gk k := hccs.tsum_le_tsum hccbound (hGs.prod_factor k)
    have hW : trigWeight r (e (k, 0)) ≤ card * (8 * π ^ 2) ^ r * X ^ r := by
      rw [show e (k, 0) = freqVec k from aliasEquiv_zero k]
      exact trigWeight_freqVec_le r k
    have hprod : X ^ r * (X ^ (r + j))⁻¹ = ε := by
      rw [hεdef, pow_add]; field_simp
    calc E (k, 0) = trigWeight r (e (k, 0)) * ‖∑' ℓ, a ℓ‖ ^ 2 := by
          simp only [E]; rw [hcoef]
      _ ≤ (card * (8 * π ^ 2) ^ r * X ^ r) *
            ((32 ^ (r + j) * (X ^ (r + j))⁻¹ * (256 * c1 ^ 3)) * Gk k) := by
          refine mul_le_mul hW (hCS.trans ?_) (sq_nonneg _) (by positivity)
          exact mul_le_mul hsb hscc (tsum_nonneg hcc0) (by have := c1_nonneg; positivity)
      _ = C1 * (X ^ r * (X ^ (r + j))⁻¹) * Gk k := by simp only [C1]; ring
      _ = C1 * ε * Gk k := by rw [hprod]
  -- the discarded frequencies: tail
  have hE_ne : ∀ k ℓ, ℓ ≠ 0 → E (k, ℓ) ≤ C2 * ε * G (k, ℓ) := by
    intro k ℓ hℓ
    simp only [E, c, G]
    rw [mFourierCoeff_proj_sub_ne f k hℓ, norm_neg]
    have := trigWeight_aliasEquiv_tail_le r j k hℓ
    calc trigWeight r (e (k, ℓ)) * ‖û (e (k, ℓ))‖ ^ 2
        ≤ (card * ((2 * π) ^ 2) ^ r * 4 ^ (r + j) * 4 ^ j * (X ^ j)⁻¹ *
            trigWeight (r + j) (e (k, ℓ))) * ‖û (e (k, ℓ))‖ ^ 2 :=
          mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = C2 * ε * (trigWeight (r + j) (e (k, ℓ)) * ‖û (e (k, ℓ))‖ ^ 2) := by
          simp only [C2, ε]; ring
  have hGkpos : ∀ k, 0 ≤ Gk k := fun k => tsum_nonneg fun ℓ => hG0 _
  have hH0 : ∀ p, 0 ≤ H p := by
    intro p; simp only [H]; split_ifs
    · exact hGkpos _
    · exact le_refl 0
  have hED : ∀ p, E p ≤ D p := by
    rintro ⟨k, ℓ⟩
    have hb : 0 ≤ (C1 + C2) * ε := by positivity
    by_cases hℓ : ℓ = 0
    · subst hℓ
      refine (hE_zero k).trans ?_
      simp only [D, H, ↓reduceIte]
      have := hG0 (k, 0)
      have : C1 * ε * Gk k ≤ (C1 + C2) * ε * Gk k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hε) (hGkpos k)
      nlinarith
    · refine (hE_ne k ℓ hℓ).trans ?_
      simp only [D, H, if_neg hℓ, add_zero]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hε) (hG0 _)
  have hHs : Summable H := by
    refine summable_of_ne_finset_zero (s := (univ : Finset (Grid N)) ×ˢ {0}) fun p hp => ?_
    simp only [H]
    rw [if_neg]
    intro h
    exact hp (mem_product.mpr ⟨mem_univ _, mem_singleton.mpr h⟩)
  have hHsum : ∑' p, H p = A := by
    rw [tsum_eq_sum (s := (univ : Finset (Grid N)) ×ˢ {0})]
    · rw [sum_product, ← hGk]
      refine sum_congr rfl fun k _ => ?_
      simp [H]
    · intro p hp
      simp only [H]
      rw [if_neg]
      intro h
      exact hp (mem_product.mpr ⟨mem_univ _, mem_singleton.mpr h⟩)
  have hDs : Summable D := (hGs.add hHs).mul_left _
  have hDsum : ∑' p, D p = 2 * (C1 + C2) * ε * A := by
    simp only [D]
    rw [tsum_mul_left, hGs.tsum_add hHs, hA, hHsum]
    ring
  have hEs : Summable E := Summable.of_nonneg_of_le hE0 hED hDs
  refine ⟨(Equiv.summable_iff e).mp hEs, ?_⟩
  unfold trigSobSq
  rw [← Equiv.tsum_eq e]
  calc ∑' p, trigWeight r (e p) * ‖mFourierCoeff ⇑(proj N ⇑f - f) (e p)‖ ^ 2
      = ∑' p, E p := rfl
    _ ≤ ∑' p, D p := hEs.tsum_le_tsum hED hDs
    _ = 2 * (C1 + C2) * ε * A := hDsum


/-! ### Stability of sampling -/

theorem mFourierCoeff_add (F G : C(UnitAddTorus (Fin 3), ℂ)) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(F + G) n = mFourierCoeff ⇑F n + mFourierCoeff ⇑G n := by
  rw [← mFourierCoeff_toLp, ← mFourierCoeff_toLp F, ← mFourierCoeff_toLp G,
    ← mFourierBasis_repr, ← mFourierBasis_repr, ← mFourierBasis_repr, map_add, map_add]
  rfl

/-- The squared trigonometric Sobolev norm is quasi-subadditive. -/
theorem trigSobSq_add_le (r : ℕ) (F G : C(UnitAddTorus (Fin 3), ℂ))
    (hF : Summable fun n => trigWeight r n * ‖mFourierCoeff ⇑F n‖ ^ 2)
    (hG : Summable fun n => trigWeight r n * ‖mFourierCoeff ⇑G n‖ ^ 2) :
    (Summable fun n => trigWeight r n * ‖mFourierCoeff ⇑(F + G) n‖ ^ 2) ∧
      trigSobSq r ⇑(F + G) ≤ 2 * trigSobSq r ⇑F + 2 * trigSobSq r ⇑G := by
  have hpt : ∀ n, trigWeight r n * ‖mFourierCoeff ⇑(F + G) n‖ ^ 2 ≤
      2 * (trigWeight r n * ‖mFourierCoeff ⇑F n‖ ^ 2) +
        2 * (trigWeight r n * ‖mFourierCoeff ⇑G n‖ ^ 2) := by
    intro n
    rw [mFourierCoeff_add]
    have hW := trigWeight_nonneg r n
    have h1 := norm_add_le (mFourierCoeff ⇑F n) (mFourierCoeff ⇑G n)
    have h2 : ‖mFourierCoeff ⇑F n + mFourierCoeff ⇑G n‖ ^ 2 ≤
        2 * ‖mFourierCoeff ⇑F n‖ ^ 2 + 2 * ‖mFourierCoeff ⇑G n‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖mFourierCoeff ⇑F n‖ - ‖mFourierCoeff ⇑G n‖)]
    nlinarith
  have hS : Summable fun n => 2 * (trigWeight r n * ‖mFourierCoeff ⇑F n‖ ^ 2) +
      2 * (trigWeight r n * ‖mFourierCoeff ⇑G n‖ ^ 2) := (hF.mul_left 2).add (hG.mul_left 2)
  have hs := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (trigWeight_nonneg r n) (sq_nonneg _)) hpt hS
  refine ⟨hs, ?_⟩
  unfold trigSobSq
  calc ∑' n, trigWeight r n * ‖mFourierCoeff ⇑(F + G) n‖ ^ 2
      ≤ ∑' n, (2 * (trigWeight r n * ‖mFourierCoeff ⇑F n‖ ^ 2) +
          2 * (trigWeight r n * ‖mFourierCoeff ⇑G n‖ ^ 2)) := hs.tsum_le_tsum hpt hS
    _ = _ := by rw [(hF.mul_left 2).tsum_add (hG.mul_left 2), tsum_mul_left, tsum_mul_left]

/-- **Sampling stability** (`eq:supp-open-sampling-estimate`, second half): for `r ≥ 2` there is
`C`, independent of the mesh, with `‖𝒫_h u‖²_{H^r} ≤ C ‖u‖²_{H^r}`. -/
theorem sampling_stable (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (f : C(UnitAddTorus (Fin 3), ℂ)),
      Summable (fun n => trigWeight r n * ‖mFourierCoeff ⇑f n‖ ^ 2) →
      Summable (fun n => trigWeight r n * ‖mFourierCoeff ⇑(proj N ⇑f) n‖ ^ 2) ∧
      trigSobSq r ⇑(proj N ⇑f) ≤ C * trigSobSq r ⇑f := by
  obtain ⟨C, hC, hE⟩ := sampling_error r 0 (by omega)
  refine ⟨2 * C + 2, by positivity, fun N _ f hf => ?_⟩
  obtain ⟨hs, hb⟩ := hE N f (by simpa using hf)
  simp only [pow_zero, inv_one, mul_one, add_zero] at hb
  have e : proj N ⇑f = (proj N ⇑f - f) + f := by abel
  rw [e]
  obtain ⟨hs2, hb2⟩ := trigSobSq_add_le r (proj N ⇑f - f) f hs hf
  refine ⟨hs2, hb2.trans ?_⟩
  have h0 : 0 ≤ trigSobSq r ⇑f := tsum_nonneg fun n => mul_nonneg (trigWeight_nonneg r n)
    (sq_nonneg _)
  nlinarith

/-! ### Difference consistency -/

/-- `|e^{iθ} - 1 - iθ| ≤ θ²` for `|θ| ≤ π`. -/
theorem norm_exp_I_mul_sub_one_sub_le {θ : ℝ} (hθ : |θ| ≤ π) :
    ‖Complex.exp (Complex.I * θ) - 1 - Complex.I * θ‖ ≤ θ ^ 2 := by
  have hre : (Complex.exp (Complex.I * θ) - 1 - Complex.I * θ).re = Real.cos θ - 1 := by
    rw [mul_comm]; simp [Complex.exp_ofReal_mul_I_re]
  have him : (Complex.exp (Complex.I * θ) - 1 - Complex.I * θ).im = Real.sin θ - θ := by
    rw [mul_comm]; simp [Complex.exp_ofReal_mul_I_im]
  have hcos1 : 1 - θ ^ 2 / 2 ≤ Real.cos θ := Real.one_sub_sq_div_two_le_cos
  have hcos2 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hsin : |Real.sin θ - θ| ≤ |θ| ^ 3 / 6 := by
    rcases le_total 0 θ with h | h
    · have h1 := Real.sin_ge_sub_cube h
      have h2 := Real.sin_le h
      rw [abs_of_nonpos (by linarith), abs_of_nonneg h]
      linarith
    · have h1 := Real.sin_ge_sub_cube (neg_nonneg.mpr h)
      have h2 := Real.sin_le (neg_nonneg.mpr h)
      rw [Real.sin_neg] at h1 h2
      rw [abs_of_nonneg (by linarith), abs_of_nonpos h]
      nlinarith
  have hpi : π ^ 2 ≤ 10 := by
    have := Real.pi_lt_d2; have := Real.pi_pos; nlinarith
  have ht2 : θ ^ 2 ≤ π ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθ 2
  have hsq : ‖Complex.exp (Complex.I * θ) - 1 - Complex.I * θ‖ ^ 2 ≤ (θ ^ 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have a1 : (Real.cos θ - 1) * (Real.cos θ - 1) ≤ (θ ^ 2 / 2) ^ 2 := by
      have : 0 ≤ 1 - Real.cos θ := by linarith
      nlinarith
    have a2 : (Real.sin θ - θ) * (Real.sin θ - θ) ≤ (|θ| ^ 3 / 6) ^ 2 := by
      rw [← sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hsin 2
    have a3 : (|θ| ^ 3 / 6) ^ 2 = θ ^ 2 * (θ ^ 2) ^ 2 / 36 := by
      rw [div_pow, ← pow_mul, show |θ| ^ (3 * 2) = (|θ| ^ 2) ^ 3 by ring, sq_abs]; ring
    rw [a3] at a2
    have a4 : θ ^ 2 * (θ ^ 2) ^ 2 / 36 ≤ 10 * (θ ^ 2) ^ 2 / 36 := by
      have := sq_nonneg (θ ^ 2)
      nlinarith
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (sq_nonneg _) two_ne_zero).mp hsq

/-- The spectral partial derivative on the grid: the grid function whose DFT is
`2πi k̃_i û(k)`; its interpolant is `∂_i 𝓘_h u` (`hasDerivAt_interp_line`). -/
noncomputable def specD (i : Fin 3) (u : Grid N → ℂ) : Grid N → ℂ :=
  fun x => ∑ k, latticeChar k x * (2 * π * Complex.I * (freqVec k i : ℂ) * dft u k)

theorem dft_synth (c : Grid N → ℂ) (k₀ : Grid N) :
    dft (fun x => ∑ k, latticeChar k x * c k) k₀ = c k₀ := by
  have e : (fun x => ∑ k, latticeChar k x * c k) =
      fun x => ∑ k, (c k • fun y => latticeChar k y) x := by
    funext x; simp [mul_comm]
  rw [e, dft_sum]
  simp only [dft_smul, dft_latticeChar, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq']; simp

theorem dft_specD (i : Fin 3) (u : Grid N → ℂ) (k : Grid N) :
    dft (specD i u) k = 2 * π * Complex.I * (freqVec k i : ℂ) * dft u k :=
  dft_synth _ k

theorem interp_sub (u v : Grid N → ℂ) : interp (u - v) = interp u - interp v := by
  simp only [interp, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [dft_sub]
  exact sub_smul (dft u k) (dft v k) (mFourier (freqVec k))

/-- A coordinate line through a lifted point of the torus. -/
noncomputable def linePt (y : Fin 3 → ℝ) (i : Fin 3) (t : ℝ) : UnitAddTorus (Fin 3) :=
  fun j => ((y j + if j = i then t else 0 : ℝ) : UnitAddCircle)

theorem mFourier_linePt (n : Fin 3 → ℤ) (y : Fin 3 → ℝ) (i : Fin 3) (t : ℝ) :
    mFourier n (linePt y i t) = mFourier n (linePt y i 0) * fourier (n i) (t : UnitAddCircle) := by
  simp only [mFourier, ContinuousMap.coe_mk, linePt, fourier_coe_apply, Fin.prod_univ_three]
  fin_cases i <;> simp only [← Complex.exp_add] <;> congr 1 <;> simp <;> push_cast <;> ring

/-- **The interpolant of `specD` is the partial derivative of the interpolant**: along every
coordinate line, `t ↦ 𝓘_h u(y + t e_i)` has derivative `𝓘_h(specD_i u)(y)` at `t = 0`. -/
theorem hasDerivAt_interp_line (u : Grid N → ℂ) (y : Fin 3 → ℝ) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => interp u (linePt y i t)) (interp (specD i u) (linePt y i 0)) 0 := by
  simp only [interp, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  refine HasDerivAt.fun_sum fun k _ => ?_
  rw [dft_specD]
  have hfun : (fun t : ℝ => dft u k * mFourier (freqVec k) (linePt y i t)) =
      fun t : ℝ => dft u k * mFourier (freqVec k) (linePt y i 0) *
        fourier (freqVec k i) ((t : ℝ) : UnitAddCircle) :=
    funext fun t => by rw [mFourier_linePt]; ring
  rw [hfun]
  have h := (hasDerivAt_fourier 1 (freqVec k i) 0).const_mul
    (dft u k * mFourier (freqVec k) (linePt y i 0))
  have h0 : fourier (freqVec k i) (((0 : ℝ) : UnitAddCircle)) = 1 := by
    rw [fourier_coe_apply]; simp
  refine h.congr_deriv ?_
  rw [h0]
  push_cast
  ring

theorem norm_sym_sub_le (i : Fin 3) (k : Grid N) :
    ‖sym i k - 2 * π * Complex.I * (freqVec k i : ℂ)‖ ≤
      4 * π ^ 2 * ((freqVec k i : ℤ) : ℝ) ^ 2 / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set θ : ℝ := 2 * π * freq i k / N
  have hθ : |θ| ≤ π := by
    have := abs_freq_le i k
    simp only [θ, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two, abs_of_pos hN]
    rw [div_le_iff₀ hN]; nlinarith [Real.pi_pos]
  have e : sym i k - 2 * π * Complex.I * (freqVec k i : ℂ) =
      (N : ℂ) * (Complex.exp (Complex.I * θ) - 1 - Complex.I * θ) := by
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
    rw [sym, chi_eq_exp]
    simp only [θ, freqVec]
    push_cast
    field_simp
  rw [e, norm_mul, Complex.norm_natCast]
  calc (N : ℝ) * ‖Complex.exp (Complex.I * θ) - 1 - Complex.I * θ‖ ≤ N * θ ^ 2 :=
        mul_le_mul_of_nonneg_left (norm_exp_I_mul_sub_one_sub_le hθ) hN.le
    _ = _ := by simp only [θ, freqVec]; field_simp; ring

theorem norm_symm_sub_le (i : Fin 3) (k : Grid N) :
    ‖(N : ℂ) * (1 - conj (chi i k)) - 2 * π * Complex.I * (freqVec k i : ℂ)‖ ≤
      4 * π ^ 2 * ((freqVec k i : ℤ) : ℝ) ^ 2 / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set θ : ℝ := 2 * π * freq i k / N
  have hθ : |-θ| ≤ π := by
    rw [abs_neg]
    have := abs_freq_le i k
    simp only [θ, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two, abs_of_pos hN]
    rw [div_le_iff₀ hN]; nlinarith [Real.pi_pos]
  have e : (N : ℂ) * (1 - conj (chi i k)) - 2 * π * Complex.I * (freqVec k i : ℂ) =
      -((N : ℂ) * (Complex.exp (Complex.I * ((-θ : ℝ) : ℂ)) - 1 - Complex.I * ((-θ : ℝ) : ℂ))) := by
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
    rw [chi_eq_exp, ← Complex.exp_conj]
    simp only [θ, freqVec, map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    field_simp
    ring
  rw [e, norm_neg, norm_mul, Complex.norm_natCast]
  calc (N : ℝ) * ‖Complex.exp (Complex.I * ((-θ : ℝ) : ℂ)) - 1 - Complex.I * ((-θ : ℝ) : ℂ)‖
      ≤ N * (-θ) ^ 2 := mul_le_mul_of_nonneg_left (norm_exp_I_mul_sub_one_sub_le hθ) hN.le
    _ = _ := by simp only [θ, freqVec]; field_simp; ring

/-- `W_r(n) (2π n_i)⁴ ≤ W_{r+2}(n)`. -/
theorem trigWeight_mul_pow_four_le (r : ℕ) (n : Fin 3 → ℤ) (i : Fin 3) :
    trigWeight r n * ((2 * π * n i) ^ 2) ^ 2 ≤ trigWeight (r + 2) n := by
  classical
  unfold trigWeight
  rw [sum_mul]
  have hshift : ∀ α : Fin 3 → ℕ, tsymSq α n * ((2 * π * n i) ^ 2) ^ 2 =
      tsymSq (α + Pi.single i 2) n := by
    intro α
    fin_cases i <;> simp [tsymSq, pow_add] <;> ring
  simp_rw [hshift]
  rw [← sum_image (f := fun β => tsymSq β n) (s := multiIndices r)
    (g := fun α => α + Pi.single i 2) (fun a _ b _ h => add_right_cancel h)]
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun β _ _ => tsymSq_nonneg β n)
  intro β hβ
  obtain ⟨α, hα, rfl⟩ := mem_image.mp hβ
  rw [mem_multiIndices] at hα ⊢
  have : deg (α + Pi.single i 2) = deg α + 2 := by
    simp only [deg, Pi.add_apply]; fin_cases i <;> simp <;> ring
  omega

/-- Pointwise norm comparison on the signed cube: `(2/π)^{2s} W_s(k̃) ≤ |grid weight|`. -/
theorem trigWeight_freqVec_le_gridWeight (s : ℕ) (k : Grid N) :
    ((2 / π) ^ 2) ^ s * trigWeight s (freqVec k) ≤ gridWeight s k := by
  rw [trigWeight, gridWeight, mul_sum]
  refine sum_le_sum fun α hα => ?_
  have hdeg := mem_multiIndices.mp hα
  have hc0 : 0 ≤ (2 / π) ^ 2 := by positivity
  have hmono : ((2 / π) ^ 2) ^ s ≤ ((2 / π) ^ 2) ^ deg α :=
    pow_le_pow_of_le_one hc0 two_div_pi_sq_le_one hdeg
  exact (mul_le_mul_of_nonneg_right hmono (tsymSq_nonneg α _)).trans (tsymSq_le_norm_dsym_sq α k)

/-- Generic difference-consistency bound: a multiplier whose symbol differs from `2πi k̃_i` by at
most `4π² k̃_i²/N` is `O(h)`-close to `∂_i` from `H_h^{r+2}` to `H^r`. -/
theorem trigSobSq_interp_mult_sub_le (r : ℕ) (i : Fin 3) (T : Module.End ℂ (Grid N → ℂ))
    (m : Grid N → ℂ) (hT : IsMult T m)
    (hm : ∀ k, ‖m k - 2 * π * Complex.I * (freqVec k i : ℂ)‖ ≤
      4 * π ^ 2 * ((freqVec k i : ℤ) : ℝ) ^ 2 / N) (u : Grid N → ℂ) :
    trigSobSq r ⇑(interp (T u) - interp (specD i u)) ≤
      ((π ^ 2 / 4) ^ (r + 2) * (((N : ℝ) ^ 2)⁻¹)) * sobSq (r + 2) u := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [← interp_sub, trigSobSq_interp, sobSq_eq_weight, mul_sum]
  refine sum_le_sum fun k _ => ?_
  have hd : dft (T u - specD i u) k =
      (m k - 2 * π * Complex.I * (freqVec k i : ℂ)) * dft u k := by
    rw [dft_sub, hT u k, dft_specD]; ring
  rw [hd, norm_mul, mul_pow]
  set x : ℝ := ((freqVec k i : ℤ) : ℝ)
  have hsym := hm k
  have hsq : ‖m k - 2 * π * Complex.I * (freqVec k i : ℂ)‖ ^ 2 ≤
      (4 * π ^ 2 * x ^ 2 / N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsym 2
  have h4 := trigWeight_mul_pow_four_le r (freqVec k) i
  have hgw := trigWeight_freqVec_le_gridWeight (r + 2) k
  have hW := trigWeight_nonneg r (freqVec k)
  have hpi : 0 < π := Real.pi_pos
  have hcst : (π ^ 2 / 4) ^ (r + 2) * ((2 / π) ^ 2) ^ (r + 2) = 1 := by
    rw [← mul_pow]; field_simp; norm_num
  have key : trigWeight r (freqVec k) * (4 * π ^ 2 * x ^ 2 / N) ^ 2 ≤
      (π ^ 2 / 4) ^ (r + 2) * ((N : ℝ) ^ 2)⁻¹ * gridWeight (r + 2) k := by
    have e1 : trigWeight r (freqVec k) * (4 * π ^ 2 * x ^ 2 / N) ^ 2 =
        ((N : ℝ) ^ 2)⁻¹ * (trigWeight r (freqVec k) * ((2 * π * x) ^ 2) ^ 2) := by
      field_simp; ring
    rw [e1]
    have h4' : trigWeight r (freqVec k) * ((2 * π * x) ^ 2) ^ 2 ≤
        trigWeight (r + 2) (freqVec k) := h4
    calc ((N : ℝ) ^ 2)⁻¹ * (trigWeight r (freqVec k) * ((2 * π * x) ^ 2) ^ 2)
        ≤ ((N : ℝ) ^ 2)⁻¹ * trigWeight (r + 2) (freqVec k) := by gcongr
      _ = ((N : ℝ) ^ 2)⁻¹ * ((π ^ 2 / 4) ^ (r + 2) *
            (((2 / π) ^ 2) ^ (r + 2) * trigWeight (r + 2) (freqVec k))) := by
          rw [← mul_assoc ((π ^ 2 / 4) ^ (r + 2)), hcst, one_mul]
      _ ≤ ((N : ℝ) ^ 2)⁻¹ * ((π ^ 2 / 4) ^ (r + 2) * gridWeight (r + 2) k) := by gcongr
      _ = _ := by ring
  calc trigWeight r (freqVec k) * (‖m k - 2 * π * Complex.I * (freqVec k i : ℂ)‖ ^ 2 *
        ‖dft u k‖ ^ 2)
      ≤ trigWeight r (freqVec k) * ((4 * π ^ 2 * x ^ 2 / N) ^ 2 * ‖dft u k‖ ^ 2) := by gcongr
    _ = (trigWeight r (freqVec k) * (4 * π ^ 2 * x ^ 2 / N) ^ 2) * ‖dft u k‖ ^ 2 := by ring
    _ ≤ ((π ^ 2 / 4) ^ (r + 2) * ((N : ℝ) ^ 2)⁻¹ * gridWeight (r + 2) k) * ‖dft u k‖ ^ 2 := by
        gcongr
    _ = _ := by ring

/-- **Difference consistency** (`eq:supp-open-difference-consistency`) for the forward
difference: `‖𝓘_h D_i⁺ u_h - ∂_i 𝓘_h u_h‖²_{H^r} ≤ (π²/4)^{r+2} h² ‖u_h‖²_{r+2,h}`. -/
theorem difference_consistency_Dp (r : ℕ) (i : Fin 3) (u : Grid N → ℂ) :
    trigSobSq r ⇑(interp (Dp i u) - interp (specD i u)) ≤
      ((π ^ 2 / 4) ^ (r + 2) * (((N : ℝ) ^ 2)⁻¹)) * sobSq (r + 2) u :=
  trigSobSq_interp_mult_sub_le r i (Dp i) (sym i) (isMult_Dp i) (norm_sym_sub_le i) u

/-- **Difference consistency** for the backward difference `D_i⁻`. -/
theorem difference_consistency_Dm (r : ℕ) (i : Fin 3) (u : Grid N → ℂ) :
    trigSobSq r ⇑(interp (Dm i u) - interp (specD i u)) ≤
      ((π ^ 2 / 4) ^ (r + 2) * (((N : ℝ) ^ 2)⁻¹)) * sobSq (r + 2) u :=
  trigSobSq_interp_mult_sub_le r i (Dm i) _ (isMult_Dm i) (norm_symm_sub_le i) u

/-- **Difference consistency** for the centred difference `D_i⁰` (by averaging). -/
theorem difference_consistency_D0 (r : ℕ) (i : Fin 3) (u : Grid N → ℂ) :
    trigSobSq r ⇑(interp (D0 i u) - interp (specD i u)) ≤
      ((π ^ 2 / 4) ^ (r + 2) * (((N : ℝ) ^ 2)⁻¹)) * sobSq (r + 2) u := by
  have hT : IsMult (D0 (N := N) i) (fun k => (2 : ℂ)⁻¹ * (sym i k + (N : ℂ) * (1 - conj (chi i k)))) := by
    have := ((isMult_Dp (N := N) i).add (isMult_Dm i)).smul (2 : ℂ)⁻¹
    intro u k
    rw [D0, this u k]
  refine trigSobSq_interp_mult_sub_le r i (D0 i) _ hT (fun k => ?_) u
  have e : (2 : ℂ)⁻¹ * (sym i k + (N : ℂ) * (1 - conj (chi i k))) -
      2 * π * Complex.I * (freqVec k i : ℂ) =
      (2 : ℂ)⁻¹ * ((sym i k - 2 * π * Complex.I * (freqVec k i : ℂ)) +
        ((N : ℂ) * (1 - conj (chi i k)) - 2 * π * Complex.I * (freqVec k i : ℂ))) := by ring
  rw [e, norm_mul]
  have h1 := norm_sym_sub_le i k
  have h2 := norm_symm_sub_le i k
  have h3 := norm_add_le (sym i k - 2 * π * Complex.I * (freqVec k i : ℂ))
    ((N : ℂ) * (1 - conj (chi i k)) - 2 * π * Complex.I * (freqVec k i : ℂ))
  have h4 : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by simp
  rw [h4]
  linarith


/-! ### The continuum product algebra on interpolants and product consistency -/

theorem interp_mul_eq (u w : Grid N → ℂ) :
    interp u * interp w = ∑ p : Grid N × Grid N,
      (dft u p.1 * dft w p.2) • mFourier (freqVec p.1 + freqVec p.2) := by
  ext x
  simp only [interp, ContinuousMap.mul_apply, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mFourier_add, Finset.sum_mul_sum,
    Fintype.sum_prod_type]
  refine sum_congr rfl fun k _ => sum_congr rfl fun k₁ _ => ?_
  ring

theorem mFourierCoeff_interp_mul (u w : Grid N → ℂ) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(interp u * interp w) n = ∑ p : Grid N × Grid N,
      if freqVec p.1 + freqVec p.2 = n then dft u p.1 * dft w p.2 else 0 := by
  rw [interp_mul_eq]
  exact mFourierCoeff_trigSum _ _ _ n

theorem bracket_add_le (p q : Fin 3 → ℤ) : bracket (p + q) ≤ 2 * (bracket p + bracket q) := by
  unfold bracket
  simp only [Pi.add_apply, Int.cast_add, Fin.sum_univ_three]
  nlinarith [sq_nonneg (((p 0 : ℤ) : ℝ) - q 0), sq_nonneg (((p 1 : ℤ) : ℝ) - q 1),
    sq_nonneg (((p 2 : ℤ) : ℝ) - q 2)]

theorem bracket_pow_add_le (s : ℕ) (p q : Fin 3 → ℤ) :
    bracket (p + q) ^ s ≤ 4 ^ s * (bracket p ^ s + bracket q ^ s) := by
  have hp := one_le_bracket p
  have hq := one_le_bracket q
  have h1 : bracket (p + q) ≤ 4 * max (bracket p) (bracket q) := by
    have := bracket_add_le p q
    have := le_max_left (bracket p) (bracket q)
    have := le_max_right (bracket p) (bracket q)
    linarith
  have h2 : max (bracket p) (bracket q) ^ s ≤ bracket p ^ s + bracket q ^ s := by
    rcases max_choice (bracket p) (bracket q) with h | h <;> rw [h]
    · have := pow_nonneg (le_trans zero_le_one hq) s; linarith
    · have := pow_nonneg (le_trans zero_le_one hp) s; linarith
  calc bracket (p + q) ^ s ≤ (4 * max (bracket p) (bracket q)) ^ s :=
        pow_le_pow_left₀ (le_trans zero_le_one (one_le_bracket _)) h1 s
    _ = 4 ^ s * max (bracket p) (bracket q) ^ s := mul_pow _ _ _
    _ ≤ 4 ^ s * (bracket p ^ s + bracket q ^ s) := by gcongr

theorem sum_inv_bracket_freqVec_le (s : ℕ) (hs : 2 ≤ s) :
    ∑ k : Grid N, (bracket (freqVec k) ^ s)⁻¹ ≤ 256 * c1 ^ 3 := by
  have h1 : ∀ k : Grid N, (bracket (freqVec k) ^ s)⁻¹ ≤ (bracket (freqVec k) ^ 2)⁻¹ := by
    intro k
    have hb := one_le_bracket (freqVec k)
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hb hs)
  calc ∑ k : Grid N, (bracket (freqVec k) ^ s)⁻¹ ≤ ∑ k : Grid N, (bracket (freqVec k) ^ 2)⁻¹ :=
        sum_le_sum fun k _ => h1 k
    _ = ∑ m ∈ (univ : Finset (Grid N)).image freqVec, (bracket m ^ 2)⁻¹ :=
        (sum_image (f := fun m => (bracket m ^ 2)⁻¹) (s := univ)
          (fun a _ b _ h => freqVec_injective h)).symm
    _ ≤ ∑' m, (bracket m ^ 2)⁻¹ :=
        summable_inv_bracket_sq.sum_le_tsum _ (fun m _ => by have := bracket_pos m; positivity)
    _ ≤ 256 * c1 ^ 3 := tsum_inv_bracket_sq_le

/-- **Uniform continuum product algebra on interpolants**: for `s ≥ 2` there is `K`, independent
of the mesh, with `‖(𝓘_h u)(𝓘_h w)‖²_{H^s} ≤ K ‖𝓘_h u‖²_{H^s} ‖𝓘_h w‖²_{H^s}`. -/
theorem trigSobSq_interp_mul_le (s : ℕ) (hs : 2 ≤ s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) [NeZero N] (u w : Grid N → ℂ),
      trigSobSq s ⇑(interp u * interp w) ≤
        K * trigSobSq s ⇑(interp u) * trigSobSq s ⇑(interp w) := by
  set card := ((multiIndices s).card : ℝ)
  set M : ℝ := 4 ^ s * (2 * (256 * c1 ^ 3))
  set K : ℝ := card * ((2 * π) ^ 2) ^ s * M * 4 ^ s * 4 ^ s
  have hM : 0 ≤ M := by have := c1_nonneg; positivity
  have hK : 0 ≤ K := by positivity
  refine ⟨K, hK, fun N _ u w => ?_⟩
  classical
  set P := (univ : Finset (Grid N × Grid N))
  set φ : Grid N × Grid N → (Fin 3 → ℤ) := fun p => freqVec p.1 + freqVec p.2
  set S := P.image φ
  set U : Grid N → ℝ := fun k => bracket (freqVec k) ^ s
  have hU : ∀ k, 0 < U k := fun k => pow_pos (bracket_pos _) s
  set c : (Fin 3 → ℤ) → ℂ := mFourierCoeff ⇑(interp u * interp w)
  have hc : ∀ n, c n = ∑ p ∈ P.filter (fun p => φ p = n), dft u p.1 * dft w p.2 := by
    intro n
    simp only [c, mFourierCoeff_interp_mul, sum_filter]
    rfl
  set G : Grid N × Grid N → ℝ := fun p => (U p.1 * ‖dft u p.1‖ ^ 2) * (U p.2 * ‖dft w p.2‖ ^ 2)
  have hG0 : ∀ p, 0 ≤ G p := fun p => by
    have := hU p.1; have := hU p.2; positivity
  -- the convolution weight bound
  have hconv : ∀ n, bracket n ^ s *
      ∑ p ∈ P.filter (fun p => φ p = n), 1 / (U p.1 * U p.2) ≤ M := by
    intro n
    rw [mul_sum]
    have hpt : ∀ p ∈ P.filter (fun p => φ p = n), bracket n ^ s * (1 / (U p.1 * U p.2)) ≤
        4 ^ s * ((U p.2)⁻¹ + (U p.1)⁻¹) := by
      intro p hp
      have hφ : φ p = n := (mem_filter.mp hp).2
      have h := bracket_pow_add_le s (freqVec p.1) (freqVec p.2)
      have h1 := hU p.1; have h2 := hU p.2
      rw [← hφ]
      calc bracket (φ p) ^ s * (1 / (U p.1 * U p.2)) ≤
            (4 ^ s * (U p.1 + U p.2)) * (1 / (U p.1 * U p.2)) := by
            gcongr
      _ = 4 ^ s * ((U p.2)⁻¹ + (U p.1)⁻¹) := by field_simp
    refine (sum_le_sum hpt).trans ?_
    rw [← mul_sum, sum_add_distrib]
    have hinj2 : Set.InjOn Prod.snd (P.filter (fun p => φ p = n) : Set (Grid N × Grid N)) := by
      intro p hp q hq h
      have hp' := (mem_filter.mp hp).2
      have hq' := (mem_filter.mp hq).2
      have : freqVec p.1 = freqVec q.1 := by
        have e1 : freqVec p.1 = n - freqVec p.2 := by rw [← hp']; simp [φ]
        have e2 : freqVec q.1 = n - freqVec q.2 := by rw [← hq']; simp [φ]
        rw [e1, e2, h]
      exact Prod.ext (freqVec_injective this) h
    have hinj1 : Set.InjOn Prod.fst (P.filter (fun p => φ p = n) : Set (Grid N × Grid N)) := by
      intro p hp q hq h
      have hp' := (mem_filter.mp hp).2
      have hq' := (mem_filter.mp hq).2
      have : freqVec p.2 = freqVec q.2 := by
        have e1 : freqVec p.2 = n - freqVec p.1 := by rw [← hp']; simp [φ]
        have e2 : freqVec q.2 = n - freqVec q.1 := by rw [← hq']; simp [φ]
        rw [e1, e2, h]
      exact Prod.ext h (freqVec_injective this)
    have hb2 : ∑ p ∈ P.filter (fun p => φ p = n), (U p.2)⁻¹ ≤ 256 * c1 ^ 3 := by
      rw [← sum_image (f := fun k => (U k)⁻¹) hinj2]
      refine (sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun k _ _ => (inv_pos.mpr (hU k)).le)).trans ?_
      exact sum_inv_bracket_freqVec_le s hs
    have hb1 : ∑ p ∈ P.filter (fun p => φ p = n), (U p.1)⁻¹ ≤ 256 * c1 ^ 3 := by
      rw [← sum_image (f := fun k => (U k)⁻¹) hinj1]
      refine (sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun k _ _ => (inv_pos.mpr (hU k)).le)).trans ?_
      exact sum_inv_bracket_freqVec_le s hs
    simp only [M]
    gcongr
    linarith
  -- pointwise bound on the coefficients
  have hpt : ∀ n, trigWeight s n * ‖c n‖ ^ 2 ≤
      card * ((2 * π) ^ 2) ^ s * M * ∑ p ∈ P.filter (fun p => φ p = n), G p := by
    intro n
    have hW : trigWeight s n ≤ card * ((2 * π) ^ 2) ^ s * bracket n ^ s := by
      have := trigWeight_le_bracket s n
      rw [mul_pow] at this; linarith
    have hCS : ‖c n‖ ^ 2 ≤ (∑ p ∈ P.filter (fun p => φ p = n), 1 / (U p.1 * U p.2)) *
        ∑ p ∈ P.filter (fun p => φ p = n), G p := by
      rw [hc n]
      have h1 : ‖∑ p ∈ P.filter (fun p => φ p = n), dft u p.1 * dft w p.2‖ ≤
          ∑ p ∈ P.filter (fun p => φ p = n), ‖dft u p.1‖ * ‖dft w p.2‖ :=
        (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun p _ => norm_mul _ _))
      have h2 : (∑ p ∈ P.filter (fun p => φ p = n), ‖dft u p.1‖ * ‖dft w p.2‖) ^ 2 ≤
          (∑ p ∈ P.filter (fun p => φ p = n), 1 / (U p.1 * U p.2)) *
            ∑ p ∈ P.filter (fun p => φ p = n), G p := by
        refine sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun p _ => ?_) (fun p _ => hG0 p)
          (fun p _ => ?_)
        · have := hU p.1; have := hU p.2; positivity
        · have hu' := hU p.1; have hv' := hU p.2
          rw [le_iff_eq_or_lt]; left
          simp only [G]
          field_simp
      exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
    have hsum0 : 0 ≤ ∑ p ∈ P.filter (fun p => φ p = n), G p := sum_nonneg fun p _ => hG0 p
    have hsum1 : 0 ≤ ∑ p ∈ P.filter (fun p => φ p = n), 1 / (U p.1 * U p.2) :=
      sum_nonneg fun p _ => by have := hU p.1; have := hU p.2; positivity
    have hb := hconv n
    have hbn : 0 ≤ bracket n ^ s := pow_nonneg (bracket_pos n).le s
    calc trigWeight s n * ‖c n‖ ^ 2
        ≤ (card * ((2 * π) ^ 2) ^ s * bracket n ^ s) *
            ((∑ p ∈ P.filter (fun p => φ p = n), 1 / (U p.1 * U p.2)) *
              ∑ p ∈ P.filter (fun p => φ p = n), G p) :=
          mul_le_mul hW hCS (sq_nonneg _) (by positivity)
      _ = card * ((2 * π) ^ 2) ^ s * ((bracket n ^ s *
            ∑ p ∈ P.filter (fun p => φ p = n), 1 / (U p.1 * U p.2)) *
              ∑ p ∈ P.filter (fun p => φ p = n), G p) := by ring
      _ ≤ card * ((2 * π) ^ 2) ^ s * (M * ∑ p ∈ P.filter (fun p => φ p = n), G p) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb hsum0) (by positivity)
      _ = _ := by ring
  -- finite support of the product coefficients
  have hsupp : ∀ n ∉ S, trigWeight s n * ‖c n‖ ^ 2 = 0 := by
    intro n hn
    rw [hc n]
    have : P.filter (fun p => φ p = n) = ∅ := by
      rw [filter_eq_empty_iff]
      intro p _ hp
      exact hn (mem_image.mpr ⟨p, mem_univ _, hp⟩)
    rw [this, sum_empty]; simp
  have hS : trigSobSq s ⇑(interp u * interp w) = ∑ n ∈ S, trigWeight s n * ‖c n‖ ^ 2 :=
    tsum_eq_sum (fun n hn => hsupp n hn)
  have hfib : ∑ n ∈ S, ∑ p ∈ P.filter (fun p => φ p = n), G p = ∑ p ∈ P, G p :=
    sum_fiberwise_of_maps_to (fun p hp => mem_image_of_mem φ hp) G
  have hprod : ∑ p ∈ P, G p = (∑ k, U k * ‖dft u k‖ ^ 2) * ∑ k, U k * ‖dft w k‖ ^ 2 := by
    simp only [P, G, Fintype.sum_prod_type, Finset.sum_mul_sum]
  have hUu : ∑ k, U k * ‖dft u k‖ ^ 2 ≤ 4 ^ s * trigSobSq s ⇑(interp u) := by
    rw [trigSobSq_interp, mul_sum]
    refine sum_le_sum fun k _ => ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (bracket_pow_le_trigWeight s _) (sq_nonneg _)
  have hUw : ∑ k, U k * ‖dft w k‖ ^ 2 ≤ 4 ^ s * trigSobSq s ⇑(interp w) := by
    rw [trigSobSq_interp, mul_sum]
    refine sum_le_sum fun k _ => ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (bracket_pow_le_trigWeight s _) (sq_nonneg _)
  have hUu0 : 0 ≤ ∑ k, U k * ‖dft u k‖ ^ 2 := sum_nonneg fun k _ => by
    have := hU k; positivity
  have hUw0 : 0 ≤ ∑ k, U k * ‖dft w k‖ ^ 2 := sum_nonneg fun k _ => by
    have := hU k; positivity
  have hTu : 0 ≤ trigSobSq s ⇑(interp u) := tsum_nonneg fun n =>
    mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _)
  rw [hS]
  calc ∑ n ∈ S, trigWeight s n * ‖c n‖ ^ 2
      ≤ ∑ n ∈ S, card * ((2 * π) ^ 2) ^ s * M * ∑ p ∈ P.filter (fun p => φ p = n), G p :=
        sum_le_sum fun n _ => hpt n
    _ = card * ((2 * π) ^ 2) ^ s * M * ((∑ k, U k * ‖dft u k‖ ^ 2) *
          ∑ k, U k * ‖dft w k‖ ^ 2) := by rw [← mul_sum, hfib, hprod]
    _ ≤ card * ((2 * π) ^ 2) ^ s * M * ((4 ^ s * trigSobSq s ⇑(interp u)) *
          (4 ^ s * trigSobSq s ⇑(interp w))) := by
        gcongr
    _ = K * trigSobSq s ⇑(interp u) * trigSobSq s ⇑(interp w) := by simp only [K]; ring

theorem sample_interp_mul (u w : Grid N → ℂ) : sample N ⇑(interp u * interp w) = u * w := by
  funext x
  simp [sample, interp_sample]

theorem trigSobSq_interp_le (r : ℕ) (u : Grid N → ℂ) :
    trigSobSq r ⇑(interp u) ≤ ((π / 2) ^ 2) ^ r * sobSq r u := by
  have h := trigSobSq_interp_le_sobSq r u
  have hc : ((π / 2) ^ 2) ^ r * ((2 / π) ^ 2) ^ r = 1 := by
    rw [← mul_pow, ← mul_pow]; field_simp; simp
  have hpos : 0 ≤ ((π / 2) ^ 2) ^ r := by positivity
  calc trigSobSq r ⇑(interp u) = ((π / 2) ^ 2) ^ r * (((2 / π) ^ 2) ^ r *
        trigSobSq r ⇑(interp u)) := by rw [← mul_assoc, hc, one_mul]
    _ ≤ ((π / 2) ^ 2) ^ r * sobSq r u := mul_le_mul_of_nonneg_left h hpos

/-- **Product consistency** (`eq:supp-open-product-consistency`): for `r ≥ 1` there is `C`,
independent of the mesh, with
`‖𝓘_h(u_h w_h) - (𝓘_h u_h)(𝓘_h w_h)‖²_{H^r} ≤ C h² ‖u_h‖²_{r+1,h} ‖w_h‖²_{r+1,h}`. -/
theorem product_consistency (r : ℕ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (u w : Grid N → ℂ),
      trigSobSq r ⇑(interp (u * w) - interp u * interp w) ≤
        C * ((N : ℝ) ^ 2)⁻¹ * sobSq (r + 1) u * sobSq (r + 1) w := by
  obtain ⟨C1, hC1, hE⟩ := sampling_error r 1 (by omega)
  obtain ⟨K, hK, hP⟩ := trigSobSq_interp_mul_le (r + 1) (by omega)
  set c := ((π / 2) ^ 2) ^ (r + 1)
  refine ⟨C1 * K * c * c, by positivity, fun N _ u w => ?_⟩
  set F := interp u * interp w
  have hFsum : Summable fun n => trigWeight (r + 1) n * ‖mFourierCoeff ⇑F n‖ ^ 2 := by
    classical
    refine summable_of_ne_finset_zero (s := (univ : Finset (Grid N × Grid N)).image
      (fun p => freqVec p.1 + freqVec p.2)) fun n hn => ?_
    rw [mFourierCoeff_interp_mul]
    have : ∀ p : Grid N × Grid N, ¬ (freqVec p.1 + freqVec p.2 = n) := fun p hp =>
      hn (mem_image.mpr ⟨p, mem_univ _, hp⟩)
    simp [this]
  obtain ⟨-, hb⟩ := hE N F hFsum
  rw [pow_one] at hb
  have e : interp (u * w) = proj N ⇑F := by rw [proj, sample_interp_mul]
  rw [e]
  have h1 := hP N u w
  have h2 := trigSobSq_interp_le (r + 1) u
  have h3 := trigSobSq_interp_le (r + 1) w
  have hNi : 0 ≤ ((N : ℝ) ^ 2)⁻¹ := by positivity
  have t0 : 0 ≤ trigSobSq (r + 1) ⇑(interp u) := tsum_nonneg fun n =>
    mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _)
  have t1 : 0 ≤ trigSobSq (r + 1) ⇑(interp w) := tsum_nonneg fun n =>
    mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _)
  have s0 := sobSq_nonneg (r + 1) u
  have s1 := sobSq_nonneg (r + 1) w
  have hc0 : 0 ≤ c := by positivity
  calc trigSobSq r ⇑(proj N ⇑F - F) ≤ C1 * ((N : ℝ) ^ 2)⁻¹ * trigSobSq (r + 1) ⇑F := hb
    _ ≤ C1 * ((N : ℝ) ^ 2)⁻¹ * (K * trigSobSq (r + 1) ⇑(interp u) *
          trigSobSq (r + 1) ⇑(interp w)) := by gcongr
    _ ≤ C1 * ((N : ℝ) ^ 2)⁻¹ * (K * (c * sobSq (r + 1) u) * (c * sobSq (r + 1) w)) := by
        gcongr
    _ = C1 * K * c * c * ((N : ℝ) ^ 2)⁻¹ * sobSq (r + 1) u * sobSq (r + 1) w := by ring

end Sampling

end RenewalGeometry.PeriodicGridSobolev
