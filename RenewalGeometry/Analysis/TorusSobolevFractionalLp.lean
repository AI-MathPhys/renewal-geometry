/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.TorusSobolevL4

/-!
# The embedding `H^s(𝕋^d) ⊂ L^p(𝕋^d)` for `s > d(1/2 - 1/p)`

Generic infrastructure (no renewal notions) for the `L^{4+δ}` clause of `prop:sobolev-bosonic`
(Einstein–Standard-Model action-closure manuscript): on `𝕋⁴`, `H^{1+σ} ⊂ L^{4+δ}` for
`δ = min σ 1`.

The proof is a Littlewood–Paley-free dyadic argument on the Fourier side.  A trigonometric
polynomial `P` is split into the blocks `P_k` carried by the shells `4^k ≤ ⟨n⟩² < 4^{k+1}` (a
telescoping sum over the sublevel sets of the weight `⟨n⟩² = sobWeight n`).  For a block with `N_k`
frequencies and `ℓ²` mass `E_k`:
`‖P_k‖_∞ ≤ (N_k E_k)^{1/2}` (Cauchy–Schwarz), `‖P_k‖²_{L²} = E_k` (Parseval), hence
`‖P_k‖_{L^p} ≤ ‖P_k‖_∞^{1-2/p} ‖P_k‖_{L²}^{2/p} = N_k^{1/2-1/p} E_k^{1/2}`.
With `N_k ≤ 2^{(k+3)d}` (the shell lies in the box `[-2^{k+1}, 2^{k+1}]^d`) and
`E_k ≤ 4^{-ks}‖P‖²_{H^s}`, Minkowski gives
`‖P‖_{L^p} ≤ Σ_k 2^{3da} (2^{da-s})^k ‖P‖_{H^s}`, `a = 1/2 - 1/p`, a convergent geometric series
when `s > da`.  General `f` follow by Fourier truncation and Fatou.

* `eLpNorm_trigPoly_le_card`: `‖P‖_{L^p} ≤ (#S)^{1/2-1/p} ‖c‖_{ℓ²(S)}` for `P` supported on `S`;
* `eLpNorm_trigPoly_le_sob`: `‖P‖_{L^p} ≤ C_{p,s} ‖P‖_{H^s}`;
* **`eLpNorm_le_of_memH_Lp`** (`H^s ⊂ L^p`, `s > d(1/2 - 1/p)`, `p ≥ 2`);
* **`eLpNorm_four_add_le_of_memH`** (`H^{1+σ}(𝕋⁴) ⊂ L^{4+δ}`, `δ = min σ 1`).
-/

open Finset Filter Topology MeasureTheory UnitAddTorus
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.TorusSobolev
namespace FracLp

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

noncomputable section

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

variable {d : Type*} [Fintype d]

/-! ### One block -/

theorem norm_trigPoly_apply_le (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (x : UnitAddTorus d) :
    ‖trigPoly S c x‖ ≤ Real.sqrt (#S) * Real.sqrt (∑ n ∈ S, ‖c n‖ ^ 2) := by
  have h1 : ‖trigPoly S c x‖ ≤ ∑ n ∈ S, ‖c n‖ := by
    unfold trigPoly
    rw [ContinuousMap.coe_sum, Finset.sum_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [ContinuousMap.coe_smul, Pi.smul_apply, norm_smul]
    have : ‖mFourier n x‖ ≤ 1 := (ContinuousMap.norm_coe_le_norm _ x).trans mFourier_norm.le
    calc ‖c n‖ * ‖mFourier n x‖ ≤ ‖c n‖ * 1 := by gcongr
      _ = ‖c n‖ := mul_one _
  refine h1.trans ?_
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.le_sqrt_of_sq_le ?_
  exact sq_sum_le_card_mul_sum_sq

theorem integral_norm_sq_trigPoly (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) :
    ∫ x, ‖trigPoly S c x‖ ^ 2 = ∑ n ∈ S, ‖c n‖ ^ 2 := by
  classical
  have h := hasSum_sq_mFourierCoeff ((trigPoly S c).toLp 2 volume ℂ)
  have e1 : ∀ k, ‖mFourierCoeff (⇑((trigPoly S c).toLp 2 volume ℂ)) k‖ ^ 2 =
      if k ∈ S then ‖c k‖ ^ 2 else 0 := fun k => by
    rw [mFourierCoeff_toLp, mFourierCoeff_trigPoly]
    split_ifs <;> simp
  simp only [e1] at h
  have e2 : ∫ t, ‖((trigPoly S c).toLp 2 volume ℂ) t‖ ^ 2 = ∫ x, ‖trigPoly S c x‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)
      (trigPoly S c)] with x hx
    rw [hx]
  rw [e2] at h
  rw [← h.tsum_eq, tsum_eq_sum (s := S) (fun k hk => if_neg hk)]
  exact Finset.sum_congr rfl fun k hk => if_pos hk

/-- `eLpNorm` of a continuous function for a real exponent `p ≥ 1`. -/
theorem eLpNorm_rpow_eq (P : C(UnitAddTorus d, ℂ)) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm P (ENNReal.ofReal p) volume = ENNReal.ofReal ((∫ x, ‖P x‖ ^ p) ^ (1 / p)) := by
  have hp0 : 0 < p := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  have hint : Integrable (fun x => ‖P x‖ ^ p) volume :=
    ((continuous_norm.comp P.continuous).rpow_const fun x => Or.inr hp0.le).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have e : ∀ x, ‖P x‖ₑ ^ p = ENNReal.ofReal (‖P x‖ ^ p) := by
    intro x
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by positivity),
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun x => by positivity) (by positivity)]

/-- **One block**: `‖P‖_{L^p} ≤ (#S)^{1/2-1/p} ‖c‖_{ℓ²(S)}` for `P` supported on `S`, `p ≥ 2`. -/
theorem eLpNorm_trigPoly_le_card (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) {p : ℝ} (hp : 2 ≤ p) :
    eLpNorm (trigPoly S c) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((#S : ℝ) ^ (1 / 2 - 1 / p) * Real.sqrt (∑ n ∈ S, ‖c n‖ ^ 2)) := by
  have hp0 : 0 < p := by linarith
  rw [eLpNorm_rpow_eq _ (by linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  set N : ℝ := (#S : ℝ)
  set E : ℝ := ∑ n ∈ S, ‖c n‖ ^ 2
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hE : 0 ≤ E := Finset.sum_nonneg fun n _ => sq_nonneg _
  set M := Real.sqrt N * Real.sqrt E
  have hM : 0 ≤ M := by positivity
  have hpt : ∀ x, ‖trigPoly S c x‖ ^ p ≤ M ^ (p - 2) * ‖trigPoly S c x‖ ^ 2 := by
    intro x
    have h0 := norm_nonneg (trigPoly S c x)
    have hle := norm_trigPoly_apply_le S c x
    rw [show p = (p - 2) + 2 by ring, Real.rpow_add' h0 (by linarith),
      show (p - 2) + 2 - 2 = p - 2 by ring]
    rw [show ‖trigPoly S c x‖ ^ ((2 : ℝ)) = ‖trigPoly S c x‖ ^ (2 : ℕ) by norm_cast]
    gcongr
  have hint1 : Integrable (fun x => ‖trigPoly S c x‖ ^ p) volume :=
    ((continuous_norm.comp (trigPoly S c).continuous).rpow_const fun x =>
      Or.inr hp0.le).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (fun x => M ^ (p - 2) * ‖trigPoly S c x‖ ^ 2) volume :=
    (continuous_const.mul ((continuous_norm.comp (trigPoly S c).continuous).pow 2)
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI : ∫ x, ‖trigPoly S c x‖ ^ p ≤ M ^ (p - 2) * E := by
    have hE' : E = ∫ x, ‖trigPoly S c x‖ ^ 2 := (integral_norm_sq_trigPoly S c).symm
    rw [hE', ← integral_const_mul]
    exact integral_mono hint1 hint2 hpt
  have hI0 : 0 ≤ ∫ x, ‖trigPoly S c x‖ ^ p := integral_nonneg fun x => by positivity
  calc (∫ x, ‖trigPoly S c x‖ ^ p) ^ (1 / p) ≤ (M ^ (p - 2) * E) ^ (1 / p) :=
        Real.rpow_le_rpow hI0 hI (by positivity)
    _ = N ^ (1 / 2 - 1 / p) * Real.sqrt E := by
        have hM' : M = (N * E) ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow hN hE, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
        rw [hM', ← Real.rpow_mul (by positivity), Real.mul_rpow hN hE, mul_assoc,
          ← Real.rpow_add_one' hE (by
            have : 1 / 2 * (p - 2) + 1 = p / 2 := by ring
            rw [this]; positivity),
          Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hN,
          ← Real.rpow_mul hE, Real.sqrt_eq_rpow]
        congr 2 <;> field_simp <;> ring

/-! ### Dyadic decomposition -/

/-- The sublevel set `{n ∈ S : ⟨n⟩² < 4^k}`. -/
def subl (S : Finset (d → ℤ)) (k : ℕ) : Finset (d → ℤ) :=
  S.filter fun n => sobWeight n < (4 : ℝ) ^ k

theorem subl_zero (S : Finset (d → ℤ)) : subl S 0 = ∅ := by
  ext n
  simp only [subl, Finset.mem_filter, pow_zero, Finset.notMem_empty, iff_false, not_and, not_lt]
  exact fun _ => one_le_sobWeight n

theorem subl_mono (S : Finset (d → ℤ)) {k l : ℕ} (h : k ≤ l) : subl S k ⊆ subl S l := by
  intro n hn
  simp only [subl, Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.trans_le (pow_le_pow_right₀ (by norm_num) h)⟩

theorem exists_subl_eq (S : Finset (d → ℤ)) : ∃ K, subl S K = S := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ n ∈ S, sobWeight n < (4 : ℝ) ^ K := by
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (∑ n ∈ S, sobWeight n) (by norm_num : (1 : ℝ) < 4)
    refine ⟨K, fun n hn => lt_of_le_of_lt ?_ hK⟩
    exact Finset.single_le_sum (f := sobWeight) (fun m _ => (sobWeight_pos m).le) hn
  exact ⟨K, Finset.filter_true_of_mem hK⟩

theorem trigPoly_sub_of_subset {T U : Finset (d → ℤ)} (hUT : U ⊆ T) (c : (d → ℤ) → ℂ) :
    trigPoly T c - trigPoly U c = trigPoly (T \ U) c := by
  unfold trigPoly
  rw [← Finset.sum_sdiff hUT, add_sub_cancel_right]

/-- The dyadic blocks `P_k`, supported on `4^k ≤ ⟨n⟩² < 4^{k+1}`. -/
def block (S : Finset (d → ℤ)) (k : ℕ) : Finset (d → ℤ) := subl S (k + 1) \ subl S k

theorem trigPoly_eq_sum_blocks (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) :
    ∃ K, trigPoly S c = ∑ k ∈ range K, trigPoly (block S k) c := by
  obtain ⟨K, hK⟩ := exists_subl_eq S
  refine ⟨K, ?_⟩
  have h := Finset.sum_range_sub (fun k => trigPoly (subl S k) c) K
  rw [hK, subl_zero] at h
  have h0 : trigPoly (∅ : Finset (d → ℤ)) c = 0 := by simp [trigPoly]
  rw [h0, sub_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact trigPoly_sub_of_subset (subl_mono S (Nat.le_succ k)) c

theorem mem_box_of_sobWeight_lt {n : d → ℤ} {R : ℕ} (h : sobWeight n < (R : ℝ) ^ 2) :
    n ∈ box R := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h1 := one_add_sq_le_sobWeight n i
  have h2 : ((n i : ℝ)) ^ 2 < (R : ℝ) ^ 2 := by linarith
  have h3 : |(n i : ℝ)| < R := abs_lt_of_sq_lt_sq h2 (Nat.cast_nonneg R)
  rw [abs_lt] at h3
  constructor
  · have : (-(R : ℤ) : ℝ) < n i := by push_cast; linarith
    exact_mod_cast this.le
  · have : ((n i : ℤ) : ℝ) < (R : ℤ) := by push_cast; linarith
    exact_mod_cast this.le

theorem card_box (R : ℕ) : #(box (d := d) R) = (2 * R + 1) ^ Fintype.card d := by
  classical
  rw [box, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Int.card_Icc]
  congr 1
  omega

/-- The block `k` has at most `2^{(k+3)d}` frequencies. -/
theorem card_block_le (S : Finset (d → ℤ)) (k : ℕ) :
    (#(block S k) : ℝ) ≤ (2 : ℝ) ^ ((k + 3) * Fintype.card d) := by
  have hsub : block S k ⊆ box (2 ^ (k + 1)) := by
    intro n hn
    simp only [block, subl, Finset.mem_sdiff, Finset.mem_filter] at hn
    refine mem_box_of_sobWeight_lt ?_
    have : (4 : ℝ) ^ (k + 1) = (((2 ^ (k + 1) : ℕ)) : ℝ) ^ 2 := by
      push_cast; rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
    rw [← this]; exact hn.1.2
  have h1 : (#(block S k) : ℝ) ≤ #(box (d := d) (2 ^ (k + 1))) := by
    exact_mod_cast Finset.card_le_card hsub
  refine h1.trans ?_
  rw [card_box, pow_mul]
  push_cast
  gcongr
  have h2 : (1 : ℝ) ≤ 2 * 2 ^ (k + 1) := by
    have : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
    linarith
  calc (2 : ℝ) * 2 ^ (k + 1) + 1 ≤ 2 * 2 ^ (k + 1) + 2 * 2 ^ (k + 1) := by gcongr
    _ = 2 ^ (k + 3) := by ring

/-! ### The `H^s` bound -/

/-- The embedding constant `2^{3da} / (1 - 2^{da - s})`, `a = 1/2 - 1/p`. -/
def lpConst (d : Type*) [Fintype d] (p s : ℝ) : ℝ :=
  (2 : ℝ) ^ (3 * ((Fintype.card d : ℝ) * (1 / 2 - 1 / p))) *
    (1 - (2 : ℝ) ^ ((Fintype.card d : ℝ) * (1 / 2 - 1 / p) - s))⁻¹

theorem geom_partial_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (K : ℕ) :
    ∑ k ∈ range K, r ^ k ≤ (1 - r)⁻¹ :=
  ((summable_geometric_of_lt_one h0 h1).sum_le_tsum (range K) fun k _ => pow_nonneg h0 k).trans_eq
    (tsum_geometric_of_lt_one h0 h1)

/-- The `ℓ²` mass of the block `k` is at most `4^{-ks}‖c‖²_{H^s}`. -/
theorem block_mass_le {s : ℝ} (hs : 0 ≤ s) (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (k : ℕ) :
    ∑ n ∈ block S k, ‖c n‖ ^ 2 ≤
      (2 : ℝ) ^ (-(2 * k * s)) * ∑ n ∈ S, sobWeight n ^ s * ‖c n‖ ^ 2 := by
  have hsub : block S k ⊆ S := fun n hn => by
    simp only [block, subl, Finset.mem_sdiff, Finset.mem_filter] at hn; exact hn.1.1
  calc ∑ n ∈ block S k, ‖c n‖ ^ 2
      ≤ ∑ n ∈ block S k, (2 : ℝ) ^ (-(2 * k * s)) * (sobWeight n ^ s * ‖c n‖ ^ 2) := by
        refine Finset.sum_le_sum fun n hn => ?_
        simp only [block, subl, Finset.mem_sdiff, Finset.mem_filter, not_and, not_lt] at hn
        have hw : (4 : ℝ) ^ k ≤ sobWeight n := hn.2 hn.1.1
        have h4 : (2 : ℝ) ^ (2 * (k : ℝ) * s) ≤ sobWeight n ^ s := by
          have e : (2 : ℝ) ^ (2 * (k : ℝ) * s) = ((4 : ℝ) ^ k) ^ s := by
            rw [Real.rpow_mul (by norm_num)]
            congr 1
            rw [show (2 : ℝ) * k = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
              pow_mul]
            norm_num
          rw [e]
          exact Real.rpow_le_rpow (by positivity) hw hs
        have hpos : 0 < (2 : ℝ) ^ (2 * (k : ℝ) * s) := by positivity
        have e2 : (2 : ℝ) ^ (-(2 * (k : ℝ) * s)) * (2 : ℝ) ^ (2 * (k : ℝ) * s) = 1 := by
          rw [Real.rpow_neg (by norm_num), inv_mul_cancel₀ hpos.ne']
        calc ‖c n‖ ^ 2 = (2 : ℝ) ^ (-(2 * (k : ℝ) * s)) *
              ((2 : ℝ) ^ (2 * (k : ℝ) * s) * ‖c n‖ ^ 2) := by rw [← mul_assoc, e2, one_mul]
          _ ≤ _ := by gcongr
    _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
          mul_nonneg (sobWeight_rpow_nonneg n s) (sq_nonneg _)) (by positivity)

/-- **`H^s` bound for trigonometric polynomials**: `‖P‖_{L^p} ≤ C_{p,s} ‖P‖_{H^s}` for `p ≥ 2` and
`s > d(1/2 - 1/p)`. -/
theorem eLpNorm_trigPoly_le_sob {p s : ℝ} (hp : 2 ≤ p)
    (hs : (Fintype.card d : ℝ) * (1 / 2 - 1 / p) < s) (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) :
    eLpNorm (trigPoly S c) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (lpConst d p s * Real.sqrt (∑ n ∈ S, sobWeight n ^ s * ‖c n‖ ^ 2)) := by
  set D : ℝ := (Fintype.card d : ℝ)
  set a : ℝ := 1 / 2 - 1 / p
  have hp0 : 0 < p := by linarith
  have ha : 0 ≤ a := by
    have : 1 / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp
    simp only [a]; linarith
  have hD : 0 ≤ D := Nat.cast_nonneg _
  have hDa : 0 ≤ D * a := mul_nonneg hD ha
  have hs0 : 0 ≤ s := hDa.trans hs.le
  set r : ℝ := (2 : ℝ) ^ (D * a - s)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set H : ℝ := ∑ n ∈ S, sobWeight n ^ s * ‖c n‖ ^ 2
  have hH : 0 ≤ H := Finset.sum_nonneg fun n _ => mul_nonneg (sobWeight_rpow_nonneg n s)
    (sq_nonneg _)
  obtain ⟨K, hK⟩ := trigPoly_eq_sum_blocks S c
  rw [hK, ContinuousMap.coe_sum]
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  refine (eLpNorm_sum_le (fun k _ => (trigPoly (block S k) c).continuous.aestronglyMeasurable)
    hp1).trans ?_
  -- each block
  have hblock : ∀ k, eLpNorm (trigPoly (block S k) c) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((2 : ℝ) ^ (3 * (D * a)) * Real.sqrt H * r ^ k) := by
    intro k
    refine (eLpNorm_trigPoly_le_card _ c hp).trans (ENNReal.ofReal_le_ofReal ?_)
    have hN := card_block_le S k
    have hN' : ((#(block S k) : ℝ)) ^ a ≤ (2 : ℝ) ^ (((k : ℝ) + 3) * D * a) := by
      calc ((#(block S k) : ℝ)) ^ a ≤ ((2 : ℝ) ^ ((k + 3) * Fintype.card d)) ^ a :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hN ha
        _ = (2 : ℝ) ^ (((k : ℝ) + 3) * D * a) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            congr 1
            push_cast
            simp only [D]
    have hE := block_mass_le hs0 S c k
    have hE' : Real.sqrt (∑ n ∈ block S k, ‖c n‖ ^ 2) ≤
        (2 : ℝ) ^ (-((k : ℝ) * s)) * Real.sqrt H := by
      calc Real.sqrt (∑ n ∈ block S k, ‖c n‖ ^ 2)
          ≤ Real.sqrt ((2 : ℝ) ^ (-(2 * (k : ℝ) * s)) * H) := Real.sqrt_le_sqrt hE
        _ = (2 : ℝ) ^ (-((k : ℝ) * s)) * Real.sqrt H := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
            ring_nf
    calc ((#(block S k) : ℝ)) ^ (1 / 2 - 1 / p) * Real.sqrt (∑ n ∈ block S k, ‖c n‖ ^ 2)
        ≤ (2 : ℝ) ^ (((k : ℝ) + 3) * D * a) * ((2 : ℝ) ^ (-((k : ℝ) * s)) * Real.sqrt H) :=
          mul_le_mul hN' hE' (Real.sqrt_nonneg _) (by positivity)
      _ = (2 : ℝ) ^ (3 * (D * a)) * Real.sqrt H * r ^ k := by
          rw [show r ^ k = (2 : ℝ) ^ ((k : ℝ) * (D * a - s)) by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]]
          have e1 : (2 : ℝ) ^ (((k : ℝ) + 3) * D * a) * (2 : ℝ) ^ (-((k : ℝ) * s)) =
              (2 : ℝ) ^ (3 * (D * a)) * (2 : ℝ) ^ ((k : ℝ) * (D * a - s)) := by
            rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
            ring_nf
          calc (2 : ℝ) ^ (((k : ℝ) + 3) * D * a) * ((2 : ℝ) ^ (-((k : ℝ) * s)) * Real.sqrt H)
              = ((2 : ℝ) ^ (((k : ℝ) + 3) * D * a) * (2 : ℝ) ^ (-((k : ℝ) * s))) *
                Real.sqrt H := by ring
            _ = _ := by rw [e1]; ring
  calc ∑ k ∈ range K, eLpNorm (⇑(trigPoly (block S k) c)) (ENNReal.ofReal p) volume
      ≤ ∑ k ∈ range K, ENNReal.ofReal ((2 : ℝ) ^ (3 * (D * a)) * Real.sqrt H * r ^ k) :=
        Finset.sum_le_sum fun k _ => hblock k
    _ = ENNReal.ofReal (∑ k ∈ range K, (2 : ℝ) ^ (3 * (D * a)) * Real.sqrt H * r ^ k) :=
        (ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity).symm
    _ ≤ ENNReal.ofReal (lpConst d p s * Real.sqrt H) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        calc (2 : ℝ) ^ (3 * (D * a)) * Real.sqrt H * ∑ k ∈ range K, r ^ k
            ≤ (2 : ℝ) ^ (3 * (D * a)) * Real.sqrt H * (1 - r)⁻¹ :=
              mul_le_mul_of_nonneg_left (geom_partial_le hr0 hr1 K) (by positivity)
          _ = lpConst d p s * Real.sqrt H := by
              simp only [lpConst]; ring

theorem lpConst_nonneg {p s : ℝ} (hp : 2 ≤ p)
    (hs : (Fintype.card d : ℝ) * (1 / 2 - 1 / p) < s) : 0 ≤ lpConst d p s := by
  unfold lpConst
  have : (2 : ℝ) ^ ((Fintype.card d : ℝ) * (1 / 2 - 1 / p) - s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have : 0 < 1 - (2 : ℝ) ^ ((Fintype.card d : ℝ) * (1 / 2 - 1 / p) - s) := by linarith
  positivity

/-- **Sobolev embedding `H^s(𝕋^d) ⊂ L^p(𝕋^d)`** for `p ≥ 2`, `s > d(1/2 - 1/p)`:
`‖f‖_{L^p} ≤ C_{p,s} ‖f‖_{H^s}`. -/
theorem eLpNorm_le_of_memH_Lp {p s : ℝ} (hp : 2 ≤ p)
    (hs : (Fintype.card d : ℝ) * (1 / 2 - 1 / p) < s) (f : L²(UnitAddTorus d)) (hf : MemH s f) :
    eLpNorm f (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (lpConst d p s * sobNorm s f) := by
  have hL2 := tendsto_fourierTrunc f
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hL2).exists_seq_tendsto_ae
  have hbound : ∀ j, eLpNorm (⇑((fourierTrunc (ns j) f).toLp 2 volume ℂ)) (ENNReal.ofReal p)
      volume ≤ ENNReal.ofReal (lpConst d p s * sobNorm s f) := by
    intro j
    rw [eLpNorm_congr_ae (ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ) _)]
    refine (eLpNorm_trigPoly_le_sob hp hs _ _).trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (lpConst_nonneg hp hs)
    exact hf.sum_le_tsum _ (fun n _ => coeffSobSq_term_nonneg s _ n)
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun j => Lp.aestronglyMeasurable _) (⇑f) hae).trans ?_
  exact liminf_le_of_frequently_le' (Frequently.of_forall hbound)

theorem memLp_of_memH_Lp {p s : ℝ} (hp : 2 ≤ p)
    (hs : (Fintype.card d : ℝ) * (1 / 2 - 1 / p) < s) (f : L²(UnitAddTorus d)) (hf : MemH s f) :
    MemLp f (ENNReal.ofReal p) volume :=
  ⟨Lp.aestronglyMeasurable f, lt_of_le_of_lt (eLpNorm_le_of_memH_Lp hp hs f hf)
    ENNReal.ofReal_lt_top⟩

/-- The exponent condition on `𝕋⁴`: `4(1/2 - 1/(4+δ)) < 1 + σ` for `δ = min σ 1`. -/
theorem exponent_four (σ : ℝ) (hσ : 0 < σ) :
    (Fintype.card (Fin 4) : ℝ) * (1 / 2 - 1 / (4 + min σ 1)) < 1 + σ := by
  rw [Fintype.card_fin]
  have hδ0 : 0 < min σ 1 := lt_min hσ one_pos
  have hδσ : min σ 1 ≤ σ := min_le_left _ _
  have hδ1 : min σ 1 ≤ 1 := min_le_right _ _
  have hpos : 0 < 4 + min σ 1 := by linarith
  have e : ((4 : ℕ) : ℝ) * (1 / 2 - 1 / (4 + min σ 1)) = 2 - 4 / (4 + min σ 1) := by
    push_cast; field_simp; ring
  rw [e]
  have h4 : 4 / (4 + min σ 1) > 1 - σ := by
    rw [gt_iff_lt, lt_div_iff₀ hpos]
    nlinarith
  linarith

/-- **`H^{1+σ}(𝕋⁴) ⊂ L^{4+δ}(𝕋⁴)`** with `δ = min σ 1 > 0` (`prop:sobolev-bosonic`: a uniform
`H^{1+σ}` bound on the Higgs field gives a uniform `L^{4+δ}` bound). -/
theorem eLpNorm_four_add_le_of_memH {σ : ℝ} (hσ : 0 < σ) (f : L²(UnitAddTorus (Fin 4)))
    (hf : MemH (1 + σ) f) :
    eLpNorm f (ENNReal.ofReal (4 + min σ 1)) volume ≤
      ENNReal.ofReal (lpConst (Fin 4) (4 + min σ 1) (1 + σ) * sobNorm (1 + σ) f) :=
  eLpNorm_le_of_memH_Lp (by have := lt_min hσ one_pos; linarith) (exponent_four σ hσ) f hf

/-- Non-vacuity: a monomial on `𝕋⁴` with the `H^{3/2}` bound lies in `L^{9/2}`. -/
example (m : Fin 4 → ℤ) :
    eLpNorm ((mFourier m).toLp 2 volume ℂ) (ENNReal.ofReal (4 + min (1 / 2) 1)) volume ≤
      ENNReal.ofReal (lpConst (Fin 4) (4 + min (1 / 2) 1) (1 + 1 / 2) *
        sobNorm (1 + 1 / 2) ⇑((mFourier m).toLp 2 volume ℂ)) := by
  refine eLpNorm_four_add_le_of_memH (by norm_num) _ ?_
  have := memH_mFourier (d := Fin 4) (1 + 1 / 2) m
  unfold MemH CoeffMemH at this ⊢
  simp_rw [mFourierCoeff_toLp]
  exact this

end

end FracLp
end RenewalGeometry.TorusSobolev
