/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.TorusSobolevEmbedding

/-!
# The embedding `H^s(𝕋^d) ⊂ L⁴(𝕋^d)` for `s > d/4`

Generic infrastructure (no renewal notions) for `prop:sobolev-bosonic` of the
Einstein–Standard-Model action-closure manuscript: on `𝕋⁴` an `H^{1+σ}` bound (`σ > 0`) controls
the `L⁴` norm, which is what the products `A ∧ A` and `ρ_H(A) H` need.

The proof is on the Fourier side and uses only Cauchy–Schwarz.  For a trigonometric polynomial
`P = Σ_{n ∈ S} c_n e_n`, `‖P‖⁴_{L⁴} = ‖P²‖²_{L²} = Σ_k |q_k|²` with
`q_k = Σ_{m + m' = k} c_m c_{m'}` (Parseval for `P²`), and Cauchy–Schwarz on each fibre with the
splitting `|c_m c_{m'}| = (⟨m⟩^s |c_m| ⟨m'⟩^s |c_{m'}|) (⟨m⟩^{-s} ⟨m'⟩^{-s})` together with
`⟨m⟩^{-2s} ⟨m'⟩^{-2s} ≤ (⟨m⟩^{-4s} + ⟨m'⟩^{-4s}) / 2` gives
`‖P‖⁴_{L⁴} ≤ Z_{2s} ‖P‖⁴_{H^s}`, `Z_{2s} = Σ_n ⟨n⟩^{-4s} < ∞` exactly when `s > d/4`.
General `f` follow by truncation and Fatou.

(Weights: `⟨n⟩² = sobWeight n = 1 + 4π²|n|²`, so `sobWeight n ^ s = ⟨n⟩^{2s}`.)

* `trigPoly`, `mFourierCoeff_trigPoly_mul_self`, `integral_norm_pow_four_trigPoly`;
* `integral_norm_pow_four_trigPoly_le`: `∫ |P|⁴ ≤ Z (Σ_S ⟨n⟩^{2s} |c_n|²)²`;
* `eLpNorm_four_le_of_memH` (**`H^s ⊂ L⁴`, `s > d/4`**):
  `‖f‖_{L⁴} ≤ Z^{1/4} ‖f‖_{H^s}` for every `f ∈ L²(𝕋^d)` with finite `H^s` norm;
* `tendsto_eLpNorm_four_of_H` : strong `H^s` convergence implies strong `L⁴` convergence.
-/

open Finset Filter Topology MeasureTheory UnitAddTorus
open scoped BigOperators Real ENNReal InnerProductSpace

namespace RenewalGeometry.TorusSobolev

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

noncomputable section

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

variable {d : Type*} [Fintype d]

/-! ### Trigonometric polynomials and their squares -/

/-- The trigonometric polynomial `Σ_{n ∈ S} c_n e_n`. -/
def trigPoly (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) : C(UnitAddTorus d, ℂ) :=
  ∑ n ∈ S, c n • mFourier n

/-- Fourier coefficients of a finite combination of monomials. -/
theorem mFourierCoeff_finset_sum {ι : Type*} (T : Finset ι) (a : ι → ℂ) (v : ι → d → ℤ)
    (k : d → ℤ) :
    mFourierCoeff ⇑(∑ j ∈ T, a j • mFourier (v j)) k = ∑ j ∈ T, if v j = k then a j else 0 := by
  classical
  rw [mFourierCoeff_eq_inner, map_sum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_right]
  have ho := orthonormal_iff_ite.mp (orthonormal_mFourier (d := d)) k (v j)
  rw [ho]
  by_cases h : v j = k
  · rw [if_pos h, if_pos h.symm, mul_one]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

theorem mFourierCoeff_trigPoly (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (k : d → ℤ) :
    mFourierCoeff ⇑(trigPoly S c) k = if k ∈ S then c k else 0 := by
  classical
  have := mFourierCoeff_finset_sum S c id k
  simp only [id] at this
  unfold trigPoly
  rw [this, Finset.sum_ite_eq']

/-- The coefficients `q_k = Σ_{(m, m') ∈ S², m + m' = k} c_m c_{m'}` of `P²`. -/
def convSq (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (k : d → ℤ) : ℂ :=
  ∑ p ∈ S ×ˢ S, if p.1 + p.2 = k then c p.1 * c p.2 else 0

theorem trigPoly_mul_self (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) :
    trigPoly S c * trigPoly S c = ∑ p ∈ S ×ˢ S, (c p.1 * c p.2) • mFourier (p.1 + p.2) := by
  unfold trigPoly
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_congr rfl fun p _ => ?_
  ext x
  simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul, mFourier_add]
  ring

theorem mFourierCoeff_trigPoly_mul_self (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (k : d → ℤ) :
    mFourierCoeff ⇑(trigPoly S c * trigPoly S c) k = convSq S c k := by
  rw [trigPoly_mul_self, mFourierCoeff_finset_sum (S ×ˢ S) (fun p => c p.1 * c p.2)
    (fun p => p.1 + p.2) k]
  rfl

/-- **`‖P‖⁴_{L⁴} = Σ_k |q_k|²`** (Parseval for `P²`). -/
theorem hasSum_convSq (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) :
    HasSum (fun k => ‖convSq S c k‖ ^ 2) (∫ x, ‖trigPoly S c x‖ ^ 4) := by
  have h := hasSum_sq_mFourierCoeff ((trigPoly S c * trigPoly S c).toLp 2 volume ℂ)
  have e1 : ∀ k, mFourierCoeff (⇑((trigPoly S c * trigPoly S c).toLp 2 volume ℂ)) k =
      convSq S c k := fun k => by rw [mFourierCoeff_toLp, mFourierCoeff_trigPoly_mul_self]
  simp only [e1] at h
  have e2 : ∫ t, ‖((trigPoly S c * trigPoly S c).toLp 2 volume ℂ) t‖ ^ 2 =
      ∫ x, ‖trigPoly S c x‖ ^ 4 := by
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)
      (trigPoly S c * trigPoly S c)] with x hx
    rw [hx]
    simp only [ContinuousMap.mul_apply, norm_mul]
    ring
  rwa [e2] at h

/-! ### The Cauchy–Schwarz bound for `Σ_k |q_k|²` -/

/-- Summability of `⟨n⟩^{-4s}` for `s > d/4`. -/
theorem summable_sobWeight_rpow_neg_two {s : ℝ} (hs : (Fintype.card d : ℝ) / 4 < s) :
    Summable fun n : d → ℤ => sobWeight n ^ (-(2 * s)) :=
  summable_sobWeight_rpow_neg (by linarith)

/-- The `L⁴` constant `Z_{2s} = Σ_n ⟨n⟩^{-4s}`. -/
def l4Const (d : Type*) [Fintype d] (s : ℝ) : ℝ := ∑' n : d → ℤ, sobWeight n ^ (-(2 * s))

theorem l4Const_nonneg (s : ℝ) : 0 ≤ l4Const d s :=
  tsum_nonneg fun n => sobWeight_rpow_nonneg n _

/-- Sum over a fibre `{m + m' = k}` of a function of one coordinate is at most the full series. -/
theorem sum_fibre_fst_le {s : ℝ} (hs : (Fintype.card d : ℝ) / 4 < s) (S : Finset (d → ℤ))
    (k : d → ℤ) :
    ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 + p.2 = k), sobWeight p.1 ^ (-(2 * s)) ≤ l4Const d s := by
  classical
  rw [← Finset.sum_image (f := fun m => sobWeight m ^ (-(2 * s))) (g := Prod.fst)]
  · exact (summable_sobWeight_rpow_neg_two hs).sum_le_tsum _
      (fun _ _ => sobWeight_rpow_nonneg _ _)
  · intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    have h2 : x.2 = y.2 := by
      have := hx.2.trans hy.2.symm
      rw [hxy] at this
      exact add_left_cancel this
    exact Prod.ext hxy h2

theorem sum_fibre_snd_le {s : ℝ} (hs : (Fintype.card d : ℝ) / 4 < s) (S : Finset (d → ℤ))
    (k : d → ℤ) :
    ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 + p.2 = k), sobWeight p.2 ^ (-(2 * s)) ≤ l4Const d s := by
  classical
  rw [← Finset.sum_image (f := fun m => sobWeight m ^ (-(2 * s))) (g := Prod.snd)]
  · exact (summable_sobWeight_rpow_neg_two hs).sum_le_tsum _
      (fun _ _ => sobWeight_rpow_nonneg _ _)
  · intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    have h1 : x.1 = y.1 := by
      have := hx.2.trans hy.2.symm
      rw [hxy] at this
      exact add_right_cancel this
    exact Prod.ext h1 hxy

/-- Pointwise Cauchy–Schwarz on one fibre:
`|q_k|² ≤ Z_{2s} Σ_{m + m' = k} ⟨m⟩^{2s}|c_m|² ⟨m'⟩^{2s}|c_{m'}|²`. -/
theorem norm_convSq_sq_le {s : ℝ} (hs : (Fintype.card d : ℝ) / 4 < s) (S : Finset (d → ℤ))
    (c : (d → ℤ) → ℂ) (k : d → ℤ) :
    ‖convSq S c k‖ ^ 2 ≤ l4Const d s * ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 + p.2 = k),
      (sobWeight p.1 ^ s * ‖c p.1‖ ^ 2) * (sobWeight p.2 ^ s * ‖c p.2‖ ^ 2) := by
  classical
  set F := (S ×ˢ S).filter (fun p => p.1 + p.2 = k)
  have hq : convSq S c k = ∑ p ∈ F, c p.1 * c p.2 := by
    unfold convSq; rw [Finset.sum_filter]
  set B : (d → ℤ) × (d → ℤ) → ℝ := fun p =>
    (sobWeight p.1 ^ (s / 2) * ‖c p.1‖) * (sobWeight p.2 ^ (s / 2) * ‖c p.2‖)
  set X : (d → ℤ) × (d → ℤ) → ℝ := fun p => sobWeight p.1 ^ (-(s / 2)) * sobWeight p.2 ^ (-(s / 2))
  have hBX : ∀ p, B p * X p = ‖c p.1‖ * ‖c p.2‖ := by
    intro p
    simp only [B, X]
    have h1 : sobWeight p.1 ^ (s / 2) * sobWeight p.1 ^ (-(s / 2)) = 1 := by
      rw [← Real.rpow_add (sobWeight_pos _), add_neg_cancel, Real.rpow_zero]
    have h2 : sobWeight p.2 ^ (s / 2) * sobWeight p.2 ^ (-(s / 2)) = 1 := by
      rw [← Real.rpow_add (sobWeight_pos _), add_neg_cancel, Real.rpow_zero]
    calc sobWeight p.1 ^ (s / 2) * ‖c p.1‖ * (sobWeight p.2 ^ (s / 2) * ‖c p.2‖) *
          (sobWeight p.1 ^ (-(s / 2)) * sobWeight p.2 ^ (-(s / 2)))
        = (sobWeight p.1 ^ (s / 2) * sobWeight p.1 ^ (-(s / 2))) *
            (sobWeight p.2 ^ (s / 2) * sobWeight p.2 ^ (-(s / 2))) * (‖c p.1‖ * ‖c p.2‖) := by
          ring
      _ = _ := by rw [h1, h2, one_mul, one_mul]
  have hB2 : ∀ p, B p ^ 2 = (sobWeight p.1 ^ s * ‖c p.1‖ ^ 2) * (sobWeight p.2 ^ s * ‖c p.2‖ ^ 2) := by
    intro p
    simp only [B]
    have e : ∀ m : d → ℤ, (sobWeight m ^ (s / 2)) ^ 2 = sobWeight m ^ s := by
      intro m
      rw [← Real.rpow_natCast, ← Real.rpow_mul (sobWeight_pos m).le]
      congr 1; push_cast; ring
    calc (sobWeight p.1 ^ (s / 2) * ‖c p.1‖ * (sobWeight p.2 ^ (s / 2) * ‖c p.2‖)) ^ 2
        = (sobWeight p.1 ^ (s / 2)) ^ 2 * ‖c p.1‖ ^ 2 *
            ((sobWeight p.2 ^ (s / 2)) ^ 2 * ‖c p.2‖ ^ 2) := by ring
      _ = _ := by rw [e, e]
  have hX2 : ∀ p, X p ^ 2 ≤ (sobWeight p.1 ^ (-(2 * s)) + sobWeight p.2 ^ (-(2 * s))) / 2 := by
    intro p
    simp only [X]
    have e : ∀ m : d → ℤ, (sobWeight m ^ (-(s / 2))) ^ 2 = sobWeight m ^ (-s) := by
      intro m
      rw [← Real.rpow_natCast, ← Real.rpow_mul (sobWeight_pos m).le]
      congr 1; push_cast; ring
    have e2 : ∀ m : d → ℤ, (sobWeight m ^ (-s)) ^ 2 = sobWeight m ^ (-(2 * s)) := by
      intro m
      rw [← Real.rpow_natCast, ← Real.rpow_mul (sobWeight_pos m).le]
      congr 1; push_cast; ring
    rw [mul_pow, e, e, ← e2 p.1, ← e2 p.2]
    nlinarith [sq_nonneg (sobWeight p.1 ^ (-s) - sobWeight p.2 ^ (-s))]
  have hnorm : ‖convSq S c k‖ ≤ ∑ p ∈ F, B p * X p := by
    rw [hq]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hBX, norm_mul]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq F B X
  have hXsum : ∑ p ∈ F, X p ^ 2 ≤ l4Const d s := by
    calc ∑ p ∈ F, X p ^ 2 ≤ ∑ p ∈ F, (sobWeight p.1 ^ (-(2 * s)) +
          sobWeight p.2 ^ (-(2 * s))) / 2 := Finset.sum_le_sum fun p _ => hX2 p
      _ = (∑ p ∈ F, sobWeight p.1 ^ (-(2 * s)) + ∑ p ∈ F, sobWeight p.2 ^ (-(2 * s))) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
      _ ≤ (l4Const d s + l4Const d s) / 2 := by
          gcongr
          · exact sum_fibre_fst_le hs S k
          · exact sum_fibre_snd_le hs S k
      _ = l4Const d s := by ring
  have hBsum_nn : 0 ≤ ∑ p ∈ F, B p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  have hsq : ‖convSq S c k‖ ^ 2 ≤ (∑ p ∈ F, B p * X p) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc ‖convSq S c k‖ ^ 2 ≤ (∑ p ∈ F, B p ^ 2) * ∑ p ∈ F, X p ^ 2 := hsq.trans hCS
    _ ≤ (∑ p ∈ F, B p ^ 2) * l4Const d s := mul_le_mul_of_nonneg_left hXsum hBsum_nn
    _ = l4Const d s * ∑ p ∈ F, B p ^ 2 := mul_comm _ _
    _ = _ := by simp_rw [hB2]

/-- **`L⁴` bound for trigonometric polynomials**: `∫ |P|⁴ ≤ Z_{2s} (Σ_S ⟨n⟩^{2s} |c_n|²)²`
for `s > d/4`. -/
theorem integral_norm_pow_four_trigPoly_le {s : ℝ} (hs : (Fintype.card d : ℝ) / 4 < s)
    (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) :
    ∫ x, ‖trigPoly S c x‖ ^ 4 ≤
      l4Const d s * (∑ n ∈ S, sobWeight n ^ s * ‖c n‖ ^ 2) ^ 2 := by
  classical
  set T := (S ×ˢ S).image (fun p => p.1 + p.2)
  have hsupp : ∀ k ∉ T, ‖convSq S c k‖ ^ 2 = 0 := by
    intro k hk
    have : convSq S c k = 0 := by
      unfold convSq
      refine Finset.sum_eq_zero fun p hp => ?_
      have : p.1 + p.2 ≠ k := fun h => hk (Finset.mem_image.mpr ⟨p, hp, h⟩)
      rw [if_neg this]
    rw [this, norm_zero, sq, mul_zero]
  rw [← (hasSum_convSq S c).tsum_eq, tsum_eq_sum (s := T) hsupp]
  calc ∑ k ∈ T, ‖convSq S c k‖ ^ 2
      ≤ ∑ k ∈ T, l4Const d s * ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 + p.2 = k),
          (sobWeight p.1 ^ s * ‖c p.1‖ ^ 2) * (sobWeight p.2 ^ s * ‖c p.2‖ ^ 2) :=
        Finset.sum_le_sum fun k _ => norm_convSq_sq_le hs S c k
    _ = l4Const d s * ∑ p ∈ S ×ˢ S,
          (sobWeight p.1 ^ s * ‖c p.1‖ ^ 2) * (sobWeight p.2 ^ s * ‖c p.2‖ ^ 2) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem _ hp) _
    _ = l4Const d s * (∑ n ∈ S, sobWeight n ^ s * ‖c n‖ ^ 2) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']

/-! ### From trigonometric polynomials to `H^s`: truncation and Fatou -/

theorem CoeffMemH.sub {s : ℝ} {c c' : (d → ℤ) → ℂ} (hc : CoeffMemH s c) (hc' : CoeffMemH s c') :
    CoeffMemH s (c - c') := by
  refine Summable.of_nonneg_of_le (coeffSobSq_term_nonneg _ _) (fun n => ?_)
    ((hc.mul_left 2).add (hc'.mul_left 2))
  have h := FourierRellich.norm_sub_sq_le (c n) (c' n)
  have hw := sobWeight_rpow_nonneg n s
  simp only [Pi.sub_apply]
  nlinarith [mul_le_mul_of_nonneg_left h hw]

theorem memH_Lp_sub {s : ℝ} {f g : L²(UnitAddTorus d)} (hf : MemH s f) (hg : MemH s g) :
    MemH s ⇑(f - g) := by
  have := CoeffMemH.sub hf hg
  unfold MemH
  convert this using 1
  funext n
  exact mFourierCoeff_Lp_sub f g n

open Classical in
/-- The cube `[-N, N]^d ∩ ℤ^d`. -/
def box (N : ℕ) : Finset (d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

theorem box_mono : Monotone (box (d := d)) := by
  intro N M hNM n hn
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc] at hn ⊢
  intro i
  have : (N : ℤ) ≤ M := by exact_mod_cast hNM
  exact ⟨by linarith [(hn i).1], by linarith [(hn i).2]⟩

theorem exists_mem_box (n : d → ℤ) : ∃ N, n ∈ box N := by
  refine ⟨∑ i, (n i).natAbs, ?_⟩
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h1 : (n i).natAbs ≤ ∑ j, (n j).natAbs :=
    Finset.single_le_sum (f := fun j => (n j).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)
  have h2 : |n i| ≤ ((∑ j, (n j).natAbs : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]; exact_mod_cast h1
  exact abs_le.mp h2

theorem tendsto_box : Tendsto (box (d := d)) atTop atTop :=
  Filter.tendsto_atTop_finset_of_monotone box_mono exists_mem_box

/-- The Fourier truncation `Σ_{n ∈ [-N,N]^d} f̂(n) e_n` of an `L²` function. -/
def fourierTrunc (N : ℕ) (f : L²(UnitAddTorus d)) : C(UnitAddTorus d, ℂ) :=
  trigPoly (box N) (mFourierCoeff f)

/-- Fourier truncations converge to `f` in `L²`. -/
theorem tendsto_fourierTrunc (f : L²(UnitAddTorus d)) :
    Tendsto (fun N => (fourierTrunc N f).toLp 2 volume ℂ) atTop (𝓝 f) := by
  have h := (hasSum_mFourier_series_L2 f).comp tendsto_box
  refine h.congr fun N => ?_
  simp only [Function.comp_apply, fourierTrunc, trigPoly, map_sum, map_smul]

/-- `∫ |P|⁴` as an `L⁴` seminorm for continuous `P`. -/
theorem eLpNorm_four_eq (P : C(UnitAddTorus d, ℂ)) :
    eLpNorm P 4 volume = ENNReal.ofReal ((∫ x, ‖P x‖ ^ 4) ^ (1 / 4 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h4 : ((4 : ℝ≥0∞)).toReal = 4 := by norm_num
  rw [h4]
  have hint : Integrable (fun x => ‖P x‖ ^ 4) volume :=
    ((continuous_norm.comp P.continuous).pow 4).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have e : ∀ x, ‖P x‖ₑ ^ (4 : ℝ) = ENNReal.ofReal (‖P x‖ ^ 4) := by
    intro x
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    congr 1
    exact_mod_cast Real.rpow_natCast ‖P x‖ 4
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by positivity),
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun x => by positivity) (by norm_num)]

/-- `L⁴` bound of trigonometric polynomials in terms of the full `H^s` norm. -/
theorem eLpNorm_four_trigPoly_le {s : ℝ} (hs : (Fintype.card d : ℝ) / 4 < s)
    (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (hc : CoeffMemH s c) :
    eLpNorm (trigPoly S c) 4 volume ≤
      ENNReal.ofReal (l4Const d s ^ (1 / 4 : ℝ) * Real.sqrt (coeffSobSq s c)) := by
  rw [eLpNorm_four_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have hS : ∑ n ∈ S, sobWeight n ^ s * ‖c n‖ ^ 2 ≤ coeffSobSq s c :=
    hc.sum_le_tsum S (fun n _ => coeffSobSq_term_nonneg s c n)
  have hS0 : 0 ≤ ∑ n ∈ S, sobWeight n ^ s * ‖c n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => coeffSobSq_term_nonneg s c n
  have hZ := l4Const_nonneg (d := d) s
  have hint := integral_norm_pow_four_trigPoly_le hs S c
  have h1 : ∫ x, ‖trigPoly S c x‖ ^ 4 ≤ l4Const d s * coeffSobSq s c ^ 2 :=
    hint.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS0 hS 2) hZ)
  have hA := coeffSobSq_nonneg s c
  calc (∫ x, ‖trigPoly S c x‖ ^ 4) ^ (1 / 4 : ℝ)
      ≤ (l4Const d s * coeffSobSq s c ^ 2) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg fun x => by positivity) h1 (by norm_num)
    _ = l4Const d s ^ (1 / 4 : ℝ) * Real.sqrt (coeffSobSq s c) := by
        rw [Real.mul_rpow hZ (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_natCast,
          ← Real.rpow_mul hA]
        norm_num

/-- **Sobolev embedding `H^s(𝕋^d) ⊂ L⁴(𝕋^d)` for `s > d/4`** (`prop:sobolev-bosonic`: on `𝕋⁴`,
`H^{1+σ} ⊂ L⁴`): `‖f‖_{L⁴} ≤ Z_{2s}^{1/4} ‖f‖_{H^s}` with `Z_{2s} = Σ_n ⟨n⟩^{-4s}`. -/
theorem eLpNorm_four_le_of_memH {s : ℝ} (hs : (Fintype.card d : ℝ) / 4 < s)
    (f : L²(UnitAddTorus d)) (hf : MemH s f) :
    eLpNorm f 4 volume ≤ ENNReal.ofReal (l4Const d s ^ (1 / 4 : ℝ) * sobNorm s f) := by
  have hL2 := tendsto_fourierTrunc f
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hL2).exists_seq_tendsto_ae
  have hbound : ∀ j, eLpNorm (⇑((fourierTrunc (ns j) f).toLp 2 volume ℂ)) 4 volume ≤
      ENNReal.ofReal (l4Const d s ^ (1 / 4 : ℝ) * sobNorm s f) := by
    intro j
    rw [eLpNorm_congr_ae (ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ) _)]
    exact eLpNorm_four_trigPoly_le hs _ _ hf
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun j => Lp.aestronglyMeasurable _) (⇑f) hae).trans ?_
  exact liminf_le_of_frequently_le' (Frequently.of_forall hbound)

/-- `H^s ⊂ L⁴` for `s > d/4`: membership. -/
theorem memLp_four_of_memH {s : ℝ} (hs : (Fintype.card d : ℝ) / 4 < s)
    (f : L²(UnitAddTorus d)) (hf : MemH s f) : MemLp f 4 volume :=
  ⟨Lp.aestronglyMeasurable f, lt_of_le_of_lt (eLpNorm_four_le_of_memH hs f hf) ENNReal.ofReal_lt_top⟩

/-- `L⁴` distance bounded by the `H^s` distance, `s > d/4`. -/
theorem eLpNorm_four_sub_le {s : ℝ} (hs : (Fintype.card d : ℝ) / 4 < s)
    {f g : L²(UnitAddTorus d)} (hf : MemH s f) (hg : MemH s g) :
    eLpNorm (⇑f - ⇑g) 4 volume ≤ ENNReal.ofReal (l4Const d s ^ (1 / 4 : ℝ) * sobNorm s ⇑(f - g)) := by
  rw [← eLpNorm_congr_ae (Lp.coeFn_sub f g)]
  exact eLpNorm_four_le_of_memH hs _ (memH_Lp_sub hf hg)

/-- **Strong `H^s` convergence implies strong `L⁴` convergence** for `s > d/4`. -/
theorem tendsto_eLpNorm_four_of_H {s : ℝ} (hs : (Fintype.card d : ℝ) / 4 < s)
    {f : ℕ → L²(UnitAddTorus d)} {f₀ : L²(UnitAddTorus d)} (hf : ∀ k, MemH s (f k))
    (hf₀ : MemH s f₀) (hconv : Tendsto (fun k => sobSq s ⇑(f k - f₀)) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (⇑(f k) - ⇑f₀) 4 volume) atTop (𝓝 0) := by
  have h := ENNReal.tendsto_ofReal
    (((Real.continuous_sqrt.tendsto 0).comp hconv).const_mul (l4Const d s ^ (1 / 4 : ℝ)))
  simp only [Function.comp_def, Real.sqrt_zero, mul_zero, ENNReal.ofReal_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun k => zero_le)
    (fun k => eLpNorm_four_sub_le hs (hf k) hf₀)

/-- Non-vacuity: a monomial on `𝕋⁴` lies in `L⁴` with the `H^{3/2}` bound (`3/2 > 4/4`). -/
example (m : Fin 4 → ℤ) :
    eLpNorm ((mFourier m).toLp 2 volume ℂ) 4 volume ≤
      ENNReal.ofReal (l4Const (Fin 4) (3 / 2) ^ (1 / 4 : ℝ) *
        sobNorm (3 / 2) ⇑((mFourier m).toLp 2 volume ℂ)) := by
  refine eLpNorm_four_le_of_memH (by norm_num) _ ?_
  have := memH_mFourier (d := Fin 4) (3 / 2) m
  unfold MemH CoeffMemH at this ⊢
  simp_rw [mFourierCoeff_toLp]
  exact this

end

end RenewalGeometry.TorusSobolev
