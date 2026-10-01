/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicGridSampling

/-!
# Continuum product algebra for trigonometric polynomials, countable Minkowski, and analytic
  composition consistency (`lem:supp-open-interpolation`,
  `eq:supp-open-composition-consistency`; emergent-spacetime manuscript)

On the unit torus `𝕋³` with the trigonometric Sobolev norms `‖f‖²_{H^s} = trigSobSq s f`:

* `tp S a = Σ_{m ∈ S} a_m e_m`: trigonometric polynomials; `mFourierCoeff_tp`, `trigSobSq_tp`,
  `tp_mul` (closure under products, explicit convolution coefficients).
* `trigSobSq_tp_mul_le` (**continuum product algebra**): for `s ≥ 2` there is `K` with
  `‖FG‖²_{H^s} ≤ K ‖F‖²_{H^s} ‖G‖²_{H^s}` for all trigonometric polynomials `F, G` (no constraint on
  the supports); `IsTP` (closure under sums, products, scalars, constants, interpolants),
  `sn_mul_le`, `sn_prod_le` (`‖Π_k F_k‖ ≤ K^n Π_k ‖F_k‖`), `norm_le_sn_two` (`H² ⊂ C⁰`).
* `fcL` (Fourier coefficients are continuous for the uniform norm), `wseq` (the weighted
  coefficient sequence in `ℓ²(ℤ³)`), `trigSobSq_tsum_le` (**countable Minkowski**: if `F = Σ_n G_n`
  uniformly then `‖F‖_{H^r} ≤ Σ_n ‖G_n‖_{H^r}`).
* `interp_const`, `interp_add`, `interp_smul`, `projL` (`𝒫_h` as a continuous linear map).
* `composition_consistency` (**`eq:supp-open-composition-consistency`**): for `A` analytic at a
  constant base point `c` (a convergent power series; the chart's real-analytic coefficient maps
  are restrictions of such maps) and `r ≥ 1`, there are mesh-independent `δ, C` with
  `‖𝓘_h A(u_h) - A(𝓘_h u_h)‖²_{H^r} ≤ C h² (Σ_j ‖u_j - c_j‖_{r+1,h})²` on the small chart
  `Σ_j ‖u_j - c_j‖_{r+1,h} ≤ δ`.  Proof: `𝓘_h A(u_h) = 𝒫_h[A(𝓘_h u_h)]`, the Taylor series
  `A(c + v) = Σ_n p_n(vⁿ)` converges uniformly with trigonometric-polynomial terms, each term obeys
  the sampling estimate and the product algebra, and countable Minkowski sums the series.
-/

open Finset ComplexConjugate UnitAddTorus
open scoped BigOperators Real

namespace RenewalGeometry.PeriodicGridSobolev

namespace Composition

open LatticeTorusPlancherel Sampling

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable section

/-! ### Trigonometric polynomials -/

/-- The trigonometric polynomial `Σ_{m ∈ S} a_m e_m` on `𝕋³`. -/
def tp (S : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ℂ) : C(UnitAddTorus (Fin 3), ℂ) :=
  ∑ m ∈ S, a m • mFourier m

theorem mFourierCoeff_tp (S : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ℂ) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(tp S a) n = if n ∈ S then a n else 0 := by
  have h := mFourierCoeff_trigSum S a id n
  simp only [id] at h
  rw [tp, h]
  simp [Finset.sum_ite_eq']

theorem trigSobSq_tp (s : ℕ) (S : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ℂ) :
    trigSobSq s ⇑(tp S a) = ∑ n ∈ S, trigWeight s n * ‖a n‖ ^ 2 := by
  unfold trigSobSq
  rw [tsum_eq_sum (s := S) (fun n hn => by rw [mFourierCoeff_tp, if_neg hn]; simp)]
  refine sum_congr rfl fun n hn => ?_
  rw [mFourierCoeff_tp, if_pos hn]

theorem summable_tp (s : ℕ) (S : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ℂ) :
    Summable fun n => trigWeight s n * ‖mFourierCoeff ⇑(tp S a) n‖ ^ 2 :=
  summable_of_ne_finset_zero (s := S) fun n hn => by rw [mFourierCoeff_tp, if_neg hn]; simp

theorem trigSobSq_nonneg' (s : ℕ) (f : UnitAddTorus (Fin 3) → ℂ) : 0 ≤ trigSobSq s f :=
  tsum_nonneg fun n => mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _)

/-- The convolution coefficients of a product of trigonometric polynomials. -/
def convC (S T : Finset (Fin 3 → ℤ)) (a b : (Fin 3 → ℤ) → ℂ) (n : Fin 3 → ℤ) : ℂ :=
  ∑ p ∈ (S ×ˢ T).filter (fun p => p.1 + p.2 = n), a p.1 * b p.2

/-- **Products of trigonometric polynomials** are trigonometric polynomials with convolution
coefficients. -/
theorem tp_mul (S T : Finset (Fin 3 → ℤ)) (a b : (Fin 3 → ℤ) → ℂ) :
    tp S a * tp T b = tp ((S ×ˢ T).image fun p => p.1 + p.2) (convC S T a b) := by
  have h1 : tp S a * tp T b = ∑ p ∈ S ×ˢ T, (a p.1 * b p.2) • mFourier (p.1 + p.2) := by
    ext x
    simp only [tp, ContinuousMap.mul_apply, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mFourier_add, Finset.sum_mul_sum,
      Finset.sum_product]
    refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
    ring
  rw [h1, tp]
  rw [← sum_fiberwise_of_maps_to (s := S ×ˢ T) (t := (S ×ˢ T).image fun p => p.1 + p.2)
    (g := fun p => p.1 + p.2) (fun p hp => mem_image_of_mem _ hp)]
  refine sum_congr rfl fun n _ => ?_
  ext x
  simp only [convC, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine sum_congr rfl fun p hp => ?_
  rw [(mem_filter.mp hp).2]

/-- The weighted convolution bound `⟨n⟩^s Σ_{p+q=n} ⟨p⟩^{-s}⟨q⟩^{-s} ≤ M`, `s ≥ 2`. -/
theorem conv_weight_le (s : ℕ) (hs : 2 ≤ s) (S T : Finset (Fin 3 → ℤ)) (n : Fin 3 → ℤ) :
    bracket n ^ s * ∑ p ∈ (S ×ˢ T).filter (fun p => p.1 + p.2 = n),
      1 / (bracket p.1 ^ s * bracket p.2 ^ s) ≤ 4 ^ s * (2 * (256 * c1 ^ 3)) := by
  set U : (Fin 3 → ℤ) → ℝ := fun k => bracket k ^ s
  have hU : ∀ k, 0 < U k := fun k => pow_pos (bracket_pos _) s
  set P := (S ×ˢ T).filter (fun p => p.1 + p.2 = n)
  rw [mul_sum]
  have hpt : ∀ p ∈ P, bracket n ^ s * (1 / (U p.1 * U p.2)) ≤ 4 ^ s * ((U p.2)⁻¹ + (U p.1)⁻¹) := by
    intro p hp
    have hφ : p.1 + p.2 = n := (mem_filter.mp hp).2
    have h := bracket_pow_add_le s p.1 p.2
    have h1 := hU p.1; have h2 := hU p.2
    rw [← hφ]
    calc bracket (p.1 + p.2) ^ s * (1 / (U p.1 * U p.2)) ≤
          (4 ^ s * (U p.1 + U p.2)) * (1 / (U p.1 * U p.2)) := by gcongr
    _ = 4 ^ s * ((U p.2)⁻¹ + (U p.1)⁻¹) := by field_simp
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum, sum_add_distrib]
  have hinj2 : Set.InjOn Prod.snd (P : Set ((Fin 3 → ℤ) × (Fin 3 → ℤ))) := by
    intro p hp q hq h
    have hp' : p.1 + p.2 = n := (mem_filter.mp hp).2
    have hq' : q.1 + q.2 = n := (mem_filter.mp hq).2
    refine Prod.ext ?_ h
    have e1 : p.1 = n - p.2 := by rw [← hp']; abel
    have e2 : q.1 = n - q.2 := by rw [← hq']; abel
    rw [e1, e2, h]
  have hinj1 : Set.InjOn Prod.fst (P : Set ((Fin 3 → ℤ) × (Fin 3 → ℤ))) := by
    intro p hp q hq h
    have hp' : p.1 + p.2 = n := (mem_filter.mp hp).2
    have hq' : q.1 + q.2 = n := (mem_filter.mp hq).2
    refine Prod.ext h ?_
    have e1 : p.2 = n - p.1 := by rw [← hp']; abel
    have e2 : q.2 = n - q.1 := by rw [← hq']; abel
    rw [e1, e2, h]
  have hinv : ∀ k, (U k)⁻¹ ≤ (bracket k ^ 2)⁻¹ := fun k =>
    inv_anti₀ (by have := bracket_pos k; positivity) (pow_le_pow_right₀ (one_le_bracket k) hs)
  have hbound : ∀ F : Finset (Fin 3 → ℤ), ∑ k ∈ F, (U k)⁻¹ ≤ 256 * c1 ^ 3 := by
    intro F
    calc ∑ k ∈ F, (U k)⁻¹ ≤ ∑ k ∈ F, (bracket k ^ 2)⁻¹ := sum_le_sum fun k _ => hinv k
      _ ≤ ∑' k, (bracket k ^ 2)⁻¹ := summable_inv_bracket_sq.sum_le_tsum _
          (fun k _ => by have := bracket_pos k; positivity)
      _ ≤ 256 * c1 ^ 3 := tsum_inv_bracket_sq_le
  have hb2 : ∑ p ∈ P, (U p.2)⁻¹ ≤ 256 * c1 ^ 3 := by
    rw [← sum_image (f := fun k => (U k)⁻¹) hinj2]; exact hbound _
  have hb1 : ∑ p ∈ P, (U p.1)⁻¹ ≤ 256 * c1 ^ 3 := by
    rw [← sum_image (f := fun k => (U k)⁻¹) hinj1]; exact hbound _
  gcongr
  linarith

/-- **Continuum product algebra for trigonometric polynomials**: for `s ≥ 2` there is `K`,
independent of the supports, with `‖FG‖²_{H^s} ≤ K ‖F‖²_{H^s} ‖G‖²_{H^s}`. -/
theorem trigSobSq_tp_mul_le (s : ℕ) (hs : 2 ≤ s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (S T : Finset (Fin 3 → ℤ)) (a b : (Fin 3 → ℤ) → ℂ),
      trigSobSq s ⇑(tp S a * tp T b) ≤ K * trigSobSq s ⇑(tp S a) * trigSobSq s ⇑(tp T b) := by
  set card := ((multiIndices s).card : ℝ)
  set M : ℝ := 4 ^ s * (2 * (256 * c1 ^ 3))
  set K : ℝ := card * ((2 * π) ^ 2) ^ s * M * 4 ^ s * 4 ^ s
  have hM : 0 ≤ M := by have := c1_nonneg; positivity
  have hK : 0 ≤ K := by positivity
  refine ⟨K, hK, fun S T a b => ?_⟩
  classical
  set P := S ×ˢ T
  set φ : (Fin 3 → ℤ) × (Fin 3 → ℤ) → (Fin 3 → ℤ) := fun p => p.1 + p.2
  set U : (Fin 3 → ℤ) → ℝ := fun k => bracket k ^ s
  have hU : ∀ k, 0 < U k := fun k => pow_pos (bracket_pos _) s
  set G : (Fin 3 → ℤ) × (Fin 3 → ℤ) → ℝ := fun p => (U p.1 * ‖a p.1‖ ^ 2) * (U p.2 * ‖b p.2‖ ^ 2)
  have hG0 : ∀ p, 0 ≤ G p := fun p => by
    have := hU p.1; have := hU p.2; positivity
  rw [tp_mul, trigSobSq_tp, trigSobSq_tp, trigSobSq_tp]
  -- pointwise bound on the coefficients
  have hpt : ∀ n, trigWeight s n * ‖convC S T a b n‖ ^ 2 ≤
      card * ((2 * π) ^ 2) ^ s * M * ∑ p ∈ P.filter (fun p => φ p = n), G p := by
    intro n
    have hW : trigWeight s n ≤ card * ((2 * π) ^ 2) ^ s * bracket n ^ s := by
      have := trigWeight_le_bracket s n
      rw [mul_pow] at this; linarith
    have hCS : ‖convC S T a b n‖ ^ 2 ≤ (∑ p ∈ P.filter (fun p => φ p = n), 1 / (U p.1 * U p.2)) *
        ∑ p ∈ P.filter (fun p => φ p = n), G p := by
      have h1 : ‖convC S T a b n‖ ≤ ∑ p ∈ P.filter (fun p => φ p = n), ‖a p.1‖ * ‖b p.2‖ :=
        (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun p _ => norm_mul _ _))
      have h2 : (∑ p ∈ P.filter (fun p => φ p = n), ‖a p.1‖ * ‖b p.2‖) ^ 2 ≤
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
    have hb := conv_weight_le s hs S T n
    calc trigWeight s n * ‖convC S T a b n‖ ^ 2
        ≤ (card * ((2 * π) ^ 2) ^ s * bracket n ^ s) *
            ((∑ p ∈ P.filter (fun p => φ p = n), 1 / (U p.1 * U p.2)) *
              ∑ p ∈ P.filter (fun p => φ p = n), G p) :=
          mul_le_mul hW hCS (sq_nonneg _) (mul_nonneg (by positivity)
            (pow_nonneg (bracket_pos n).le s))
      _ = card * ((2 * π) ^ 2) ^ s * ((bracket n ^ s *
            ∑ p ∈ P.filter (fun p => φ p = n), 1 / (U p.1 * U p.2)) *
              ∑ p ∈ P.filter (fun p => φ p = n), G p) := by ring
      _ ≤ card * ((2 * π) ^ 2) ^ s * (M * ∑ p ∈ P.filter (fun p => φ p = n), G p) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb hsum0) (by positivity)
      _ = _ := by ring
  have hfib : ∑ n ∈ P.image φ, ∑ p ∈ P.filter (fun p => φ p = n), G p = ∑ p ∈ P, G p :=
    sum_fiberwise_of_maps_to (fun p hp => mem_image_of_mem φ hp) G
  have hprod : ∑ p ∈ P, G p = (∑ k ∈ S, U k * ‖a k‖ ^ 2) * ∑ k ∈ T, U k * ‖b k‖ ^ 2 := by
    simp only [P, G, Finset.sum_product, Finset.sum_mul_sum]
  have hUa : ∑ k ∈ S, U k * ‖a k‖ ^ 2 ≤ 4 ^ s * ∑ n ∈ S, trigWeight s n * ‖a n‖ ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun k _ => ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (bracket_pow_le_trigWeight s _) (sq_nonneg _)
  have hUb : ∑ k ∈ T, U k * ‖b k‖ ^ 2 ≤ 4 ^ s * ∑ n ∈ T, trigWeight s n * ‖b n‖ ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun k _ => ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (bracket_pow_le_trigWeight s _) (sq_nonneg _)
  have hUa0 : 0 ≤ ∑ k ∈ S, U k * ‖a k‖ ^ 2 := sum_nonneg fun k _ => by have := hU k; positivity
  have hUb0 : 0 ≤ ∑ k ∈ T, U k * ‖b k‖ ^ 2 := sum_nonneg fun k _ => by have := hU k; positivity
  have hTa : 0 ≤ ∑ n ∈ S, trigWeight s n * ‖a n‖ ^ 2 :=
    sum_nonneg fun n _ => mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _)
  calc ∑ n ∈ P.image φ, trigWeight s n * ‖convC S T a b n‖ ^ 2
      ≤ ∑ n ∈ P.image φ, card * ((2 * π) ^ 2) ^ s * M *
          ∑ p ∈ P.filter (fun p => φ p = n), G p := sum_le_sum fun n _ => hpt n
    _ = card * ((2 * π) ^ 2) ^ s * M * ((∑ k ∈ S, U k * ‖a k‖ ^ 2) *
          ∑ k ∈ T, U k * ‖b k‖ ^ 2) := by rw [← mul_sum, hfib, hprod]
    _ ≤ card * ((2 * π) ^ 2) ^ s * M * ((4 ^ s * ∑ n ∈ S, trigWeight s n * ‖a n‖ ^ 2) *
          (4 ^ s * ∑ n ∈ T, trigWeight s n * ‖b n‖ ^ 2)) := by gcongr
    _ = K * (∑ n ∈ S, trigWeight s n * ‖a n‖ ^ 2) * ∑ n ∈ T, trigWeight s n * ‖b n‖ ^ 2 := by
        simp only [K]; ring

/-! ### Fourier coefficients are continuous for the uniform norm -/

theorem norm_mFourierCoeff_le (f : C(UnitAddTorus (Fin 3), ℂ)) (n : Fin 3 → ℤ) :
    ‖mFourierCoeff ⇑f n‖ ≤ ‖f‖ := by
  unfold mFourierCoeff
  refine (MeasureTheory.norm_integral_le_of_norm_le_const (C := ‖f‖)
    (Filter.Eventually.of_forall fun t => ?_)).trans ?_
  · rw [norm_smul]
    have h1 : ‖mFourier (-n) t‖ = 1 := by
      rw [show ‖mFourier (-n) t‖ = ‖(mFourier (-n) t : ℂ)‖ from rfl]
      simp [mFourier, Circle.norm_coe]
    rw [h1, one_mul]
    exact f.norm_coe_le_norm t
  · simp

theorem mFourierCoeff_smul' (c : ℂ) (f : C(UnitAddTorus (Fin 3), ℂ)) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(c • f) n = c • mFourierCoeff ⇑f n := by
  rw [← mFourierCoeff_toLp, ← mFourierCoeff_toLp f, ← mFourierBasis_repr, ← mFourierBasis_repr,
    map_smul, map_smul]
  rfl

/-- The `n`-th Fourier coefficient as a continuous linear functional on `C(𝕋³, ℂ)`. -/
def fcL (n : Fin 3 → ℤ) : C(UnitAddTorus (Fin 3), ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => mFourierCoeff ⇑f n
      map_add' := fun f g => mFourierCoeff_add f g n
      map_smul' := fun c f => mFourierCoeff_smul' c f n }
    1 fun f => by rw [one_mul]; exact norm_mFourierCoeff_le f n

@[simp] theorem fcL_apply (n : Fin 3 → ℤ) (f : C(UnitAddTorus (Fin 3), ℂ)) :
    fcL n f = mFourierCoeff ⇑f n := rfl

/-! ### Countable Minkowski for the trigonometric Sobolev norms -/

/-- The weighted coefficient sequence `m ↦ √W_r(m) f̂(m)` in `ℓ²(ℤ³)`. -/
def wseq (r : ℕ) (f : C(UnitAddTorus (Fin 3), ℂ))
    (hf : Summable fun n => trigWeight r n * ‖mFourierCoeff ⇑f n‖ ^ 2) :
    lp (fun _ : Fin 3 → ℤ => ℂ) 2 :=
  ⟨fun m => ((Real.sqrt (trigWeight r m) : ℝ) : ℂ) * mFourierCoeff ⇑f m, by
    refine memℓp_gen ?_
    have e : ∀ m, ‖((Real.sqrt (trigWeight r m) : ℝ) : ℂ) * mFourierCoeff ⇑f m‖ ^
        (2 : ENNReal).toReal = trigWeight r m * ‖mFourierCoeff ⇑f m‖ ^ 2 := by
      intro m
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        ENNReal.toReal_ofNat, Real.rpow_two, mul_pow, Real.sq_sqrt (trigWeight_nonneg r m)]
    simp only [e]
    exact hf⟩

theorem wseq_apply (r : ℕ) (f : C(UnitAddTorus (Fin 3), ℂ)) (hf) (m : Fin 3 → ℤ) :
    (wseq r f hf : (Fin 3 → ℤ) → ℂ) m =
      ((Real.sqrt (trigWeight r m) : ℝ) : ℂ) * mFourierCoeff ⇑f m := rfl

theorem norm_wseq (r : ℕ) (f : C(UnitAddTorus (Fin 3), ℂ)) (hf) :
    ‖wseq r f hf‖ = Real.sqrt (trigSobSq r ⇑f) := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (wseq r f hf)
  have e : ∀ m, ‖(wseq r f hf : (Fin 3 → ℤ) → ℂ) m‖ ^ (2 : ENNReal).toReal =
      trigWeight r m * ‖mFourierCoeff ⇑f m‖ ^ 2 := by
    intro m
    rw [wseq_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), ENNReal.toReal_ofNat, Real.rpow_two, mul_pow,
      Real.sq_sqrt (trigWeight_nonneg r m)]
  simp only [e] at h
  rw [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [trigSobSq, ← h, Real.sqrt_sq (norm_nonneg _)]

/-- **Countable Minkowski inequality** for `‖·‖_{H^r}`: if `F = Σ_n G_n` uniformly and
`Σ_n ‖G_n‖_{H^r} < ∞`, then `F ∈ H^r` and `‖F‖_{H^r} ≤ Σ_n ‖G_n‖_{H^r}`. -/
theorem trigSobSq_tsum_le (r : ℕ) {G : ℕ → C(UnitAddTorus (Fin 3), ℂ)}
    {F : C(UnitAddTorus (Fin 3), ℂ)} (hF : HasSum G F)
    (hG : ∀ n, Summable fun m => trigWeight r m * ‖mFourierCoeff ⇑(G n) m‖ ^ 2)
    (hS : Summable fun n => Real.sqrt (trigSobSq r ⇑(G n))) :
    (Summable fun m => trigWeight r m * ‖mFourierCoeff ⇑F m‖ ^ 2) ∧
      Real.sqrt (trigSobSq r ⇑F) ≤ ∑' n, Real.sqrt (trigSobSq r ⇑(G n)) := by
  set y : ℕ → lp (fun _ : Fin 3 → ℤ => ℂ) 2 := fun n => wseq r (G n) (hG n)
  have hy : Summable fun n => ‖y n‖ := by simpa [y, norm_wseq] using hS
  have hys : Summable y := hy.of_norm
  set Y := ∑' n, y n
  -- coordinates of the limit
  have hcoef : ∀ m, HasSum (fun n => mFourierCoeff ⇑(G n) m) (mFourierCoeff ⇑F m) := by
    intro m
    have := (fcL m).hasSum hF
    simpa using this
  have hYm : ∀ m, (Y : (Fin 3 → ℤ) → ℂ) m =
      ((Real.sqrt (trigWeight r m) : ℝ) : ℂ) * mFourierCoeff ⇑F m := by
    intro m
    have h1 : HasSum (fun n => (lp.evalCLM ℂ (fun _ : Fin 3 → ℤ => ℂ) 2 m) (y n))
        ((lp.evalCLM ℂ (fun _ : Fin 3 → ℤ => ℂ) 2 m) Y) :=
      (lp.evalCLM ℂ (fun _ : Fin 3 → ℤ => ℂ) 2 m).hasSum hys.hasSum
    have h2 : HasSum (fun n => (lp.evalCLM ℂ (fun _ : Fin 3 → ℤ => ℂ) 2 m) (y n))
        (((Real.sqrt (trigWeight r m) : ℝ) : ℂ) * mFourierCoeff ⇑F m) := by
      have := (hcoef m).mul_left (((Real.sqrt (trigWeight r m) : ℝ) : ℂ))
      simpa [y, lp.evalCLM, wseq_apply] using this
    exact h1.unique h2
  have hsq : ∀ m, ‖(Y : (Fin 3 → ℤ) → ℂ) m‖ ^ (2 : ENNReal).toReal =
      trigWeight r m * ‖mFourierCoeff ⇑F m‖ ^ 2 := by
    intro m
    rw [hYm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      ENNReal.toReal_ofNat, Real.rpow_two, mul_pow, Real.sq_sqrt (trigWeight_nonneg r m)]
  have hsumm : Summable fun m => trigWeight r m * ‖mFourierCoeff ⇑F m‖ ^ 2 := by
    have := (lp.memℓp Y).summable (by norm_num)
    simpa only [hsq] using this
  refine ⟨hsumm, ?_⟩
  have hnorm : ‖Y‖ = Real.sqrt (trigSobSq r ⇑F) := by
    have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) Y
    simp only [hsq] at h
    rw [ENNReal.toReal_ofNat, Real.rpow_two] at h
    rw [trigSobSq, ← h, Real.sqrt_sq (norm_nonneg _)]
  rw [← hnorm]
  refine (norm_tsum_le_tsum_norm hy).trans (le_of_eq ?_)
  simp [y, norm_wseq]

/-! ### The class of trigonometric polynomials -/

/-- `F` is a trigonometric polynomial. -/
def IsTP (F : C(UnitAddTorus (Fin 3), ℂ)) : Prop :=
  ∃ (S : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ℂ), F = tp S a

theorem IsTP.mul {F G : C(UnitAddTorus (Fin 3), ℂ)} (hF : IsTP F) (hG : IsTP G) :
    IsTP (F * G) := by
  obtain ⟨S, a, rfl⟩ := hF
  obtain ⟨T, b, rfl⟩ := hG
  exact ⟨_, _, tp_mul S T a b⟩

theorem tp_add (S T : Finset (Fin 3 → ℤ)) (a b : (Fin 3 → ℤ) → ℂ) :
    tp S a + tp T b = tp (S ∪ T) (fun m => (if m ∈ S then a m else 0) + if m ∈ T then b m else 0) := by
  classical
  ext x
  simp only [tp, ContinuousMap.add_apply, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, ite_mul,
    zero_mul]
  rw [Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.union_inter_cancel_left,
    Finset.union_inter_cancel_right]

theorem IsTP.add {F G : C(UnitAddTorus (Fin 3), ℂ)} (hF : IsTP F) (hG : IsTP G) :
    IsTP (F + G) := by
  obtain ⟨S, a, rfl⟩ := hF
  obtain ⟨T, b, rfl⟩ := hG
  exact ⟨_, _, tp_add S T a b⟩

theorem IsTP.smul {F : C(UnitAddTorus (Fin 3), ℂ)} (hF : IsTP F) (c : ℂ) : IsTP (c • F) := by
  obtain ⟨S, a, rfl⟩ := hF
  refine ⟨S, fun m => c * a m, ?_⟩
  simp only [tp, smul_sum, smul_smul]

theorem IsTP.neg {F : C(UnitAddTorus (Fin 3), ℂ)} (hF : IsTP F) : IsTP (-F) := by
  have e : -F = (-1 : ℂ) • F := by ext x; simp
  rw [e]; exact hF.smul (-1)

theorem IsTP.sub {F G : C(UnitAddTorus (Fin 3), ℂ)} (hF : IsTP F) (hG : IsTP G) :
    IsTP (F - G) := by
  rw [sub_eq_add_neg]; exact hF.add hG.neg

theorem mFourier_zero' : (mFourier (0 : Fin 3 → ℤ) : C(UnitAddTorus (Fin 3), ℂ)) = 1 := by
  ext x; simp [mFourier]

theorem isTP_const (c : ℂ) : IsTP (ContinuousMap.const _ c) := by
  refine ⟨{0}, fun _ => c, ?_⟩
  ext x
  simp [tp, mFourier_zero']

theorem isTP_interp {N : ℕ} [NeZero N] (u : Grid N → ℂ) : IsTP (interp u) := by
  classical
  refine ⟨(univ : Finset (Grid N)).image freqVec, fun m => mFourierCoeff ⇑(interp u) m, ?_⟩
  have hc : ∀ k, mFourierCoeff ⇑(interp u) (freqVec k) = dft u k := mFourierCoeff_interp_freqVec u
  rw [tp, sum_image (fun a _ b _ h => freqVec_injective h)]
  simp only [hc]
  rfl

theorem IsTP.summable {F : C(UnitAddTorus (Fin 3), ℂ)} (hF : IsTP F) (s : ℕ) :
    Summable fun n => trigWeight s n * ‖mFourierCoeff ⇑F n‖ ^ 2 := by
  obtain ⟨S, a, rfl⟩ := hF; exact summable_tp s S a

/-- The trigonometric Sobolev norm `‖F‖_{H^s}`. -/
def sn (s : ℕ) (F : UnitAddTorus (Fin 3) → ℂ) : ℝ := Real.sqrt (trigSobSq s F)

theorem sn_nonneg (s : ℕ) (F : UnitAddTorus (Fin 3) → ℂ) : 0 ≤ sn s F := Real.sqrt_nonneg _

theorem wseq_add (s : ℕ) (F G : C(UnitAddTorus (Fin 3), ℂ)) (hF hG hFG) :
    wseq s (F + G) hFG = wseq s F hF + wseq s G hG := by
  ext m
  simp only [lp.coeFn_add, Pi.add_apply, wseq_apply, mFourierCoeff_add, mul_add]

theorem sn_add_le (s : ℕ) {F G : C(UnitAddTorus (Fin 3), ℂ)} (hF : IsTP F) (hG : IsTP G) :
    sn s ⇑(F + G) ≤ sn s ⇑F + sn s ⇑G := by
  have h := norm_add_le (wseq s F (hF.summable s)) (wseq s G (hG.summable s))
  rw [← wseq_add s F G (hF.summable s) (hG.summable s) ((hF.add hG).summable s),
    norm_wseq, norm_wseq, norm_wseq] at h
  exact h

theorem sn_smul (s : ℕ) (c : ℂ) (F : C(UnitAddTorus (Fin 3), ℂ)) :
    sn s ⇑(c • F) = ‖c‖ * sn s ⇑F := by
  unfold sn trigSobSq
  have e : ∀ n, trigWeight s n * ‖mFourierCoeff ⇑(c • F) n‖ ^ 2 =
      ‖c‖ ^ 2 * (trigWeight s n * ‖mFourierCoeff ⇑F n‖ ^ 2) := by
    intro n; rw [mFourierCoeff_smul', smul_eq_mul, norm_mul]; ring
  simp only [e]
  rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem sn_sum_le (s : ℕ) {κ : Type*} (t : Finset κ) {F : κ → C(UnitAddTorus (Fin 3), ℂ)}
    (hF : ∀ i, IsTP (F i)) : IsTP (∑ i ∈ t, F i) ∧ sn s ⇑(∑ i ∈ t, F i) ≤ ∑ i ∈ t, sn s ⇑(F i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨⟨∅, 0, by simp [tp]⟩, ?_⟩
    simp [sn, trigSobSq, mFourierCoeff]
  | insert a t ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact ⟨(hF a).add ih.1, (sn_add_le s (hF a) ih.1).trans (add_le_add le_rfl ih.2)⟩

/-- Product algebra in norm form for trigonometric polynomials. -/
theorem sn_mul_le (s : ℕ) (hs : 2 ≤ s) :
    ∃ K ≥ 1, ∀ F G : C(UnitAddTorus (Fin 3), ℂ), IsTP F → IsTP G →
      sn s ⇑(F * G) ≤ K * sn s ⇑F * sn s ⇑G := by
  obtain ⟨K, hK, h⟩ := trigSobSq_tp_mul_le s hs
  refine ⟨max (Real.sqrt K) 1, le_max_right _ _, fun F G hF hG => ?_⟩
  obtain ⟨S, a, rfl⟩ := hF
  obtain ⟨T, b, rfl⟩ := hG
  have h1 := Real.sqrt_le_sqrt (h S T a b)
  rw [Real.sqrt_mul (mul_nonneg hK (trigSobSq_nonneg' _ _)), Real.sqrt_mul hK] at h1
  refine h1.trans ?_
  unfold sn
  gcongr
  exact le_max_left _ _

theorem sn_prod_le (s : ℕ) {K : ℝ} (hK1 : 1 ≤ K)
    (hK : ∀ F G : C(UnitAddTorus (Fin 3), ℂ), IsTP F → IsTP G →
      sn s ⇑(F * G) ≤ K * sn s ⇑F * sn s ⇑G) :
    ∀ (n : ℕ) (F : Fin (n + 1) → C(UnitAddTorus (Fin 3), ℂ)), (∀ k, IsTP (F k)) →
      IsTP (∏ k, F k) ∧ sn s ⇑(∏ k, F k) ≤ K ^ n * ∏ k, sn s ⇑(F k)
  | 0, F, hF => by simp [hF 0]
  | n + 1, F, hF => by
    obtain ⟨ih1, ih2⟩ := sn_prod_le s hK1 hK n (fun k => F k.succ) (fun k => hF k.succ)
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ (fun k => sn s ⇑(F k))]
    refine ⟨(hF 0).mul ih1, (hK _ _ (hF 0) ih1).trans ?_⟩
    have h0 := sn_nonneg s ⇑(F 0)
    calc K * sn s ⇑(F 0) * sn s ⇑(∏ k : Fin (n + 1), F k.succ)
        ≤ K * sn s ⇑(F 0) * (K ^ n * ∏ k : Fin (n + 1), sn s ⇑(F k.succ)) := by gcongr
      _ = K ^ (n + 1) * (sn s ⇑(F 0) * ∏ k : Fin (n + 1), sn s ⇑(F k.succ)) := by ring

theorem trigWeight_mono {r r' : ℕ} (h : r ≤ r') (n : Fin 3 → ℤ) :
    trigWeight r n ≤ trigWeight r' n :=
  sum_le_sum_of_subset_of_nonneg
    (fun α hα => mem_multiIndices.mpr ((mem_multiIndices.mp hα).trans h))
    (fun _ _ _ => tsymSq_nonneg _ _)

theorem sn_mono {r r' : ℕ} (h : r ≤ r') {F : C(UnitAddTorus (Fin 3), ℂ)} (hF : IsTP F) :
    sn r ⇑F ≤ sn r' ⇑F := by
  obtain ⟨S, a, rfl⟩ := hF
  unfold sn
  rw [trigSobSq_tp, trigSobSq_tp]
  exact Real.sqrt_le_sqrt (sum_le_sum fun n _ =>
    mul_le_mul_of_nonneg_right (trigWeight_mono h n) (sq_nonneg _))

/-- The embedding constant `Σ_n W₂(n)^{-1}`. -/
def cEmb : ℝ := ∑' n : Fin 3 → ℤ, (trigWeight 2 n)⁻¹

theorem cEmb_nonneg : 0 ≤ cEmb := tsum_nonneg fun n => (inv_pos.mpr (trigWeight_pos 2 n)).le

/-- **Uniform embedding `H² ⊂ C⁰`** for trigonometric polynomials: `‖F‖_∞ ≤ √c ‖F‖_{H²}`. -/
theorem norm_le_sn_two {F : C(UnitAddTorus (Fin 3), ℂ)} (hF : IsTP F) :
    ‖F‖ ≤ Real.sqrt cEmb * sn 2 ⇑F := by
  obtain ⟨S, a, rfl⟩ := hF
  have hcoef : ∀ m ∈ S, mFourierCoeff ⇑(tp S a) m = a m := fun m hm => by
    rw [mFourierCoeff_tp, if_pos hm]
  have h1 : ‖tp S a‖ ≤ ∑ m ∈ S, ‖a m‖ := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_)
    rw [norm_smul]
    have : ‖(mFourier m : C(UnitAddTorus (Fin 3), ℂ))‖ ≤ 1 := by
      refine (ContinuousMap.norm_le _ zero_le_one).mpr fun x => ?_
      simp [mFourier, Circle.norm_coe]
    calc ‖a m‖ * ‖(mFourier m : C(UnitAddTorus (Fin 3), ℂ))‖ ≤ ‖a m‖ * 1 := by gcongr
      _ = ‖a m‖ := mul_one _
  refine h1.trans ?_
  have hW : ∀ m, 0 < trigWeight 2 m := fun m => trigWeight_pos 2 m
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun m => Real.sqrt ((trigWeight 2 m)⁻¹))
    (fun m => Real.sqrt (trigWeight 2 m) * ‖a m‖)
  have e : ∀ m, Real.sqrt ((trigWeight 2 m)⁻¹) * (Real.sqrt (trigWeight 2 m) * ‖a m‖) = ‖a m‖ := by
    intro m
    rw [← mul_assoc, ← Real.sqrt_mul (inv_pos.mpr (hW m)).le, inv_mul_cancel₀ (hW m).ne',
      Real.sqrt_one, one_mul]
  simp only [e] at hcs
  have e2 : ∀ m, Real.sqrt ((trigWeight 2 m)⁻¹) ^ 2 = (trigWeight 2 m)⁻¹ := fun m =>
    Real.sq_sqrt (inv_pos.mpr (hW m)).le
  have e3 : ∀ m, (Real.sqrt (trigWeight 2 m) * ‖a m‖) ^ 2 = trigWeight 2 m * ‖a m‖ ^ 2 := by
    intro m; rw [mul_pow, Real.sq_sqrt (hW m).le]
  simp only [e2, e3] at hcs
  have hB : ∑ m ∈ S, (trigWeight 2 m)⁻¹ ≤ cEmb :=
    (summable_inv_trigWeight 2 le_rfl).sum_le_tsum _ (fun m _ => (inv_pos.mpr (hW m)).le)
  have hsn : sn 2 ⇑(tp S a) = Real.sqrt (∑ m ∈ S, trigWeight 2 m * ‖a m‖ ^ 2) := by
    rw [sn, trigSobSq_tp]
  rw [hsn, ← Real.sqrt_mul cEmb_nonneg]
  refine Real.le_sqrt_of_sq_le (hcs.trans ?_)
  exact mul_le_mul_of_nonneg_right hB (sum_nonneg fun m _ => by have := hW m; positivity)

theorem interp_const {N : ℕ} [NeZero N] (c : ℂ) :
    interp (fun _ : Grid N => c) = ContinuousMap.const _ c := by
  have hdft : ∀ k : Grid N, dft (fun _ : Grid N => c) k = if (0 : Grid N) = k then c else 0 := by
    intro k
    have h := dft_latticeChar (N := N) 0 k
    have e : (fun _ : Grid N => c) = c • fun x => latticeChar (0 : Grid N) x := by
      funext x
      simp [latticeChar_comm 0 x, latticeChar_zero_right]
    rw [e, dft_smul, h]
    split_ifs <;> simp
  have h0 : freqVec (0 : Grid N) = 0 := by funext i; simp [freqVec, freq]
  ext x
  rw [interp, ContinuousMap.coe_sum, Finset.sum_apply, Finset.sum_eq_single (0 : Grid N)]
  · rw [ContinuousMap.coe_smul, Pi.smul_apply, hdft, if_pos rfl, h0, smul_eq_mul]
    simp [mFourier]
  · intro k _ hk
    rw [ContinuousMap.coe_smul, Pi.smul_apply, hdft, if_neg (Ne.symm hk), zero_smul]
  · simp

theorem interp_add {N : ℕ} [NeZero N] (u w : Grid N → ℂ) :
    interp (u + w) = interp u + interp w := by
  ext x
  simp only [interp, ContinuousMap.add_apply, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, dft_add, add_mul, Finset.sum_add_distrib]

theorem interp_smul {N : ℕ} [NeZero N] (c : ℂ) (u : Grid N → ℂ) :
    interp (c • u) = c • interp u := by
  ext x
  simp only [interp, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
    Pi.smul_apply, smul_eq_mul, dft_smul, Finset.mul_sum, mul_assoc]

/-- The sampling projector `𝒫_h` as a continuous linear map on `C(𝕋³, ℂ)`. -/
def projL (N : ℕ) [NeZero N] : C(UnitAddTorus (Fin 3), ℂ) →L[ℂ] C(UnitAddTorus (Fin 3), ℂ) :=
  (LinearMap.toContinuousLinearMap
    ({ toFun := interp, map_add' := interp_add, map_smul' := interp_smul } :
      (Grid N → ℂ) →ₗ[ℂ] C(UnitAddTorus (Fin 3), ℂ))).comp
    (ContinuousLinearMap.pi fun x => ContinuousMap.evalCLM (R := ℂ) (samplePt x))

theorem projL_apply (N : ℕ) [NeZero N] (F : C(UnitAddTorus (Fin 3), ℂ)) :
    projL N F = proj N ⇑F := rfl

theorem projL_const (N : ℕ) [NeZero N] (c : ℂ) :
    projL N (ContinuousMap.const _ c) = ContinuousMap.const _ c := by
  rw [projL_apply, proj]
  exact interp_const c

/-! ### Analytic composition consistency -/

section CompositionSection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinate expansion of a complex multilinear map on the diagonal. -/
theorem cml_diag_eq {n : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ)
    (w : ι → ℂ) :
    q (fun _ => w) = ∑ ρ : Fin n → ι, (∏ k, w (ρ k)) * q (fun k => Pi.single (ρ k) 1) := by
  have hw : w = ∑ j, w j • (Pi.single j 1 : ι → ℂ) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  rw [q.map_sum (fun _ j => w j • (Pi.single j 1 : ι → ℂ))]
  refine sum_congr rfl fun ρ _ => ?_
  rw [q.map_smul_univ (fun k => w (ρ k)) (fun k => Pi.single (ρ k) 1), smul_eq_mul]

theorem norm_pi_single_one (j : ι) : ‖(Pi.single j 1 : ι → ℂ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  by_cases h : i = j
  · subst h; simp
  · simp [Pi.single_apply, h]

/-- The `n`-th Taylor term `y ↦ p_n(v(y), …, v(y))` as a combination of products. -/
def taylorTerm {n : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ)
    (v : ι → C(UnitAddTorus (Fin 3), ℂ)) : C(UnitAddTorus (Fin 3), ℂ) :=
  ∑ ρ : Fin n → ι, q (fun k => Pi.single (ρ k) 1) • ∏ k, v (ρ k)

theorem taylorTerm_apply {n : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ)
    (v : ι → C(UnitAddTorus (Fin 3), ℂ)) (y : UnitAddTorus (Fin 3)) :
    taylorTerm q v y = q (fun _ => fun j => v j y) := by
  rw [cml_diag_eq]
  simp only [taylorTerm, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
    Pi.smul_apply, smul_eq_mul, ContinuousMap.coe_prod, Finset.prod_apply]
  exact sum_congr rfl fun ρ _ => mul_comm _ _

theorem isTP_taylorTerm {n : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ)
    {v : ι → C(UnitAddTorus (Fin 3), ℂ)} (hv : ∀ j, IsTP (v j)) : IsTP (taylorTerm q v) := by
  have hprod : ∀ ρ : Fin n → ι, IsTP (∏ k, v (ρ k)) := by
    intro ρ
    rcases n with _ | m
    · simp only [univ_eq_empty, prod_empty]
      have := isTP_const 1
      convert this using 1
      ext; simp
    · obtain ⟨K, hK1, hK⟩ := sn_mul_le 2 le_rfl
      exact (sn_prod_le 2 hK1 hK m (fun k => v (ρ k)) (fun k => hv _)).1
  exact (sn_sum_le 0 univ (fun ρ => (hprod ρ).smul _)).1

theorem norm_taylorTerm_le {n : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ)
    (v : ι → C(UnitAddTorus (Fin 3), ℂ)) :
    ‖taylorTerm q v‖ ≤ ‖q‖ * (∑ j, ‖v j‖) ^ n := by
  unfold taylorTerm
  refine (norm_sum_le _ _).trans ?_
  have hq : ∀ ρ : Fin n → ι, ‖q (fun k => Pi.single (ρ k) 1)‖ ≤ ‖q‖ := by
    intro ρ
    refine (q.le_opNorm _).trans ?_
    calc ‖q‖ * ∏ k, ‖(Pi.single (ρ k) 1 : ι → ℂ)‖ ≤ ‖q‖ * ∏ _k : Fin n, (1 : ℝ) := by
          gcongr with k; exact norm_pi_single_one _
      _ = ‖q‖ := by simp
  calc ∑ ρ : Fin n → ι, ‖q (fun k => Pi.single (ρ k) 1) • ∏ k, v (ρ k)‖
      ≤ ∑ ρ : Fin n → ι, ‖q‖ * ∏ k, ‖v (ρ k)‖ := by
        refine sum_le_sum fun ρ _ => ?_
        rw [norm_smul]
        exact mul_le_mul (hq ρ) (Finset.norm_prod_le _ _) (norm_nonneg _) (norm_nonneg _)
    _ = ‖q‖ * (∑ j, ‖v j‖) ^ n := by
        rw [← mul_sum, ← Fintype.prod_sum (fun (_ : Fin n) j => ‖v j‖)]
        simp

end CompositionSection

section CompositionMain

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sn_interp_le {N : ℕ} [NeZero N] (r : ℕ) (u : Grid N → ℂ) :
    sn r ⇑(interp u) ≤ (π / 2) ^ r * sobNorm r u := by
  have h := Real.sqrt_le_sqrt (trigSobSq_interp_le r u)
  rw [Real.sqrt_mul (by positivity), ← pow_mul, show 2 * r = r * 2 by ring, pow_mul,
    Real.sqrt_sq (by positivity)] at h
  exact h

theorem sn_taylorTerm_le (s : ℕ) {K : ℝ} (hK1 : 1 ≤ K)
    (hK : ∀ F G : C(UnitAddTorus (Fin 3), ℂ), IsTP F → IsTP G →
      sn s ⇑(F * G) ≤ K * sn s ⇑F * sn s ⇑G) {n : ℕ}
    (q : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => ι → ℂ) ℂ)
    {v : ι → C(UnitAddTorus (Fin 3), ℂ)} (hv : ∀ j, IsTP (v j)) :
    sn s ⇑(taylorTerm q v) ≤ ‖q‖ * K ^ n * (∑ j, sn s ⇑(v j)) ^ (n + 1) := by
  have hprod : ∀ ρ : Fin (n + 1) → ι, IsTP (∏ k, v (ρ k)) ∧
      sn s ⇑(∏ k, v (ρ k)) ≤ K ^ n * ∏ k, sn s ⇑(v (ρ k)) := fun ρ =>
    sn_prod_le s hK1 hK n (fun k => v (ρ k)) (fun k => hv _)
  have hsum := sn_sum_le s univ (F := fun ρ : Fin (n + 1) → ι =>
    q (fun k => Pi.single (ρ k) 1) • ∏ k, v (ρ k)) (fun ρ => (hprod ρ).1.smul _)
  refine hsum.2.trans ?_
  have hq : ∀ ρ : Fin (n + 1) → ι, ‖q (fun k => Pi.single (ρ k) 1)‖ ≤ ‖q‖ := by
    intro ρ
    refine (q.le_opNorm _).trans ?_
    calc ‖q‖ * ∏ k, ‖(Pi.single (ρ k) 1 : ι → ℂ)‖ ≤ ‖q‖ * ∏ _k : Fin (n + 1), (1 : ℝ) := by
          gcongr with k; exact norm_pi_single_one _
      _ = ‖q‖ := by simp
  calc ∑ ρ : Fin (n + 1) → ι, sn s ⇑(q (fun k => Pi.single (ρ k) 1) • ∏ k, v (ρ k))
      ≤ ∑ ρ : Fin (n + 1) → ι, ‖q‖ * (K ^ n * ∏ k, sn s ⇑(v (ρ k))) := by
        refine sum_le_sum fun ρ _ => ?_
        rw [sn_smul]
        exact mul_le_mul (hq ρ) (hprod ρ).2 (sn_nonneg _ _) (norm_nonneg _)
    _ = ‖q‖ * K ^ n * (∑ j, sn s ⇑(v j)) ^ (n + 1) := by
        rw [← mul_sum, ← mul_sum, ← Fintype.prod_sum (fun (_ : Fin (n + 1)) j => sn s ⇑(v j))]
        simp only [prod_const, card_univ, Fintype.card_fin]
        ring

/-- **Analytic composition consistency** (`eq:supp-open-composition-consistency`).  Let
`A : ℂ^ι → ℂ` be analytic at the constant base point `c` (a convergent power series on a ball;
the coefficient maps of the chart are restrictions of such maps) and `r ≥ 1`.  There are
`δ > 0` and `C`, independent of the mesh, such that for every `N` and every family of grid arrays
`u = (u_j)_{j ∈ ι}` in the small chart `Σ_j ‖u_j - c_j‖_{r+1,h} ≤ δ`,
`‖𝓘_h A(u_h) - A(𝓘_h u_h)‖²_{H^r} ≤ C h² (Σ_j ‖u_j - c_j‖_{r+1,h})²`. -/
theorem composition_consistency (r : ℕ) (hr : 1 ≤ r) {A : (ι → ℂ) → ℂ}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) ℂ} {c : ι → ℂ} {R : ENNReal}
    (hA : HasFPowerSeriesOnBall A p c R) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (u : ι → Grid N → ℂ),
      ∑ j, sobNorm (r + 1) (u j - fun _ => c j) ≤ δ →
      trigSobSq r (fun y => interp (fun x => A (fun j => u j x)) y -
          A (fun j => interp (u j) y)) ≤
        C * ((N : ℝ) ^ 2)⁻¹ * (∑ j, sobNorm (r + 1) (u j - fun _ => c j)) ^ 2 := by
  obtain ⟨C1, hC1, hE⟩ := sampling_error r 1 (by omega)
  obtain ⟨K, hK1, hK⟩ := sn_mul_le (r + 1) (by omega)
  obtain ⟨ρ, hρ0, hρR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hA.r_pos
  obtain ⟨Cp, hCp, hpn⟩ := p.norm_mul_pow_le_of_lt_radius (hρR.trans_le hA.r_le)
  have hρ : (0 : ℝ) < ρ := NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hρ0)
  set cπ : ℝ := (π / 2) ^ (r + 1) with hcπ
  have hcπ0 : 0 < cπ := by positivity
  set L : ℝ := K + Real.sqrt cEmb + 1
  have hL : 0 < L := by positivity
  set δ : ℝ := ρ / (2 * cπ * L)
  have hδ : 0 < δ := by positivity
  set Cfin : ℝ := (4 * Real.sqrt C1 * Cp * K * cπ / ρ) ^ 2
  refine ⟨δ, hδ, Cfin, by positivity, fun N _ u hu => ?_⟩
  set σ := ∑ j, sobNorm (r + 1) (u j - fun _ => c j) with hσdef
  have hσ0 : 0 ≤ σ := sum_nonneg fun j _ => Real.sqrt_nonneg _
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  -- the interpolated deviations
  set v : ι → C(UnitAddTorus (Fin 3), ℂ) := fun j => interp (u j - fun _ => c j)
  have hv : ∀ j, IsTP (v j) := fun j => isTP_interp _
  set S := ∑ j, sn (r + 1) ⇑(v j) with hSdef
  have hS0 : 0 ≤ S := sum_nonneg fun j _ => sn_nonneg _ _
  have hSσ : S ≤ cπ * σ := by
    rw [hSdef, hσdef, mul_sum]
    exact sum_le_sum fun j _ => sn_interp_le (r + 1) _
  have hcπσ : cπ * σ ≤ ρ / (2 * L) := by
    calc cπ * σ ≤ cπ * δ := mul_le_mul_of_nonneg_left hu hcπ0.le
      _ = ρ / (2 * L) := by
          rw [show δ = ρ / (2 * cπ * L) from rfl]
          field_simp
  set x : ℝ := K * S / ρ
  have hx0 : 0 ≤ x := by positivity
  have hx : x ≤ 1 / 2 := by
    rw [div_le_iff₀ hρ]
    have : K * S ≤ L * (cπ * σ) := by
      calc K * S ≤ K * (cπ * σ) := mul_le_mul_of_nonneg_left hSσ (by linarith)
        _ ≤ L * (cπ * σ) := by
            gcongr
            have := Real.sqrt_nonneg cEmb
            linarith
    have h2 : L * (cπ * σ) ≤ ρ / 2 := by
      calc L * (cπ * σ) ≤ L * (ρ / (2 * L)) := mul_le_mul_of_nonneg_left hcπσ hL.le
        _ = ρ / 2 := by field_simp
    linarith
  -- the sup bound
  have hsup : ∑ j, ‖v j‖ ≤ Real.sqrt cEmb * S := by
    rw [hSdef, mul_sum]
    exact sum_le_sum fun j _ => (norm_le_sn_two (hv j)).trans
      (mul_le_mul_of_nonneg_left (sn_mono (by omega) (hv j)) (Real.sqrt_nonneg _))
  set z : ℝ := (∑ j, ‖v j‖) / ρ
  have hz0 : 0 ≤ z := by positivity
  have hz : z ≤ 1 / 2 := by
    rw [div_le_iff₀ hρ]
    have : Real.sqrt cEmb * S ≤ L * (cπ * σ) := by
      calc Real.sqrt cEmb * S ≤ Real.sqrt cEmb * (cπ * σ) :=
            mul_le_mul_of_nonneg_left hSσ (Real.sqrt_nonneg _)
        _ ≤ L * (cπ * σ) := by
            gcongr
            linarith
    have h2 : L * (cπ * σ) ≤ ρ / 2 := by
      calc L * (cπ * σ) ≤ L * (ρ / (2 * L)) := mul_le_mul_of_nonneg_left hcπσ hL.le
        _ = ρ / 2 := by field_simp
    linarith
  -- the Taylor terms
  set T : ℕ → C(UnitAddTorus (Fin 3), ℂ) := fun n => taylorTerm (p n) v
  have hTnorm : ∀ n, ‖T n‖ ≤ Cp * (1 / 2) ^ n := by
    intro n
    refine (norm_taylorTerm_le (p n) v).trans ?_
    have h1 : ‖p n‖ ≤ Cp / (ρ : ℝ) ^ n := by
      rw [le_div_iff₀ (by positivity)]; exact hpn n
    calc ‖p n‖ * (∑ j, ‖v j‖) ^ n ≤ Cp / (ρ : ℝ) ^ n * (∑ j, ‖v j‖) ^ n :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = Cp * z ^ n := by rw [div_pow]; field_simp
      _ ≤ Cp * (1 / 2) ^ n := by gcongr
  have hTs : Summable T :=
    Summable.of_norm_bounded (summable_geometric_two.mul_left Cp) hTnorm
  set Fsum := ∑' n, T n
  have hT : HasSum T Fsum := hTs.hasSum
  -- pointwise identification `Fsum = A(c + v)`
  have hFsum : ∀ y, Fsum y = A (c + fun j => v j y) := by
    intro y
    have h1 : HasSum (fun n => T n y) (Fsum y) :=
      (ContinuousMap.evalCLM (R := ℂ) y).hasSum hT
    have hmem : (fun j => v j y) ∈ Metric.eball (0 : ι → ℂ) R := by
      rw [Metric.mem_eball, edist_zero_right]
      refine lt_of_le_of_lt ?_ hρR
      rw [enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
      have hle : ‖fun j => v j y‖ ≤ ∑ j, ‖v j‖ := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
        exact ((v j).norm_coe_le_norm y).trans
          (single_le_sum (f := fun j => ‖v j‖) (fun _ _ => norm_nonneg _) (mem_univ j))
      have : ∑ j, ‖v j‖ ≤ ρ / 2 := by
        have := (div_le_iff₀ hρ).mp hz
        linarith
      linarith
    have h2 := hA.hasSum hmem
    have e : (fun n => T n y) = fun n => p n (fun _ => fun j => v j y) := by
      funext n; exact taylorTerm_apply (p n) v y
    rw [e] at h1
    exact h1.unique h2
  -- the sampling error terms
  set G : ℕ → C(UnitAddTorus (Fin 3), ℂ) := fun n => projL N (T n) - T n
  have hG : HasSum G (projL N Fsum - Fsum) := ((projL N).hasSum hT).sub hT
  have hGzero : G 0 = 0 := by
    have hT0 : T 0 = ContinuousMap.const _ (p 0 (fun _ => 0)) := by
      ext y
      rw [taylorTerm_apply, ContinuousMap.const_apply]
      congr 1
      funext k; exact k.elim0
    simp only [G, hT0, projL_const, sub_self]
  set bnd : ℕ → ℝ := fun n => Real.sqrt C1 * (N : ℝ)⁻¹ * Cp * x * 2 * (1 / 2) ^ n
  have hGb : ∀ n, sn r ⇑(G n) ≤ bnd n := by
    intro n
    rcases n with _ | m
    · rw [hGzero]
      have : sn r ⇑(0 : C(UnitAddTorus (Fin 3), ℂ)) = 0 := by
        simp [sn, trigSobSq, mFourierCoeff]
      rw [this]; positivity
    · have hTP := isTP_taylorTerm (p (m + 1)) hv
      obtain ⟨-, hb⟩ := hE N (T (m + 1)) (hTP.summable _)
      have h1 : sn r ⇑(G (m + 1)) ≤ Real.sqrt C1 * (N : ℝ)⁻¹ * sn (r + 1) ⇑(T (m + 1)) := by
        have := Real.sqrt_le_sqrt hb
        rw [pow_one, Real.sqrt_mul (by positivity), Real.sqrt_mul hC1, Real.sqrt_inv,
          Real.sqrt_sq hN.le] at this
        exact this
      have h2 := sn_taylorTerm_le (r + 1) hK1 hK (p (m + 1)) hv
      have h3 : ‖p (m + 1)‖ ≤ Cp / (ρ : ℝ) ^ (m + 1) := by
        rw [le_div_iff₀ (by positivity)]; exact hpn _
      have h4 : ‖p (m + 1)‖ * K ^ m * S ^ (m + 1) ≤ Cp * x ^ (m + 1) := by
        calc ‖p (m + 1)‖ * K ^ m * S ^ (m + 1) ≤ Cp / (ρ : ℝ) ^ (m + 1) * K ^ (m + 1) *
              S ^ (m + 1) := by
              gcongr
              exact Nat.le_succ m
          _ = Cp * x ^ (m + 1) := by rw [div_pow, mul_pow]; field_simp
      have h5 : x ^ (m + 1) ≤ x * 2 * (1 / 2) ^ (m + 1) := by
        rw [pow_succ', show x * 2 * (1 / 2) ^ (m + 1) = x * (1 / 2) ^ m by ring]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx m) hx0
      calc sn r ⇑(G (m + 1)) ≤ Real.sqrt C1 * (N : ℝ)⁻¹ * sn (r + 1) ⇑(T (m + 1)) := h1
        _ ≤ Real.sqrt C1 * (N : ℝ)⁻¹ * (Cp * (x * 2 * (1 / 2) ^ (m + 1))) := by
            gcongr
            exact h2.trans (h4.trans (mul_le_mul_of_nonneg_left h5 hCp.le))
        _ = bnd (m + 1) := by simp only [bnd]; ring
  have hbs : Summable bnd := summable_geometric_two.mul_left _
  have hGs : Summable fun n => sn r ⇑(G n) :=
    Summable.of_nonneg_of_le (fun n => sn_nonneg _ _) hGb hbs
  have hGsum : ∀ n, Summable fun m => trigWeight r m * ‖mFourierCoeff ⇑(G n) m‖ ^ 2 := by
    intro n
    have hTP := isTP_taylorTerm (p n) hv
    have hP : IsTP (projL N (T n)) := isTP_interp _
    exact (hP.sub hTP).summable r
  obtain ⟨-, hMink⟩ := trigSobSq_tsum_le r hG hGsum hGs
  have hbsum : ∑' n, bnd n = Real.sqrt C1 * (N : ℝ)⁻¹ * Cp * x * 2 * 2 := by
    simp only [bnd]; rw [tsum_mul_left, tsum_geometric_two]
  -- identification of the error function
  have hEfun : (fun y => interp (fun x => A (fun j => u j x)) y - A (fun j => interp (u j) y)) =
      ⇑(projL N Fsum - Fsum) := by
    funext y
    have hsamp : sample N ⇑Fsum = fun x => A (fun j => u j x) := by
      funext x
      rw [sample, hFsum]
      congr 1
      funext j
      simp only [Pi.add_apply, v, interp_sample, Pi.sub_apply]
      ring
    have hy : (c + fun j => v j y) = fun j => interp (u j) y := by
      funext j
      simp only [Pi.add_apply, v]
      rw [show (u j - fun _ => c j) = u j + (-1 : ℂ) • (fun _ : Grid N => c j) by
        funext x; simp; ring, interp_add, interp_smul, interp_const]
      simp
    rw [ContinuousMap.sub_apply, projL_apply, proj, hsamp, hFsum, hy]
  rw [hEfun]
  have hsq : Real.sqrt (trigSobSq r ⇑(projL N Fsum - Fsum)) ≤
      Real.sqrt C1 * (N : ℝ)⁻¹ * Cp * x * 2 * 2 := by
    refine hMink.trans ?_
    rw [← hbsum]
    exact hGs.tsum_le_tsum hGb hbs
  have hfin := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
  rw [Real.sq_sqrt (trigSobSq_nonneg' _ _)] at hfin
  refine hfin.trans ?_
  have hxσ : x ≤ K * cπ * σ / ρ := by
    simp only [x]
    rw [div_le_div_iff_of_pos_right hρ]
    calc K * S ≤ K * (cπ * σ) := mul_le_mul_of_nonneg_left hSσ (by linarith)
      _ = K * cπ * σ := by ring
  calc (Real.sqrt C1 * (N : ℝ)⁻¹ * Cp * x * 2 * 2) ^ 2
      ≤ (Real.sqrt C1 * (N : ℝ)⁻¹ * Cp * (K * cπ * σ / ρ) * 2 * 2) ^ 2 := by
        gcongr
    _ = Cfin * ((N : ℝ) ^ 2)⁻¹ * σ ^ 2 := by
        simp only [Cfin]; field_simp; ring

end CompositionMain

end

end Composition

end RenewalGeometry.PeriodicGridSobolev
