/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicGridSobolevCalculus

/-!
# Trigonometric interpolation on the periodic grid and uniform norm equivalence

For a grid function `u : (ℤ/N)³ → ℂ` the trigonometric interpolant
`𝓘_h u = Σ_k û(k) e^{2πi ⟨k̃, x⟩}` (`interp`) is the genuine continuous function on the
unit torus `𝕋³ = UnitAddTorus (Fin 3)` (Mathlib's `mFourier` monomials) whose frequencies
`k̃ = freqVec k` are the signed representatives of the grid frequencies (the cube
`{-m, …, m}³` when `N = 2m + 1`).

* `interp_sample`: `𝓘_h u` interpolates the grid values, `𝓘_h u(x/N) = u(x)`.
* `mFourierCoeff_interp`: its Mathlib Fourier coefficients are `û(k)` on the signed cube and
  vanish elsewhere.
* `trigSobSq r f = Σ_{n ∈ ℤ³} Σ_{|α| ≤ r} Π_i (2π n_i)^{2α_i} |f̂(n)|²` is the trigonometric
  `H^r(𝕋³)` norm (`= Σ_{|α| ≤ r} ‖∂^α f‖²_{L²}` by Parseval), and
  `trigGradSq f = Σ_n 4π²|n|² |f̂(n)|² = ‖∇ f‖²_{L²}`.
* `sobSq_le_trigSobSq_interp`, `trigSobSq_interp_le_sobSq`
  (`lem:supp-open-calculus`, norm equivalence): uniformly in `N`,
  `(2/π)^{2r} ‖𝓘_h u‖²_{H^r} ≤ ‖u‖²_{r,h} ≤ ‖𝓘_h u‖²_{H^r}`, from the symbol comparison
  `4|k_i| ≤ |d_i(k)| ≤ 2π|k_i|`.
* `coordForm_le_trigGradSq_interp`, `trigGradSq_interp_le_coordForm`: the same comparison for
  the coordinate Dirichlet form `Σ_i ‖D_i⁺ u‖_h²` and `‖∇ 𝓘_h u‖²_{L²}`.
-/

open Finset ComplexConjugate UnitAddTorus
open scoped BigOperators Real

namespace RenewalGeometry.PeriodicGridSobolev

open LatticeTorusPlancherel

set_option linter.unusedSectionVars false

/- The Haar probability measure on `UnitAddCircle` used by Mathlib's multidimensional Fourier
theory (`Mathlib.Analysis.Fourier.AddCircleMulti`). -/
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

variable {N : ℕ} [NeZero N]

/-- The signed frequency vector `k̃ ∈ ℤ³` of a grid frequency. -/
def freqVec (k : Grid N) : Fin 3 → ℤ := fun i => freq i k

theorem freqVec_injective : Function.Injective (freqVec (N := N)) := by
  intro k k' h
  funext i
  exact ZMod.injective_valMinAbs (congrFun h i)

/-- The trigonometric interpolant `𝓘_h u = Σ_k û(k) e_{k̃}` on the unit torus. -/
noncomputable def interp (u : Grid N → ℂ) : C(UnitAddTorus (Fin 3), ℂ) :=
  ∑ k, dft u k • mFourier (freqVec k)

/-- The grid point `x/N` of the unit torus. -/
noncomputable def samplePt (x : Grid N) : UnitAddTorus (Fin 3) :=
  fun i => (((x i).val : ℝ) / N : ℝ)

theorem mFourier_freqVec_samplePt (k x : Grid N) :
    mFourier (freqVec k) (samplePt x) = latticeChar k x := by
  simp only [mFourier, ContinuousMap.coe_mk, latticeChar, samplePt]
  refine prod_congr rfl fun i _ => ?_
  rw [fourier_coe_apply]
  have e : k i * x i = (((freq i k * ((x i).val : ℤ) : ℤ) : ZMod N)) := by
    push_cast
    rw [show ((freq i k : ℤ) : ZMod N) = k i from (k i).coe_valMinAbs]
    simp
  rw [e, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  simp only [freqVec]
  ring

/-- `𝓘_h u` interpolates the grid values: `𝓘_h u(x/N) = u(x)`. -/
theorem interp_sample (u : Grid N → ℂ) (x : Grid N) : interp u (samplePt x) = u x := by
  rw [← dft_inversion u x]
  simp only [interp, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, mFourier_freqVec_samplePt]
  refine sum_congr rfl fun k _ => mul_comm _ _

/-- Fourier coefficients of a finite trigonometric sum. -/
theorem mFourierCoeff_trigSum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (φ : ι → Fin 3 → ℤ)
    (n : Fin 3 → ℤ) :
    mFourierCoeff (⇑(∑ i ∈ s, a i • mFourier (φ i))) n =
      ∑ i ∈ s, if φ i = n then a i else 0 := by
  rw [← mFourierCoeff_toLp, ← mFourierBasis_repr]
  have hL : ContinuousMap.toLp 2 MeasureTheory.volume ℂ (∑ i ∈ s, a i • mFourier (φ i)) =
      ∑ i ∈ s, a i • mFourierBasis (φ i) := by
    rw [map_sum]
    simp only [map_smul, coe_mFourierBasis]
  rw [hL, map_sum]
  simp only [map_smul, HilbertBasis.repr_self]
  rw [lp.coeFn_sum, Finset.sum_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : φ i = n
  · simp [h]
  · simp [h, Ne.symm h]

/-- The Fourier coefficients of the interpolant are `û(k)` at the signed frequency `k̃` and
vanish off the signed cube. -/
theorem mFourierCoeff_interp (u : Grid N → ℂ) (n : Fin 3 → ℤ) :
    mFourierCoeff (⇑(interp u)) n = ∑ k, if freqVec k = n then dft u k else 0 :=
  mFourierCoeff_trigSum _ _ _ n

theorem mFourierCoeff_interp_freqVec (u : Grid N → ℂ) (k : Grid N) :
    mFourierCoeff (⇑(interp u)) (freqVec k) = dft u k := by
  rw [mFourierCoeff_interp, sum_eq_single k]
  · simp
  · intro b _ hb
    rw [if_neg]
    exact fun h => hb (freqVec_injective h)
  · simp

theorem mFourierCoeff_interp_of_not_mem (u : Grid N → ℂ) (n : Fin 3 → ℤ)
    (hn : n ∉ Set.range (freqVec (N := N))) : mFourierCoeff (⇑(interp u)) n = 0 := by
  rw [mFourierCoeff_interp]
  refine sum_eq_zero fun k _ => ?_
  rw [if_neg]
  exact fun h => hn ⟨k, h⟩

/-! ### Trigonometric Sobolev norms -/

/-- The symbol `|(2πi n)^α|² = Π_i (2π n_i)^{2α_i}` of `∂^α`. -/
noncomputable def tsymSq (α : Fin 3 → ℕ) (n : Fin 3 → ℤ) : ℝ :=
  ((2 * π * n 0) ^ 2) ^ α 0 * ((2 * π * n 1) ^ 2) ^ α 1 * ((2 * π * n 2) ^ 2) ^ α 2

/-- The trigonometric `H^r` weight `Σ_{|α| ≤ r} |(2πi n)^α|²`. -/
noncomputable def trigWeight (r : ℕ) (n : Fin 3 → ℤ) : ℝ :=
  ∑ α ∈ multiIndices r, tsymSq α n

/-- The squared trigonometric `H^r(𝕋³)` norm
`‖f‖²_{H^r} = Σ_{n ∈ ℤ³} Σ_{|α| ≤ r} |(2πi n)^α|² |f̂(n)|² = Σ_{|α| ≤ r} ‖∂^α f‖²_{L²}`. -/
noncomputable def trigSobSq (r : ℕ) (f : UnitAddTorus (Fin 3) → ℂ) : ℝ :=
  ∑' n, trigWeight r n * ‖mFourierCoeff f n‖ ^ 2

/-- The squared gradient norm `‖∇f‖²_{L²} = Σ_n 4π²|n|² |f̂(n)|²`. -/
noncomputable def trigGradSq (f : UnitAddTorus (Fin 3) → ℂ) : ℝ :=
  ∑' n, (∑ i, (2 * π * n i) ^ 2) * ‖mFourierCoeff f n‖ ^ 2

/-- A coefficient-weighted sum over `ℤ³` of the interpolant reduces to the finite cube. -/
theorem tsum_interp (W : (Fin 3 → ℤ) → ℝ) (u : Grid N → ℂ) :
    ∑' n, W n * ‖mFourierCoeff (⇑(interp u)) n‖ ^ 2 =
      ∑ k, W (freqVec k) * ‖dft u k‖ ^ 2 := by
  rw [tsum_eq_sum (s := (univ : Finset (Grid N)).image freqVec)]
  · rw [sum_image (fun a _ b _ h => freqVec_injective h)]
    refine sum_congr rfl fun k _ => ?_
    rw [mFourierCoeff_interp_freqVec]
  · intro n hn
    have : n ∉ Set.range (freqVec (N := N)) := by
      rintro ⟨k, rfl⟩
      exact hn (mem_image_of_mem _ (mem_univ k))
    rw [mFourierCoeff_interp_of_not_mem u n this]
    simp

theorem trigSobSq_interp (r : ℕ) (u : Grid N → ℂ) :
    trigSobSq r (interp u) = ∑ k, trigWeight r (freqVec k) * ‖dft u k‖ ^ 2 :=
  tsum_interp _ u

theorem trigGradSq_interp (u : Grid N → ℂ) :
    trigGradSq (interp u) = ∑ k, (∑ i, (2 * π * freqVec k i) ^ 2) * ‖dft u k‖ ^ 2 :=
  tsum_interp _ u

/-! ### Uniform norm equivalence -/

theorem norm_dsym_sq (α : Fin 3 → ℕ) (k : Grid N) :
    ‖dsym α k‖ ^ 2 =
      (‖sym 0 k‖ ^ 2) ^ α 0 * (‖sym 1 k‖ ^ 2) ^ α 1 * (‖sym 2 k‖ ^ 2) ^ α 2 := by
  simp only [dsym, norm_mul, norm_pow]
  ring

theorem norm_sym_sq_le_tsym (i : Fin 3) (k : Grid N) :
    ‖sym i k‖ ^ 2 ≤ (2 * π * freqVec k i) ^ 2 := by
  have := norm_sym_sq_le i k
  simp only [freqVec]
  nlinarith

theorem tsym_le_norm_sym_sq (i : Fin 3) (k : Grid N) :
    (2 / π) ^ 2 * (2 * π * freqVec k i) ^ 2 ≤ ‖sym i k‖ ^ 2 := by
  have := sq_le_norm_sym_sq i k
  have hπ : π ≠ 0 := Real.pi_ne_zero
  simp only [freqVec]
  calc (2 / π) ^ 2 * (2 * π * (freq i k : ℝ)) ^ 2 = 16 * (freq i k : ℝ) ^ 2 := by
        field_simp; ring
    _ ≤ _ := this

theorem norm_dsym_sq_le_tsymSq (α : Fin 3 → ℕ) (k : Grid N) :
    ‖dsym α k‖ ^ 2 ≤ tsymSq α (freqVec k) := by
  rw [norm_dsym_sq, tsymSq]
  have h0 := norm_sym_sq_le_tsym 0 k
  have h1 := norm_sym_sq_le_tsym 1 k
  have h2 := norm_sym_sq_le_tsym 2 k
  exact mul_le_mul (mul_le_mul (pow_le_pow_left₀ (by positivity) h0 _)
    (pow_le_pow_left₀ (by positivity) h1 _) (by positivity) (by positivity))
    (pow_le_pow_left₀ (by positivity) h2 _) (by positivity) (by positivity)

theorem tsymSq_le_norm_dsym_sq (α : Fin 3 → ℕ) (k : Grid N) :
    ((2 / π) ^ 2) ^ deg α * tsymSq α (freqVec k) ≤ ‖dsym α k‖ ^ 2 := by
  rw [norm_dsym_sq, tsymSq, deg, pow_add, pow_add]
  have h0 := tsym_le_norm_sym_sq 0 k
  have h1 := tsym_le_norm_sym_sq 1 k
  have h2 := tsym_le_norm_sym_sq 2 k
  calc ((2 / π) ^ 2) ^ α 0 * ((2 / π) ^ 2) ^ α 1 * ((2 / π) ^ 2) ^ α 2 *
        (((2 * π * freqVec k 0) ^ 2) ^ α 0 * ((2 * π * freqVec k 1) ^ 2) ^ α 1 *
          ((2 * π * freqVec k 2) ^ 2) ^ α 2)
      = ((2 / π) ^ 2 * (2 * π * freqVec k 0) ^ 2) ^ α 0 *
          ((2 / π) ^ 2 * (2 * π * freqVec k 1) ^ 2) ^ α 1 *
          ((2 / π) ^ 2 * (2 * π * freqVec k 2) ^ 2) ^ α 2 := by
        rw [mul_pow ((2 / π) ^ 2) ((2 * π * freqVec k 0) ^ 2) (α 0),
          mul_pow ((2 / π) ^ 2) ((2 * π * freqVec k 1) ^ 2) (α 1),
          mul_pow ((2 / π) ^ 2) ((2 * π * freqVec k 2) ^ 2) (α 2)]
        ac_rfl
    _ ≤ _ := mul_le_mul (mul_le_mul (pow_le_pow_left₀ (by positivity) h0 _)
        (pow_le_pow_left₀ (by positivity) h1 _) (by positivity) (by positivity))
        (pow_le_pow_left₀ (by positivity) h2 _) (by positivity) (by positivity)

theorem two_div_pi_sq_le_one : (2 / π) ^ 2 ≤ 1 := by
  have h : 2 / π ≤ 1 := by
    rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
  have h0 : 0 ≤ 2 / π := by positivity
  nlinarith

/-- `lem:supp-open-calculus`, norm equivalence (upper half):
`‖u‖²_{r,h} ≤ ‖𝓘_h u‖²_{H^r}` for every `r` and every `N`. -/
theorem sobSq_le_trigSobSq_interp (r : ℕ) (u : Grid N → ℂ) :
    sobSq r u ≤ trigSobSq r (interp u) := by
  rw [sobSq_eq_weight, trigSobSq_interp]
  refine sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact sum_le_sum fun α _ => norm_dsym_sq_le_tsymSq α k

/-- `lem:supp-open-calculus`, norm equivalence (lower half):
`(2/π)^{2r} ‖𝓘_h u‖²_{H^r} ≤ ‖u‖²_{r,h}` for every `r` and every `N`. -/
theorem trigSobSq_interp_le_sobSq (r : ℕ) (u : Grid N → ℂ) :
    ((2 / π) ^ 2) ^ r * trigSobSq r (interp u) ≤ sobSq r u := by
  rw [sobSq_eq_weight, trigSobSq_interp, mul_sum]
  refine sum_le_sum fun k _ => ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [trigWeight, gridWeight, mul_sum]
  refine sum_le_sum fun α hα => ?_
  have hdeg := mem_multiIndices.mp hα
  have hc0 : 0 ≤ (2 / π) ^ 2 := by positivity
  have hmono : ((2 / π) ^ 2) ^ r ≤ ((2 / π) ^ 2) ^ deg α :=
    pow_le_pow_of_le_one hc0 two_div_pi_sq_le_one hdeg
  have ht : 0 ≤ tsymSq α (freqVec k) := by unfold tsymSq; positivity
  exact (mul_le_mul_of_nonneg_right hmono ht).trans (tsymSq_le_norm_dsym_sq α k)

/-- The coordinate Dirichlet form `Σ_i ‖D_i⁺ u‖_h²`. -/
noncomputable def coordForm (u : Grid N → ℂ) : ℝ := ∑ i, gridNormSq (Dp i u)

theorem coordForm_eq (u : Grid N → ℂ) :
    coordForm u = ∑ k, (∑ i, ‖sym i k‖ ^ 2) * ‖dft u k‖ ^ 2 := by
  unfold coordForm
  simp only [gridNormSq_mult (isMult_Dp _), sum_mul]
  rw [sum_comm]

/-- `Σ_i ‖D_i⁺ u‖_h² ≤ ‖∇ 𝓘_h u‖²_{L²}`. -/
theorem coordForm_le_trigGradSq_interp (u : Grid N → ℂ) :
    coordForm u ≤ trigGradSq (interp u) := by
  rw [coordForm_eq, trigGradSq_interp]
  refine sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact sum_le_sum fun i _ => norm_sym_sq_le_tsym i k

/-- `(2/π)² ‖∇ 𝓘_h u‖²_{L²} ≤ Σ_i ‖D_i⁺ u‖_h²`. -/
theorem trigGradSq_interp_le_coordForm (u : Grid N → ℂ) :
    (2 / π) ^ 2 * trigGradSq (interp u) ≤ coordForm u := by
  rw [coordForm_eq, trigGradSq_interp, mul_sum]
  refine sum_le_sum fun k _ => ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [mul_sum]
  exact sum_le_sum fun i _ => tsym_le_norm_sym_sq i k

end RenewalGeometry.PeriodicGridSobolev
