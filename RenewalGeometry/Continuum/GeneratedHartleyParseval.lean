/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoGalerkinLimit

/-!
# Parseval's identity in the Hartley basis, in `L²` and in `H^q`

Generic infrastructure (no renewal notions) for the readouts of `thm:generated-dynamics`
(Einstein–Standard-Model action-closure manuscript, `eq:generated-bosonic`, `eq:generated-Dirac`):
the rates of `KatoGenDyn.generated_dynamics_rates` are stated in Fourier form (weighted sums of
squared `cas` coefficients over finite mode sets), while the composition estimates
(`KatoSecond.Q_compF_sub_le`) use the classical slice norms `Q q f t`.  This file proves that the
two agree.

* `mFourierCoeff_slice` — the complex Fourier coefficient of a slice through the cosine and sine
  moments; `coef_eq_cos_add_sin`, `coef_neg_eq_cos_sub_sin`.
* **`hasSum_coef_sq`** — `L²` Parseval in the Hartley basis:
  `Σ_k ⟨f(t,·), cas_k⟩² = ∫ |f(t,·)|²` for continuous spatially periodic `f`.
* `coef_pd_succ`, `coef_sd_sq` — coefficients of derivatives:
  `⟨∂_i f, cas_k⟩ = -2πk_i ⟨f, cas_{-k}⟩`, `⟨∂^L f, cas_k⟩² = μ_L(k) ⟨f, cas_{±k}⟩²`.
* **`hasSum_wq_coef_sq`** — `H^q` Parseval: `Σ_k wq q k ⟨f(t,·), cas_k⟩² = Q q f t` for smooth
  spatially periodic `f`.
* **`Q_le_of_sum_le`** — if every finite weighted coefficient sum is at most `B`, then
  `Q q f t ≤ B` (the bridge from the Fourier-form rates to classical slice norms).
-/

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators ContDiff Real

noncomputable section

namespace RenewalGeometry.GenParseval

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg KatoGalerkin

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-! ### Cosine and sine moments -/

/-- The cosine moment of a slice. -/
def cosM (f : ST d → ℝ) (t : ℝ) (n : Fin d → ℤ) : ℝ :=
  ∫ y in Icc (0 : Fin d → ℝ) 1, Real.cos (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y)

/-- The sine moment of a slice. -/
def sinM (f : ST d → ℝ) (t : ℝ) (n : Fin d → ℤ) : ℝ :=
  ∫ y in Icc (0 : Fin d → ℝ) 1, Real.sin (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y)

theorem integrableOn_cos_mul {f : ST d → ℝ} (hf : Continuous f) (t : ℝ) (n : Fin d → ℤ) :
    IntegrableOn (fun y : Fin d → ℝ =>
      Real.cos (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y)) (Icc 0 1) :=
  integrableOn_cube_of_continuousOn (by
    have := hf.comp (continuous_cons (d := d) t)
    fun_prop)

theorem integrableOn_sin_mul {f : ST d → ℝ} (hf : Continuous f) (t : ℝ) (n : Fin d → ℤ) :
    IntegrableOn (fun y : Fin d → ℝ =>
      Real.sin (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y)) (Icc 0 1) :=
  integrableOn_cube_of_continuousOn (by
    have := hf.comp (continuous_cons (d := d) t)
    fun_prop)

theorem neg_phase (n : Fin d → ℤ) (y : Fin d → ℝ) :
    2 * π * ∑ i, ((-n) i : ℝ) * y i = -(2 * π * ∑ i, (n i : ℝ) * y i) := by
  rw [← mul_neg, ← Finset.sum_neg_distrib]; congr 1
  refine Finset.sum_congr rfl fun i _ => ?_; simp

/-- `⟨f, cas_n⟩ = C_n + S_n`. -/
theorem coef_eq_cos_add_sin {f : ST d → ℝ} (hf : Continuous f) (t : ℝ) (n : Fin d → ℤ) :
    coef f t n = cosM f t n + sinM f t n := by
  unfold coef sint cosM sinM
  rw [← integral_add (integrableOn_cos_mul hf t n) (integrableOn_sin_mul hf t n)]
  refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
  simp only
  rw [casS_cons]; unfold cas; ring

/-- `⟨f, cas_{-n}⟩ = C_n - S_n`. -/
theorem coef_neg_eq_cos_sub_sin {f : ST d → ℝ} (hf : Continuous f) (t : ℝ) (n : Fin d → ℤ) :
    coef f t (-n) = cosM f t n - sinM f t n := by
  unfold coef sint cosM sinM
  rw [← integral_sub (integrableOn_cos_mul hf t n) (integrableOn_sin_mul hf t n)]
  refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
  simp only
  rw [casS_cons, neg_phase]; unfold cas; rw [Real.cos_neg, Real.sin_neg]; ring

/-! ### The complex Fourier coefficient of a slice -/

/-- **The complex Fourier coefficient of the descended slice** `y ↦ f(t, y)`:
`ĝ(n) = C_n - i S_n`. -/
theorem mFourierCoeff_slice {f : ST d → ℝ} (hf : Continuous f) (hp : IsSPeriodic f) (t : ℝ)
    (n : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (SobolevBoxCr.descendFun
        (fun y : Fin d → ℝ => (f (Fin.cons t y) : ℂ))) n =
      (cosM f t n : ℂ) - (sinM f t n : ℂ) * Complex.I := by
  set g : (Fin d → ℝ) → ℂ := fun y => (f (Fin.cons t y) : ℂ) with hg
  have hgp : SobolevBoxCr.IsPeriodic g := fun m x => by
    simp only [hg]
    congr 1
    exact hp.slice t m x
  unfold UnitAddTorus.mFourierCoeff
  rw [SobolevOpen.integral_torus_eq_unitCube]
  have e : ∀ y : Fin d → ℝ, UnitAddTorus.mFourier (-n) (fun i => (y i : UnitAddCircle)) •
      SobolevBoxCr.descendFun g (fun i => (y i : UnitAddCircle)) =
      ((Real.cos (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y) : ℝ) : ℂ) -
        ((Real.sin (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y) : ℝ) : ℂ) *
          Complex.I := by
    intro y
    have h1 := SobolevBoxCr.descendFun_mk hgp y
    have h2 := mFourier_torusMk (-n) y
    rw [show (fun i => (y i : UnitAddCircle)) = SobolevBoxCr.torusMk y from rfl, h1, h2,
      smul_eq_mul]
    rw [neg_phase, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  simp_rw [e]
  rw [setIntegral_congr_set KatoGalerkin.unitCube_ae_eq_Icc]
  have i1 : IntegrableOn (fun y : Fin d → ℝ =>
      ((Real.cos (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y) : ℝ) : ℂ)) (Icc 0 1) :=
    (integrableOn_cos_mul hf t n).ofReal
  have i2 : IntegrableOn (fun y : Fin d → ℝ =>
      ((Real.sin (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y) : ℝ) : ℂ) * Complex.I)
      (Icc 0 1) :=
    (integrableOn_sin_mul hf t n).ofReal.mul_const _
  rw [integral_sub i1 i2, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]
  rfl

theorem norm_mFourierCoeff_slice_sq {f : ST d → ℝ} (hf : Continuous f) (hp : IsSPeriodic f)
    (t : ℝ) (n : Fin d → ℤ) :
    ‖UnitAddTorus.mFourierCoeff (SobolevBoxCr.descendFun
        (fun y : Fin d → ℝ => (f (Fin.cons t y) : ℂ))) n‖ ^ 2 =
      cosM f t n ^ 2 + sinM f t n ^ 2 := by
  rw [mFourierCoeff_slice hf hp t n, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

/-! ### `L²` Parseval in the Hartley basis -/

/-- **Parseval's identity in the Hartley basis**: for a continuous spatially periodic field,
`Σ_k ⟨f(t,·), cas_k⟩² = ∫_{[0,1]^d} f(t,·)²`. -/
theorem hasSum_coef_sq {f : ST d → ℝ} (hf : Continuous f) (hp : IsSPeriodic f) (t : ℝ) :
    HasSum (fun k => coef f t k ^ 2) (sint (fun x => f x ^ 2) t) := by
  set g : (Fin d → ℝ) → ℂ := fun y => (f (Fin.cons t y) : ℂ) with hg
  have hgc : Continuous g := Complex.continuous_ofReal.comp (hf.comp (continuous_cons t))
  have hgp : SobolevBoxCr.IsPeriodic g := fun m x => by
    simp only [hg]
    congr 1
    exact hp.slice t m x
  have hsum := SobolevBoxCr.hasSum_sq_descend hgc hgp
  have hI : ∫ y in SobolevOpen.unitCube, ‖g y‖ ^ 2 = sint (fun x => f x ^ 2) t := by
    rw [setIntegral_congr_set KatoGalerkin.unitCube_ae_eq_Icc]
    unfold sint
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    simp [hg, Complex.norm_real, sq_abs]
  rw [hI] at hsum
  replace hsum : HasSum (fun n => cosM f t n ^ 2 + sinM f t n ^ 2)
      (sint (fun x => f x ^ 2) t) :=
    hsum.congr_fun fun n => (norm_mFourierCoeff_slice_sq hf hp t n).symm
  set a : (Fin d → ℤ) → ℝ := fun k => coef f t k ^ 2 with ha
  have hpair : ∀ k, a k + a (-k) = 2 * (cosM f t k ^ 2 + sinM f t k ^ 2) := fun k => by
    simp only [ha]
    rw [coef_neg_eq_cos_sub_sin hf, coef_eq_cos_add_sin hf]; ring
  have h2 : HasSum (fun k => a k + a (-k)) (2 * sint (fun x => f x ^ 2) t) := by
    simp_rw [hpair]; exact hsum.mul_left 2
  have ha0 : ∀ k, 0 ≤ a k := fun k => sq_nonneg _
  have hsa : Summable a :=
    Summable.of_nonneg_of_le ha0 (fun k => le_add_of_nonneg_right (ha0 (-k))) h2.summable
  have hsn : HasSum (fun k => a (-k)) (∑' k, a k) :=
    (Equiv.neg (Fin d → ℤ)).hasSum_iff.2 hsa.hasSum
  have h3 := hsa.hasSum.add hsn
  have h4 := h3.unique h2
  have h5 : ∑' k, a k = sint (fun x => f x ^ 2) t := by linarith
  rw [← h5]; exact hsa.hasSum

/-! ### Coefficients of derivatives -/

/-- `⟨∂_i f, cas_k⟩ = -2πk_i ⟨f, cas_{-k}⟩`. -/
theorem coef_pd_succ {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hp : IsSPeriodic f) (i : Fin d)
    (t : ℝ) (k : Fin d → ℤ) :
    coef (pd f i.succ) t k = -(2 * π * (k i : ℝ)) * coef f t (-k) := by
  unfold coef
  rw [sint_mul_pd (contDiff_casS k) hf (isSPeriodic_casS k) hp i t, pd_casS_succ]
  unfold sint
  rw [← integral_neg, ← integral_const_mul]
  congr 1; funext y; ring

/-- `⟨∂^L f, cas_k⟩² = μ_L(k) ⟨f, cas_{(-1)^{|L|}k}⟩²`. -/
theorem coef_sd_sq : ∀ (L : List (Fin d)) {f : ST d → ℝ}, ContDiff ℝ ∞ f → IsSPeriodic f →
    ∀ (t : ℝ) (k : Fin d → ℤ),
      coef (sd L f) t k ^ 2 = muL L k * coef f t ((-1 : ℤ) ^ L.length • k) ^ 2
  | [], f, _, _, t, k => by simp [muL_nil]
  | i :: L, f, hf, hp, t, k => by
    rw [sd_cons, coef_sd_sq L (contDiff_pd_top hf i.succ) (isSPeriodic_pd hp i.succ) t k,
      coef_pd_succ hf hp i t, muL_cons]
    have e : -((-1 : ℤ) ^ L.length • k) = (-1 : ℤ) ^ (i :: L).length • k := by
      rw [List.length_cons, pow_succ, mul_comm, mul_smul, neg_one_smul]
    have e2 : (((-1 : ℤ) ^ L.length • k) i : ℝ) ^ 2 = (k i : ℝ) ^ 2 := by
      rcases neg_one_pow_eq_or ℤ L.length with h | h <;> simp [h]
    rw [e, mul_pow, neg_sq, mul_pow, e2]
    ring

/-! ### `H^q` Parseval -/

theorem hasSum_reindex_sign (a : (Fin d → ℤ) → ℝ) (j : ℕ) {s : ℝ} (h : HasSum a s) :
    HasSum (fun k => a ((-1 : ℤ) ^ j • k)) s := by
  rcases neg_one_pow_eq_or ℤ j with hj | hj
  · simpa [hj] using h
  · simp only [hj, neg_smul, one_smul]
    exact (Equiv.neg (Fin d → ℤ)).hasSum_iff.2 h

/-- **Parseval's identity in `H^q`** (Hartley basis): for a smooth spatially periodic field,
`Σ_k wq q k ⟨f(t,·), cas_k⟩² = Q q f t`. -/
theorem hasSum_wq_coef_sq (q : ℕ) {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hp : IsSPeriodic f)
    (t : ℝ) : HasSum (fun k => wq q k * coef f t k ^ 2) (Q q f t) := by
  have hL : ∀ L ∈ wordsLE d q, HasSum (fun k => muL L k * coef f t k ^ 2)
      (∫ y in Icc (0 : Fin d → ℝ) 1, sd L f (Fin.cons t y) ^ 2) := by
    intro L _
    have h1 := hasSum_coef_sq (contDiff_sd L hf).continuous (isSPeriodic_sd L hp) t
    have hI : sint (fun x => sd L f x ^ 2) t =
        ∫ y in Icc (0 : Fin d → ℝ) 1, sd L f (Fin.cons t y) ^ 2 := rfl
    rw [hI] at h1
    have h1' : HasSum (fun k => muL L k * coef f t ((-1 : ℤ) ^ L.length • k) ^ 2)
        (∫ y in Icc (0 : Fin d → ℝ) 1, sd L f (Fin.cons t y) ^ 2) := by
      refine h1.congr_fun ?_
      intro k
      exact (coef_sd_sq L hf hp t k).symm
    have h2 := hasSum_reindex_sign _ L.length h1'
    refine h2.congr_fun ?_
    intro k
    have e : (-1 : ℤ) ^ L.length • (-1 : ℤ) ^ L.length • k = k := by
      rw [smul_smul, ← mul_pow]; simp
    have e2 : muL L ((-1 : ℤ) ^ L.length • k) = muL L k := by
      rcases neg_one_pow_eq_or ℤ L.length with h | h
      · rw [h, one_smul]
      · rw [h, neg_smul, one_smul, muL_neg]
    show muL L k * coef f t k ^ 2 = muL L ((-1 : ℤ) ^ L.length • k) *
      coef f t ((-1 : ℤ) ^ L.length • (-1 : ℤ) ^ L.length • k) ^ 2
    rw [e, e2]
  have hs := hasSum_sum (f := fun L k => muL L k * coef f t k ^ 2) hL
  unfold Q
  convert hs using 1
  funext k
  rw [wq, Finset.sum_mul]

/-- **From Fourier-form bounds to slice norms**: if every finite weighted coefficient sum of a
smooth spatially periodic field is at most `B`, then `Q q f t ≤ B`. -/
theorem Q_le_of_sum_le (q : ℕ) {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hp : IsSPeriodic f)
    {t B : ℝ} (h : ∀ S : Finset (Fin d → ℤ), ∑ k ∈ S, wq q k * coef f t k ^ 2 ≤ B) :
    Q q f t ≤ B := by
  have hs := hasSum_wq_coef_sq q hf hp t
  rw [← hs.tsum_eq]
  exact hs.summable.tsum_le_of_sum_le h

end RenewalGeometry.GenParseval
