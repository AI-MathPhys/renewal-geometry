/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.Continuum.LichnerowiczRegularity
import MathPhys.Analysis.GevreyFourierDecay

/-!
# Rapidly decaying Fourier series on `𝕋³` are smooth periodic functions on `ℝ³`

Generic infrastructure (no renewal notions) for `prop:generated-initial`: elliptic regularity
of the conformal factor in Fourier form (`LichnerowiczRegularity`) gives `C^∞` slice data.

* `contDiff_lift`: if `Σ_n (1 + |n|₁)^k |F̂(n)| < ∞` for every `k`, the lift
  `y ↦ F(y mod ℤ³)` is `C^∞` on `ℝ³` (termwise differentiation of the plane waves,
  `contDiff_tsum`);
* `lap_lift`: its classical Laplacian is the Fourier Laplacian `lap F`;
* `lapR_lift_re`: the real version for real-valued `F`;
* `wsum_of_smooth`: conversely, the descent of a smooth periodic function has Fourier
  coefficients in every weighted Wiener algebra (integration by parts,
  `GevreyFourier.norm_mFourierCoeff_mul_pow_le`).
-/

open Finset Filter Topology UnitAddTorus
open scoped BigOperators Real ContDiff

namespace MathPhys.LichReg

open SobolevOpen (pd)
open TorusFourierTruncation TorusSobolevTransfer PeriodicGridSobolev PeriodicGridSobolev.Sampling
  LichnerowiczContraction SobolevBoxCr

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable section

theorem contDiff_pd3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {β : (Fin 3 → ℝ) → E} (hβ : ContDiff ℝ ∞ β) (j : Fin 3) : ContDiff ℝ ∞ (pd β j) := by
  unfold SobolevOpen.pd
  exact (hβ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-! ### Plane waves -/

/-- `t ↦ e^{it}`. -/
def hexp (t : ℝ) : ℂ := Complex.exp (t * Complex.I)

theorem hasDerivAt_hexp (c : ℂ) (t : ℝ) :
    HasDerivAt (fun t => c * hexp t) (c * Complex.I * hexp t) t := by
  have h := (((hasDerivAt_id t).ofReal_comp).mul_const Complex.I).cexp.const_mul c
  refine h.congr_deriv ?_
  simp only [hexp, id]
  push_cast
  ring

theorem iteratedDeriv_hexp (k : ℕ) :
    iteratedDeriv k hexp = fun t => Complex.I ^ k * hexp t := by
  induction k with
  | zero => funext t; simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [(hasDerivAt_hexp (Complex.I ^ k) t).deriv, pow_succ]

theorem contDiff_hexp : ContDiff ℝ ∞ hexp :=
  Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)

theorem norm_iteratedFDeriv_hexp (k : ℕ) (t : ℝ) : ‖iteratedFDeriv ℝ k hexp t‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_hexp]
  simp only [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, hexp]
  rw [Complex.norm_exp_ofReal_mul_I]

/-- The phase `y ↦ 2π n·y`. -/
def phaseL (n : Fin 3 → ℤ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => 2 * π * ∑ i, (n i : ℝ) * y i
      map_add' := fun y z => by simp only [Pi.add_apply, mul_add, sum_add_distrib]
      map_smul' := fun c y => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [mul_sum, mul_sum, mul_sum]
        exact sum_congr rfl fun i _ => by ring }

theorem phaseL_apply (n : Fin 3 → ℤ) (y : Fin 3 → ℝ) :
    phaseL n y = 2 * π * ∑ i, (n i : ℝ) * y i := rfl

theorem norm_phaseL_le (n : Fin 3 → ℤ) : ‖phaseL n‖ ≤ 2 * π * ab n := by
  have h0 : 0 ≤ 2 * π * ab n := by have := ab_nonneg n; positivity
  refine ContinuousLinearMap.opNorm_le_bound (phaseL n) h0 fun y => ?_
  have hb : |∑ i, (n i : ℝ) * y i| ≤ ab n * ‖y‖ := by
    unfold ab
    rw [sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm y i) (abs_nonneg _)
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  calc ‖phaseL n y‖ = 2 * π * |∑ i, (n i : ℝ) * y i| := by
        rw [phaseL_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg h2π]
    _ ≤ 2 * π * (ab n * ‖y‖) := mul_le_mul_of_nonneg_left hb h2π
    _ = 2 * π * ab n * ‖y‖ := by ring

theorem mFourier_torusMk (n : Fin 3 → ℤ) (y : Fin 3 → ℝ) :
    mFourier n (torusMk y) = hexp (phaseL n y) := by
  simp only [mFourier, ContinuousMap.coe_mk, torusMk, fourier_coe_apply, hexp, phaseL_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [mul_sum, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  ring

theorem norm_iteratedFDeriv_wave (c : ℂ) (n : Fin 3 → ℤ) (k : ℕ) (y : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ k (fun y => c * hexp (phaseL n y)) y‖ ≤ ‖c‖ * (2 * π * ab n) ^ k := by
  have hcomp : (fun y => c * hexp (phaseL n y)) = c • (hexp ∘ ⇑(phaseL n)) := by
    funext y; simp [smul_eq_mul]
  rw [hcomp, iteratedFDeriv_const_smul_apply
    ((contDiff_hexp.comp (phaseL n).contDiff).contDiffAt.of_le (by exact_mod_cast le_top)),
    norm_smul, ContinuousLinearMap.iteratedFDeriv_comp_right (phaseL n) contDiff_hexp y
      (by exact_mod_cast le_top)]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_hexp, one_mul, prod_const, card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_phaseL_le n) k

/-! ### Smoothness of the lift -/

theorem ab_le_wt (n : Fin 3 → ℤ) (k : ℕ) : ab n ^ k ≤ wt 1 k n := by
  unfold wt
  rw [div_one]
  exact pow_le_pow_left₀ (ab_nonneg n) (by linarith) k

/-- The lift of `F` as a Fourier series. -/
theorem lift_eq_tsum {F : CT} (hF : Summable fun n => ‖mFourierCoeff ⇑F n‖) (y : Fin 3 → ℝ) :
    F (torusMk y) = ∑' n, mFourierCoeff ⇑F n * hexp (phaseL n y) := by
  have h := hasSum_mFourier_series_apply_of_summable hF.of_norm (torusMk y)
  rw [← h.tsum_eq]
  simp only [smul_eq_mul, mFourier_torusMk]

/-- **A function with Fourier coefficients in every weighted Wiener algebra lifts to a `C^∞`
function on `ℝ³`.** -/
theorem contDiff_lift {F : CT} (hF : ∀ k, WSum 1 k F) :
    ContDiff ℝ ∞ (fun y => F (torusMk y)) := by
  have h0 := (hF 0).summable_norm one_pos
  have e : (fun y => F (torusMk y)) =
      fun y => ∑' n, mFourierCoeff ⇑F n * hexp (phaseL n y) := funext (lift_eq_tsum h0)
  rw [e]
  refine contDiff_tsum (N := ⊤) (v := fun k n => ‖mFourierCoeff ⇑F n‖ * (2 * π * ab n) ^ k)
    (fun n => contDiff_const.mul (contDiff_hexp.comp (phaseL n).contDiff)) (fun k _ => ?_)
    (fun k n y _ => norm_iteratedFDeriv_wave _ n k y)
  refine Summable.of_nonneg_of_le (fun n => by have := ab_nonneg n; positivity) (fun n => ?_)
    ((hF k).mul_left ((2 * π) ^ k))
  rw [mul_pow]
  have h1 := ab_le_wt n k
  have h2 := norm_nonneg (mFourierCoeff ⇑F n)
  have h3 : 0 ≤ (2 * π) ^ k := by positivity
  calc ‖mFourierCoeff ⇑F n‖ * ((2 * π) ^ k * ab n ^ k)
      = (2 * π) ^ k * (ab n ^ k * ‖mFourierCoeff ⇑F n‖) := by ring
    _ ≤ (2 * π) ^ k * (wt 1 k n * ‖mFourierCoeff ⇑F n‖) := by gcongr

theorem isPeriodic_lift (F : CT) : SobolevBoxCr.IsPeriodic (fun y => F (torusMk y)) := by
  intro n y
  show F (torusMk (y + fun i => (n i : ℝ))) = F (torusMk y)
  congr 1
  exact (torusMk_eq_iff.mpr ⟨n, rfl⟩).symm

theorem descendFun_lift (F : CT) : descendFun (fun y => F (torusMk y)) = ⇑F := by
  funext t
  simp only [descendFun]
  rw [torusMk_torusRep]

/-! ### The classical Laplacian of the lift -/

/-- The classical Laplacian `Σᵢ ∂ᵢ∂ᵢ g`. -/
def lapC (g : (Fin 3 → ℝ) → ℂ) (y : Fin 3 → ℝ) : ℂ := ∑ i, pd (pd g i) i y

theorem iterPd_two (g : (Fin 3 → ℝ) → ℂ) (i : Fin 3) :
    iterPd g (fun _ : Fin 2 => i) = pd (pd g i) i := rfl

/-- **The Fourier Laplacian is the classical Laplacian of the lift.** -/
theorem lap_lift {F : CT} (hF : ∀ k, WSum 1 k F) (y : Fin 3 → ℝ) :
    lap F (torusMk y) = lapC (fun y => F (torusMk y)) y := by
  set g : (Fin 3 → ℝ) → ℂ := fun y => F (torusMk y) with hg
  have hgs : ContDiff ℝ ∞ g := contDiff_lift hF
  have hgp : SobolevBoxCr.IsPeriodic g := isPeriodic_lift F
  have hdd : ∀ i, ContDiff ℝ ∞ (pd (pd g i) i) := fun i => contDiff_pd3 (contDiff_pd3 hgs i) i
  have hddp : ∀ i, SobolevBoxCr.IsPeriodic (pd (pd g i) i) := fun i => (hgp.pd i).pd i
  have hLs : ContDiff ℝ ∞ (lapC g) := by
    unfold lapC; exact ContDiff.sum fun i _ => hdd i
  have hLp : SobolevBoxCr.IsPeriodic (lapC g) := by
    intro n x; unfold lapC; exact sum_congr rfl fun i _ => hddp i n x
  set Δ : CT := SobolevBoxCr.descend hLs.continuous hLp with hΔ
  -- the Fourier coefficients of the descended Laplacian
  have hcΔ : ∀ n, mFourierCoeff ⇑Δ n = -((lapSym n : ℝ) : ℂ) * mFourierCoeff ⇑F n := by
    intro n
    have hsplit : Δ = ∑ i, SobolevBoxCr.descend (hdd i).continuous (hddp i) := by
      ext t
      simp only [hΔ, SobolevBoxCr.descend, ContinuousMap.coe_mk, ContinuousMap.coe_sum,
        Finset.sum_apply, descendFun, lapC]
    rw [hsplit, ← coeffL_apply, map_sum]
    have hi : ∀ i, coeffL n (SobolevBoxCr.descend (hdd i).continuous (hddp i)) =
        (2 * π * Complex.I * (n i : ℂ)) ^ 2 * mFourierCoeff ⇑F n := by
      intro i
      rw [coeffL_apply]
      have := mFourierCoeff_descend_iterPd hgs hgp (fun _ : Fin 2 => i) n
      rw [symbol_idx_const, iterPd_two, descendFun_lift] at this
      exact this
    simp only [hi]
    rw [← sum_mul]
    congr 1
    unfold lapSym
    push_cast
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring_nf
    rw [Complex.I_sq]
    ring
  -- the Fourier Laplacian
  have hsum : Summable fun n => ‖-((lapSym n : ℝ) : ℂ) * mFourierCoeff ⇑F n‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((hF 2).mul_left ((2 * π) ^ 2))
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (lapSym_nonneg n)]
    have hl : lapSym n ≤ (2 * π) ^ 2 * wt 1 2 n := by
      unfold lapSym wt
      rw [div_one]
      have h1 : ∑ i, (2 * π * (n i : ℝ)) ^ 2 = (2 * π) ^ 2 * ∑ i, ((n i : ℝ)) ^ 2 := by
        rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
      rw [h1]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h2 : ∑ i, ((n i : ℝ)) ^ 2 ≤ ab n ^ 2 := by
        unfold ab
        rw [Fin.sum_univ_three, Fin.sum_univ_three]
        have a0 := abs_nonneg ((n 0 : ℝ)); have a1 := abs_nonneg ((n 1 : ℝ))
        have a2 := abs_nonneg ((n 2 : ℝ))
        rw [← sq_abs ((n 0 : ℝ)), ← sq_abs ((n 1 : ℝ)), ← sq_abs ((n 2 : ℝ))]
        nlinarith
      have := ab_nonneg n
      nlinarith
    calc lapSym n * ‖mFourierCoeff ⇑F n‖ ≤ ((2 * π) ^ 2 * wt 1 2 n) * ‖mFourierCoeff ⇑F n‖ :=
          mul_le_mul_of_nonneg_right hl (norm_nonneg _)
      _ = (2 * π) ^ 2 * (wt 1 2 n * ‖mFourierCoeff ⇑F n‖) := by ring
  have hlapΔ : lap F = Δ := by
    refine coeff_ext fun n => ?_
    rw [lap, mFourierCoeff_fmul hsum, hcΔ]
  rw [hlapΔ]
  show descendFun (lapC g) (torusMk y) = lapC g y
  exact descendFun_mk hLp y

/-- **Real version**: for real-valued `F`, the classical Laplacian of the real lift is the real
part of the Fourier Laplacian. -/
theorem lapR_lift_re {F : CT} (hF : ∀ k, WSum 1 k F) (hre : ∀ x, (F x).im = 0)
    (y : Fin 3 → ℝ) :
    ∑ i, pd (pd (fun y => (F (torusMk y)).re) i) i y = (lap F (torusMk y)).re := by
  set fR : (Fin 3 → ℝ) → ℝ := fun y => (F (torusMk y)).re with hfR
  have hg : (fun y => F (torusMk y)) = fun y => ((fR y : ℝ) : ℂ) := by
    funext y; apply Complex.ext <;> simp [hfR, hre]
  have hgs := contDiff_lift hF
  have hfs : ContDiff ℝ ∞ fR := Complex.reCLM.contDiff.comp hgs
  rw [lap_lift hF y, hg]
  unfold lapC
  have h1 : ∀ i, pd (fun y => ((fR y : ℝ) : ℂ)) i = fun y => ((pd fR i y : ℝ) : ℂ) := fun i =>
    funext fun y => SobolevOpen.pd_ofReal (hfs.of_le (by norm_cast)) i y
  simp only [h1]
  rw [Complex.re_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [SobolevOpen.pd_ofReal ((contDiff_pd3 hfs i).of_le (by norm_cast)) i y, Complex.ofReal_re]

end

end MathPhys.LichReg
