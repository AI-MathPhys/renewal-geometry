/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallSobolevDeriv
import RenewalGeometry.Analysis.BallSobolevMulGen
import RenewalGeometry.Analysis.BallSobolevContinuous
import RenewalGeometry.Analysis.BallLinearizedCoulombHk

/-!
# Weak product rule and weakly tangential fields on balls
  (stage D1c of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `hasWeakPartialR_mul` — **the product rule for weak derivatives** of `H¹(B)` functions:
  `∂_i(u v) = (∂_i u) v + u ∂_i v` (weakly, as `L¹` functions), by smooth approximation;
* `IsWeakTangential a d` — the weak form of "`a·ν = 0` on the sphere, `div a = d`":
  `Σ_ν ∫_B a_ν ∂_νφ = -∫_B d φ` for every `C¹` function `φ` (no boundary condition on `φ`);
* `IsWeakTangential.mul` — **tangential fields form a module**: if `a` is weakly tangential with
  `a_ν ∈ H³(B)` and `div a ∈ L^∞`, and `ξ ∈ H¹(B)`, then `ξ a` is weakly tangential with
  divergence `Σ_ν ∂_ν(a_ν ξ)`;
* `IsWeakTangential.inner_H1B` — the integration by parts extends to all test fields of `H¹(B)`
  (closure of the `C¹` graphs).
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg

set_option linter.unusedSectionVars false

section Weak

variable (c : Fin 4 → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- Integrals against a bounded weight are `L¹`-continuous. -/
theorem abs_setIntegral_mul_sub_le {h F G : (Fin 4 → ℝ) → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hh : AEStronglyMeasurable h (volume.restrict (euclBall c r)))
    (hM : ∀ᵐ x ∂(volume.restrict (euclBall c r)), |h x| ≤ M)
    (hF : Integrable F (volume.restrict (euclBall c r)))
    (hG : Integrable G (volume.restrict (euclBall c r))) :
    |(∫ x in euclBall c r, h x * F x) - ∫ x in euclBall c r, h x * G x| ≤
      M * (eLpNorm (F - G) 1 (volume.restrict (euclBall c r))).toReal := by
  have hhF : Integrable (fun x => h x * F x) (volume.restrict (euclBall c r)) :=
    hF.bdd_mul hh hM
  have hhG : Integrable (fun x => h x * G x) (volume.restrict (euclBall c r)) :=
    hG.bdd_mul hh hM
  rw [← integral_sub hhF hhG]
  refine (abs_integral_le_integral_abs).trans ?_
  have hpt : ∀ᵐ x ∂(volume.restrict (euclBall c r)), |h x * F x - h x * G x| ≤ M * |(F - G) x| := by
    filter_upwards [hM] with x hx
    rw [← mul_sub, abs_mul, Pi.sub_apply]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  refine (integral_mono_ae (hhF.sub hhG).abs ((hF.sub hG).abs.const_mul M) hpt).trans ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hM0
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hF.sub hG),
    ENNReal.toReal_ofReal (integral_nonneg fun x => norm_nonneg _)]
  rfl

/-- Integrals against a bounded weight pass to `L¹` limits. -/
theorem tendsto_setIntegral_mul {h : (Fin 4 → ℝ) → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    {F : ℕ → (Fin 4 → ℝ) → ℝ} {F0 : (Fin 4 → ℝ) → ℝ}
    (hh : AEStronglyMeasurable h (volume.restrict (euclBall c r)))
    (hM : ∀ᵐ x ∂(volume.restrict (euclBall c r)), |h x| ≤ M)
    (hFi : ∀ m, Integrable (F m) (volume.restrict (euclBall c r)))
    (hF0 : Integrable F0 (volume.restrict (euclBall c r)))
    (hlim : Tendsto (fun m => eLpNorm (F m - F0) 1 (volume.restrict (euclBall c r))) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x in euclBall c r, h x * F m x) atTop
      (𝓝 (∫ x in euclBall c r, h x * F0 x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim' : Tendsto (fun m => M * (eLpNorm (F m - F0) 1 (volume.restrict (euclBall c r))).toReal)
      atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    simpa using this.const_mul M
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) hlim'
  rw [Real.norm_eq_abs]
  exact abs_setIntegral_mul_sub_le c r hM0 hh hM (hFi m) hF0

/-- `L²(B)` functions are integrable on the ball. -/
theorem integrable_of_memLp_two {f : (Fin 4 → ℝ) → ℝ}
    (hf : MemLp f 2 (volume.restrict (euclBall c r))) :
    Integrable f (volume.restrict (euclBall c r)) := by
  have := isFiniteMeasure_restrict_euclBall c hr.out.le
  exact hf.integrable (by norm_num)

theorem integrable_mul_of_memLp_two {f g : (Fin 4 → ℝ) → ℝ}
    (hf : MemLp f 2 (volume.restrict (euclBall c r)))
    (hg : MemLp g 2 (volume.restrict (euclBall c r))) :
    Integrable (fun x => f x * g x) (volume.restrict (euclBall c r)) := by
  exact hf.integrable_mul hg

/-- **The product rule for weak derivatives in `H¹(B)`**: `∂_i(u v) = (∂_i u) v + u ∂_i v`. -/
theorem hasWeakPartialR_mul {i : Fin 4} {u v gu gv : (Fin 4 → ℝ) → ℝ}
    (hu : MemHk (euclBall c r) 1 u) (hv : MemHk (euclBall c r) 1 v)
    (hgu : MemLp gu 2 (volume.restrict (euclBall c r)))
    (hgv : MemLp gv 2 (volume.restrict (euclBall c r)))
    (hdu : HasWeakPartialR (euclBall c r) i u gu) (hdv : HasWeakPartialR (euclBall c r) i v gv) :
    HasWeakPartialR (euclBall c r) i (fun x => u x * v x) (fun x => gu x * v x + u x * gv x) := by
  have hfin := isFiniteMeasure_restrict_euclBall c hr.out.le
  set μB := volume.restrict (euclBall c r)
  have hBo := isOpen_euclBall c r
  obtain ⟨φ, hφ, hcu⟩ := (memHk_iff_exists_convHk c r 1).mp hu
  obtain ⟨ψ, hψ, hcv⟩ := (memHk_iff_exists_convHk c r 1).mp hv
  -- the derivative limits are the given weak derivatives
  obtain ⟨gu', hgu'⟩ := hcu.2 i
  obtain ⟨gv', hgv'⟩ := hcv.2 i
  have hwu' := hasWeakPartialR_of_conv (isBounded_euclBall' c r) (measurableSet_euclBall c r) hφ
    hcu.1.1 hgu'.1 hcu.1.2 hgu'.2
  have hwv' := hasWeakPartialR_of_conv (isBounded_euclBall' c r) (measurableSet_euclBall c r) hψ
    hcv.1.1 hgv'.1 hcv.1.2 hgv'.2
  have eu : gu' =ᵐ[μB] gu := by
    have := weakR_ae_eq hBo hwu' hdu hgu'.1 hgu
    rw [EventuallyEq, ae_restrict_iff' (measurableSet_euclBall c r)]; exact this
  have ev : gv' =ᵐ[μB] gv := by
    have := weakR_ae_eq hBo hwv' hdv hgv'.1 hgv
    rw [EventuallyEq, ae_restrict_iff' (measurableSet_euclBall c r)]; exact this
  have hdφ : Tendsto (fun m => eLpNorm (pd (φ m) i - gu) 2 μB) atTop (𝓝 0) :=
    hgu'.2.congr fun m => eLpNorm_congr_ae (EventuallyEq.rfl.sub eu)
  have hdψ : Tendsto (fun m => eLpNorm (pd (ψ m) i - gv) 2 μB) atTop (𝓝 0) :=
    hgv'.2.congr fun m => eLpNorm_congr_ae (EventuallyEq.rfl.sub ev)
  have hφm : ∀ m, AEStronglyMeasurable (φ m) μB := fun m => (hφ m).continuous.aestronglyMeasurable
  have hψm : ∀ m, AEStronglyMeasurable (ψ m) μB := fun m => (hψ m).continuous.aestronglyMeasurable
  have hdφm : ∀ m, AEStronglyMeasurable (pd (φ m) i) μB := fun m =>
    (contDiff_pd (hφ m) i).continuous.aestronglyMeasurable
  have hdψm : ∀ m, AEStronglyMeasurable (pd (ψ m) i) μB := fun m =>
    (contDiff_pd (hψ m) i).continuous.aestronglyMeasurable
  -- `L¹` convergence of the products
  have hP := tendsto_eLpNorm_one_mul hφm hψm hu.memLp hv.memLp hcu.1.2 hcv.1.2
  have hQ1 := tendsto_eLpNorm_one_mul hdφm hψm hgu hv.memLp hdφ hcv.1.2
  have hQ2 := tendsto_eLpNorm_one_mul hφm hdψm hu.memLp hgv hcu.1.2 hdψ
  intro χ hχ
  rw [integral_test_eq_setIntegral c r (isTest_pd hχ i), integral_test_eq_setIntegral c r hχ]
  -- the identity for the smooth approximants
  have hsm : ∀ m, ∫ x in euclBall c r, pd χ i x * (φ m x * ψ m x) =
      -∫ x in euclBall c r, χ x * (pd (φ m) i x * ψ m x + φ m x * pd (ψ m) i x) := by
    intro m
    have h1 := hasWeakPartialR_of_contDiff (euclBall c r)
      (((hφ m).mul (hψ m)).of_le (by simp) : ContDiff ℝ 1 fun x => φ m x * ψ m x) i χ hχ
    rw [integral_test_eq_setIntegral c r (isTest_pd hχ i),
      integral_test_eq_setIntegral c r hχ] at h1
    rw [h1]
    congr 1
    refine setIntegral_congr_fun (measurableSet_euclBall c r) fun x _ => ?_
    rw [pd_mul_real (((hφ m).differentiable (by simp)) x) (((hψ m).differentiable (by simp)) x) i]
  -- bounds on the test functions
  obtain ⟨M1, hM10, hM1⟩ := exists_abs_bound_of_test (isTest_pd hχ i)
  obtain ⟨M0, hM00, hM0⟩ := exists_abs_bound_of_test hχ
  have hint : ∀ {f g : (Fin 4 → ℝ) → ℝ}, MemLp f 2 μB → MemLp g 2 μB →
      Integrable (fun x => f x * g x) μB := fun hf hg => integrable_mul_of_memLp_two c r hf hg
  have hL : Tendsto (fun m => ∫ x in euclBall c r, pd χ i x * (φ m x * ψ m x)) atTop
      (𝓝 (∫ x in euclBall c r, pd χ i x * (u x * v x))) :=
    tendsto_setIntegral_mul c r hM10 (contDiff_pd hχ.smooth i).continuous.aestronglyMeasurable
      (Eventually.of_forall hM1)
      (fun m => hint (memLp_euclBall_of_continuous c hr.out.le (hφ m).continuous 2)
        (memLp_euclBall_of_continuous c hr.out.le (hψ m).continuous 2))
      (hint hu.memLp hv.memLp) (by simpa [Pi.sub_def] using hP)
  have hR : Tendsto (fun m => ∫ x in euclBall c r,
      χ x * (pd (φ m) i x * ψ m x + φ m x * pd (ψ m) i x)) atTop
      (𝓝 (∫ x in euclBall c r, χ x * (gu x * v x + u x * gv x))) := by
    refine tendsto_setIntegral_mul c r hM00 hχ.continuous.aestronglyMeasurable
      (Eventually.of_forall hM0) (fun m => (hint (memLp_euclBall_of_continuous c hr.out.le
        (contDiff_pd (hφ m) i).continuous 2) (memLp_euclBall_of_continuous c hr.out.le
          (hψ m).continuous 2)).add (hint (memLp_euclBall_of_continuous c hr.out.le
            (hφ m).continuous 2) (memLp_euclBall_of_continuous c hr.out.le
              (contDiff_pd (hψ m) i).continuous 2)))
      ((hint hgu hv.memLp).add (hint hu.memLp hgv)) ?_
    have hsum := hQ1.add hQ2
    rw [zero_add] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
      fun m => ?_
    have e : ((fun x => pd (φ m) i x * ψ m x + φ m x * pd (ψ m) i x) -
        fun x => gu x * v x + u x * gv x) =
        (fun x => pd (φ m) i x * ψ m x - gu x * v x) + (fun x => φ m x * pd (ψ m) i x - u x * gv x) := by
      funext x; simp only [Pi.sub_apply, Pi.add_apply]; ring
    rw [e]
    exact eLpNorm_add_le (((hdφm m).mul (hψm m)).sub (hgu.aestronglyMeasurable.mul
      hv.memLp.aestronglyMeasurable)) (((hφm m).mul (hdψm m)).sub
        (hu.memLp.aestronglyMeasurable.mul hgv.aestronglyMeasurable)) le_rfl
  have := tendsto_nhds_unique hL ((hR.neg).congr fun m => (hsm m).symm)
  exact this

/-- `L²(B)` convergence implies `L¹(B)` convergence. -/
theorem tendsto_eLpNorm_one_of_two {F : ℕ → (Fin 4 → ℝ) → ℝ} {F0 : (Fin 4 → ℝ) → ℝ}
    (hFm : ∀ m, AEStronglyMeasurable (F m) (volume.restrict (euclBall c r)))
    (hF0 : AEStronglyMeasurable F0 (volume.restrict (euclBall c r)))
    (h : Tendsto (fun m => eLpNorm (F m - F0) 2 (volume.restrict (euclBall c r))) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (F m - F0) 1 (volume.restrict (euclBall c r))) atTop (𝓝 0) := by
  have hfin := isFiniteMeasure_restrict_euclBall c hr.out.le
  set V : ℝ≥0∞ := (volume.restrict (euclBall c r)) Set.univ ^
    (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
  have hVt : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  have := ENNReal.Tendsto.mul_const h (Or.inr hVt)
  rw [zero_mul] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => bot_le)
    fun m => eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) ((hFm m).sub hF0)

/-- A `C¹` function and its partial derivatives are bounded on the ball. -/
theorem exists_bound_C1_ball {φ : (Fin 4 → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ x ∈ euclBall c r, |φ x| ≤ M) ∧
      ∀ ν, ∀ x ∈ euclBall c r, |pd φ ν x| ≤ M := by
  have hK := isCompact_closedBall c |r|
  obtain ⟨M0, hM0⟩ := hK.exists_bound_of_continuousOn hφ.continuous.continuousOn
  have hd : ∀ ν, ∃ M, ∀ x ∈ closedBall c |r|, ‖pd φ ν x‖ ≤ M := fun ν =>
    hK.exists_bound_of_continuousOn (continuous_pd hφ ν).continuousOn
  choose M hM using hd
  refine ⟨|M0| + ∑ ν, |M ν|, by positivity, fun x hx => ?_, fun ν x hx => ?_⟩
  · have hxc : x ∈ closedBall c |r| :=
      mem_closedBall_of_sqDist_le (abs_nonneg r) (by rw [sq_abs]; exact le_of_lt hx)
    have := hM0 x hxc
    rw [Real.norm_eq_abs] at this
    have h2 : 0 ≤ ∑ ν, |M ν| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith [le_abs_self M0]
  · have hxc : x ∈ closedBall c |r| :=
      mem_closedBall_of_sqDist_le (abs_nonneg r) (by rw [sq_abs]; exact le_of_lt hx)
    have := hM ν x hxc
    rw [Real.norm_eq_abs] at this
    have h2 : |M ν| ≤ ∑ ν, |M ν| :=
      Finset.single_le_sum (f := fun ν => |M ν|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ν)
    linarith [le_abs_self (M ν), abs_nonneg M0]

end Weak

/-! ### Weakly tangential fields -/

section Tangential

variable (c : Fin 4 → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- **`a` is weakly tangential with divergence `d`** on the ball: `Σ_ν ∫_B a_ν ∂_νφ = -∫_B d φ`
for every `C¹` function `φ` (the weak form of `div a = d` in `B`, `a·ν = 0` on `∂B`). -/
def IsWeakTangential (a : Fin 4 → (Fin 4 → ℝ) → ℝ) (d : (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ φ : (Fin 4 → ℝ) → ℝ, ContDiff ℝ 1 φ →
    ∑ ν, ∫ x in euclBall c r, a ν x * pd φ ν x = -∫ x in euclBall c r, d x * φ x

/-- **Weakly tangential fields form a module over `H¹(B)`**: if `a` (bounded, with bounded
divergence `d`) is weakly tangential and `ξ ∈ H¹(B)` has weak gradient `g`, then `ξ a` is weakly
tangential with divergence `d ξ + Σ_ν a_ν g_ν`. -/
theorem IsWeakTangential.mul {a : Fin 4 → (Fin 4 → ℝ) → ℝ} {d : (Fin 4 → ℝ) → ℝ} {M : ℝ}
    (htan : IsWeakTangential c r a d) (hM : 0 ≤ M)
    (ham : ∀ ν, AEStronglyMeasurable (a ν) (volume.restrict (euclBall c r)))
    (hdm : AEStronglyMeasurable d (volume.restrict (euclBall c r)))
    (ha : ∀ ν, ∀ᵐ x ∂(volume.restrict (euclBall c r)), |a ν x| ≤ M)
    (hd : ∀ᵐ x ∂(volume.restrict (euclBall c r)), |d x| ≤ M)
    {ξ : (Fin 4 → ℝ) → ℝ} {g : Fin 4 → (Fin 4 → ℝ) → ℝ}
    (hξ : MemLp ξ 2 (volume.restrict (euclBall c r)))
    (hg : ∀ ν, MemLp (g ν) 2 (volume.restrict (euclBall c r)))
    (hξg : ∀ ν, HasWeakPartialR (euclBall c r) ν ξ (g ν)) :
    IsWeakTangential c r (fun ν x => a ν x * ξ x) (fun x => d x * ξ x + ∑ ν, a ν x * g ν x) := by
  intro φ hφ
  have hfin := isFiniteMeasure_restrict_euclBall c hr.out.le
  set μB := volume.restrict (euclBall c r)
  have hBm := measurableSet_euclBall c r
  have hξ1 : MemHk (euclBall c r) 1 ξ := ⟨hξ, fun ν => ⟨g ν, hξg ν, hg ν⟩⟩
  obtain ⟨ψ, hψ, hcv⟩ := (memHk_iff_exists_convHk c r 1).mp hξ1
  have hdψ : ∀ ν, Tendsto (fun m => eLpNorm (pd (ψ m) ν - g ν) 2 μB) atTop (𝓝 0) := by
    intro ν
    obtain ⟨g', hg'⟩ := hcv.2 ν
    have hw' := hasWeakPartialR_of_conv (isBounded_euclBall' c r) hBm hψ hcv.1.1 hg'.1 hcv.1.2 hg'.2
    have e : g' =ᵐ[μB] g ν := by
      have := weakR_ae_eq (isOpen_euclBall c r) hw' (hξg ν) hg'.1 (hg ν)
      rw [EventuallyEq, ae_restrict_iff' hBm]; exact this
    exact hg'.2.congr fun m => eLpNorm_congr_ae (EventuallyEq.rfl.sub e)
  have hψm : ∀ m, AEStronglyMeasurable (ψ m) μB := fun m => (hψ m).continuous.aestronglyMeasurable
  have hdψm : ∀ m ν, AEStronglyMeasurable (pd (ψ m) ν) μB := fun m ν =>
    (contDiff_pd (hψ m) ν).continuous.aestronglyMeasurable
  have hL1ψ := tendsto_eLpNorm_one_of_two c r hψm hξ.aestronglyMeasurable hcv.1.2
  have hL1dψ : ∀ ν, Tendsto (fun m => eLpNorm (pd (ψ m) ν - g ν) 1 μB) atTop (𝓝 0) := fun ν =>
    tendsto_eLpNorm_one_of_two c r (fun m => hdψm m ν) (hg ν).aestronglyMeasurable (hdψ ν)
  obtain ⟨K, hK0, hK, hKd⟩ := exists_bound_C1_ball c r hφ
  have hφae : ∀ᵐ x ∂μB, |φ x| ≤ K := by
    filter_upwards [ae_restrict_mem hBm] with x hx; exact hK x hx
  have hdφae : ∀ ν, ∀ᵐ x ∂μB, |pd φ ν x| ≤ K := fun ν => by
    filter_upwards [ae_restrict_mem hBm] with x hx; exact hKd ν x hx
  have hφm : AEStronglyMeasurable φ μB := hφ.continuous.aestronglyMeasurable
  have hdφm : ∀ ν, AEStronglyMeasurable (pd φ ν) μB := fun ν =>
    (continuous_pd hφ ν).aestronglyMeasurable
  have hint2 : ∀ {f : (Fin 4 → ℝ) → ℝ}, MemLp f 2 μB → Integrable f μB := fun hf =>
    integrable_of_memLp_two c r hf
  have hψL : ∀ m, MemLp (ψ m) 2 μB := fun m =>
    memLp_euclBall_of_continuous c hr.out.le (hψ m).continuous 2
  have hdψL : ∀ m ν, MemLp (pd (ψ m) ν) 2 μB := fun m ν =>
    memLp_euclBall_of_continuous c hr.out.le (contDiff_pd (hψ m) ν).continuous 2
  -- bounded weights
  have hMK : 0 ≤ M * K := mul_nonneg hM hK0
  have hw1 : ∀ ν, ∀ᵐ x ∂μB, |a ν x * pd φ ν x| ≤ M * K := fun ν => by
    filter_upwards [ha ν, hdφae ν] with x h1 h2
    rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) hM
  have hw2 : ∀ᵐ x ∂μB, |d x * φ x| ≤ M * K := by
    filter_upwards [hd, hφae] with x h1 h2
    rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) hM
  have hw3 : ∀ ν, ∀ᵐ x ∂μB, |a ν x * φ x| ≤ M * K := fun ν => by
    filter_upwards [ha ν, hφae] with x h1 h2
    rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) hM
  have hw1m : ∀ ν, AEStronglyMeasurable (fun x => a ν x * pd φ ν x) μB := fun ν =>
    (ham ν).mul (hdφm ν)
  have hw2m : AEStronglyMeasurable (fun x => d x * φ x) μB := hdm.mul hφm
  have hw3m : ∀ ν, AEStronglyMeasurable (fun x => a ν x * φ x) μB := fun ν => (ham ν).mul hφm
  have hib : ∀ {w f : (Fin 4 → ℝ) → ℝ}, AEStronglyMeasurable w μB → (∀ᵐ x ∂μB, |w x| ≤ M * K) →
      MemLp f 2 μB → Integrable (fun x => w x * f x) μB := fun hwm hw hf =>
    (hint2 hf).bdd_mul hwm hw
  -- the identity for the approximants
  have hsm : ∀ m, ∑ ν, ((∫ x in euclBall c r, (a ν x * φ x) * pd (ψ m) ν x) +
      ∫ x in euclBall c r, (a ν x * pd φ ν x) * ψ m x) =
        -∫ x in euclBall c r, (d x * φ x) * ψ m x := by
    intro m
    have h1 := htan (fun x => ψ m x * φ x) (((hψ m).of_le (by simp)).mul hφ)
    have epd : ∀ ν x, pd (fun x => ψ m x * φ x) ν x = pd (ψ m) ν x * φ x + ψ m x * pd φ ν x :=
      fun ν x => pd_mul_real (((hψ m).differentiable (by simp)) x)
        ((hφ.differentiable one_ne_zero) x) ν
    simp only [epd] at h1
    have e1 : ∀ ν, ∫ x in euclBall c r, a ν x * (pd (ψ m) ν x * φ x + ψ m x * pd φ ν x) =
        (∫ x in euclBall c r, (a ν x * φ x) * pd (ψ m) ν x) +
          ∫ x in euclBall c r, (a ν x * pd φ ν x) * ψ m x := by
      intro ν
      rw [← integral_add (hib (hw3m ν) (hw3 ν) (hdψL m ν)) (hib (hw1m ν) (hw1 ν) (hψL m))]
      congr 1; funext x; ring
    have e2 : ∫ x in euclBall c r, d x * (ψ m x * φ x) =
        ∫ x in euclBall c r, (d x * φ x) * ψ m x := by
      congr 1; funext x; ring
    rw [← e2, ← h1]
    exact Finset.sum_congr rfl fun ν _ => (e1 ν).symm
  -- pass to the limit
  have hT3 : ∀ ν, Tendsto (fun m => ∫ x in euclBall c r, (a ν x * φ x) * pd (ψ m) ν x) atTop
      (𝓝 (∫ x in euclBall c r, (a ν x * φ x) * g ν x)) := fun ν =>
    tendsto_setIntegral_mul c r hMK (hw3m ν) (hw3 ν) (fun m => hint2 (hdψL m ν))
      (hint2 (hg ν)) (hL1dψ ν)
  have hT1 : ∀ ν, Tendsto (fun m => ∫ x in euclBall c r, (a ν x * pd φ ν x) * ψ m x) atTop
      (𝓝 (∫ x in euclBall c r, (a ν x * pd φ ν x) * ξ x)) := fun ν =>
    tendsto_setIntegral_mul c r hMK (hw1m ν) (hw1 ν) (fun m => hint2 (hψL m)) (hint2 hξ) hL1ψ
  have hT2 : Tendsto (fun m => ∫ x in euclBall c r, (d x * φ x) * ψ m x) atTop
      (𝓝 (∫ x in euclBall c r, (d x * φ x) * ξ x)) :=
    tendsto_setIntegral_mul c r hMK hw2m hw2 (fun m => hint2 (hψL m)) (hint2 hξ) hL1ψ
  have hlimL := tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun ν _ => (hT3 ν).add (hT1 ν)
  have hlim := tendsto_nhds_unique hlimL ((hT2.neg).congr fun m => (hsm m).symm)
  -- rearrange
  have eL : ∑ ν, ∫ x in euclBall c r, (fun ν x => a ν x * ξ x) ν x * pd φ ν x =
      ∑ ν, ∫ x in euclBall c r, (a ν x * pd φ ν x) * ξ x := by
    refine Finset.sum_congr rfl fun ν _ => ?_
    congr 1; funext x; ring
  have eR : ∫ x in euclBall c r, (d x * ξ x + ∑ ν, a ν x * g ν x) * φ x =
      (∫ x in euclBall c r, (d x * φ x) * ξ x) +
        ∑ ν, ∫ x in euclBall c r, (a ν x * φ x) * g ν x := by
    rw [← integral_finsetSum _ fun ν _ => hib (hw3m ν) (hw3 ν) (hg ν),
      ← integral_add (hib hw2m hw2 hξ) (integrable_finsetSum _ fun ν _ =>
        hib (hw3m ν) (hw3 ν) (hg ν))]
    congr 1; funext x
    rw [add_mul, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun ν _ => by ring
  rw [eL, eR]
  rw [Finset.sum_add_distrib] at hlim
  linarith

/-- Bounded multipliers preserve `L²(B)`. -/
theorem memLp_bdd_mul {w f : (Fin 4 → ℝ) → ℝ} {M : ℝ}
    (hwm : AEStronglyMeasurable w (volume.restrict (euclBall c r)))
    (hw : ∀ᵐ x ∂(volume.restrict (euclBall c r)), |w x| ≤ M)
    (hf : MemLp f 2 (volume.restrict (euclBall c r))) :
    MemLp (fun x => w x * f x) 2 (volume.restrict (euclBall c r)) := by
  refine (hf.const_mul M).of_le (hwm.mul hf.aestronglyMeasurable) ?_
  filter_upwards [hw] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
  have hM : 0 ≤ M := (abs_nonneg _).trans hx
  rw [abs_of_nonneg hM]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

/-- **The tangential integration by parts on `H¹(B)`**: for `x, y ∈ H¹(B)` (closure of the
`C¹` graphs) and a bounded weakly tangential field `a` with bounded divergence `d`,
`Σ_ν ∫_B a_ν x₀ y_ν = -∫_B (d x₀ + Σ_ν a_ν x_ν) y₀`. -/
theorem IsWeakTangential.integral_H1B {a : Fin 4 → (Fin 4 → ℝ) → ℝ} {d : (Fin 4 → ℝ) → ℝ}
    {M : ℝ} (htan : IsWeakTangential c r a d) (hM : 0 ≤ M)
    (ham : ∀ ν, AEStronglyMeasurable (a ν) (volume.restrict (euclBall c r)))
    (hdm : AEStronglyMeasurable d (volume.restrict (euclBall c r)))
    (ha : ∀ ν, ∀ᵐ x ∂(volume.restrict (euclBall c r)), |a ν x| ≤ M)
    (hd : ∀ᵐ x ∂(volume.restrict (euclBall c r)), |d x| ≤ M)
    {x : H1Amb c r} (hx : x ∈ H1B c r) :
    ∀ y ∈ H1B c r, ∑ ν, ∫ z in euclBall c r, a ν z * (x none : (Fin 4 → ℝ) → ℝ) z *
        (y (some ν) : (Fin 4 → ℝ) → ℝ) z =
      -∫ z in euclBall c r, (d z * (x none : (Fin 4 → ℝ) → ℝ) z +
        ∑ ν, a ν z * (x (some ν) : (Fin 4 → ℝ) → ℝ) z) * (y none : (Fin 4 → ℝ) → ℝ) z := by
  set ξ : (Fin 4 → ℝ) → ℝ := (x none : (Fin 4 → ℝ) → ℝ)
  set g : Fin 4 → (Fin 4 → ℝ) → ℝ := fun ν => (x (some ν) : (Fin 4 → ℝ) → ℝ)
  have hξ : MemLp ξ 2 (volume.restrict (euclBall c r)) := Lp.memLp _
  have hg : ∀ ν, MemLp (g ν) 2 (volume.restrict (euclBall c r)) := fun ν => Lp.memLp _
  have hξg : ∀ ν, HasWeakPartialR (euclBall c r) ν ξ (g ν) := fun ν =>
    hasWeakPartialR_of_H1B c r hx ν
  have htan' := htan.mul c r hM ham hdm ha hd hξ hg hξg
  have hFν : ∀ ν, MemLp (fun z => a ν z * ξ z) 2 (volume.restrict (euclBall c r)) := fun ν =>
    memLp_bdd_mul c r (ham ν) (ha ν) hξ
  have hG : MemLp (fun z => d z * ξ z + ∑ ν, a ν z * g ν z) 2 (volume.restrict (euclBall c r)) :=
    (memLp_bdd_mul c r hdm hd hξ).add (memLp_finsetSum _ fun ν _ =>
      memLp_bdd_mul c r (ham ν) (ha ν) (hg ν))
  -- inner-product form
  have eL : ∀ y : H1Amb c r, ∑ ν, ∫ z in euclBall c r, a ν z * ξ z *
      (y (some ν) : (Fin 4 → ℝ) → ℝ) z = ∑ ν, ⟪(hFν ν).toLp (fun z => a ν z * ξ z), y (some ν)⟫ :=
    fun y => Finset.sum_congr rfl fun ν _ => (inner_toLp_left c r (hFν ν) _).symm
  have eR : ∀ y : H1Amb c r, ∫ z in euclBall c r, (d z * ξ z + ∑ ν, a ν z * g ν z) *
      (y none : (Fin 4 → ℝ) → ℝ) z =
        ⟪hG.toLp (fun z => d z * ξ z + ∑ ν, a ν z * g ν z), y none⟫ :=
    fun y => (inner_toLp_left c r hG _).symm
  intro y hy
  rw [eL, eR]
  revert y
  refine H1B_induction c r (P := fun y => ∑ ν, ⟪(hFν ν).toLp (fun z => a ν z * ξ z),
    y (some ν)⟫ = -⟪hG.toLp (fun z => d z * ξ z + ∑ ν, a ν z * g ν z), y none⟫) ?_ ?_
  · have hp := fun k => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin 4) => L2B c r) k).continuous
    exact isClosed_eq (continuous_finsetSum _ fun ν _ => continuous_const.inner (hp (some ν)))
      (continuous_const.inner (hp none)).neg
  · rintro ⟨v, hv⟩
    replace hv : ContDiff ℝ 1 v := hv
    simp only [graphC1_some, graphC1_none]
    rw [inner_toLp_toLp c r hG (memLp_ball_of_C1 c r hv),
      Finset.sum_congr rfl fun ν _ => inner_toLp_toLp c r (hFν ν) (memLp_ball_pd_of_C1 c r hv ν)]
    exact htan' v hv

end Tangential

end RenewalGeometry.BallAnalysis.BallAlg
