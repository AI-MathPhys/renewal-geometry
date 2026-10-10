/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallExtension

/-!
# The critical Sobolev inequality on Euclidean balls
  (stage C2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `pd_comp_ray`, `abs_pd_reflScale_le`, `norm_pd_extOut_le`: pointwise bounds for the derivatives
  of the outer piece `θ · u∘Φ` of the reflection extension
  (`|∂_i(θ u∘Φ)| ≤ (3M/r)|u∘Φ| + 4 Σ_j |∂_j u∘Φ|`, `M = sup|θ'|`);
* `integral_annulus_reflBall_le` (**change of variables under the reflection**, in polar
  coordinates and one-dimensional substitution `s = 2r - ρ`):
  `∫_{r ≤ |x-c| ≤ 3r/2} G(Φ x) dx ≤ 3^{n-1} ∫_{B_r(c)} G` for continuous `G ≥ 0`, and its `L²`
  form `eLpNorm_annulus_comp_le`;
* `memW12_ballExt`, `ballExt_eq_zero`: the reflection extension is a compactly supported
  `W^{1,2}(ℝⁿ)` function;
* `sobolev_ball` (**critical Sobolev inequality on balls**, `n ≥ 3`, `1/p' = 1/2 - 1/n`):
  `‖u‖_{L^{p'}(B_r(c))} ≤ C (Σ_i ‖∂_i u‖_{L²(B_r(c))} + r⁻¹ ‖u‖_{L²(B_r(c))})` for every `C¹`
  function `u`, with `C` independent of `c, r` (scale invariant); `p' = 4` for `n = 4`.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ} [NeZero n]

/-! ### Derivative bounds for the outer piece -/

theorem clm_apply_eq_sum_C (L : (Fin n → ℝ) →L[ℝ] ℂ) (v : Fin n → ℝ) :
    L v = ∑ j, ((v j : ℝ) : ℂ) * L (Pi.single j 1) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Complex.real_smul]

/-- Chain rule along rays: `∂_i [u(c + λ(y)(y - c))] = ∂_iλ · ⟨x - c, ∇u⟩ + λ ∂_i u`. -/
theorem pd_comp_ray {c x : Fin n → ℝ} {u : (Fin n → ℝ) → ℂ} {l : (Fin n → ℝ) → ℝ}
    (hu : DifferentiableAt ℝ u (c + l x • (x - c))) (hl : DifferentiableAt ℝ l x) (i : Fin n) :
    pd (fun y => u (c + l y • (y - c))) i x =
      ((pd l i x : ℝ) : ℂ) * ∑ j, ((x j - c j : ℝ) : ℂ) * pd u j (c + l x • (x - c)) +
        ((l x : ℝ) : ℂ) * pd u i (c + l x • (x - c)) := by
  have hg : HasFDerivAt (fun y => c + l y • (y - c))
      (l x • (ContinuousLinearMap.id ℝ (Fin n → ℝ)) + (fderiv ℝ l x).smulRight (x - c)) x := by
    have h1 : HasFDerivAt (fun y : Fin n → ℝ => y - c) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) x :=
      (hasFDerivAt_id x).sub_const c
    exact (hl.hasFDerivAt.smul h1).const_add c
  unfold pd
  rw [show (fun y => u (c + l y • (y - c))) = u ∘ (fun y => c + l y • (y - c)) from rfl,
    fderiv_comp x hu hg.differentiableAt, hg.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, Complex.real_smul]
  rw [clm_apply_eq_sum_C (fderiv ℝ u (c + l x • (x - c))) (x - c)]
  simp only [Pi.sub_apply]
  ring

theorem abs_sub_le_sqrt_sqDist (c x : Fin n → ℝ) (i : Fin n) :
    |x i - c i| ≤ Real.sqrt (sqDist c x) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_le_sqDist c x i)

/-- `|∂_i λ| ≤ 2/r` outside the ball. -/
theorem abs_pd_reflScale_le {c x : Fin n → ℝ} {r : ℝ} (hr : 0 < r) (hx : r ^ 2 ≤ sqDist c x)
    (i : Fin n) : |pd (reflScale c r) i x| ≤ 2 / r := by
  set s := sqDist c x
  have hs : 0 < s := lt_of_lt_of_le (by positivity) hx
  set S := Real.sqrt s with hSdef
  have hS : 0 < S := Real.sqrt_pos.mpr hs
  have hS2 : S ^ 2 = s := Real.sq_sqrt hs.le
  have hrS : r ≤ S := by rw [hSdef]; exact Real.le_sqrt_of_sq_le hx
  have hh : HasDerivAt (fun t : ℝ => 2 * r / Real.sqrt t - 1)
      ((0 * Real.sqrt s - 2 * r * (1 / (2 * Real.sqrt s))) / Real.sqrt s ^ 2) s :=
    ((hasDerivAt_const s (2 * r)).div (Real.hasDerivAt_sqrt hs.ne') (Real.sqrt_pos.mpr hs).ne'
      ).sub_const 1
  have e : reflScale c r = fun y => (fun t : ℝ => 2 * r / Real.sqrt t - 1) (sqDist c y) := rfl
  rw [e, pd_comp_real hh.differentiableAt ((contDiff_sqDist c (k := 1)).differentiable
    (by norm_num) x), hh.deriv, pd_sqDist]
  rw [← hSdef]
  have hxi := abs_sub_le_sqrt_sqDist c x i
  rw [← hSdef] at hxi
  have e2 : (0 * S - 2 * r * (1 / (2 * S))) / S ^ 2 * (2 * (x i - c i)) =
      -(2 * r * (x i - c i)) / S ^ 3 := by field_simp; ring
  rw [e2, abs_div, abs_neg, abs_of_pos (by positivity : 0 < S ^ 3), div_le_div_iff₀
    (by positivity) hr, abs_mul, abs_of_pos (by positivity : 0 < 2 * r)]
  have : 2 * r * |x i - c i| * r ≤ 2 * r * S * r := by gcongr
  nlinarith [mul_pos hS hS]

theorem abs_reflScale_le_one {c x : Fin n → ℝ} {r : ℝ} (hr : 0 < r) (hx1 : r ^ 2 ≤ sqDist c x)
    (hx2 : sqDist c x ≤ 9 / 4 * r ^ 2) : |reflScale c r x| ≤ 1 := by
  unfold reflScale
  set S := Real.sqrt (sqDist c x) with hSdef
  have hrS : r ≤ S := by rw [hSdef]; exact Real.le_sqrt_of_sq_le hx1
  have hS32 : S ≤ 3 / 2 * r := by
    rw [hSdef, Real.sqrt_le_left (by positivity)]; nlinarith
  have hS : 0 < S := lt_of_lt_of_le hr hrS
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hS]; nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hS]; nlinarith

/-- **Pointwise derivative bound for the outer piece** of the extension (with `M` a bound on
`|θ'|`): outside the ball,
`|∂_i (θ u∘Φ)| ≤ (3M/r) |u(Φ x)| + 4 Σ_j |∂_j u(Φ x)|`. -/
theorem norm_pd_extOut_le (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {u : (Fin n → ℝ) → ℂ}
    (hu : ContDiff ℝ 1 u) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ t, |deriv extCut t| ≤ M)
    {x : Fin n → ℝ} (hx : r ^ 2 ≤ sqDist c x) (i : Fin n) :
    ‖pd (extOut c r u) i x‖ ≤
      3 * M / r * ‖u (reflBall c r x)‖ + 4 * ∑ j, ‖pd u j (reflBall c r x)‖ := by
  have hs : 0 < sqDist c x := lt_of_lt_of_le (by positivity) hx
  have hdu : ∀ p, DifferentiableAt ℝ u p := fun p => (hu.differentiable (by norm_num)) p
  have hl : DifferentiableAt ℝ (reflScale c r) x :=
    (contDiffAt_reflScale (k := 1) r hs).differentiableAt (by norm_num)
  have hθ : HasDerivAt (fun t : ℝ => extCut (t / r ^ 2))
      (deriv extCut (sqDist c x / r ^ 2) * (1 / r ^ 2)) (sqDist c x) := by
    have h1 : HasDerivAt (fun t : ℝ => t / r ^ 2) (1 / r ^ 2) (sqDist c x) := by
      simpa using (hasDerivAt_id (sqDist c x)).div_const (r ^ 2)
    exact ((contDiff_extCut (k := 1)).differentiable (by norm_num) _).hasDerivAt.comp _ h1
  have hpθ : pd (fun y => extCut (sqDist c y / r ^ 2)) i x =
      deriv extCut (sqDist c x / r ^ 2) * (1 / r ^ 2) * (2 * (x i - c i)) := by
    rw [pd_comp_real (h := fun t : ℝ => extCut (t / r ^ 2)) hθ.differentiableAt
      ((contDiff_sqDist c (k := 1)).differentiable (by norm_num) x), hθ.deriv, pd_sqDist]
  have hdθ : DifferentiableAt ℝ (fun y => ((extCut (sqDist c y / r ^ 2) : ℝ) : ℂ)) x :=
    (Complex.ofRealCLM.differentiableAt).comp x (((contDiff_extCut (k := 1)).comp
      ((contDiff_sqDist c).div_const _)).differentiable (by norm_num) x)
  have hdΦ : DifferentiableAt ℝ (fun y => u (reflBall c r y)) x :=
    (hdu _).comp x ((contDiffAt_reflBall (k := 1) r hs).differentiableAt (by norm_num))
  have hpd : pd (extOut c r u) i x =
      ((deriv extCut (sqDist c x / r ^ 2) * (1 / r ^ 2) * (2 * (x i - c i)) : ℝ) : ℂ) *
          u (reflBall c r x) +
        ((extCut (sqDist c x / r ^ 2) : ℝ) : ℂ) *
          (((pd (reflScale c r) i x : ℝ) : ℂ) *
              ∑ j, ((x j - c j : ℝ) : ℂ) * pd u j (reflBall c r x) +
            ((reflScale c r x : ℝ) : ℂ) * pd u i (reflBall c r x)) := by
    unfold extOut
    rw [pd_mul_cc hdθ hdΦ, pd_ofReal_fun (φ := fun y => extCut (sqDist c y / r ^ 2))
      ((contDiff_extCut (k := 1)).comp
      ((contDiff_sqDist c).div_const _)), hpθ]
    congr 2
    exact pd_comp_ray (u := u) (l := reflScale c r) (hdu _) hl i
  by_cases hfar : 9 / 4 * r ^ 2 ≤ sqDist c x
  · have h9 : 9 / 4 ≤ sqDist c x / r ^ 2 := (le_div_iff₀ (by positivity)).mpr hfar
    rw [hpd, deriv_extCut_eq_zero_of_ge h9, extCut_eq_zero_of_ge h9]
    simp only [zero_mul, Complex.ofReal_zero, zero_add, norm_zero]
    positivity
  · have hnear : sqDist c x ≤ 9 / 4 * r ^ 2 := le_of_lt (not_le.mp hfar)
    have hSle : Real.sqrt (sqDist c x) ≤ 3 / 2 * r := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    have hxj : ∀ j, |x j - c j| ≤ 3 / 2 * r := fun j =>
      (abs_sub_le_sqrt_sqDist c x j).trans hSle
    have hθ1 : |extCut (sqDist c x / r ^ 2)| ≤ 1 := by
      rw [abs_of_nonneg (extCut_nonneg _)]; exact extCut_le_one _
    have hlam := abs_reflScale_le_one hr hx hnear
    have hplam := abs_pd_reflScale_le hr hx i
    set P := ∑ j, ‖pd u j (reflBall c r x)‖
    have hP0 : 0 ≤ P := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hPi : ‖pd u i (reflBall c r x)‖ ≤ P :=
      Finset.single_le_sum (f := fun j => ‖pd u j (reflBall c r x)‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ i)
    have hsum : ‖∑ j, ((x j - c j : ℝ) : ℂ) * pd u j (reflBall c r x)‖ ≤ 3 / 2 * r * P := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hxj j) (norm_nonneg _)
    have hT1 : ‖((deriv extCut (sqDist c x / r ^ 2) * (1 / r ^ 2) * (2 * (x i - c i)) : ℝ) : ℂ)‖ ≤
        3 * M / r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / r ^ 2), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have h1 := hM (sqDist c x / r ^ 2)
      have h2 := hxj i
      calc |deriv extCut (sqDist c x / r ^ 2)| * (1 / r ^ 2) * (2 * |x i - c i|) ≤
            M * (1 / r ^ 2) * (2 * (3 / 2 * r)) := by gcongr
        _ = 3 * M / r := by field_simp
    have hT2 : ‖((pd (reflScale c r) i x : ℝ) : ℂ) *
          ∑ j, ((x j - c j : ℝ) : ℂ) * pd u j (reflBall c r x) +
        ((reflScale c r x : ℝ) : ℂ) * pd u i (reflBall c r x)‖ ≤ 4 * P := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have a1 : |pd (reflScale c r) i x| *
          ‖∑ j, ((x j - c j : ℝ) : ℂ) * pd u j (reflBall c r x)‖ ≤ 2 / r * (3 / 2 * r * P) :=
        mul_le_mul hplam hsum (norm_nonneg _) (by positivity)
      have a2 : |reflScale c r x| * ‖pd u i (reflBall c r x)‖ ≤ 1 * P :=
        mul_le_mul hlam hPi (norm_nonneg _) zero_le_one
      have e3 : 2 / r * (3 / 2 * r * P) = 3 * P := by field_simp
      linarith
    have hθ1' : ‖((extCut (sqDist c x / r ^ 2) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hθ1
    rw [hpd]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have b1 := mul_le_mul_of_nonneg_right hT1 (norm_nonneg (u (reflBall c r x)))
    have b2 := mul_le_mul hθ1' hT2 (norm_nonneg _) zero_le_one
    linarith


/-! ### Change of variables under the reflection -/

/-- The closed annulus `r ≤ |x - c| ≤ 3r/2` where the outer piece lives. -/
def annulus (c : Fin n → ℝ) (r : ℝ) : Set (Fin n → ℝ) :=
  {x | r ^ 2 ≤ sqDist c x ∧ sqDist c x ≤ 9 / 4 * r ^ 2}

theorem measurableSet_annulus (c : Fin n → ℝ) (r : ℝ) : MeasurableSet (annulus c r) :=
  (measurableSet_le measurable_const (continuous_sqDist c).measurable).inter
    (measurableSet_le (continuous_sqDist c).measurable measurable_const)

/-- Beyond the annulus the outer piece vanishes identically, hence so do its derivatives. -/
theorem pd_extOut_eq_zero (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (u : (Fin n → ℝ) → ℂ)
    {x : Fin n → ℝ} (hx : 9 / 4 * r ^ 2 < sqDist c x) (i : Fin n) :
    pd (extOut c r u) i x = 0 := by
  have : extOut c r u =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const (continuous_sqDist c)).mem_nhds hx] with y hy
    exact extOut_eq_zero hr u (le_of_lt hy)
  unfold pd; rw [this.fderiv_eq]; simp

/-- `G ∘ Φ` is integrable on the annulus for continuous `G`. -/
theorem integrableOn_annulus_comp {c : Fin n → ℝ} {r : ℝ} (hr : 0 < r) {F : Type*}
    [NormedAddCommGroup F] {G : (Fin n → ℝ) → F} (hG : Continuous G) :
    IntegrableOn (fun x => G (reflBall c r x)) (annulus c r) := by
  set K := {x : Fin n → ℝ | r ^ 2 ≤ sqDist c x ∧ sqDist c x ≤ 9 / 4 * r ^ 2}
  have hKc : IsCompact K := by
    refine (isCompact_closedBall c (3 / 2 * r)).of_isClosed_subset
      ((isClosed_le continuous_const (continuous_sqDist c)).inter
        (isClosed_le (continuous_sqDist c) continuous_const)) fun x hx => ?_
    exact mem_closedBall_of_sqDist_le (by positivity) (by nlinarith [hx.2])
  have hcont : ContinuousOn (fun x => G (reflBall c r x)) K := by
    intro x hx
    have hpos : 0 < sqDist c x := lt_of_lt_of_le (by positivity) hx.1
    exact (hG.continuousAt.comp ((contDiffAt_reflBall (k := 0) r hpos).continuousAt)
      ).continuousWithinAt
  exact hcont.integrableOn_compact hKc

/-- The radial profile of `1_{annulus} · G∘Φ` on a ray. -/
theorem annulus_indicator_ray {c w : Fin n → ℝ} {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hw : ∑ i, w i ^ 2 = 1) (G : (Fin n → ℝ) → ℝ) :
    (annulus c r).indicator (fun x => G (reflBall c r x)) (c + ρ • w) =
      (Icc r (3 / 2 * r)).indicator (fun ρ => G (c + (2 * r - ρ) • w)) ρ := by
  have hs := sqDist_add_smul c w ρ hw
  have hmem : c + ρ • w ∈ annulus c r ↔ ρ ∈ Icc r (3 / 2 * r) := by
    simp only [annulus, mem_setOf_eq, hs, mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
  by_cases h : ρ ∈ Icc r (3 / 2 * r)
  · rw [indicator_of_mem (hmem.mpr h), indicator_of_mem h, reflBall_ray c w hρ hw]
  · rw [indicator_of_notMem (fun h' => h (hmem.mp h')), indicator_of_notMem h]

theorem ball_indicator_ray {c w : Fin n → ℝ} {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hw : ∑ i, w i ^ 2 = 1) (G : (Fin n → ℝ) → ℝ) :
    (euclBall c r).indicator G (c + ρ • w) = (Iio r).indicator (fun ρ => G (c + ρ • w)) ρ := by
  have hmem : c + ρ • w ∈ euclBall c r ↔ ρ ∈ Iio r := by
    simp only [euclBall, mem_setOf_eq, sqDist_add_smul c w ρ hw, mem_Iio]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  by_cases h : ρ ∈ Iio r
  · rw [indicator_of_mem (hmem.mpr h), indicator_of_mem h]
  · rw [indicator_of_notMem (fun h' => h (hmem.mp h')), indicator_of_notMem h]

/-- The one-dimensional comparison: `∫_r^{3r/2} ρ^{n-1} g(2r - ρ) dρ ≤ 3^{n-1} ∫_0^r s^{n-1} g(s) ds`
for continuous `g ≥ 0`. -/
theorem radial_reflect_le {r : ℝ} (hr : 0 < r) (k : ℕ) {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ s, 0 ≤ g s) :
    ∫ ρ in Ioi (0 : ℝ), ρ ^ k * (Icc r (3 / 2 * r)).indicator (fun ρ => g (2 * r - ρ)) ρ ≤
      3 ^ k * ∫ ρ in Ioi (0 : ℝ), ρ ^ k * (Iio r).indicator g ρ := by
  have e1 : ∫ ρ in Ioi (0 : ℝ), ρ ^ k * (Icc r (3 / 2 * r)).indicator (fun ρ => g (2 * r - ρ)) ρ =
      ∫ ρ in r..(3 / 2 * r), ρ ^ k * g (2 * r - ρ) := by
    have : (fun ρ => ρ ^ k * (Icc r (3 / 2 * r)).indicator (fun ρ => g (2 * r - ρ)) ρ) =
        (Icc r (3 / 2 * r)).indicator (fun ρ => ρ ^ k * g (2 * r - ρ)) := by
      funext ρ; by_cases h : ρ ∈ Icc r (3 / 2 * r) <;> simp [h]
    have hset : Ioi (0 : ℝ) ∩ Icc r (3 / 2 * r) = Icc r (3 / 2 * r) :=
      inter_eq_right.mpr fun x hx => lt_of_lt_of_le hr hx.1
    rw [this, setIntegral_indicator measurableSet_Icc, hset,
      intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
  have e2 : ∫ ρ in Ioi (0 : ℝ), ρ ^ k * (Iio r).indicator g ρ = ∫ ρ in (0 : ℝ)..r, ρ ^ k * g ρ := by
    have : (fun ρ => ρ ^ k * (Iio r).indicator g ρ) = (Iio r).indicator (fun ρ => ρ ^ k * g ρ) := by
      funext ρ; by_cases h : ρ ∈ Iio r <;> simp [h]
    rw [this, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
      intervalIntegral.integral_of_le hr.le, integral_Ioc_eq_integral_Ioo]
  rw [e1, e2]
  -- substitution `s = 2r - ρ`
  have e3 : ∫ ρ in r..(3 / 2 * r), ρ ^ k * g (2 * r - ρ) =
      ∫ s in (r / 2)..r, (2 * r - s) ^ k * g s := by
    have := intervalIntegral.integral_comp_sub_left (fun s => (2 * r - s) ^ k * g s)
      (a := r) (b := 3 / 2 * r) (2 * r)
    simp only [sub_sub_cancel] at this
    rw [this]; congr 1 <;> ring
  rw [e3]
  have hcont1 : Continuous fun s => (2 * r - s) ^ k * g s := by fun_prop
  have hcont2 : Continuous fun s => s ^ k * g s := by fun_prop
  have h4 : ∫ s in (r / 2)..r, (2 * r - s) ^ k * g s ≤ ∫ s in (r / 2)..r, 3 ^ k * (s ^ k * g s) := by
    refine intervalIntegral.integral_mono_on (by linarith) (hcont1.intervalIntegrable _ _)
      ((continuous_const.mul hcont2).intervalIntegrable _ _) fun s hs => ?_
    have h2 : 2 * r - s ≤ 3 * s := by linarith [hs.1]
    have h3 : (2 * r - s) ^ k ≤ (3 * s) ^ k := pow_le_pow_left₀ (by linarith [hs.2]) h2 k
    rw [mul_pow] at h3
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h3 (hg0 s)
  have h5 : ∫ s in (r / 2)..r, s ^ k * g s ≤ ∫ s in (0 : ℝ)..r, s ^ k * g s := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := r / 2) (c := r)
      (hcont2.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _)]
    have : 0 ≤ ∫ s in (0 : ℝ)..(r / 2), s ^ k * g s :=
      intervalIntegral.integral_nonneg (by linarith) fun s hs =>
        mul_nonneg (pow_nonneg hs.1 _) (hg0 s)
    linarith
  rw [intervalIntegral.integral_const_mul] at h4
  calc _ ≤ 3 ^ k * ∫ s in (r / 2)..r, s ^ k * g s := h4
    _ ≤ 3 ^ k * ∫ s in (0 : ℝ)..r, s ^ k * g s := by gcongr

/-- **Change of variables under the reflection**: for continuous `G ≥ 0`,
`∫_{annulus} G(Φ(x)) dx ≤ 3^{n-1} ∫_{B_r(c)} G`. -/
theorem integral_annulus_reflBall_le (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    {G : (Fin n → ℝ) → ℝ} (hG : Continuous G) (hG0 : ∀ x, 0 ≤ G x) :
    ∫ x in annulus c r, G (reflBall c r x) ≤ 3 ^ (n - 1) * ∫ x in euclBall c r, G x := by
  have hiA : Integrable ((annulus c r).indicator fun x => G (reflBall c r x)) :=
    (integrable_indicator_iff (measurableSet_annulus c r)).mpr (integrableOn_annulus_comp hr hG)
  have hiB : Integrable ((euclBall c r).indicator G) :=
    (integrable_indicator_iff (measurableSet_euclBall c r)).mpr
      (integrableOn_euclBall hr.le hG)
  rw [← integral_indicator (measurableSet_annulus c r),
    ← integral_indicator (measurableSet_euclBall c r), integral_polar c _ hiA,
    integral_polar c _ hiB, ← integral_const_mul]
  refine integral_mono_ae (integrable_polar c _ hiA) ((integrable_polar c _ hiB).const_mul _) ?_
  filter_upwards [ae_sphereMeasure n] with w hw
  simp only [smul_eq_mul]
  have eA : ∫ ρ in Ioi (0 : ℝ), ρ ^ (n - 1) *
        (annulus c r).indicator (fun x => G (reflBall c r x)) (c + ρ • w) =
      ∫ ρ in Ioi (0 : ℝ), ρ ^ (n - 1) *
        (Icc r (3 / 2 * r)).indicator (fun ρ => (fun s => G (c + s • w)) (2 * r - ρ)) ρ :=
    setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => by
      rw [annulus_indicator_ray hr hρ hw]
  have eB : ∫ ρ in Ioi (0 : ℝ), ρ ^ (n - 1) * (euclBall c r).indicator G (c + ρ • w) =
      ∫ ρ in Ioi (0 : ℝ), ρ ^ (n - 1) * (Iio r).indicator (fun s => G (c + s • w)) ρ :=
    setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => by
      rw [ball_indicator_ray hr hρ hw]
  rw [eA, eB]
  exact radial_reflect_le hr (n - 1)
    (hG.comp (continuous_const.add (continuous_id.smul continuous_const))) fun s => hG0 _


/-! ### `L²` norms -/

theorem eLpNorm_two_eq_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : Integrable (fun x => ‖f x‖ ^ 2) μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall fun x => by positivity)]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  norm_num

/-- **`L²` change of variables under the reflection**:
`‖g ∘ Φ‖_{L²(annulus)} ≤ 3^{(n-1)/2} ‖g‖_{L²(B_r(c))}` for continuous `g`. -/
theorem eLpNorm_annulus_comp_le (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {g : (Fin n → ℝ) → ℂ}
    (hg : Continuous g) :
    eLpNorm (fun x => g (reflBall c r x)) 2 (volume.restrict (annulus c r)) ≤
      ENNReal.ofReal (3 ^ (n - 1)) ^ (1 / 2 : ℝ) *
        eLpNorm g 2 (volume.restrict (euclBall c r)) := by
  have hG : Continuous fun x => ‖g x‖ ^ 2 := hg.norm.pow 2
  have key := integral_annulus_reflBall_le c hr hG (fun x => by positivity)
  rw [eLpNorm_two_eq_ofReal (integrableOn_annulus_comp hr hG),
    eLpNorm_two_eq_ofReal (integrableOn_euclBall hr.le hG),
    ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal key) (by norm_num)

/-! ### The extension is a compactly supported `H¹(ℝⁿ)` function -/

theorem isFiniteMeasure_restrict_euclBall (c : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    IsFiniteMeasure (volume.restrict (euclBall c r)) :=
  ⟨by rw [Measure.restrict_apply_univ]
      exact (measure_mono (euclBall_subset_closedBall c hr)).trans_lt
        (isCompact_closedBall c r).measure_lt_top⟩

theorem memLp_euclBall_of_continuous (c : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r) {F : Type*}
    [NormedAddCommGroup F] {g : (Fin n → ℝ) → F} (hg : Continuous g) (p : ℝ≥0∞) :
    MemLp g p (volume.restrict (euclBall c r)) := by
  have := isFiniteMeasure_restrict_euclBall c hr
  obtain ⟨C, hC⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable C
    (ae_restrict_of_forall_mem (measurableSet_euclBall c r) fun x hx =>
      hC x (euclBall_subset_closedBall c hr hx))

theorem hasCompactSupport_extOut (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (u : (Fin n → ℝ) → ℂ) :
    HasCompactSupport (extOut c r u) := by
  refine HasCompactSupport.intro (isCompact_closedBall c (3 / 2 * r)) fun x hx => ?_
  refine extOut_eq_zero hr u ?_
  by_contra h
  exact hx (mem_closedBall_of_sqDist_le (by positivity) (by nlinarith [not_le.mp h]))

theorem ballExt_eq_add (c : Fin n → ℝ) (r : ℝ) (u : (Fin n → ℝ) → ℂ) :
    ballExt c r u = (euclBall c r).indicator u + (euclBall c r)ᶜ.indicator (extOut c r u) := by
  funext x
  by_cases hx : x ∈ euclBall c r <;> simp [ballExt, hx]

theorem ballExtGrad_eq_add (c : Fin n → ℝ) (r : ℝ) (u : (Fin n → ℝ) → ℂ) (i : Fin n) :
    ballExtGrad c r u i =
      (euclBall c r).indicator (pd u i) + (euclBall c r)ᶜ.indicator (pd (extOut c r u) i) := by
  funext x
  by_cases hx : x ∈ euclBall c r <;> simp [ballExtGrad, hx]

/-- The extension is in `W^{1,2}(ℝⁿ)`. -/
theorem memW12_ballExt (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {u : (Fin n → ℝ) → ℂ}
    (hu : ContDiff ℝ 1 u) : MemW12 univ (ballExt c r u) (ballExtGrad c r u) := by
  have hB := measurableSet_euclBall c r
  have hext := contDiff_extOut c hr hu
  refine ⟨?_, fun i => ?_, fun i => hasWeakPartial_ballExt c hr hu i⟩
  · rw [Measure.restrict_univ, ballExt_eq_add]
    refine MemLp.add ((memLp_indicator_iff_restrict hB).mpr
      (memLp_euclBall_of_continuous c hr.le hu.continuous 2)) (MemLp.indicator hB.compl ?_)
    exact hext.continuous.memLp_of_hasCompactSupport (hasCompactSupport_extOut c hr u)
  · rw [Measure.restrict_univ, ballExtGrad_eq_add]
    refine MemLp.add ((memLp_indicator_iff_restrict hB).mpr
      (memLp_euclBall_of_continuous c hr.le (continuous_pd hu i) 2)) (MemLp.indicator hB.compl ?_)
    exact (continuous_pd hext i).memLp_of_hasCompactSupport
      (hasCompactSupport_pd (hasCompactSupport_extOut c hr u) i)

/-- The extension vanishes far away (in the sup norm of `Fin n → ℝ`). -/
theorem ballExt_eq_zero (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (u : (Fin n → ℝ) → ℂ)
    {x : Fin n → ℝ} (hx : ‖c‖ + 2 * r < ‖x‖) : ballExt c r u x = 0 := by
  have hxc : 2 * r < ‖x - c‖ := by
    have := norm_sub_norm_le x c; linarith
  have hfar : 9 / 4 * r ^ 2 ≤ sqDist c x := by
    by_contra h
    have hle : sqDist c x ≤ (2 * r) ^ 2 := by nlinarith [not_le.mp h]
    have := mem_closedBall_of_sqDist_le (by positivity) hle
    rw [mem_closedBall, dist_eq_norm] at this
    linarith
  have hnot : x ∉ euclBall c r := fun h => by
    have : sqDist c x < r ^ 2 := h
    nlinarith
  simp only [ballExt, piecewise_eq_of_notMem _ _ _ hnot]
  exact extOut_eq_zero hr u hfar

/-! ### The critical Sobolev inequality on balls -/

/-- **`L²` bound for the gradient of the extension outside the ball.** -/
theorem eLpNorm_pd_extOut_le (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {u : (Fin n → ℝ) → ℂ}
    (hu : ContDiff ℝ 1 u) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ t, |deriv extCut t| ≤ M) (i : Fin n) :
    eLpNorm (pd (extOut c r u) i) 2 (volume.restrict (euclBall c r)ᶜ) ≤
      ENNReal.ofReal (3 ^ (n - 1)) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (3 * M / r) * eLpNorm u 2 (volume.restrict (euclBall c r)) +
          4 * ∑ j, eLpNorm (pd u j) 2 (volume.restrict (euclBall c r))) := by
  set bnd : (Fin n → ℝ) → ℝ := fun x =>
    3 * M / r * ‖u (reflBall c r x)‖ + 4 * ∑ j, ‖pd u j (reflBall c r x)‖
  have hA := measurableSet_annulus c r
  have h1 : eLpNorm (pd (extOut c r u) i) 2 (volume.restrict (euclBall c r)ᶜ) ≤
      eLpNorm ((annulus c r).indicator bnd) 2 (volume.restrict (euclBall c r)ᶜ) := by
    refine eLpNorm_mono_ae (ae_restrict_of_forall_mem (measurableSet_euclBall c r).compl
      fun x hx => ?_)
    have hx1 : r ^ 2 ≤ sqDist c x := not_lt.mp hx
    by_cases hxa : x ∈ annulus c r
    · rw [indicator_of_mem hxa, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact norm_pd_extOut_le c hr hu hM0 hM hx1 i
    · have hfar : 9 / 4 * r ^ 2 < sqDist c x := by
        by_contra h; exact hxa ⟨hx1, not_lt.mp h⟩
      rw [pd_extOut_eq_zero c hr u hfar, norm_zero]; exact norm_nonneg _
  have h2 : eLpNorm ((annulus c r).indicator bnd) 2 (volume.restrict (euclBall c r)ᶜ) ≤
      eLpNorm bnd 2 (volume.restrict (annulus c r)) := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hA]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hmA : ∀ {g : (Fin n → ℝ) → ℂ}, Continuous g →
      AEStronglyMeasurable (fun x => ‖g (reflBall c r x)‖) (volume.restrict (annulus c r)) :=
    fun hg => (integrableOn_annulus_comp hr hg).aestronglyMeasurable.norm
  have h3 : eLpNorm bnd 2 (volume.restrict (annulus c r)) ≤
      ENNReal.ofReal (3 * M / r) *
          eLpNorm (fun x => u (reflBall c r x)) 2 (volume.restrict (annulus c r)) +
        4 * ∑ j, eLpNorm (fun x => pd u j (reflBall c r x)) 2 (volume.restrict (annulus c r)) := by
    refine (eLpNorm_add_le ((hmA hu.continuous).const_mul _)
      ((Finset.aestronglyMeasurable_fun_sum _ fun j _ => hmA (continuous_pd hu j)).const_mul _)
      (by norm_num)).trans (add_le_add ?_ ?_)
    · rw [show (fun x => 3 * M / r * ‖u (reflBall c r x)‖) =
          (3 * M / r) • fun x => ‖u (reflBall c r x)‖ from rfl]
      refine eLpNorm_const_smul_le.trans (le_of_eq ?_)
      rw [Real.enorm_eq_ofReal (by positivity), eLpNorm_norm]
    · rw [show (fun x => 4 * ∑ j, ‖pd u j (reflBall c r x)‖) =
          (4 : ℝ) • ∑ j, (fun x => ‖pd u j (reflBall c r x)‖) from by
            funext x; simp [Finset.sum_apply]]
      refine eLpNorm_const_smul_le.trans ?_
      rw [Real.enorm_eq_ofReal (by norm_num), ENNReal.ofReal_ofNat]
      gcongr
      refine (eLpNorm_sum_le (fun j _ => hmA (continuous_pd hu j)) (by norm_num)).trans
        (le_of_eq ?_)
      exact Finset.sum_congr rfl fun j _ => eLpNorm_norm _
  have h4 := eLpNorm_annulus_comp_le c hr hu.continuous
  have h5 := fun j => eLpNorm_annulus_comp_le c hr (continuous_pd hu j)
  refine h1.trans (h2.trans (h3.trans ?_))
  set K := ENNReal.ofReal (3 ^ (n - 1)) ^ (1 / 2 : ℝ)
  rw [mul_add]
  refine add_le_add ?_ ?_
  · calc ENNReal.ofReal (3 * M / r) *
          eLpNorm (fun x => u (reflBall c r x)) 2 (volume.restrict (annulus c r))
        ≤ ENNReal.ofReal (3 * M / r) * (K * eLpNorm u 2 (volume.restrict (euclBall c r))) := by
          gcongr
      _ = _ := mul_left_comm _ _ _
  · calc 4 * ∑ j, eLpNorm (fun x => pd u j (reflBall c r x)) 2 (volume.restrict (annulus c r))
        ≤ 4 * ∑ j, K * eLpNorm (pd u j) 2 (volume.restrict (euclBall c r)) := by
          gcongr with j; exact h5 j
      _ = _ := by rw [← Finset.mul_sum, mul_left_comm]


/-- The extension restricted to the ball is `u`. -/
theorem eLpNorm_ball_le_ballExt (c : Fin n → ℝ) (r : ℝ) (u : (Fin n → ℝ) → ℂ) (p : ℝ≥0∞) :
    eLpNorm u p (volume.restrict (euclBall c r)) ≤ eLpNorm (ballExt c r u) p volume := by
  have e : eLpNorm u p (volume.restrict (euclBall c r)) =
      eLpNorm (ballExt c r u) p (volume.restrict (euclBall c r)) := by
    refine eLpNorm_congr_ae ((ae_restrict_iff' (measurableSet_euclBall c r)).mpr
      (Eventually.of_forall fun x hx => ?_))
    simp [ballExt, hx]
  rw [e]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

theorem eLpNorm_ballExtGrad_le (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {u : (Fin n → ℝ) → ℂ}
    (hu : ContDiff ℝ 1 u) (i : Fin n) :
    eLpNorm (ballExtGrad c r u i) 2 volume ≤
      eLpNorm (pd u i) 2 (volume.restrict (euclBall c r)) +
        eLpNorm (pd (extOut c r u) i) 2 (volume.restrict (euclBall c r)ᶜ) := by
  have hB := measurableSet_euclBall c r
  rw [ballExtGrad_eq_add]
  refine (eLpNorm_add_le ((continuous_pd hu i).aestronglyMeasurable.indicator hB)
    ((continuous_pd (contDiff_extOut c hr hu) i).aestronglyMeasurable.indicator hB.compl)
    (by norm_num)).trans (le_of_eq ?_)
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hB, eLpNorm_indicator_eq_eLpNorm_restrict hB.compl]

/-- **The critical Sobolev inequality on Euclidean balls** for `C¹` functions: in dimension
`n ≥ 3`, with `1/p' = 1/2 - 1/n` (`p' = 4` for `n = 4`), there is a constant `C` (independent of
the ball) such that
`‖u‖_{L^{p'}(B_r(c))} ≤ C (Σ_i ‖∂_i u‖_{L²(B_r(c))} + r⁻¹ ‖u‖_{L²(B_r(c))})`.
Scale invariant.  Proof: the reflection extension `ballExt` (gluing lemma, `L²` change of
variables under the reflection) is a compactly supported `W^{1,2}(ℝⁿ)` function, to which the
critical Sobolev embedding `SobolevOpen.eLpNorm_le_sum_grad_of_ball` applies. -/
theorem sobolev_ball (hn : 2 < n) {p' : ℝ≥0} (hp' : (p' : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (n : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ (c : Fin n → ℝ) (r : ℝ), 0 < r → ∀ u : (Fin n → ℝ) → ℂ, ContDiff ℝ 1 u →
      eLpNorm u p' (volume.restrict (euclBall c r)) ≤
        C * (∑ i, eLpNorm (pd u i) 2 (volume.restrict (euclBall c r)) +
          ENNReal.ofReal r⁻¹ * eLpNorm u 2 (volume.restrict (euclBall c r))) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_extCut
  set CG := SNormLESNormFDerivOfEqConst ℂ (volume : Measure (Fin n → ℝ)) 2
  set K : ℝ≥0∞ := ENNReal.ofReal (3 ^ (n - 1)) ^ (1 / 2 : ℝ)
  have hK : K ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  set T : ℝ≥0∞ := 1 + 4 * n * K + n * K * ENNReal.ofReal (3 * M)
  have hT : T ≠ ⊤ := by
    simp only [T]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top n)) hK⟩,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hK)
        ENNReal.ofReal_ne_top⟩
  have hCfin : (CG : ℝ≥0∞) * T ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hT
  refine ⟨((CG : ℝ≥0∞) * T).toNNReal, fun c r hr u hu => ?_⟩
  rw [ENNReal.coe_toNNReal hCfin]
  set S := ∑ i, eLpNorm (pd u i) 2 (volume.restrict (euclBall c r))
  set U := eLpNorm u 2 (volume.restrict (euclBall c r))
  set R := ENNReal.ofReal r⁻¹
  have hW := memW12_ballExt c hr hu
  have hcard : 2 < Fintype.card (Fin n) := by simpa using hn
  have hGNS := eLpNorm_le_sum_grad_of_ball hW (fun x hx => ballExt_eq_zero c hr u hx) hcard
    (by simpa using hp')
  have hA : ENNReal.ofReal (3 * M / r) = ENNReal.ofReal (3 * M) * R := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity)]
  have hGi : ∀ i, eLpNorm (ballExtGrad c r u i) 2 volume ≤
      eLpNorm (pd u i) 2 (volume.restrict (euclBall c r)) +
        K * (ENNReal.ofReal (3 * M) * R * U + 4 * S) := fun i => by
    refine (eLpNorm_ballExtGrad_le c hr hu i).trans (add_le_add le_rfl ?_)
    have := eLpNorm_pd_extOut_le c hr hu hM0 hM i
    rwa [hA] at this
  have hsum : ∑ i, eLpNorm (ballExtGrad c r u i) 2 volume ≤
      (1 + 4 * n * K) * S + n * K * ENNReal.ofReal (3 * M) * (R * U) := by
    refine (Finset.sum_le_sum fun i _ => hGi i).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  calc eLpNorm u p' (volume.restrict (euclBall c r))
      ≤ eLpNorm (ballExt c r u) p' volume := eLpNorm_ball_le_ballExt c r u p'
    _ ≤ CG * ∑ i, eLpNorm (ballExtGrad c r u i) 2 volume := hGNS
    _ ≤ CG * ((1 + 4 * n * K) * S + n * K * ENNReal.ofReal (3 * M) * (R * U)) := by gcongr
    _ ≤ CG * (T * S + T * (R * U)) := by
        gcongr
        · simp only [T]; exact le_add_right le_rfl
        · simp only [T]; exact le_add_left le_rfl
    _ = CG * T * (S + R * U) := by ring

end RenewalGeometry.BallAnalysis
