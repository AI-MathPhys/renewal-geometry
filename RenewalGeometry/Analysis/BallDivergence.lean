/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallPolar
import RenewalGeometry.Analysis.SobolevChainRule

/-!
# The divergence theorem and integration by parts on Euclidean balls
  (stage C0 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.  On the coordinate space `Fin n → ℝ`
(`n ≥ 1`, partial derivatives `SobolevOpen.pd`), with the Euclidean ball
`euclBall c r = {x | |x - c|² < r²}` (`sqDist c x = Σ (x i - c i)²`) and the surface measure
`σ = sphereMeasure n` of the unit sphere (`BallPolar.lean`):

* `divergence_ball` (**Gauss divergence theorem on a ball**): for a `C¹` vector field `X`,
  `∫_{B_r(c)} div X = r^{n-1} ∫_{S^{n-1}} ⟨X(c + rω), ω⟩ dσ(ω)`;
* `integral_pd_ball`: `∫_{B_r(c)} ∂_i f = r^{n-1} ∫ f(c + rω) ω_i dσ`;
* `integral_mul_pd_ball` (**integration by parts**):
  `∫_B u ∂_i v = r^{n-1} ∫ u v ω_i dσ - ∫_B ∂_i u v`;
* `green_first_ball` (**Green's first identity**): `∫_B u Δv + ∫_B ∇u·∇v = r^{n-1} ∫ u ∂_ν v dσ`.

Proof of the divergence theorem (no boundary charts): the smooth cutoffs
`χ_k(x) = θ((k+1)(1 - |x - c|²/r²))` (`ballCut`; `θ = smoothTransition`) are compactly supported,
so the whole-space integration by parts (`integral_pd_mul_eq_neg_real`) gives
`∫ χ_k div X = ∫ cutGrad_k(x) ⟨x - c, X(x)⟩ dx` (`integral_ballCut_mul_div`); in polar
coordinates (`integral_polar`) the right side is `∫_σ ∫_0^∞ K_k(ρ) ρ^{n-1} ⟨ω, X(c + ρω)⟩ dρ dσ`
with the radial approximate identity `K_k = cutK r k` (`integral_cutGrad_polar`).  As `k → ∞`,
`χ_k → 1_{B_r(c)}` pointwise (`tendsto_ballCut`, dominated convergence, `tendsto_ball_side`) and
`K_k` concentrates at `ρ = r` (`tendsto_integral_cutK`, dominated convergence on the finite
measure `σ`, `tendsto_sphere_side`).
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-! ### Euclidean balls in `Fin n → ℝ` -/

/-- The squared Euclidean distance `|x - c|² = Σ (x i - c i)²`. -/
def sqDist (c x : Fin n → ℝ) : ℝ := ∑ i, (x i - c i) ^ 2

/-- The open Euclidean ball `{x : |x - c| < r}` in the coordinate space `Fin n → ℝ`. -/
def euclBall (c : Fin n → ℝ) (r : ℝ) : Set (Fin n → ℝ) := {x | sqDist c x < r ^ 2}

theorem continuous_sqDist (c : Fin n → ℝ) : Continuous (sqDist c) := by
  unfold sqDist; fun_prop

theorem contDiff_sqDist (c : Fin n → ℝ) {k : WithTop ℕ∞} : ContDiff ℝ k (sqDist c) := by
  unfold sqDist
  exact ContDiff.sum fun i _ => ((contDiff_apply ℝ ℝ i).sub contDiff_const).pow 2

theorem isOpen_euclBall (c : Fin n → ℝ) (r : ℝ) : IsOpen (euclBall c r) :=
  isOpen_lt (continuous_sqDist c) continuous_const

theorem measurableSet_euclBall (c : Fin n → ℝ) (r : ℝ) : MeasurableSet (euclBall c r) :=
  (isOpen_euclBall c r).measurableSet

theorem sqDist_nonneg (c x : Fin n → ℝ) : 0 ≤ sqDist c x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sq_le_sqDist (c x : Fin n → ℝ) (i : Fin n) : (x i - c i) ^ 2 ≤ sqDist c x :=
  Finset.single_le_sum (f := fun i => (x i - c i) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ i)

/-- A point with `|x - c| ≤ r` lies in the (sup-norm) closed ball `closedBall c r`. -/
theorem mem_closedBall_of_sqDist_le {c x : Fin n → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (h : sqDist c x ≤ r ^ 2) : x ∈ closedBall c r := by
  rw [mem_closedBall, dist_pi_le_iff hr]
  intro i
  rw [Real.dist_eq]
  have := (sq_le_sqDist c x i).trans h
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem euclBall_subset_closedBall (c : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    euclBall c r ⊆ closedBall c r := fun _ hx => mem_closedBall_of_sqDist_le hr (le_of_lt hx)

theorem sqDist_add_smul (c w : Fin n → ℝ) (ρ : ℝ) (hw : ∑ i, w i ^ 2 = 1) :
    sqDist c (c + ρ • w) = ρ ^ 2 := by
  unfold sqDist
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left, mul_pow]
  rw [← Finset.mul_sum, hw, mul_one]

/-- The partial derivatives of `|x - c|²`. -/
theorem hasFDerivAt_sqDist (c x : Fin n → ℝ) :
    HasFDerivAt (sqDist c) (∑ j, (2 * (x j - c j)) • ContinuousLinearMap.proj
      (R := ℝ) (φ := fun _ : Fin n => ℝ) j) x := by
  unfold sqDist
  have : ∀ j ∈ (Finset.univ : Finset (Fin n)), HasFDerivAt (fun x : Fin n → ℝ => (x j - c j) ^ 2)
      ((2 * (x j - c j)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) x := by
    intro j _
    have h0 : HasFDerivAt (fun x : Fin n → ℝ => x j)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) x := hasFDerivAt_apply j x
    have h1 := (h0.sub_const (c j)).pow 2
    refine h1.congr_fderiv ?_
    rw [nsmul_eq_mul]; norm_num
  exact HasFDerivAt.fun_sum this

theorem pd_sqDist (c x : Fin n → ℝ) (i : Fin n) : pd (sqDist c) i x = 2 * (x i - c i) := by
  unfold pd
  rw [(hasFDerivAt_sqDist c x).fderiv]
  simp [Pi.single_apply]

/-- Chain rule for `pd` through a real function of one variable. -/
theorem pd_comp_real {h : ℝ → ℝ} {q : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hh : DifferentiableAt ℝ h (q x)) (hq : DifferentiableAt ℝ q x) (i : Fin n) :
    pd (fun y => h (q y)) i x = deriv h (q x) * pd q i x := by
  unfold pd
  have := hh.hasDerivAt.comp_hasFDerivAt x hq.hasFDerivAt
  rw [show (fun y => h (q y)) = h ∘ q from rfl, this.fderiv]
  simp

/-! ### The smooth cutoffs of the ball -/

/-- The smooth cutoff `χ_k(x) = θ((k+1)(1 - |x - c|²/r²))` of the ball `B_r(c)`:
`1` on `B_{r√(1-1/(k+1))}(c)`, `0` outside `B_r(c)`. -/
def ballCut (c : Fin n → ℝ) (r : ℝ) (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  Real.smoothTransition (((k : ℝ) + 1) * (1 - sqDist c x / r ^ 2))

/-- The weight `-(∂χ_k)·(x - c)/|x-c|²`-type factor:
`-∂_i χ_k(x) = cutGrad c r k x · (x i - c i)`. -/
def cutGrad (c : Fin n → ℝ) (r : ℝ) (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  2 / r ^ 2 * ((k : ℝ) + 1) *
    deriv Real.smoothTransition (((k : ℝ) + 1) * (1 - sqDist c x / r ^ 2))

theorem contDiff_ballCut (c : Fin n → ℝ) (r : ℝ) (k : ℕ) : ContDiff ℝ ∞ (ballCut c r k) := by
  unfold ballCut
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp
    (contDiff_const.mul (contDiff_const.sub ((contDiff_sqDist c).div_const _)))

theorem continuous_cutGrad (c : Fin n → ℝ) (r : ℝ) (k : ℕ) : Continuous (cutGrad c r k) := by
  unfold cutGrad
  exact continuous_const.mul (continuous_deriv_smoothTransition.comp
    (continuous_const.mul (continuous_const.sub ((continuous_sqDist c).div_const _))))

theorem ballCut_eq_zero {c x : Fin n → ℝ} {r : ℝ} (hr : 0 < r) (k : ℕ)
    (h : r ^ 2 ≤ sqDist c x) : ballCut c r k x = 0 := by
  unfold ballCut
  apply Real.smoothTransition.zero_of_nonpos
  have : 1 ≤ sqDist c x / r ^ 2 := by rw [one_le_div (by positivity)]; exact h
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  nlinarith

theorem cutGrad_eq_zero {c x : Fin n → ℝ} {r : ℝ} (hr : 0 < r) (k : ℕ)
    (h : r ^ 2 ≤ sqDist c x) : cutGrad c r k x = 0 := by
  unfold cutGrad
  rw [deriv_smoothTransition_eq_zero (Or.inl ?_), mul_zero]
  have : 1 ≤ sqDist c x / r ^ 2 := by rw [one_le_div (by positivity)]; exact h
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  nlinarith

theorem eq_zero_of_not_mem_closedBall {c x : Fin n → ℝ} {r : ℝ} (hr : 0 < r)
    (hx : x ∉ closedBall c r) : r ^ 2 ≤ sqDist c x := by
  by_contra h
  exact hx (mem_closedBall_of_sqDist_le hr.le (le_of_lt (not_le.mp h)))

theorem hasCompactSupport_ballCut (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    HasCompactSupport (ballCut c r k) :=
  HasCompactSupport.intro (isCompact_closedBall c r) fun _ hx =>
    ballCut_eq_zero hr k (eq_zero_of_not_mem_closedBall hr hx)

theorem hasCompactSupport_cutGrad (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    HasCompactSupport (cutGrad c r k) :=
  HasCompactSupport.intro (isCompact_closedBall c r) fun _ hx =>
    cutGrad_eq_zero hr k (eq_zero_of_not_mem_closedBall hr hx)

theorem ballCut_nonneg (c : Fin n → ℝ) (r : ℝ) (k : ℕ) (x : Fin n → ℝ) : 0 ≤ ballCut c r k x :=
  Real.smoothTransition.nonneg _

theorem ballCut_le_one (c : Fin n → ℝ) (r : ℝ) (k : ℕ) (x : Fin n → ℝ) : ballCut c r k x ≤ 1 :=
  Real.smoothTransition.le_one _

theorem pd_ballCut (c : Fin n → ℝ) (r : ℝ) (k : ℕ) (i : Fin n) (x : Fin n → ℝ) :
    pd (ballCut c r k) i x = -(cutGrad c r k x * (x i - c i)) := by
  set h : ℝ → ℝ := fun s => Real.smoothTransition (((k : ℝ) + 1) * (1 - s / r ^ 2))
  have hh : HasDerivAt h (deriv Real.smoothTransition (((k : ℝ) + 1) * (1 - sqDist c x / r ^ 2)) *
      (((k : ℝ) + 1) * (-(1 / r ^ 2)))) (sqDist c x) := by
    have h1 : HasDerivAt (fun s : ℝ => ((k : ℝ) + 1) * (1 - s / r ^ 2))
        (((k : ℝ) + 1) * (-(1 / r ^ 2))) (sqDist c x) := by
      have := ((hasDerivAt_id (sqDist c x)).div_const (r ^ 2)).const_sub 1 |>.const_mul ((k : ℝ) + 1)
      exact this.congr_deriv (by simp)
    exact (((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num))
      _).hasDerivAt.comp _ h1
  have e : ballCut c r k = fun y => h (sqDist c y) := rfl
  rw [e, pd_comp_real hh.differentiableAt ((contDiff_sqDist c (k := 1)).differentiable
    (by norm_num) x), hh.deriv, pd_sqDist]
  unfold cutGrad; ring

/-- Pointwise convergence of the cutoffs to the indicator of the open ball. -/
theorem tendsto_ballCut (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (x : Fin n → ℝ) :
    Tendsto (fun k : ℕ => ballCut c r k x) atTop (𝓝 ((euclBall c r).indicator 1 x)) := by
  by_cases hx : x ∈ euclBall c r
  · rw [indicator_of_mem hx, Pi.one_apply]
    have ht : 0 < 1 - sqDist c x / r ^ 2 := by
      rw [sub_pos, div_lt_one (by positivity)]; exact hx
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - sqDist c x / r ^ 2))
    refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N, fun k hk => ?_⟩)
    unfold ballCut
    symm; apply Real.smoothTransition.one_of_one_le
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_lt_iff₀ ht] at hN
    nlinarith
  · rw [indicator_of_notMem hx]
    have : r ^ 2 ≤ sqDist c x := not_lt.mp hx
    simp only [ballCut_eq_zero hr _ this]
    exact tendsto_const_nhds

/-! ### The divergence theorem on Euclidean balls -/

/-- Step 1 (whole-space integration by parts against the cutoff):
`∫ χ_k div X = ∫ cutGrad · ⟨x - c, X⟩`. -/
theorem integral_ballCut_mul_div (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (X : Fin n → (Fin n → ℝ) → ℝ) (hX : ∀ i, ContDiff ℝ 1 (X i)) (k : ℕ) :
    ∫ x, ballCut c r k x * ∑ i, pd (X i) i x =
      ∫ x, cutGrad c r k x * ∑ i, (x i - c i) * X i x := by
  have h1 : ∀ i, ∫ x, ballCut c r k x * pd (X i) i x =
      ∫ x, cutGrad c r k x * ((x i - c i) * X i x) := by
    intro i
    have h0 := integral_pd_mul_eq_neg_real (hX i) (contDiff_ballCut c r k)
      (hasCompactSupport_ballCut c hr k) i
    have h2 : ∫ x, pd (ballCut c r k) i x * X i x =
        -∫ x, cutGrad c r k x * ((x i - c i) * X i x) := by
      rw [← integral_neg]; congr 1; funext x; rw [pd_ballCut]; ring
    linarith
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum _ (fun i _ => ?_), integral_finset_sum _ (fun i _ => ?_)]
  · exact Finset.sum_congr rfl fun i _ => h1 i
  · exact ((continuous_cutGrad c r k).mul (((continuous_apply i).sub continuous_const).mul
      (hX i).continuous)).integrable_of_hasCompactSupport
      (hasCompactSupport_cutGrad c hr k).mul_right
  · exact ((contDiff_ballCut c r k).continuous.mul (continuous_pd (hX i) i)
      ).integrable_of_hasCompactSupport (hasCompactSupport_ballCut c hr k).mul_right

variable [NeZero n]

/-- Step 2 (polar coordinates): the right side of step 1 as a radial average. -/
theorem integral_cutGrad_polar (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (X : Fin n → (Fin n → ℝ) → ℝ) (hX : ∀ i, Continuous (X i)) (k : ℕ) :
    ∫ x, cutGrad c r k x * ∑ i, (x i - c i) * X i x =
      ∫ w, (∫ ρ in Ioi (0 : ℝ), cutK r k ρ * (ρ ^ (n - 1) * ∑ i, w i * X i (c + ρ • w)))
        ∂(sphereMeasure n) := by
  have hint : Integrable (fun x => cutGrad c r k x * ∑ i, (x i - c i) * X i x) :=
    ((continuous_cutGrad c r k).mul (continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).sub continuous_const).mul (hX i))).integrable_of_hasCompactSupport
      (hasCompactSupport_cutGrad c hr k).mul_right
  rw [integral_polar c _ hint]
  refine integral_congr_ae ?_
  filter_upwards [ae_sphereMeasure n] with w hw
  congr 1; funext ρ
  simp only [cutGrad, cutK, sqDist_add_smul c w ρ hw, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
    add_sub_cancel_left]
  simp_rw [mul_assoc ρ]
  rw [← Finset.mul_sum]
  ring

/-- Step 3 (the boundary side): concentration of the radial kernel on the sphere. -/
theorem tendsto_sphere_side (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (X : Fin n → (Fin n → ℝ) → ℝ) (hX : ∀ i, Continuous (X i)) :
    Tendsto (fun k : ℕ => ∫ w, (∫ ρ in Ioi (0 : ℝ),
        cutK r k ρ * (ρ ^ (n - 1) * ∑ i, w i * X i (c + ρ • w))) ∂(sphereMeasure n))
      atTop (𝓝 (∫ w, r ^ (n - 1) * ∑ i, w i * X i (c + r • w) ∂(sphereMeasure n))) := by
  set φ : (Fin n → ℝ) → ℝ → ℝ := fun w ρ => ρ ^ (n - 1) * ∑ i, w i * X i (c + ρ • w)
  have hφ : Continuous fun p : (Fin n → ℝ) × ℝ => φ p.1 p.2 := by
    simp only [φ]
    refine (continuous_snd.pow _).mul (continuous_finset_sum _ fun i _ => ?_)
    exact ((continuous_apply i).comp continuous_fst).mul ((hX i).comp
      (continuous_const.add (continuous_snd.smul continuous_fst)))
  obtain ⟨B, hB⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn
    (f := fun y => ∑ i, |X i y|) (continuous_finset_sum _ fun i _ => (hX i).abs).continuousOn
  refine tendsto_integral_of_dominated_convergence (fun _ => r ^ (n - 1) * B) (fun k => ?_)
    (integrable_const _) (fun k => ?_) (Eventually.of_forall fun w => ?_)
  · have hc : Continuous fun p : (Fin n → ℝ) × ℝ => cutK r k p.2 * φ p.1 p.2 :=
      ((continuous_cutK r k).comp continuous_snd).mul hφ
    exact (hc.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))
      ).aestronglyMeasurable
  · filter_upwards [ae_sphereMeasure n] with w hw
    rw [Real.norm_eq_abs]
    refine abs_integral_cutK_le hr k fun ρ hρ => ?_
    have hmem : c + ρ • w ∈ closedBall c r :=
      mem_closedBall_of_sqDist_le hr.le (by rw [sqDist_add_smul c w ρ hw]; nlinarith [hρ.1, hρ.2])
    have hBw := hB _ hmem
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)] at hBw
    have hw1 : ∀ i, |w i| ≤ 1 := fun i => by
      have : w i ^ 2 ≤ 1 := hw ▸ Finset.single_le_sum (f := fun i => w i ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    show |ρ ^ (n - 1) * ∑ i, w i * X i (c + ρ • w)| ≤ r ^ (n - 1) * B
    rw [abs_mul, abs_of_nonneg (pow_nonneg hρ.1 _)]
    refine mul_le_mul (pow_le_pow_left₀ hρ.1 hρ.2 _) ?_ (abs_nonneg _) (pow_nonneg hr.le _)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_ hBw)
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hw1 i)
  · exact tendsto_integral_cutK hr (φ := fun ρ => φ w ρ)
      (hφ.comp (continuous_const.prodMk continuous_id)).continuousOn

/-- Step 4 (the volume side): `∫ χ_k D → ∫_{B_r(c)} D` for continuous `D`. -/
theorem tendsto_ball_side (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {D : (Fin n → ℝ) → ℝ}
    (hD : Continuous D) :
    Tendsto (fun k : ℕ => ∫ x, ballCut c r k x * D x) atTop (𝓝 (∫ x in euclBall c r, D x)) := by
  rw [← integral_indicator (measurableSet_euclBall c r)]
  have hbd : Integrable ((closedBall c r).indicator fun x => |D x|) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (hD.abs.continuousOn.integrableOn_compact (isCompact_closedBall c r))
  refine tendsto_integral_of_dominated_convergence _ (fun k => ?_) hbd (fun k => ?_)
    (Eventually.of_forall fun x => ?_)
  · exact ((contDiff_ballCut c r k).continuous.mul hD).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ballCut_nonneg c r k x)]
    by_cases hx : x ∈ closedBall c r
    · rw [indicator_of_mem hx]
      exact mul_le_of_le_one_left (abs_nonneg _) (ballCut_le_one c r k x)
    · rw [indicator_of_notMem hx, ballCut_eq_zero hr k (eq_zero_of_not_mem_closedBall hr hx),
        zero_mul]
  · have := (tendsto_ballCut c hr x).mul_const (D x)
    convert this using 2
    by_cases hx : x ∈ euclBall c r
    · simp [indicator_of_mem hx]
    · simp [indicator_of_notMem hx]

/-- **The divergence theorem on a Euclidean ball.**  For a `C¹` vector field `X` on `ℝⁿ`
(`n ≥ 1`) and a ball `B_r(c)`,
`∫_{B_r(c)} div X = r^{n-1} ∫_{S^{n-1}} ⟨X(c + rω), ω⟩ dσ(ω)`
(`σ = sphereMeasure n`; `r^{n-1} dσ` is the surface measure of `∂B_r(c)` and `ω` its outer unit
normal). -/
theorem divergence_ball (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (X : Fin n → (Fin n → ℝ) → ℝ) (hX : ∀ i, ContDiff ℝ 1 (X i)) :
    ∫ x in euclBall c r, ∑ i, pd (X i) i x =
      r ^ (n - 1) * ∫ w, ∑ i, X i (c + r • w) * w i ∂(sphereMeasure n) := by
  have hXc : ∀ i, Continuous (X i) := fun i => (hX i).continuous
  have hD : Continuous fun x => ∑ i, pd (X i) i x :=
    continuous_finset_sum _ fun i _ => continuous_pd (hX i) i
  have hL := tendsto_ball_side c hr hD
  have hR := tendsto_sphere_side c hr X hXc
  have heq : (fun k : ℕ => ∫ x, ballCut c r k x * ∑ i, pd (X i) i x) =
      fun k : ℕ => ∫ w, (∫ ρ in Ioi (0 : ℝ),
        cutK r k ρ * (ρ ^ (n - 1) * ∑ i, w i * X i (c + ρ • w))) ∂(sphereMeasure n) := by
    funext k
    rw [integral_ballCut_mul_div c hr X hX k, integral_cutGrad_polar c hr X hXc k]
  rw [heq] at hL
  rw [tendsto_nhds_unique hL hR, ← integral_const_mul]
  congr 1; funext w
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _


/-! ### Integration by parts on balls -/

theorem continuous_sphereEmb (n : ℕ) : Continuous (sphereEmb n) :=
  (PiLp.continuous_ofLp 2 _).comp continuous_subtype_val

/-- Continuous functions are `σ`-integrable. -/
theorem integrable_sphereMeasure {F : Type*} [NormedAddCommGroup F] {g : (Fin n → ℝ) → F}
    (hg : Continuous g) : Integrable g (sphereMeasure n) := by
  unfold sphereMeasure
  rw [(measurableEmbedding_sphereEmb n).integrable_map_iff]
  exact (hg.comp (continuous_sphereEmb n)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integrableOn_euclBall {c : Fin n → ℝ} {r : ℝ} (hr : 0 ≤ r) {F : Type*}
    [NormedAddCommGroup F] {g : (Fin n → ℝ) → F} (hg : Continuous g) :
    IntegrableOn g (euclBall c r) :=
  (hg.continuousOn.integrableOn_compact (isCompact_closedBall c r)).mono_set
    (euclBall_subset_closedBall c hr)

theorem pd_zero_fun (i : Fin n) (x : Fin n → ℝ) : pd (fun _ : Fin n → ℝ => (0 : ℝ)) i x = 0 := by
  simp [pd]

/-- **Gauss–Green on a ball** (one partial derivative):
`∫_{B_r(c)} ∂_i f = r^{n-1} ∫_{S^{n-1}} f(c + rω) ω_i dσ(ω)` for real `C¹` functions `f`. -/
theorem integral_pd_ball (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin n) :
    ∫ x in euclBall c r, pd f i x = r ^ (n - 1) * ∫ w, f (c + r • w) * w i ∂(sphereMeasure n) := by
  set X : Fin n → (Fin n → ℝ) → ℝ := fun j => if j = i then f else fun _ => 0
  have hX : ∀ j, ContDiff ℝ 1 (X j) := fun j => by
    by_cases h : j = i
    · simp only [X, h, if_true]; exact hf
    · simp only [X, h, if_false]; exact contDiff_const
  have h := divergence_ball c hr X hX
  have e1 : ∀ x, ∑ j, pd (X j) j x = pd f i x := fun x => by
    rw [Finset.sum_eq_single i]
    · simp [X]
    · intro j _ hj; simp only [X, hj, if_false]; exact pd_zero_fun j x
    · simp
  have e2 : ∀ w : Fin n → ℝ, ∑ j, X j (c + r • w) * w j = f (c + r • w) * w i := fun w => by
    rw [Finset.sum_eq_single i]
    · simp [X]
    · intro j _ hj; simp [X, hj]
    · simp
  simp only [e1, e2] at h
  exact h

/-- **Integration by parts on a ball**:
`∫_{B_r(c)} u ∂_i v = r^{n-1} ∫_{S^{n-1}} u v ω_i dσ - ∫_{B_r(c)} ∂_i u · v` (real `C¹`). -/
theorem integral_mul_pd_ball (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {u v : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (i : Fin n) :
    ∫ x in euclBall c r, u x * pd v i x =
      r ^ (n - 1) * ∫ w, u (c + r • w) * v (c + r • w) * w i ∂(sphereMeasure n) -
        ∫ x in euclBall c r, pd u i x * v x := by
  have h := integral_pd_ball c hr (hu.mul hv) i
  simp only [pd_mul hu hv i] at h
  rw [integral_add (f := fun x => pd u i x * v x) (g := fun x => u x * pd v i x)
    (integrableOn_euclBall hr.le ((continuous_pd hu i).mul hv.continuous))
    (integrableOn_euclBall hr.le (hu.continuous.mul (continuous_pd hv i)))] at h
  linarith

/-- **Green's first identity on a ball**: for `C¹` `u` and `C²` `v`,
`∫_{B} u Δv + ∫_{B} ∇u·∇v = r^{n-1} ∫_{S^{n-1}} u ∂_ν v dσ`. -/
theorem green_first_ball (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {u v : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v) :
    (∫ x in euclBall c r, u x * ∑ i, pd (pd v i) i x) +
        ∫ x in euclBall c r, ∑ i, pd u i x * pd v i x =
      r ^ (n - 1) * ∫ w, u (c + r • w) * ∑ i, pd v i (c + r • w) * w i ∂(sphereMeasure n) := by
  have hv1 : ∀ i, ContDiff ℝ 1 (pd v i) := fun i => by
    unfold pd
    exact (hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have h := fun i => integral_mul_pd_ball c hr hu (hv1 i) i
  have hs : ∫ x in euclBall c r, u x * ∑ i, pd (pd v i) i x =
      ∑ i, ∫ x in euclBall c r, u x * pd (pd v i) i x := by
    simp_rw [Finset.mul_sum]
    exact integral_finset_sum _ fun i _ =>
      integrableOn_euclBall hr.le (hu.continuous.mul (continuous_pd (hv1 i) i))
  have hs2 : ∫ x in euclBall c r, ∑ i, pd u i x * pd v i x =
      ∑ i, ∫ x in euclBall c r, pd u i x * pd v i x :=
    integral_finset_sum _ fun i _ =>
      integrableOn_euclBall hr.le ((continuous_pd hu i).mul (hv1 i).continuous)
  have hs3 : ∫ w, u (c + r • w) * ∑ i, pd v i (c + r • w) * w i ∂(sphereMeasure n) =
      ∑ i, ∫ w, u (c + r • w) * pd v i (c + r • w) * w i ∂(sphereMeasure n) := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    refine integral_finset_sum _ fun i _ => ?_
    have hu' := hu.continuous
    have hv' := (hv1 i).continuous
    exact integrable_sphereMeasure (by fun_prop)
  rw [hs, hs2, hs3, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h i]; ring

end RenewalGeometry.BallAnalysis
