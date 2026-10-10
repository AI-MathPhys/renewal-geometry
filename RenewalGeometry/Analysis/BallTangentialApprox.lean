/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallTangentialTrace

/-!
# Smooth tangential approximation of weakly tangential `H⁴` fields on a ball
  (stage D2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

A weakly tangential field `w ∈ H⁴(B)⁴` on `B = B_r(c) ⊂ ℝ⁴` is the `H¹(B)`-limit of **smooth
fields with vanishing normal component on the sphere** (boundary-layer correction):

* `etaC r ε s = θ((s - r²(1-ε))/(r²ε))/s` — a smooth cutoff of the shell `r²(1-ε) ≤ |x-c|² ≤ r²`
  with `etaC r ε r² = 1/r²` (`contDiff_etaC`, `etaC_eq_zero`, `etaC_sq`, bounds);
* `corr c r W ε ν x = etaC(|x-c|²) f(x) (x_ν - c_ν)`, `f = nrm c W` the normal component:
  `W - corr` is smooth and exactly tangential on the sphere (`tangent_sub_corr`);
* `abs_nrm_le_shell` — on the shell, `|f(x)| ≤ sup_{∂B}|f| + 4 L r ε` (mean value theorem along
  the radius, `L` a bound of `∇f` on `B`);
* `eLpNorm_le_shell` — functions supported in the shell and bounded there are small in `L²(B)`;
* `exists_tangential_approx` (**main result**): smooth tangential `W̃_m → w` in `H¹(B)`
  (values and gradients in `L²(B)`).  Proof: `H⁴(B)` approximants (`memHk_iff_exists_convHk`),
  uniform `C¹(B)` bounds (`bounds_of_convHk4`), the normal trace tends to zero uniformly
  (`normal_trace_le`), correction in a shell of width `ε_m → 0` with `sup_{∂B}|f_m| ≤ ε_m`.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis.TanApprox

open SobolevOpen BallReg BallAlg

set_option linter.unusedSectionVars false

/-! ### The boundary-layer cutoff -/

/-- `etaC r ε s = θ((s - r²(1-ε))/(r²ε)) / s` with `θ = smoothTransition`. -/
def etaC (r ε s : ℝ) : ℝ := Real.smoothTransition ((s - r ^ 2 * (1 - ε)) / (r ^ 2 * ε)) / s

theorem etaC_eq_zero {r ε s : ℝ} (hr : 0 < r) (hε : 0 < ε) (hs : s ≤ r ^ 2 * (1 - ε)) :
    etaC r ε s = 0 := by
  unfold etaC
  rw [Real.smoothTransition.zero_of_nonpos, zero_div]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem etaC_sq {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) : etaC r ε (r ^ 2) = 1 / r ^ 2 := by
  unfold etaC
  rw [Real.smoothTransition.one_of_one_le]
  rw [le_div_iff₀ (by positivity)]; linarith

theorem contDiff_etaC {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε1 : ε < 1) :
    ContDiff ℝ ∞ (etaC r ε) := by
  have ha : 0 < r ^ 2 * (1 - ε) := mul_pos (by positivity) (by linarith)
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s < r ^ 2 * (1 - ε)
  · have : etaC r ε =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hs] with t ht
      exact etaC_eq_zero hr hε (le_of_lt ht)
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have hs0 : s ≠ 0 := by
      have : r ^ 2 * (1 - ε) ≤ s := not_lt.mp hs
      exact (lt_of_lt_of_le ha this).ne'
    unfold etaC
    have h1 : ContDiff ℝ ∞ fun s : ℝ => Real.smoothTransition ((s - r ^ 2 * (1 - ε)) / (r ^ 2 * ε)) :=
      Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
    exact h1.contDiffAt.div contDiffAt_id hs0

theorem exists_bound_deriv_smoothTransition :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |deriv Real.smoothTransition t| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    continuous_deriv_smoothTransition.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact (Real.norm_eq_abs _ ▸ hM t ht).trans (le_max_left _ _)
  · rw [deriv_smoothTransition_eq_zero]
    · simp
    · simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with h | h
      · exact Or.inl h.le
      · exact Or.inr h.le

theorem hasDerivAt_etaC {r ε s : ℝ} (hs : 0 < s) :
    HasDerivAt (etaC r ε)
      ((deriv Real.smoothTransition ((s - r ^ 2 * (1 - ε)) / (r ^ 2 * ε)) * (1 / (r ^ 2 * ε)) * s -
        Real.smoothTransition ((s - r ^ 2 * (1 - ε)) / (r ^ 2 * ε)) * 1) / s ^ 2) s := by
  have h1 : HasDerivAt (fun s : ℝ => (s - r ^ 2 * (1 - ε)) / (r ^ 2 * ε)) (1 / (r ^ 2 * ε)) s :=
    ((hasDerivAt_id s).sub_const _).div_const _
  have h2 := (Real.smoothTransition.contDiff (n := 1).differentiable one_ne_zero _).hasDerivAt.comp
    s h1
  exact h2.div (hasDerivAt_id s) hs.ne'

/-- Bounds of the cutoff and its derivative on `s ≥ r²(1-ε)`, `0 < ε ≤ 1/2`. -/
theorem etaC_bounds {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {Mst : ℝ}
    (hMst : ∀ t, |deriv Real.smoothTransition t| ≤ Mst) {s : ℝ} (hs : r ^ 2 * (1 - ε) ≤ s) :
    |etaC r ε s| ≤ 2 / r ^ 2 ∧ |deriv (etaC r ε) s| ≤ 2 * Mst / (r ^ 4 * ε) + 4 / r ^ 4 := by
  have hr2 : 0 < r ^ 2 := by positivity
  have ha : r ^ 2 / 2 ≤ s := by nlinarith
  have hs0 : 0 < s := by linarith
  have hMst0 : 0 ≤ Mst := (abs_nonneg _).trans (hMst 0)
  set t := (s - r ^ 2 * (1 - ε)) / (r ^ 2 * ε)
  have hst0 := Real.smoothTransition.nonneg t
  have hst1 := Real.smoothTransition.le_one t
  have hinv : 1 / s ≤ 2 / r ^ 2 := by
    rw [div_le_div_iff₀ hs0 hr2]; linarith
  constructor
  · unfold etaC
    rw [abs_div, abs_of_nonneg hst0, abs_of_pos hs0]
    calc Real.smoothTransition t / s ≤ 1 / s := by gcongr
      _ ≤ 2 / r ^ 2 := hinv
  · rw [(hasDerivAt_etaC hs0).deriv]
    have hD := hMst t
    have e : (deriv Real.smoothTransition t * (1 / (r ^ 2 * ε)) * s -
        Real.smoothTransition t * 1) / s ^ 2 =
        deriv Real.smoothTransition t / (r ^ 2 * ε) / s - Real.smoothTransition t / s ^ 2 := by
      field_simp
    rw [e]
    refine (abs_sub _ _).trans ?_
    have h1 : |deriv Real.smoothTransition t / (r ^ 2 * ε) / s| ≤ 2 * Mst / (r ^ 4 * ε) := by
      rw [abs_div, abs_div, abs_of_pos (by positivity : 0 < r ^ 2 * ε), abs_of_pos hs0]
      calc |deriv Real.smoothTransition t| / (r ^ 2 * ε) / s
          ≤ Mst / (r ^ 2 * ε) / (r ^ 2 / 2) := by gcongr
        _ = 2 * Mst / (r ^ 4 * ε) := by field_simp <;> ring
    have h2 : |Real.smoothTransition t / s ^ 2| ≤ 4 / r ^ 4 := by
      rw [abs_div, abs_of_nonneg hst0, abs_of_pos (by positivity : 0 < s ^ 2)]
      calc Real.smoothTransition t / s ^ 2 ≤ 1 / (r ^ 2 / 2) ^ 2 := by
            gcongr
        _ = 4 / r ^ 4 := by field_simp <;> ring
    linarith

/-! ### The correction -/

variable (c : Fin 4 → ℝ) (r : ℝ)

/-- The boundary-layer correction `etaC(|x-c|²) f(x) (x_ν - c_ν)`, `f = nrm c W`. -/
def corr (W : Fin 4 → (Fin 4 → ℝ) → ℝ) (ε : ℝ) (ν : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  etaC r ε (sqDist c x) * nrm c W x * (x ν - c ν)

theorem contDiff_corr {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {W : Fin 4 → (Fin 4 → ℝ) → ℝ} (hW : ∀ ν, ContDiff ℝ ∞ (W ν)) (ν : Fin 4) :
    ContDiff ℝ ∞ (corr c r W ε ν) := by
  unfold corr
  exact (((contDiff_etaC hr hε hε1).comp (contDiff_sqDist c)).mul (contDiff_nrm c hW)).mul
    ((contDiff_apply ℝ ℝ ν).sub contDiff_const)

/-- **The corrected field is tangential on the sphere.** -/
theorem tangent_sub_corr {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε)
    (W : Fin 4 → (Fin 4 → ℝ) → ℝ) {y : Fin 4 → ℝ} (hy : sqDist c y = r ^ 2) :
    ∑ ν, (y ν - c ν) * (W ν y - corr c r W ε ν y) = 0 := by
  have h1 : ∀ ν, (y ν - c ν) * (W ν y - corr c r W ε ν y) =
      (y ν - c ν) * W ν y - etaC r ε (sqDist c y) * nrm c W y * (y ν - c ν) ^ 2 := fun ν => by
    simp only [corr]; ring
  rw [Finset.sum_congr rfl fun ν _ => h1 ν, Finset.sum_sub_distrib, ← Finset.mul_sum,
    show ∑ ν, (y ν - c ν) * W ν y = nrm c W y from rfl,
    show ∑ ν, (y ν - c ν) ^ 2 = sqDist c y from rfl, hy, etaC_sq hr hε]
  field_simp
  ring

theorem corr_eq_zero {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) (W : Fin 4 → (Fin 4 → ℝ) → ℝ)
    (ν : Fin 4) {x : Fin 4 → ℝ} (hx : sqDist c x ≤ r ^ 2 * (1 - ε)) : corr c r W ε ν x = 0 := by
  simp [corr, etaC_eq_zero hr hε hx]

/-- The shell `{r²(1-ε) ≤ |x - c|²}`. -/
def shell (ε : ℝ) : Set (Fin 4 → ℝ) := {x | r ^ 2 * (1 - ε) ≤ sqDist c x}

theorem measurableSet_shell (ε : ℝ) : MeasurableSet (shell c r ε) :=
  measurableSet_le measurable_const (contDiff_sqDist c (k := 0)).continuous.measurable

theorem support_corr_subset {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε)
    (W : Fin 4 → (Fin 4 → ℝ) → ℝ) (ν : Fin 4) :
    Function.support (corr c r W ε ν) ⊆ shell c r ε := by
  intro x hx
  by_contra h
  exact hx (corr_eq_zero c hr hε W ν (le_of_lt (not_le.mp h)))

theorem support_pd_corr_subset {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε)
    (W : Fin 4 → (Fin 4 → ℝ) → ℝ) (ν μ : Fin 4) :
    Function.support (pd (corr c r W ε ν) μ) ⊆ shell c r ε := by
  intro x hx
  by_contra h
  apply hx
  have hlt : sqDist c x < r ^ 2 * (1 - ε) := not_le.mp h
  have hev : corr c r W ε ν =ᶠ[𝓝 x] fun _ => 0 := by
    have ho : IsOpen {y : Fin 4 → ℝ | sqDist c y < r ^ 2 * (1 - ε)} :=
      isOpen_lt (contDiff_sqDist c (k := 0)).continuous continuous_const
    filter_upwards [ho.mem_nhds hlt] with y hy
    exact corr_eq_zero c hr hε W ν (le_of_lt hy)
  unfold pd
  rw [hev.fderiv_eq]
  simp

/-- The partial derivatives of the correction. -/
theorem pd_corr {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {W : Fin 4 → (Fin 4 → ℝ) → ℝ} (hW : ∀ ν, ContDiff ℝ ∞ (W ν)) (ν μ : Fin 4)
    (x : Fin 4 → ℝ) :
    pd (corr c r W ε ν) μ x =
      deriv (etaC r ε) (sqDist c x) * (2 * (x μ - c μ)) * nrm c W x * (x ν - c ν) +
        etaC r ε (sqDist c x) * pd (nrm c W) μ x * (x ν - c ν) +
          etaC r ε (sqDist c x) * nrm c W x * (if ν = μ then 1 else 0) := by
  have he := contDiff_etaC hr hε hε1
  have hd1 : DifferentiableAt ℝ (fun y => etaC r ε (sqDist c y)) x :=
    ((he.comp (contDiff_sqDist c)).differentiable (by simp)) x
  have hd2 : DifferentiableAt ℝ (nrm c W) x := ((contDiff_nrm c hW).differentiable (by simp)) x
  have hd3 : DifferentiableAt ℝ (fun y : Fin 4 → ℝ => y ν - c ν) x :=
    (hasFDerivAt_apply ν x).differentiableAt.sub_const (c ν)
  have hd12 : DifferentiableAt ℝ (fun y => etaC r ε (sqDist c y) * nrm c W y) x := hd1.mul hd2
  show pd (fun y => (etaC r ε (sqDist c y) * nrm c W y) * (y ν - c ν)) μ x = _
  rw [pd_mul_real hd12 hd3, pd_mul_real hd1 hd2, pd_coord_sub,
    pd_comp_real ((he.differentiable (by simp)) _) ((contDiff_sqDist c (k := 1)).differentiable
      one_ne_zero x),
    pd_sqDist]
  ring

/-! ### The mean value estimate in the shell -/

/-- **The normal component in the shell**: if `|∂_i f| ≤ L` on `B` and `|f| ≤ δ` on the sphere,
then `|f(x)| ≤ δ + 4 L r ε` for `x ∈ B` with `|x - c|² ≥ r²(1 - ε)`, `0 ≤ ε ≤ 1`. -/
theorem abs_le_shell {r : ℝ} (hr : 0 < r) {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {L δ ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε < 1) (hL : ∀ z ∈ euclBall c r, ∀ i, |pd f i z| ≤ L)
    (hδ : ∀ y, sqDist c y = r ^ 2 → |f y| ≤ δ) {x : Fin 4 → ℝ} (hx : x ∈ euclBall c r)
    (hxs : r ^ 2 * (1 - ε) ≤ sqDist c x) : |f x| ≤ δ + 4 * L * r * ε := by
  have hxB : sqDist c x < r ^ 2 := hx
  have hq0 : 0 ≤ sqDist c x := Finset.sum_nonneg fun i _ => sq_nonneg _
  set ρ := Real.sqrt (sqDist c x)
  have hρ2 : ρ ^ 2 = sqDist c x := Real.sq_sqrt hq0
  have hρr : ρ < r := by
    rw [← Real.sqrt_sq hr.le]; exact Real.sqrt_lt_sqrt hq0 hxB
  have hL0 : 0 ≤ L := by
    have := hL x hx 0
    exact (abs_nonneg _).trans this
  have hρpos : 0 < ρ := by
    apply Real.sqrt_pos.mpr
    have : 0 < r ^ 2 * (1 - ε) := mul_pos (by positivity) (by linarith)
    linarith
  · have hρpos := hρpos
    set y : Fin 4 → ℝ := c + (r / ρ) • (x - c)
    have hy : sqDist c y = r ^ 2 := by
      rw [show y = c + (r / ρ) • (x - c) from rfl, sqDist_line, ← hρ2]
      field_simp
    have hseg : ∀ t ∈ Ico (0 : ℝ) 1, seg y x t ∈ euclBall c r := by
      intro t ht
      show sqDist c (seg y x t) < r ^ 2
      have e : seg y x t = c + (1 + t * (r / ρ - 1)) • (x - c) := by
        funext i; simp only [seg, y, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
      rw [e, sqDist_line, ← hρ2]
      have hq : 0 < r / ρ - 1 := by rw [sub_pos, one_lt_div hρpos]; exact hρr
      have hlam : (1 + t * (r / ρ - 1)) * ρ < r := by
        have : t * (r / ρ - 1) < r / ρ - 1 := by nlinarith [ht.2]
        have h2 : (1 + t * (r / ρ - 1)) < r / ρ := by linarith
        calc (1 + t * (r / ρ - 1)) * ρ < r / ρ * ρ := by gcongr
          _ = r := by field_simp
      have hlam0 : 0 ≤ (1 + t * (r / ρ - 1)) * ρ := by
        have : 0 ≤ t * (r / ρ - 1) := mul_nonneg ht.1 hq.le
        positivity
      nlinarith
    have hyx : ∀ i, |y i - x i| ≤ r - ρ := by
      intro i
      have e : y i - x i = (r / ρ - 1) * (x i - c i) := by
        simp only [y, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
      rw [e, abs_mul, abs_of_pos (by rw [sub_pos, one_lt_div hρpos]; exact hρr)]
      have hxi : |x i - c i| ≤ ρ := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => (x i - c i) ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
      calc (r / ρ - 1) * |x i - c i| ≤ (r / ρ - 1) * ρ := by
            gcongr; rw [sub_nonneg, le_div_iff₀ hρpos, one_mul]; exact hρr.le
        _ = r - ρ := by field_simp
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun t => f (seg y x t))
      (C := 4 * L * (r - ρ)) (fun t _ => (hasDerivAt_comp_seg hf y x t).hasDerivWithinAt)
      (fun t ht => by
        rw [Real.norm_eq_abs]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i, |(y i - x i) * pd f i (seg y x t)| ≤ ∑ _i : Fin 4, (r - ρ) * L := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [abs_mul]
              exact mul_le_mul (hyx i) (hL _ (hseg t ht) i) (abs_nonneg _) (by linarith)
          _ = 4 * L * (r - ρ) := by simp; ring)
    simp only [seg, one_smul, zero_smul, add_zero, add_sub_cancel] at hmv
    rw [Real.norm_eq_abs] at hmv
    -- `r - ρ ≤ r ε`
    have hrρ : r - ρ ≤ r * ε := by
      have h2 : (r * (1 - ε)) ^ 2 ≤ sqDist c x := by
        calc (r * (1 - ε)) ^ 2 = r ^ 2 * (1 - ε) * (1 - ε) := by ring
          _ ≤ r ^ 2 * (1 - ε) * 1 := by
              apply mul_le_mul_of_nonneg_left (by linarith)
              exact mul_nonneg (by positivity) (by linarith)
          _ ≤ sqDist c x := by linarith
      have h1 : r * (1 - ε) ≤ ρ := by
        have := Real.sqrt_le_sqrt h2
        rwa [Real.sqrt_sq (mul_nonneg hr.le (by linarith))] at this
      linarith
    have h1 := hδ y hy
    have h3 : |f x| ≤ |f y| + |f y - f x| := by
      have := abs_sub_abs_le_abs_sub (f x) (f y)
      linarith [abs_sub_comm (f x) (f y)]
    have h4 : 4 * L * (r - ρ) ≤ 4 * L * r * ε := by nlinarith
    linarith

/-! ### Smallness in `L²` of functions supported in thin shells -/

/-- The measure of the part of the ball in the shell tends to zero with the width. -/
theorem tendsto_volume_shell {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ε => volume (euclBall c r ∩ shell c r ε)) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_measure_biInter_gt (μ := volume) (s := fun ε => euclBall c r ∩ shell c r ε)
    (a := (0 : ℝ)) (fun ε _ => ((measurableSet_euclBall c r).inter (measurableSet_shell c r ε)).nullMeasurableSet)
    (fun i j _ hij x hx => ⟨hx.1, by
      have := hx.2; simp only [shell, mem_setOf_eq] at this ⊢
      have hr2 : 0 ≤ r ^ 2 := by positivity
      nlinarith⟩)
    ⟨1, one_pos, ((measure_mono (inter_subset_left.trans
      (euclBall_subset_closedBall c hr.le))).trans_lt (isCompact_closedBall c r).measure_lt_top).ne⟩
  have hempty : (⋂ ε > (0 : ℝ), euclBall c r ∩ shell c r ε) = ∅ := by
    ext x
    simp only [mem_iInter, mem_inter_iff, mem_empty_iff_false, iff_false, not_forall]
    by_cases hx : x ∈ euclBall c r
    · have hxB : sqDist c x < r ^ 2 := hx
      have hr2 : 0 < r ^ 2 := by positivity
      refine ⟨(r ^ 2 - sqDist c x) / (2 * r ^ 2), by
        have : 0 < r ^ 2 - sqDist c x := by linarith
        positivity, fun h => ?_⟩
      have h2 := h.2
      simp only [shell, mem_setOf_eq] at h2
      have : r ^ 2 * (1 - (r ^ 2 - sqDist c x) / (2 * r ^ 2)) = r ^ 2 / 2 + sqDist c x / 2 := by
        field_simp; ring
      rw [this] at h2
      linarith
    · exact ⟨1, one_pos, fun h => hx h.1⟩
  rw [hempty, measure_empty] at h
  exact h

/-- A function supported in the shell and bounded by `Q` on the ball has
`‖g‖_{L²(B)} ≤ Q |B ∩ shell|^{1/2}`. -/
theorem eLpNorm_le_shell {g : (Fin 4 → ℝ) → ℝ} {ε Q : ℝ}
    (hsupp : Function.support g ⊆ shell c r ε)
    (hQ : ∀ x ∈ euclBall c r, x ∈ shell c r ε → |g x| ≤ Q) :
    eLpNorm g 2 (volume.restrict (euclBall c r)) ≤
      volume (euclBall c r ∩ shell c r ε) ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal Q := by
  rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
  refine (eLpNorm_le_of_ae_bound (C := Q) ?_).trans (le_of_eq ?_)
  · rw [ae_restrict_iff' (measurableSet_shell c r ε), ae_restrict_iff' (measurableSet_euclBall c r)]
    exact Eventually.of_forall fun x hxB hxs => by rw [Real.norm_eq_abs]; exact hQ x hxB hxs
  · rw [Measure.restrict_apply_univ, Measure.restrict_apply (measurableSet_shell c r ε),
      inter_comm]


/-! ### The main approximation theorem -/

theorem pd_nrm {W : Fin 4 → (Fin 4 → ℝ) → ℝ} (hW : ∀ ν, ContDiff ℝ 1 (W ν)) (i : Fin 4)
    (z : Fin 4 → ℝ) :
    pd (nrm c W) i z = ∑ ν, ((if ν = i then 1 else 0) * W ν z + (z ν - c ν) * pd (W ν) i z) := by
  have hd : ∀ ν, DifferentiableAt ℝ (fun y : Fin 4 → ℝ => (y ν - c ν) * W ν y) z := fun ν =>
    ((hasFDerivAt_apply ν z).differentiableAt.sub_const (c ν)).mul
      (((hW ν).differentiable one_ne_zero) z)
  show pd (fun y => ∑ ν, (y ν - c ν) * W ν y) i z = _
  rw [pd_sum_real fun ν _ => hd ν]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [pd_mul_real ((hasFDerivAt_apply ν z).differentiableAt.sub_const (c ν))
    (((hW ν).differentiable one_ne_zero) z), pd_coord_sub]

/-- **Smooth tangential approximation of weakly tangential `H⁴(B)` fields**: if `w ∈ H⁴(B)⁴` with
weak gradients `gw` is weakly tangential on `B = B_r(c)`, there are smooth fields `W̃_k` with
vanishing normal component on the sphere `∂B_r(c)` converging to `w` in `H¹(B)`. -/
theorem exists_tangential_approx {r : ℝ} (hr : 0 < r) {w : Fin 4 → (Fin 4 → ℝ) → ℝ}
    {gw : Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℝ}
    (hw : ∀ ν, MemHk (euclBall c r) 4 (w ν))
    (hgw : ∀ ν μ, HasWeakPartialR (euclBall c r) μ (w ν) (gw ν μ))
    (hgm : ∀ ν μ, MemLp (gw ν μ) 2 (volume.restrict (euclBall c r)))
    (htan : IsWeakTangential c r w (fun x => ∑ ν, gw ν ν x)) :
    ∃ Wt : ℕ → Fin 4 → (Fin 4 → ℝ) → ℝ, (∀ k ν, ContDiff ℝ ∞ (Wt k ν)) ∧
      (∀ k y, sqDist c y = r ^ 2 → ∑ ν, (y ν - c ν) * Wt k ν y = 0) ∧
      (∀ ν, Tendsto (fun k => eLpNorm (Wt k ν - w ν) 2 (volume.restrict (euclBall c r)))
        atTop (𝓝 0)) ∧
      (∀ ν μ, Tendsto (fun k => eLpNorm (pd (Wt k ν) μ - gw ν μ) 2
        (volume.restrict (euclBall c r))) atTop (𝓝 0)) := by
  haveI : Fact (0 < r) := ⟨hr⟩
  set ρ := volume.restrict (euclBall c r)
  choose φ hφ hcv using fun ν => (memHk_iff_exists_convHk c r 4).mp (hw ν)
  set W : ℕ → Fin 4 → (Fin 4 → ℝ) → ℝ := fun m ν => φ ν m
  have hW : ∀ m ν, ContDiff ℝ ∞ (W m ν) := fun m ν => hφ ν m
  have hW1 : ∀ m ν, ContDiff ℝ 1 (W m ν) := fun m ν => (hW m ν).of_le (by simp)
  have hL2 : ∀ ν, Tendsto (fun m => eLpNorm (W m ν - w ν) 2 ρ) atTop (𝓝 0) := fun ν =>
    (hcv ν).1.2
  have hD : ∀ ν μ, Tendsto (fun m => eLpNorm (pd (W m ν) μ - gw ν μ) 2 ρ) atTop (𝓝 0) := by
    intro ν μ
    obtain ⟨g', hg'⟩ := (hcv ν).2 μ
    have hb := hg'.base
    have hw' := hasWeakPartialR_of_conv (isBounded_euclBall' c r) (measurableSet_euclBall c r)
      (hφ ν) (hcv ν).1.1 hb.1 (hcv ν).1.2 hb.2
    have e : g' =ᵐ[ρ] gw ν μ := by
      have := weakR_ae_eq (isOpen_euclBall c r) hw' (hgw ν μ) hb.1 (hgm ν μ)
      rw [EventuallyEq, ae_restrict_iff' (measurableSet_euclBall c r)]; exact this
    exact hb.2.congr fun m => eLpNorm_congr_ae (EventuallyEq.rfl.sub e)
  -- uniform bounds
  choose N e M he he0 hM0 hbd using fun ν => bounds_of_convHk4 c hr (hφ ν) (hcv ν)
  set N0 : ℕ := ∑ ν, N ν
  have hN0 : ∀ ν, N ν ≤ N0 := fun ν =>
    Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ν)
  set E : ℕ → ℝ := fun m => ∑ ν, e ν m
  set MM : ℝ := ∑ ν, M ν
  have hE : Tendsto E atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun ν _ => he ν
  have hE0 : ∀ m, 0 ≤ E m := fun m => Finset.sum_nonneg fun ν _ => he0 ν m
  have hMM0 : 0 ≤ MM := Finset.sum_nonneg fun ν _ => hM0 ν
  have hle : ∀ ν m, e ν m ≤ E m := fun ν m =>
    Finset.single_le_sum (f := fun ν => e ν m) (fun ν _ => he0 ν m) (Finset.mem_univ ν)
  have hMle : ∀ ν, M ν ≤ MM := fun ν =>
    Finset.single_le_sum (f := M) (fun ν _ => hM0 ν) (Finset.mem_univ ν)
  have hcau : ∀ m ≥ N0, ∀ p ≥ N0, ∀ x ∈ euclBall c r, ∀ ν, |W m ν x - W p ν x| ≤ E m + E p := by
    intro m hm p hp x hx ν
    have := ((hbd ν m ((hN0 ν).trans hm) x hx).1 p ((hN0 ν).trans hp))
    exact this.trans (add_le_add (hle ν m) (hle ν p))
  have hWb : ∀ m ≥ N0, ∀ x ∈ euclBall c r, ∀ ν, |W m ν x| ≤ MM ∧ ∀ i, |pd (W m ν) i x| ≤ MM := by
    intro m hm x hx ν
    obtain ⟨-, h1, h2⟩ := hbd ν m ((hN0 ν).trans hm) x hx
    exact ⟨h1.trans (hMle ν), fun i => (h2 i).trans (hMle ν)⟩
  -- the normal trace
  have htr := normal_trace_le c r hW (fun ν => (hw ν).memLp) hgm hL2 hD htan hE hcau
  -- gradient bound of the normal component
  set L : ℝ := 4 * (MM + r * MM)
  have hL0 : 0 ≤ L := by positivity
  have hLb : ∀ m ≥ N0, ∀ z ∈ euclBall c r, ∀ i, |pd (nrm c (W m)) i z| ≤ L := by
    intro m hm z hz i
    rw [pd_nrm c (hW1 m) i z]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ ν, |(if ν = i then (1 : ℝ) else 0) * W m ν z + (z ν - c ν) * pd (W m ν) i z|
        ≤ ∑ _ν : Fin 4, (MM + r * MM) := by
          refine Finset.sum_le_sum fun ν _ => (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul]
            have h1 : |(if ν = i then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
            calc |(if ν = i then (1 : ℝ) else 0)| * |W m ν z| ≤ 1 * MM :=
                  mul_le_mul h1 (hWb m hm z hz ν).1 (abs_nonneg _) zero_le_one
              _ = MM := one_mul _
          · rw [abs_mul]
            exact mul_le_mul (abs_sub_le_of_sqDist_le c (le_of_lt hz) hr.le ν)
              ((hWb m hm z hz ν).2 i) (abs_nonneg _) hr.le
      _ = L := by simp [L]; ring
  -- the widths
  set δ : ℕ → ℝ := fun m => 4 * r * E m
  have hδ : Tendsto δ atTop (𝓝 0) := by simpa [δ] using hE.const_mul (4 * r)
  have hδ0 : ∀ m, 0 ≤ δ m := fun m => by have := hE0 m; positivity
  set ε : ℕ → ℝ := fun m => min (1 / 2) (max (δ m) (1 / ((m : ℝ) + 2)))
  have hε0 : ∀ m, 0 < ε m := fun m => lt_min (by norm_num) (lt_max_of_lt_right (by positivity))
  have hε2 : ∀ m, ε m ≤ 1 / 2 := fun m => min_le_left _ _
  have hε1 : ∀ m, ε m < 1 := fun m => (hε2 m).trans_lt (by norm_num)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 2)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      refine squeeze_zero (fun m => by positivity) (fun m => ?_) this
      gcongr; linarith
    have h2 : Tendsto (fun m => max (δ m) (1 / ((m : ℝ) + 2))) atTop (𝓝 (max 0 0)) :=
      hδ.max h1
    rw [max_self] at h2
    have h3 := (tendsto_const_nhds (x := (1 / 2 : ℝ))).min h2
    rwa [min_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h3
  have hεW : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hεlim, Eventually.of_forall hε0⟩
  have hδε : ∀ᶠ m in atTop, δ m ≤ ε m := by
    filter_upwards [hδ.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with m hm
    exact le_min hm (le_max_left _ _)
  -- the constants
  obtain ⟨Mst, hMst0, hMst⟩ := exists_bound_deriv_smoothTransition
  set A : ℝ := 1 + 4 * L * r
  have hA0 : 0 ≤ A := by positivity
  set Q0 : ℝ := A / r
  set Q1 : ℝ := (4 * Mst * A + 5 * A) / r ^ 2 + 2 * L / r
  -- the pointwise bound of the normal component in the shell
  have hnrm : ∀ m ≥ N0, δ m ≤ ε m → ∀ x ∈ euclBall c r, x ∈ shell c r (ε m) →
      |nrm c (W m) x| ≤ ε m * A := by
    intro m hm hδm x hx hxs
    have := abs_le_shell c hr ((contDiff_nrm c (hW m)).of_le (by simp)) (hε0 m).le (hε1 m)
      (hLb m hm) (htr m hm) hx hxs
    calc |nrm c (W m) x| ≤ δ m + 4 * L * r * ε m := this
      _ ≤ ε m + 4 * L * r * ε m := by gcongr
      _ = ε m * A := by ring
  have hvol : ∀ Q : ℝ, Tendsto (fun m => volume (euclBall c r ∩ shell c r (ε m)) ^
      (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal Q) atTop (𝓝 0) := by
    intro Q
    have h1 := (tendsto_volume_shell c hr).comp hεW
    have h2 : Tendsto (fun m => volume (euclBall c r ∩ shell c r (ε m)) ^ (2 : ℝ≥0∞).toReal⁻¹)
        atTop (𝓝 ((0 : ℝ≥0∞) ^ (2 : ℝ≥0∞).toReal⁻¹)) :=
      (ENNReal.continuous_rpow_const.tendsto 0).comp h1
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    have h3 := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal Q) h2 (Or.inr ENNReal.ofReal_ne_top)
    rwa [zero_mul] at h3
  -- the corrected fields
  refine ⟨fun m ν => W m ν - corr c r (W m) (ε m) ν, fun m ν =>
    (hW m ν).sub (contDiff_corr c hr (hε0 m) (hε1 m) (hW m) ν),
    fun m y hy => tangent_sub_corr c hr (hε0 m) (W m) hy, ?_, ?_⟩
  · intro ν
    have hc : Tendsto (fun m => eLpNorm (corr c r (W m) (ε m) ν) 2 ρ) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hvol Q0)
        (Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards [eventually_ge_atTop N0, hδε] with m hm hδm
      refine eLpNorm_le_shell c r (support_corr_subset c hr (hε0 m) (W m) ν) fun x hx hxs => ?_
      have h1 := hnrm m hm hδm x hx hxs
      have h2 := (etaC_bounds hr (hε0 m) (hε2 m) hMst hxs).1
      have h3 := abs_sub_le_of_sqDist_le c (le_of_lt hx) hr.le ν
      simp only [corr, abs_mul]
      calc |etaC r (ε m) (sqDist c x)| * |nrm c (W m) x| * |x ν - c ν|
          ≤ 2 / r ^ 2 * (1 / 2 * A) * r := by
            gcongr
            exact h1.trans (by gcongr; exact hε2 m)
        _ = Q0 := by simp only [Q0]; field_simp <;> ring
    have hsplit : ∀ m, eLpNorm ((fun x => W m ν x - corr c r (W m) (ε m) ν x) - w ν) 2 ρ ≤
        eLpNorm (W m ν - w ν) 2 ρ + eLpNorm (corr c r (W m) (ε m) ν) 2 ρ := by
      intro m
      have e1 : ((fun x => W m ν x - corr c r (W m) (ε m) ν x) - w ν) =
          (W m ν - w ν) - corr c r (W m) (ε m) ν := by funext x; simp; ring
      rw [e1]
      exact eLpNorm_sub_le ((hW m ν).continuous.aestronglyMeasurable.sub
        (hw ν).memLp.aestronglyMeasurable)
        (contDiff_corr c hr (hε0 m) (hε1 m) (hW m) ν).continuous.aestronglyMeasurable (by norm_num)
    have := (hL2 ν).add hc
    rw [add_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this
      (fun _ => bot_le) hsplit
  · intro ν μ
    have hc : Tendsto (fun m => eLpNorm (pd (corr c r (W m) (ε m) ν) μ) 2 ρ) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hvol Q1)
        (Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards [eventually_ge_atTop N0, hδε] with m hm hδm
      refine eLpNorm_le_shell c r (support_pd_corr_subset c hr (hε0 m) (W m) ν μ)
        fun x hx hxs => ?_
      have h1 := hnrm m hm hδm x hx hxs
      obtain ⟨h2, h2'⟩ := etaC_bounds hr (hε0 m) (hε2 m) hMst hxs
      have h3 := abs_sub_le_of_sqDist_le c (le_of_lt hx) hr.le ν
      have h3' := abs_sub_le_of_sqDist_le c (le_of_lt hx) hr.le μ
      have h4 := hLb m hm x hx μ
      have hεm := hε0 m
      rw [pd_corr c hr (hε0 m) (hε1 m) (hW m) ν μ x]
      have hδ1 : |(if ν = μ then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      have t1 : |deriv (etaC r (ε m)) (sqDist c x) * (2 * (x μ - c μ)) * nrm c (W m) x *
          (x ν - c ν)| ≤ (2 * Mst / (r ^ 4 * ε m) + 4 / r ^ 4) * (2 * r) * (ε m * A) * r := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]
        gcongr
      have t2 : |etaC r (ε m) (sqDist c x) * pd (nrm c (W m)) μ x * (x ν - c ν)| ≤
          2 / r ^ 2 * L * r := by
        rw [abs_mul, abs_mul]; gcongr
      have t3 : |etaC r (ε m) (sqDist c x) * nrm c (W m) x * (if ν = μ then (1 : ℝ) else 0)| ≤
          2 / r ^ 2 * (ε m * A) * 1 := by
        rw [abs_mul, abs_mul]; gcongr
      have e1 : (2 * Mst / (r ^ 4 * ε m) + 4 / r ^ 4) * (2 * r) * (ε m * A) * r =
          (4 * Mst * A + 8 * ε m * A) / r ^ 2 := by field_simp <;> ring
      have e2 : 2 / r ^ 2 * L * r = 2 * L / r := by field_simp <;> ring
      have t3' : 2 / r ^ 2 * (ε m * A) * 1 ≤ A / r ^ 2 := by
        have : ε m * A ≤ 1 / 2 * A := by gcongr; exact hε2 m
        calc 2 / r ^ 2 * (ε m * A) * 1 ≤ 2 / r ^ 2 * (1 / 2 * A) * 1 := by gcongr
          _ = A / r ^ 2 := by field_simp
      have t1' : (4 * Mst * A + 8 * ε m * A) / r ^ 2 ≤ (4 * Mst * A + 4 * A) / r ^ 2 := by
        have h8 : 8 * ε m * A ≤ 4 * A := by nlinarith [hε2 m, hA0, hε0 m]
        gcongr ?_ / _
        linarith
      rw [e1] at t1
      rw [e2] at t2
      calc _ ≤ _ := abs_add_three _ _ _
        _ ≤ (4 * Mst * A + 4 * A) / r ^ 2 + 2 * L / r + A / r ^ 2 := by linarith
        _ = Q1 := by simp only [Q1]; field_simp <;> ring
    have hsplit : ∀ m, eLpNorm (pd (fun x => W m ν x - corr c r (W m) (ε m) ν x) μ - gw ν μ) 2 ρ ≤
        eLpNorm (pd (W m ν) μ - gw ν μ) 2 ρ + eLpNorm (pd (corr c r (W m) (ε m) ν) μ) 2 ρ := by
      intro m
      have e1 : pd (fun x => W m ν x - corr c r (W m) (ε m) ν x) μ - gw ν μ =
          (pd (W m ν) μ - gw ν μ) - pd (corr c r (W m) (ε m) ν) μ := by
        funext x
        simp only [Pi.sub_apply]
        rw [pd_sub_real (((hW m ν).differentiable (by simp)) x)
          (((contDiff_corr c hr (hε0 m) (hε1 m) (hW m) ν).differentiable (by simp)) x)]
        ring
      rw [e1]
      exact eLpNorm_sub_le ((continuous_pd (hW1 m ν) μ).aestronglyMeasurable.sub
        (hgm ν μ).aestronglyMeasurable)
        (continuous_pd ((contDiff_corr c hr (hε0 m) (hε1 m) (hW m) ν).of_le (by simp))
          μ).aestronglyMeasurable (by norm_num)
    have := (hD ν μ).add hc
    rw [add_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this
      (fun _ => bot_le) hsplit

end RenewalGeometry.BallAnalysis.TanApprox
