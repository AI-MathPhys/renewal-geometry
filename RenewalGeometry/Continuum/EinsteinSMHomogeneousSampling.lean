/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMSmoothSampling
import RenewalGeometry.Gravity.HomogeneousEinsteinHiggsExact

/-!
# The homogeneous Einstein–Higgs example as a sampled comparison configuration

Einstein–Standard-Model action-closure manuscript, `prop:homogeneous` (closing sentence "Smooth
sampling yields the finite residual conclusion of `prop:smooth-sampling`") and
`cor:local-calibration-nonempty` ("A backreacting Einstein–Higgs example is supplied by
`prop:homogeneous`, after a regular gauge change on a smaller slab").

`homogeneous_comparison_member`: from the local solution `(a, φ, π, ℋ)` of `eq:homogeneous-ODE`
on `(-ε, ε)` (`HomogeneousEinsteinHiggs.exists_local_solution`), the fields
`e = diag(1, a, a, a)`, `H = (φ/√2) h₀`, `A = 0`, `Ψ = Ψ̄ = 0` of `eq:homogeneous-fields`, after
the regular change of time coordinate `t ↦ t - ε` (so that the smaller slab `[-ε/2, ε/2]` becomes
`[ε/2, 3ε/2] ⊂ (0, 2ε)`) and a smooth bump cut-off outside the smaller slab (constant coframe
`diag(1, a₀, a₀, a₀)` and zero Higgs field far from it), form a smooth configuration on
`(0, 2ε) × 𝕋³` that is a member of the sampled `C^{1,1}` class with coframe in a compact subset of
the nondegenerate chart, and agrees with `eq:homogeneous-fields` on the smaller slab.

Rendering (disclosed): the "regular gauge change on a smaller slab" is rendered as this time
translation together with the cut-off extension outside the smaller slab (the comparison box only
sees the fields on the slab where the tests live).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace Comparison

open SobolevOpen (pd)
open CardinalQI C11Calculus

/-! ### Bump extensions of functions given on an interval -/

section BumpExt

/-- The bump `χ = 1` on `[-ε/2, ε/2]`, supported in `(-3ε/4, 3ε/4)`. -/
def slabBump {ε : ℝ} (hε : 0 < ε) : ContDiffBump (0 : ℝ) :=
  ⟨ε / 2, 3 * ε / 4, by positivity, by linarith⟩

/-- The shifted bump extension `t ↦ χ(t-ε) f(t-ε) + (1 - χ(t-ε)) c`. -/
def bumpExt {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ) (c : ℝ) (t : ℝ) : ℝ :=
  slabBump hε (t - ε) * f (t - ε) + (1 - slabBump hε (t - ε)) * c

theorem bumpExt_eq_of_near {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ) (c : ℝ) {t : ℝ}
    (ht : |t - ε| ≤ ε / 2) : bumpExt hε f c t = f (t - ε) := by
  have : slabBump hε (t - ε) = 1 :=
    (slabBump hε).one_of_mem_closedBall (by rw [mem_closedBall, Real.dist_eq, sub_zero]; exact ht)
  simp [bumpExt, this]

theorem bumpExt_eq_of_far {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ) (c : ℝ) {t : ℝ}
    (ht : 3 * ε / 4 ≤ |t - ε|) : bumpExt hε f c t = c := by
  have : slabBump hε (t - ε) = 0 :=
    (slabBump hε).zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact ht)
  simp [bumpExt, this]

theorem contDiff_bumpExt {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo (-ε) ε))
    (c : ℝ) : ContDiff ℝ ∞ (bumpExt hε f c) := by
  refine contDiff_iff_contDiffAt.mpr fun t => ?_
  by_cases ht : |t - ε| < ε
  · have hmem : t - ε ∈ Ioo (-ε) ε := by
      rw [abs_lt] at ht; exact ⟨ht.1, ht.2⟩
    have hfa : ContDiffAt ℝ ∞ (fun s => f (s - ε)) t :=
      (hf.contDiffAt (Ioo_mem_nhds hmem.1 hmem.2)).comp t
        ((contDiff_id.sub contDiff_const).contDiffAt)
    have hχ : ContDiffAt ℝ ∞ (fun s => slabBump hε (s - ε)) t :=
      ((slabBump hε).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
    exact (hχ.mul hfa).add ((contDiffAt_const.sub hχ).mul contDiffAt_const)
  · push_neg at ht
    have ho : IsOpen {s : ℝ | 3 * ε / 4 < |s - ε|} :=
      isOpen_lt continuous_const ((continuous_id.sub continuous_const).abs)
    have hev : bumpExt hε f c =ᶠ[𝓝 t] fun _ => c :=
      Filter.eventually_of_mem (ho.mem_nhds (show 3 * ε / 4 < |t - ε| by linarith))
        fun s hs => bumpExt_eq_of_far hε f c (le_of_lt hs)
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem hasCompactSupport_bumpExt_sub {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ) (c : ℝ) :
    HasCompactSupport fun t => bumpExt hε f c t - c := by
  refine HasCompactSupport.intro (isCompact_closedBall ε (3 * ε / 4)) fun t ht => ?_
  rw [mem_closedBall, Real.dist_eq, not_le] at ht
  rw [bumpExt_eq_of_far hε f c ht.le, sub_self]

/-- Uniform bounds of a `C²` function that is constant outside a compact set. -/
theorem exists_bounds_of_compactSupport_sub {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {c : ℝ}
    (hs : HasCompactSupport fun t => g t - c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |g t| ≤ B ∧ |deriv g t| ≤ B ∧ |deriv (deriv g) t| ≤ B := by
  have hg1 : ContDiff ℝ 1 (deriv g) := (contDiff_succ_iff_deriv.mp hg).2.2
  have hg0 : Continuous (deriv (deriv g)) :=
    ((contDiff_succ_iff_deriv.mp (show ContDiff ℝ (0 + 1) (deriv g) from hg1)).2.2).continuous
  have hd1 : deriv g = deriv fun t => g t - c := by
    funext t; rw [deriv_sub_const]
  have hs1 : HasCompactSupport (deriv g) := hd1 ▸ hs.deriv
  have hs2 : HasCompactSupport (deriv (deriv g)) := hs1.deriv
  obtain ⟨C₀, hC₀⟩ := (hg.continuous.sub continuous_const).bounded_above_of_compact_support hs
  obtain ⟨C₁, hC₁⟩ := hg1.continuous.bounded_above_of_compact_support hs1
  obtain ⟨C₂, hC₂⟩ := hg0.bounded_above_of_compact_support hs2
  refine ⟨|C₀| + |c| + |C₁| + |C₂|, by positivity, fun t => ⟨?_, ?_, ?_⟩⟩
  · have h : |g t - c| ≤ C₀ := by simpa [Real.norm_eq_abs] using hC₀ t
    have := abs_sub_abs_le_abs_sub (g t) c
    have := le_abs_self C₀
    have := abs_nonneg C₁; have := abs_nonneg C₂
    linarith
  · have h : |deriv g t| ≤ C₁ := by simpa [Real.norm_eq_abs] using hC₁ t
    have := le_abs_self C₁; have := abs_nonneg C₀; have := abs_nonneg c
    have := abs_nonneg C₂
    linarith
  · have h : |deriv (deriv g) t| ≤ C₂ := by simpa [Real.norm_eq_abs] using hC₂ t
    have := le_abs_self C₂; have := abs_nonneg C₀; have := abs_nonneg c
    have := abs_nonneg C₁
    linarith

/-- `x ↦ g(x⁰)` is `C^{1,1}` with constant `B` when `g`, `g'`, `g''` are bounded by `B`. -/
theorem isC11_comp_time {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {B : ℝ}
    (hb : ∀ t, |g t| ≤ B ∧ |deriv g t| ≤ B ∧ |deriv (deriv g) t| ≤ B) :
    IsC11 (fun x : E4 => g (x 0)) B := by
  have hdg : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hg1 : ContDiff ℝ 1 (deriv g) := (contDiff_succ_iff_deriv.mp hg).2.2
  have hdg1 : Differentiable ℝ (deriv g) := hg1.differentiable (by norm_num)
  set P : E4 →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hP : ‖P‖ ≤ 1 := norm_proj_le_one 0
  have hd : ∀ x : E4, HasFDerivAt (fun x : E4 => g (x 0)) (deriv g (x 0) • P) x := fun x =>
    (hdg (x 0)).hasDerivAt.comp_hasFDerivAt x (P.hasFDerivAt (x := x))
  have hfd : ∀ x : E4, fderiv ℝ (fun x : E4 => g (x 0)) x = deriv g (x 0) • P := fun x =>
    (hd x).fderiv
  have hsm : ∀ r : ℝ, ‖r • P‖ ≤ |r| := fun r => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) hP
  refine ⟨fun x => by rw [hfd]; exact hd x, fun x => ?_, fun x => ?_, fun x y => ?_⟩
  · rw [Real.norm_eq_abs]; exact (hb _).1
  · rw [hfd]; exact (hsm _).trans (hb _).2.1
  · rw [hfd, hfd, ← sub_smul]
    refine (hsm _).trans ?_
    have hmv : ‖deriv g (x 0) - deriv g (y 0)‖ ≤ B * ‖x 0 - y 0‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv g) (s := univ)
        (fun t _ => hdg1 t) (fun t _ => by rw [Real.norm_eq_abs]; exact (hb t).2.2) convex_univ
        (mem_univ _) (mem_univ _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
    refine hmv.trans (mul_le_mul_of_nonneg_left ?_ ((abs_nonneg _).trans (hb 0).1))
    rw [← Real.norm_eq_abs, ← Pi.sub_apply]
    exact norm_le_pi_norm (x - y) 0

end BumpExt

/-! ### The homogeneous comparison configuration -/

/-- The FLRW coframe `diag(1, α, α, α)`. -/
def frameDiag (α : ℝ) : CoframeFibre := fun i j => if i = j then (if i = 0 then 1 else α) else 0

/-- `frameDiag α = E₀ + α D` with `E₀ = diag(1,0,0,0)`, `D = diag(0,1,1,1)`. -/
def frameE0 : CoframeFibre := fun i j => if i = j ∧ i = 0 then 1 else 0

def frameD : CoframeFibre := fun i j => if i = j ∧ i ≠ 0 then 1 else 0

theorem frameDiag_eq (α : ℝ) : frameDiag α = frameE0 + α • frameD := by
  funext i j
  by_cases hij : i = j
  · subst hij; by_cases hi : i = 0 <;> simp [frameDiag, frameE0, frameD, hi]
  · simp [frameDiag, frameE0, frameD, hij]

theorem det_frameDiag (α : ℝ) : (Matrix.of (frameDiag α)).det = α ^ 3 := by
  have : Matrix.of (frameDiag α) = Matrix.diagonal fun i : Fin 4 => if i = 0 then 1 else α := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [frameDiag]
    · simp [frameDiag, hij]
  rw [this, Matrix.det_diagonal, Fin.prod_univ_four]
  simp; ring

theorem frameDiag_mem_chart {α : ℝ} (hα : 0 < α) : frameDiag α ∈ coframeChart :=
  ⟨by rw [det_frameDiag]; positivity, by simp [frameDiag]⟩

theorem continuous_frameDiag : Continuous frameDiag := by
  have : frameDiag = fun α => frameE0 + α • frameD := funext frameDiag_eq
  rw [this]; fun_prop

variable {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec)

/-- **`prop:homogeneous` / `cor:local-calibration-nonempty`: the homogeneous Einstein–Higgs
example as a sampled comparison configuration.** -/
theorem homogeneous_comparison_member (κ lamH vH a₀ φ₀ π₀ H₀ : ℝ) (ha₀ : 0 < a₀)
    (h₀ : HiggsFibre) :
    ∃ (ε : ℝ) (_ : 0 < ε) (a φ π ℋ : ℝ → ℝ),
      a 0 = a₀ ∧ φ 0 = φ₀ ∧ π 0 = π₀ ∧ ℋ 0 = H₀ ∧
      HomogeneousEinsteinHiggs.IsSolution κ lamH vH a φ π ℋ (Ioo (-ε) ε) ∧
      (∀ t ∈ Ioo (-ε) ε, 0 < a t) ∧
      ∃ (zs : SmoothFields (2 * ε) FC.left) (B : ℝ) (Kf : Set CoframeFibre),
        0 ≤ B ∧ IsCompact Kf ∧ Kf ⊆ coframeChart ∧ SampledFamily FC B Kf zs.z ∧
        ∀ x : E4, x 0 ∈ Icc (ε / 2) (3 * ε / 2) →
          zs.z.e x = frameDiag (a (x 0 - ε)) ∧ zs.z.H x = (φ (x 0 - ε) / Real.sqrt 2) • h₀ ∧
          zs.z.A x = 0 ∧ zs.z.Ψ x = 0 ∧ zs.z.Ψb x = 0 := by
  obtain ⟨ε, hε, a, φ, π, ℋ, h1, h2, h3, h4, hsol, hpos, hca, hcφ, -, -⟩ :=
    HomogeneousEinsteinHiggs.exists_local_solution κ lamH vH a₀ φ₀ π₀ H₀ ha₀
  refine ⟨ε, hε, a, φ, π, ℋ, h1, h2, h3, h4, hsol, hpos, ?_⟩
  set ga := bumpExt hε a a₀
  set gφ := bumpExt hε φ 0
  have hga : ContDiff ℝ ∞ ga := contDiff_bumpExt hε hca a₀
  have hgφ : ContDiff ℝ ∞ gφ := contDiff_bumpExt hε hcφ 0
  obtain ⟨Ba, hBa, hba⟩ := exists_bounds_of_compactSupport_sub (hga.of_le (by norm_cast))
    (hasCompactSupport_bumpExt_sub hε a a₀)
  obtain ⟨Bφ, hBφ, hbφ⟩ := exists_bounds_of_compactSupport_sub (hgφ.of_le (by norm_cast))
    (hasCompactSupport_bumpExt_sub hε φ 0)
  -- positivity of the extended scale factor
  have hgapos : ∀ t, 0 < ga t := fun t => by
    have hχ0 := (slabBump hε).nonneg' (t - ε)
    have hχ1 : slabBump hε (t - ε) ≤ 1 := (slabBump hε).le_one
    by_cases ht : |t - ε| < ε
    · have hm : t - ε ∈ Ioo (-ε) ε := by rw [abs_lt] at ht; exact ⟨ht.1, ht.2⟩
      have ha := hpos _ hm
      show 0 < slabBump hε (t - ε) * a (t - ε) + (1 - slabBump hε (t - ε)) * a₀
      rcases eq_or_lt_of_le hχ0 with h | h
      · rw [← h]; simp; exact ha₀
      · nlinarith [mul_pos h ha, mul_nonneg (sub_nonneg.mpr hχ1) ha₀.le]
    · push_neg at ht
      rw [show ga t = a₀ from bumpExt_eq_of_far hε a a₀ (by linarith)]; exact ha₀
  -- the coframe values form a compact subset of the chart
  set S := ga '' closedBall ε ε
  have hS : IsCompact S := (isCompact_closedBall ε ε).image hga.continuous
  have hrange : ∀ t, ga t ∈ S := fun t => by
    by_cases ht : |t - ε| ≤ ε
    · exact ⟨t, by rw [mem_closedBall, Real.dist_eq]; exact ht, rfl⟩
    · push_neg at ht
      refine ⟨2 * ε, by rw [mem_closedBall, Real.dist_eq, show 2 * ε - ε = ε by ring,
        abs_of_pos hε], ?_⟩
      show bumpExt hε a a₀ (2 * ε) = bumpExt hε a a₀ t
      rw [bumpExt_eq_of_far hε a a₀ (by rw [show 2 * ε - ε = ε by ring, abs_of_pos hε]; linarith),
        bumpExt_eq_of_far hε a a₀ (by linarith)]
  set Kf := frameDiag '' S
  have hKf : IsCompact Kf := hS.image continuous_frameDiag
  have hKfC : Kf ⊆ coframeChart := by
    rintro _ ⟨α, ⟨t, -, rfl⟩, rfl⟩
    exact frameDiag_mem_chart (hgapos t)
  -- the fields
  set hv : HiggsFibre := (1 / Real.sqrt 2) • h₀
  set z : FieldTuple FC.C := (fun x => frameDiag (ga (x 0)), 0, fun x => gφ (x 0) • hv, 0, 0)
  have hze : z.e = fun x => frameE0 + ga (x 0) • frameD := funext fun x => frameDiag_eq _
  have hcze : IsC11 z.e (‖frameE0‖ + ‖(ContinuousLinearMap.id ℝ ℝ).smulRight frameD‖ * Ba) := by
    rw [hze]
    exact (IsC11.const frameE0).add
      ((isC11_comp_time (hga.of_le (by norm_cast)) hba).clm
        ((ContinuousLinearMap.id ℝ ℝ).smulRight frameD))
  have hczH : IsC11 z.H (‖(ContinuousLinearMap.id ℝ ℝ).smulRight hv‖ * Bφ) :=
    ((isC11_comp_time (hgφ.of_le (by norm_cast)) hbφ).clm
      ((ContinuousLinearMap.id ℝ ℝ).smulRight hv)).congr fun x => rfl
  set B := ‖frameE0‖ + ‖(ContinuousLinearMap.id ℝ ℝ).smulRight frameD‖ * Ba +
    ‖(ContinuousLinearMap.id ℝ ℝ).smulRight hv‖ * Bφ
  have hB : 0 ≤ B := by positivity
  have hzero : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W],
      IsC11 (0 : E4 → W) B := fun {W} _ _ =>
    ((IsC11.const (0 : W)).mono (by simpa using hB)).congr fun _ => rfl
  have n1 := norm_nonneg ((ContinuousLinearMap.id ℝ ℝ).smulRight hv)
  have n2 := norm_nonneg ((ContinuousLinearMap.id ℝ ℝ).smulRight frameD)
  have n3 := norm_nonneg frameE0
  have hB1 : ‖frameE0‖ + ‖(ContinuousLinearMap.id ℝ ℝ).smulRight frameD‖ * Ba ≤ B := by
    simp only [B]; nlinarith
  have hB2 : ‖(ContinuousLinearMap.id ℝ ℝ).smulRight hv‖ * Bφ ≤ B := by
    simp only [B]; nlinarith
  have hfam : SampledFamily FC B Kf z :=
    ⟨⟨hcze.mono hB1, hzero, hczH.mono hB2, hzero, hzero⟩,
      fun y => ⟨ga (y 0), hrange _, rfl⟩,
      fun n y => by
        show frameDiag (ga ((y + spatialShift n) 0)) = frameDiag (ga (y 0))
        rw [Pi.add_apply, spatialShift_zero, add_zero],
      fun n y => rfl,
      fun n y => by
        show gφ ((y + spatialShift n) 0) • hv = gφ (y 0) • hv
        rw [Pi.add_apply, spatialShift_zero, add_zero],
      fun n y => rfl, fun n y => rfl,
      fun _ _ => smLie.zero_mem, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  let zs : SmoothFields (2 * ε) FC.left :=
    { z := z
      smooth_e := by
        have : ContDiff ℝ ∞ fun x : E4 => frameDiag (ga (x 0)) := by
          have hfr : frameDiag = fun α => frameE0 + α • frameD := funext frameDiag_eq
          rw [hfr]
          exact contDiff_const.add ((hga.comp (contDiff_apply ℝ ℝ 0)).smul contDiff_const)
        exact this.contDiffOn
      smooth_A := contDiff_const.contDiffOn
      smooth_H := ((hgφ.comp (contDiff_apply ℝ ℝ 0)).smul contDiff_const).contDiffOn
      smooth_Ψ := contDiff_const.contDiffOn
      smooth_Ψb := contDiff_const.contDiffOn
      periodic_e := hfam.per_e
      periodic_A := hfam.per_A
      periodic_H := hfam.per_H
      periodic_Ψ := hfam.per_Ψ
      periodic_Ψb := hfam.per_Ψb
      lie := hfam.lie
      chiral := hfam.chiral
      cochiral := hfam.cochiral }
  refine ⟨zs, B, Kf, hB, hKf, hKfC, hfam, fun x hx => ?_⟩
  have hnear : |x 0 - ε| ≤ ε / 2 := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · show frameDiag (bumpExt hε a a₀ (x 0)) = _
    rw [bumpExt_eq_of_near hε a a₀ hnear]
  · show bumpExt hε φ 0 (x 0) • hv = _
    rw [bumpExt_eq_of_near hε φ 0 hnear, smul_smul]
    congr 1; field_simp


/-- **The sampling clause of `prop:homogeneous`**: the homogeneous Einstein–Higgs comparison
configuration (after the time translation and cut-off of `homogeneous_comparison_member`) is
smoothly sampled with `c_h(K) = O(h)`, `d_K(z_h, z_*) = O(h)`, and `ε_h(K) = O(h)` whenever it
satisfies the weak Euler equations on the tests of `K` (`prop:smooth-sampling`). -/
theorem homogeneous_smooth_sampling [Nonempty FC.C] (κ lamH vH a₀ φ₀ π₀ H₀ : ℝ) (ha₀ : 0 < a₀)
    (h₀ : HiggsFibre) :
    ∃ (ε : ℝ) (_ : 0 < ε) (a φ π ℋ : ℝ → ℝ),
      HomogeneousEinsteinHiggs.IsSolution κ lamH vH a φ π ℋ (Ioo (-ε) ε) ∧
      ∃ (zs : SmoothFields (2 * ε) FC.left) (B : ℝ) (Kf : Set CoframeFibre)
        (hzs : SampledFamily FC B Kf zs.z),
        (∀ x : E4, x 0 ∈ Icc (ε / 2) (3 * ε / 2) →
          zs.z.e x = frameDiag (a (x 0 - ε)) ∧ zs.z.H x = (φ (x 0 - ε) / Real.sqrt 2) • h₀ ∧
          zs.z.A x = 0 ∧ zs.z.Ψ x = 0 ∧ zs.z.Ψb x = 0) ∧
        ∀ (θ : CoefficientBank Ysec) (_ : θ ∈ physicalBanks) (t₀ t₁ : ℝ) (h0 : 0 < t₀)
          (h01 : t₀ < t₁) (h1 : t₁ < 2 * ε) (K : CylRegion (2 * ε))
          (_ : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) (P : ℕ) (_ : 2 * ε ≤ P) (r₀ : ℕ) (_ : 2 ≤ r₀),
          ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ (N : ℕ) (_ : N₀ ≤ N) (hN : 0 < N),
            comparisonDefect FC (2 * ε) θ P N r₀ K (sampleRec FC (1 / N) zs.z) ≤
                ENNReal.ofReal (C * (1 / N)) ∧
              dK (slabChart t₀ t₁ h0 h01 h1 (T := 2 * ε)) (reconSmooth FC (2 * ε) hN hzs) θ zs θ ≤
                ENNReal.ofReal (C * (1 / N)) ∧
              ((∀ v ∈ testSubmodule FC.left K, ∑ b, firstVariation (2 * ε) FC θ b zs.z v = 0) →
                comparisonStationarity FC (2 * ε) θ P N r₀ K (sampleRec FC (1 / N) zs.z) ≤
                  ENNReal.ofReal (C * (1 / N))) := by
  obtain ⟨ε, hε, a, φ, π, ℋ, -, -, -, -, hsol, -, zs, B, Kf, hB, hKf, hKfC, hzs, heq⟩ :=
    homogeneous_comparison_member FC κ lamH vH a₀ φ₀ π₀ H₀ ha₀ h₀
  refine ⟨ε, hε, a, φ, π, ℋ, hsol, zs, B, Kf, hzs, heq, fun θ hθ t₀ t₁ h0 h01 h1 K hK P hTP r₀ hr =>
    ?_⟩
  obtain ⟨C, hC, N₀, hss⟩ := smooth_sampling FC θ hθ h0 h01 h1 hK hTP hr hB hKf hKfC
  exact ⟨C, hC, N₀, fun N hN₀ hN => hss zs hzs N hN₀ hN⟩

end Comparison
end EinsteinSM
end RenewalGeometry
