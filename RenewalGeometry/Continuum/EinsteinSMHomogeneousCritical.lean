/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMHomogeneousCovector

/-!
# The homogeneous Einstein–Higgs configuration is a critical point of the continuum action
  (`prop:homogeneous`, Einstein–Standard-Model action-closure manuscript)

`prop:homogeneous`: the fields `eq:homogeneous-fields` built from a local solution of
`eq:homogeneous-ODE` with the Friedmann constraint `eq:Friedmann-initial` solve the
torsion-free Einstein–Standard-Model equations, and "smooth sampling yields the finite residual
conclusion of `prop:smooth-sampling`".

* `homogeneous_critical_member`: on the slab `(-ε/2, ε/2)` of the local solution, translated
  to the comparison cylinder `M = (0, ε) × 𝕋³` (time translation `t ↦ t + ε/2`; outside the closed
  slab the fields are extended by a smooth cut-off so that they belong to the sampled `C^{1,1}`
  class), the configuration `e = diag(1, a, a, a)`, `H = (φ/√2) h₀`, `A = 0`, `Ψ = Ψ̄ = 0`
  satisfies the weak Euler equations of the library's continuum action
  `Σ_b D𝒮_{b,θ}(z_*)[v] = 0` for **every** physical test `v ∈ 𝒱_K` and every `K ⋐ M`.
  Proof: the first variation is the slab integral of the jet covectors (`gravVariation_eq_cov`,
  `smVariation_eq_cov`); at the homogeneous jet these are computed in closed form
  (`gravCov_flrw`, `bosonCov_flrw`, `diracCov_zero`), and the integrand is the divergence of an
  explicit flux once the Friedmann constraint, `ℋ̇ = -(κ/2)π²` and the Higgs equation are used
  (`integrand_eq_div`); spatial periodicity and the compact time support of the test make the
  integral of the divergence vanish (`integral_div_slab_eq_zero`).
* `homogeneous_smooth_sampling_closed`: hence `c_h(K) = O(h)`, `d_K(z_h, z_*) = O(h)` and
  `ε_h(K) = O(h)` (unconditionally) for the sampled homogeneous configuration
  (`prop:smooth-sampling` via `smooth_sampling`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff

noncomputable section

set_option synthInstance.maxSize 1024
set_option linter.unusedSectionVars false

namespace RenewalGeometry
namespace EinsteinSM
namespace HomogeneousCritical

open SobolevOpen (pd)
open CardinalQI C11Calculus Comparison HomogeneousCov GammaCov

/-! ### Shifted bump extensions -/

/-- The shifted bump extension `t ↦ χ(t-σ) f(t-σ) + (1 - χ(t-σ)) c`. -/
def bumpShift {ε : ℝ} (hε : 0 < ε) (σ : ℝ) (f : ℝ → ℝ) (c : ℝ) (t : ℝ) : ℝ :=
  slabBump hε (t - σ) * f (t - σ) + (1 - slabBump hε (t - σ)) * c

theorem bumpShift_eq_of_near {ε : ℝ} (hε : 0 < ε) (σ : ℝ) (f : ℝ → ℝ) (c : ℝ) {t : ℝ}
    (ht : |t - σ| ≤ ε / 2) : bumpShift hε σ f c t = f (t - σ) := by
  have : slabBump hε (t - σ) = 1 :=
    (slabBump hε).one_of_mem_closedBall (by rw [mem_closedBall, Real.dist_eq, sub_zero]; exact ht)
  simp [bumpShift, this]

theorem bumpShift_eq_of_far {ε : ℝ} (hε : 0 < ε) (σ : ℝ) (f : ℝ → ℝ) (c : ℝ) {t : ℝ}
    (ht : 3 * ε / 4 ≤ |t - σ|) : bumpShift hε σ f c t = c := by
  have : slabBump hε (t - σ) = 0 :=
    (slabBump hε).zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact ht)
  simp [bumpShift, this]

theorem contDiff_bumpShift {ε : ℝ} (hε : 0 < ε) (σ : ℝ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo (-ε) ε)) (c : ℝ) : ContDiff ℝ ∞ (bumpShift hε σ f c) := by
  refine contDiff_iff_contDiffAt.mpr fun t => ?_
  by_cases ht : |t - σ| < ε
  · have hmem : t - σ ∈ Ioo (-ε) ε := by
      rw [abs_lt] at ht; exact ⟨ht.1, ht.2⟩
    have hfa : ContDiffAt ℝ ∞ (fun s => f (s - σ)) t :=
      (hf.contDiffAt (Ioo_mem_nhds hmem.1 hmem.2)).comp t
        ((contDiff_id.sub contDiff_const).contDiffAt)
    have hχ : ContDiffAt ℝ ∞ (fun s => slabBump hε (s - σ)) t :=
      ((slabBump hε).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
    exact (hχ.mul hfa).add ((contDiffAt_const.sub hχ).mul contDiffAt_const)
  · push_neg at ht
    have ho : IsOpen {s : ℝ | 3 * ε / 4 < |s - σ|} :=
      isOpen_lt continuous_const ((continuous_id.sub continuous_const).abs)
    have hev : bumpShift hε σ f c =ᶠ[𝓝 t] fun _ => c :=
      Filter.eventually_of_mem (ho.mem_nhds (show 3 * ε / 4 < |t - σ| by linarith))
        fun s hs => bumpShift_eq_of_far hε σ f c (le_of_lt hs)
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem hasCompactSupport_bumpShift_sub {ε : ℝ} (hε : 0 < ε) (σ : ℝ) (f : ℝ → ℝ) (c : ℝ) :
    HasCompactSupport fun t => bumpShift hε σ f c t - c := by
  refine HasCompactSupport.intro (isCompact_closedBall σ (3 * ε / 4)) fun t ht => ?_
  rw [mem_closedBall, Real.dist_eq, not_le] at ht
  rw [bumpShift_eq_of_far hε σ f c ht.le, sub_self]

/-- Near a point of the open slab, the bump extension is the translated function. -/
theorem bumpShift_eventuallyEq {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ) (c : ℝ) {t : ℝ}
    (ht : t ∈ Ioo 0 ε) : bumpShift hε (ε / 2) f c =ᶠ[𝓝 t] fun s => f (s - ε / 2) := by
  have hU : IsOpen (Ioo (0 : ℝ) ε) := isOpen_Ioo
  filter_upwards [hU.mem_nhds ht] with s hs
  refine bumpShift_eq_of_near hε (ε / 2) f c ?_
  rw [abs_le]; constructor <;> linarith [hs.1, hs.2]

/-! ### The translated homogeneous configuration -/

section Config

variable {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec)

/-- The Higgs direction `h₀/√2`. -/
def hvec (h₀ : HiggsFibre) : HiggsFibre := (1 / Real.sqrt 2) • h₀

/-- **The translated homogeneous configuration** on `M = (0, ε) × 𝕋³`:
`e = diag(1, ã, ã, ã)`, `A = 0`, `H = φ̃ h₀/√2`, `Ψ = Ψ̄ = 0`, with `ã, φ̃` the bump extensions of
`t ↦ a(t - ε/2)`, `t ↦ φ(t - ε/2)` (equal to them for `t ∈ [0, ε]`). -/
def homConfig {ε : ℝ} (hε : 0 < ε) (a φ : ℝ → ℝ) (a₀ : ℝ) (h₀ : HiggsFibre) : FieldTuple FC.C :=
  (fun x => frameDiag (bumpShift hε (ε / 2) a a₀ (x 0)), 0,
    fun x => bumpShift hε (ε / 2) φ 0 (x 0) • hvec h₀, 0, 0)

theorem homConfig_e {ε : ℝ} (hε : 0 < ε) (a φ : ℝ → ℝ) (a₀ : ℝ) (h₀ : HiggsFibre) (x : E4) :
    (homConfig FC hε a φ a₀ h₀).e x = frameDiag (bumpShift hε (ε / 2) a a₀ (x 0)) := rfl

theorem homConfig_H {ε : ℝ} (hε : 0 < ε) (a φ : ℝ → ℝ) (a₀ : ℝ) (h₀ : HiggsFibre) (x : E4) :
    (homConfig FC hε a φ a₀ h₀).H x = bumpShift hε (ε / 2) φ 0 (x 0) • hvec h₀ := rfl

theorem homConfig_A {ε : ℝ} (hε : 0 < ε) (a φ : ℝ → ℝ) (a₀ : ℝ) (h₀ : HiggsFibre) :
    (homConfig FC hε a φ a₀ h₀).A = 0 := rfl

theorem homConfig_Ψ {ε : ℝ} (hε : 0 < ε) (a φ : ℝ → ℝ) (a₀ : ℝ) (h₀ : HiggsFibre) :
    (homConfig FC hε a φ a₀ h₀).Ψ = 0 := rfl

theorem homConfig_Ψb {ε : ℝ} (hε : 0 < ε) (a φ : ℝ → ℝ) (a₀ : ℝ) (h₀ : HiggsFibre) :
    (homConfig FC hε a φ a₀ h₀).Ψb = 0 := rfl

/-- **The translated homogeneous configuration is smooth, spatially periodic and lies in the
sampled `C^{1,1}` class with coframe values in a compact subset of the chart.** -/
theorem homConfig_sampled {ε : ℝ} (hε : 0 < ε) {a φ : ℝ → ℝ} {a₀ : ℝ} (ha₀ : 0 < a₀)
    (h₀ : HiggsFibre) (hca : ContDiffOn ℝ ∞ a (Ioo (-ε) ε)) (hcφ : ContDiffOn ℝ ∞ φ (Ioo (-ε) ε))
    (hpos : ∀ t ∈ Ioo (-ε) ε, 0 < a t) :
    ∃ (zs : SmoothFields ε FC.left) (B : ℝ) (Kf : Set CoframeFibre),
      zs.z = homConfig FC hε a φ a₀ h₀ ∧ 0 ≤ B ∧ IsCompact Kf ∧ Kf ⊆ coframeChart ∧
        SampledFamily FC B Kf zs.z ∧ (∀ t, 0 < bumpShift hε (ε / 2) a a₀ t) := by
  set ga := bumpShift hε (ε / 2) a a₀
  set gφ := bumpShift hε (ε / 2) φ 0
  have hga : ContDiff ℝ ∞ ga := contDiff_bumpShift hε (ε / 2) hca a₀
  have hgφ : ContDiff ℝ ∞ gφ := contDiff_bumpShift hε (ε / 2) hcφ 0
  obtain ⟨Ba, hBa, hba⟩ := exists_bounds_of_compactSupport_sub (hga.of_le (by norm_cast))
    (hasCompactSupport_bumpShift_sub hε (ε / 2) a a₀)
  obtain ⟨Bφ, hBφ, hbφ⟩ := exists_bounds_of_compactSupport_sub (hgφ.of_le (by norm_cast))
    (hasCompactSupport_bumpShift_sub hε (ε / 2) φ 0)
  have hgapos : ∀ t, 0 < ga t := fun t => by
    have hχ0 := (slabBump hε).nonneg' (t - ε / 2)
    have hχ1 : slabBump hε (t - ε / 2) ≤ 1 := (slabBump hε).le_one
    by_cases ht : |t - ε / 2| < ε
    · have hm : t - ε / 2 ∈ Ioo (-ε) ε := by rw [abs_lt] at ht; exact ⟨ht.1, ht.2⟩
      have ha := hpos _ hm
      show 0 < slabBump hε (t - ε / 2) * a (t - ε / 2) + (1 - slabBump hε (t - ε / 2)) * a₀
      rcases eq_or_lt_of_le hχ0 with h | h
      · rw [← h]; simp; exact ha₀
      · nlinarith [mul_pos h ha, mul_nonneg (sub_nonneg.mpr hχ1) ha₀.le]
    · push_neg at ht
      rw [show ga t = a₀ from bumpShift_eq_of_far hε (ε / 2) a a₀ (by linarith)]; exact ha₀
  set S := ga '' closedBall (ε / 2) ε
  have hS : IsCompact S := (isCompact_closedBall (ε / 2) ε).image hga.continuous
  have hrange : ∀ t, ga t ∈ S := fun t => by
    by_cases ht : |t - ε / 2| ≤ ε
    · exact ⟨t, by rw [mem_closedBall, Real.dist_eq]; exact ht, rfl⟩
    · push_neg at ht
      refine ⟨ε / 2 + ε, by rw [mem_closedBall, Real.dist_eq, show ε / 2 + ε - ε / 2 = ε by ring,
        abs_of_pos hε], ?_⟩
      show bumpShift hε (ε / 2) a a₀ (ε / 2 + ε) = bumpShift hε (ε / 2) a a₀ t
      rw [bumpShift_eq_of_far hε (ε / 2) a a₀
          (by rw [show ε / 2 + ε - ε / 2 = ε by ring, abs_of_pos hε]; linarith),
        bumpShift_eq_of_far hε (ε / 2) a a₀ (by linarith)]
  set Kf := frameDiag '' S
  have hKf : IsCompact Kf := hS.image continuous_frameDiag
  have hKfC : Kf ⊆ coframeChart := by
    rintro _ ⟨α, ⟨t, -, rfl⟩, rfl⟩
    exact frameDiag_mem_chart (hgapos t)
  set hv : HiggsFibre := hvec h₀
  set z : FieldTuple FC.C := homConfig FC hε a φ a₀ h₀
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
  let zs : SmoothFields ε FC.left :=
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
  exact ⟨zs, B, Kf, rfl, hB, hKf, hKfC, hfam, hgapos⟩

end Config

/-! ### Jets of homogeneous fields -/

section Jets

variable {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec)

/-- Partial derivatives of a function of time only. -/
theorem pd_time {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : ℝ → F} {x : E4}
    (hg : DifferentiableAt ℝ g (x 0)) (i : Fin 4) :
    pd (fun y : E4 => g (y 0)) i x = (if i = 0 then (1 : ℝ) else 0) • deriv g (x 0) := by
  unfold pd
  have hP : HasFDerivAt (fun y : E4 => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).hasFDerivAt
  have h := hg.hasFDerivAt.comp x hP
  rw [show (fun y : E4 => g (y 0)) = g ∘ fun y : E4 => y 0 from rfl, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv,
    ContinuousLinearMap.proj_apply, Pi.single_apply]
  by_cases hi : i = 0
  · subst hi; simp
  · simp [hi, Ne.symm hi]

theorem hasDerivAt_frameDiag_comp {g : ℝ → ℝ} {t : ℝ} (hg : DifferentiableAt ℝ g t) :
    HasDerivAt (fun s => frameDiag (g s)) (deriv g t • frameD) t := by
  have h : (fun s => frameDiag (g s)) = fun s => frameE0 + g s • frameD :=
    funext fun s => frameDiag_eq (g s)
  rw [h]
  exact (hg.hasDerivAt.smul_const frameD).const_add frameE0

variable {ε : ℝ} (hε : 0 < ε) (a φ : ℝ → ℝ) (a₀ : ℝ) (h₀ : HiggsFibre)

theorem redJet_homConfig_e (x : E4) :
    (redJet (homConfig FC hε a φ a₀ h₀) x).e = frameDiag (bumpShift hε (ε / 2) a a₀ (x 0)) := rfl

theorem redJet_homConfig_de (hca : ContDiff ℝ ∞ (bumpShift hε (ε / 2) a a₀)) (x : E4) :
    (redJet (homConfig FC hε a φ a₀ h₀) x).de =
      flrwDe (deriv (bumpShift hε (ε / 2) a a₀) (x 0)) := by
  have hd : DifferentiableAt ℝ (bumpShift hε (ε / 2) a a₀) (x 0) :=
    (hca.differentiable (by simp)).differentiableAt
  have hfd : DifferentiableAt ℝ (fun s => frameDiag (bumpShift hε (ε / 2) a a₀ s)) (x 0) :=
    (hasDerivAt_frameDiag_comp hd).differentiableAt
  funext i
  show pd (fun y : E4 => frameDiag (bumpShift hε (ε / 2) a a₀ (y 0))) i x = _
  rw [pd_time hfd i, (hasDerivAt_frameDiag_comp hd).deriv]
  simp only [flrwDe]
  by_cases hi : i = 0 <;> simp [hi, smul_smul]

theorem redJet_homConfig_A (x : E4) : (redJet (homConfig FC hε a φ a₀ h₀) x).A = 0 := rfl

theorem redJet_homConfig_F (x : E4) : (redJet (homConfig FC hε a φ a₀ h₀) x).F = 0 := by
  funext μ ν
  show curvatureF 0 x μ ν = 0
  simp [curvatureF, pd, comm, mmul]

theorem redJet_homConfig_H (x : E4) :
    (redJet (homConfig FC hε a φ a₀ h₀) x).H = bumpShift hε (ε / 2) φ 0 (x 0) • hvec h₀ := rfl

theorem higgsAct_zero_left (u : HiggsFibre) : higgsAct 0 u = 0 := by
  funext i; simp [higgsAct]

theorem redJet_homConfig_K (hcφ : ContDiff ℝ ∞ (bumpShift hε (ε / 2) φ 0)) (x : E4) :
    (redJet (homConfig FC hε a φ a₀ h₀) x).K =
      fun μ => if μ = 0 then deriv (bumpShift hε (ε / 2) φ 0) (x 0) • hvec h₀ else 0 := by
  have hd : DifferentiableAt ℝ (bumpShift hε (ε / 2) φ 0) (x 0) :=
    (hcφ.differentiable (by simp)).differentiableAt
  have hdv : DifferentiableAt ℝ (fun s => bumpShift hε (ε / 2) φ 0 s • hvec h₀) (x 0) :=
    hd.smul_const _
  have hder : deriv (fun s => bumpShift hε (ε / 2) φ 0 s • hvec h₀) (x 0) =
      deriv (bumpShift hε (ε / 2) φ 0) (x 0) • hvec h₀ :=
    (hd.hasDerivAt.smul_const (hvec h₀)).deriv
  funext μ
  show covDerivHiggs 0 (fun y : E4 => bumpShift hε (ε / 2) φ 0 (y 0) • hvec h₀) x μ = _
  simp only [covDerivHiggs, Pi.zero_apply, higgsAct_zero_left, add_zero]
  rw [pd_time hdv μ, hder]
  by_cases hμ : μ = 0 <;> simp [hμ]

theorem redJet_homConfig_Ψ (x : E4) : (redJet (homConfig FC hε a φ a₀ h₀) x).Ψ = 0 := rfl

theorem redJet_homConfig_dΨ (x : E4) : (redJet (homConfig FC hε a φ a₀ h₀) x).dΨ = 0 := by
  funext i; show pd (0 : E4 → SpinorFibre FC.C) i x = 0; simp [pd]

theorem redJet_homConfig_Ψb (x : E4) : (redJet (homConfig FC hε a φ a₀ h₀) x).Ψb = 0 := rfl

theorem redJet_homConfig_dΨb (x : E4) : (redJet (homConfig FC hε a φ a₀ h₀) x).dΨb = 0 := by
  funext i; show pd (0 : E4 → SpinorFibre FC.C) i x = 0; simp [pd]

end Jets

/-! ### Higgs-sector algebra -/

section HiggsAlg

theorem higgsAct_smul_real (X : LieFibre) (c : ℝ) (u : HiggsFibre) :
    higgsAct X (c • u) = c • higgsAct X u := by
  funext i
  simp only [higgsAct, Pi.smul_apply, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The gauge current vanishes** on a real multiple of a fixed Higgs direction:
`Re⟨u, ρ_H(X) u⟩ = 0` for `X ∈ 𝔰(𝔲(3)⊕𝔲(2))` (skew-Hermitian generators). -/
theorem hInnerReL_higgsAct_self {X : LieFibre} (hX : X ∈ smLie) (u : HiggsFibre) :
    hInnerReL u (higgsAct X u) = 0 := by
  have hs := hX.1
  set S : ℂ := ∑ i, star (u i) * ∑ j, X (Fin.natAdd 3 i) (Fin.natAdd 3 j) * u j with hSdef
  have hS : star S = -S := by
    simp only [hSdef, Fin.sum_univ_two, star_add, star_mul', star_star]
    have e00 := hs (Fin.natAdd 3 (0 : Fin 2)) (Fin.natAdd 3 (0 : Fin 2))
    have e01 := hs (Fin.natAdd 3 (0 : Fin 2)) (Fin.natAdd 3 (1 : Fin 2))
    have e10 := hs (Fin.natAdd 3 (1 : Fin 2)) (Fin.natAdd 3 (0 : Fin 2))
    have e11 := hs (Fin.natAdd 3 (1 : Fin 2)) (Fin.natAdd 3 (1 : Fin 2))
    have s00 : star (X (Fin.natAdd 3 (0 : Fin 2)) (Fin.natAdd 3 (0 : Fin 2))) = -X (Fin.natAdd 3 (0 : Fin 2)) (Fin.natAdd 3 (0 : Fin 2)) := by
      have h := e00; rw [eq_neg_iff_add_eq_zero] at h; rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    have s01 : star (X (Fin.natAdd 3 (0 : Fin 2)) (Fin.natAdd 3 (1 : Fin 2))) = -X (Fin.natAdd 3 (1 : Fin 2)) (Fin.natAdd 3 (0 : Fin 2)) := by
      rw [e10, star_neg, star_star]
    have s10 : star (X (Fin.natAdd 3 (1 : Fin 2)) (Fin.natAdd 3 (0 : Fin 2))) = -X (Fin.natAdd 3 (0 : Fin 2)) (Fin.natAdd 3 (1 : Fin 2)) := by
      rw [e01, star_neg, star_star]
    have s11 : star (X (Fin.natAdd 3 (1 : Fin 2)) (Fin.natAdd 3 (1 : Fin 2))) = -X (Fin.natAdd 3 (1 : Fin 2)) (Fin.natAdd 3 (1 : Fin 2)) := by
      have h := e11; rw [eq_neg_iff_add_eq_zero] at h; rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    rw [s00, s01, s10, s11]
    ring
  have hre : S.re = 0 := by
    have := congrArg Complex.re hS
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
    linarith
  simp only [hInnerReL, mkBilinL_apply]
  exact hre

theorem hInnerReL_hvec_self {h₀ : HiggsFibre} (hq : higgsQuad h₀ = 1) :
    hInnerReL (hvec h₀) (hvec h₀) = 1 / 2 := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hq' : hInnerReL h₀ h₀ = 1 := hq
  simp only [hvec, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hq']
  field_simp
  rw [h2]

end HiggsAlg

/-! ### Time derivatives along the solution -/

section ODE

variable {ε : ℝ} (hε : 0 < ε) {κ lamH vH : ℝ} {a φ π ℋ : ℝ → ℝ}

theorem slab_shift_mem {t : ℝ} (ht : t ∈ Ioo 0 ε) : t - ε / 2 ∈ Ioo (-ε) ε :=
  ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩

theorem hasDerivAt_shift {f : ℝ → ℝ} {f' t : ℝ} (h : HasDerivAt f f' (t - ε / 2)) :
    HasDerivAt (fun r => f (r - ε / 2)) f' t := by
  have h' : HasDerivAt f f' (id t - ε / 2) := h
  have := h'.comp t ((hasDerivAt_id t).sub_const (ε / 2))
  simp only [mul_one] at this
  exact this

/-- First derivatives of the bump extensions on the slab. -/
theorem deriv_bumpShift_eq (sol : HomogeneousEinsteinHiggs.IsSolution κ lamH vH a φ π ℋ
    (Ioo (-ε) ε)) (a₀ : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 ε) :
    HasDerivAt (bumpShift hε (ε / 2) a a₀) (a (t - ε / 2) * ℋ (t - ε / 2)) t ∧
      HasDerivAt (bumpShift hε (ε / 2) φ 0) (π (t - ε / 2)) t := by
  have hs := slab_shift_mem ht
  refine ⟨(hasDerivAt_shift (sol.a_deriv _ hs)).congr_of_eventuallyEq
      (bumpShift_eventuallyEq hε a a₀ ht),
    (hasDerivAt_shift (sol.φ_deriv _ hs)).congr_of_eventuallyEq
      (bumpShift_eventuallyEq hε φ 0 ht)⟩

/-- Second derivatives of the bump extensions on the slab. -/
theorem deriv2_bumpShift_eq (sol : HomogeneousEinsteinHiggs.IsSolution κ lamH vH a φ π ℋ
    (Ioo (-ε) ε)) (a₀ : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 ε) :
    HasDerivAt (deriv (bumpShift hε (ε / 2) a a₀))
        (a (t - ε / 2) * ℋ (t - ε / 2) * ℋ (t - ε / 2) +
          a (t - ε / 2) * (-(κ / 2) * π (t - ε / 2) ^ 2)) t ∧
      HasDerivAt (deriv (bumpShift hε (ε / 2) φ 0))
        (-3 * ℋ (t - ε / 2) * π (t - ε / 2) -
          HomogeneousEinsteinHiggs.higgsPotentialDeriv lamH vH (φ (t - ε / 2))) t := by
  have hs := slab_shift_mem ht
  have hU : Ioo (0 : ℝ) ε ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
  have ea : deriv (bumpShift hε (ε / 2) a a₀) =ᶠ[𝓝 t]
      fun r => a (r - ε / 2) * ℋ (r - ε / 2) := by
    filter_upwards [hU] with r hr using (deriv_bumpShift_eq hε sol a₀ hr).1.deriv
  have eφ : deriv (bumpShift hε (ε / 2) φ 0) =ᶠ[𝓝 t] fun r => π (r - ε / 2) := by
    filter_upwards [hU] with r hr using (deriv_bumpShift_eq hε sol a₀ hr).2.deriv
  refine ⟨?_, ?_⟩
  · have h := (hasDerivAt_shift (sol.a_deriv _ hs)).mul (hasDerivAt_shift (sol.ℋ_deriv _ hs))
    exact h.congr_of_eventuallyEq ea
  · exact (hasDerivAt_shift (sol.π_deriv _ hs)).congr_of_eventuallyEq eφ

end ODE

/-! ### The integrand is a divergence -/

section Divergence

variable {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec)

theorem pd_clm {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (L : F →L[ℝ] G) {f : E4 → F} {x : E4} (hf : DifferentiableAt ℝ f x)
    (i : Fin 4) : pd (fun y => L (f y)) i x = L (pd f i x) := by
  unfold pd
  rw [show (fun y => L (f y)) = L ∘ f from rfl, (L.hasFDerivAt.comp x hf.hasFDerivAt).fderiv]
  rfl

theorem pd_time_mul {c : ℝ → ℝ} {w : E4 → ℝ} {x : E4} (hc : DifferentiableAt ℝ c (x 0))
    (hw : DifferentiableAt ℝ w x) (i : Fin 4) :
    pd (fun y => c (y 0) * w y) i x =
      (if i = 0 then deriv c (x 0) else 0) * w x + c (x 0) * pd w i x := by
  have hcx : DifferentiableAt ℝ (fun y : E4 => c (y 0)) x :=
    hc.comp x (differentiableAt_apply 0 x)
  rw [pd_mul' hcx hw, pd_time hc i]
  by_cases hi : i = 0 <;> simp [hi]

/-- The divergence flux of the homogeneous critical point: the time component
`ã⁴ã'/κ (k₁₁ + k₂₂ + k₃₃) + 2ã³φ̃' Re⟨h₀/√2, η_H⟩` and the spatial components
`ã²ã'/(4κ) (k₀ⱼ + kⱼ₀)`. -/
def homFlux {ε : ℝ} (hε : 0 < ε) (θ : CoefficientBank Ysec) (a φ : ℝ → ℝ) (a₀ : ℝ)
    (h₀ : HiggsFibre) (v : FieldTuple FC.C) (i : Fin 4) (y : E4) : ℝ :=
  if i = 0 then
    bumpShift hε (ε / 2) a a₀ (y 0) ^ 4 * deriv (bumpShift hε (ε / 2) a a₀) (y 0) / θ.kappa *
        (v.e y 1 1 + v.e y 2 2 + v.e y 3 3) +
      2 * bumpShift hε (ε / 2) a a₀ (y 0) ^ 3 * deriv (bumpShift hε (ε / 2) φ 0) (y 0) *
        hInnerReL (hvec h₀) (v.H y)
  else
    bumpShift hε (ε / 2) a a₀ (y 0) ^ 2 * deriv (bumpShift hε (ε / 2) a a₀) (y 0) /
        (4 * θ.kappa) * (v.e y 0 i + v.e y i 0)

/-- **The algebraic core of the Euler–Lagrange identity** at the homogeneous configuration: the
covector integrand minus the divergence of the flux is `(a³k₀₀ - a⁵Σkᵢᵢ)/(2κ)` times the
Friedmann residual. -/
theorem homogeneous_EL_core (A H P Φ κ Λ lam vH k00 k11 k22 k33 d011 d022 d033 d101 d110 d202 d220
    d303 d330 eta deta : ℝ) (hκ : κ ≠ 0)
    (hF : 3 * H ^ 2 = Λ + κ * (P ^ 2 / 2 + lam * (Φ ^ 2 / 2 - vH ^ 2) ^ 2)) :
    (4 * κ)⁻¹ * (2 * (3 * A * (A * H) ^ 2 - Λ * A ^ 3) * k00 +
        2 * (7 * A ^ 3 * (A * H) ^ 2 + Λ * A ^ 5) * (k11 + k22 + k33) +
        4 * A ^ 4 * (A * H) * (d011 + d022 + d033) +
        A ^ 2 * (A * H) * (d101 + d110 + d202 + d220 + d303 + d330)) +
      (-k00 * A ^ 3 * (P ^ 2 / 2) + A ^ 3 * (k00 - A ^ 2 * (k11 + k22 + k33)) / 2 * (P ^ 2 / 2) +
        2 * A ^ 3 * (P * deta) -
        lam * (2 * (Φ ^ 2 / 2 - vH ^ 2) * (2 * (Φ * eta)) * A ^ 3 +
          (Φ ^ 2 / 2 - vH ^ 2) ^ 2 * (A ^ 3 * (k00 - A ^ 2 * (k11 + k22 + k33)) / 2))) =
    ((4 * A ^ 3 * (A * H) * (A * H) + A ^ 4 * (A * H * H + A * (-(κ / 2) * P ^ 2))) / κ *
        (k11 + k22 + k33) + A ^ 4 * (A * H) / κ * (d011 + d022 + d033) +
      ((6 * A ^ 2 * (A * H) * P + 2 * A ^ 3 * (-3 * H * P - 2 * lam * Φ * (Φ ^ 2 / 2 - vH ^ 2))) *
        eta + 2 * A ^ 3 * P * deta)) +
      A ^ 2 * (A * H) / (4 * κ) * (d101 + d110) + A ^ 2 * (A * H) / (4 * κ) * (d202 + d220) +
      A ^ 2 * (A * H) / (4 * κ) * (d303 + d330) := by
  linear_combination (norm := skip)
    (A ^ 3 * k00 / (2 * κ) - A ^ 5 * (k11 + k22 + k33) / (2 * κ)) * hF
  field_simp
  ring

theorem pd_add₂ {f g : E4 → ℝ} {x : E4} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd (fun y => f y + g y) i x = pd f i x + pd g i x := by
  unfold pd
  rw [show (fun y => f y + g y) = f + g from rfl, fderiv_add hf hg]
  rfl

/-- **Pointwise Euler–Lagrange identity**: on the open slab, the first-variation integrand of
the complete action (gravity + Yang–Mills + Higgs + Dirac–Yukawa covectors) at the homogeneous
configuration is the divergence of `homFlux`. -/
theorem integrand_eq_div (θ : CoefficientBank Ysec) (hκ : θ.kappa ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {a φ π ℋ : ℝ → ℝ} (a₀ : ℝ) (h₀ : HiggsFibre) (hq : higgsQuad h₀ = 1)
    (sol : HomogeneousEinsteinHiggs.IsSolution θ.kappa θ.lambdaH θ.vH a φ π ℋ (Ioo (-ε) ε))
    (hfr : ∀ s ∈ Ioo (-ε) ε, 3 * ℋ s ^ 2 = θ.Lambda + θ.kappa *
      (π s ^ 2 / 2 + HomogeneousEinsteinHiggs.higgsPotential θ.lambdaH θ.vH (φ s)))
    (hpos : ∀ s ∈ Ioo (-ε) ε, 0 < a s)
    (hga : ContDiff ℝ ∞ (bumpShift hε (ε / 2) a a₀))
    (hgφ : ContDiff ℝ ∞ (bumpShift hε (ε / 2) φ 0))
    {T : ℝ} {K : CylRegion T} (v : FieldTuple FC.C) (hv : v ∈ testSubmodule FC.left K)
    (x : E4) (hx : x 0 ∈ Ioo 0 ε) :
    gravCov θ (redJet (homConfig FC hε a φ a₀ h₀) x) (testJet v x) +
        (bosonCov θ (redJet (homConfig FC hε a φ a₀ h₀) x) +
          diracCov FC θ (redJet (homConfig FC hε a φ a₀ h₀) x)) (testJet v x) =
      ∑ i, pd (homFlux FC hε θ a φ a₀ h₀ v i) i x := by
  set ga := bumpShift hε (ε / 2) a a₀ with hgadef
  set gφ := bumpShift hε (ε / 2) φ 0 with hgφdef
  set z := homConfig FC hε a φ a₀ h₀
  set t := x 0 with htdef
  set s := t - ε / 2
  have hs : s ∈ Ioo (-ε) ε := slab_shift_mem hx
  have hnear : |t - ε / 2| ≤ ε / 2 := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hA : ga t = a s := bumpShift_eq_of_near hε (ε / 2) a a₀ hnear
  have hΦ : gφ t = φ s := bumpShift_eq_of_near hε (ε / 2) φ 0 hnear
  obtain ⟨hda, hdφ⟩ := deriv_bumpShift_eq hε sol a₀ hx
  obtain ⟨hdda, hddφ⟩ := deriv2_bumpShift_eq hε sol a₀ hx
  have hd1 : deriv ga t = a s * ℋ s := hda.deriv
  have hd2 : deriv gφ t = π s := hdφ.deriv
  have hapos : 0 < ga t := by rw [hA]; exact hpos s hs
  -- the covectors
  have hJe := redJet_homConfig_e FC hε a φ a₀ h₀ x
  have hJd := redJet_homConfig_de FC hε a φ a₀ h₀ hga x
  have hJK := redJet_homConfig_K FC hε a φ a₀ h₀ hgφ x
  have hGL : (redJet z x).e ∈ coframeGL := by rw [hJe]; exact frameDiag_mem_GL hapos.ne'
  rw [gravCov_flrw θ hapos _ hJe hJd, ContinuousLinearMap.add_apply,
    bosonCov_flrw θ hapos hJe (redJet_homConfig_A FC hε a φ a₀ h₀ x)
      (redJet_homConfig_F FC hε a φ a₀ h₀ x) _ hJK,
    diracCov_zero FC θ hGL (redJet_homConfig_Ψ FC hε a φ a₀ h₀ x)
      (redJet_homConfig_dΨ FC hε a φ a₀ h₀ x) (redJet_homConfig_Ψb FC hε a φ a₀ h₀ x)
      (redJet_homConfig_dΨb FC hε a φ a₀ h₀ x), add_zero, redJet_homConfig_H]
  -- the test jet
  obtain ⟨hve, hvA, hvH, -, -, -, hlie, -, -⟩ := hv
  have hde : DifferentiableAt ℝ v.e x := (hve.smooth.differentiable (by simp)) x
  have hdH : DifferentiableAt ℝ v.H x := (hvH.smooth.differentiable (by simp)) x
  have hdent : ∀ i j, DifferentiableAt ℝ (fun y => v.e y i j) x := fun i j =>
    differentiableAt_apply₂ hde i j
  simp only [testJet, RJet.mk_e, RJet.mk_de, RJet.mk_A, RJet.mk_H, RJet.mk_K]
  -- the Higgs inner products
  set hv := hvec h₀
  have hvv : hInnerReL hv hv = 1 / 2 := hInnerReL_hvec_self hq
  have hgauge : hInnerReL hv (higgsAct (v.A x 0) hv) = 0 :=
    hInnerReL_higgsAct_self (hlie x 0) hv
  have hq1 : hInnerReL (deriv gφ t • hv) (deriv gφ t • hv) = deriv gφ t ^ 2 / 2 := by
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hvv]; ring
  have hq2 : hInnerReL (deriv gφ t • hv) (pd v.H 0 x + higgsAct (v.A x 0) (gφ t • hv)) =
      deriv gφ t * hInnerReL hv (pd v.H 0 x) := by
    simp only [map_smul, map_add, ContinuousLinearMap.smul_apply, smul_eq_mul,
      higgsAct_smul_real, hgauge]
    ring
  have hq3 : higgsQuad (gφ t • hv) = gφ t ^ 2 / 2 := by
    simp only [higgsQuad, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hvv]; ring
  have hq4 : hInnerReL (v.H x) (gφ t • hv) = gφ t * hInnerReL hv (v.H x) := by
    rw [hInnerReL_comm]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hq1, hq2, hq3, hq4]
  -- the divergence of the flux
  have hgad : ∀ r, DifferentiableAt ℝ ga r := fun r => (hga.differentiable (by simp)) r
  have hgφd : ∀ r, DifferentiableAt ℝ gφ r := fun r => (hgφ.differentiable (by simp)) r
  have hgad' : ∀ r, DifferentiableAt ℝ (deriv ga) r := fun r =>
    ((hga.iterate_deriv 1).differentiable (by simp)) r
  have hgφd' : ∀ r, DifferentiableAt ℝ (deriv gφ) r := fun r =>
    ((hgφ.iterate_deriv 1).differentiable (by simp)) r
  have hc1 : HasDerivAt (fun r => ga r ^ 4 * deriv ga r / θ.kappa)
      ((4 * ga t ^ 3 * deriv ga t * deriv ga t +
        ga t ^ 4 * (a s * ℋ s * ℋ s + a s * (-(θ.kappa / 2) * π s ^ 2))) / θ.kappa) t := by
    have := (((hgad t).hasDerivAt.pow 4).mul hdda).div_const θ.kappa
    refine this.congr_deriv ?_
    simp only [Pi.pow_apply]
    push_cast; ring
  have hc4 : HasDerivAt (fun r => 2 * ga r ^ 3 * deriv gφ r)
      (6 * ga t ^ 2 * deriv ga t * deriv gφ t + 2 * ga t ^ 3 * (-3 * ℋ s * π s -
        HomogeneousEinsteinHiggs.higgsPotentialDeriv θ.lambdaH θ.vH (φ s))) t := by
    have := (((hgad t).hasDerivAt.pow 3).const_mul 2).mul hddφ
    refine this.congr_deriv ?_
    simp only [Pi.pow_apply]
    push_cast; ring
  have hf0 : homFlux FC hε θ a φ a₀ h₀ v 0 = fun y =>
      (fun r => ga r ^ 4 * deriv ga r / θ.kappa) (y 0) * (v.e y 1 1 + v.e y 2 2 + v.e y 3 3) +
        (fun r => 2 * ga r ^ 3 * deriv gφ r) (y 0) * hInnerReL hv (v.H y) := by
    funext y; simp [homFlux, hgadef, hgφdef, hv]
  have hfj : ∀ j : Fin 4, j ≠ 0 → homFlux FC hε θ a φ a₀ h₀ v j = fun y =>
      (fun r => ga r ^ 2 * deriv ga r / (4 * θ.kappa)) (y 0) * (v.e y 0 j + v.e y j 0) := by
    intro j hj; funext y; simp [homFlux, hj, hgadef]
  have hw1 : DifferentiableAt ℝ (fun y => v.e y 1 1 + v.e y 2 2 + v.e y 3 3) x :=
    ((hdent 1 1).add (hdent 2 2)).add (hdent 3 3)
  have hw2 : DifferentiableAt ℝ (fun y => hInnerReL hv (v.H y)) x :=
    (hInnerReL hv).differentiableAt.comp x hdH
  have hcd1 : DifferentiableAt ℝ (fun r => ga r ^ 4 * deriv ga r / θ.kappa) t :=
    hc1.differentiableAt
  have hcd4 : DifferentiableAt ℝ (fun r => 2 * ga r ^ 3 * deriv gφ r) t := hc4.differentiableAt
  have hcd2 : DifferentiableAt ℝ (fun r => ga r ^ 2 * deriv ga r / (4 * θ.kappa)) t :=
    (((hgad t).pow 2).mul (hgad' t)).div_const _
  have hcd1x : DifferentiableAt ℝ (fun y : E4 => (fun r => ga r ^ 4 * deriv ga r / θ.kappa) (y 0))
      x := DifferentiableAt.comp (g := fun r => ga r ^ 4 * deriv ga r / θ.kappa) x hcd1
        (differentiableAt_apply 0 x)
  have hcd4x : DifferentiableAt ℝ (fun y : E4 => (fun r => 2 * ga r ^ 3 * deriv gφ r) (y 0))
      x := DifferentiableAt.comp (g := fun r => 2 * ga r ^ 3 * deriv gφ r) x hcd4
        (differentiableAt_apply 0 x)
  have hpd0 : pd (homFlux FC hε θ a φ a₀ h₀ v 0) 0 x =
      ((4 * ga t ^ 3 * deriv ga t * deriv ga t +
        ga t ^ 4 * (a s * ℋ s * ℋ s + a s * (-(θ.kappa / 2) * π s ^ 2))) / θ.kappa) *
          (v.e x 1 1 + v.e x 2 2 + v.e x 3 3) +
        ga t ^ 4 * deriv ga t / θ.kappa *
          (pd v.e 0 x 1 1 + pd v.e 0 x 2 2 + pd v.e 0 x 3 3) +
        ((6 * ga t ^ 2 * deriv ga t * deriv gφ t + 2 * ga t ^ 3 * (-3 * ℋ s * π s -
          HomogeneousEinsteinHiggs.higgsPotentialDeriv θ.lambdaH θ.vH (φ s))) *
            hInnerReL hv (v.H x) + 2 * ga t ^ 3 * deriv gφ t * hInnerReL hv (pd v.H 0 x)) := by
    rw [hf0, pd_add₂
        (f := fun y => (fun r => ga r ^ 4 * deriv ga r / θ.kappa) (y 0) *
          (v.e y 1 1 + v.e y 2 2 + v.e y 3 3))
        (g := fun y => (fun r => 2 * ga r ^ 3 * deriv gφ r) (y 0) * hInnerReL hv (v.H y))
        (hcd1x.mul hw1) (hcd4x.mul hw2),
      pd_time_mul hcd1 hw1, pd_time_mul hcd4 hw2, if_pos rfl, if_pos rfl, hc1.deriv, hc4.deriv,
      pd_add₂ (f := fun y => v.e y 1 1 + v.e y 2 2) (g := fun y => v.e y 3 3)
        ((hdent 1 1).add (hdent 2 2)) (hdent 3 3),
      pd_add₂ (f := fun y => v.e y 1 1) (g := fun y => v.e y 2 2) (hdent 1 1) (hdent 2 2),
      pd_apply₂ hde, pd_apply₂ hde, pd_apply₂ hde, pd_clm (hInnerReL hv) hdH]
  have hpdj : ∀ j : Fin 4, j ≠ 0 → pd (homFlux FC hε θ a φ a₀ h₀ v j) j x =
      ga t ^ 2 * deriv ga t / (4 * θ.kappa) * (pd v.e j x 0 j + pd v.e j x j 0) := by
    intro j hj
    rw [hfj j hj, pd_time_mul (w := fun y => v.e y 0 j + v.e y j 0) hcd2
        ((hdent 0 j).add (hdent j 0)), if_neg hj,
      pd_add₂ (f := fun y => v.e y 0 j) (g := fun y => v.e y j 0) (hdent 0 j) (hdent j 0),
      pd_apply₂ hde, pd_apply₂ hde]
    ring
  rw [Fin.sum_univ_four, hpd0, hpdj 1 (by decide), hpdj 2 (by decide), hpdj 3 (by decide)]
  -- substitute the solution and close by the Friedmann constraint
  rw [hA, hd1, hd2, hΦ]
  have hF := hfr s hs
  simp only [HomogeneousEinsteinHiggs.higgsPotential, HomogeneousEinsteinHiggs.higgsPotentialDeriv]
    at hF ⊢
  have := homogeneous_EL_core (a s) (ℋ s) (π s) (φ s) θ.kappa θ.Lambda θ.lambdaH θ.vH
    (v.e x 0 0) (v.e x 1 1) (v.e x 2 2) (v.e x 3 3) (pd v.e 0 x 1 1) (pd v.e 0 x 2 2)
    (pd v.e 0 x 3 3) (pd v.e 1 x 0 1) (pd v.e 1 x 1 0) (pd v.e 2 x 0 2) (pd v.e 2 x 2 0)
    (pd v.e 3 x 0 3) (pd v.e 3 x 3 0) (hInnerReL hv (v.H x)) (hInnerReL hv (pd v.H 0 x)) hκ hF
  linear_combination this

end Divergence

/-! ### Criticality -/

section Critical

variable {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec)

theorem test_eq_zero_of_time {T : ℝ} {K : CylRegion T} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E4 → F} (hf : IsCylTest K f) {t₀ t₁ : ℝ}
    (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) {x : E4} (hx : x 0 = t₀ ∨ x 0 = t₁) : f x = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun hxs => ?_
  have hmem := hK _ (hf.support hxs)
  have : (cylProj x).1 = x 0 := rfl
  rw [this] at hmem
  rcases hx with h | h <;> rw [h] at hmem
  · exact lt_irrefl _ hmem.1
  · exact lt_irrefl _ hmem.2

/-- **`prop:homogeneous`, criticality**: the translated homogeneous Einstein–Higgs configuration is
a critical point of the library's continuum action on the whole comparison cylinder
`M = (0, ε) × 𝕋³`: `Σ_b D𝒮_{b,θ}(z_*)[v] = 0` for every `K ⋐ M` and every `v ∈ 𝒱_K`. -/
theorem homConfig_critical (θ : CoefficientBank Ysec) (hκ : θ.kappa ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {a φ π ℋ : ℝ → ℝ} {a₀ : ℝ} (h₀ : HiggsFibre) (hq : higgsQuad h₀ = 1)
    (sol : HomogeneousEinsteinHiggs.IsSolution θ.kappa θ.lambdaH θ.vH a φ π ℋ (Ioo (-ε) ε))
    (hfr : ∀ s ∈ Ioo (-ε) ε, 3 * ℋ s ^ 2 = θ.Lambda + θ.kappa *
      (π s ^ 2 / 2 + HomogeneousEinsteinHiggs.higgsPotential θ.lambdaH θ.vH (φ s)))
    (hpos : ∀ s ∈ Ioo (-ε) ε, 0 < a s)
    (hga : ContDiff ℝ ∞ (bumpShift hε (ε / 2) a a₀))
    (hgφ : ContDiff ℝ ∞ (bumpShift hε (ε / 2) φ 0))
    (hgapos : ∀ t, 0 < bumpShift hε (ε / 2) a a₀ t)
    (zs : SmoothFields ε FC.left) (hz : zs.z = homConfig FC hε a φ a₀ h₀)
    {Kf : Set CoframeFibre} (hKf : IsCompact Kf) (hKfC : Kf ⊆ coframeChart)
    (hchart : ∀ y, zs.z.e y ∈ Kf) (K : CylRegion ε) (v : FieldTuple FC.C)
    (hv : v ∈ testSubmodule FC.left K) :
    ∑ b, firstVariation ε FC θ b zs.z v = 0 := by
  obtain ⟨t₀, t₁, h0, h01, h1, hK⟩ := K.exists_slab_Ioo hε
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := ε)
  set w : CrTest FC.left 0 K := ⟨v, hv⟩
  have hKGL : Kf ⊆ coframeGL := hKfC.trans coframeChart_subset_GL
  have hG := gravVariation_eq_cov FC θ h0 h01 h1 hK zs w hKf hKGL (fun x _ => hchart x)
  have hS := smVariation_eq_cov FC θ h0 h01 h1 (fun p hp => Ioo_subset_Icc_self (hK p hp)) zs w
    hKf hKGL (fun x _ => hchart x)
  rw [show w.val = v from rfl] at hG hS
  rw [sum_sector_real, hG, hS]
  rw [hz]
  set z := homConfig FC hε a φ a₀ h₀
  set ga := bumpShift hε (ε / 2) a a₀ with hgadef
  set gφ := bumpShift hε (ε / 2) φ 0 with hgφdef
  have hvmem := hv
  obtain ⟨hve, hvA, hvH, -, -, -, hlie, -, -⟩ := hv
  -- explicit forms of the covector integrands (valid at every point)
  have hJe := redJet_homConfig_e FC hε a φ a₀ h₀
  have hJd := redJet_homConfig_de FC hε a φ a₀ h₀ hga
  have hJK := redJet_homConfig_K FC hε a φ a₀ h₀ hgφ
  have hGform : ∀ x, gravCov θ (redJet z x) (testJet v x) =
      (4 * θ.kappa)⁻¹ * (2 * (3 * ga (x 0) * deriv ga (x 0) ^ 2 - θ.Lambda * ga (x 0) ^ 3) *
          v.e x 0 0 +
        2 * (7 * ga (x 0) ^ 3 * deriv ga (x 0) ^ 2 + θ.Lambda * ga (x 0) ^ 5) *
          (v.e x 1 1 + v.e x 2 2 + v.e x 3 3) +
        4 * ga (x 0) ^ 4 * deriv ga (x 0) *
          (pd v.e 0 x 1 1 + pd v.e 0 x 2 2 + pd v.e 0 x 3 3) +
        ga (x 0) ^ 2 * deriv ga (x 0) * (pd v.e 1 x 0 1 + pd v.e 1 x 1 0 + pd v.e 2 x 0 2 +
          pd v.e 2 x 2 0 + pd v.e 3 x 0 3 + pd v.e 3 x 3 0)) := fun x =>
    gravCov_flrw θ (hgapos (x 0)) _ (hJe x) (hJd x) (testJet v x)
  have hSform : ∀ x, (bosonCov θ (redJet z x) + diracCov FC θ (redJet z x)) (testJet v x) =
      -(v.e x 0 0) * ga (x 0) ^ 3 *
          hInnerReL (deriv gφ (x 0) • hvec h₀) (deriv gφ (x 0) • hvec h₀) +
        ga (x 0) ^ 3 * (v.e x 0 0 - ga (x 0) ^ 2 * (v.e x 1 1 + v.e x 2 2 + v.e x 3 3)) / 2 *
          hInnerReL (deriv gφ (x 0) • hvec h₀) (deriv gφ (x 0) • hvec h₀) +
        2 * ga (x 0) ^ 3 * hInnerReL (deriv gφ (x 0) • hvec h₀)
          (pd v.H 0 x + higgsAct (v.A x 0) (gφ (x 0) • hvec h₀)) -
        θ.lambdaH * (2 * (higgsQuad (gφ (x 0) • hvec h₀) - θ.vH ^ 2) *
            (2 * hInnerReL (v.H x) (gφ (x 0) • hvec h₀)) * ga (x 0) ^ 3 +
          (higgsQuad (gφ (x 0) • hvec h₀) - θ.vH ^ 2) ^ 2 *
            (ga (x 0) ^ 3 * (v.e x 0 0 - ga (x 0) ^ 2 * (v.e x 1 1 + v.e x 2 2 + v.e x 3 3)) /
              2)) := by
    intro x
    have hGL : (redJet z x).e ∈ coframeGL := by
      rw [hJe x]; exact frameDiag_mem_GL (hgapos (x 0)).ne'
    rw [ContinuousLinearMap.add_apply,
      bosonCov_flrw θ (hgapos (x 0)) (hJe x) (redJet_homConfig_A FC hε a φ a₀ h₀ x)
        (redJet_homConfig_F FC hε a φ a₀ h₀ x) _ (hJK x),
      diracCov_zero FC θ hGL (redJet_homConfig_Ψ FC hε a φ a₀ h₀ x)
        (redJet_homConfig_dΨ FC hε a φ a₀ h₀ x) (redJet_homConfig_Ψb FC hε a φ a₀ h₀ x)
        (redJet_homConfig_dΨb FC hε a φ a₀ h₀ x), add_zero, redJet_homConfig_H]
    rfl
  -- continuity of the pieces
  have hc0 : Continuous ga := hga.continuous
  have hc1 : Continuous (deriv ga) := (hga.iterate_deriv 1).continuous
  have hc2 : Continuous gφ := hgφ.continuous
  have hc3 : Continuous (deriv gφ) := (hgφ.iterate_deriv 1).continuous
  have hce : ∀ i j, Continuous fun x => v.e x i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hve.smooth.continuous)
  have hcpe : ∀ c i j, Continuous fun x => pd v.e c x i j := fun c i j =>
    (continuous_apply j).comp ((continuous_apply i).comp
      (SobolevOpen.continuous_pd (hve.smooth.of_le (by simp)) c))
  have hcH : Continuous v.H := hvH.smooth.continuous
  have hcpH : Continuous fun x => pd v.H 0 x :=
    SobolevOpen.continuous_pd (hvH.smooth.of_le (by simp)) 0
  have hcA : Continuous fun x => v.A x 0 :=
    (continuous_apply 0).comp hvA.smooth.continuous
  have hct : Continuous fun x : E4 => x 0 := continuous_apply 0
  have hcgaT : Continuous fun x : E4 => ga (x 0) := hc0.comp hct
  have hcgaT' : Continuous fun x : E4 => deriv ga (x 0) := hc1.comp hct
  have hcgφT : Continuous fun x : E4 => gφ (x 0) := hc2.comp hct
  have hcgφT' : Continuous fun x : E4 => deriv gφ (x 0) := hc3.comp hct
  have hcHA : Continuous fun x : E4 => higgsAct (v.A x 0) (gφ (x 0) • hvec h₀) := by
    have hc : Continuous fun p : LieFibre × HiggsFibre => higgsAct p.1 p.2 := by
      unfold higgsAct; fun_prop
    exact hc.comp (hcA.prodMk (hcgφT.smul continuous_const))
  have hGcont : Continuous fun x => gravCov θ (redJet z x) (testJet v x) := by
    simp only [hGform]
    have := hce 0 0; have := hce 1 1; have := hce 2 2; have := hce 3 3
    have := hcpe 0 1 1; have := hcpe 0 2 2; have := hcpe 0 3 3; have := hcpe 1 0 1
    have := hcpe 1 1 0; have := hcpe 2 0 2; have := hcpe 2 2 0; have := hcpe 3 0 3
    have := hcpe 3 3 0
    fun_prop
  have hScont : Continuous fun x =>
      (bosonCov θ (redJet z x) + diracCov FC θ (redJet z x)) (testJet v x) := by
    simp only [hSform]
    have := hce 0 0; have := hce 1 1; have := hce 2 2; have := hce 3 3
    have hq : Continuous fun x : E4 => higgsQuad (gφ (x 0) • hvec h₀) := by
      unfold higgsQuad; fun_prop
    fun_prop
  have hQc := isCompact_closure_slabChart h0 h01 h1 (T := ε)
  have hGi : IntegrableOn (fun x => gravCov θ (redJet z x) (testJet v x)) Q.set :=
    (hGcont.continuousOn.integrableOn_compact hQc).mono_set subset_closure
  have hSi : IntegrableOn (fun x =>
      (bosonCov θ (redJet z x) + diracCov FC θ (redJet z x)) (testJet v x)) Q.set :=
    (hScont.continuousOn.integrableOn_compact hQc).mono_set subset_closure
  rw [← integral_add hGi hSi]
  -- the integrand is a divergence on the slab box
  have hQm : MeasurableSet Q.set := (SobolevOpen.isOpen_box Q.a Q.b).measurableSet
  rw [setIntegral_congr_fun hQm fun x hx => integrand_eq_div FC θ hκ hε a₀ h₀ hq sol hfr hpos
    hga hgφ v hvmem x (by
      have := (mem_slabChart.mp hx).1
      exact ⟨h0.trans this.1, this.2.trans h1⟩)]
  -- the divergence theorem
  have hfl : ∀ i, ContDiff ℝ 1 (homFlux FC hε θ a φ a₀ h₀ v i) := by
    intro i
    have hga1 : ContDiff ℝ 1 ga := hga.of_le (by simp)
    have hgad1 : ContDiff ℝ 1 (deriv ga) := (hga.iterate_deriv 1).of_le (by simp)
    have hgφd1 : ContDiff ℝ 1 (deriv gφ) := (hgφ.iterate_deriv 1).of_le (by simp)
    have hve1 : ContDiff ℝ 1 v.e := hve.smooth.of_le (by simp)
    have hvH1 : ContDiff ℝ 1 v.H := hvH.smooth.of_le (by simp)
    have hent : ∀ i j, ContDiff ℝ 1 fun y => v.e y i j := fun i j =>
      (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin 4 → ℝ) i).comp hve1)
    have hT : ContDiff ℝ 1 fun y : E4 => y 0 := contDiff_apply ℝ ℝ 0
    have hηr : ContDiff ℝ 1 fun y => hInnerReL (hvec h₀) (v.H y) :=
      (hInnerReL (hvec h₀)).contDiff.comp hvH1
    by_cases hi : i = 0
    · subst hi
      have := hent 1 1; have := hent 2 2; have := hent 3 3
      have e1 : ContDiff ℝ 1 fun y : E4 => ga (y 0) := hga1.comp hT
      have e2 : ContDiff ℝ 1 fun y : E4 => deriv ga (y 0) := hgad1.comp hT
      have e3 : ContDiff ℝ 1 fun y : E4 => deriv gφ (y 0) := hgφd1.comp hT
      have hf : homFlux FC hε θ a φ a₀ h₀ v 0 = fun y =>
          ga (y 0) ^ 4 * deriv ga (y 0) / θ.kappa * (v.e y 1 1 + v.e y 2 2 + v.e y 3 3) +
            2 * ga (y 0) ^ 3 * deriv gφ (y 0) * hInnerReL (hvec h₀) (v.H y) := by
        funext y; simp [homFlux, hgadef, hgφdef]
      rw [hf]
      fun_prop
    · have := hent 0 i; have := hent i 0
      have e1 : ContDiff ℝ 1 fun y : E4 => ga (y 0) := hga1.comp hT
      have e2 : ContDiff ℝ 1 fun y : E4 => deriv ga (y 0) := hgad1.comp hT
      have hf : homFlux FC hε θ a φ a₀ h₀ v i = fun y =>
          ga (y 0) ^ 2 * deriv ga (y 0) / (4 * θ.kappa) * (v.e y 0 i + v.e y i 0) := by
        funext y; simp [homFlux, hi, hgadef]
      rw [hf]
      fun_prop
  refine integral_div_slab_eq_zero h0 h01 h1 isOpen_univ (subset_univ _)
    (fun i => (hfl i).contDiffOn) (fun x hx => ?_) (fun j x => ?_)
  · have he0 : v.e x = 0 := test_eq_zero_of_time hve hK hx
    have hH0 : v.H x = 0 := test_eq_zero_of_time hvH hK hx
    simp [homFlux, he0, hH0]
  · have hj : (j.succ : Fin 4) ≠ 0 := Fin.succ_ne_zero j
    simp only [homFlux, hj, if_false, Pi.add_apply, spatialShift_zero, add_zero,
      hve.periodic]

end Critical

/-! ### `prop:homogeneous`: the closed statement -/

section Main

variable {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec)

/-- **`prop:homogeneous` (critical comparison member).**  Let `κ = θ.kappa ≠ 0`, `λ_H`, `v_H`,
`Λ` be the couplings of the bank `θ`, `h₀` a unit Higgs vector, and `(a₀ > 0, φ₀, π₀, ℋ₀)` initial
data satisfying the Friedmann constraint `eq:Friedmann-initial`.  Then `eq:homogeneous-ODE` has a
smooth local solution on `(-ε, ε)` with `a > 0` and the given initial data, and the fields
`eq:homogeneous-fields` built from it on the slab `[-ε/2, ε/2]`, translated to the comparison
cylinder `M = (0, ε) × 𝕋³` (and extended by a smooth cut-off outside the closed slab), form a
smooth configuration of the sampled `C^{1,1}` class with coframe in a compact subset of the chart
which is a **critical point of the continuum Einstein–Standard-Model action**:
`Σ_b D𝒮_{b,θ}(z_*)[v] = 0` for every `K ⋐ M` and every physical test `v ∈ 𝒱_K`. -/
theorem homogeneous_critical_member (θ : CoefficientBank Ysec) (hκ : θ.kappa ≠ 0)
    (a₀ φ₀ π₀ H₀ : ℝ) (ha₀ : 0 < a₀) (h₀ : HiggsFibre) (hq : higgsQuad h₀ = 1)
    (hF : 3 * H₀ ^ 2 = θ.Lambda + θ.kappa *
      (π₀ ^ 2 / 2 + HomogeneousEinsteinHiggs.higgsPotential θ.lambdaH θ.vH φ₀)) :
    ∃ (ε : ℝ) (_ : 0 < ε) (a φ π ℋ : ℝ → ℝ),
      a 0 = a₀ ∧ φ 0 = φ₀ ∧ π 0 = π₀ ∧ ℋ 0 = H₀ ∧
      HomogeneousEinsteinHiggs.IsSolution θ.kappa θ.lambdaH θ.vH a φ π ℋ (Ioo (-ε) ε) ∧
      (∀ t ∈ Ioo (-ε) ε, 0 < a t) ∧
      ∃ (zs : SmoothFields ε FC.left) (B : ℝ) (Kf : Set CoframeFibre),
        0 ≤ B ∧ IsCompact Kf ∧ Kf ⊆ coframeChart ∧ SampledFamily FC B Kf zs.z ∧
        (∀ x : E4, x 0 ∈ Icc 0 ε →
          zs.z.e x = frameDiag (a (x 0 - ε / 2)) ∧
          zs.z.H x = (φ (x 0 - ε / 2) / Real.sqrt 2) • h₀ ∧
          zs.z.A x = 0 ∧ zs.z.Ψ x = 0 ∧ zs.z.Ψb x = 0) ∧
        ∀ (K : CylRegion ε), ∀ v ∈ testSubmodule FC.left K,
          ∑ b, firstVariation ε FC θ b zs.z v = 0 := by
  obtain ⟨ε, hε, a, φ, π, ℋ, h1, h2, h3, h4, sol, hpos, hca, hcφ, -, -⟩ :=
    HomogeneousEinsteinHiggs.exists_local_solution θ.kappa θ.lambdaH θ.vH a₀ φ₀ π₀ H₀ ha₀
  have hfr : ∀ s ∈ Ioo (-ε) ε, 3 * ℋ s ^ 2 = θ.Lambda + θ.kappa *
      (π s ^ 2 / 2 + HomogeneousEinsteinHiggs.higgsPotential θ.lambdaH θ.vH (φ s)) :=
    HomogeneousEinsteinHiggs.friedmann_constraint_propagates hε sol θ.Lambda
      (by rw [h2, h3, h4]; exact hF)
  obtain ⟨zs, B, Kf, hz, hB, hKf, hKfC, hfam, hgapos⟩ :=
    homConfig_sampled FC hε ha₀ h₀ hca hcφ hpos
  refine ⟨ε, hε, a, φ, π, ℋ, h1, h2, h3, h4, sol, hpos, zs, B, Kf, hB, hKf, hKfC, hfam,
    fun x hx => ?_, fun K v hv => ?_⟩
  · have hnear : |x 0 - ε / 2| ≤ ε / 2 := by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    rw [hz]
    refine ⟨?_, ?_, rfl, rfl, rfl⟩
    · rw [homConfig_e, bumpShift_eq_of_near hε (ε / 2) a a₀ hnear]
    · rw [homConfig_H, bumpShift_eq_of_near hε (ε / 2) φ 0 hnear, hvec, smul_smul]
      congr 1; field_simp
  · exact homConfig_critical FC θ hκ hε h₀ hq sol hfr hpos
      (contDiff_bumpShift hε (ε / 2) hca a₀) (contDiff_bumpShift hε (ε / 2) hcφ 0) hgapos zs hz
      hKf hKfC hfam.chart K v hv

/-- **`prop:homogeneous`, closing sentence ("smooth sampling yields the finite residual conclusion
of `prop:smooth-sampling`")**: for a physical bank and the critical homogeneous configuration of
`homogeneous_critical_member`, on every test region `K ⋐ M` (time support in `(t₀, t₁)`),
`c_h(K) = O(h)`, `d_K(z_h, z_*) = O(h)` and `ε_h(K) = O(h)` — the last one unconditionally. -/
theorem homogeneous_smooth_sampling_closed [Nonempty FC.C] (θ : CoefficientBank Ysec)
    (hθ : θ ∈ physicalBanks) (a₀ φ₀ π₀ H₀ : ℝ) (ha₀ : 0 < a₀) (h₀ : HiggsFibre)
    (hq : higgsQuad h₀ = 1)
    (hF : 3 * H₀ ^ 2 = θ.Lambda + θ.kappa *
      (π₀ ^ 2 / 2 + HomogeneousEinsteinHiggs.higgsPotential θ.lambdaH θ.vH φ₀)) :
    ∃ (ε : ℝ) (_ : 0 < ε) (a φ π ℋ : ℝ → ℝ),
      a 0 = a₀ ∧ φ 0 = φ₀ ∧ π 0 = π₀ ∧ ℋ 0 = H₀ ∧
      HomogeneousEinsteinHiggs.IsSolution θ.kappa θ.lambdaH θ.vH a φ π ℋ (Ioo (-ε) ε) ∧
      ∃ (zs : SmoothFields ε FC.left) (B : ℝ) (Kf : Set CoframeFibre)
        (hzs : SampledFamily FC B Kf zs.z),
        (∀ x : E4, x 0 ∈ Icc 0 ε →
          zs.z.e x = frameDiag (a (x 0 - ε / 2)) ∧
          zs.z.H x = (φ (x 0 - ε / 2) / Real.sqrt 2) • h₀ ∧
          zs.z.A x = 0 ∧ zs.z.Ψ x = 0 ∧ zs.z.Ψb x = 0) ∧
        ∀ (t₀ t₁ : ℝ) (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < ε) (K : CylRegion ε)
          (_ : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) (P : ℕ) (_ : ε ≤ P) (r₀ : ℕ) (_ : 2 ≤ r₀),
          ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ (N : ℕ) (_ : N₀ ≤ N) (hN : 0 < N),
            comparisonDefect FC ε θ P N r₀ K (sampleRec FC (1 / N) zs.z) ≤
                ENNReal.ofReal (C * (1 / N)) ∧
              dK (slabChart t₀ t₁ h0 h01 h1 (T := ε)) (reconSmooth FC ε hN hzs) θ zs θ ≤
                ENNReal.ofReal (C * (1 / N)) ∧
              comparisonStationarity FC ε θ P N r₀ K (sampleRec FC (1 / N) zs.z) ≤
                ENNReal.ofReal (C * (1 / N)) := by
  obtain ⟨ε, hε, a, φ, π, ℋ, h1, h2, h3, h4, sol, -, zs, B, Kf, hB, hKf, hKfC, hzs, heq, hcrit⟩ :=
    homogeneous_critical_member FC θ hθ.1.ne' a₀ φ₀ π₀ H₀ ha₀ h₀ hq hF
  refine ⟨ε, hε, a, φ, π, ℋ, h1, h2, h3, h4, sol, zs, B, Kf, hzs, heq,
    fun t₀ t₁ h0 h01 h1 K hK P hTP r₀ hr => ?_⟩
  obtain ⟨C, hC, N₀, hss⟩ := smooth_sampling FC θ hθ h0 h01 h1 hK hTP hr hB hKf hKfC
  refine ⟨C, hC, N₀, fun N hN₀ hN => ?_⟩
  obtain ⟨c1, c2, c3⟩ := hss zs hzs N hN₀ hN
  exact ⟨c1, c2, c3 (hcrit K)⟩

/-- Non-vacuity: a unit Higgs vector exists. -/
theorem exists_unit_higgs : ∃ h₀ : HiggsFibre, higgsQuad h₀ = 1 :=
  ⟨![1, 0], by simp [higgsQuad_eq, Fin.sum_univ_two]⟩

/-- Non-vacuity: Friedmann initial data exist for every physical bank with `Λ ≥ 0` (take
`ℋ₀ = √((Λ + κ(π₀²/2 + U(φ₀)))/3)`). -/
theorem exists_friedmann_data (θ : CoefficientBank Ysec) (hθ : θ ∈ physicalBanks)
    (hΛ : 0 ≤ θ.Lambda) (φ₀ π₀ : ℝ) :
    ∃ H₀ : ℝ, 3 * H₀ ^ 2 = θ.Lambda + θ.kappa *
      (π₀ ^ 2 / 2 + HomogeneousEinsteinHiggs.higgsPotential θ.lambdaH θ.vH φ₀) := by
  have hU : 0 ≤ HomogeneousEinsteinHiggs.higgsPotential θ.lambdaH θ.vH φ₀ := by
    unfold HomogeneousEinsteinHiggs.higgsPotential
    exact mul_nonneg hθ.2.2.2.2.le (sq_nonneg _)
  have hr : 0 ≤ (θ.Lambda + θ.kappa *
      (π₀ ^ 2 / 2 + HomogeneousEinsteinHiggs.higgsPotential θ.lambdaH θ.vH φ₀)) / 3 := by
    have := hθ.1.le
    positivity
  refine ⟨Real.sqrt ((θ.Lambda + θ.kappa *
      (π₀ ^ 2 / 2 + HomogeneousEinsteinHiggs.higgsPotential θ.lambdaH θ.vH φ₀)) / 3), ?_⟩
  rw [Real.sq_sqrt hr]
  ring


/-- Non-vacuity of `homogeneous_critical_member`: a concrete physical bank (`κ = 1`, `Λ = 0`,
`g_j = λ_H = 1`, `v_H = 0`), the unit Higgs vector `(1, 0)` and the Friedmann data
`(a₀, φ₀, π₀, ℋ₀) = (1, 0, 0, 0)`. -/
example : ∃ (ε : ℝ) (_ : 0 < ε) (a φ π ℋ : ℝ → ℝ),
    a 0 = 1 ∧ φ 0 = 0 ∧ π 0 = 0 ∧ ℋ 0 = 0 ∧
    HomogeneousEinsteinHiggs.IsSolution 1 1 0 a φ π ℋ (Ioo (-ε) ε) ∧
    (∀ t ∈ Ioo (-ε) ε, 0 < a t) ∧
    ∃ (zs : SmoothFields ε (trivialCarrier Unit).left) (B : ℝ) (Kf : Set CoframeFibre),
      0 ≤ B ∧ IsCompact Kf ∧ Kf ⊆ coframeChart ∧ SampledFamily (trivialCarrier Unit) B Kf zs.z ∧
      (∀ x : E4, x 0 ∈ Icc 0 ε →
        zs.z.e x = frameDiag (a (x 0 - ε / 2)) ∧
        zs.z.H x = (φ (x 0 - ε / 2) / Real.sqrt 2) • (![1, 0] : HiggsFibre) ∧
        zs.z.A x = 0 ∧ zs.z.Ψ x = 0 ∧ zs.z.Ψb x = 0) ∧
      ∀ (K : CylRegion ε), ∀ v ∈ testSubmodule (trivialCarrier Unit).left K,
        ∑ b, firstVariation ε (trivialCarrier Unit)
          (⟨1, 0, 1, 1, 1, 1, 0, fun _ => 0⟩ : CoefficientBank Unit) b zs.z v = 0 :=
  homogeneous_critical_member (trivialCarrier Unit) ⟨1, 0, 1, 1, 1, 1, 0, fun _ => 0⟩
    one_ne_zero 1 0 0 0 one_pos ![1, 0] (by simp [higgsQuad_eq, Fin.sum_univ_two])
    (by simp [HomogeneousEinsteinHiggs.higgsPotential])

end Main

end HomogeneousCritical
end EinsteinSM
end RenewalGeometry
