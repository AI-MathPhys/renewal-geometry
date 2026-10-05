/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMMeshMain

/-!
# Strong-packet convergence of the sampled reconstruction

Einstein–Standard-Model action-closure manuscript, `prop:mesh-consistency` ("The reconstruction
converges in the strong packet": "The reconstructed fields converge in `W^{1,∞}` on the smooth
family, and their curvature and covariant derivatives converge by the same expansions. This
implies every norm in the strong packet on a compact region.").

* `norm_contJet_sub_le`: the packet jet `(e, F_A, H, D_AH, Ψ, ∇Ψ, Ψ̄, ∇Ψ̄)` is Lipschitz in the
  first jet of the fields (pointwise), on `C^{1,1}` fields with coframes in a compact chart set.
* `exists_strong_packet_pointwise`: for the sampled family, `z_h - f = O(h)` in `C¹` and
  `contJet z_h - contJet f = O(h)` uniformly.
* `exists_dK_le`: the strong-packet distance `d_K` of `eq:strong-geometry`–`eq:strong-spinors`
  between `z_h` and `f` on a chart slab is `O(h)`.
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

variable {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec)

/-! ### Pointwise Lipschitz dependence of the packet on the first jet -/

theorem PtSmall.diffAt_sub {z f : FieldTuple FC.C} {B : ℝ} (hz : FieldC11 FC z B)
    (hf : FieldC11 FC f B) (x : E4) : DiffAt FC (z - f) x :=
  ⟨(hz.e.differentiable x).sub (hf.e.differentiable x),
    (hz.A.differentiable x).sub (hf.A.differentiable x),
    (hz.H.differentiable x).sub (hf.H.differentiable x),
    (hz.Ψ.differentiable x).sub (hf.Ψ.differentiable x),
    (hz.Ψb.differentiable x).sub (hf.Ψb.differentiable x)⟩

theorem curvatureF_sub_apply {z f : FieldTuple FC.C} {x : E4} (hz : DiffAt FC z x)
    (hf : DiffAt FC f x) (μ ν : Fin 4) :
    curvatureF z.A x μ ν - curvatureF f.A x μ ν =
      pd (fun y => (z - f).A y ν) μ x - pd (fun y => (z - f).A y μ) ν x +
        (comm (z.A x μ - f.A x μ) (z.A x ν) + comm (f.A x μ) (z.A x ν - f.A x ν)) := by
  have h1 := pd_sub_fun (f := fun y => z.A y ν) (g := fun y => f.A y ν)
    (differentiableAt_comp_apply hz.A ν) (differentiableAt_comp_apply hf.A ν) μ
  have h2 := pd_sub_fun (f := fun y => z.A y μ) (g := fun y => f.A y μ)
    (differentiableAt_comp_apply hz.A μ) (differentiableAt_comp_apply hf.A μ) ν
  have e1 : pd (fun y => (z - f).A y ν) μ x = pd (fun y => z.A y ν) μ x -
      pd (fun y => f.A y ν) μ x := h1
  have e2 : pd (fun y => (z - f).A y μ) ν x = pd (fun y => z.A y μ) ν x -
      pd (fun y => f.A y μ) ν x := h2
  rw [e1, e2, ← comm_sub4]
  simp only [curvatureF]
  abel

theorem covDerivHiggs_sub_apply {z f : FieldTuple FC.C} {x : E4} (hz : DiffAt FC z x)
    (hf : DiffAt FC f x) (μ : Fin 4) :
    covDerivHiggs z.A z.H x μ - covDerivHiggs f.A f.H x μ =
      pd (z - f).H μ x + (higgsAct (z.A x μ - f.A x μ) (z.H x) +
        higgsAct (f.A x μ) (z.H x - f.H x)) := by
  have h1 : pd (z - f).H μ x = pd z.H μ x - pd f.H μ x := pd_sub_fun hz.H hf.H μ
  rw [h1, ← higgsAct_sub4]
  simp only [covDerivHiggs]
  abel

/-- **Pointwise Lipschitz dependence of the packet jet on the first jet of the fields.** -/
theorem norm_contJet_sub_le {Ke : Set CoframeFibre} (hKeGL : Ke ⊆ coframeGL) {B M : ℝ}
    (hS : SpinChart FC Ke B M) {z f : FieldTuple FC.C} {x : E4} {s : ℝ} (hz : FieldC11 FC z B)
    (hf : FieldC11 FC f B) (hzK : ∀ y, z.e y ∈ Ke) (hfK : ∀ y, f.e y ∈ Ke)
    (hs : PtSmall FC (z - f) x s) :
    ‖contJet FC z x - contJet FC f x‖ ≤ (2 + 24 * B + M * B + M) * s := by
  have hs0 := hs.nonneg
  have hB := hz.nonneg
  have hM := hS.nonneg
  have hBs : 0 ≤ B * s := mul_nonneg hB hs0
  have hMBs : 0 ≤ M * B * s := by positivity
  have hMs : 0 ≤ M * s := mul_nonneg hM hs0
  have hc0 : 0 ≤ (2 + 24 * B + M * B + M) * s := by positivity
  have hd := PtSmall.diffAt_sub FC hz hf x
  have hzA : ∀ μ, ‖z.A x μ‖ ≤ B := fun μ => (norm_le_pi_norm _ μ).trans (hz.A.norm_le x)
  have hfA : ∀ μ, ‖f.A x μ‖ ≤ B := fun μ => (norm_le_pi_norm _ μ).trans (hf.A.norm_le x)
  have hdA : ∀ μ, ‖z.A x μ - f.A x μ‖ ≤ s := fun μ =>
    (norm_le_pi_norm (z.A x - f.A x) μ).trans hs.A
  have hcomm : ∀ a b : LieFibre, ‖a‖ ≤ B → ‖b‖ ≤ s → ‖comm a b‖ ≤ 10 * B * s := fun a b ha hb =>
    (norm_comm_le a b).trans (by
      have := mul_le_mul ha hb (norm_nonneg b) hB; nlinarith)
  have hcomm' : ∀ a b : LieFibre, ‖a‖ ≤ s → ‖b‖ ≤ B → ‖comm a b‖ ≤ 10 * B * s := fun a b ha hb =>
    (norm_comm_le a b).trans (by
      have := mul_le_mul ha hb (norm_nonneg b) hs0; nlinarith)
  have hsp : ∀ μ, spinConnection FC z μ x = spinConnMap FC μ (sjetOf FC z μ x) := fun μ =>
    spinConnection_eq_map FC z μ (hz.e.differentiable x) (hKeGL (hzK x))
  have hsp' : ∀ μ, spinConnection FC f μ x = spinConnMap FC μ (sjetOf FC f μ x) := fun μ =>
    spinConnection_eq_map FC f μ (hf.e.differentiable x) (hKeGL (hfK x))
  have hcsp : ∀ μ, cospinConnection FC z μ x = cospinConnMap FC μ (sjetOf FC z μ x) := fun μ =>
    cospinConnection_eq_map FC z μ (hz.e.differentiable x) (hKeGL (hzK x))
  have hcsp' : ∀ μ, cospinConnection FC f μ x = cospinConnMap FC μ (sjetOf FC f μ x) := fun μ =>
    cospinConnection_eq_map FC f μ (hf.e.differentiable x) (hKeGL (hfK x))
  have hsj : ∀ μ, ‖sjetOf FC z μ x - sjetOf FC f μ x‖ ≤ s := fun μ => by
    rw [← sjetOf_sub FC (hz.e.differentiable x) (hf.e.differentiable x)]
    exact hs.sjetOf FC μ
  have hmz := sjetOf_mem FC hz hzK
  have hmf := sjetOf_mem FC hf hfK
  have happ : ∀ (L L' : SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C) (v v' : SpinorFibre FC.C),
      ‖L - L'‖ ≤ M * s → ‖v‖ ≤ B → ‖L'‖ ≤ M → ‖v - v'‖ ≤ s →
      ‖L v - L' v'‖ ≤ M * s * B + M * s := fun L L' v v' h1 h2 h3 h4 => by
    have e : L v - L' v' = (L - L') v + L' (v - v') := by
      simp only [ContinuousLinearMap.sub_apply, map_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add (((L - L').le_opNorm v).trans
      (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))) ((L'.le_opNorm _).trans
      (mul_le_mul h3 h4 (norm_nonneg _) hM)))
  rw [contJet, contJet, rjet_mk_sub]
  refine norm_rjet_le FC ?_ (by simpa using hc0) (by simpa using hc0)
    (norm_pi2_le hc0 fun μ ν => ?_) ?_ (norm_pi1_le hc0 fun μ => ?_) ?_
    (norm_pi1_le hc0 fun μ => ?_) ?_ (norm_pi1_le hc0 fun μ => ?_)
  · exact hs.e.trans (by nlinarith)
  · show ‖curvatureF z.A x μ ν - curvatureF f.A x μ ν‖ ≤ _
    rw [curvatureF_sub_apply FC (hz.diffAt FC x) (hf.diffAt FC x)]
    have p1 := (norm_pd_comp_le hd.A ν μ).trans hs.dA
    have p2 := (norm_pd_comp_le hd.A μ ν).trans hs.dA
    have c1 := hcomm' _ _ (hdA μ) (hzA ν)
    have c2 := hcomm _ _ (hfA μ) (hdA ν)
    have t1 := norm_add_le (pd (fun y => (z - f).A y ν) μ x - pd (fun y => (z - f).A y μ) ν x)
      (comm (z.A x μ - f.A x μ) (z.A x ν) + comm (f.A x μ) (z.A x ν - f.A x ν))
    have t2 := norm_sub_le (pd (fun y => (z - f).A y ν) μ x) (pd (fun y => (z - f).A y μ) ν x)
    have t3 := norm_add_le (comm (z.A x μ - f.A x μ) (z.A x ν))
      (comm (f.A x μ) (z.A x ν - f.A x ν))
    refine t1.trans ((add_le_add t2 t3).trans ?_)
    linarith
  · exact hs.H.trans (by nlinarith)
  · show ‖covDerivHiggs z.A z.H x μ - covDerivHiggs f.A f.H x μ‖ ≤ _
    rw [covDerivHiggs_sub_apply FC (hz.diffAt FC x) (hf.diffAt FC x)]
    have p1 := (norm_pd_le (z - f).H μ x).trans hs.dH
    have h1 := norm_higgsAct_le (z.A x μ - f.A x μ) (z.H x)
    have h2 := norm_higgsAct_le (f.A x μ) (z.H x - f.H x)
    have e1 := mul_le_mul (hdA μ) (hz.H.norm_le x) (norm_nonneg _) hs0
    have hsH : ‖z.H x - f.H x‖ ≤ s := hs.H
    have e2 := mul_le_mul (hfA μ) hsH (norm_nonneg _) hB
    have t1 := norm_add_le (pd (z - f).H μ x) (higgsAct (z.A x μ - f.A x μ) (z.H x) +
      higgsAct (f.A x μ) (z.H x - f.H x))
    have t2 := norm_add_le (higgsAct (z.A x μ - f.A x μ) (z.H x))
      (higgsAct (f.A x μ) (z.H x - f.H x))
    nlinarith
  · exact hs.Ψ.trans (by nlinarith)
  · show ‖covDerivSpinor FC z.e z.A z.Ψ x μ - covDerivSpinor FC f.e f.A f.Ψ x μ‖ ≤ _
    rw [covDerivSpinor_eq, covDerivSpinor_eq, hsp, hsp']
    have p1 : ‖pd z.Ψ μ x - pd f.Ψ μ x‖ ≤ s := by
      rw [← pd_sub_fun (hz.Ψ.differentiable x) (hf.Ψ.differentiable x)]
      exact (norm_pd_le _ μ x).trans hs.dΨ
    have q := happ (spinConnMap FC μ (sjetOf FC z μ x)) (spinConnMap FC μ (sjetOf FC f μ x))
      (z.Ψ x) (f.Ψ x) (((hS.lip μ _ (hmz μ x) _ (hmf μ x)).1).trans
        (mul_le_mul_of_nonneg_left (hsj μ) hM)) (hz.Ψ.norm_le x) (hS.bound μ _ (hmf μ x)).1 hs.Ψ
    have e : pd z.Ψ μ x + spinConnMap FC μ (sjetOf FC z μ x) (z.Ψ x) -
        (pd f.Ψ μ x + spinConnMap FC μ (sjetOf FC f μ x) (f.Ψ x)) =
        (pd z.Ψ μ x - pd f.Ψ μ x) + (spinConnMap FC μ (sjetOf FC z μ x) (z.Ψ x) -
          spinConnMap FC μ (sjetOf FC f μ x) (f.Ψ x)) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    nlinarith
  · exact hs.Ψb.trans (by nlinarith)
  · show ‖covDerivCospinor FC z.e z.A z.Ψb x μ - covDerivCospinor FC f.e f.A f.Ψb x μ‖ ≤ _
    rw [covDerivCospinor_eq, covDerivCospinor_eq, hcsp, hcsp']
    have p1 : ‖pd z.Ψb μ x - pd f.Ψb μ x‖ ≤ s := by
      rw [← pd_sub_fun (hz.Ψb.differentiable x) (hf.Ψb.differentiable x)]
      exact (norm_pd_le _ μ x).trans hs.dΨb
    have q := happ (cospinConnMap FC μ (sjetOf FC z μ x)) (cospinConnMap FC μ (sjetOf FC f μ x))
      (z.Ψb x) (f.Ψb x) (((hS.lip μ _ (hmz μ x) _ (hmf μ x)).2).trans
        (mul_le_mul_of_nonneg_left (hsj μ) hM)) (hz.Ψb.norm_le x) (hS.bound μ _ (hmf μ x)).2
        hs.Ψb
    have e : pd z.Ψb μ x + cospinConnMap FC μ (sjetOf FC z μ x) (z.Ψb x) -
        (pd f.Ψb μ x + cospinConnMap FC μ (sjetOf FC f μ x) (f.Ψb x)) =
        (pd z.Ψb μ x - pd f.Ψb μ x) + (cospinConnMap FC μ (sjetOf FC z μ x) (z.Ψb x) -
          cospinConnMap FC μ (sjetOf FC f μ x) (f.Ψb x)) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    nlinarith


/-! ### Strong-packet convergence of the sampled reconstruction (pointwise) -/

/-- **Strong-packet convergence, pointwise form**: for the sampled bounded `C^{1,1}` family,
`z_h - f = O(h)` in `C¹` and the packet jets (curvature, covariant Higgs gradient, spin–gauge
covariant derivatives) converge at rate `O(h)`, uniformly in the family. -/
theorem exists_strong_packet_pointwise {B : ℝ} (hB : 0 ≤ B) {Kf : Set CoframeFibre}
    (hKf : IsCompact Kf) (hKfGL : Kf ⊆ coframeGL) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ f : FieldTuple FC.C, SampledFamily FC B Kf f →
      ∀ N : ℕ, N₀ ≤ N → 0 < N → ∀ x : E4,
        PtSmall FC (reconFields FC (1 / N) (sampleRec FC (1 / N) f) - f) x (C * (1 / N)) ∧
        ‖contJet FC (reconFields FC (1 / N) (sampleRec FC (1 / N) f)) x - contJet FC f x‖ ≤
          C * (1 / N) := by
  obtain ⟨δ, hδ, hδU⟩ := hKf.exists_cthickening_subset_open isOpen_coframeGL hKfGL
  set Ke := cthickening δ Kf
  have hKe : IsCompact Ke := hKf.cthickening
  have hcR := one_le_cRec
  set Bz := cRec * B
  have hBz : 0 ≤ Bz := by positivity
  have hBBz : B ≤ Bz := le_mul_of_one_le_left hB hcR
  obtain ⟨M, hS⟩ := exists_spinChart FC hKe hδU Bz
  have hcv := cVal_nonneg (d := 4); have hcd := cDer_nonneg (d := 4)
  set c₁ := (cVal 4 + cDer 4) * B
  have hc₁ : 0 ≤ c₁ := by positivity
  set CJ := 2 + 24 * Bz + M * Bz + M
  have hCJ : 0 ≤ CJ := by have := hS.nonneg; positivity
  set h₁ := min 1 (δ / (cVal 4 * B + 1))
  have hh₁ : 0 < h₁ := lt_min one_pos (by positivity)
  refine ⟨c₁ + CJ * c₁, by positivity, ⌈1 / h₁⌉₊ + 1, fun f hf N hN₀ hN x => ?_⟩
  set h : ℝ := 1 / N with hhdef
  have hh : 0 < h := one_div_N_pos hN
  have hhh₁ : h ≤ h₁ := by
    have hN' : (1 / h₁ : ℝ) < N := by
      have := Nat.le_ceil (1 / h₁)
      have h2 : ((⌈1 / h₁⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN₀
      push_cast at h2
      linarith
    rw [hhdef, div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hh₁] at hN'
    linarith
  have hh1 : h ≤ 1 := hhh₁.trans (min_le_left _ _)
  have hhδ : h ≤ δ / (cVal 4 * B + 1) := hhh₁.trans (min_le_right _ _)
  set z := reconFields FC h (sampleRec FC h f)
  have hzC : FieldC11 FC z Bz := fieldC11_reconFields FC hf.c11 hh hh1
  have hfC : FieldC11 FC f Bz := hf.c11.mono FC hBBz
  have hzK : ∀ y, z.e y ∈ Ke := fun y => by
    refine mem_cthickening_of_dist_le (z.e y) (f.e y) δ Kf (hf.chart y) ?_
    rw [dist_eq_norm]
    refine (norm_recon_samp_sub_le' hf.c11.e hh y).trans ?_
    rw [le_div_iff₀ (by positivity)] at hhδ
    nlinarith
  have hfK : ∀ y, f.e y ∈ Ke := fun y => self_subset_cthickening _ (hf.chart y)
  have hs : PtSmall FC (z - f) x (c₁ * h) := by
    have := ptSmall_reconFields_sub FC hf.c11 hh x
    simpa only [c₁] using this
  have hJ := norm_contJet_sub_le FC hδU hS hzC hfC hzK hfK hs
  have e1 : c₁ * h ≤ (c₁ + CJ * c₁) * h := by
    have := mul_nonneg (mul_nonneg hCJ hc₁) hh.le; nlinarith
  refine ⟨?_, hJ.trans (by nlinarith [mul_nonneg hc₁ hh.le])⟩
  exact ⟨hs.e.trans e1, hs.de.trans e1, hs.A.trans e1, hs.dA.trans e1, hs.H.trans e1,
    hs.dH.trans e1, hs.Ψ.trans e1, hs.dΨ.trans e1, hs.Ψb.trans e1, hs.dΨb.trans e1⟩


/-! ### The strong-packet distance `d_K` -/

section DKBound

variable {T : ℝ}

theorem rpow_le_max_one (x : ℝ≥0∞) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : x ^ a ≤ max 1 x := by
  rcases le_total x 1 with hx | hx
  · exact (ENNReal.rpow_le_one hx ha0).trans (le_max_left _ _)
  · calc x ^ a ≤ x ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hx ha1
      _ = x := ENNReal.rpow_one x
      _ ≤ _ := le_max_right _ _

theorem eLpNorm_le_of_le_chart (Q : ChartBox T) {F : Type*} [NormedAddCommGroup F] {g : E4 → F}
    {c : ℝ} (hc : ∀ x, ‖g x‖ ≤ c) {p : ℝ≥0∞} (hp : p.toReal⁻¹ ≤ 1) :
    eLpNorm g p Q.μ ≤ max 1 (Q.μ univ) * ENNReal.ofReal c :=
  (eLpNorm_le_of_ae_bound (Filter.Eventually.of_forall hc)).trans
    (by gcongr; exact rpow_le_max_one _ (inv_nonneg.mpr ENNReal.toReal_nonneg) hp)

theorem RJet.norm_F_le' (R : RJet FC.C) : ‖R.F‖ ≤ ‖R‖ :=
  (norm_fst_le _).trans ((norm_snd_le _).trans ((norm_snd_le _).trans (norm_snd_le _)))

theorem RJet.norm_K_le' (R : RJet FC.C) : ‖R.K‖ ≤ ‖R‖ :=
  (norm_fst_le _).trans ((norm_snd_le _).trans ((norm_snd_le _).trans ((norm_snd_le _).trans
    ((norm_snd_le _).trans (norm_snd_le _)))))

theorem norm_cast_pi2_sub_le {ι κ : Type*} [Fintype ι] [Fintype κ] (a b : ι → κ → ℝ) {s : ℝ}
    (hs : ‖a - b‖ ≤ s) :
    ‖(fun p : ι × κ => ((a p.1 p.2 : ℝ) : ℂ)) - fun p : ι × κ => ((b p.1 p.2 : ℝ) : ℂ)‖ ≤ s := by
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hs
  refine (pi_norm_le_iff_of_nonneg hs0).mpr fun p => ?_
  simp only [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real]
  exact (norm_le_pi_norm ((a - b) p.1) p.2).trans ((norm_le_pi_norm (a - b) p.1).trans hs)

theorem norm_pi2_sub_le {ι κ : Type*} [Fintype ι] [Fintype κ] (a b : ι → κ → ℂ) {s : ℝ}
    (hs : ‖a - b‖ ≤ s) :
    ‖(fun p : ι × κ => a p.1 p.2) - fun p : ι × κ => b p.1 p.2‖ ≤ s := by
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hs
  refine (pi_norm_le_iff_of_nonneg hs0).mpr fun p => ?_
  exact (norm_le_pi_norm ((a - b) p.1) p.2).trans ((norm_le_pi_norm (a - b) p.1).trans hs)

/-- **`d_K` from pointwise first-jet and packet bounds** (the `L^p` norms on the chart box,
each at most `max(1, |Q|) s`; equal banks). -/
theorem dK_le_of_pointwise (Q : ChartBox T) (z₁ z₂ : SmoothFields T FC.left)
    (θ : CoefficientBank Ysec) {s : ℝ} (hd₁ : ∀ x, DiffAt FC z₁.z x) (hd₂ : ∀ x, DiffAt FC z₂.z x)
    (hs : ∀ x, PtSmall FC (z₁.z - z₂.z) x s)
    (hJ : ∀ x, ‖contJet FC z₁.z x - contJet FC z₂.z x‖ ≤ s) :
    dK Q z₁ θ z₂ θ ≤ 16 * (max 1 (Q.μ univ) * ENNReal.ofReal s) := by
  set V := max 1 (Q.μ univ) * ENNReal.ofReal s
  have h2 : (2 : ℝ≥0∞).toReal⁻¹ ≤ 1 := by norm_num
  have h4 : (4 : ℝ≥0∞).toReal⁻¹ ≤ 1 := by norm_num
  have hT : (⊤ : ℝ≥0∞).toReal⁻¹ ≤ 1 := by simp
  have hpd : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {g₁ g₂ : E4 → W} (x : E4),
      DifferentiableAt ℝ g₁ x → DifferentiableAt ℝ g₂ x → ‖fderiv ℝ (g₁ - g₂) x‖ ≤ s →
      ‖(fun i => pd g₁ i x) - fun i => pd g₂ i x‖ ≤ s := fun x h₁ h₂ hb => by
    have hs0 : 0 ≤ s := (norm_nonneg _).trans hb
    refine (pi_norm_le_iff_of_nonneg hs0).mpr fun i => ?_
    rw [Pi.sub_apply, ← pd_sub_fun h₁ h₂]
    exact (norm_pd_le _ i x).trans hb
  have c0 : eLpNorm (z₁.z.e - z₂.z.e) ⊤ Q.μ ≤ V := eLpNorm_le_of_le_chart Q (fun x => (hs x).e) hT
  have c1a : eLpNorm (coframeC z₁.z.e - coframeC z₂.z.e) 2 Q.μ ≤ V :=
    eLpNorm_le_of_le_chart Q (fun x => norm_cast_pi2_sub_le _ _ (hs x).e) h2
  have c1b : eLpNorm (coframeGrad z₁.z.e - coframeGrad z₂.z.e) 2 Q.μ ≤ V :=
    eLpNorm_le_of_le_chart Q (fun x => by
      have hb := hpd x (hd₁ x).e (hd₂ x).e (hs x).de
      have hs0 : 0 ≤ s := (hs x).nonneg
      refine (pi_norm_le_iff_of_nonneg hs0).mpr fun i => ?_
      exact norm_cast_pi2_sub_le _ _ ((norm_le_pi_norm (_ - _) i).trans hb)) h2
  have c2 : eLpNorm (z₁.z.A - z₂.z.A) 4 Q.μ ≤ V := eLpNorm_le_of_le_chart Q (fun x => (hs x).A) h4
  have c3 : eLpNorm (curvatureF z₁.z.A - curvatureF z₂.z.A) 2 Q.μ ≤ V :=
    eLpNorm_le_of_le_chart Q (fun x => (RJet.norm_F_le' FC _).trans (hJ x)) h2
  have c4 : eLpNorm (z₁.z.H - z₂.z.H) 4 Q.μ ≤ V := eLpNorm_le_of_le_chart Q (fun x => (hs x).H) h4
  have c5 : eLpNorm (covDerivHiggs z₁.z.A z₁.z.H - covDerivHiggs z₂.z.A z₂.z.H) 2 Q.μ ≤ V :=
    eLpNorm_le_of_le_chart Q (fun x => (RJet.norm_K_le' FC _).trans (hJ x)) h2
  have c6a : eLpNorm (spinorC z₁.z.Ψ - spinorC z₂.z.Ψ) 2 Q.μ ≤ V :=
    eLpNorm_le_of_le_chart Q (fun x => norm_pi2_sub_le _ _ (hs x).Ψ) h2
  have c6b : eLpNorm (spinorGrad z₁.z.Ψ - spinorGrad z₂.z.Ψ) 2 Q.μ ≤ V :=
    eLpNorm_le_of_le_chart Q (fun x => by
      have hb := hpd x (hd₁ x).Ψ (hd₂ x).Ψ (hs x).dΨ
      have hs0 : 0 ≤ s := (hs x).nonneg
      refine (pi_norm_le_iff_of_nonneg hs0).mpr fun i => ?_
      exact norm_pi2_sub_le _ _ ((norm_le_pi_norm (_ - _) i).trans hb)) h2
  have c7a : eLpNorm (spinorC z₁.z.Ψb - spinorC z₂.z.Ψb) 2 Q.μ ≤ V :=
    eLpNorm_le_of_le_chart Q (fun x => norm_pi2_sub_le _ _ (hs x).Ψb) h2
  have c7b : eLpNorm (spinorGrad z₁.z.Ψb - spinorGrad z₂.z.Ψb) 2 Q.μ ≤ V :=
    eLpNorm_le_of_le_chart Q (fun x => by
      have hb := hpd x (hd₁ x).Ψb (hd₂ x).Ψb (hs x).dΨb
      have hs0 : 0 ≤ s := (hs x).nonneg
      refine (pi_norm_le_iff_of_nonneg hs0).mpr fun i => ?_
      exact norm_pi2_sub_le _ _ ((norm_le_pi_norm (_ - _) i).trans hb)) h2
  have hV : V ≤ 2 * V := by rw [two_mul]; exact le_add_self
  have hc : ∀ i, dKComp Q z₁ z₂ i ≤ 2 * V := by
    intro i
    fin_cases i
    · exact c0.trans hV
    · exact (add_le_add c1a c1b).trans (le_of_eq (two_mul V).symm)
    · exact c2.trans hV
    · exact c3.trans hV
    · exact c4.trans hV
    · exact c5.trans hV
    · exact (add_le_add c6a c6b).trans (le_of_eq (two_mul V).symm)
    · exact (add_le_add c7a c7b).trans (le_of_eq (two_mul V).symm)
  unfold dK
  rw [edist_self, add_zero]
  calc ∑ i, dKComp Q z₁ z₂ i ≤ ∑ _i : Fin 8, 2 * V := Finset.sum_le_sum fun i _ => hc i
    _ = 16 * V := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
      norm_num

end DKBound

end Comparison
end EinsteinSM
end RenewalGeometry
