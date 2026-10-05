/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMMeshPacket
import RenewalGeometry.Action.CriticalShadowingExact

/-!
# Smooth sampling is a consistency realization (`prop:smooth-sampling`)

Einstein–Standard-Model action-closure manuscript, `prop:smooth-sampling`: on the comparison
regulator of `app:reconstruction`, smooth sampling of a smooth configuration `z_*` (fixed
nondegenerate coframe chart) gives `z_h → z_*` in the strong packet and `c_h(K) ≤ C_K h`
(`eq:sampling-consistency`); if `z_*` solves the classical Euler equations on the test space then
`ε_h(K) ≤ C'_K h` (`eq:sampling-stationarity`), by `ε_h ≤ c_h + C_K d_K(z_h, z_*)`
(`prop:variation-continuity`, `VarLip.variation_continuity`).

Renderings (disclosed): the physical stationarity defect of the comparison regulator is
`ε_h(K) = sup_{‖v‖ ≤ 1} |Σ_b D S_{b,h}(q_h)[𝓘_h v]|` (the common comparison action is the sum of
the two sector actions); "solves the classical Euler equations" is the weak form
`Σ_b D𝒮_{b,θ}(z_*)[v] = 0` for all `v ∈ 𝒱_K`; the bank is fixed (`θ_h = θ`, physical).
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

/-! ### `d_K(z_h, z_*) = O(h)` for the sampled family -/

theorem one_div_N_le_one {N : ℕ} (hN : 0 < N) : (1 : ℝ) / N ≤ 1 :=
  (div_le_one (by exact_mod_cast hN)).mpr (by exact_mod_cast hN)

/-- **Strong-packet convergence in `d_K`**: for the sampled family, the strong-packet distance of
`eq:strong-geometry`–`eq:strong-spinors` on a chart slab satisfies `d_K(z_h, z_*) ≤ C h`. -/
theorem exists_dK_sampling {B : ℝ} (hB : 0 ≤ B) {Kf : Set CoframeFibre} (hKf : IsCompact Kf)
    (hKfGL : Kf ⊆ coframeGL) {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    (θ : CoefficientBank Ysec) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ (zs : SmoothFields T FC.left)
      (hzs : SampledFamily FC B Kf zs.z) (N : ℕ) (_ : N₀ ≤ N) (hN : 0 < N),
      dK (slabChart t₀ t₁ h0 h01 h1 (T := T)) (reconSmooth FC T hN hzs) θ zs θ ≤
        ENNReal.ofReal (C * (1 / N)) := by
  obtain ⟨C, hC, N₀, hP⟩ := exists_strong_packet_pointwise FC hB hKf hKfGL
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  set m := (max 1 (Q.μ univ)).toReal
  have hm : max 1 (Q.μ univ) = ENNReal.ofReal m :=
    (ENNReal.ofReal_toReal (max_ne_top ENNReal.one_ne_top (measure_ne_top _ _))).symm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  refine ⟨16 * m * C, by positivity, N₀, fun zs hzs N hN₀ hN => ?_⟩
  have hh := one_div_N_pos hN
  have hzC := fieldC11_reconFields FC hzs.c11 hh (one_div_N_le_one hN)
  have := dK_le_of_pointwise FC Q (reconSmooth FC T hN hzs) zs θ (fun x => hzC.diffAt FC x)
    (fun x => hzs.c11.diffAt FC x) (fun x => (hP zs.z hzs N hN₀ hN x).1)
    (fun x => (hP zs.z hzs N hN₀ hN x).2)
  refine this.trans (le_of_eq ?_)
  rw [hm, ← ENNReal.ofReal_mul hm0, show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by norm_num,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring

/-! ### Packet bounds of `C^{1,1}` fields -/

section PacketBounds

variable {T : ℝ}

theorem norm_cast_pi2_le {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → κ → ℝ) {s : ℝ}
    (hs : ‖a‖ ≤ s) : ‖fun p : ι × κ => ((a p.1 p.2 : ℝ) : ℂ)‖ ≤ s := by
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hs
  refine (pi_norm_le_iff_of_nonneg hs0).mpr fun p => ?_
  rw [Complex.norm_real]
  exact (norm_le_pi_norm (a p.1) p.2).trans ((norm_le_pi_norm a p.1).trans hs)

theorem norm_pi2_le' {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → κ → ℂ) {s : ℝ}
    (hs : ‖a‖ ≤ s) : ‖fun p : ι × κ => a p.1 p.2‖ ≤ s := by
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hs
  refine (pi_norm_le_iff_of_nonneg hs0).mpr fun p => ?_
  exact (norm_le_pi_norm (a p.1) p.2).trans ((norm_le_pi_norm a p.1).trans hs)

theorem norm_pdPi_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {g : E4 → W}
    {B : ℝ} (hg : IsC11 g B) (x : E4) : ‖fun i => pd g i x‖ ≤ B :=
  (pi_norm_le_iff_of_nonneg hg.nonneg).mpr fun i => (norm_pd_le g i x).trans (hg.norm_fderiv_le x)

/-- **The bounded strong-packet class** contains every `C^{1,1}` smooth field tuple with coframe
in the chart set (`L^p` norms on the chart box from sup bounds). -/
theorem packetBound_of_C11 (Q : ChartBox T) {Ke : Set CoframeFibre} (z : SmoothFields T FC.left)
    {Bz : ℝ} (hz : FieldC11 FC z.z Bz) (hzK : ∀ x, z.z.e x ∈ Ke) :
    VarLip.PacketBound Q Ke
      (2 * (max 1 (Q.μ univ) * ENNReal.ofReal (2 * Bz + 10 * Bz * Bz))) z := by
  have hB := hz.nonneg
  set c := 2 * Bz + 10 * Bz * Bz
  have hBc : Bz ≤ c := by simp only [c]; nlinarith
  set V := max 1 (Q.μ univ) * ENNReal.ofReal c
  have hV : V ≤ 2 * V := by rw [two_mul]; exact le_add_self
  have h2 : (2 : ℝ≥0∞).toReal⁻¹ ≤ 1 := by norm_num
  have h4 : (4 : ℝ≥0∞).toReal⁻¹ ≤ 1 := by norm_num
  have hzA : ∀ x μ, ‖z.z.A x μ‖ ≤ Bz := fun x μ => (norm_le_pi_norm _ μ).trans (hz.A.norm_le x)
  have hcurv : ∀ x, ‖curvatureF z.z.A x‖ ≤ c := fun x => by
    refine norm_pi2_le (by positivity) fun μ ν => ?_
    have p1 := (norm_pd_comp_le (hz.A.differentiable x) ν μ).trans (hz.A.norm_fderiv_le x)
    have p2 := (norm_pd_comp_le (hz.A.differentiable x) μ ν).trans (hz.A.norm_fderiv_le x)
    have c1 := norm_comm_le (z.z.A x μ) (z.z.A x ν)
    have e1 := mul_le_mul (hzA x μ) (hzA x ν) (norm_nonneg _) hB
    have t1 := norm_add_le (pd (fun y => z.z.A y ν) μ x - pd (fun y => z.z.A y μ) ν x)
      (comm (z.z.A x μ) (z.z.A x ν))
    have t2 := norm_sub_le (pd (fun y => z.z.A y ν) μ x) (pd (fun y => z.z.A y μ) ν x)
    show ‖pd (fun y => z.z.A y ν) μ x - pd (fun y => z.z.A y μ) ν x +
      comm (z.z.A x μ) (z.z.A x ν)‖ ≤ c
    simp only [c]
    nlinarith
  have hcov : ∀ x, ‖covDerivHiggs z.z.A z.z.H x‖ ≤ c := fun x => by
    refine norm_pi1_le (by positivity) fun μ => ?_
    have p1 := (norm_pd_le z.z.H μ x).trans (hz.H.norm_fderiv_le x)
    have c1 := norm_higgsAct_le (z.z.A x μ) (z.z.H x)
    have e1 := mul_le_mul (hzA x μ) (hz.H.norm_le x) (norm_nonneg _) hB
    have t1 := norm_add_le (pd z.z.H μ x) (higgsAct (z.z.A x μ) (z.z.H x))
    show ‖pd z.z.H μ x + higgsAct (z.z.A x μ) (z.z.H x)‖ ≤ c
    simp only [c]
    nlinarith
  refine ⟨fun x _ => hzK x, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (add_le_add (eLpNorm_le_of_le_chart Q (fun x =>
      norm_cast_pi2_le _ ((hz.e.norm_le x).trans hBc)) h2) (eLpNorm_le_of_le_chart Q (fun x =>
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => norm_cast_pi2_le _
        ((norm_le_pi_norm _ i).trans ((norm_pdPi_le hz.e x).trans hBc))) h2)).trans
      (le_of_eq (two_mul V).symm)
  · exact (eLpNorm_le_of_le_chart Q (fun x => (hz.A.norm_le x).trans hBc) h4).trans hV
  · exact (eLpNorm_le_of_le_chart Q hcurv h2).trans hV
  · exact (eLpNorm_le_of_le_chart Q (fun x => (hz.H.norm_le x).trans hBc) h4).trans hV
  · exact (eLpNorm_le_of_le_chart Q hcov h2).trans hV
  · exact (add_le_add (eLpNorm_le_of_le_chart Q (fun x =>
      norm_pi2_le' _ ((hz.Ψ.norm_le x).trans hBc)) h2) (eLpNorm_le_of_le_chart Q (fun x =>
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => norm_pi2_le' _
        ((norm_le_pi_norm _ i).trans ((norm_pdPi_le hz.Ψ x).trans hBc))) h2)).trans
      (le_of_eq (two_mul V).symm)
  · exact (add_le_add (eLpNorm_le_of_le_chart Q (fun x =>
      norm_pi2_le' _ ((hz.Ψb.norm_le x).trans hBc)) h2) (eLpNorm_le_of_le_chart Q (fun x =>
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => norm_pi2_le' _
        ((norm_le_pi_norm _ i).trans ((norm_pdPi_le hz.Ψb x).trans hBc))) h2)).trans
      (le_of_eq (two_mul V).symm)

end PacketBounds


/-! ### `prop:smooth-sampling` -/

/-- **The physical stationarity defect `ε_h(K)`** (`eq:stationarity`) of the comparison regulator:
`sup_{v ∈ 𝒱_K, ‖v‖_{C^{r₀}} ≤ 1} |Σ_b D S_{b,h}(q)[𝓘_h v]|`. -/
def comparisonStationarity (T : ℝ) (θ : CoefficientBank Ysec) (P N r₀ : ℕ) (K : CylRegion T)
    (q : (Fin 4 → ℤ) → FieldVal FC.C) : ℝ≥0∞ :=
  ⨆ (v : ↥(testSubmodule FC.left K)) (_ : testNorm r₀ v.1 ≤ 1),
    ENNReal.ofReal |∑ b : Sector, finiteVar (sectorAction FC θ P N b) q
      (liftRec FC P N (1 / N) (reconFields FC (1 / N) q) v.1)|

theorem sum_sector_real (F : Sector → ℝ) : ∑ b, F b = F .gravity + F .standardModel :=
  Finset.sum_pair (by decide)

theorem isOpen_coframeChart : IsOpen coframeChart := by
  have hdet : Continuous fun e : CoframeFibre => (Matrix.of e).det :=
    Continuous.matrix_det continuous_id
  have h00 : Continuous fun e : CoframeFibre => e 0 0 :=
    (continuous_apply 0).comp (continuous_apply 0)
  exact (isOpen_lt continuous_const hdet).inter (isOpen_lt continuous_const h00)

theorem isCompactBankSet_singleton {θ : CoefficientBank Ysec} (hθ : θ ∈ physicalBanks) :
    IsCompactBankSet {θ} :=
  ⟨by rw [Set.image_singleton]; exact isCompact_singleton, Set.singleton_subset_iff.mpr hθ⟩

theorem yukawaLipOn_singleton (θ : CoefficientBank Ysec) :
    VarLip.YukawaLipOn FC {θ} 0 (‖yukL FC θ‖ + ‖FC.yukawa θ 0‖) := by
  refine ⟨le_rfl, by positivity, fun θ' h => ?_, fun θ' h => ?_, fun θ₁ h₁ θ₂ h₂ => ?_,
    fun θ₁ h₁ θ₂ h₂ => ?_⟩
  · rw [Set.mem_singleton_iff.mp h]; exact le_add_of_nonneg_right (norm_nonneg _)
  · rw [Set.mem_singleton_iff.mp h]; exact le_add_of_nonneg_left (norm_nonneg _)
  · rw [Set.mem_singleton_iff.mp h₁, Set.mem_singleton_iff.mp h₂, sub_self, norm_zero,
      ENNReal.ofReal_zero]; exact zero_le
  · rw [Set.mem_singleton_iff.mp h₁, Set.mem_singleton_iff.mp h₂, sub_self, norm_zero,
      ENNReal.ofReal_zero]; exact zero_le

/-- **`prop:smooth-sampling`** (consistency and stationarity clauses): for smooth configurations
`z_*` in a bounded `C^{1,1}` class with coframe in a fixed compact subset of the nondegenerate
chart, nodal sampling and cardinal reconstruction give, uniformly, for `h = 1/N`, `N ≥ N₀`:
`c_h(K) ≤ C h` (`eq:sampling-consistency`), `d_K(z_h, z_*) ≤ C h` (strong-packet convergence) and,
if `z_*` is critical (weak Euler equations on `𝒱_K`), `ε_h(K) ≤ C h`
(`eq:sampling-stationarity`). -/
theorem smooth_sampling [Nonempty FC.C] (θ : CoefficientBank Ysec) (hθ : θ ∈ physicalBanks)
    {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T}
    (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) {P : ℕ} (hTP : T ≤ P) {r₀ : ℕ} (hr : 2 ≤ r₀)
    {B : ℝ} (hB : 0 ≤ B) {Kf : Set CoframeFibre} (hKf : IsCompact Kf) (hKfC : Kf ⊆ coframeChart) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ (zs : SmoothFields T FC.left)
      (hzs : SampledFamily FC B Kf zs.z) (N : ℕ) (_ : N₀ ≤ N) (hN : 0 < N),
      comparisonDefect FC T θ P N r₀ K (sampleRec FC (1 / N) zs.z) ≤
          ENNReal.ofReal (C * (1 / N)) ∧
        dK (slabChart t₀ t₁ h0 h01 h1 (T := T)) (reconSmooth FC T hN hzs) θ zs θ ≤
          ENNReal.ofReal (C * (1 / N)) ∧
        ((∀ v ∈ testSubmodule FC.left K, ∑ b, firstVariation T FC θ b zs.z v = 0) →
          comparisonStationarity FC T θ P N r₀ K (sampleRec FC (1 / N) zs.z) ≤
            ENNReal.ofReal (C * (1 / N))) := by
  have hKfGL : Kf ⊆ coframeGL := hKfC.trans coframeChart_subset_GL
  obtain ⟨Cm, hCm, N₁, hMC⟩ := mesh_consistency FC θ h0 h01 h1 hK hTP hr hB hKf hKfGL
  obtain ⟨Cs, hCs, N₂, hSB⟩ := exists_mesh_sector_bound FC θ h0 h01 h1 hK hTP hr hB hKf hKfGL
  obtain ⟨Cd, hCd, N₃, hDK⟩ := exists_dK_sampling FC hB hKf hKfGL h0 h01 h1 θ
  obtain ⟨δ, hδ, hδU⟩ := hKf.exists_cthickening_subset_open isOpen_coframeChart hKfC
  set Ke := cthickening δ Kf
  have hKe : IsCompactCoframeSet Ke := ⟨hKf.cthickening, hδU⟩
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  have hcR := one_le_cRec
  set Bz := cRec * B
  have hBz : 0 ≤ Bz := by positivity
  have hBBz : B ≤ Bz := le_mul_of_one_le_left hB hcR
  set Bp := 2 * (max 1 (Q.μ univ) * ENNReal.ofReal (2 * Bz + 10 * Bz * Bz))
  have hBp : Bp ≠ ⊤ := by
    have : max 1 (Q.μ univ) ≠ ⊤ := max_ne_top ENNReal.one_ne_top (measure_ne_top _ _)
    finiteness
  obtain ⟨CK, hCK, hVC⟩ := VarLip.variation_continuity FC h0 h01 h1 hK (r := r₀) (by omega) hKe
    (isCompactBankSet_singleton hθ) (yukawaLipOn_singleton FC θ) hBp
  have hcv := cVal_nonneg (d := 4)
  set h₁ := δ / (cVal 4 * B + 1)
  have hh₁ : 0 < h₁ := by positivity
  set N₄ := ⌈1 / h₁⌉₊ + 1
  refine ⟨Cm + Cd + 2 * Cs + 2 * (CK.toReal * Cd), by positivity, max (max N₁ N₂) (max N₃ N₄),
    fun zs hzs N hN₀ hN => ?_⟩
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN₀)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN₀)
  have hN₃ : N₃ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN₀)
  have hN₄ : N₄ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN₀)
  set h : ℝ := 1 / N with hhdef
  have hh : 0 < h := one_div_N_pos hN
  have hmono : ∀ a : ℝ, a ≤ Cm + Cd + 2 * Cs + 2 * (CK.toReal * Cd) →
      ENNReal.ofReal (a * h) ≤ ENNReal.ofReal ((Cm + Cd + 2 * Cs + 2 * (CK.toReal * Cd)) * h) :=
    fun a ha => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ha hh.le)
  have hCKt : 0 ≤ CK.toReal := ENNReal.toReal_nonneg
  have hdk := hDK zs hzs N hN₃ hN
  refine ⟨(hMC zs.z hzs N hN₁ hN).trans (hmono _ (by nlinarith [mul_nonneg hCKt hCd])),
    hdk.trans (hmono _ (by nlinarith [mul_nonneg hCKt hCd])), fun hcrit => ?_⟩
  -- the stationarity clause
  have hhh₁ : h ≤ h₁ := by
    have hN' : (1 / h₁ : ℝ) < N := by
      have := Nat.le_ceil (1 / h₁)
      have h2 : ((⌈1 / h₁⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN₄
      push_cast at h2
      linarith
    rw [hhdef, div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hh₁] at hN'
    linarith
  set zh := reconSmooth FC T hN hzs
  have hzhC : FieldC11 FC zh.z Bz := fieldC11_reconFields FC hzs.c11 hh (one_div_N_le_one hN)
  have hzhK : ∀ y, zh.z.e y ∈ Ke := fun y => by
    refine mem_cthickening_of_dist_le (zh.z.e y) (zs.z.e y) δ Kf (hzs.chart y) ?_
    rw [dist_eq_norm]
    refine (norm_recon_samp_sub_le' hzs.c11.e hh y).trans ?_
    have := hhh₁
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hpb₁ := packetBound_of_C11 FC Q zh hzhC hzhK
  have hpb₂ := packetBound_of_C11 FC Q (Ke := Ke) zs (hzs.c11.mono FC hBBz) fun y =>
    self_subset_cthickening (δ := δ) _ (hzs.chart y)
  refine iSup₂_le fun v hv => ENNReal.ofReal_le_ofReal ?_
  set v' : CrTest FC.left r₀ K := ⟨v.1, v.2⟩
  have hD : ∀ b, |firstVariation T FC θ b zh.z v.1 - firstVariation T FC θ b zs.z v.1| ≤
      CK.toReal * (Cd * h) := fun b => by
    have h1' := hVC zh zs θ θ (Set.mem_singleton θ) (Set.mem_singleton θ) hpb₁ hpb₂ b v'
    have hv1 : ENNReal.ofReal ‖v'‖ ≤ 1 := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hv
    have h2' : ENNReal.ofReal |firstVariation T FC θ b zh.z v.1 -
        firstVariation T FC θ b zs.z v.1| ≤ ENNReal.ofReal (CK.toReal * (Cd * h)) := by
      refine h1'.trans ?_
      calc CK * dK Q zh θ zs θ * ENNReal.ofReal ‖v'‖ ≤ CK * ENNReal.ofReal (Cd * h) * 1 := by
            gcongr
        _ = ENNReal.ofReal (CK.toReal * (Cd * h)) := by
            rw [mul_one, ENNReal.ofReal_mul hCKt, ENNReal.ofReal_toReal hCK]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2'
  have hS : ∀ b, |finiteVar (sectorAction FC θ P N b) (sampleRec FC (1 / N) zs.z)
      (liftRec FC P N (1 / N) (reconFields FC (1 / N) (sampleRec FC (1 / N) zs.z)) v.1) -
      firstVariation T FC θ b zh.z v.1| ≤ Cs * h := fun b =>
    hSB zs.z hzs N hN₂ hN v.1 v.2 hv b
  have hc := hcrit v.1 v.2
  rw [sum_sector_real] at hc ⊢
  have a1 := hS .gravity
  have a2 := hS .standardModel
  have d1 := hD .gravity
  have d2 := hD .standardModel
  rw [abs_le] at a1 a2 d1 d2 ⊢
  constructor <;> nlinarith [mul_nonneg hCKt (mul_nonneg hCd hh.le), mul_nonneg hCm hh.le,
    mul_nonneg hCd hh.le, mul_nonneg hCs hh.le]


/-! ### `prop:critical-shadowing`: the reconstruction clause -/

/-- **`prop:critical-shadowing`, reconstruction clause**: in a complete normed slice `X` with the
Newton hypotheses (S1)–(S3) at mesh `h = 1/N`, a reconstruction `R` with `R x₀ = 𝒥_h(q_h)` (the
sampled finite configuration) that is `d_K`-Lipschitz on the ball (S4), the unique finite critical
point `x_h^*` of the Newton ball satisfies `d_K(R x_h^*, z_*) ≤ (2 C_R M C₀ + C_S) h`; the sampling
rate `C_S` is the strong-packet rate of `exists_dK_sampling` (uniform over the family). -/
theorem critical_shadowing_reconstruction {B : ℝ} (hB : 0 ≤ B) {Kf : Set CoframeFibre}
    (hKf : IsCompact Kf) (hKfGL : Kf ⊆ coframeGL) {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁)
    (h1 : t₁ < T) (θ : CoefficientBank Ysec) :
    ∃ CS : ℝ, 0 ≤ CS ∧ ∃ N₀ : ℕ, ∀ (zs : SmoothFields T FC.left)
      (hzs : SampledFamily FC B Kf zs.z) (N : ℕ) (_ : N₀ ≤ N) (hN : 0 < N)
      {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      {F : X → X} {F' : X → X →L[ℝ] X} {Bi : X →L[ℝ] X} {x₀ : X} {r M L C₀ : ℝ}
      (_ : CriticalShadowing.Hypotheses F F' Bi x₀ r M L C₀ (1 / N))
      (R : X → SmoothFields T FC.left) (_ : R x₀ = reconSmooth FC T hN hzs) {CR : ℝ}
      (_ : 0 ≤ CR) (_ : ∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
        dK (slabChart t₀ t₁ h0 h01 h1 (T := T)) (R x) θ (R y) θ ≤ ENNReal.ofReal (CR * ‖x - y‖)),
      (∃! xs : X, xs ∈ closedBall x₀ (2 * M * C₀ * (1 / N)) ∧ F xs = 0) ∧
        ∀ xs ∈ closedBall x₀ (2 * M * C₀ * (1 / N)),
          dK (slabChart t₀ t₁ h0 h01 h1 (T := T)) (R xs) θ zs θ ≤
            ENNReal.ofReal ((2 * CR * M * C₀ + CS) * (1 / N)) := by
  obtain ⟨CS, hCS, N₀, hDK⟩ := exists_dK_sampling FC hB hKf hKfGL h0 h01 h1 θ
  refine ⟨CS, hCS, N₀, fun zs hzs N hN₀ hN X _ _ _ F F' Bi x₀ r M L C₀ H R hR0 CR hCR hRLip => ?_⟩
  refine ⟨CriticalShadowing.exists_unique_zero_in_newton_ball H, fun xs hxs => ?_⟩
  have hh : (0 : ℝ) < 1 / N := one_div_N_pos hN
  have hsub := CriticalShadowing.newtonBall_subset H
  have hρ := CriticalShadowing.newtonRadius_nonneg H
  have hx0 : x₀ ∈ closedBall x₀ r := mem_closedBall_self (le_trans hρ H.newton_le)
  have hM := H.M_nonneg; have hC₀ := H.C₀_nonneg
  have hd : ‖xs - x₀‖ ≤ 2 * M * C₀ * (1 / N) := by rw [← dist_eq_norm]; exact mem_closedBall.1 hxs
  calc dK (slabChart t₀ t₁ h0 h01 h1 (T := T)) (R xs) θ zs θ
      ≤ dK (slabChart t₀ t₁ h0 h01 h1 (T := T)) (R xs) θ (R x₀) θ +
          dK (slabChart t₀ t₁ h0 h01 h1 (T := T)) (R x₀) θ zs θ := dK_triangle _ _ _ _ _ _ _
    _ ≤ ENNReal.ofReal (CR * ‖xs - x₀‖) + ENNReal.ofReal (CS * (1 / N)) := by
        rw [hR0]
        exact add_le_add (hR0 ▸ hRLip xs (hsub hxs) x₀ hx0) (hDK zs hzs N hN₀ hN)
    _ ≤ ENNReal.ofReal (CR * (2 * M * C₀ * (1 / N))) + ENNReal.ofReal (CS * (1 / N)) := by
        gcongr
    _ = ENNReal.ofReal ((2 * CR * M * C₀ + CS) * (1 / N)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end Comparison
end EinsteinSM
end RenewalGeometry
