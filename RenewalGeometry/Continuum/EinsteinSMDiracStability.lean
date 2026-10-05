/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SymmetricHyperbolicStability
import RenewalGeometry.Continuum.EinsteinSMMainLimit

/-!
# `prop:dirac-stability` and the closed (C4b) route of `thm:certificate-packet` /
  `thm:main-limit` (Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMCompactnessCertificates.lean`: `Σ = 𝕋³` (fields on `ℝ⁴` periodic under
the spatial shifts `spatialShift k`, `k ∈ ℤ³`; the manuscript's `Σ` is a general closed
three-manifold), the compact subslab is `I × Σ`, `I = [t₀, t₁] ⊂ (0, T)`, and the hypotheses of
`prop:dirac-stability` are the ledger's `DiracStabilityHyp t₀ t₁ ψ` (residuals defined by the
equation, coefficients and data Cauchy, `W^{1,∞}`/`L^∞`/`L^∞_tH²_x` bounds, Hermitian `A^μ`,
uniformly positive `A⁰`).

* `stabHyp_of_diracStabilityHyp`: `DiracStabilityHyp` for smooth periodic fields gives the generic
  hypotheses `SymHypEnergy.StabHyp` (the `L^∞_tH²_x` bound is converted from `spatialH2`, i.e.
  `Σ_{j ≤ 2} ‖D^j_y ψ(t)‖_{L²}`, by `‖∂_jψ‖ ≤ ‖Dψ‖`, `‖∂_j∂_jψ‖ ≤ ‖D²ψ‖`).
* **`dirac_stability`** (`prop:dirac-stability`): the spinors are Cauchy in `C_t L²_x` and
  `C_t H¹_x` on `[t₀,t₁] × 𝕋³`, and Cauchy in `H¹(I × 𝕋³)` (all four first derivatives), by the
  `L²` energy inequality `SymHypEnergy.l2_energy_estimate` + Gronwall, the `L²`–`H²`
  interpolation `PeriodicCube.integral_norm_pd_sq_le`, and solving the system for `∂ₜψ`.
* `dirac_stability_limit_equation`: the final clause (residuals `→ 0` ⇒ the limit solves the
  limiting system), with the measurability of `B_h` read off the `L^∞` clause of
  `DiracStabilityHyp`.
* `h1Cauchy_chartBox`: hence Cauchy in `H¹(Q)` on every chart box `Q ⊂ I × ℝ³` (periodicity and
  side length `≤ 1` compare `Q` with the fundamental domain).
* **`diracRoute_spinorH1Cauchy`**: route (C4b) (`DiracStabilityRoute Q z`) implies
  `SpinorH1Cauchy Q z` — this discharges the hypothesis `hdirac` of `certificate_packet` and
  `main_limit`, giving **`certificate_packet_closed`** (`thm:certificate-packet`) and
  **`main_limit_closed`** (`thm:main-limit`) with no hypothesis beyond those of the ledger
  encodings.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry
namespace EinsteinSM
namespace DiracStab

open SymHypEnergy PeriodicCube
open SobolevOpen (pd)

set_option linter.unusedSectionVars false

/-! ### Conversions -/

theorem cube3_eq : cube3 = cubeD 3 := rfl

/-- An `L²(cube)` bound on a dominating function bounds the cube integral of `‖u‖²`. -/
theorem integral_sq_le_of_eLpNorm_le {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    {u : (Fin 3 → ℝ) → F} {v : (Fin 3 → ℝ) → G} (hu : Continuous u)
    (huv : ∀ y, ‖u y‖ ≤ ‖v y‖) {C : ℝ} (hC : 0 ≤ C)
    (hv : eLpNorm v 2 (volume.restrict cube3) ≤ ENNReal.ofReal C) :
    ∫ y in Icc (0 : Fin 3 → ℝ) 1, ‖u y‖ ^ 2 ≤ C ^ 2 := by
  have h1 : eLpNorm u 2 (volume.restrict cube3) ≤ ENNReal.ofReal C := (eLpNorm_mono huv).trans hv
  rw [setIntegral_congr_set (cubeD_ae_eq (d := 3)).symm, ← cube3_eq,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => sq_nonneg _)
      (hu.norm.pow 2).aestronglyMeasurable]
  have h2 : ∫⁻ y in cube3, ENNReal.ofReal (‖u y‖ ^ 2) = eLpNorm u 2 (volume.restrict cube3) ^ 2 := by
    rw [eLpNorm_two_sq]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [h2]
  have h3 : eLpNorm u 2 (volume.restrict cube3) ^ 2 ≤ ENNReal.ofReal C ^ 2 := by gcongr
  calc (eLpNorm u 2 (volume.restrict cube3) ^ 2).toReal ≤ (ENNReal.ofReal C ^ 2).toReal :=
        ENNReal.toReal_mono (by simp) h3
    _ = C ^ 2 := by rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hC]

theorem norm_pd_le_iteratedFDeriv_one {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : (Fin 3 → ℝ) → F) (j : Fin 3) (y : Fin 3 → ℝ) :
    ‖pd G j y‖ ≤ ‖iteratedFDeriv ℝ 1 G y‖ := by
  rw [norm_iteratedFDeriv_one]
  unfold SobolevOpen.pd
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [show (Pi.single j 1 : Fin 3 → ℝ) = ev j from rfl, norm_ev, mul_one]

theorem norm_pd_pd_le_iteratedFDeriv_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : (Fin 3 → ℝ) → F} (hG : ContDiff ℝ 2 G) (j : Fin 3) (y : Fin 3 → ℝ) :
    ‖pd (pd G j) j y‖ ≤ ‖iteratedFDeriv ℝ 2 G y‖ := by
  have hd : DifferentiableAt ℝ (fderiv ℝ G) y :=
    ((hG.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) y
  have hh := ((ContinuousLinearMap.apply ℝ F (ev j)).hasFDerivAt).comp y hd.hasFDerivAt
  have he : pd (pd G j) j y = iteratedFDeriv ℝ 2 G y ![ev j, ev j] := by
    rw [iteratedFDeriv_two_apply]
    unfold SobolevOpen.pd
    rw [show (fun z => fderiv ℝ G z (Pi.single j 1)) =
      (ContinuousLinearMap.apply ℝ F (ev j)) ∘ fderiv ℝ G from rfl, hh.fderiv]
    rfl
  rw [he]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  simp [norm_ev]

/-! ### From `DiracStabilityHyp` to the generic stability hypotheses -/

theorem ip_mv_eq {N : Type} [Fintype N] (A : N → N → ℂ) (ξ : N → ℂ) :
    ip ξ (mv A ξ) = (∑ i, ∑ j, star (ξ i) * A i j * ξ j).re := by
  unfold ip mv
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem mvec_eq_mv {N : Type} [Fintype N] : (mvec : (N → N → ℂ) → (N → ℂ) → N → ℂ) = mv := rfl

/-- **`DiracStabilityHyp` (for smooth spatially periodic fields on the open slab `(0,T) × ℝ³`)
gives the generic hypotheses `StabHyp`**, together with the `L^∞` measurability and the spatial
periodicity of the zeroth-order coefficients `B_h` (the inputs of `dirac_limit_equation` that
`StabHyp` does not carry). -/
theorem stabHyp_of_diracStabilityHyp {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {N : Type} [Fintype N] {ψ : ℕ → E4 → N → ℂ} (hsm : ∀ n, ContDiffOn ℝ ∞ (ψ n) (cylSlab T))
    (hper : ∀ n k x, ψ n (x + spatialShift k) = ψ n x) (hD : DiracStabilityHyp t₀ t₁ ψ) :
    ∃ (A : ℕ → Fin 4 → E4 → N → N → ℂ) (B : ℕ → E4 → N → N → ℂ) (c : ℝ) (Cb : ℝ≥0),
      StabHyp (d := 3) ψ A B 0 t₀ t₁ T c Cb ∧
      (∀ n, AEStronglyMeasurable (B n) (volume.restrict (SymHypEnergy.slab t₀ t₁))) ∧
      ∀ n k x, B n (x + spatialShift k) = B n x := by
  obtain ⟨A, B, hAper, hBper, hBm, hherm, ⟨c, hc, hpos⟩, ⟨Cb, hbd⟩, hcoef, hinit, hres⟩ := hD
  have hslab : ∀ t : ℝ, t ∈ Icc t₀ t₁ → ∀ y : Fin 3 → ℝ,
      (Fin.cons t y : E4) ∈ cylSlab T := fun t ht y =>
    ⟨h0.trans_le ht.1, ht.2.trans_lt h1⟩
  have hsl : ∀ n (t : ℝ), t ∈ Icc t₀ t₁ → ContDiff ℝ 2 (fun y : Fin 3 → ℝ => ψ n (Fin.cons t y)) :=
    fun n t ht => ((hsm n).of_le (by norm_cast)).comp_contDiff (contDiff_cons t)
      fun y => hslab t ht y
  -- the three `L²` bounds hidden in `spatialH2`
  have hH : ∀ n, ∀ t ∈ Icc t₀ t₁, ∀ j ∈ Finset.range 3,
      eLpNorm (fun y : Fin 3 → ℝ => ‖iteratedFDeriv ℝ j (fun y' => ψ n (Fin.cons t y')) y‖) 2
        (volume.restrict cube3) ≤ ENNReal.ofReal Cb := by
    intro n t ht j hj
    rw [ENNReal.ofReal_coe_nnreal]
    exact (Finset.single_le_sum (f := fun j => eLpNorm (fun y : Fin 3 → ℝ =>
      ‖iteratedFDeriv ℝ j (fun y' => ψ n (Fin.cons t y')) y‖) 2 (volume.restrict cube3))
      (fun _ _ => zero_le) hj).trans ((hbd n).2.2 t ht)
  refine ⟨A, B, c, Cb, ?_, hBm, hBper⟩
  exact
  { ha := h0
    h01 := h01
    hb := h1
    smooth := fun n => (hsm n).of_le (by norm_cast)
    ψper := fun n k x => hper n k x
    Aper := fun n μ k x => hAper n μ k x
    herm := fun n μ x i k => hherm n μ x i k
    hc := hc
    pos := fun n x hx ξ => by rw [ip_mv_eq]; exact hpos n x hx ξ
    Abound := fun n μ x hx => ((hbd n).1 μ).1 x hx
    Alip := fun n μ => ((hbd n).1 μ).2
    Bbound := fun n => (hbd n).2.1
    H0 := fun n t ht => by
      refine integral_sq_le_of_eLpNorm_le (v := fun y : Fin 3 → ℝ =>
        ‖iteratedFDeriv ℝ 0 (fun y' => ψ n (Fin.cons t y')) y‖) (hsl n t ht).continuous
        (fun y => by simp [norm_iteratedFDeriv_zero]) Cb.2 (hH n t ht 0 (by simp))
    H1 := fun n j t ht => by
      have hd : ∀ y : Fin 3 → ℝ, DifferentiableAt ℝ (ψ n) (Fin.cons t y) := fun y =>
        ((hsm n).contDiffAt ((isOpen_cylSlab T).mem_nhds (hslab t ht y))).differentiableAt
          (by simp)
      have hc1 : Continuous fun y : Fin 3 → ℝ => pd (ψ n) j.succ (Fin.cons t y) := by
        have : (fun y : Fin 3 → ℝ => pd (ψ n) j.succ (Fin.cons t y)) =
            pd (fun y => ψ n (Fin.cons t y)) j := by
          funext y; rw [pd_slice j (hd y)]
        rw [this]
        unfold SobolevOpen.pd
        exact ((hsl n t ht).continuous_fderiv (by norm_num)).clm_apply continuous_const
      refine integral_sq_le_of_eLpNorm_le (v := fun y : Fin 3 → ℝ =>
        ‖iteratedFDeriv ℝ 1 (fun y' => ψ n (Fin.cons t y')) y‖) hc1 (fun y => ?_) Cb.2
        (hH n t ht 1 (by simp))
      rw [← pd_slice j (hd y), norm_norm]
      exact norm_pd_le_iteratedFDeriv_one _ j y
    H2 := fun n j k t ht => by
      have hG := hsl n t ht
      have hGd : Differentiable ℝ (fun y : Fin 3 → ℝ => ψ n (Fin.cons t y)) :=
        hG.differentiable (by norm_num)
      have hp1 : ContDiff ℝ 1 (pd (fun y : Fin 3 → ℝ => ψ n (Fin.cons t y)) j) := by
        unfold SobolevOpen.pd
        exact (hG.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
      have he1 : pd (fun y : Fin 3 → ℝ => ψ n (Fin.cons t y) k) j =
          fun y => pd (fun y : Fin 3 → ℝ => ψ n (Fin.cons t y)) j y k := by
        funext y; exact pd_apply' (hGd y) k j
      have he2 : ∀ y, pd (pd (fun y : Fin 3 → ℝ => ψ n (Fin.cons t y) k) j) j y =
          pd (pd (fun y : Fin 3 → ℝ => ψ n (Fin.cons t y)) j) j y k := by
        intro y; rw [he1]; exact pd_apply' ((hp1.differentiable one_ne_zero) y) k j
      have hc2 : Continuous (pd (pd (fun y : Fin 3 → ℝ => ψ n (Fin.cons t y) k) j) j) := by
        have hk : ContDiff ℝ 2 (fun y : Fin 3 → ℝ => ψ n (Fin.cons t y) k) := contDiff_pi.mp hG k
        have hk1 : ContDiff ℝ 1 (pd (fun y : Fin 3 → ℝ => ψ n (Fin.cons t y) k) j) := by
          unfold SobolevOpen.pd
          exact (hk.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
        unfold SobolevOpen.pd
        exact (hk1.continuous_fderiv one_ne_zero).clm_apply continuous_const
      refine integral_sq_le_of_eLpNorm_le (v := fun y : Fin 3 → ℝ =>
        ‖iteratedFDeriv ℝ 2 (fun y' => ψ n (Fin.cons t y')) y‖) hc2 (fun y => ?_) Cb.2
        (hH n t ht 2 (by simp))
      rw [he2, norm_norm]
      exact (norm_le_pi_norm _ k).trans (norm_pd_pd_le_iteratedFDeriv_two hG j y)
    coef := fun ε hε => by
      obtain ⟨N₀, hN₀⟩ := hcoef ε hε
      exact ⟨N₀, fun m hm n hn => hN₀ m hm n hn⟩
    init := fun ε hε => by
      obtain ⟨N₀, hN₀⟩ := hinit (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
      refine ⟨N₀, fun m hm n hn => ?_⟩
      have hcm := (hsl m t₀ ⟨le_rfl, h01.le⟩).continuous
      have hcn := (hsl n t₀ ⟨le_rfl, h01.le⟩).continuous
      have := integral_sq_le_of_eLpNorm_le (u := fun y : Fin 3 → ℝ =>
        ψ m (Fin.cons t₀ y) - ψ n (Fin.cons t₀ y)) (hcm.sub hcn) (fun y => le_rfl)
        (Real.sqrt_nonneg ε) (hN₀ m hm n hn)
      rwa [Real.sq_sqrt hε.le] at this
    res := fun ε hε => by
      obtain ⟨N₀, hN₀⟩ := hres ε hε
      exact ⟨N₀, fun m hm n hn => hN₀ m hm n hn⟩ }

/-! ### From the fundamental domain to chart boxes -/

theorem eLpNorm_le_of_sq_le {α F G : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    [NormedAddCommGroup G] {f : α → F} {g : α → G} {μ ν : Measure α}
    (h : eLpNorm f 2 μ ^ 2 ≤ eLpNorm g 2 ν ^ 2) : eLpNorm f 2 μ ≤ eLpNorm g 2 ν := by
  have := ENNReal.rpow_le_rpow h (z := ((2 : ℕ)⁻¹ : ℝ)) (by positivity)
  rwa [ENNReal.pow_rpow_inv_natCast two_ne_zero, ENNReal.pow_rpow_inv_natCast two_ne_zero]
    at this

/-- **Chart boxes inside the subslab are controlled by the fundamental domain**: for a spatially
periodic `f` continuous on the slab `[t₀,t₁] × ℝ³` and a chart box `Q` with time sides in
`[t₀,t₁]` (spatial sides `≤ 1`), `‖f‖_{L²(Q)} ≤ ‖f‖_{L²([t₀,t₁] × [0,1)³)}`. -/
theorem eLpNorm_chartBox_le' {T t₀ t₁ : ℝ} {F : Type*} [NormedAddCommGroup F] (Q : ChartBox T)
    (hQ0 : t₀ ≤ Q.a 0) (hQ1 : Q.b 0 ≤ t₁) {f : E4 → F}
    (hf : AEStronglyMeasurable f (volume.restrict (SymHypEnergy.slab t₀ t₁)))
    (hper : ∀ k x, f (x + spatialShift k) = f x) :
    eLpNorm f 2 Q.μ ≤ eLpNorm f 2 (volume.restrict (slabFundD (d := 3) t₀ t₁)) := by
  refine eLpNorm_le_of_sq_le ?_
  set a' : Fin 3 → ℝ := fun i => Q.a i.succ
  have hsub : Q.set ⊆ cyl (Icc t₀ t₁) (boxIoc a') := by
    intro x hx
    have hx' : ∀ i, x i ∈ Ioo (Q.a i) (Q.b i) := fun i => hx i (mem_univ i)
    refine ⟨⟨hQ0.trans (hx' 0).1.le, (hx' 0).2.le.trans hQ1⟩, fun i => ⟨(hx' i.succ).1, ?_⟩⟩
    have := Q.spatial_le i
    have := (hx' i.succ).2
    show x i.succ ≤ Q.a i.succ + 1
    linarith
  have hcylS : cyl (Icc t₀ t₁) (boxIoc a') ⊆ SymHypEnergy.slab t₀ t₁ := fun x hx => hx.1
  have hmeasC : MeasurableSet (cyl (Icc t₀ t₁) (boxIoc a')) :=
    measurableSet_cyl measurableSet_Icc (measurableSet_boxIoc a')
  have hae1 : AEMeasurable (fun x => ‖f x‖ₑ ^ 2) (volume.restrict (cyl (Icc t₀ t₁) (boxIoc a'))) :=
    (hf.mono_measure (Measure.restrict_mono hcylS le_rfl)).enorm.pow_const 2
  have hae2 : AEMeasurable (fun x => ‖f x‖ₑ ^ 2)
      (volume.restrict (cyl (Icc t₀ t₁) (cubeD 3))) := by
    rw [← slabFundD_eq]
    exact (hf.mono_measure (Measure.restrict_mono (slabFundD_subset t₀ t₁) le_rfl)).enorm.pow_const 2
  have hslice : ∀ t : ℝ, IsZPeriodic (fun y : Fin 3 → ℝ => ‖f (Fin.cons t y)‖ₑ ^ 2) := by
    intro t k y
    have := hper k (Fin.cons t y)
    rw [show (Fin.cons t y : E4) + spatialShift k = Fin.cons t (y + zvec k) by
      rw [spatialShift, cons_add_cons, add_zero]; rfl] at this
    simp only [this]
  rw [eLpNorm_two_sq, eLpNorm_two_sq, slabFundD_eq]
  calc ∫⁻ x in Q.set, ‖f x‖ₑ ^ 2 ≤ ∫⁻ x in cyl (Icc t₀ t₁) (boxIoc a'), ‖f x‖ₑ ^ 2 :=
        lintegral_mono_set hsub
    _ = ∫⁻ t in Icc t₀ t₁, ∫⁻ y in boxIoc a', ‖f (Fin.cons t y)‖ₑ ^ 2 :=
        lintegral_cyl measurableSet_Icc (measurableSet_boxIoc a') _ hae1
    _ = ∫⁻ t in Icc t₀ t₁, ∫⁻ y in cubeD 3, ‖f (Fin.cons t y)‖ₑ ^ 2 := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_boxIoc_eq_cube (hslice t), setLIntegral_congr (cubeD_ae_eq (d := 3))]
    _ = ∫⁻ x in cyl (Icc t₀ t₁) (cubeD 3), ‖f x‖ₑ ^ 2 :=
        (lintegral_cyl measurableSet_Icc (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
          _ hae2).symm

theorem measurableSet_slab' (t₀ t₁ : ℝ) : MeasurableSet (SymHypEnergy.slab (d := 3) t₀ t₁) :=
  measurableSet_Icc.preimage (measurable_pi_apply 0)

/-- `eLpNorm_chartBox_le'` for fields continuous on the slab. -/
theorem eLpNorm_chartBox_le {T t₀ t₁ : ℝ} {F : Type*} [NormedAddCommGroup F] (Q : ChartBox T)
    (hQ0 : t₀ ≤ Q.a 0) (hQ1 : Q.b 0 ≤ t₁) {f : E4 → F}
    (hf : ContinuousOn f (SymHypEnergy.slab t₀ t₁))
    (hper : ∀ k x, f (x + spatialShift k) = f x) :
    eLpNorm f 2 Q.μ ≤ eLpNorm f 2 (volume.restrict (slabFundD (d := 3) t₀ t₁)) :=
  eLpNorm_chartBox_le' Q hQ0 hQ1 (hf.aestronglyMeasurable (measurableSet_slab' t₀ t₁)) hper

theorem eLpNorm_slab_le_ofReal_nrm {t₀ t₁ : ℝ} {F : Type*} [NormedAddCommGroup F] {f : E4 → F}
    (hf : ContinuousOn f (SymHypEnergy.slab t₀ t₁)) :
    eLpNorm f 2 (volume.restrict (slabFundD (d := 3) t₀ t₁)) = ENNReal.ofReal (nrm t₀ t₁ f) := by
  rw [nrm, ENNReal.ofReal_toReal (memLp_slab hf).eLpNorm_ne_top]

theorem pd_periodic' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F}
    (hf : ∀ k x, f (x + spatialShift k) = f x) (μ : Fin 4) :
    ∀ k x, pd f μ (x + spatialShift k) = pd f μ x := fun k x => by
  unfold SobolevOpen.pd
  have h : (fun z => f (z + spatialShift k)) = f := funext (hf k)
  rw [← fderiv_comp_add_right, h]

/-! ### `prop:dirac-stability` -/

/-- `prop:dirac-stability` from the generic hypotheses `StabHyp` (explicit coefficients): fields are Cauchy in `C_t L²_x`
(`sup_t ‖ψ_m(t) - ψ_n(t)‖²_{L²(𝕋³)} → 0`), in `C_t H¹_x` (spatial derivatives), and in
`H¹(I × 𝕋³)` (values and all four first derivatives in `L²(I × [0,1)³)`). -/
theorem dirac_stability_of_stabHyp {T t₀ t₁ : ℝ} {N : Type} [Fintype N] {ψ : ℕ → E4 → N → ℂ}
    {A : ℕ → Fin 4 → E4 → N → N → ℂ} {B : ℕ → E4 → N → N → ℂ} {c : ℝ} {Cb : ℝ≥0}
    (hS : StabHyp (d := 3) ψ A B 0 t₀ t₁ T c Cb) :
    ∀ δ > (0 : ℝ), ∃ N₀ : ℕ, ∀ m ≥ N₀, ∀ n ≥ N₀,
      (∀ t ∈ Icc t₀ t₁, ∫ y in Icc (0 : Fin 3 → ℝ) 1,
        ‖ψ m (Fin.cons t y) - ψ n (Fin.cons t y)‖ ^ 2 ≤ δ) ∧
      (∀ t ∈ Icc t₀ t₁, ∀ j : Fin 3, ∫ y in Icc (0 : Fin 3 → ℝ) 1,
        ‖pd (ψ m) j.succ (Fin.cons t y) - pd (ψ n) j.succ (Fin.cons t y)‖ ^ 2 ≤ δ) ∧
      eLpNorm (ψ m - ψ n) 2 (volume.restrict (slabFund t₀ t₁)) ≤ ENNReal.ofReal δ ∧
      ∀ μ : Fin 4, eLpNorm (fun x => pd (ψ m) μ x - pd (ψ n) μ x) 2
        (volume.restrict (slabFund t₀ t₁)) ≤ ENNReal.ofReal δ := by
  intro δ hδ
  obtain ⟨N₀, hN⟩ := hS.cauchy δ hδ
  refine ⟨N₀, fun m hm n hn => ?_⟩
  obtain ⟨e1, e2, e3, e4⟩ := hN m hm n hn
  have hw : ContinuousOn (ψ m - ψ n) (SymHypEnergy.slab t₀ t₁) := (hS.cont m).sub (hS.cont n)
  refine ⟨fun t ht => e1 t ht, fun t ht j => ?_, ?_, fun μ => ?_⟩
  · have := e2 t ht j
    refine le_of_eq_of_le (integral_congr_ae (Eventually.of_forall fun y => ?_)) this
    simp only
    rw [hS.pd_diff_eq m n j.succ ((cons_mem_slab y).mpr ht)]
  · rw [show slabFund t₀ t₁ = slabFundD (d := 3) t₀ t₁ from rfl, eLpNorm_slab_le_ofReal_nrm hw]
    exact ENNReal.ofReal_le_ofReal e3
  · have hc : ContinuousOn (fun x => pd (ψ m) μ x - pd (ψ n) μ x) (SymHypEnergy.slab t₀ t₁) :=
      (hS.pdcont m μ).sub (hS.pdcont n μ)
    rw [show slabFund t₀ t₁ = slabFundD (d := 3) t₀ t₁ from rfl, eLpNorm_slab_le_ofReal_nrm hc]
    refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) (e4 μ))
    unfold nrm
    congr 1
    refine eLpNorm_congr_ae ((ae_restrict_mem (measurableSet_slabFundD t₀ t₁)).mono
      fun x hx => ?_)
    exact (hS.pd_diff_eq m n μ (slabFundD_subset t₀ t₁ hx)).symm

/-- **`prop:dirac-stability`** (on `I × 𝕋³`, `I = [t₀,t₁] ⊂ (0,T)`): smooth spatially periodic
fields satisfying the hypotheses `DiracStabilityHyp t₀ t₁ ψ` are Cauchy in `C_t L²_x`
(`sup_t ‖ψ_m(t) - ψ_n(t)‖²_{L²(𝕋³)} → 0`), in `C_t H¹_x` (spatial derivatives), and in
`H¹(I × 𝕋³)` (values and all four first derivatives in `L²(I × [0,1)³)`). -/
theorem dirac_stability {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {N : Type} [Fintype N] {ψ : ℕ → E4 → N → ℂ} (hsm : ∀ n, ContDiffOn ℝ ∞ (ψ n) (cylSlab T))
    (hper : ∀ n k x, ψ n (x + spatialShift k) = ψ n x) (hD : DiracStabilityHyp t₀ t₁ ψ) :
    ∀ δ > (0 : ℝ), ∃ N₀ : ℕ, ∀ m ≥ N₀, ∀ n ≥ N₀,
      (∀ t ∈ Icc t₀ t₁, ∫ y in Icc (0 : Fin 3 → ℝ) 1,
        ‖ψ m (Fin.cons t y) - ψ n (Fin.cons t y)‖ ^ 2 ≤ δ) ∧
      (∀ t ∈ Icc t₀ t₁, ∀ j : Fin 3, ∫ y in Icc (0 : Fin 3 → ℝ) 1,
        ‖pd (ψ m) j.succ (Fin.cons t y) - pd (ψ n) j.succ (Fin.cons t y)‖ ^ 2 ≤ δ) ∧
      eLpNorm (ψ m - ψ n) 2 (volume.restrict (slabFund t₀ t₁)) ≤ ENNReal.ofReal δ ∧
      ∀ μ : Fin 4, eLpNorm (fun x => pd (ψ m) μ x - pd (ψ n) μ x) 2
        (volume.restrict (slabFund t₀ t₁)) ≤ ENNReal.ofReal δ := by
  obtain ⟨A, B, c, Cb, hS, -, -⟩ := stabHyp_of_diracStabilityHyp h0 h01 h1 hsm hper hD
  exact dirac_stability_of_stabHyp hS

/-- `prop:dirac-stability` on chart boxes, from the generic hypotheses `StabHyp`. -/
theorem h1Cauchy_chartBox_of_stabHyp {T t₀ t₁ : ℝ} (Q : ChartBox T) (hQ0 : t₀ ≤ Q.a 0)
    (hQ1 : Q.b 0 ≤ t₁) {N : Type} [Fintype N] {ψ : ℕ → E4 → N → ℂ}
    {A : ℕ → Fin 4 → E4 → N → N → ℂ} {B : ℕ → E4 → N → N → ℂ} {c : ℝ} {Cb : ℝ≥0}
    (hS : StabHyp (d := 3) ψ A B 0 t₀ t₁ T c Cb)
    (hper : ∀ n k x, ψ n (x + spatialShift k) = ψ n x) :
    H1Cauchy Q ψ (fun n x i => pd (ψ n) i x) := by
  intro ε hε
  obtain ⟨N₀, hN⟩ := dirac_stability_of_stabHyp hS (ε / 5) (by positivity)
  refine ⟨N₀, fun m hm n hn => ?_⟩
  obtain ⟨-, -, e3, e4⟩ := hN m hm n hn
  have hw : ContinuousOn (ψ m - ψ n) (SymHypEnergy.slab t₀ t₁) := (hS.cont m).sub (hS.cont n)
  have hwper : ∀ k x, (ψ m - ψ n) (x + spatialShift k) = (ψ m - ψ n) x := fun k x => by
    simp [hper m k x, hper n k x]
  have hpc : ∀ μ, ContinuousOn (fun x => pd (ψ m) μ x - pd (ψ n) μ x)
      (SymHypEnergy.slab t₀ t₁) := fun μ => (hS.pdcont m μ).sub (hS.pdcont n μ)
  have hpper : ∀ μ k x, (fun x => pd (ψ m) μ x - pd (ψ n) μ x) (x + spatialShift k) =
      (fun x => pd (ψ m) μ x - pd (ψ n) μ x) x := fun μ k x => by
    simp only [pd_periodic' (hper m) μ k x, pd_periodic' (hper n) μ k x]
  have hQs : Q.set ⊆ SymHypEnergy.slab t₀ t₁ := fun x hx =>
    ⟨hQ0.trans (hx 0 (mem_univ 0)).1.le, (hx 0 (mem_univ 0)).2.le.trans hQ1⟩
  -- the value part
  have hv : eLpNorm (ψ m - ψ n) 2 Q.μ ≤ ENNReal.ofReal (ε / 5) :=
    (eLpNorm_chartBox_le Q hQ0 hQ1 hw hwper).trans e3
  -- the gradient part
  have hg : eLpNorm ((fun x i => pd (ψ m) i x) - fun x i => pd (ψ n) i x) 2 Q.μ ≤
      ∑ μ : Fin 4, ENNReal.ofReal (ε / 5) := by
    have hmeas : ∀ μ ∈ (Finset.univ : Finset (Fin 4)), AEStronglyMeasurable
        (fun x => ‖pd (ψ m) μ x - pd (ψ n) μ x‖) Q.μ := fun μ _ =>
      ((hpc μ).mono hQs).norm.aestronglyMeasurable Q.isOpen.measurableSet
    have hpt : ∀ x, ‖((fun x i => pd (ψ m) i x) - fun x i => pd (ψ n) i x) x‖ ≤
        ‖(∑ μ : Fin 4, fun x => ‖pd (ψ m) μ x - pd (ψ n) μ x‖) x‖ := by
      intro x
      rw [Finset.sum_apply, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun μ _ => norm_nonneg _)]
      refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun μ _ => norm_nonneg _)).mpr
        fun i => ?_
      exact Finset.single_le_sum (f := fun μ => ‖pd (ψ m) μ x - pd (ψ n) μ x‖)
        (fun μ _ => norm_nonneg _) (Finset.mem_univ i)
    refine (eLpNorm_mono hpt).trans ((eLpNorm_sum_le hmeas (by norm_num)).trans
      (Finset.sum_le_sum fun μ _ => ?_))
    rw [eLpNorm_norm]
    exact (eLpNorm_chartBox_le Q hQ0 hQ1 (hpc μ) (hpper μ)).trans (e4 μ)
  unfold h1Norm
  calc eLpNorm (ψ m - ψ n) 2 Q.μ +
      eLpNorm ((fun x i => pd (ψ m) i x) - fun x i => pd (ψ n) i x) 2 Q.μ
      ≤ ENNReal.ofReal (ε / 5) + ∑ _μ : Fin 4, ENNReal.ofReal (ε / 5) := add_le_add hv hg
    _ = ENNReal.ofReal ε := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [show ((4 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- **`prop:dirac-stability` on chart boxes**: the hypotheses of `prop:dirac-stability` on a
subslab `[t₀, t₁] × 𝕋³` containing the chart box `Q` give `H¹(Q)`-Cauchy fields (values and all
four classical first derivatives). -/
theorem h1Cauchy_chartBox {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    (Q : ChartBox T) (hQ0 : t₀ ≤ Q.a 0) (hQ1 : Q.b 0 ≤ t₁)
    {N : Type} [Fintype N] {ψ : ℕ → E4 → N → ℂ} (hsm : ∀ n, ContDiffOn ℝ ∞ (ψ n) (cylSlab T))
    (hper : ∀ n k x, ψ n (x + spatialShift k) = ψ n x) (hD : DiracStabilityHyp t₀ t₁ ψ) :
    H1Cauchy Q ψ (fun n x i => pd (ψ n) i x) := by
  obtain ⟨A, B, c, Cb, hS, -, -⟩ := stabHyp_of_diracStabilityHyp h0 h01 h1 hsm hper hD
  exact h1Cauchy_chartBox_of_stabHyp Q hQ0 hQ1 hS hper

/-! ### The limit equation (final clause of `prop:dirac-stability`) -/

/-- A Cauchy sequence in `L²` has an `L²` limit. -/
theorem exists_L2_limit {F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {μ : Measure E4}
    {u : ℕ → E4 → F} (hu : ∀ n, MemLp (u n) 2 μ)
    (hc : ∀ ε > (0 : ℝ), ∃ N, ∀ m ≥ N, ∀ n ≥ N, eLpNorm (u m - u n) 2 μ ≤ ENNReal.ofReal ε) :
    ∃ u₀, MemLp u₀ 2 μ ∧ Tendsto (fun n => eLpNorm (u n - u₀) 2 μ) atTop (𝓝 0) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set v : ℕ → Lp F 2 μ := fun n => (hu n).toLp (u n)
  have hcs : CauchySeq v := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε / 2) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [Lp.dist_def]
    have he : eLpNorm (⇑(v m) - ⇑(v n)) 2 μ = eLpNorm (u m - u n) 2 μ :=
      eLpNorm_congr_ae ((hu m).coeFn_toLp.sub (hu n).coeFn_toLp)
    rw [he]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hN m hm n hn)
    rw [ENNReal.toReal_ofReal (by positivity)] at this
    linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨L, Lp.memLp L, ?_⟩
  have := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' v L).mp hL
  refine this.congr fun n => eLpNorm_congr_ae ?_
  exact (hu n).coeFn_toLp.sub (EventuallyEq.refl _ _)

/-- Uniformly Cauchy sequences converge uniformly. -/
theorem exists_unif_limit {X F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {S : Set X}
    {f : ℕ → X → F} (hc : ∀ ε > (0 : ℝ), ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ x ∈ S, ‖f m x - f n x‖ ≤ ε) :
    ∃ f₀ : X → F, ∀ ε > (0 : ℝ), ∃ N, ∀ n ≥ N, ∀ x ∈ S, ‖f n x - f₀ x‖ ≤ ε := by
  have hcs : ∀ x ∈ S, CauchySeq fun n => f n x := by
    intro x hx
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε / 2) (by positivity)
    exact ⟨N, fun m hm n hn => by
      rw [dist_eq_norm]; linarith [hN m hm n hn x hx]⟩
  refine ⟨fun x => limUnder atTop fun n => f n x, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hc ε hε
  refine ⟨N, fun n hn x hx => ?_⟩
  have hlim := (hcs x hx).tendsto_limUnder
  have h2 : Tendsto (fun m => ‖f n x - f m x‖) atTop (𝓝 ‖f n x - limUnder atTop fun n => f n x‖) :=
    (tendsto_const_nhds.sub hlim).norm
  exact le_of_tendsto h2 (eventually_atTop.mpr ⟨N, fun m hm => hN n hn m hm x hx⟩)

theorem tendsto_of_unif {F : Type*} [NormedAddCommGroup F] {f : ℕ → F} {f₀ : F}
    (h : ∀ ε > (0 : ℝ), ∃ N, ∀ n ≥ N, ‖f n - f₀‖ ≤ ε) : Tendsto f atTop (𝓝 f₀) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := h (ε / 2) (by positivity)
  exact ⟨N, fun n hn => by rw [dist_eq_norm]; linarith [hN n hn]⟩

theorem eLpNorm_const_mul_norm {F : Type*} [NormedAddCommGroup F] {μ : Measure E4} {a : ℝ}
    (ha : 0 ≤ a) (v : E4 → F) :
    eLpNorm (fun x => a * ‖v x‖) 2 μ = ENNReal.ofReal a * eLpNorm v 2 μ := by
  have : (fun x => a * ‖v x‖) = a • fun x => ‖v x‖ := rfl
  rw [this, eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal_abs, abs_of_nonneg ha]

/-- Domination by five `L²` real functions. -/
theorem eLpNorm_le_five {F : Type*} [NormedAddCommGroup F] {μ : Measure E4} {E : E4 → F}
    (h : Fin 5 → E4 → ℝ) (hm : ∀ i, AEStronglyMeasurable (h i) μ) (b : Fin 5 → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hb : ∀ i, eLpNorm (h i) 2 μ ≤ ENNReal.ofReal (b i))
    (hle : ∀ᵐ x ∂μ, ‖E x‖ ≤ ∑ i, h i x) :
    eLpNorm E 2 μ ≤ ENNReal.ofReal (∑ i, b i) := by
  have h1 : eLpNorm E 2 μ ≤ eLpNorm (∑ i, h i) 2 μ :=
    eLpNorm_mono_ae (hle.mono fun x hx => by
      rw [Finset.sum_apply, Real.norm_eq_abs]; exact hx.trans (le_abs_self _))
  refine h1.trans ((eLpNorm_sum_le (fun i _ => hm i) (by norm_num)).trans ?_)
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => hb0 i]
  exact Finset.sum_le_sum fun i _ => hb i

set_option maxHeartbeats 1000000 in
/-- **The final clause of `prop:dirac-stability`: the limit solves the limiting system.**  For
`C^∞` periodic solutions with the generic hypotheses `StabHyp` (explicit coefficients), `L^∞`
(i.e. measurable, bounded) periodic coefficients `B_h`, and residuals `r_h → 0` in
`L²(I × 𝕋³)`, on every chart box `Q ⊂ I × ℝ³`: `ψ_h → ψ` in `H¹(Q)` with `ψ ∈ H¹(Q)` (weak
gradient `g`), `A_h^μ → A^μ` uniformly and `B_h → B` in `L^∞` on the slab, and
`A^μ ∂_μψ + Bψ = 0` a.e. on `Q`. -/
theorem dirac_limit_equation {T t₀ t₁ : ℝ} (Q : ChartBox T) (hQ0 : t₀ ≤ Q.a 0) (hQ1 : Q.b 0 ≤ t₁)
    {N : Type} [Fintype N] {ψ : ℕ → E4 → N → ℂ} {A : ℕ → Fin 4 → E4 → N → N → ℂ}
    {B : ℕ → E4 → N → N → ℂ} {c : ℝ} {Cb : ℝ≥0} (hS : StabHyp (d := 3) ψ A B 0 t₀ t₁ T c Cb)
    (hsm : ∀ n, ContDiffOn ℝ ∞ (ψ n) (cylSlab T))
    (hBm : ∀ n, AEStronglyMeasurable (B n) (volume.restrict (SymHypEnergy.slab t₀ t₁)))
    (hBper : ∀ n k x, B n (x + spatialShift k) = B n x)
    (hr : Tendsto (fun n => eLpNorm (resid (A n) (B n) (ψ n)) 2
      (volume.restrict (slabFundD (d := 3) t₀ t₁))) atTop (𝓝 0)) :
    ∃ (ψ₀ : E4 → N → ℂ) (g₀ : E4 → Fin 4 → N → ℂ) (A₀ : Fin 4 → E4 → N → N → ℂ)
      (B₀ : E4 → N → N → ℂ),
      MemH1 Q ψ₀ g₀ ∧ H1Tendsto Q ψ (fun n x i => pd (ψ n) i x) ψ₀ g₀ ∧
      (∀ ε > (0 : ℝ), ∃ N₀, ∀ n ≥ N₀, ∀ μ, ∀ x ∈ SymHypEnergy.slab t₀ t₁,
        ‖A n μ x - A₀ μ x‖ ≤ ε) ∧
      (∀ ε > (0 : ℝ), ∃ N₀, ∀ n ≥ N₀, ∀ᵐ x ∂(volume.restrict (SymHypEnergy.slab t₀ t₁)),
        ‖B n x - B₀ x‖ ≤ ε) ∧
      ∀ᵐ x ∂Q.μ, ∑ μ, mv (A₀ μ x) (g₀ x μ) + mv (B₀ x) (ψ₀ x) = 0 := by
  have hper : ∀ n k x, ψ n (x + spatialShift k) = ψ n x := fun n k x => hS.ψper n k x
  have hcauchy := h1Cauchy_chartBox_of_stabHyp Q hQ0 hQ1 hS hper
  have hmem : ∀ n, MemH1 Q (ψ n) (fun x i c => pd (ψ n) i x c) := fun n =>
    memH1_of_smooth Q (hsm n)
  have hu : ∀ n, MemLp (ψ n) 2 Q.μ := fun n => memLp_pi_iff.mpr fun c => (hmem n c).memLp
  have hg : ∀ n, MemLp (fun x i => pd (ψ n) i x) 2 Q.μ := fun n =>
    memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun c => (hmem n c).memLp_grad i
  -- limits of values and gradients
  obtain ⟨ψ₀, hψ₀, hψlim⟩ := exists_L2_limit hu fun ε hε => by
    obtain ⟨N₀, hN₀⟩ := hcauchy ε hε
    exact ⟨N₀, fun m hm n hn => le_self_add.trans (hN₀ m hm n hn)⟩
  obtain ⟨g₀, hg₀, hglim⟩ := exists_L2_limit hg fun ε hε => by
    obtain ⟨N₀, hN₀⟩ := hcauchy ε hε
    exact ⟨N₀, fun m hm n hn => le_add_self.trans (hN₀ m hm n hn)⟩
  -- coefficient limits
  obtain ⟨A₀', hA₀'⟩ := exists_unif_limit (S := univ ×ˢ SymHypEnergy.slab t₀ t₁)
    (f := fun n (p : Fin 4 × E4) => A n p.1 p.2) fun ε hε => by
      obtain ⟨N₀, hN₀⟩ := hS.coef ε hε
      exact ⟨N₀, fun m hm n hn p hp => (hN₀ m hm n hn).1 p.1 p.2 hp.2⟩
  set A₀ : Fin 4 → E4 → N → N → ℂ := fun μ x => A₀' (μ, x) with hA₀def
  have hAlim : ∀ ε > (0 : ℝ), ∃ N₀, ∀ n ≥ N₀, ∀ μ, ∀ x ∈ SymHypEnergy.slab t₀ t₁,
      ‖A n μ x - A₀ μ x‖ ≤ ε := fun ε hε => by
    obtain ⟨N₀, hN₀⟩ := hA₀' ε hε
    exact ⟨N₀, fun n hn μ x hx => hN₀ n hn (μ, x) ⟨mem_univ _, hx⟩⟩
  choose NB hNB using fun k : ℕ => hS.coef (1 / ((k : ℝ) + 1)) (by positivity)
  set G : Set E4 := {x | ∀ k : ℕ, ∀ m ≥ NB k, ∀ n ≥ NB k, ‖B m x - B n x‖ ≤ 1 / ((k : ℝ) + 1)}
  have hG : ∀ᵐ x ∂(volume.restrict (SymHypEnergy.slab t₀ t₁)), x ∈ G := by
    have hk : ∀ (k m n : ℕ), ∀ᵐ x ∂(volume.restrict (SymHypEnergy.slab t₀ t₁)),
        m ≥ NB k → n ≥ NB k → ‖B m x - B n x‖ ≤ 1 / ((k : ℝ) + 1) := by
      intro k m n
      by_cases hm : m ≥ NB k
      · by_cases hn : n ≥ NB k
        · exact ((hNB k m hm n hn).2).mono fun x hx _ _ => hx
        · exact Eventually.of_forall fun x _ h => absurd h hn
      · exact Eventually.of_forall fun x h => absurd h hm
    have := ae_all_iff.mpr fun k => ae_all_iff.mpr fun m => ae_all_iff.mpr fun n => hk k m n
    exact this.mono fun x hx k m hm n hn => hx k m n hm hn
  obtain ⟨B₀, hB₀⟩ := exists_unif_limit (S := G) (f := B) fun ε hε => by
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    exact ⟨NB k, fun m hm n hn x hx => (hx k m hm n hn).trans hk.le⟩
  have hBlim : ∀ ε > (0 : ℝ), ∃ N₀, ∀ n ≥ N₀, ∀ᵐ x ∂(volume.restrict (SymHypEnergy.slab t₀ t₁)),
      ‖B n x - B₀ x‖ ≤ ε := fun ε hε => by
    obtain ⟨N₀, hN₀⟩ := hB₀ ε hε
    exact ⟨N₀, fun n hn => hG.mono fun x hx => hN₀ n hn x hx⟩
  -- the weak gradient of the limit
  have hQsub : Q.set ⊆ SymHypEnergy.slab t₀ t₁ := fun x hx =>
    ⟨hQ0.trans (hx 0 (mem_univ 0)).1.le, (hx 0 (mem_univ 0)).2.le.trans hQ1⟩
  have hcomp : ∀ {M : Type} [Fintype M] (v : ℕ → E4 → M → ℂ) (v₀ : E4 → M → ℂ) (c : M),
      Tendsto (fun n => eLpNorm (v n - v₀) 2 Q.μ) atTop (𝓝 0) →
      Tendsto (fun n => eLpNorm ((fun x => v n x c) - fun x => v₀ x c) 2 Q.μ) atTop (𝓝 0) := by
    intro M _ v v₀ c h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => zero_le)
      fun n => eLpNorm_mono fun x => ?_
    exact norm_le_pi_norm ((v n - v₀) x) c
  have hcompG : ∀ (i : Fin 4) (c : N), Tendsto (fun n => eLpNorm ((fun x => pd (ψ n) i x c) -
      fun x => g₀ x i c) 2 Q.μ) atTop (𝓝 0) := by
    intro i c
    have h1 : Tendsto (fun n => eLpNorm ((fun x => pd (ψ n) i x) - fun x => g₀ x i) 2 Q.μ)
        atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglim (fun n => zero_le)
        fun n => eLpNorm_mono fun x => norm_le_pi_norm
          (((fun x i => pd (ψ n) i x) - g₀) x) i
    exact hcomp (fun n x => pd (ψ n) i x) (fun x => g₀ x i) c h1
  have hH1 : MemH1 Q ψ₀ g₀ := by
    intro c
    refine ⟨memLp_pi_iff.mp hψ₀ c, fun i => memLp_pi_iff.mp (memLp_pi_iff.mp hg₀ i) c,
      fun i => ?_⟩
    exact SobolevOpen.hasWeakPartial_of_tendsto Q.isOpen.measurableSet (SobolevOpen.volume_box_ne_top _ _)
      (u := fun k x => ψ k x c) (g := fun k x => pd (ψ k) i x c) (fun k => (hmem k c).weak i)
      (fun k => (hmem k c).memLp) (fun k => (hmem k c).memLp_grad i) (memLp_pi_iff.mp hψ₀ c)
      (memLp_pi_iff.mp (memLp_pi_iff.mp hg₀ i) c) (hcomp ψ ψ₀ c hψlim) (hcompG i c)
  have hH1t : H1Tendsto Q ψ (fun n x i => pd (ψ n) i x) ψ₀ g₀ := by
    have := hψlim.add hglim
    simp only [add_zero] at this
    exact this
  refine ⟨ψ₀, g₀, A₀, B₀, hH1, hH1t, hAlim, hBlim, ?_⟩
  -- measurability on `Q`
  have hAm : ∀ n μ, AEStronglyMeasurable (A n μ) Q.μ := fun n μ =>
    ((hS.Acont n μ).mono hQsub).aestronglyMeasurable Q.isOpen.measurableSet
  have hA₀m : ∀ μ, AEStronglyMeasurable (A₀ μ) Q.μ := fun μ =>
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => hAm n μ)
      ((ae_restrict_mem Q.isOpen.measurableSet).mono fun x hx => tendsto_of_unif fun ε hε => by
        obtain ⟨N₀, hN₀⟩ := hAlim ε hε
        exact ⟨N₀, fun n hn => hN₀ n hn μ x (hQsub hx)⟩)
  have hBQ : ∀ n, AEStronglyMeasurable (B n) Q.μ := fun n =>
    (hBm n).mono_measure (Measure.restrict_mono hQsub le_rfl)
  have hGQ : ∀ᵐ x ∂Q.μ, x ∈ G := ae_restrict_of_ae_restrict_of_subset hQsub hG
  have hB₀m : AEStronglyMeasurable B₀ Q.μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hBQ (hGQ.mono fun x hx => tendsto_of_unif
      fun ε hε => by
        obtain ⟨N₀, hN₀⟩ := hB₀ ε hε
        exact ⟨N₀, fun n hn => hN₀ n hn x hx⟩)
  have hψ₀m : AEStronglyMeasurable ψ₀ Q.μ := hψ₀.1
  have hg₀m : AEStronglyMeasurable g₀ Q.μ := hg₀.1
  set E : E4 → N → ℂ := fun x => ∑ μ, mv (A₀ μ x) (g₀ x μ) + mv (B₀ x) (ψ₀ x) with hEdef
  have hmvc : Continuous fun p : (N → N → ℂ) × (N → ℂ) => mv p.1 p.2 := by
    unfold mv; fun_prop
  have hEm : AEStronglyMeasurable E Q.μ := by
    have h1 : ∀ μ, AEStronglyMeasurable (fun x => mv (A₀ μ x) (g₀ x μ)) Q.μ := fun μ =>
      hmvc.comp_aestronglyMeasurable ((hA₀m μ).prodMk
        ((continuous_apply μ).comp_aestronglyMeasurable hg₀m))
    have h2 : AEStronglyMeasurable (fun x => mv (B₀ x) (ψ₀ x)) Q.μ :=
      hmvc.comp_aestronglyMeasurable (hB₀m.prodMk hψ₀m)
    exact (Finset.univ.aestronglyMeasurable_fun_sum fun μ _ => h1 μ).add h2
  -- the residual is measurable and periodic
  have hRm : ∀ n, AEStronglyMeasurable (resid (A n) (B n) (ψ n))
      (volume.restrict (SymHypEnergy.slab t₀ t₁)) := by
    intro n
    have h1 : AEStronglyMeasurable (princ (A n) (ψ n)) (volume.restrict (SymHypEnergy.slab t₀ t₁)) :=
      (hS.princ_cont n n).aestronglyMeasurable (measurableSet_slab' t₀ t₁)
    have hψm : AEStronglyMeasurable (ψ n) (volume.restrict (SymHypEnergy.slab t₀ t₁)) :=
      (hS.cont n).aestronglyMeasurable (measurableSet_slab' t₀ t₁)
    have h2 : AEStronglyMeasurable (fun x => mv (B n x) (ψ n x))
        (volume.restrict (SymHypEnergy.slab t₀ t₁)) :=
      hmvc.comp_aestronglyMeasurable ((hBm n).prodMk hψm)
    exact h1.add h2
  have hRper : ∀ n k x, resid (A n) (B n) (ψ n) (x + spatialShift k) =
      resid (A n) (B n) (ψ n) x := by
    intro n k x
    have hAp : ∀ μ, A n μ (x + spatialShift k) = A n μ x := fun μ => hS.Aper n μ k x
    have hpp : ∀ μ, pd (ψ n) μ (x + spatialShift k) = pd (ψ n) μ x := fun μ =>
      pd_periodic' (hper n) μ k x
    simp only [resid, princ, hBper n k x, hper n k x, hAp, hpp]
  -- the bound: for every `δ ∈ (0,1]`
  set n₀ : ℝ := (Fintype.card N : ℝ)
  have hn₀ : 0 ≤ n₀ := Nat.cast_nonneg _
  set mg := (eLpNorm g₀ 2 Q.μ).toReal
  set mψ := (eLpNorm ψ₀ 2 Q.μ).toReal
  have hmg : eLpNorm g₀ 2 Q.μ = ENNReal.ofReal mg := (ENNReal.ofReal_toReal hg₀.eLpNorm_ne_top).symm
  have hmψ : eLpNorm ψ₀ 2 Q.μ = ENNReal.ofReal mψ :=
    (ENNReal.ofReal_toReal hψ₀.eLpNorm_ne_top).symm
  set K : ℝ := 1 + 4 * n₀ * mg + 4 * n₀ * Cb + n₀ * mψ + n₀ * Cb
  have hbound : ∀ δ > (0 : ℝ), eLpNorm E 2 Q.μ ≤ ENNReal.ofReal (δ * K) := by
    intro δ hδ
    obtain ⟨NA, hNA⟩ := hAlim δ hδ
    obtain ⟨NBδ, hNBδ⟩ := hBlim δ hδ
    obtain ⟨Nr, hNr⟩ := eventually_atTop.mp (hr.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ)))
    obtain ⟨Nψ, hNψ⟩ := eventually_atTop.mp
      (hψlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ)))
    obtain ⟨Ng, hNg⟩ := eventually_atTop.mp
      (hglim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ)))
    set n := max (max NA NBδ) (max Nr (max Nψ Ng))
    have hnA : n ≥ NA := le_trans (le_max_left _ _) (le_max_left _ _)
    have hnB : n ≥ NBδ := le_trans (le_max_right _ _) (le_max_left _ _)
    have hnr : n ≥ Nr := le_trans (le_max_left _ _) (le_max_right _ _)
    have hnψ : n ≥ Nψ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    have hng : n ≥ Ng := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
    -- the five dominating functions
    set h : Fin 5 → E4 → ℝ := ![fun x => ‖resid (A n) (B n) (ψ n) x‖,
      fun x => (4 * n₀ * δ) * ‖g₀ x‖,
      fun x => (4 * n₀ * Cb) * ‖(g₀ - fun x i => pd (ψ n) i x) x‖,
      fun x => (n₀ * δ) * ‖ψ₀ x‖, fun x => (n₀ * Cb) * ‖(ψ₀ - ψ n) x‖] with hh
    have hm : ∀ i, AEStronglyMeasurable (h i) Q.μ := by
      intro i
      fin_cases i
      · exact ((hRm n).mono_measure (Measure.restrict_mono hQsub le_rfl)).norm
      · exact aestronglyMeasurable_const.mul hg₀m.norm
      · exact aestronglyMeasurable_const.mul (hg₀m.sub (hg n).1).norm
      · exact aestronglyMeasurable_const.mul hψ₀m.norm
      · exact aestronglyMeasurable_const.mul (hψ₀m.sub (hu n).1).norm
    have hle : ∀ᵐ x ∂Q.μ, ‖E x‖ ≤ ∑ i, h i x := by
      filter_upwards [ae_restrict_mem Q.isOpen.measurableSet,
        ae_restrict_of_ae_restrict_of_subset hQsub (hS.Bbound n),
        ae_restrict_of_ae_restrict_of_subset hQsub (hNBδ n hnB)] with x hx hBx hBδx
      have hxs := hQsub hx
      have hid : E x = resid (A n) (B n) (ψ n) x +
          ∑ μ, (mv (A₀ μ x - A n μ x) (g₀ x μ) + mv (A n μ x) (g₀ x μ - pd (ψ n) μ x)) +
          mv (B₀ x - B n x) (ψ₀ x) + mv (B n x) (ψ₀ x - ψ n x) := by
        simp only [hEdef, resid, princ, mv_sub, mv_sub_left, Finset.sum_add_distrib,
          Finset.sum_sub_distrib]
        abel
      rw [hid]
      have e1 : ‖∑ μ, (mv (A₀ μ x - A n μ x) (g₀ x μ) + mv (A n μ x) (g₀ x μ - pd (ψ n) μ x))‖ ≤
          (4 * n₀ * δ) * ‖g₀ x‖ + (4 * n₀ * Cb) * ‖(g₀ - fun x i => pd (ψ n) i x) x‖ := by
        refine (norm_sum_le _ _).trans ?_
        have : ∀ μ, ‖mv (A₀ μ x - A n μ x) (g₀ x μ) + mv (A n μ x) (g₀ x μ - pd (ψ n) μ x)‖ ≤
            n₀ * δ * ‖g₀ x‖ + n₀ * Cb * ‖(g₀ - fun x i => pd (ψ n) i x) x‖ := by
          intro μ
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · refine (norm_mv_le _ _).trans ?_
            rw [norm_sub_rev]
            calc n₀ * (‖A n μ x - A₀ μ x‖ * ‖g₀ x μ‖) ≤ n₀ * (δ * ‖g₀ x‖) := by
                  gcongr
                  · exact hNA n hnA μ x hxs
                  · exact norm_le_pi_norm (g₀ x) μ
              _ = _ := by ring
          · refine (norm_mv_le _ _).trans ?_
            calc n₀ * (‖A n μ x‖ * ‖g₀ x μ - pd (ψ n) μ x‖)
                ≤ n₀ * (Cb * ‖(g₀ - fun x i => pd (ψ n) i x) x‖) := by
                  gcongr
                  · exact hS.Abound n μ x hxs
                  · exact norm_le_pi_norm ((g₀ - fun x i => pd (ψ n) i x) x) μ
              _ = _ := by ring
        calc ∑ μ, ‖mv (A₀ μ x - A n μ x) (g₀ x μ) + mv (A n μ x) (g₀ x μ - pd (ψ n) μ x)‖
            ≤ ∑ _μ : Fin 4, (n₀ * δ * ‖g₀ x‖ + n₀ * Cb * ‖(g₀ - fun x i => pd (ψ n) i x) x‖) :=
              Finset.sum_le_sum fun μ _ => this μ
          _ = _ := by simp; ring
      have e2 : ‖mv (B₀ x - B n x) (ψ₀ x)‖ ≤ (n₀ * δ) * ‖ψ₀ x‖ := by
        refine (norm_mv_le _ _).trans ?_
        rw [norm_sub_rev]
        calc n₀ * (‖B n x - B₀ x‖ * ‖ψ₀ x‖) ≤ n₀ * (δ * ‖ψ₀ x‖) := by gcongr
          _ = _ := by ring
      have e3 : ‖mv (B n x) (ψ₀ x - ψ n x)‖ ≤ (n₀ * Cb) * ‖(ψ₀ - ψ n) x‖ := by
        refine (norm_mv_le _ _).trans ?_
        calc n₀ * (‖B n x‖ * ‖ψ₀ x - ψ n x‖) ≤ n₀ * (Cb * ‖ψ₀ x - ψ n x‖) := by gcongr
          _ = _ := by rw [Pi.sub_apply]; ring
      rw [Fin.sum_univ_five]
      show _ ≤ ‖resid (A n) (B n) (ψ n) x‖ + (4 * n₀ * δ) * ‖g₀ x‖ +
        (4 * n₀ * Cb) * ‖(g₀ - fun x i => pd (ψ n) i x) x‖ + (n₀ * δ) * ‖ψ₀ x‖ +
        (n₀ * Cb) * ‖(ψ₀ - ψ n) x‖
      have e0 : ‖resid (A n) (B n) (ψ n) x +
          ∑ μ, (mv (A₀ μ x - A n μ x) (g₀ x μ) + mv (A n μ x) (g₀ x μ - pd (ψ n) μ x)) +
          mv (B₀ x - B n x) (ψ₀ x) + mv (B n x) (ψ₀ x - ψ n x)‖ ≤
          ‖resid (A n) (B n) (ψ n) x‖ +
          ‖∑ μ, (mv (A₀ μ x - A n μ x) (g₀ x μ) + mv (A n μ x) (g₀ x μ - pd (ψ n) μ x))‖ +
          ‖mv (B₀ x - B n x) (ψ₀ x)‖ + ‖mv (B n x) (ψ₀ x - ψ n x)‖ := norm_add₄_le
      linarith
    set b : Fin 5 → ℝ := ![δ, 4 * n₀ * δ * mg, 4 * n₀ * Cb * δ, n₀ * δ * mψ, n₀ * Cb * δ] with hbdef
    have hb0 : ∀ i, 0 ≤ b i := by
      intro i
      have : 0 ≤ mg := ENNReal.toReal_nonneg
      have : 0 ≤ mψ := ENNReal.toReal_nonneg
      fin_cases i <;> simp [hbdef] <;> positivity
    have hb : ∀ i, eLpNorm (h i) 2 Q.μ ≤ ENNReal.ofReal (b i) := by
      intro i
      fin_cases i
      · show eLpNorm (fun x => ‖resid (A n) (B n) (ψ n) x‖) 2 Q.μ ≤ ENNReal.ofReal δ
        rw [eLpNorm_norm]
        exact (eLpNorm_chartBox_le' Q hQ0 hQ1 (hRm n) (hRper n)).trans (hNr n hnr).le
      · show eLpNorm (fun x => (4 * n₀ * δ) * ‖g₀ x‖) 2 Q.μ ≤ ENNReal.ofReal (4 * n₀ * δ * mg)
        rw [eLpNorm_const_mul_norm (by positivity), hmg, ← ENNReal.ofReal_mul (by positivity)]
      · show eLpNorm (fun x => (4 * n₀ * Cb) * ‖(g₀ - fun x i => pd (ψ n) i x) x‖) 2 Q.μ ≤
          ENNReal.ofReal (4 * n₀ * Cb * δ)
        rw [eLpNorm_const_mul_norm (by positivity),
          ENNReal.ofReal_mul (p := 4 * n₀ * Cb) (by positivity), eLpNorm_sub_comm]
        gcongr
        exact (hNg n hng).le
      · show eLpNorm (fun x => (n₀ * δ) * ‖ψ₀ x‖) 2 Q.μ ≤ ENNReal.ofReal (n₀ * δ * mψ)
        rw [eLpNorm_const_mul_norm (by positivity), hmψ, ← ENNReal.ofReal_mul (by positivity)]
      · show eLpNorm (fun x => (n₀ * Cb) * ‖(ψ₀ - ψ n) x‖) 2 Q.μ ≤ ENNReal.ofReal (n₀ * Cb * δ)
        rw [eLpNorm_const_mul_norm (by positivity),
          ENNReal.ofReal_mul (p := n₀ * Cb) (by positivity), eLpNorm_sub_comm]
        gcongr
        exact (hNψ n hnψ).le
    refine (eLpNorm_le_five h hm b hb0 hb hle).trans (le_of_eq ?_)
    congr 1
    rw [Fin.sum_univ_five]
    show δ + 4 * n₀ * δ * mg + 4 * n₀ * Cb * δ + n₀ * δ * mψ + n₀ * Cb * δ =
      δ * (1 + 4 * n₀ * mg + 4 * n₀ * Cb + n₀ * mψ + n₀ * Cb)
    ring
  -- conclude
  have hzero : eLpNorm E 2 Q.μ = 0 := by
    have hK0 : 0 ≤ K := by
      have : 0 ≤ mg := ENNReal.toReal_nonneg
      have : 0 ≤ mψ := ENNReal.toReal_nonneg
      positivity
    have ht : Tendsto (fun δ : ℝ => ENNReal.ofReal (δ * K)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun δ : ℝ => δ * K) (𝓝[>] 0) (𝓝 0) := by
        have h := (continuous_mul_right K).tendsto (0 : ℝ)
        rw [zero_mul] at h
        exact h.mono_left nhdsWithin_le_nhds
      simpa using ENNReal.tendsto_ofReal this
    exact le_antisymm (ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ hδ =>
      hbound δ hδ)) zero_le
  exact (eLpNorm_eq_zero_iff hEm two_ne_zero).mp hzero

/-- **`prop:dirac-stability` with its final clause, from the ledger hypotheses**: for smooth
spatially periodic fields satisfying `DiracStabilityHyp t₀ t₁ ψ` (whose `L^∞_{t,x}` clause on `B_h`
includes measurability), the coefficient systems `(A_h, B_h)` of the hypothesis satisfy `StabHyp`
(so `ψ_h` is Cauchy in `H¹`), and if the residuals `r_h = A_h^μ ∂_μψ_h + B_hψ_h` tend to `0` in
`L²(I × 𝕋³)`, then on every chart box `Q ⊂ I × ℝ³` the `H¹(Q)` limit `ψ` solves the limiting
system `A^μ ∂_μψ + Bψ = 0` a.e., with `A_h → A` uniformly and `B_h → B` in `L^∞` on the slab.
The measurability of `B_h` is taken from `DiracStabilityHyp` (no separate hypothesis). -/
theorem dirac_stability_limit_equation {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {N : Type} [Fintype N] {ψ : ℕ → E4 → N → ℂ} (hsm : ∀ n, ContDiffOn ℝ ∞ (ψ n) (cylSlab T))
    (hper : ∀ n k x, ψ n (x + spatialShift k) = ψ n x) (hD : DiracStabilityHyp t₀ t₁ ψ) :
    ∃ (A : ℕ → Fin 4 → E4 → N → N → ℂ) (B : ℕ → E4 → N → N → ℂ) (c : ℝ) (Cb : ℝ≥0),
      StabHyp (d := 3) ψ A B 0 t₀ t₁ T c Cb ∧
      ∀ Q : ChartBox T, t₀ ≤ Q.a 0 → Q.b 0 ≤ t₁ →
        Tendsto (fun n => eLpNorm (resid (A n) (B n) (ψ n)) 2
          (volume.restrict (slabFundD (d := 3) t₀ t₁))) atTop (𝓝 0) →
        ∃ (ψ₀ : E4 → N → ℂ) (g₀ : E4 → Fin 4 → N → ℂ) (A₀ : Fin 4 → E4 → N → N → ℂ)
          (B₀ : E4 → N → N → ℂ),
          MemH1 Q ψ₀ g₀ ∧ H1Tendsto Q ψ (fun n x i => pd (ψ n) i x) ψ₀ g₀ ∧
          (∀ ε > (0 : ℝ), ∃ N₀, ∀ n ≥ N₀, ∀ μ, ∀ x ∈ SymHypEnergy.slab t₀ t₁,
            ‖A n μ x - A₀ μ x‖ ≤ ε) ∧
          (∀ ε > (0 : ℝ), ∃ N₀, ∀ n ≥ N₀, ∀ᵐ x ∂(volume.restrict (SymHypEnergy.slab t₀ t₁)),
            ‖B n x - B₀ x‖ ≤ ε) ∧
          ∀ᵐ x ∂Q.μ, ∑ μ, mv (A₀ μ x) (g₀ x μ) + mv (B₀ x) (ψ₀ x) = 0 := by
  obtain ⟨A, B, c, Cb, hS, hBm, hBper⟩ := stabHyp_of_diracStabilityHyp h0 h01 h1 hsm hper hD
  exact ⟨A, B, c, Cb, hS, fun Q hQ0 hQ1 hr =>
    dirac_limit_equation Q hQ0 hQ1 hS hsm hBm hBper hr⟩

/-! ### The spinor route (C4b) and the closed main theorems -/

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool}

theorem spinorC_contDiffOn {Ψ : E4 → SpinorFibre C} (hΨ : ContDiffOn ℝ ∞ Ψ (cylSlab T)) :
    ContDiffOn ℝ ∞ (spinorC Ψ) (cylSlab T) :=
  (spinorFlatL C).contDiff.comp_contDiffOn hΨ

theorem spinorC_periodic {Ψ : E4 → SpinorFibre C} (hΨ : ∀ n x, Ψ (x + spatialShift n) = Ψ x) :
    ∀ k x, spinorC Ψ (x + spatialShift k) = spinorC Ψ x := fun k x => by
  funext p; simp [spinorC, hΨ k x]

theorem h1Cauchy_spinor (Q : ChartBox T) {Ψ : ℕ → E4 → SpinorFibre C}
    (hsm : ∀ n, ContDiffOn ℝ ∞ (Ψ n) (cylSlab T))
    (h : H1Cauchy Q (fun n => spinorC (Ψ n)) (fun n x i => pd (spinorC (Ψ n)) i x)) :
    H1Cauchy Q (fun n => spinorC (Ψ n)) (fun n => spinorGrad (Ψ n)) := by
  have heq : ∀ n, ∀ x ∈ Q.set, (fun i => pd (spinorC (Ψ n)) i x) = spinorGrad (Ψ n) x := by
    intro n x hx
    have hd := differentiableAt_of_contDiffOn_slab (hsm n)
      (Q.closure_subset_cylSlab (subset_closure hx))
    funext i
    exact pd_clm_comp hd (spinorFlatL C) i
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := h ε hε
  refine ⟨N₀, fun m hm n hn => ?_⟩
  refine le_of_eq_of_le ?_ (hN₀ m hm n hn)
  unfold h1Norm
  congr 1
  refine eLpNorm_congr_ae ((ae_restrict_mem Q.isOpen.measurableSet).mono fun x hx => ?_)
  simp only [Pi.sub_apply, ← heq m x hx, ← heq n x hx]

/-- **Route (C4b) gives `H¹`-Cauchy spinors** (`prop:dirac-stability` applied to the
reconstructed Dirac and dual-Dirac systems): this is the hypothesis `hdirac` of
`certificate_packet` and `main_limit`, now a theorem. -/
theorem diracRoute_spinorH1Cauchy (Q : ChartBox T) {z : ℕ → SmoothFields T left}
    (h : DiracStabilityRoute Q z) : SpinorH1Cauchy Q z := by
  obtain ⟨t₀, t₁, h0, h01, h1, hQ0, hQ1, hΨ, hΨb⟩ := h
  exact ⟨h1Cauchy_spinor Q (fun n => (z n).smooth_Ψ)
      (h1Cauchy_chartBox h0 h01 h1 Q hQ0 hQ1 (fun n => spinorC_contDiffOn (z n).smooth_Ψ)
        (fun n => spinorC_periodic (z n).periodic_Ψ) hΨ),
    h1Cauchy_spinor Q (fun n => (z n).smooth_Ψb)
      (h1Cauchy_chartBox h0 h01 h1 Q hQ0 hQ1 (fun n => spinorC_contDiffOn (z n).smooth_Ψb)
        (fun n => spinorC_periodic (z n).periodic_Ψb) hΨb)⟩

/-- **`thm:certificate-packet` (closed)**: a sequence of smooth reconstructed fields satisfying
the classical compactness certificate (C1)–(C5) on every chart box — spinor route (C4a) or (C4b)
on each — and the coframe chart condition has, along every cutoff subsequence, a further
subsequence and a field tuple for which all convergences of `def:strong-packet` hold on every chart
box.  Route (C4b) is discharged by `prop:dirac-stability` (`diracRoute_spinorH1Cauchy`). -/
theorem certificate_packet_closed {Ysec : Type} [Fintype Ysec] (hT : 0 < T)
    {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec}
    (hcert : ∀ Q : ChartBox T, CompactnessCertificate Q z θ)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q z) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields C) (θ₀ : CoefficientBank Ysec),
      StrongPacket (fun k => z (ns (ψ k))) (fun k => θ (ns (ψ k))) L θ₀ :=
  certificate_packet hT hcert hch (fun Q h => diracRoute_spinorH1Cauchy Q h) ns hns

/-- **`thm:main-limit` (closed)**: the strong-packet refinement of variational closure, with the
compactness certificate as stated (route (C4a) or (C4b) on each chart box); route (C4b) is
discharged by `prop:dirac-stability` (`diracRoute_spinorH1Cauchy`). -/
theorem main_limit_closed {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec} (hT : 0 < T)
    (reg : RegulatorSequence T FC)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesCompactnessCertificate Q)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q reg.fields)
    (hcons : reg.FirstVariationConsistent) {W : ℕ → Type} [∀ n, NormedAddCommGroup (W n)]
    [∀ n, InnerProductSpace ℝ (W n)] {a : ∀ n, W n →L[ℝ] ℝ} {R Lc : ℕ → ℝ}
    {e : CylRegion T → ℕ → ℝ} {vh : ∀ n (K : CylRegion T), CrTest FC.left reg.r0 K → W n}
    (hsrc : SourceBounds reg W a R Lc e vh)
    (hvan : ∀ K, Tendsto (fun n => Lc n * Real.sqrt (R n) + e K n) atTop (𝓝 0))
    (hyuk : FC.YukawaContinuous) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec),
      θ₀ ∈ physicalBanks ∧
      StrongPacket (fun k => reg.fields (ns (ψ k))) (fun k => reg.bank (ns (ψ k))) L θ₀ ∧
      FirstVariationsConverge FC reg.r0 (fun k => reg.fields (ns (ψ k)))
        (fun k => reg.bank (ns (ψ k))) L θ₀ ∧
      IsDistributionalSolution (T := T) FC reg.r0 L θ₀ ∧
      SatisfiesEinsteinSM (T := T) FC reg.r0 L θ₀ :=
  main_limit hT reg hcert hch (fun Q h => diracRoute_spinorH1Cauchy Q h) hcons hsrc hvan hyuk
    ns hns

/-! ### Non-vacuity -/

/-- The hypotheses of `prop:dirac-stability` are satisfiable (zero sequence, `A⁰ = 1`), and so are
the generic hypotheses `StabHyp` they produce. -/
example (T : ℝ) (hT : 0 < T) : ∃ (A : ℕ → Fin 4 → E4 → Unit → Unit → ℂ)
    (B : ℕ → E4 → Unit → Unit → ℂ) (c : ℝ) (Cb : ℝ≥0),
    StabHyp (d := 3) (fun (_ : ℕ) (_ : E4) => (0 : Unit → ℂ)) A B 0 (T / 3) (2 * T / 3) T c Cb :=
  let ⟨A, B, c, Cb, hS, _⟩ := stabHyp_of_diracStabilityHyp (by positivity) (by linarith)
    (by linarith) (fun _ => contDiffOn_const) (fun _ _ _ => rfl) (diracStabilityHyp_zero _ _)
  ⟨A, B, c, Cb, hS⟩

/-- **Non-vacuity of route (C4b) through `prop:dirac-stability`**: the flat regulator. -/
example (T : ℝ) (Q : ChartBox T) : SpinorH1Cauchy Q (flatRegulator T).fields :=
  diracRoute_spinorH1Cauchy Q (flatRegulator_diracRoute T Q)

/-- **Non-vacuity of `main_limit_closed`**: the flat regulator satisfies every hypothesis. -/
example (hT : 0 < T) :=
  main_limit_closed hT (flatRegulator T) (fun Q => flatRegulator_compactnessCertificate T Q)
    (flatRegulator_coframeChart T) (flatRegulator_consistent hT) flatRegulator_sourceBounds
    (fun K => by simp) (trivialCarrier_yukawaContinuous Unit) id strictMono_id

/-- **Non-vacuity of `certificate_packet_closed`**: the flat regulator. -/
example (hT : 0 < T) :=
  certificate_packet_closed (Ysec := Unit) hT (fun Q => flatRegulator_compactnessCertificate T Q)
    (flatRegulator_coframeChart T) id strictMono_id

end DiracStab
end EinsteinSM
end RenewalGeometry
