/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeAllSectorGraphClosure

/-!
# Varying coefficient banks in the native all-sector limit
  (`thm:native-firstvariation-no-band`, hypothesis `(N5)`)

Einstein–SM action-closure manuscript, `thm:native-firstvariation-no-band`, `(N5)`: "the
coefficient banks converge in a compact physical parameter set".  The bank is
`θ = (κ, Λ, g_1, g_2, g_3, λ_H, v_H, Y)`; the gauge couplings enter through the invariant metric
`⟨·,·⟩_𝐠 = Σ_j g_j^{-2} ⟨·,·⟩_j` (`eq:SM-action`: "the positive invariant Lie-algebra metric in the
first term has the three coefficients `g_j^{-2}`").

* **Bounded continuum covectors** (`abs_contGrav_le`, `abs_firstVarCont_le`, `abs_contHiggs_le`,
  `abs_contDirac_le`, `abs_contAllVar_le`): at the limit fields of the sector theorems, the
  continuum Einstein–SM first variation is bounded on every `C²` test ball (it lies in
  `(V^r_K)^*`).
* **Banks** (`Bank`, `bankData`, `bankT`): a bank `θ = (κ, Λ, λ_H, v_H, w, Y)` with gauge weights
  `w_j = g_j^{-2}` acting on fixed invariant metrics `⟪T_j ·, T_j ·⟫`, a fixed representation
  packet `D₀` (`ρ_H, ρ_S, σ, γ`, Hermitian Higgs form); `bankT` realizes
  `Σ_j w_j ⟪T_j ·, T_j ·⟫ = ⟪T_θ ·, T_θ ·⟫` for nonnegative weights (`bank_hip`).
* **Affine structure** (`nativeDensity_bank`, `localAction_bank_affine`): the unchanged local
  action is an affine function of the coefficient vector
  `(κ⁻¹, Λκ⁻¹, w, λ_H, λ_H v_H², λ_H v_H⁴, Y)`; it is an explicit affine combination of the
  actions of finitely many fixed banks.
* **`native_all_sector_limit_bank`** (`eq:native-all-sector-limit` with varying banks): if
  `θ_h → θ` (`κ ≠ 0`, nonnegative gauge weights), then
  `|D S_{θ_h,h}^{loc}(z_h)[𝓘_h v] - D𝒮_θ(z)[v]| → 0` uniformly on every `C²` ball, and the Euler
  corollary holds with varying banks.
-/

open MeasureTheory Set Finset Filter Topology Metric NormedSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace RenewalGeometry.NativeBank

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 200000

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

local instance fact_one_le_two_bk : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

open TorusPiecewiseConstantTranslation (pc stronglyMeasurable_pc gridNorm)
open ShiftedJetAction (Grid unitVec fwdDiff)
open NativeScaling (Mat)
open NativeGravityFirstJet (M4 asM4 coframeM)
open NativeDensity
open NativeDiracLimit (DTest testRec)
open NativeDiracConv (CoHyp)
open NativeDiracConvergence (SpinHyp)

/-! ### Bounded continuum covectors -/

section Bounds

/-- A covector field in `L¹` applied to a uniformly bounded jet field. -/
theorem abs_integral_clm_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {G : 𝕋 → V →L[ℝ] ℝ} (hG : Integrable G MeasureTheory.volume) {J : 𝕋 → V} {c : ℝ}
    (hJ : ∀ z, ‖J z‖ ≤ c) : |∫ z, G z (J z)| ≤ (∫ z, ‖G z‖) * c := by
  rw [← Real.norm_eq_abs, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hG.norm.mul_const c) (Eventually.of_forall fun z => ?_)
  exact ((G z).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hJ z) (norm_nonneg _))

/-- A first-variation covector `∫ G[J] + ∫ Λ[J](u)` with `G ∈ L¹`, `Λ, u ∈ L²` is bounded by the
sup of the jet. -/
theorem abs_integral_GL_le {V U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup U] [NormedSpace ℝ U] {Gk : ℕ → 𝕋 → V →L[ℝ] ℝ} {G : 𝕋 → V →L[ℝ] ℝ}
    (hG : LpTendsto MeasureTheory.volume 1 Gk G) {Lk : ℕ → 𝕋 → V →L[ℝ] U →L[ℝ] ℝ}
    {L : 𝕋 → V →L[ℝ] U →L[ℝ] ℝ} (hL : LpTendsto MeasureTheory.volume 2 Lk L) {u : 𝕋 → U}
    (hu : MemLp u 2 MeasureTheory.volume) :
    ∃ C, ∀ (J : 𝕋 → V) (c : ℝ), (∀ z, ‖J z‖ ≤ c) →
      |∫ z, (G z (J z) + L z (J z) (u z))| ≤ C * c := by
  have hG1 := memLp_one_iff_integrable.1 hG.memLp_lim
  have hLu : Integrable (fun z => ‖L z‖ * ‖u z‖) MeasureTheory.volume := by
    have := hL.memLp_lim.norm.integrable_mul hu.norm
    exact this
  refine ⟨(∫ z, ‖G z‖) + ∫ z, ‖L z‖ * ‖u z‖, fun J c hJ => ?_⟩
  rw [← Real.norm_eq_abs, add_mul, ← integral_mul_const, ← integral_mul_const,
    ← integral_add (hG1.norm.mul_const _) (hLu.mul_const _)]
  refine norm_integral_le_of_norm_le ((hG1.norm.mul_const _).add (hLu.mul_const _))
    (Eventually.of_forall fun z => ?_)
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact ((G z).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hJ z) (norm_nonneg _))
  · calc ‖L z (J z) (u z)‖ ≤ ‖L z (J z)‖ * ‖u z‖ := (L z _).le_opNorm _
      _ ≤ ‖L z‖ * ‖J z‖ * ‖u z‖ :=
          mul_le_mul_of_nonneg_right ((L z).le_opNorm _) (norm_nonneg _)
      _ ≤ ‖L z‖ * c * ‖u z‖ := by gcongr; exact hJ z
      _ = ‖L z‖ * ‖u z‖ * c := by ring

/-- Sum of `4⁴` terms bounded by `c`. -/
theorem abs_sum4_le {f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ} {c : ℝ}
    (h : ∀ a b c' d, |f a b c' d| ≤ c) :
    |∑ a, ∑ b, ∑ c', ∑ d, f a b c' d| ≤ 256 * c := by
  have h1 : ∀ a b c', |∑ d, f a b c' d| ≤ 4 * c := fun a b c' =>
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun d _ => h a b c' d).trans
      (by simp))
  have h2 : ∀ a b, |∑ c', ∑ d, f a b c' d| ≤ 16 * c := fun a b =>
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun c' _ => h1 a b c').trans
      (by simp; ring_nf; rfl))
  have h3 : ∀ a, |∑ b, ∑ c', ∑ d, f a b c' d| ≤ 64 * c := fun a =>
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun b _ => h2 a b).trans
      (by simp; ring_nf; rfl))
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun a _ => h3 a).trans
    (by simp; ring_nf; rfl))

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}

/-- **The continuum Palatini covector is bounded on `C²` tests.** -/
theorem abs_contGrav_le (H : CoHyp n y) (hpos : ∀ M ∈ H.Ke, 0 < Matrix.det (show Mat from M))
    (κ Λ : ℝ) : ∃ C, ∀ k : TorusC2Tests.C2Test M4,
      |NativeGravityFirstJet.contGravVariation κ Λ H.e₀ H.p k| ≤ C * k.norm := by
  have hL := NativeGravityFirstJet.lpTendsto_limitCov κ Λ (Ke := (H.Ke : Set Mat)) H.hKe hpos
    (f := fun k => pc (coframeM (y k))) (fun k y' => H.hval k _) H.he
    (g := fun k μ => pc (NativeDiracConv.qM (y k) μ)) H.hp
  refine ⟨∫ y', ‖NativeGravityFirstJet.limitCov κ Λ (H.e₀ y') (fun μ => H.p μ y')‖, fun τk => ?_⟩
  have hc0 : NativeGravityFirstJet.contGravVariation κ Λ H.e₀ H.p τk =
      ∫ y', NativeGravityFirstJet.limitCov κ Λ (H.e₀ y') (fun μ => H.p μ y')
        (NativeGravityFirstJet.limitJet (τk.f y') (fun lam => τk.df lam y')) := by
    refine integral_congr_ae ?_
    filter_upwards [H.e₀_mem] with y' hy'
    exact (NativeGravityFirstJet.limitCov_apply κ Λ (hpos _ hy').ne' (fun μ => H.p μ y')
      (τk.f y') (fun lam => τk.df lam y')).symm
  rw [hc0]
  exact abs_integral_clm_le (memLp_one_iff_integrable.1 hL.memLp_lim)
    (NativeGravityFirstJet.norm_limitJet_le τk)

/-- **The continuum Higgs covector is bounded on `C²` tests.** -/
theorem abs_contHiggs_le (D : Data 𝔄 𝓗 𝓢) (H : CoHyp n y) (P : NativeHiggsVar.HiggsHyp D y) :
    ∃ C, ∀ τ : DTest 𝔄 𝓗 𝓢 W', |NativeHiggsVar.contHiggsVar D H P τ| ≤ C * τ.norm :=
  ⟨_, fun τ => abs_integral_clm_le
    (memLp_one_iff_integrable.1 (P.lpTendsto_hcov H).memLp_lim)
    (NativeHiggsVar.norm_contHJet_le τ)⟩

/-- **The continuum Dirac–Yukawa covector is bounded on `C²` tests.** -/
theorem abs_contDirac_le (D : Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢) (H : CoHyp n y)
    (S : SpinHyp κ y) {u₀ : 𝕋 → NativeDiracLimit.Dif 𝓢 W'} (hu₀ : MemLp u₀ 2 MeasureTheory.volume) :
    ∃ C, ∀ τ : DTest 𝔄 𝓗 𝓢 W',
      |NativeSpinorVariation.contDiracVar D κ H S u₀ τ| ≤ C * τ.norm := by
  obtain ⟨C, hC⟩ := abs_integral_GL_le (S.lpTendsto_Gop (D := D) H)
    (S.lpTendsto_Λop (D := D) H) hu₀
  exact ⟨C, fun τ => hC _ _ (NativeSpinorVariation.norm_contJet_le τ)⟩

end Bounds

section YMBound

open NativeYMMetric (Cof Coef4 GLc ymCoef dCoef varDens FextC DaT firstVarCont MetricBound
  GaugeBound)

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem abs_coef4_le (θ : Coef4) (μ ν ρ σ : Fin 4) : |θ μ ν ρ σ| ≤ ‖θ‖ := by
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm (θ μ ν ρ) σ).trans ((norm_le_pi_norm (θ μ ν) ρ).trans
    ((norm_le_pi_norm (θ μ) ν).trans (norm_le_pi_norm θ μ)))

theorem abs_inner_T_le (T : 𝔸 →L[ℝ] E) (X Y : 𝔸) : |⟪T X, T Y⟫| ≤ ‖T‖ ^ 2 * (‖X‖ * ‖Y‖) := by
  refine (abs_real_inner_le_norm _ _).trans ?_
  calc ‖T X‖ * ‖T Y‖ ≤ (‖T‖ * ‖X‖) * (‖T‖ * ‖Y‖) :=
        mul_le_mul (T.le_opNorm X) (T.le_opNorm Y) (norm_nonneg _) (by positivity)
    _ = ‖T‖ ^ 2 * (‖X‖ * ‖Y‖) := by ring

theorem norm_FextC_le (F : Fin 4 → Fin 4 → 𝕋 → 𝔸) (y : 𝕋) (μ ν : Fin 4) :
    ‖FextC F y μ ν‖ ≤ ∑ α, ∑ β, ‖F α β y‖ := by
  have h : ∀ α β, ‖F α β y‖ ≤ ∑ α, ∑ β, ‖F α β y‖ := fun α β =>
    (Finset.single_le_sum (f := fun β => ‖F α β y‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ β)).trans (Finset.single_le_sum (f := fun α => ∑ β, ‖F α β y‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ α))
  unfold FextC
  split_ifs
  · exact h μ ν
  · rw [norm_neg]; exact h ν μ
  · rw [norm_zero]; exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_DaT_le {M : NNReal} (A₀ : Fin 4 → 𝕋 → 𝔸) (a : NativeYMVariation.C1Test 𝔸)
    (ha : GaugeBound M a) (y : 𝕋) (μ ν : Fin 4) :
    ‖DaT A₀ a y μ ν‖ ≤ 2 * M * (1 + 2 * ∑ α, ‖A₀ α y‖) := by
  have hA : ∀ α, ‖A₀ α y‖ ≤ ∑ α, ‖A₀ α y‖ := fun α =>
    Finset.single_le_sum (f := fun α => ‖A₀ α y‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ α)
  have hM : (0 : ℝ) ≤ M := M.2
  have h1 := ha.da_le μ ν y
  have h2 := ha.da_le ν μ y
  have h3 := ha.a_le ν y
  have h4 := ha.a_le μ y
  have hp : ∀ X Y : 𝔸, ‖X * Y‖ ≤ ‖X‖ * ‖Y‖ := fun X Y => norm_mul_le X Y
  unfold DaT
  calc ‖(a.da μ ν y - a.da ν μ y) + ((A₀ μ y * a.a ν y - a.a ν y * A₀ μ y) +
        (a.a μ y * A₀ ν y - A₀ ν y * a.a μ y))‖
      ≤ (‖a.da μ ν y‖ + ‖a.da ν μ y‖) + ((‖A₀ μ y‖ * ‖a.a ν y‖ + ‖a.a ν y‖ * ‖A₀ μ y‖) +
        (‖a.a μ y‖ * ‖A₀ ν y‖ + ‖A₀ ν y‖ * ‖a.a μ y‖)) := by
        refine (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · exact (norm_sub_le _ _).trans (add_le_add (hp _ _) (hp _ _))
        · exact (norm_sub_le _ _).trans (add_le_add (hp _ _) (hp _ _))
    _ ≤ (M + M) + ((‖A₀ μ y‖ * M + M * ‖A₀ μ y‖) + (M * ‖A₀ ν y‖ + ‖A₀ ν y‖ * M)) := by
        gcongr
    _ ≤ 2 * M * (1 + 2 * ∑ α, ‖A₀ α y‖) := by
        nlinarith [hA μ, hA ν, mul_le_mul_of_nonneg_left (hA μ) hM,
          mul_le_mul_of_nonneg_left (hA ν) hM]

/-- **The continuum Yang–Mills covector is bounded on `C^{0,1}`-bounded tests**: for coframes in a
compact nondegenerate chart, `A ∈ L²` and `F ∈ L²`, `|D𝒮_YM[k, a]| ≤ C` for all metric and gauge
tests bounded by `M`. -/
theorem abs_firstVarCont_le (T : 𝔸 →L[ℝ] E) {Ke : Set Cof} (hKe : IsCompact Ke)
    (hKGL : Ke ⊆ GLc) {e₀ : 𝕋 → Cof} (he₀ : ∀ᵐ z, e₀ z ∈ Ke) {A₀ : Fin 4 → 𝕋 → 𝔸}
    (hA : ∀ μ, MemLp (A₀ μ) 2 MeasureTheory.volume) {F : Fin 4 → Fin 4 → 𝕋 → 𝔸}
    (hF : ∀ μ ν, MemLp (F μ ν) 2 MeasureTheory.volume) (M : NNReal) :
    ∃ C, ∀ (k : C(𝕋, Cof)) (a : NativeYMVariation.C1Test 𝔸), MetricBound M k → GaugeBound M a →
      |firstVarCont T e₀ A₀ F k a| ≤ C := by
  obtain ⟨Cθ, hCθ⟩ : ∃ C, ∀ e ∈ Ke, ‖ymCoef e‖ ≤ C :=
    hKe.exists_bound_of_continuousOn
      ((NativeYMMetric.contDiffOn_ymCoef (n := 0)).continuousOn.mono hKGL)
  obtain ⟨Cd, hCd⟩ : ∃ C, ∀ p ∈ Ke ×ˢ Metric.closedBall (0 : Cof) M, ‖dCoef p.1 p.2‖ ≤ C :=
    (hKe.prod (isCompact_closedBall 0 M)).exists_bound_of_continuousOn
      (NativeYMMetric.continuousOn_dCoef.mono (Set.prod_mono hKGL (Set.subset_univ _)))
  set SF : 𝕋 → ℝ := fun y => ∑ μ, ∑ ν, ‖F μ ν y‖ with hSFdef
  set SA : 𝕋 → ℝ := fun y => ∑ μ, ‖A₀ μ y‖ with hSAdef
  have hSF : MemLp SF 2 MeasureTheory.volume :=
    memLp_finsetSum _ fun μ _ => memLp_finsetSum _ fun ν _ => (hF μ ν).norm
  have hSA : MemLp SA 2 MeasureTheory.volume := memLp_finsetSum _ fun μ _ => (hA μ).norm
  have hSF0 : ∀ y, 0 ≤ SF y := fun y => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hSA0 : ∀ y, 0 ≤ SA y := fun y => Finset.sum_nonneg fun _ _ => norm_nonneg _
  set K1 : ℝ := Cd * ‖T‖ ^ 2
  set K2 : ℝ := 2 * Cθ * ‖T‖ ^ 2 * (2 * M)
  set g : 𝕋 → ℝ := fun y => 64 * (K1 * (SF y * SF y) + K2 * (SF y * (1 + 2 * SA y)))
  have hg : Integrable g MeasureTheory.volume := by
    have i1 : Integrable (fun y => SF y * SF y) MeasureTheory.volume := hSF.integrable_mul hSF
    have i2 : Integrable (fun y => SF y * SA y) MeasureTheory.volume := hSF.integrable_mul hSA
    have i3 : Integrable SF MeasureTheory.volume := hSF.integrable (by norm_num)
    refine (((i1.const_mul K1).add ((i3.add (i2.const_mul 2)).const_mul K2)).const_mul 64).congr
      (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply]
    ring
  refine ⟨∫ y, g y, fun k a hk ha => ?_⟩
  rw [firstVarCont, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hg ?_
  filter_upwards [he₀] with y hy
  have hθ : ‖ymCoef (e₀ y)‖ ≤ Cθ := hCθ _ hy
  have hθ' : ‖dCoef (e₀ y) (k y)‖ ≤ Cd :=
    hCd ⟨e₀ y, k y⟩ ⟨hy, by rw [Metric.mem_closedBall, dist_zero_right]; exact hk.k_le y⟩
  have hCθ0 : 0 ≤ Cθ := (norm_nonneg _).trans hθ
  have hCd0 : 0 ≤ Cd := (norm_nonneg _).trans hθ'
  have hFx : ∀ μ ν, ‖FextC F y μ ν‖ ≤ SF y := fun μ ν => norm_FextC_le F y μ ν
  have hDx : ∀ μ ν, ‖DaT A₀ a y μ ν‖ ≤ 2 * M * (1 + 2 * SA y) := fun μ ν => norm_DaT_le A₀ a ha y μ ν
  have hB0 : 0 ≤ 2 * (M : ℝ) * (1 + 2 * SA y) := by have := hSA0 y; positivity
  have hterm : ∀ μ ν ρ σ,
      |dCoef (e₀ y) (k y) μ ν ρ σ * ⟪T (FextC F y μ ν), T (FextC F y ρ σ)⟫ +
        ymCoef (e₀ y) μ ν ρ σ * (⟪T (FextC F y μ ν), T (DaT A₀ a y ρ σ)⟫ +
          ⟪T (DaT A₀ a y μ ν), T (FextC F y ρ σ)⟫)| ≤
        K1 * (SF y * SF y) + K2 * (SF y * (1 + 2 * SA y)) := by
    intro μ ν ρ σ
    have e1 := abs_coef4_le (dCoef (e₀ y) (k y)) μ ν ρ σ
    have e2 := abs_coef4_le (ymCoef (e₀ y)) μ ν ρ σ
    have i1 := abs_inner_T_le T (FextC F y μ ν) (FextC F y ρ σ)
    have i2 := abs_inner_T_le T (FextC F y μ ν) (DaT A₀ a y ρ σ)
    have i3 := abs_inner_T_le T (DaT A₀ a y μ ν) (FextC F y ρ σ)
    have p1 : ‖FextC F y μ ν‖ * ‖FextC F y ρ σ‖ ≤ SF y * SF y :=
      mul_le_mul (hFx μ ν) (hFx ρ σ) (norm_nonneg _) (hSF0 y)
    have p2 : ‖FextC F y μ ν‖ * ‖DaT A₀ a y ρ σ‖ ≤ SF y * (2 * M * (1 + 2 * SA y)) :=
      mul_le_mul (hFx μ ν) (hDx ρ σ) (norm_nonneg _) (hSF0 y)
    have p3 : ‖DaT A₀ a y μ ν‖ * ‖FextC F y ρ σ‖ ≤ (2 * M * (1 + 2 * SA y)) * SF y :=
      mul_le_mul (hDx μ ν) (hFx ρ σ) (norm_nonneg _) hB0
    have hT2 : 0 ≤ ‖T‖ ^ 2 := by positivity
    calc _ ≤ |dCoef (e₀ y) (k y) μ ν ρ σ| * |⟪T (FextC F y μ ν), T (FextC F y ρ σ)⟫| +
          |ymCoef (e₀ y) μ ν ρ σ| * (|⟪T (FextC F y μ ν), T (DaT A₀ a y ρ σ)⟫| +
            |⟪T (DaT A₀ a y μ ν), T (FextC F y ρ σ)⟫|) := by
          refine (abs_add_le _ _).trans (add_le_add (le_of_eq (abs_mul _ _)) ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
      _ ≤ Cd * (‖T‖ ^ 2 * (SF y * SF y)) + Cθ * (‖T‖ ^ 2 * (SF y * (2 * M * (1 + 2 * SA y))) +
          ‖T‖ ^ 2 * ((2 * M * (1 + 2 * SA y)) * SF y)) := by
          gcongr
          · exact e1.trans hθ'
          · exact i1.trans (mul_le_mul_of_nonneg_left p1 hT2)
          · exact e2.trans hθ
          · exact i2.trans (mul_le_mul_of_nonneg_left p2 hT2)
          · exact i3.trans (mul_le_mul_of_nonneg_left p3 hT2)
      _ = K1 * (SF y * SF y) + K2 * (SF y * (1 + 2 * SA y)) := by ring
  have hsum := abs_sum4_le hterm
  rw [NativeYMMetric.varDens, Real.norm_eq_abs, abs_mul]
  calc |-(1 / 4 : ℝ)| * |∑ μ, ∑ ν, ∑ ρ, ∑ σ, _| ≤ (1 / 4) * (256 *
        (K1 * (SF y * SF y) + K2 * (SF y * (1 + 2 * SA y)))) := by
        rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = g y := by simp only [g]; ring

end YMBound

section AllBound

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}

/-- **The continuum Einstein–SM first variation `D𝒮_θ(z)` is bounded on every `C²` test ball**
(it lies in `(V^r_K)^*`), at the limit fields of the sector theorems. -/
theorem abs_contAllVar_le (D : Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢) (T : 𝔄 →L[ℝ] E)
    (H : CoHyp n y) (hpos : ∀ M ∈ H.Ke, 0 < Matrix.det (show Mat from M))
    {F : Fin 4 → Fin 4 → 𝕋 → 𝔄} (hF : ∀ μ ν, MemLp (F μ ν) 2 MeasureTheory.volume)
    (P : NativeHiggsVar.HiggsHyp D y) (S : SpinHyp κ y) {u₀ : 𝕋 → NativeDiracLimit.Dif 𝓢 W'}
    (hu₀ : MemLp u₀ 2 MeasureTheory.volume) (M : NNReal) :
    ∃ C, ∀ τ : DTest 𝔄 𝓗 𝓢 W', τ.norm ≤ M →
      |NativeAllSector.contAllVar D κ T H F P S u₀ τ| ≤ C := by
  obtain ⟨Cg, hCg⟩ := abs_contGrav_le H hpos D.κ D.Λ
  obtain ⟨Cy, hCy⟩ := abs_firstVarCont_le T (Ke := H.Ke) H.hKe (fun M hM => H.hKdet M hM)
    H.e₀_mem (A₀ := H.A₀) (fun μ => (H.hA μ).memLp_lim.mono_exponent (by norm_num)) hF M
  obtain ⟨Ch, hCh⟩ := abs_contHiggs_le (W' := W') D H P
  obtain ⟨Cd, hCd⟩ := abs_contDirac_le D κ H S hu₀
  refine ⟨(|Cg| + |Ch| + |Cd|) * M + Cy, fun τ hτ => ?_⟩
  have hM0 : (0 : ℝ) ≤ M := M.2
  have hk : τ.k.norm ≤ M := τ.k_le.trans hτ
  have h1 := hCg τ.k
  have h2 := hCy τ.k.f (NativeYMBridge.toC1 τ.a) (NativeYMBridge.metricBound_of_C2 τ.k hk)
    (NativeYMBridge.gaugeBound_toC1 τ.a (τ.a_le.trans hτ))
  have h3 := hCh τ
  have h4 := hCd τ
  have hk0 := τ.k.norm_nonneg
  have hτ0 := τ.norm_nonneg
  have b1 : Cg * τ.k.norm ≤ |Cg| * M :=
    (le_abs_self _ |>.trans (by rw [abs_mul, abs_of_nonneg hk0])).trans
      (mul_le_mul_of_nonneg_left hk (abs_nonneg _))
  have b3 : Ch * τ.norm ≤ |Ch| * M :=
    (le_abs_self _ |>.trans (by rw [abs_mul, abs_of_nonneg hτ0])).trans
      (mul_le_mul_of_nonneg_left hτ (abs_nonneg _))
  have b4 : Cd * τ.norm ≤ |Cd| * M :=
    (le_abs_self _ |>.trans (by rw [abs_mul, abs_of_nonneg hτ0])).trans
      (mul_le_mul_of_nonneg_left hτ (abs_nonneg _))
  unfold NativeAllSector.contAllVar
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl).trans ?_
  linarith

end AllBound

/-! ### Coefficient banks and the affine structure of the local action -/

section Banks

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {J : ℕ}

/-- **A coefficient bank** `θ = (κ, Λ, λ_H, v_H, w, Y)`: gravitational coupling, cosmological
constant, Higgs self-coupling and vacuum value, gauge weights `w_j = g_j^{-2}` and the Yukawa
map. -/
structure Bank (J : ℕ) (𝓗 𝓢 : Type*) [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗]
    [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] where
  κ : ℝ
  Λ : ℝ
  lamH : ℝ
  vH : ℝ
  w : Fin J → ℝ
  Y : 𝓗 →L[ℝ] Spin 𝓢

/-- The invariant metric `Σ_j w_j ⟪T_j ·, T_j ·⟫` of the gauge algebra. -/
def bankForm (Tj : Fin J → 𝔄 →L[ℝ] E) (w : Fin J → ℝ) : 𝔄 →L[ℝ] 𝔄 →L[ℝ] ℝ :=
  ∑ j, w j • (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (Tj j) (Tj j)

theorem bankForm_apply (Tj : Fin J → 𝔄 →L[ℝ] E) (w : Fin J → ℝ) (X Y : 𝔄) :
    bankForm Tj w X Y = ∑ j, w j * ⟪Tj j X, Tj j Y⟫ := by
  simp [bankForm, ContinuousLinearMap.sum_apply, ContinuousLinearMap.bilinearComp_apply]

/-- The native data of a bank over a fixed representation packet `D₀`
(`ρ_H, ρ_S, σ, γ` and the Hermitian Higgs form). -/
def bankData (D₀ : Data 𝔄 𝓗 𝓢) (Tj : Fin J → 𝔄 →L[ℝ] E) (θ : Bank J 𝓗 𝓢) : Data 𝔄 𝓗 𝓢 :=
  { D₀ with
    κ := θ.κ
    Λ := θ.Λ
    lamH := θ.lamH
    vH := θ.vH
    ipA := bankForm Tj θ.w
    yukawa := θ.Y }

/-- The map `T_θ = (√w_j T_j)_j` realizing the bank metric as a Hilbert pull-back. -/
def bankT (Tj : Fin J → 𝔄 →L[ℝ] E) (w : Fin J → ℝ) : 𝔄 →L[ℝ] PiLp 2 (fun _ : Fin J => E) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin J => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => Real.sqrt (w j) • Tj j)

/-- For nonnegative weights the bank metric is `⟪T_θ ·, T_θ ·⟫`. -/
theorem bank_hip (D₀ : Data 𝔄 𝓗 𝓢) (Tj : Fin J → 𝔄 →L[ℝ] E) (θ : Bank J 𝓗 𝓢)
    (hw : ∀ j, 0 ≤ θ.w j) (X Y : 𝔄) :
    (bankData D₀ Tj θ).ipA X Y = ⟪bankT Tj θ.w X, bankT Tj θ.w Y⟫ := by
  change bankForm Tj θ.w X Y = _
  rw [bankForm_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [bankT, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.coe_symm_continuousLinearEquiv, PiLp.toLp_apply,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.smul_apply, real_inner_smul_left,
    real_inner_smul_right]
  rw [← mul_assoc, Real.mul_self_sqrt (hw j)]

variable (D₀ : Data 𝔄 𝓗 𝓢) (Tj : Fin J → 𝔄 →L[ℝ] E)
variable {N : ℕ} [NeZero N]

/-- The Yang–Mills density of a bilinear form. -/
def ymForm (B : 𝔄 →L[ℝ] 𝔄 →L[ℝ] ℝ) (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) : ℝ :=
  -(4⁻¹ * volume (coframe y x) * ∑ μ, ∑ ν, ∑ ρ, ∑ σ,
    ginv (coframe y x) μ ρ * ginv (coframe y x) ν σ *
      B (antisym (NativeScaling.fieldStrength h (gauge y) x) μ ν)
        (antisym (NativeScaling.fieldStrength h (gauge y) x) ρ σ))

theorem ymForm_add (B B' : 𝔄 →L[ℝ] 𝔄 →L[ℝ] ℝ) (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) :
    ymForm (B + B') h y x = ymForm B h y x + ymForm B' h y x := by
  simp only [ymForm, ContinuousLinearMap.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem ymForm_smul (c : ℝ) (B : 𝔄 →L[ℝ] 𝔄 →L[ℝ] ℝ) (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢)
    (x : Grid N) : ymForm (c • B) h y x = c * ymForm B h y x := by
  simp only [ymForm, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_left_comm _ c,
    ← Finset.mul_sum]
  ring

theorem ymForm_zero (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) :
    ymForm (0 : 𝔄 →L[ℝ] 𝔄 →L[ℝ] ℝ) h y x = 0 := by
  simp [ymForm]

theorem ymForm_sum (B : Fin J → 𝔄 →L[ℝ] 𝔄 →L[ℝ] ℝ) (w : Fin J → ℝ) (h : ℝ)
    (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) :
    ymForm (∑ j, w j • B j) h y x = ∑ j, w j * ymForm (B j) h y x := by
  classical
  induction (Finset.univ : Finset (Fin J)) using Finset.induction_on with
  | empty => simp [ymForm_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, ymForm_add, ymForm_smul, ih]

/-- The gravitational density at unit coupling, `Σ pal(1) R`. -/
def gravP (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) : ℝ :=
  ∑ μ, ∑ ν, ∑ a, ∑ b, pal 1 (coframe y x) μ ν a b *
    opEntry (antisym (cartanCurvature h (coframe y) x) μ ν) a b

/-- The Higgs kinetic density (bank independent). -/
def higgsKin (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) : ℝ :=
  -(volume (coframe y x) * ∑ μ, ∑ ν, ginv (coframe y x) μ ν *
      D₀.hermH (higgsLink D₀ h y x μ) (higgsLink D₀ h y x ν))

/-- The Dirac kinetic density (bank independent). -/
def diracKin (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) : ℝ :=
  volume (coframe y x) *
    (Complex.I / 2 * ∑ μ, (psiBar y x (gammaMu D₀ μ (coframe y x) (diracDiff D₀ h y x μ)) -
        diracDiffBar D₀ h y x μ (gammaMu D₀ μ (coframe y x) (psi y x)))).re

/-- The Yukawa density of a Yukawa map. -/
def yukD (Y : 𝓗 →L[ℝ] Spin 𝓢) (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) : ℝ :=
  volume (coframe y x) * (psiBar y x (Y (higgs y x) (psi y x))).re

theorem yukD_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Y : ι → 𝓗 →L[ℝ] Spin 𝓢)
    (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) :
    yukD (∑ i ∈ s, c i • Y i) y x = ∑ i ∈ s, c i * yukD (Y i) y x := by
  simp only [yukD, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum,
    map_smul, Complex.re_sum, Complex.smul_re, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The affine normal form of the native density in the bank.** -/
theorem nativeDensity_bank (θ : Bank J 𝓗 𝓢) (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) :
    nativeDensity (bankData D₀ Tj θ) h y x =
      (θ.κ⁻¹ * gravP h y x - θ.Λ * θ.κ⁻¹ * volume (coframe y x)) +
      ∑ j, θ.w j * ymForm ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (Tj j) (Tj j)) h y x +
      (higgsKin D₀ h y x - volume (coframe y x) *
        (θ.lamH * (D₀.hermH (higgs y x) (higgs y x) - θ.vH ^ 2) ^ 2)) +
      (diracKin D₀ h y x - yukD θ.Y y x) := by
  have hg : gravityDensity (bankData D₀ Tj θ) h y x =
      θ.κ⁻¹ * gravP h y x - θ.Λ * θ.κ⁻¹ * volume (coframe y x) := by
    have hpal : ∀ e μ ν a b, pal θ.κ e μ ν a b = θ.κ⁻¹ * pal 1 e μ ν a b := by
      intro e μ ν a b; simp only [pal]; ring
    show (∑ μ, ∑ ν, ∑ a, ∑ b, pal θ.κ (coframe y x) μ ν a b *
        opEntry (antisym (cartanCurvature h (coframe y) x) μ ν) a b) -
      θ.Λ / θ.κ * volume (coframe y x) = _
    simp only [gravP, hpal, Finset.mul_sum, mul_assoc, div_eq_mul_inv]
  have hy : ymDensity (bankData D₀ Tj θ) h y x =
      ∑ j, θ.w j * ymForm ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (Tj j) (Tj j)) h y x :=
    ymForm_sum _ θ.w h y x
  have hh : higgsDensity (bankData D₀ Tj θ) h y x = higgsKin D₀ h y x - volume (coframe y x) *
      (θ.lamH * (D₀.hermH (higgs y x) (higgs y x) - θ.vH ^ 2) ^ 2) := rfl
  have hd : diracDensity (bankData D₀ Tj θ) h y x = diracKin D₀ h y x - yukD θ.Y y x := by
    unfold diracDensity diracKin yukD
    rw [Complex.sub_re, mul_sub]
    rfl
  rw [nativeDensity, hg, hy, hh, hd]

end Banks

/-! ### The unit banks and the affine decomposition -/

section Affine

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {J : ℕ}

/-- The dimension of the space of Yukawa maps. -/
abbrev dY (𝓗 𝓢 : Type*) [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [FiniteDimensional ℝ 𝓗]
    [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [FiniteDimensional ℝ 𝓢] : ℕ :=
  Module.finrank ℝ (𝓗 →L[ℝ] Spin 𝓢)

/-- A basis of the Yukawa maps. -/
abbrev yBasis (𝓗 𝓢 : Type*) [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [FiniteDimensional ℝ 𝓗]
    [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [FiniteDimensional ℝ 𝓢] :
    Module.Basis (Fin (dY 𝓗 𝓢)) ℝ (𝓗 →L[ℝ] Spin 𝓢) :=
  Module.finBasis ℝ (𝓗 →L[ℝ] Spin 𝓢)

/-- The zero bank. -/
def bank0 : Bank J 𝓗 𝓢 := ⟨0, 0, 0, 0, 0, 0⟩

/-- The index set of the unit directions of the bank: `(κ⁻¹, Λκ⁻¹, λ_H, λ_H v², λ_H v⁴)`, the gauge
weights and the Yukawa coordinates. -/
abbrev Unit5 (J d : ℕ) := Fin 5 ⊕ Fin J ⊕ Fin d

/-- The "positive" bank of a unit direction. -/
def posBank : Unit5 J (dY 𝓗 𝓢) → Bank J 𝓗 𝓢
  | .inl 0 => { (bank0 : Bank J 𝓗 𝓢) with κ := 1 }
  | .inl 1 => { (bank0 : Bank J 𝓗 𝓢) with κ := 1, Λ := 1 }
  | .inl 2 => { (bank0 : Bank J 𝓗 𝓢) with lamH := 1 }
  | .inl 3 => { (bank0 : Bank J 𝓗 𝓢) with lamH := 1, vH := 1 }
  | .inl 4 => { (bank0 : Bank J 𝓗 𝓢) with lamH := 1, vH := Real.sqrt 2 }
  | .inr (.inl j) => { (bank0 : Bank J 𝓗 𝓢) with w := Pi.single j 1 }
  | .inr (.inr i) => { (bank0 : Bank J 𝓗 𝓢) with Y := yBasis 𝓗 𝓢 i }

/-- The "negative" bank of a unit direction. -/
def negBank : Unit5 J (dY 𝓗 𝓢) → Bank J 𝓗 𝓢
  | .inl 1 => { (bank0 : Bank J 𝓗 𝓢) with κ := 1 }
  | .inl 3 => { (bank0 : Bank J 𝓗 𝓢) with lamH := 1 }
  | .inl 4 => { (bank0 : Bank J 𝓗 𝓢) with lamH := 1 }
  | _ => bank0

/-- The affine coordinates of a bank. -/
def coef (θ : Bank J 𝓗 𝓢) : Unit5 J (dY 𝓗 𝓢) → ℝ
  | .inl 0 => θ.κ⁻¹
  | .inl 1 => θ.Λ * θ.κ⁻¹
  | .inl 2 => θ.lamH
  | .inl 3 => 2 * θ.lamH * θ.vH ^ 2 - θ.lamH * θ.vH ^ 4
  | .inl 4 => (θ.lamH * θ.vH ^ 4 - θ.lamH * θ.vH ^ 2) / 2
  | .inr (.inl j) => θ.w j
  | .inr (.inr i) => (yBasis 𝓗 𝓢).repr θ.Y i

theorem posBank_w_nonneg (u : Unit5 J (dY 𝓗 𝓢)) (j : Fin J) : 0 ≤ (posBank u).w j := by
  rcases u with u | j' | i
  · fin_cases u <;> simp [posBank, bank0]
  · simp only [posBank]
    by_cases h : j = j'
    · subst h; simp
    · simp [Pi.single_apply, h]
  · simp [posBank, bank0]

theorem negBank_w_nonneg (u : Unit5 J (dY 𝓗 𝓢)) (j : Fin J) : 0 ≤ (negBank u).w j := by
  rcases u with u | j' | i
  · fin_cases u <;> simp [negBank, bank0]
  · simp [negBank, bank0]
  · simp [negBank, bank0]

theorem bank0_w_nonneg (j : Fin J) : 0 ≤ (bank0 : Bank J 𝓗 𝓢).w j := by simp [bank0]

variable (D₀ : Data 𝔄 𝓗 𝓢) (Tj : Fin J → 𝔄 →L[ℝ] E)
variable {N : ℕ} [NeZero N]

theorem yukD_zero (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) :
    yukD (0 : 𝓗 →L[ℝ] Spin 𝓢) y x = 0 := by simp [yukD]

/-- The native density of a bank, split off the zero bank. -/
theorem nativeDensity_split (θ : Bank J 𝓗 𝓢) (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢)
    (x : Grid N) :
    nativeDensity (bankData D₀ Tj θ) h y x = nativeDensity (bankData D₀ Tj bank0) h y x +
      ((θ.κ⁻¹ * gravP h y x - θ.Λ * θ.κ⁻¹ * volume (coframe y x)) +
      ∑ j, θ.w j * ymForm ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (Tj j) (Tj j)) h y x -
      volume (coframe y x) * (θ.lamH * (D₀.hermH (higgs y x) (higgs y x) - θ.vH ^ 2) ^ 2) -
      yukD θ.Y y x) := by
  rw [nativeDensity_bank, nativeDensity_bank]
  simp only [bank0, inv_zero, mul_zero, zero_mul, sub_zero, Pi.zero_apply, Finset.sum_const_zero,
    yukD_zero, add_zero]
  ring

/-- The unit densities. -/
def unitVal (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) : Unit5 J (dY 𝓗 𝓢) → ℝ
  | .inl 0 => gravP h y x
  | .inl 1 => -volume (coframe y x)
  | .inl 2 => -(volume (coframe y x) * D₀.hermH (higgs y x) (higgs y x) ^ 2)
  | .inl 3 => -(volume (coframe y x) * ((D₀.hermH (higgs y x) (higgs y x) - 1) ^ 2 -
      D₀.hermH (higgs y x) (higgs y x) ^ 2))
  | .inl 4 => -(volume (coframe y x) * ((D₀.hermH (higgs y x) (higgs y x) - 2) ^ 2 -
      D₀.hermH (higgs y x) (higgs y x) ^ 2))
  | .inr (.inl j) => ymForm ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (Tj j) (Tj j)) h y x
  | .inr (.inr i) => -yukD (yBasis 𝓗 𝓢 i) y x

theorem sum_single_mul (j : Fin J) (f : Fin J → ℝ) :
    ∑ j', (Pi.single j (1 : ℝ) : Fin J → ℝ) j' * f j' = f j := by
  rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [Pi.single_apply, hj'])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

/-- Each unit direction isolates its unit density. -/
theorem nativeDensity_unit (u : Unit5 J (dY 𝓗 𝓢)) (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢)
    (x : Grid N) :
    nativeDensity (bankData D₀ Tj (posBank u)) h y x -
      nativeDensity (bankData D₀ Tj (negBank u)) h y x = unitVal D₀ Tj h y x u := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [nativeDensity_split D₀ Tj (posBank u), nativeDensity_split D₀ Tj (negBank u)]
  rcases u with u | j | i
  · fin_cases u <;>
      simp [posBank, negBank, unitVal, bank0, yukD_zero, h2] <;> ring
  · simp only [posBank, negBank, unitVal, bank0, sum_single_mul, yukD_zero, inv_zero, mul_zero,
      zero_mul, sub_zero, Pi.zero_apply, Finset.sum_const_zero]
    ring
  · simp [posBank, negBank, unitVal, bank0, yukD_zero]

/-- **The affine decomposition of the native density** over the unit banks. -/
theorem nativeDensity_affine (θ : Bank J 𝓗 𝓢) (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢)
    (x : Grid N) :
    nativeDensity (bankData D₀ Tj θ) h y x = nativeDensity (bankData D₀ Tj bank0) h y x +
      ∑ u, coef θ u * (nativeDensity (bankData D₀ Tj (posBank u)) h y x -
        nativeDensity (bankData D₀ Tj (negBank u)) h y x) := by
  simp only [nativeDensity_unit D₀ Tj _ h y x]
  rw [nativeDensity_split D₀ Tj θ h y x]
  have hY : yukD θ.Y y x = ∑ i, (yBasis 𝓗 𝓢).repr θ.Y i * yukD (yBasis 𝓗 𝓢 i) y x := by
    conv_lhs => rw [← (yBasis 𝓗 𝓢).sum_repr θ.Y]
    exact yukD_sum _ _ _ y x
  rw [hY]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_five, coef, unitVal, mul_neg,
    Finset.sum_neg_distrib]
  ring

end Affine

/-! ### The affine decomposition of the action and of its first variation -/

section AffineVar

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
variable {J : ℕ}
variable (D₀ : Data 𝔄 𝓗 𝓢) (Tj : Fin J → 𝔄 →L[ℝ] E)

/-- **The affine decomposition of the unchanged local action** over the unit banks. -/
theorem localAction_affine {N : ℕ} [NeZero N] (θ : Bank J 𝓗 𝓢) (h : ℝ)
    (y : Grid N → Field 𝔄 𝓗 𝓢) :
    localAction (bankData D₀ Tj θ) h y = localAction (bankData D₀ Tj bank0) h y +
      ∑ u, coef θ u * (localAction (bankData D₀ Tj (posBank u)) h y -
        localAction (bankData D₀ Tj (negBank u)) h y) := by
  have e : ∑ x, nativeDensity (bankData D₀ Tj θ) h y x = ∑ x, (nativeDensity
      (bankData D₀ Tj bank0) h y x + ∑ u, coef θ u * (nativeDensity (bankData D₀ Tj (posBank u))
        h y x - nativeDensity (bankData D₀ Tj (negBank u)) h y x)) :=
    Finset.sum_congr rfl fun x _ => nativeDensity_affine D₀ Tj θ h y x
  simp only [localAction]
  rw [e, Finset.sum_add_distrib, Finset.sum_comm]
  simp only [mul_add, Finset.mul_sum, mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The complete native variation has a derivative along the nodal test record on the charts. -/
theorem hasDerivAt_localAction (D : Data 𝔄 𝓗 𝓢) (κf : W' →L[ℝ] CoSpinor 𝓢) (T : 𝔄 →L[ℝ] E')
    (hip : ∀ X Y, D.ipA X Y = ⟪T X, T Y⟫) {N : ℕ} [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢)
    (τ : DTest 𝔄 𝓗 𝓢 W') (hdet : ∀ x, 0 < (coframe y x).det)
    (hlog : ∀ x μ ν, ‖NativeDensity.cartanPlaquette (N : ℝ)⁻¹ (coframe y) x μ ν - 1‖ < 1)
    (hreg : ∀ x, NativeGravityJet.GravRegular ((N : ℝ)⁻¹,
      (ShiftedJetAction.stencil (N : ℝ)⁻¹ (shiftVec N) x (coframeM y) :
        NativeGravityFirstJet.T4)))
    (hch : ∀ x μ ν, (N : ℝ)⁻¹ * LogBCH.normSum
      (NativeYMIdentification.slots (NativeYMBridge.gaugeArr y) x μ ν) ≤ 1 / 32) :
    HasDerivAt (fun s : ℝ => localAction D (N : ℝ)⁻¹ (y + s • testRec κf N y τ))
      (NativeAllSector.nativeVar D N y (testRec κf N y τ)) 0 := by
  have hN : ((N : ℝ))⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne N))
  have hdet' : ∀ x, (coframe y x).det ≠ 0 := fun x => (hdet x).ne'
  have hg1 := NativeGravityFirstJet.hasDerivAt_gravAction D hN y
    (NativeGravityFirstJet.liftRecord N y τ.k) hdet hlog hreg
  have hg : HasDerivAt (fun s : ℝ => NativeGravityFirstJet.gravAction D (N : ℝ)⁻¹
      (y + s • testRec κf N y τ)) (NativeGravityFirstJet.gravVariation D N y τ.k) 0 := by
    have e : (fun s : ℝ => NativeGravityFirstJet.gravAction D (N : ℝ)⁻¹
        (y + s • testRec κf N y τ)) = fun s => NativeGravityFirstJet.gravAction D (N : ℝ)⁻¹
          (y + s • NativeGravityFirstJet.liftRecord N y τ.k) :=
      funext fun s => NativeAllSector.gravAction_testRec D κf _ y τ s
    rw [e, NativeGravityFirstJet.gravVariation, hg1.deriv]
    exact hg1
  have hy := NativeYMBridge.hasDerivAt_ymAct D T hip y (testRec κf N y τ) (fun x => hdet' x) hch
  have hh := NativeHiggsVar.hasDerivAt_higgsAct D y (testRec κf N y τ) hdet'
  have hd := NativeDirac.hasDerivAt_dAct D (N : ℝ)⁻¹ y (testRec κf N y τ) hdet'
  have htot := ((hg.add hy).add hh).add hd
  have e : (fun s : ℝ => localAction D (N : ℝ)⁻¹ (y + s • testRec κf N y τ)) =
      fun s => NativeGravityFirstJet.gravAction D (N : ℝ)⁻¹ (y + s • testRec κf N y τ) +
        NativeYMBridge.ymAct D (N : ℝ)⁻¹ (y + s • testRec κf N y τ) +
        NativeHiggsVar.higgsAct D (N : ℝ)⁻¹ (y + s • testRec κf N y τ) +
        NativeDirac.dAct D (N : ℝ)⁻¹ (y + s • testRec κf N y τ) :=
    funext fun s => NativeAllSector.localAction_eq_sum D _ _
  rw [e, NativeAllSector.nativeVar_testRec_eq D κf T hip y τ hdet hlog hreg hch,
    NativeYMBridge.ymVar, hy.deriv, NativeHiggsVar.higgsVar, hh.deriv, NativeDirac.dVar, hd.deriv]
  exact htot

/-- **The affine decomposition of the complete native first variation.** -/
theorem nativeVar_affine (θ : Bank J 𝓗 𝓢) {N : ℕ} [NeZero N] (y v : Grid N → Field 𝔄 𝓗 𝓢)
    (hd0 : HasDerivAt (fun s : ℝ => localAction (bankData D₀ Tj bank0) (N : ℝ)⁻¹ (y + s • v))
      (NativeAllSector.nativeVar (bankData D₀ Tj bank0) N y v) 0)
    (hdp : ∀ u, HasDerivAt (fun s : ℝ => localAction (bankData D₀ Tj (posBank u)) (N : ℝ)⁻¹
      (y + s • v)) (NativeAllSector.nativeVar (bankData D₀ Tj (posBank u)) N y v) 0)
    (hdn : ∀ u, HasDerivAt (fun s : ℝ => localAction (bankData D₀ Tj (negBank u)) (N : ℝ)⁻¹
      (y + s • v)) (NativeAllSector.nativeVar (bankData D₀ Tj (negBank u)) N y v) 0) :
    NativeAllSector.nativeVar (bankData D₀ Tj θ) N y v =
      NativeAllSector.nativeVar (bankData D₀ Tj bank0) N y v +
        ∑ u, coef θ u * (NativeAllSector.nativeVar (bankData D₀ Tj (posBank u)) N y v -
          NativeAllSector.nativeVar (bankData D₀ Tj (negBank u)) N y v) := by
  have hD := hd0.add (HasDerivAt.fun_sum (u := Finset.univ) fun u _ =>
    ((hdp u).sub (hdn u)).const_mul (coef θ u))
  have e : (fun s : ℝ => localAction (bankData D₀ Tj θ) (N : ℝ)⁻¹ (y + s • v)) =
      fun s => localAction (bankData D₀ Tj bank0) (N : ℝ)⁻¹ (y + s • v) +
        ∑ u, coef θ u * (localAction (bankData D₀ Tj (posBank u)) (N : ℝ)⁻¹ (y + s • v) -
          localAction (bankData D₀ Tj (negBank u)) (N : ℝ)⁻¹ (y + s • v)) :=
    funext fun s => localAction_affine D₀ Tj θ _ _
  rw [NativeAllSector.nativeVar, e]
  exact hD.deriv

end AffineVar

/-! ### `eq:native-all-sector-limit` with varying coefficient banks -/

section Limit

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {J : ℕ}
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}

/-- **Convergence of coefficient banks** `θ_h → θ` (all coordinates). -/
structure BankConv (θs : ℕ → Bank J 𝓗 𝓢) (θ : Bank J 𝓗 𝓢) : Prop where
  κ : Tendsto (fun k => (θs k).κ) atTop (𝓝 θ.κ)
  Λ : Tendsto (fun k => (θs k).Λ) atTop (𝓝 θ.Λ)
  lamH : Tendsto (fun k => (θs k).lamH) atTop (𝓝 θ.lamH)
  vH : Tendsto (fun k => (θs k).vH) atTop (𝓝 θ.vH)
  w : ∀ j, Tendsto (fun k => (θs k).w j) atTop (𝓝 (θ.w j))
  Y : Tendsto (fun k => (θs k).Y) atTop (𝓝 θ.Y)

/-- The affine coordinates of convergent banks converge (`κ ≠ 0`). -/
theorem tendsto_coef {θs : ℕ → Bank J 𝓗 𝓢} {θ : Bank J 𝓗 𝓢} (hθ : BankConv θs θ)
    (hκ : θ.κ ≠ 0) (u : Unit5 J (dY 𝓗 𝓢)) :
    Tendsto (fun k => coef (θs k) u) atTop (𝓝 (coef θ u)) := by
  rcases u with u | j | i
  · fin_cases u
    · exact hθ.κ.inv₀ hκ
    · exact hθ.Λ.mul (hθ.κ.inv₀ hκ)
    · exact hθ.lamH
    · exact ((tendsto_const_nhds.mul hθ.lamH).mul (hθ.vH.pow 2)).sub
        (hθ.lamH.mul (hθ.vH.pow 4))
    · exact ((hθ.lamH.mul (hθ.vH.pow 4)).sub (hθ.lamH.mul (hθ.vH.pow 2))).div_const 2
  · exact hθ.w j
  · have hc : Continuous fun Y : 𝓗 →L[ℝ] Spin 𝓢 => (yBasis 𝓗 𝓢).repr Y i :=
      LinearMap.continuous_of_finiteDimensional ((yBasis 𝓗 𝓢).coord i)
    exact (hc.tendsto θ.Y).comp hθ.Y

variable (D₀ : Data 𝔄 𝓗 𝓢) (Tj : Fin J → 𝔄 →L[ℝ] E) (κf : W' →L[ℝ] CoSpinor 𝓢)

/-- The Higgs hypotheses only involve the (bank-independent) Higgs representation. -/
def higgsHypBank {θ : Bank J 𝓗 𝓢} (P : NativeHiggsVar.HiggsHyp (bankData D₀ Tj θ) y)
    (b : Bank J 𝓗 𝓢) : NativeHiggsVar.HiggsHyp (bankData D₀ Tj b) y :=
  ⟨P.H₀, P.hH, P.K₀, P.hK⟩

set_option maxHeartbeats 1600000 in
/-- **`eq:native-all-sector-limit` with varying coefficient banks** (`(N5)`,
`thm:native-firstvariation-no-band`).  Let `θ_h → θ` (`κ ≠ 0`, nonnegative gauge weights at the
limit) and let the hypotheses of `NativeAllSector.native_all_sector_limit` hold at the limit bank.
Then the complete finite first variation **with the cutoff banks `θ_h`** converges to the
continuum first variation `D𝒮_θ(z)` at the limit bank, uniformly on every `C²` ball. -/
theorem native_all_sector_limit_bank {θs : ℕ → Bank J 𝓗 𝓢} {θ : Bank J 𝓗 𝓢}
    (hθ : BankConv θs θ) (hκ : θ.κ ≠ 0) (hw : ∀ j, 0 ≤ θ.w j) (H : CoHyp n y)
    (hpos : ∀ M ∈ H.Ke, 0 < Matrix.det (show Mat from M)) (hc : H.c ≤ 1 / 64)
    {F : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hF : ∀ μ ν, LpTendsto MeasureTheory.volume 2
      (fun k => pc (fun x => NativeScaling.fieldStrength (n k : ℝ)⁻¹ (gauge (y k)) x μ ν))
      (F μ ν))
    (P : NativeHiggsVar.HiggsHyp (bankData D₀ Tj θ) y) (S : SpinHyp κf y)
    {u₀ : 𝕋 → NativeDiracLimit.Dif 𝓢 W'} (hu₀ : MemLp u₀ 2 MeasureTheory.volume) {C : ℝ}
    (hub : ∀ k, (eLpNorm (pc (NativeDiracLimit.difs (y k) (S.χ k))) 2
      MeasureTheory.volume).toReal ≤ C)
    (hwk : ∀ g : 𝕋 → NativeDiracLimit.Dif 𝓢 W' →L[ℝ] ℝ, MemLp g 2 MeasureTheory.volume →
      Tendsto (fun k => ∫ z, g z (pc (NativeDiracLimit.difs (y k) (S.χ k)) z)) atTop
        (𝓝 (∫ z, g z (u₀ z))))
    (M : NNReal) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 W', τ.norm ≤ M →
      |NativeAllSector.nativeVar (bankData D₀ Tj (θs k)) (n k) (y k) (testRec κf (n k) (y k) τ) -
        NativeAllSector.contAllVar (bankData D₀ Tj θ) κf (bankT Tj θ.w) H F P S u₀ τ| ≤ ε := by
  intro ε hε
  have hF2 : ∀ μ ν, MemLp (F μ ν) 2 MeasureTheory.volume := fun μ ν => (hF μ ν).memLp_lim
  -- the limit at the limit bank
  have hlimθ := NativeAllSector.native_all_sector_limit (bankData D₀ Tj θ) κf (bankT Tj θ.w)
    (bank_hip D₀ Tj θ hw) H hpos hc hF P S hu₀ hub hwk M (ε / 2) (half_pos hε)
  -- uniform bounds of the unit-bank variations
  have hbd : ∀ b : Bank J 𝓗 𝓢, (∀ j, 0 ≤ b.w j) → ∃ K, ∀ᶠ k in atTop,
      ∀ τ : DTest 𝔄 𝓗 𝓢 W', τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData D₀ Tj b) (n k) (y k) (testRec κf (n k) (y k) τ)| ≤
          K := by
    intro b hb
    obtain ⟨Cb, hCb⟩ := abs_contAllVar_le (bankData D₀ Tj b) κf (bankT Tj b.w) H hpos hF2
      (higgsHypBank D₀ Tj P b) S hu₀ M
    refine ⟨Cb + 1, ?_⟩
    filter_upwards [NativeAllSector.native_all_sector_limit (bankData D₀ Tj b) κf (bankT Tj b.w)
      (bank_hip D₀ Tj b hb) H hpos hc hF (higgsHypBank D₀ Tj P b) S hu₀ hub hwk M 1 one_pos]
      with k hk τ hτ
    have h1 := hk τ hτ
    have h2 := hCb τ hτ
    have := abs_sub_abs_le_abs_sub
      (NativeAllSector.nativeVar (bankData D₀ Tj b) (n k) (y k) (testRec κf (n k) (y k) τ))
      (NativeAllSector.contAllVar (bankData D₀ Tj b) κf (bankT Tj b.w) H F
        (higgsHypBank D₀ Tj P b) S u₀ τ)
    linarith
  choose Kp hKp using fun u => hbd (posBank u) (posBank_w_nonneg u)
  choose Kn hKn using fun u => hbd (negBank u) (negBank_w_nonneg u)
  -- the coefficient errors
  set Ku : Unit5 J (dY 𝓗 𝓢) → ℝ := fun u => |Kp u| + |Kn u|
  have hcoef : Tendsto (fun k => ∑ u, |coef (θs k) u - coef θ u| * Ku u) atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset (Unit5 J (dY 𝓗 𝓢))) fun u _ =>
      (((tendsto_coef hθ hκ u).sub_const (coef θ u)).abs.mul_const (Ku u))
    simpa using this
  have hcoefε : ∀ᶠ k in atTop, ∑ u, |coef (θs k) u - coef θ u| * Ku u ≤ ε / 2 :=
    (tendsto_order.1 hcoef).2 (ε / 2) (half_pos hε) |>.mono fun k hk => hk.le
  filter_upwards [hlimθ, hcoefε, Filter.eventually_all.2 hKp, Filter.eventually_all.2 hKn,
    NativeAllSector.eventually_charts H hpos hc] with k hk1 hk2 hk3 hk4 hch τ hτ
  -- the affine decomposition at the cutoff bank and at the limit bank
  have hD : ∀ b : Bank J 𝓗 𝓢, (∀ j, 0 ≤ b.w j) → HasDerivAt
      (fun s : ℝ => localAction (bankData D₀ Tj b) (n k : ℝ)⁻¹
        (y k + s • testRec κf (n k) (y k) τ))
      (NativeAllSector.nativeVar (bankData D₀ Tj b) (n k) (y k) (testRec κf (n k) (y k) τ)) 0 :=
    fun b hb => hasDerivAt_localAction (bankData D₀ Tj b) κf (bankT Tj b.w) (bank_hip D₀ Tj b hb)
      (y k) τ hch.1 hch.2.1 hch.2.2.1 hch.2.2.2
  have e1 := nativeVar_affine D₀ Tj (θs k) (y k) (testRec κf (n k) (y k) τ)
    (hD bank0 bank0_w_nonneg) (fun u => hD _ (posBank_w_nonneg u))
    (fun u => hD _ (negBank_w_nonneg u))
  have e2 := nativeVar_affine D₀ Tj θ (y k) (testRec κf (n k) (y k) τ)
    (hD bank0 bank0_w_nonneg) (fun u => hD _ (posBank_w_nonneg u))
    (fun u => hD _ (negBank_w_nonneg u))
  set V := fun b => NativeAllSector.nativeVar (bankData D₀ Tj b) (n k) (y k)
    (testRec κf (n k) (y k) τ) with hVdef
  have hdiff : |V (θs k) - V θ| ≤ ε / 2 := by
    have e : V (θs k) - V θ =
        ∑ u, (coef (θs k) u - coef θ u) * (V (posBank u) - V (negBank u)) := by
      simp only [V] at e1 e2 ⊢
      rw [e1, e2, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans (Finset.sum_le_sum fun u _ => ?_) hk2)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ?_ ?_)) (abs_nonneg _)
    · exact (hk3 u τ hτ).trans (le_abs_self _)
    · exact (hk4 u τ hτ).trans (le_abs_self _)
  have h1 := hk1 τ hτ
  calc |V (θs k) - NativeAllSector.contAllVar (bankData D₀ Tj θ) κf (bankT Tj θ.w) H F P S u₀ τ|
      ≤ |V (θs k) - V θ| + |V θ -
          NativeAllSector.contAllVar (bankData D₀ Tj θ) κf (bankT Tj θ.w) H F P S u₀ τ| :=
        abs_sub_le _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hdiff h1
    _ = ε := by ring

end Limit

/-! ### The Euler corollary and the closure from `(N1)–(N5)` with varying banks -/

section Closure

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {J : ℕ}
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- **The Euler corollary with varying banks**: if the complete finite variation with the cutoff
banks tends to zero on the unit test family, the limit satisfies `D𝒮_θ(z)[v] = 0` for every test
`v` (limit bank `θ`). -/
theorem native_all_sector_euler_bank {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗]
    [CompleteSpace 𝓗] [Nontrivial 𝓗] [FiniteDimensional ℝ 𝓗]
    {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢} (D₀ : Data 𝔄 𝓗 𝓢) (Tj : Fin J → 𝔄 →L[ℝ] E)
    (κf : W' →L[ℝ] CoSpinor 𝓢) {θs : ℕ → Bank J 𝓗 𝓢} {θ : Bank J 𝓗 𝓢}
    (hθ : BankConv θs θ) (hκ : θ.κ ≠ 0) (hw : ∀ j, 0 ≤ θ.w j) (H : CoHyp n y)
    (hpos : ∀ M ∈ H.Ke, 0 < Matrix.det (show Mat from M)) (hc : H.c ≤ 1 / 64)
    {F : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hF : ∀ μ ν, LpTendsto MeasureTheory.volume 2
      (fun k => pc (fun x => NativeScaling.fieldStrength (n k : ℝ)⁻¹ (gauge (y k)) x μ ν))
      (F μ ν))
    (P : NativeHiggsVar.HiggsHyp (bankData D₀ Tj θ) y) (S : SpinHyp κf y)
    {u₀ : 𝕋 → NativeDiracLimit.Dif 𝓢 W'} (hu₀ : MemLp u₀ 2 MeasureTheory.volume) {C : ℝ}
    (hub : ∀ k, (eLpNorm (pc (NativeDiracLimit.difs (y k) (S.χ k))) 2
      MeasureTheory.volume).toReal ≤ C)
    (hwk : ∀ g : 𝕋 → NativeDiracLimit.Dif 𝓢 W' →L[ℝ] ℝ, MemLp g 2 MeasureTheory.volume →
      Tendsto (fun k => ∫ z, g z (pc (NativeDiracLimit.difs (y k) (S.χ k)) z)) atTop
        (𝓝 (∫ z, g z (u₀ z))))
    (hstat : ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 W', τ.norm ≤ 1 →
      |NativeAllSector.nativeVar (bankData D₀ Tj (θs k)) (n k) (y k)
        (testRec κf (n k) (y k) τ)| ≤ ε)
    (τ : DTest 𝔄 𝓗 𝓢 W') :
    NativeAllSector.contAllVar (bankData D₀ Tj θ) κf (bankT Tj θ.w) H F P S u₀ τ = 0 := by
  have hτ0 := τ.norm_nonneg
  set c : ℝ := τ.norm + 1 with hc'
  have hc0 : 0 < c := by positivity
  refine abs_eq_zero.1 (le_antisymm ?_ (abs_nonneg _))
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlim := native_all_sector_limit_bank D₀ Tj κf hθ hκ hw H hpos hc hF P S hu₀ hub hwk
    ⟨τ.norm, hτ0⟩ (ε / 2) (by positivity)
  have hst := hstat (ε / (2 * c)) (by positivity)
  obtain ⟨k, hk1, hk2⟩ := (hlim.and hst).exists
  have h1 := hk1 τ le_rfl
  have hτ1 : (NativeAllSector.dsmul c⁻¹ τ).norm ≤ 1 := by
    rw [NativeAllSector.dsmul_norm, abs_of_pos (inv_pos.2 hc0), inv_mul_le_iff₀ hc0]
    linarith
  have h2 := hk2 (NativeAllSector.dsmul c⁻¹ τ) hτ1
  have hrec : testRec κf (n k) (y k) τ =
      c • testRec κf (n k) (y k) (NativeAllSector.dsmul c⁻¹ τ) := by
    rw [NativeAllSector.testRec_dsmul, smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]
  rw [hrec, NativeAllSector.nativeVar_smul] at h1
  have h3 : |c * NativeAllSector.nativeVar (bankData D₀ Tj (θs k)) (n k) (y k)
      (testRec κf (n k) (y k) (NativeAllSector.dsmul c⁻¹ τ))| ≤ ε / 2 := by
    rw [abs_mul, abs_of_pos hc0]
    calc c * |NativeAllSector.nativeVar (bankData D₀ Tj (θs k)) (n k) (y k)
          (testRec κf (n k) (y k) (NativeAllSector.dsmul c⁻¹ τ))|
        ≤ c * (ε / (2 * c)) := mul_le_mul_of_nonneg_left h2 hc0.le
      _ = ε / 2 := by field_simp
  have h4 := abs_sub_abs_le_abs_sub
    (NativeAllSector.contAllVar (bankData D₀ Tj θ) κf (bankT Tj θ.w) H F P S u₀ τ)
    (c * NativeAllSector.nativeVar (bankData D₀ Tj (θs k)) (n k) (y k)
      (testRec κf (n k) (y k) (NativeAllSector.dsmul c⁻¹ τ)))
  rw [abs_sub_comm] at h4
  linarith

variable {rH : ℕ} [NeZero rH] {r r' : ℕ} [NeZero r] [NeZero r']

open NativeSpinorGraph (κid spinGraph dualGraph coHypSubseq)

set_option maxHeartbeats 1600000 in
/-- **`thm:native-firstvariation-no-band`, main assertions, from `(N1)–(N5)`** (varying coefficient
banks).  Hypotheses as in `NativeAllSectorGraph.native_all_sector_closure`, with the unchanged
local action at the cutoff banks `θ_h` (fixed representation packet `D₀`, gauge metrics
`⟪T_j ·, T_j ·⟫`), `θ_h → θ` with `κ ≠ 0` and nonnegative limit gauge weights (`(N5)`).  Then
after extraction `F = F_A`, `K = D_A H` with `R^0 D⁺H_h → K - ρ_H(A)H` in `L²`, the spinor limits
with `u₀ = (∂Ψ, ∂Ψ̄)`, `eq:native-all-sector-limit` (cutoff banks against the limit bank, uniformly
on every `C²` ball) and the Euler corollary hold. -/
theorem native_all_sector_closure_bank (D₀ : Data 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (Tj : Fin J → 𝔄 →L[ℝ] E) {θs : ℕ → Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢}
    {θ : Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢} (hθ : BankConv θs θ) (hκ : θ.κ ≠ 0)
    (hw : ∀ j, 0 ≤ θ.w j)
    (Θ : 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (Θ' : CoSpinor 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r'))
    {y : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢} (H : CoHyp n y)
    (hpos : ∀ M ∈ H.Ke, 0 < Matrix.det (show Mat from M)) (hc : H.c ≤ 1 / 64)
    {F : Fin 4 → Fin 4 → 𝕋 → 𝔄}
    (hF : ∀ μ ν, LpTendsto MeasureTheory.volume 2
      (fun k => pc (fun x => NativeScaling.fieldStrength (n k : ℝ)⁻¹ (gauge (y k)) x μ ν))
      (F μ ν))
    (hUH : ∀ k x μ (v : EuclideanSpace ℝ (Fin rH)),
      ‖exp ((n k : ℝ)⁻¹ • D₀.ρHL (gauge (y k) μ x)) v‖ = ‖v‖)
    {BH : ℝ} (hHb : ∀ k, gridNorm (higgs (y k)) ≤ BH)
    {K₀ : Fin 4 → 𝕋 → EuclideanSpace ℝ (Fin rH)}
    (hK : ∀ μ, LpTendsto MeasureTheory.volume 2
      (fun k => pc (fun x => higgsLink D₀ (n k : ℝ)⁻¹ (y k) x μ)) (K₀ μ))
    (hU : ∀ k x μ (v : 𝓢), ‖D₀.ρS (exp ((n k : ℝ)⁻¹ • gauge (y k) μ x)) v‖ = ‖v‖)
    {B : ℝ} (hΨ : ∀ k, gridNorm (psi (y k)) ≤ B)
    (hKs : ∀ k μ, gridNorm (fun x => spinGraph D₀ (n k : ℝ)⁻¹ (y k) x μ) ≤ B)
    (hΨb : ∀ k, gridNorm (psiBar (y k)) ≤ B)
    (hKb : ∀ k μ, gridNorm (fun x => dualGraph D₀ (n k : ℝ)⁻¹ (y k) x μ) ≤ B) :
    ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ,
      ∃ P : NativeHiggsVar.HiggsHyp (bankData D₀ Tj θ) (fun k => y (φ k)),
      ∃ S : SpinHyp (κid 𝓢) (fun k => y (φ k)), ∃ u₀ : 𝕋 → NativeDiracLimit.Dif 𝓢 (CoSpinor 𝓢),
      -- `F = F_A`
      (∀ μ ν (ℓ : 𝔄 →L[ℝ] ℂ) (m : Fin 4 → ℤ),
        UnitAddTorus.mFourierCoeff (fun z => ℓ (F μ ν z)) m -
            UnitAddTorus.mFourierCoeff
              (fun z => ℓ (H.A₀ μ z * H.A₀ ν z - H.A₀ ν z * H.A₀ μ z)) m =
          2 * Real.pi * Complex.I * m μ * UnitAddTorus.mFourierCoeff (fun z => ℓ (H.A₀ ν z)) m -
            2 * Real.pi * Complex.I * m ν *
              UnitAddTorus.mFourierCoeff (fun z => ℓ (H.A₀ μ z)) m) ∧
      -- `K = D_A H`
      P.K₀ = K₀ ∧
      (∀ μ, LpTendsto MeasureTheory.volume 2
        (fun k => pc (NativeHiggs.DpV μ (higgs (y (φ k)))))
        (fun z => K₀ μ z - D₀.ρHL (H.A₀ μ z) (P.H₀ z))) ∧
      -- `u₀ = (∂Ψ, ∂Ψ̄)`
      (∀ j, ∃ f : Lp ℂ 2 (MeasureTheory.volume : Measure 𝕋),
        ((f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ (S.Ψ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 f ∧ ∀ μ, (TorusSobolev.weakDeriv μ f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume]
          fun z => ((Θ ((u₀ z).1 μ) j : ℝ) : ℂ)) ∧
      (∀ j, ∃ f : Lp ℂ 2 (MeasureTheory.volume : Measure 𝕋),
        ((f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ' (S.χ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 f ∧ ∀ μ, (TorusSobolev.weakDeriv μ f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume]
          fun z => ((Θ' ((u₀ z).2 μ) j : ℝ) : ℂ)) ∧
      -- `eq:native-all-sector-limit` with the cutoff banks
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData D₀ Tj (θs (φ k))) (n (φ k)) (y (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          NativeAllSector.contAllVar (bankData D₀ Tj θ) (κid 𝓢) (bankT Tj θ.w)
            (coHypSubseq H hφ) F P S u₀ τ| ≤ ε) ∧
      -- the Euler corollary with the cutoff banks
      ((∀ ε > 0, ∀ᶠ k in atTop,
          ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ 1 →
          |NativeAllSector.nativeVar (bankData D₀ Tj (θs k)) (n k) (y k)
            (testRec (κid 𝓢) (n k) (y k) τ)| ≤ ε) →
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
          NativeAllSector.contAllVar (bankData D₀ Tj θ) (κid 𝓢) (bankT Tj θ.w)
            (coHypSubseq H hφ) F P S u₀ τ = 0) := by
  set D := bankData D₀ Tj θ
  -- `(N3)`: the Higgs extraction
  obtain ⟨φ₁, hφ₁, P₁, hP₁, hDH⟩ := NativeHiggsVar.exists_higgsHyp D H.hn H.hA hUH hHb hK
  -- `(N4)`: the spinor extraction along `φ₁`
  have hn₁ : Tendsto (fun k => n (φ₁ k)) atTop atTop := H.hn.comp hφ₁.tendsto_atTop
  obtain ⟨φ₂, hφ₂, S, u₀, -, hu₀, ⟨C, hub⟩, hwk, hid1, hid2⟩ :=
    NativeSpinorGraph.native_spinor_extraction D Θ Θ' hn₁
      (fun μ => (H.hA μ).comp_strictMono hφ₁) (P₁.hH.mono (by norm_num) (by norm_num))
      (fun k => hU (φ₁ k)) (fun k => hΨ (φ₁ k)) (fun k => hKs (φ₁ k)) (fun k => hΨb (φ₁ k))
      (fun k => hKb (φ₁ k))
  have hφ : StrictMono (fun k => φ₁ (φ₂ k)) := hφ₁.comp hφ₂
  set P := NativeAllSectorGraph.higgsHypSubseq P₁ hφ₂ with hPdef
  set H' := coHypSubseq H hφ with hH'
  have hF' : ∀ μ ν, LpTendsto MeasureTheory.volume 2 (fun k => pc (fun x =>
      NativeScaling.fieldStrength (n (φ₁ (φ₂ k)) : ℝ)⁻¹ (gauge (y (φ₁ (φ₂ k)))) x μ ν))
      (F μ ν) :=
    fun μ ν => (hF μ ν).comp_strictMono hφ
  have hθ' : BankConv (fun k => θs (φ₁ (φ₂ k))) θ :=
    ⟨hθ.κ.comp hφ.tendsto_atTop, hθ.Λ.comp hφ.tendsto_atTop, hθ.lamH.comp hφ.tendsto_atTop,
      hθ.vH.comp hφ.tendsto_atTop, fun j => (hθ.w j).comp hφ.tendsto_atTop,
      hθ.Y.comp hφ.tendsto_atTop⟩
  refine ⟨fun k => φ₁ (φ₂ k), hφ, P, S, u₀, fun μ ν ℓ m => ?_, by rw [hPdef]; exact hP₁,
    fun μ => (hDH μ).comp_strictMono hφ₂, hid1, hid2,
    fun M => native_all_sector_limit_bank D₀ Tj (κid 𝓢) hθ' hκ hw H' hpos hc hF' P S hu₀
      hub hwk M, fun hstat τ => ?_⟩
  · have hA : ∀ μ, LpTendsto MeasureTheory.volume 4
        (fun k => pc (fun x => NativeYMBridge.gaugeArr (y k) x μ)) (H.A₀ μ) := H.hA
    exact (NativeYMIdentification.native_YM_curvature_identification H.hn hA
      (NativeAllSectorGraph.lpTendsto_curvLog H hF) μ ν).2 ℓ m
  · refine native_all_sector_euler_bank D₀ Tj (κid 𝓢) hθ' hκ hw H' hpos hc hF' P S hu₀ hub hwk
      (fun ε hε => ?_) τ
    exact (hstat ε hε).filter_mono hφ.tendsto_atTop |>.mono fun k hk => hk

end Closure

/-! ### Non-vacuity -/

section NonVacuity

open NativeAllSectorGraph (exData2 exCoHyp2 exCoHyp2_pos flat2 frameC frameCo gauge_flat2)
open NativeGravityFirstJet (flatRecord)
open NativeSpinorGraph (κid spinGraph dualGraph coHypSubseq)

local instance : Nontrivial (CoSpinor ℂ) :=
  ⟨⟨0, ContinuousLinearMap.id ℝ ℂ, fun h => by
    have := congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) h
    simp at this⟩⟩

local instance : NeZero (Module.finrank ℝ (CoSpinor ℂ)) := ⟨Module.finrank_pos.ne'⟩

/-- The `u(1)` gauge metric `⟪X, Y⟫` on `ℂ` (one simple factor). -/
def exTj : Fin 1 → ℂ →L[ℝ] ℂ := fun _ => ContinuousLinearMap.id ℝ ℂ

/-- The limit bank `(κ, Λ, λ_H, v_H, g^{-2}, Y) = (1, 0, 1, 1, 1, 0)`. -/
def exBank : Bank 1 (EuclideanSpace ℝ (Fin 2)) ℂ := ⟨1, 0, 1, 1, fun _ => 1, 0⟩

/-- Genuinely varying cutoff banks `κ_h = 1 + 1/(k+1) → 1`. -/
def exBanks (k : ℕ) : Bank 1 (EuclideanSpace ℝ (Fin 2)) ℂ :=
  ⟨1 + 1 / ((k : ℝ) + 1), 0, 1, 1, fun _ => 1, 0⟩

theorem exBanks_conv : BankConv exBanks exBank where
  κ := by simpa [exBanks, exBank] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
  Λ := tendsto_const_nhds
  lamH := tendsto_const_nhds
  vH := tendsto_const_nhds
  w _ := tendsto_const_nhds
  Y := tendsto_const_nhds

/-- **Non-vacuity of `native_all_sector_closure_bank`** (`(N1)–(N5)` with genuinely varying banks):
the flat records of the abelian Einstein–Higgs–Dirac packet with cutoff banks
`κ_h = 1 + 1/(k+1) → 1` satisfy every hypothesis; the theorem yields the extraction and the
all-sector limit at the limit bank. -/
example : ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ,
    ∃ P : NativeHiggsVar.HiggsHyp (bankData exData2 exTj exBank) (fun k => flat2 (φ k + 1)),
    ∃ S : SpinHyp (κid ℂ) (fun k => flat2 (φ k + 1)),
    ∃ u₀ : 𝕋 → NativeDiracLimit.Dif ℂ (CoSpinor ℂ),
      ∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest ℂ (EuclideanSpace ℝ (Fin 2)) ℂ
        (CoSpinor ℂ), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData exData2 exTj (exBanks (φ k))) (φ k + 1)
            (flat2 (φ k + 1)) (testRec (κid ℂ) (φ k + 1) (flat2 (φ k + 1)) τ) -
          NativeAllSector.contAllVar (bankData exData2 exTj exBank) (κid ℂ) (bankT exTj exBank.w)
            (coHypSubseq exCoHyp2 hφ) (fun _ _ _ => 0) P S u₀ τ| ≤ ε := by
  obtain ⟨φ, hφ, P, S, u₀, -, -, -, -, -, hlim, -⟩ := native_all_sector_closure_bank exData2 exTj
    exBanks_conv (by norm_num [exBank]) (fun _ => by norm_num [exBank]) frameC frameCo exCoHyp2
    exCoHyp2_pos (by norm_num [exCoHyp2]) (F := fun _ _ _ => 0)
    (fun μ ν => (LpTendsto.const (u := fun _ : 𝕋 => (0 : ℂ)) (memLp_const _)).congr
      (fun k => Eventually.of_forall fun z => by
        rw [gauge_flat2]
        simp [pc, NativeScaling.fieldStrength, NativeScaling.gaugePlaquette,
          ShiftedPlaquette.logOneAdd])
      (Eventually.of_forall fun _ => rfl))
    (fun k x μ v => by rw [gauge_flat2]; simp)
    (BH := 0) (fun k => by
      simp [TorusPiecewiseConstantTranslation.gridNorm, higgs, flat2, flatRecord])
    (K₀ := fun _ _ => 0)
    (fun μ => (LpTendsto.const (u := fun _ : 𝕋 => (0 : EuclideanSpace ℝ (Fin 2)))
      (memLp_const _)).congr (fun k => Eventually.of_forall fun z => by
        simp [pc, higgsLink, NativeScaling.higgsLink, higgs, flat2, flatRecord])
      (Eventually.of_forall fun _ => rfl))
    (fun k x μ v => by rw [gauge_flat2]; simp)
    (B := 0) (fun k => by simp [TorusPiecewiseConstantTranslation.gridNorm, psi, flat2, flatRecord])
    (fun k μ => by
      simp [TorusPiecewiseConstantTranslation.gridNorm, spinGraph, psi, flat2, flatRecord])
    (fun k => by simp [TorusPiecewiseConstantTranslation.gridNorm, psiBar, flat2, flatRecord])
    (fun k μ => by
      simp [TorusPiecewiseConstantTranslation.gridNorm, dualGraph, psiBar, flat2, flatRecord])
  exact ⟨φ, hφ, P, S, u₀, hlim⟩

end NonVacuity

end

end RenewalGeometry.NativeBank
