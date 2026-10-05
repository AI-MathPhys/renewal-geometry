/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.FiniteWilsonGaugeTransfer
import RenewalGeometry.Continuum.NativeLinkCovectorNorm
import RenewalGeometry.GaugeTheory.NativeRecordNormalizationSM

/-!
# The finite Wilson-screen zero-defect criterion (`thm:finite-Wilson-zero-defect`)

This file closes the two bridges left open by `FiniteWilsonZeroDefect.finite_wilson_criterion`
(the criterion after the same-record normalization):

* **(F5) ⟹ native stationarity** (`abs_nativeVar_testRec_le`): on the chart, the complete native
  first variation along the nodal test lift is bounded by the link covector norm,
  `|D S_h^{loc}(y)[𝓘_h v]| ≤ σ_h^{link} · K ‖v‖_{C²}` with `K` uniform in the cutoff
  (`NativeLinkCov.nativeVar_eq_linkCov`, the Cauchy–Schwarz bound
  `NativeLinkCov.abs_linkCov_le`, and the uniform mass bound `massSqP_tanOf_testRec_le` of the
  realized link tangents: symmetric coframe lift on the compact chart, `‖𝒥(h ad_A)‖ ≤ 2` on the
  scaled logarithm chart).
* **(i) the normalization glue** (`finite_wilson_zero_defect_of_rootedNorm`): the rooted
  certificate `(F2)` produces, via the rooted Coulomb normalization of the gauge group
  (`RootedNorm`: `rootedNorm_unitary` for `U(𝔄)` from
  `NativeRecordNorm.rooted_coulomb_normalization_chart`, `rootedNorm_SM` for
  `G_SM = S(U(3) × U(2))` from `NativeRecordNormSM.rooted_coulomb_normalization_chart_SM`), a
  site gauge `g` with values in the gauge group; the gauge-transformed records
  `y'_h = g·y_h` (`NativeGauge.gaugeRecord`) are in exact discrete Coulomb gauge with `‖A'_h‖_{4,h} ≤ ε_*`; `(F1)`, `(F3)`, `(F4)` transfer to them
  (`FiniteWilsonTransfer`), as does `(F5)` (`NativeLinkCov.covNormP_record_gauge`); then
  `finite_wilson_criterion` applies, and its stationarity premise holds.
* **`thm:finite-Wilson-zero-defect`**: `finite_wilson_zero_defect_SM` (the manuscript gauge group
  `G_SM`, `eq:gauge-group`) and `finite_wilson_zero_defect` (full unitary group `U(𝔄)`).
* `native_stationarity_budget` (`prop:equivariant-native-budgets`, stationarity clause, Cauchy–
  Schwarz form): `|D S_h^{loc}(y)[v]| ≤ σ_h^{link} √K ‖v‖_{0,h}` for every nodal test lift.

The coefficient banks enter the action through `bankData`; `bankCov` equips it with the
covariance structure of the representation packet (`Ad`-invariant component metrics `T_j`,
covariant Yukawa banks).
-/

open NormedSpace Finset Filter Topology Set MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace RenewalGeometry.FiniteWilsonClosure

open ShiftedJetAction (Grid unitVec)
open NativeScaling (Mat)
open NativeDensity NativeGauge NativeLinkCov NativeBank
open NativeDiracLimit (DTest testRec samp)
open NativeGravityFirstJet (M4 liftM coframeM)
open NativeSpinorGraph (κid)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### The symmetric coframe lift on a compact chart -/

theorem exists_liftM_bound {Ke : Set M4} (hK : IsCompact Ke) :
    ∃ Kl, 0 ≤ Kl ∧ ∀ e ∈ Ke, ∀ k : M4, ‖NativeGravityFirstJet.liftL e k‖ ≤ Kl * ‖k‖ := by
  have hc0 : Continuous fun p : M4 × M4 => NativeGravityFirstJet.liftL p.1 p.2 := by
    refine continuous_pi fun a => continuous_pi fun μ => ?_
    have e : (fun p : M4 × M4 => NativeGravityFirstJet.liftL p.1 p.2 a μ) = fun p : M4 × M4 =>
        -(1 / 2) * ∑ α, ∑ β, p.1 a α *
          NativeScaling.metric (show Mat from p.1) μ β * p.2 α β := by
      funext p
      exact NativeGravityFirstJet.liftM_apply (show Mat from p.1) (show Mat from p.2) a μ
    rw [e]
    simp only [NativeScaling.metric]
    fun_prop
  have hc : Continuous fun p : M4 × M4 => ‖NativeGravityFirstJet.liftL p.1 p.2‖ :=
    continuous_norm.comp hc0
  obtain ⟨K, hK'⟩ := (hK.prod (isCompact_closedBall (0 : M4) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun e he k => ?_⟩
  rcases eq_or_ne k 0 with rfl | hk
  · have h0 : NativeGravityFirstJet.liftL e (0 : M4) = 0 := map_zero _
    rw [h0, norm_zero]; simp
  · have hkpos : 0 < ‖k‖ := norm_pos_iff.2 hk
    have hmem : ((e, ‖k‖⁻¹ • k) : M4 × M4) ∈ Ke ×ˢ Metric.closedBall (0 : M4) 1 := by
      refine ⟨he, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hkpos.ne']
    have h1 := hK' _ hmem
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h1
    have e2 : NativeGravityFirstJet.liftL e k =
        ‖k‖ • NativeGravityFirstJet.liftL e (‖k‖⁻¹ • k) := by
      rw [map_smul, smul_smul, mul_inv_cancel₀ hkpos.ne', one_smul]
    rw [e2, norm_smul, norm_norm, mul_comm]
    exact mul_le_mul_of_nonneg_right (h1.trans (le_max_left _ _)) (norm_nonneg _)

/-! ### The bank data as a covariant packet -/

section Bank

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {J : ℕ}

/-- **The covariant packet of a coefficient bank**: the native data of the bank
(`bankData`, gauge metric `Σ_j w_j ⟪T_j ·, T_j ·⟫`, Yukawa block `θ.Y`) over a covariant
representation packet `C₀`, when each component metric `⟪T_j ·, T_j ·⟫` is `Ad`-invariant and the
Yukawa bank is covariant (the standing assumptions `tab:SM-representations`, `lem:SM-descent`). -/
def bankCov (C₀ : CovData 𝔄 𝓗 𝓢) (Tj : Fin J → 𝔄 →L[ℝ] E) (θ : Bank J 𝓗 𝓢)
    (hT : ∀ g ∈ C₀.G, ∀ j (X Y : 𝔄),
      ⟪Tj j ((g : 𝔄) * X * ↑g⁻¹), Tj j ((g : 𝔄) * Y * ↑g⁻¹)⟫ = ⟪Tj j X, Tj j Y⟫)
    (hY : ∀ g ∈ C₀.G, ∀ H : 𝓗, θ.Y (C₀.ρH g H) = C₀.ρS g * θ.Y H * C₀.ρS ↑g⁻¹) :
    CovData 𝔄 𝓗 𝓢 :=
  { bankData C₀.toData Tj θ with
    G := C₀.G
    norm_conj := C₀.norm_conj
    ipA_conj := fun g hg X Y => by
      change bankForm Tj θ.w _ _ = bankForm Tj θ.w X Y
      simp only [bankForm_apply, hT g hg]
    hermH_inv := C₀.hermH_inv
    σ_comm := C₀.σ_comm
    γ_comm := C₀.γ_comm
    yukawa_cov := hY
    ρS_isom := C₀.ρS_isom }

theorem bankCov_toData (C₀ : CovData 𝔄 𝓗 𝓢) (Tj : Fin J → 𝔄 →L[ℝ] E) (θ : Bank J 𝓗 𝓢) (hT hY) :
    (bankCov C₀ Tj θ hT hY).toData = bankData C₀.toData Tj θ := rfl

theorem massMetric_invariant_bankCov (C₀ : CovData 𝔄 𝓗 𝓢) (M : MassMetric 𝔄 𝓗)
    (hM : M.Invariant C₀) (Tj : Fin J → 𝔄 →L[ℝ] E) (θ : Bank J 𝓗 𝓢) (hT hY) :
    M.Invariant (bankCov C₀ Tj θ hT hY) :=
  ⟨hM.gm_conj, hM.hm_inv⟩

end Bank

/-! ### The uniform mass bound of the realized test tangents -/

section MassBound

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [Nontrivial 𝔄] [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]

theorem card_grid (N : ℕ) [NeZero N] : (Fintype.card (Grid N) : ℝ) = (N : ℝ) ^ 4 := by
  simp [Grid, ZMod.card]

/-- **The realized link tangents of the nodal test lift have uniformly bounded mass**:
`‖tanOf(𝓘_h v)‖²_{link} ≤ K ‖v‖²_{C²}` with `K` depending only on the coframe chart and the fixed
metrics (not on the cutoff). -/
theorem massSqP_tanOf_testRec_le (M : MassMetric 𝔄 𝓗) {Kl : ℝ} (hKl0 : 0 ≤ Kl) {Ke : Set M4}
    (hKl : ∀ e ∈ Ke, ∀ k : M4, ‖NativeGravityFirstJet.liftL e k‖ ≤ Kl * ‖k‖) {N : ℕ} [NeZero N]
    {y : Grid N → Field 𝔄 𝓗 𝓢} (hval : ∀ x, coframeM y x ∈ Ke)
    (hs : ∀ μ x, ‖(N : ℝ)⁻¹ • NativeDensity.gauge y μ x‖ < 1 / 32)
    (τ : DTest 𝔄 𝓗 𝓢 (CoSpinor 𝓢)) :
    massSqP M (N : ℝ)⁻¹ (tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)) ≤
      (Kl ^ 2 + 16 * ‖M.gm‖ + ‖M.hm‖ + 2) * τ.norm ^ 2 := by
  set t := τ.norm
  have ht0 : 0 ≤ t := τ.norm_nonneg
  set pt := fun x : Grid N => TorusCellEmbedding.samplePt x
  have hpt : ∀ x, ‖(tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).ε x‖ ^ 2 +
      ∑ μ, M.gm ((tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).α μ x)
        ((tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).α μ x) +
      M.hm ((tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).η x)
        ((tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).η x) +
      ‖(tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).ψ x‖ ^ 2 +
      ‖(tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).ψb x‖ ^ 2 ≤
      (Kl ^ 2 + 16 * ‖M.gm‖ + ‖M.hm‖ + 2) * t ^ 2 := by
    intro x
    -- the coframe component
    have hk : ‖τ.k.f (pt x)‖ ≤ t := (NativeSpinorVariation.norm_f_le' _ _).trans τ.k_le
    have hε : ‖(tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).ε x‖ ≤ Kl * t := by
      change ‖NativeGravityFirstJet.liftL (coframeM y x) (τ.k.f (pt x))‖ ≤ _
      exact (hKl _ (hval x) _).trans (mul_le_mul_of_nonneg_left hk hKl0)
    -- the gauge components
    have hα : ∀ μ, ‖(tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).α μ x‖ ≤ 2 * t := by
      intro μ
      change ‖jac (N : ℝ)⁻¹ y μ x (τ.a.f (pt x) μ)‖ ≤ _
      have ha : ‖τ.a.f (pt x) μ‖ ≤ t :=
        (norm_le_pi_norm _ μ).trans ((NativeSpinorVariation.norm_f_le' _ _).trans τ.a_le)
      exact ((jac (N : ℝ)⁻¹ y μ x).le_opNorm _).trans
        (mul_le_mul (norm_jac_le hs μ x) ha (norm_nonneg _) (by norm_num))
    have hg : ∀ μ, M.gm ((tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).α μ x)
        ((tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).α μ x) ≤ ‖M.gm‖ * (4 * t ^ 2) := by
      intro μ
      set a := (tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).α μ x
      calc M.gm a a ≤ ‖M.gm a a‖ := le_abs_self _
        _ ≤ ‖M.gm‖ * ‖a‖ * ‖a‖ := M.gm.le_opNorm₂ a a
        _ = ‖M.gm‖ * ‖a‖ ^ 2 := by ring
        _ ≤ ‖M.gm‖ * (2 * t) ^ 2 := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hα μ) 2) (ContinuousLinearMap.opNorm_nonneg _)
        _ = ‖M.gm‖ * (4 * t ^ 2) := by ring
    have hgs : ∑ μ, M.gm ((tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).α μ x)
        ((tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).α μ x) ≤ 16 * ‖M.gm‖ * t ^ 2 := by
      refine (Finset.sum_le_sum fun μ _ => hg μ).trans (le_of_eq ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    -- the matter components
    have hη : ‖(tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).η x‖ ≤ t :=
      (NativeSpinorVariation.norm_f_le' _ _).trans τ.η_le
    have hh : M.hm ((tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).η x)
        ((tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).η x) ≤ ‖M.hm‖ * t ^ 2 := by
      set a := (tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).η x
      calc M.hm a a ≤ ‖M.hm a a‖ := le_abs_self _
        _ ≤ ‖M.hm‖ * ‖a‖ * ‖a‖ := M.hm.le_opNorm₂ a a
        _ = ‖M.hm‖ * ‖a‖ ^ 2 := by ring
        _ ≤ ‖M.hm‖ * t ^ 2 := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) hη 2) (ContinuousLinearMap.opNorm_nonneg _)
    have hψ : ‖(tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).ψ x‖ ≤ t :=
      (NativeSpinorVariation.norm_f_le' _ _).trans τ.ψ_le
    have hψb : ‖(tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)).ψb x‖ ≤ t :=
      (NativeSpinorVariation.norm_f_le' _ _).trans τ.ψb_le
    have e1 := pow_le_pow_left₀ (norm_nonneg _) hε 2
    have e4 := pow_le_pow_left₀ (norm_nonneg _) hψ 2
    have e5 := pow_le_pow_left₀ (norm_nonneg _) hψb 2
    nlinarith [ContinuousLinearMap.opNorm_nonneg M.gm, ContinuousLinearMap.opNorm_nonneg M.hm]
  unfold massSqP
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  calc ((N : ℝ)⁻¹) ^ 4 * ∑ x, _ ≤ ((N : ℝ)⁻¹) ^ 4 *
        ∑ _x : Grid N, (Kl ^ 2 + 16 * ‖M.gm‖ + ‖M.hm‖ + 2) * t ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hpt x) (by positivity)
    _ = (Kl ^ 2 + 16 * ‖M.gm‖ + ‖M.hm‖ + 2) * t ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_grid]
        field_simp

end MassBound

/-! ### `(F5)` ⟹ native stationarity -/

section Stationarity

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [Nontrivial 𝔄] [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]

theorem covNormP_nonneg (C : CovData 𝔄 𝓗 𝓢) (M : MassMetric 𝔄 𝓗) {N : ℕ} [NeZero N] (h : ℝ)
    (c : LinkConfig N 𝔄 𝓗 𝓢) : 0 ≤ covNormP C M h c :=
  Real.sSup_nonneg fun _ ⟨_, _, hr⟩ => hr ▸ abs_nonneg _

/-- **`(F5)` controls the native first variation on the test lift**: on the chart (nondegenerate
coframes in `K_e`, Cartan and gauge plaquettes in the logarithm chart, `‖hA‖ < 1/32`), with `K`
depending only on `K_e` and the fixed metrics,
`|D S_h^{loc}(y)[𝓘_h v]| ≤ σ_h^{link}(y) · √K ‖v‖_{C²}`. -/
theorem abs_nativeVar_testRec_le (C : CovData 𝔄 𝓗 𝓢) (M : MassMetric 𝔄 𝓗) {Kl : ℝ}
    (hKl0 : 0 ≤ Kl) {Ke : Set M4}
    (hKl : ∀ e ∈ Ke, ∀ k : M4, ‖NativeGravityFirstJet.liftL e k‖ ≤ Kl * ‖k‖) {N : ℕ} [NeZero N]
    {y : Grid N → Field 𝔄 𝓗 𝓢} (hval : ∀ x, coframeM y x ∈ Ke)
    (hs : ∀ μ x, ‖(N : ℝ)⁻¹ • NativeDensity.gauge y μ x‖ < 1 / 32)
    (hd : DifferentiableAt ℝ (localAction C.toData (N : ℝ)⁻¹) y)
    (τ : DTest 𝔄 𝓗 𝓢 (CoSpinor 𝓢)) :
    |NativeAllSector.nativeVar C.toData N y (testRec (κid 𝓢) N y τ)| ≤
      covNormP C M (N : ℝ)⁻¹ (toLinks (N : ℝ)⁻¹ y) *
        (Real.sqrt (Kl ^ 2 + 16 * ‖M.gm‖ + ‖M.hm‖ + 2) * τ.norm) := by
  have hN : (N : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne N))
  have e : NativeAllSector.nativeVar C.toData N y (testRec (κid 𝓢) N y τ) =
      linkCov C (N : ℝ)⁻¹ (toLinks (N : ℝ)⁻¹ y)
        (tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)) :=
    nativeVar_eq_linkCov C hs hd _
  rw [e]
  refine (abs_linkCov_le C M hN hs hd _).trans (mul_le_mul_of_nonneg_left ?_
    (covNormP_nonneg C M _ _))
  have hm := massSqP_tanOf_testRec_le M hKl0 hKl hval hs τ
  calc Real.sqrt (massSqP M (N : ℝ)⁻¹ (tanOf (N : ℝ)⁻¹ y (testRec (κid 𝓢) N y τ)))
      ≤ Real.sqrt ((Kl ^ 2 + 16 * ‖M.gm‖ + ‖M.hm‖ + 2) * τ.norm ^ 2) := Real.sqrt_le_sqrt hm
    _ = Real.sqrt (Kl ^ 2 + 16 * ‖M.gm‖ + ‖M.hm‖ + 2) * τ.norm := by
        rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq τ.norm_nonneg]

/-- **`prop:equivariant-native-budgets`, stationarity clause** (`eq:eq-native-stationarity`,
Cauchy–Schwarz form): on the scaled logarithm chart, for every logarithmic-coordinate nodal test
lift `v` (in particular the covariant cell-average lift, whose mass norm is at most the `L²` norm
of the continuum test, `CovariantQuadrature.cellAverage_sq_sum_le`),
`|D S_h^{loc}(y)[v]| ≤ σ_h^{link}(y) · √K · ‖v‖_{0,h}` with `K = 1 + 4‖g_m‖ + ‖h_m‖` independent of
the cutoff and of the record. -/
theorem native_stationarity_budget (C : CovData 𝔄 𝓗 𝓢) (M : MassMetric 𝔄 𝓗) {N : ℕ} [NeZero N]
    {y : Grid N → Field 𝔄 𝓗 𝓢}
    (hs : ∀ μ x, ‖(N : ℝ)⁻¹ • NativeDensity.gauge y μ x‖ < 1 / 32)
    (hd : DifferentiableAt ℝ (localAction C.toData (N : ℝ)⁻¹) y) (v : Grid N → Field 𝔄 𝓗 𝓢) :
    |NativeAllSector.nativeVar C.toData N y v| ≤
      covNormP C M (N : ℝ)⁻¹ (toLinks (N : ℝ)⁻¹ y) *
        (Real.sqrt (1 + 4 * ‖M.gm‖ + ‖M.hm‖) * Real.sqrt (nodalL2Sq (N : ℝ)⁻¹ v)) :=
  abs_deriv_localAction_le C M hs hd v

end Stationarity

/-! ### Unitary links -/

section Unitary

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [Nontrivial 𝔄] [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]

theorem exp_neg_eq_star {a : 𝔄} (ha : exp a ∈ unitary 𝔄) : exp (-a) = star (exp a) := by
  calc exp (-a) = (star (exp a) * exp a) * exp (-a) := by
        rw [Unitary.star_mul_self_of_mem ha, one_mul]
    _ = star (exp a) := by rw [mul_assoc, NativeDensity.exp_mul_exp_neg, mul_one]

/-- The adjoint action of unitary links is isometric. -/
theorem adUnit_of_links {N : ℕ} [NeZero N] {y : Grid N → Field 𝔄 𝓗 𝓢}
    {U : Grid N × Fin 4 → unitary 𝔄}
    (hUe : ∀ x μ, (U (x, μ) : 𝔄) = exp ((N : ℝ)⁻¹ • NativeDensity.gauge y μ x))
    (x : Grid N) (μ : Fin 4) (X : 𝔄) :
    ‖exp ((N : ℝ)⁻¹ • NativeDensity.gauge y μ x) * X *
      exp (-((N : ℝ)⁻¹ • NativeDensity.gauge y μ x))‖ = ‖X‖ := by
  have hu : exp ((N : ℝ)⁻¹ • NativeDensity.gauge y μ x) ∈ unitary 𝔄 := by
    rw [← hUe]; exact (U (x, μ)).2
  rw [exp_neg_eq_star hu, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hu),
    CStarRing.norm_mem_unitary_mul _ hu]

theorem toUnits_mem {C₀ : CovData 𝔄 𝓗 𝓢} (hG : unitaryUnits 𝔄 ≤ C₀.G) (u : unitary 𝔄) :
    Unitary.toUnits u ∈ C₀.G :=
  hG ⟨u, rfl⟩

/-- The unitary group acts in the gauge group (gauge group `⊇ U(𝔄)`). -/
theorem top_in_G {C₀ : CovData 𝔄 𝓗 𝓢} (hG : unitaryUnits 𝔄 ≤ C₀.G) :
    ∀ u ∈ (⊤ : Subgroup (unitary 𝔄)), Unitary.toUnits u ∈ C₀.G :=
  fun u _ => toUnits_mem hG u

/-- Unitary links act isometrically on the Higgs fibre. -/
theorem higgsUnit_of_links (C₀ : CovData 𝔄 𝓗 𝓢) (K : Subgroup (unitary 𝔄))
    (hG : ∀ u ∈ K, Unitary.toUnits u ∈ C₀.G)
    (hρH : ∀ k ∈ C₀.G, ∀ v : 𝓗, ‖C₀.ρH k v‖ = ‖v‖) {N : ℕ} [NeZero N]
    {y : Grid N → Field 𝔄 𝓗 𝓢} {U : Grid N × Fin 4 → unitary 𝔄}
    (hUe : ∀ x μ, (U (x, μ) : 𝔄) = exp ((N : ℝ)⁻¹ • NativeDensity.gauge y μ x))
    (hUK : ∀ e, U e ∈ K)
    (x : Grid N) (μ : Fin 4) (v : 𝓗) :
    ‖exp ((N : ℝ)⁻¹ • C₀.ρHL (NativeDensity.gauge y μ x)) v‖ = ‖v‖ := by
  rw [FiniteWilsonTransfer.rhoH_exp, ← hUe]
  exact hρH _ (hG _ (hUK (x, μ))) v

/-- Unitary links act isometrically on spinors. -/
theorem spinUnit_of_links (C₀ : CovData 𝔄 𝓗 𝓢) (K : Subgroup (unitary 𝔄))
    (hG : ∀ u ∈ K, Unitary.toUnits u ∈ C₀.G) {N : ℕ} [NeZero N]
    {y : Grid N → Field 𝔄 𝓗 𝓢} {U : Grid N × Fin 4 → unitary 𝔄}
    (hUe : ∀ x μ, (U (x, μ) : 𝔄) = exp ((N : ℝ)⁻¹ • NativeDensity.gauge y μ x))
    (hUK : ∀ e, U e ∈ K)
    (x : Grid N) (μ : Fin 4) (v : 𝓢) :
    ‖C₀.ρS (exp ((N : ℝ)⁻¹ • NativeDensity.gauge y μ x)) v‖ = ‖v‖ := by
  rw [← hUe]
  exact C₀.ρS_isom _ (hG _ (hUK (x, μ))) v

/-- The literal plaquettes of unitary links are the plaquettes of the link configuration. -/
theorem plaq_eq_litPlaq {N : ℕ} [NeZero N] {y : Grid N → Field 𝔄 𝓗 𝓢}
    {U : Grid N × Fin 4 → unitary 𝔄}
    (hUe : ∀ x μ, (U (x, μ) : 𝔄) = exp ((N : ℝ)⁻¹ • NativeDensity.gauge y μ x))
    (x : Grid N) (μ ν : Fin 4) :
    plaq (toLinks (N : ℝ)⁻¹ y) x μ ν = RootedCoulomb.litPlaq U μ ν x := by
  have hinv : ∀ z κ, Ring.inverse (exp ((N : ℝ)⁻¹ • NativeDensity.gauge y κ z)) =
      star (U (z, κ) : 𝔄) := by
    intro z κ
    rw [ring_inverse_exp, hUe]
    exact exp_neg_eq_star (by rw [← hUe]; exact (U (z, κ)).2)
  simp only [plaq, toLinks, RootedCoulomb.litPlaq, hinv, hUe]
  rfl

end Unitary

/-! ### The criterion -/

section Main

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

open TorusPiecewiseConstantTranslation KolmogorovRieszTorus
open NativeHiggsVar NativeDiracConvergence FiniteWilsonZeroDefect
open NativeDiracConv (CoHyp qM ωM)
open NativeSpinorGraph (spinGraph dualGraph)
open NativeDiracLimit (Dif)

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [Nontrivial 𝔄] [FiniteDimensional ℝ 𝔄]
variable {rH : ℕ} [NeZero rH]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {E E₀ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup E₀]
  [InnerProductSpace ℝ E₀] [Nontrivial E₀] [FiniteDimensional ℝ E₀]
variable {r r' : ℕ} [NeZero r] [NeZero r'] {J : ℕ}

local instance fact_one_le_two_fz : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩

/-- **The rooted Coulomb normalization property** of a gauge subgroup `K ⊆ U(𝔄)` (the Coulomb
clause of `prop:rooted-gauge-certificate` at mesh `h = 1/m`, unit side): for every `ε_* > 0` there
is a cutoff-independent `ε_c > 0` such that links with values in `K` whose rooted seed is
admissible, whose plaquettes are in the logarithm chart and whose rooted certificate is `≤ ε_c`
admit a site gauge with values in `K` putting them in exact discrete Coulomb gauge with
`‖A‖_{4,h} ≤ ε_*`, the normalized links lying in the logarithm chart.  Proved for `K = U(𝔄)`
(`rootedNorm_unitary`) and for `K = G_SM = S(U(3) × U(2))` (`rootedNorm_SM`). -/
def RootedNorm (K : Subgroup (unitary 𝔄)) (toE : 𝔄 ≃L[ℝ] E₀) : Prop :=
  ∀ εstar > 0, ∃ εc > 0, ∀ (m : ℕ) [NeZero m] (o : Grid m)
    (w : ∀ v, LatticeWalk (RootedCoulomb.latSrc (ι := Fin 4) (n := m)) RootedCoulomb.latTgt v o)
    (U : Grid m × Fin 4 → unitary 𝔄), (∀ e, U e ∈ K) →
    (∀ μ x, ‖((RootedWilson.rootedWord w U (x, μ) : unitary 𝔄) : 𝔄) - 1‖ ≤ 1 / 64) →
    (∀ μ ν x, ‖RootedCoulomb.litPlaq U μ ν x - 1‖ < 1) →
    CoulombApriori.oneL4 (m : ℝ)⁻¹ (toE : 𝔄 →L[ℝ] E₀) (RootedCoulomb.treeSeed (m : ℝ)⁻¹ w U) +
      RootedCoulomb.litCurvL2 toE (m : ℝ)⁻¹ U ≤ εc →
    ∃ g : Grid m → unitary 𝔄, (∀ x, g x ∈ K) ∧
      (∀ μ x, ‖((gaugeLinks RootedCoulomb.latSrc RootedCoulomb.latTgt g U (x, μ) :
        unitary 𝔄) : 𝔄) - 1‖ < 1) ∧
      periodicHodgeCodiff (m : ℝ)⁻¹ GridSobolev.gridStep
        (CoulombApriori.bar (toE : 𝔄 →L[ℝ] E₀) (fun μ x => ((m : ℝ)⁻¹)⁻¹ •
          SeriesLogChart.logChart ((gaugeLinks RootedCoulomb.latSrc RootedCoulomb.latTgt g U
            (x, μ) : unitary 𝔄) : 𝔄))) = 0 ∧
      CoulombApriori.oneL4 (m : ℝ)⁻¹ (toE : 𝔄 →L[ℝ] E₀) (fun μ x => ((m : ℝ)⁻¹)⁻¹ •
          SeriesLogChart.logChart ((gaugeLinks RootedCoulomb.latSrc RootedCoulomb.latTgt g U
            (x, μ) : unitary 𝔄) : 𝔄)) ≤ εstar

/-- **The rooted normalization property for the full unitary group** (from
`NativeRecordNorm.rooted_coulomb_normalization_chart`). -/
theorem rootedNorm_unitary (toE : 𝔄 ≃L[ℝ] E₀)
    (hM1 : ∀ V ∈ unitary 𝔄, ∀ X, ‖toE (V * X * star V)‖ = ‖toE X‖)
    (hM2 : ∀ a : 𝔄, star a = -a → ∀ u, inner ℝ (toE a) (toE (a * u - u * a)) = 0) :
    RootedNorm ⊤ toE := by
  intro εstar hεstar
  obtain ⟨εc, Cc, hεc, -, H⟩ :=
    NativeRecordNorm.rooted_coulomb_normalization_chart toE (ι := Fin 4) (by simp) hM1 hM2
      one_pos hεstar
  refine ⟨εc, hεc, fun m _ o w U _ hadm hplaq hcert => ?_⟩
  have hpos : (0 : ℝ) < (m : ℝ)⁻¹ :=
    inv_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m))
  obtain ⟨g, hch, -, hcod, -, hsm⟩ := H m (m : ℝ)⁻¹ hpos
    (mul_inv_cancel₀ (inv_pos.1 hpos).ne') o w U hadm hplaq hcert
  exact ⟨g, fun _ => Subgroup.mem_top _, hch, hcod, hsm⟩

/-- The normalized links are the rooted-gauge transforms of the internal links. -/
theorem gaugeAct_toLinks_U (C₀ : CovData 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢) {N : ℕ} [NeZero N]
    {y : Grid N → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢} {U : Grid N × Fin 4 → unitary 𝔄}
    (hUe : ∀ x μ, (U (x, μ) : 𝔄) = exp ((N : ℝ)⁻¹ • NativeDensity.gauge y μ x))
    (gU : Grid N → unitary 𝔄) (μ : Fin 4) (x : Grid N) :
    (gaugeAct C₀ (fun x => Unitary.toUnits (gU x)) (toLinks (N : ℝ)⁻¹ y)).U μ x =
      ((gaugeLinks RootedCoulomb.latSrc RootedCoulomb.latTgt gU U (x, μ) : unitary 𝔄) : 𝔄) := by
  change ((gU x : unitary 𝔄) : 𝔄) * exp ((N : ℝ)⁻¹ • NativeDensity.gauge y μ x) *
      star ((gU (x + unitVec N μ) : unitary 𝔄) : 𝔄) = _
  rw [gaugeLinks_apply, ← hUe]
  rfl

theorem isGaugeTransform_bankCov (C₀ : CovData 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (Tj : Fin J → 𝔄 →L[ℝ] E) (θ : Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢) (hT hY) {N : ℕ}
    [NeZero N] {h : ℝ} {g : Grid N → 𝔄ˣ} {y y' : Grid N → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢}
    (hy : IsGaugeTransform C₀ h g y y') :
    IsGaugeTransform (bankCov C₀ Tj θ hT hY) h g y y' :=
  ⟨hy.1, hy.2⟩

set_option maxHeartbeats 6400000 in
-- the normalization, the transfer of the hypotheses and the criterion
/-- **`thm:finite-Wilson-zero-defect`** (unit-torus rendering, mesh `h = 1/N`; gauge group the
unitary group of a finite-dimensional C*-algebra `𝔄` with invariant metric `toE`; Higgs fibre
`ℝ^{r_H}`; fixed covariant representation packet `C₀`, coefficient banks over the
`Ad`-invariant component metrics `T_j`).  There are cutoff-independent thresholds `ε_c, ε_* > 0`
such that, for native records `y_h` whose internal links `U_h = e^{hA_h}` are unitary, under
* `(F2)`: for one predeclared rooted family of tree paths, the rooted seed is admissible, the
  plaquettes are in the logarithm chart and the same-record certificate
  `‖B^𝔗‖_{4,h} + ‖𝔽_h(U)‖_{2,h} ≤ ε_c` (`eq:rooted-Wilson-certificate`);
* `(F1)`: coframes in one compact oriented chart, the scaled connection margin `c_* ≤ 1/64`,
  `R⁰E_h`, `R⁰D⁺E_h` precompact in `L²`, reconstructed coframes in the same chart;
* `(F3)`: bounded literal packets `𝔽_h`, `𝕂_h`, `H_h` and vanishing Wilson screens
  `eq:two-finite-Wilson-screens`;
* `(F4)`: bounded positive internal-link spinor graphs `eq:native-spinor-graph`, coefficient banks
  in a compact physical parameter set (covariant Yukawa banks);
* `(F5)`: the norm `σ_h^{phys}` of the complete finite action covector in the positive physical
  link/matter mass metric (`NativeLinkCov.covNormP`, fixed coercive invariant metrics `M`) tends
  to zero,

there are site gauges `g_h` (unitary) acting on the same finite records for which the normalized
logarithmic connections are in exact discrete Coulomb gauge (`δ_h A'_h = 0`,
`‖A'_h‖_{4,h} ≤ ε_*`), and, after extraction, `eq:Wilson-strong-convergence` holds
(`e_h → e` strongly in `H¹`, `A'_h → A` in `L⁴` with `D⁺A'_h → ∂A` in `L²`, `F_{A'_h} → F_A`,
`H'_h → H` in `L⁴` with `R⁰D⁺H'_h → K - ρ_H(A)H`, `R⁰𝕂'_h → K = D_AH`, spinors weakly in `H¹`),
the complete first variations converge to the classical one (`eq:native-all-sector-limit`) and
are consistent with the unfiltered reconstructed fields, **every limit satisfies the
distributional Einstein–Standard-Model equations**, and the bosonic stress densities converge
strongly in `L¹`.  (The complete fermionic metric variation with cutoff banks is
`FiniteWilsonZeroDefect.native_fermion_variation_bank`.) -/
theorem finite_wilson_zero_defect_of_rootedNorm (C₀ : CovData 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (K : Subgroup (unitary 𝔄)) (hG : ∀ u ∈ K, Unitary.toUnits u ∈ C₀.G)
    (hρH : ∀ k ∈ C₀.G, ∀ v : EuclideanSpace ℝ (Fin rH), ‖C₀.ρH k v‖ = ‖v‖)
    (Tj : Fin J → 𝔄 →L[ℝ] E)
    (hT : ∀ g ∈ C₀.G, ∀ j (X Y : 𝔄),
      ⟪Tj j ((g : 𝔄) * X * ↑g⁻¹), Tj j ((g : 𝔄) * Y * ↑g⁻¹)⟫ = ⟪Tj j X, Tj j Y⟫)
    (toE : 𝔄 ≃L[ℝ] E₀) (HN : RootedNorm K toE)
    (M : MassMetric 𝔄 (EuclideanSpace ℝ (Fin rH))) (hM : M.Invariant C₀)
    (Θ : 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (Θ' : CoSpinor 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r')) :
    ∃ εc > 0, ∃ εstar > 0, ∀ (n : ℕ → ℕ) [∀ k, NeZero (n k)]
      (y : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
      (θs : ℕ → Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢), Tendsto n atTop atTop →
      -- the unitary internal links of the records and `(F2)`
      ∀ (U : ∀ k, Grid (n k) × Fin 4 → unitary 𝔄)
        (hUe : ∀ k x μ, (U k (x, μ) : 𝔄) = exp ((n k : ℝ)⁻¹ • NativeDensity.gauge (y k) μ x))
        (hUK : ∀ k e, U k e ∈ K) (o : ∀ k, Grid (n k))
        (w : ∀ k, ∀ v, LatticeWalk (RootedCoulomb.latSrc (ι := Fin 4) (n := n k))
          RootedCoulomb.latTgt v (o k)),
      (∀ k μ x, ‖((RootedWilson.rootedWord (w k) (U k) (x, μ) : unitary 𝔄) : 𝔄) - 1‖ ≤ 1 / 64) →
      (∀ k μ ν x, ‖RootedCoulomb.litPlaq (U k) μ ν x - 1‖ < 1) →
      (∀ k, CoulombApriori.oneL4 (n k : ℝ)⁻¹ (toE : 𝔄 →L[ℝ] E₀)
          (RootedCoulomb.treeSeed (n k : ℝ)⁻¹ (w k) (U k)) +
        RootedCoulomb.litCurvL2 toE (n k : ℝ)⁻¹ (U k) ≤ εc) →
      -- `(F1)`
      ∀ (Ke : Set M4), IsCompact Ke → (∀ M ∈ Ke, 0 < Matrix.det (show Mat from M)) →
      (∀ k x, coframeM (y k) x ∈ Ke) → ∀ cm : ℝ, cm ≤ 1 / 64 →
      (∀ k x μ, (n k : ℝ)⁻¹ * ‖ωM (y k) μ x‖ ≤ cm) →
      TotallyBounded (range fun k => pcLp (coframeM (y k))) →
      TotallyBounded (range fun k => pcLp (fun x lam => qM (y k) lam x)) →
      (∀ k z, NativeTrigRec.recon (coframeM (y k)) z ∈ Ke) →
      -- `(F3)`
      (∃ B, ∀ k, gridNorm (curvPacket (n k) (y k)) ≤ B) →
      (∃ B, ∀ k, gridNorm (higgsPacket C₀.toData (n k) (y k)) ≤ B) →
      ∀ BH : ℝ, (∀ k, gridNorm (higgs (y k)) ≤ BH) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (adLinks (n k) (y k) (adUnit_of_links (hUe k))) μ m
          (curvPacket (n k) (y k)) - curvPacket (n k) (y k)) ≤ ε) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (higgsLinks C₀.toData (n k) (y k)
            (higgsUnit_of_links C₀ K hG hρH (hUe k) (hUK k))) μ m
          (higgsPacket C₀.toData (n k) (y k)) - higgsPacket C₀.toData (n k) (y k)) ≤ ε) →
      -- `(F4)`
      ∀ B : ℝ, (∀ k, gridNorm (psi (y k)) ≤ B) →
      (∀ k μ, gridNorm (fun x => spinGraph C₀.toData (n k : ℝ)⁻¹ (y k) x μ) ≤ B) →
      (∀ k, gridNorm (psiBar (y k)) ≤ B) →
      (∀ k μ, gridNorm (fun x => dualGraph C₀.toData (n k : ℝ)⁻¹ (y k) x μ) ≤ B) →
      ∀ (Kθ : Set (ℝ × ℝ × ℝ × ℝ × (Fin J → ℝ) ×
          (EuclideanSpace ℝ (Fin rH) →L[ℝ] Spin 𝓢))), IsCompact Kθ →
      (∀ k, bankVec (θs k) ∈ Kθ) → (∀ v ∈ Kθ, v.1 ≠ 0 ∧ ∀ j, 0 ≤ v.2.2.2.2.1 j) →
      ∀ (hY : ∀ k, ∀ g ∈ C₀.G, ∀ H : EuclideanSpace ℝ (Fin rH),
        (θs k).Y (C₀.ρH g H) = C₀.ρS g * (θs k).Y H * C₀.ρS ↑g⁻¹),
      -- `(F5)`
      Tendsto (fun k => covNormP (bankCov C₀ Tj (θs k) hT (hY k)) M (n k : ℝ)⁻¹
        (toLinks (n k : ℝ)⁻¹ (y k))) atTop (𝓝 0) →
      ∃ g : ∀ k, Grid (n k) → 𝔄ˣ, ∃ y' : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢,
      (∀ k x, ∃ u ∈ K, g k x = Unitary.toUnits u) ∧
      (∀ k, y' k = gaugeRecord C₀ (n k : ℝ)⁻¹ (g k) (y k)) ∧
      (∀ k, IsGaugeTransform C₀ (n k : ℝ)⁻¹ (g k) (y k) (y' k)) ∧
      -- exact discrete Coulomb gauge
      (∀ k, NativeCoulomb.codiffT (toE : 𝔄 →L[ℝ] E₀) (NativeYMBridge.gaugeArr (y' k)) = 0) ∧
      (∀ k μ, NativeCoulomb.g4 (fun x => toE (NativeDensity.gauge (y' k) μ x)) ≤ εstar) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ H : CoHyp (fun k => n (φ k)) (fun k => y' (φ k)),
      H.Ke = Ke ∧
      ∃ θ : Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢, BankConv (fun k => θs (φ k)) θ ∧
      ∃ F : Fin 4 → Fin 4 → 𝕋 → 𝔄, ∃ G : Fin 4 → Fin 4 → 𝕋 → 𝔄,
      ∃ P : HiggsHyp (bankData C₀.toData Tj θ) (fun k => y' (φ k)),
      ∃ S : SpinHyp (κid 𝓢) (fun k => y' (φ k)), ∃ u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢),
      -- `eq:Wilson-strong-convergence`
      (∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
        NativeScaling.fieldStrength (n (φ k) : ℝ)⁻¹ (NativeDensity.gauge (y' (φ k))) x μ ν))
        (F μ ν)) ∧
      (∀ μ ν, LpTendsto volume 2
        (fun k => pc (NativeHiggs.DpV μ (NativeDensity.gauge (y' (φ k)) ν))) (G μ ν)) ∧
      (∀ μ ν, F μ ν =ᵐ[MeasureTheory.volume] NativeReconstructed.recCurv H.A₀ G μ ν) ∧
      (∀ μ, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (higgs (y' (φ k)))))
        (fun z => P.K₀ μ z - C₀.ρHL (H.A₀ μ z) (P.H₀ z))) ∧
      (∀ j, ∃ fj : Lp ℂ 2 (MeasureTheory.volume : Measure 𝕋),
        ((fj : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ (S.Ψ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 fj ∧ ∀ μ, (TorusSobolev.weakDeriv μ fj : 𝕋 → ℂ)
          =ᵐ[MeasureTheory.volume] fun z => ((Θ ((u₀ z).1 μ) j : ℝ) : ℂ)) ∧
      -- `eq:native-all-sector-limit` with the cutoff banks
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData C₀.toData Tj (θs (φ k))) (n (φ k)) (y' (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y' (φ k)) τ) -
          NativeAllSector.contAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀
            τ| ≤ ε) ∧
      -- consistency relative to the reconstructed fields
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData C₀.toData Tj (θs (φ k))) (n (φ k)) (y' (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y' (φ k)) τ) -
          NativeReconstructed.recAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w)
            (NativeTrigRec.recon (coframeM (y' (φ k))))
            (fun lam => NativeTrigRec.drecon lam (coframeM (y' (φ k))))
            (fun μ => NativeTrigRec.recon (NativeDensity.gauge (y' (φ k)) μ))
            (fun μ ν => NativeTrigRec.drecon μ (NativeDensity.gauge (y' (φ k)) ν))
            (NativeTrigRec.recon (higgs (y' (φ k))))
            (fun μ => NativeTrigRec.drecon μ (higgs (y' (φ k))))
            (NativeTrigRec.recon (psi (y' (φ k)))) (NativeTrigRec.recon (psiBar (y' (φ k))))
            (NativeTrigRec.recJets (y' (φ k))) τ| ≤ ε) ∧
      -- the distributional Einstein–Standard-Model equations
      (∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
        NativeAllSector.contAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀ τ
          = 0) ∧
      -- the bosonic stress densities
      (∀ (ΘF : M4 → (Fin 4 → Fin 4 → 𝔄) →L[ℝ] (Fin 4 → Fin 4 → 𝔄) →L[ℝ] ℝ)
        (ΘK : M4 → (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ]
          (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ] ℝ) (ΘV : M4 → ℝ),
        ContinuousOn ΘF Ke → ContinuousOn ΘK Ke → ContinuousOn ΘV Ke →
        LpTendsto volume 1
          (fun k z => ΘF (pc (coframeM (y' (φ k))) z) (pc (curvPacket (n (φ k)) (y' (φ k))) z)
              (pc (curvPacket (n (φ k)) (y' (φ k))) z) +
            ΘK (pc (coframeM (y' (φ k))) z)
              (pc (higgsPacket C₀.toData (n (φ k)) (y' (φ k))) z)
              (pc (higgsPacket C₀.toData (n (φ k)) (y' (φ k))) z) +
            ΘV (pc (coframeM (y' (φ k))) z) *
              potential (bankData C₀.toData Tj (θs (φ k))) (pc (higgs (y' (φ k))) z))
          (fun z => ΘF (H.e₀ z) (fun μ ν => F μ ν z) (fun μ ν => F μ ν z) +
            ΘK (H.e₀ z) (fun μ => P.K₀ μ z) (fun μ => P.K₀ μ z) +
            ΘV (H.e₀ z) * potential (bankData C₀.toData Tj θ) (P.H₀ z))) := by
  -- constants
  set c₀ : ℝ := ‖(toE.symm : E₀ →L[ℝ] 𝔄)‖ with hc₀def
  have hc0 : 0 ≤ c₀ := norm_nonneg _
  have hc : ∀ X : 𝔄, ‖X‖ ≤ c₀ * ‖(toE : 𝔄 →L[ℝ] E₀) X‖ := FiniteCoulomb.norm_le_symm toE
  obtain ⟨ε₀, hε₀, hcrit⟩ := finite_wilson_criterion (J := J) C₀.toData Tj
    (toE : 𝔄 →L[ℝ] E₀) hc0 hc Θ Θ'
  set ε₁ : ℝ := min ε₀ (1 / (128 * (c₀ + 1))) with hε₁def
  have hε₁ : 0 < ε₁ := lt_min hε₀ (by positivity)
  have hε₁₀ : ε₁ ≤ ε₀ := min_le_left _ _
  have h128 : 128 * c₀ * ε₁ ≤ 1 := by
    have h1 : ε₁ ≤ 1 / (128 * (c₀ + 1)) := min_le_right _ _
    have h2 : 128 * c₀ * ε₁ ≤ 128 * c₀ * (1 / (128 * (c₀ + 1))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    refine h2.trans ?_
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  obtain ⟨εc, hεc, hroot⟩ := HN ε₁ hε₁
  refine ⟨εc, hεc, ε₁, hε₁, fun n _ y θs hn U hUe hUK o w hadm hplaq hcert Ke hKe hpos hval cm hcm
    hmar hTBe hTBq hrec hFb hKb BH hHb hΩF hΩK B hΨ hKs hΨb hKbd Kθ hKθ hθK hphys hY hF5 => ?_⟩
  have hNpos : ∀ k, (0 : ℝ) < (n k : ℝ)⁻¹ := fun k =>
    inv_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k)))
  -- the normalizing site gauges
  choose gU hgU using fun k => hroot (n k) (o k) (w k) (U k) (hUK k) (hadm k) (hplaq k)
    (hcert k)
  set g : ∀ k, Grid (n k) → 𝔄ˣ := fun k x => Unitary.toUnits (gU k x) with hgdef
  set y' : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 :=
    fun k => gaugeRecord C₀ (n k : ℝ)⁻¹ (g k) (y k) with hy'def
  have hgG : ∀ k x, g k x ∈ C₀.G := fun k x => hG _ ((hgU k).1 x)
  have hUA : ∀ k μ x, (gaugeAct C₀ (g k) (toLinks (n k : ℝ)⁻¹ (y k))).U μ x =
      ((gaugeLinks RootedCoulomb.latSrc RootedCoulomb.latTgt (gU k) (U k) (x, μ) :
        unitary 𝔄) : 𝔄) :=
    fun k μ x => gaugeAct_toLinks_U C₀ (hUe k) (gU k) μ x
  have hIG : ∀ k, IsGaugeTransform C₀ (n k : ℝ)⁻¹ (g k) (y k) (y' k) := fun k =>
    ⟨hgG k, toLinks_gaugeRecord C₀ (hNpos k).ne' (g k) (y k) fun x μ => by
      rw [hUA]; exact (hgU k).2.1 μ x⟩
  have hgauge : ∀ k μ x, NativeDensity.gauge (y' k) μ x = ((n k : ℝ)⁻¹)⁻¹ •
      SeriesLogChart.logChart ((gaugeLinks RootedCoulomb.latSrc RootedCoulomb.latTgt (gU k) (U k)
        (x, μ) : unitary 𝔄) : 𝔄) := fun k μ x => by
    rw [← hUA]; rfl
  -- exact discrete Coulomb gauge
  have hcod : ∀ k, NativeCoulomb.codiffT (toE : 𝔄 →L[ℝ] E₀)
      (NativeYMBridge.gaugeArr (y' k)) = 0 := by
    intro k
    have h := (hgU k).2.2.1
    unfold NativeCoulomb.codiffT
    convert h using 2
    funext μ x
    change toE (NativeDensity.gauge (y' k) μ x) = _
    rw [hgauge]
    rfl
  have hsm : ∀ k μ, NativeCoulomb.g4 (fun x => toE (NativeDensity.gauge (y' k) μ x)) ≤ ε₁ := by
    intro k μ
    have h := (CoulombApriori.gridL4_le_oneL4 (hNpos k).le (toE : 𝔄 →L[ℝ] E₀) _ μ).trans
      (hgU k).2.2.2
    refine (le_of_eq ?_).trans h
    unfold NativeCoulomb.g4
    congr 1
    funext x
    change toE (NativeDensity.gauge (y' k) μ x) = _
    rw [hgauge]
    rfl
  -- transfer of `(F1)`
  have hcf : ∀ k, coframe (y' k) = coframe (y k) := fun k =>
    FiniteWilsonTransfer.coframe_eq C₀ (hIG k)
  have hcfM : ∀ k, coframeM (y' k) = coframeM (y k) := fun k => by
    unfold coframeM; rw [hcf k]
  have hωM : ∀ k μ x, ωM (y' k) μ x = ωM (y k) μ x := fun k μ x => by
    unfold ωM; rw [hcf k]
  have hqM : ∀ k lam x, qM (y' k) lam x = qM (y k) lam x := fun k lam x => by
    unfold qM; rw [hcf k]
  have hval' : ∀ k x, coframeM (y' k) x ∈ Ke := fun k x => by rw [hcfM]; exact hval k x
  -- the plaquette chart of the original links
  have hP : ∀ k x μ ν, ‖plaq (toLinks (n k : ℝ)⁻¹ (y k)) x μ ν - 1‖ < 1 := fun k x μ ν => by
    rw [plaq_eq_litPlaq (hUe k)]; exact hplaq k μ ν x
  -- unitarity of the normalized links
  have hAd' := fun k => FiniteWilsonTransfer.adUnit_gauge C₀ (hIG k) (adUnit_of_links (hUe k))
  have hUH' := fun k => FiniteWilsonTransfer.higgsUnit_gauge C₀ hρH (hIG k)
    (higgsUnit_of_links C₀ K hG hρH (hUe k) (hUK k))
  have hU' := fun k => FiniteWilsonTransfer.spinUnit_gauge C₀ (hIG k)
    (spinUnit_of_links C₀ K hG (hUe k) (hUK k))
  -- transfer of `(F3)`, `(F4)`
  obtain ⟨BF, hBF⟩ := hFb
  obtain ⟨BK, hBK⟩ := hKb
  have hFb' : ∃ B, ∀ k, gridNorm (curvPacket (n k) (y' k)) ≤ B := ⟨BF, fun k => by
    rw [FiniteWilsonTransfer.gridNorm_curvPacket_gauge C₀ (hIG k) (hP k)]; exact hBF k⟩
  have hKb' : ∃ B, ∀ k, gridNorm (higgsPacket C₀.toData (n k) (y' k)) ≤ B := ⟨BK, fun k => by
    rw [FiniteWilsonTransfer.gridNorm_higgsPacket_gauge C₀ hρH (hIG k)]; exact hBK k⟩
  have hHb' : ∀ k, gridNorm (higgs (y' k)) ≤ BH := fun k => by
    rw [FiniteWilsonTransfer.gridNorm_higgs_gauge C₀ hρH (hIG k)]; exact hHb k
  have hΩF' : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m →
      (m : ℝ) / n k ≤ ρ → gridNorm (wilsonShiftR (adLinks (n k) (y' k) (hAd' k)) μ m
        (curvPacket (n k) (y' k)) - curvPacket (n k) (y' k)) ≤ ε := by
    intro ε hε
    obtain ⟨ρ, hρ, hev⟩ := hΩF ε hε
    refine ⟨ρ, hρ, hev.mono fun k hk μ m hm hmρ => ?_⟩
    rw [FiniteWilsonTransfer.gridNorm_wilson_curv_gauge C₀ (hIG k) (hP k)
      (adUnit_of_links (hUe k)) (hAd' k)]
    exact hk μ m hm hmρ
  have hΩK' : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m →
      (m : ℝ) / n k ≤ ρ → gridNorm (wilsonShiftR (higgsLinks C₀.toData (n k) (y' k) (hUH' k))
        μ m (higgsPacket C₀.toData (n k) (y' k)) - higgsPacket C₀.toData (n k) (y' k)) ≤ ε := by
    intro ε hε
    obtain ⟨ρ, hρ, hev⟩ := hΩK ε hε
    refine ⟨ρ, hρ, hev.mono fun k hk μ m hm hmρ => ?_⟩
    rw [FiniteWilsonTransfer.gridNorm_wilson_higgs_gauge C₀ hρH (hIG k)
      (higgsUnit_of_links C₀ K hG hρH (hUe k) (hUK k)) (hUH' k)]
    exact hk μ m hm hmρ
  have hΨ' : ∀ k, gridNorm (psi (y' k)) ≤ B := fun k => by
    rw [FiniteWilsonTransfer.gridNorm_psi_gauge C₀ (hIG k)]; exact hΨ k
  have hKs' : ∀ k μ, gridNorm (fun x => spinGraph C₀.toData (n k : ℝ)⁻¹ (y' k) x μ) ≤ B :=
    fun k μ => by rw [FiniteWilsonTransfer.gridNorm_spinGraph_gauge C₀ (hIG k)]; exact hKs k μ
  have hΨb' : ∀ k, gridNorm (psiBar (y' k)) ≤ B := fun k => by
    rw [FiniteWilsonTransfer.gridNorm_psiBar_gauge C₀ (hIG k)]; exact hΨb k
  have hKbd' : ∀ k μ, gridNorm (fun x => dualGraph C₀.toData (n k : ℝ)⁻¹ (y' k) x μ) ≤ B :=
    fun k μ => by rw [FiniteWilsonTransfer.gridNorm_dualGraph_gauge C₀ (hIG k)]; exact hKbd k μ
  have hTBe' : TotallyBounded (range fun k => pcLp (coframeM (y' k))) := by
    simp only [hcfM]; exact hTBe
  have hTBq' : TotallyBounded (range fun k => pcLp (fun x lam => qM (y' k) lam x)) := by
    simp only [hqM]; exact hTBq
  have hrec' : ∀ k z, NativeTrigRec.recon (coframeM (y' k)) z ∈ Ke := fun k z => by
    rw [hcfM]; exact hrec k z
  -- the criterion on the normalized records
  obtain ⟨φ, hφ, H, hHK, θ, hθ, F, G, P, S, u₀, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ :=
    hcrit n y' θs hn hcod (fun k μ => (hsm k μ).trans hε₁₀) Ke hKe hpos hval' cm hcm
      (fun k x μ => by rw [hωM]; exact hmar k x μ) hTBe' hTBq' hAd' hUH' hFb' hKb' BH hHb'
      hΩF' hΩK' hU' B hΨ' hKs' hΨb' hKbd' Kθ hKθ hθK hphys hrec'
  -- `(F5)` ⟹ native stationarity
  obtain ⟨Kl, hKl0, hKl⟩ := exists_liftM_bound hKe
  have hs : ∀ k μ x, ‖(n k : ℝ)⁻¹ • NativeDensity.gauge (y' k) μ x‖ < 1 / 32 := by
    intro k μ x
    have h1 := mesh_small (toE : 𝔄 →L[ℝ] E₀) hc0 hc
      (fun μ x => NativeDensity.gauge (y' k) μ x) (hsm k) x μ
    rw [norm_smul, Real.norm_of_nonneg (hNpos k).le]
    have h2 : c₀ * ε₁ ≤ 1 / 128 := by nlinarith
    linarith
  have hd : ∀ k, DifferentiableAt ℝ
      (localAction (bankCov C₀ Tj (θs k) hT (hY k)).toData (n k : ℝ)⁻¹) (y' k) := by
    intro k
    refine NativeFrechet.differentiableAt_localAction _ (hNpos k).ne'
      (fun x => (hpos _ (hval' k x)).ne') (fun x μ ν _ => ?_) (fun x μ ν _ => ?_)
    · refine NativeGravityFirstJet.cartan_log_lt (hNpos k) hcm (coframe (y' k))
        (fun x μ => ?_) x μ ν
      have := hmar k x μ
      rw [← hωM] at this
      exact this
    · have hch : ((n k : ℝ))⁻¹ * LogBCH.normSum
          (NativeYMIdentification.slots (NativeYMBridge.gaugeArr (y' k)) x μ ν) ≤ 1 / 32 :=
        NativeCoulomb.chart_of_small (toE : 𝔄 →L[ℝ] E₀) hc0 hc h128
          (NativeYMBridge.gaugeArr (y' k)) (hsm k) x μ ν
      exact NativeYMBridge.gaugePlaquette_lt_of_chart (NativeDensity.gauge (y' k)) x μ ν hch
  have hstat : ∀ ε > 0, ∀ᶠ k in atTop,
      ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ 1 →
      |NativeAllSector.nativeVar (bankData C₀.toData Tj (θs k)) (n k) (y' k)
        (testRec (κid 𝓢) (n k) (y' k) τ)| ≤ ε := by
    intro ε hε
    set s := Real.sqrt (Kl ^ 2 + 16 * ‖M.gm‖ + ‖M.hm‖ + 2)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hev := hF5.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / (s + 1)))
    filter_upwards [hev] with k hk τ hτ
    have hb := abs_nativeVar_testRec_le (bankCov C₀ Tj (θs k) hT (hY k)) M hKl0 hKl (hval' k)
      (hs k) (hd k) τ
    rw [covNormP_record_gauge (bankCov C₀ Tj (θs k) hT (hY k)) M
      (massMetric_invariant_bankCov C₀ M hM Tj (θs k) hT (hY k))
      (isGaugeTransform_bankCov C₀ Tj (θs k) hT (hY k) (hIG k))
      (fun x μ ν _ => hP k x μ ν)] at hb
    have hc0' := covNormP_nonneg (bankCov C₀ Tj (θs k) hT (hY k)) M (N := n k) (n k : ℝ)⁻¹
      (toLinks (n k : ℝ)⁻¹ (y k))
    have hτ0 := τ.norm_nonneg
    calc _ ≤ _ := hb
      _ ≤ ε / (s + 1) * (s * 1) :=
          mul_le_mul hk.le (mul_le_mul_of_nonneg_left hτ hs0) (by positivity) (by positivity)
      _ ≤ ε := by
          rw [mul_one, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  exact ⟨g, y', fun k x => ⟨gU k x, (hgU k).1 x, rfl⟩, fun k => rfl, hIG, hcod, hsm, φ, hφ, H, hHK, θ, hθ,
    F, G, P, S, u₀, c1, c2, c3, c4, c5, c6, c7, c8 hstat, c9⟩


set_option maxHeartbeats 6400000 in
-- specialization of the general criterion
/-- **`thm:finite-Wilson-zero-defect` for the full unitary gauge group `U(𝔄)`** of a
finite-dimensional C*-algebra (`finite_wilson_zero_defect_of_rootedNorm` with
`rootedNorm_unitary`). -/
theorem finite_wilson_zero_defect (C₀ : CovData 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (hG : unitaryUnits 𝔄 ≤ C₀.G)
    (hρH : ∀ k ∈ C₀.G, ∀ v : EuclideanSpace ℝ (Fin rH), ‖C₀.ρH k v‖ = ‖v‖)
    (Tj : Fin J → 𝔄 →L[ℝ] E)
    (hT : ∀ g ∈ C₀.G, ∀ j (X Y : 𝔄),
      ⟪Tj j ((g : 𝔄) * X * ↑g⁻¹), Tj j ((g : 𝔄) * Y * ↑g⁻¹)⟫ = ⟪Tj j X, Tj j Y⟫)
    (toE : 𝔄 ≃L[ℝ] E₀) (hM1 : ∀ V ∈ unitary 𝔄, ∀ X, ‖toE (V * X * star V)‖ = ‖toE X‖)
    (hM2 : ∀ a : 𝔄, star a = -a → ∀ u, inner ℝ (toE a) (toE (a * u - u * a)) = 0)
    (M : MassMetric 𝔄 (EuclideanSpace ℝ (Fin rH))) (hM : M.Invariant C₀)
    (Θ : 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (Θ' : CoSpinor 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r')) :
    ∃ εc > 0, ∃ εstar > 0, ∀ (n : ℕ → ℕ) [∀ k, NeZero (n k)]
      (y : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
      (θs : ℕ → Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢), Tendsto n atTop atTop →
      -- the unitary internal links of the records and `(F2)`
      ∀ (U : ∀ k, Grid (n k) × Fin 4 → unitary 𝔄)
        (hUe : ∀ k x μ, (U k (x, μ) : 𝔄) = exp ((n k : ℝ)⁻¹ • NativeDensity.gauge (y k) μ x))
        (o : ∀ k, Grid (n k))
        (w : ∀ k, ∀ v, LatticeWalk (RootedCoulomb.latSrc (ι := Fin 4) (n := n k))
          RootedCoulomb.latTgt v (o k)),
      (∀ k μ x, ‖((RootedWilson.rootedWord (w k) (U k) (x, μ) : unitary 𝔄) : 𝔄) - 1‖ ≤ 1 / 64) →
      (∀ k μ ν x, ‖RootedCoulomb.litPlaq (U k) μ ν x - 1‖ < 1) →
      (∀ k, CoulombApriori.oneL4 (n k : ℝ)⁻¹ (toE : 𝔄 →L[ℝ] E₀)
          (RootedCoulomb.treeSeed (n k : ℝ)⁻¹ (w k) (U k)) +
        RootedCoulomb.litCurvL2 toE (n k : ℝ)⁻¹ (U k) ≤ εc) →
      -- `(F1)`
      ∀ (Ke : Set M4), IsCompact Ke → (∀ M ∈ Ke, 0 < Matrix.det (show Mat from M)) →
      (∀ k x, coframeM (y k) x ∈ Ke) → ∀ cm : ℝ, cm ≤ 1 / 64 →
      (∀ k x μ, (n k : ℝ)⁻¹ * ‖ωM (y k) μ x‖ ≤ cm) →
      TotallyBounded (range fun k => pcLp (coframeM (y k))) →
      TotallyBounded (range fun k => pcLp (fun x lam => qM (y k) lam x)) →
      (∀ k z, NativeTrigRec.recon (coframeM (y k)) z ∈ Ke) →
      -- `(F3)`
      (∃ B, ∀ k, gridNorm (curvPacket (n k) (y k)) ≤ B) →
      (∃ B, ∀ k, gridNorm (higgsPacket C₀.toData (n k) (y k)) ≤ B) →
      ∀ BH : ℝ, (∀ k, gridNorm (higgs (y k)) ≤ BH) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (adLinks (n k) (y k) (adUnit_of_links (hUe k))) μ m
          (curvPacket (n k) (y k)) - curvPacket (n k) (y k)) ≤ ε) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (higgsLinks C₀.toData (n k) (y k)
            (higgsUnit_of_links C₀ ⊤ (top_in_G hG) hρH (hUe k) (fun _ => Subgroup.mem_top _))) μ m
          (higgsPacket C₀.toData (n k) (y k)) - higgsPacket C₀.toData (n k) (y k)) ≤ ε) →
      -- `(F4)`
      ∀ B : ℝ, (∀ k, gridNorm (psi (y k)) ≤ B) →
      (∀ k μ, gridNorm (fun x => spinGraph C₀.toData (n k : ℝ)⁻¹ (y k) x μ) ≤ B) →
      (∀ k, gridNorm (psiBar (y k)) ≤ B) →
      (∀ k μ, gridNorm (fun x => dualGraph C₀.toData (n k : ℝ)⁻¹ (y k) x μ) ≤ B) →
      ∀ (Kθ : Set (ℝ × ℝ × ℝ × ℝ × (Fin J → ℝ) ×
          (EuclideanSpace ℝ (Fin rH) →L[ℝ] Spin 𝓢))), IsCompact Kθ →
      (∀ k, bankVec (θs k) ∈ Kθ) → (∀ v ∈ Kθ, v.1 ≠ 0 ∧ ∀ j, 0 ≤ v.2.2.2.2.1 j) →
      ∀ (hY : ∀ k, ∀ g ∈ C₀.G, ∀ H : EuclideanSpace ℝ (Fin rH),
        (θs k).Y (C₀.ρH g H) = C₀.ρS g * (θs k).Y H * C₀.ρS ↑g⁻¹),
      -- `(F5)`
      Tendsto (fun k => covNormP (bankCov C₀ Tj (θs k) hT (hY k)) M (n k : ℝ)⁻¹
        (toLinks (n k : ℝ)⁻¹ (y k))) atTop (𝓝 0) →
      ∃ g : ∀ k, Grid (n k) → 𝔄ˣ, ∃ y' : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢,
      (∀ k x, g k x ∈ unitaryUnits 𝔄) ∧
      (∀ k, y' k = gaugeRecord C₀ (n k : ℝ)⁻¹ (g k) (y k)) ∧
      (∀ k, IsGaugeTransform C₀ (n k : ℝ)⁻¹ (g k) (y k) (y' k)) ∧
      -- exact discrete Coulomb gauge
      (∀ k, NativeCoulomb.codiffT (toE : 𝔄 →L[ℝ] E₀) (NativeYMBridge.gaugeArr (y' k)) = 0) ∧
      (∀ k μ, NativeCoulomb.g4 (fun x => toE (NativeDensity.gauge (y' k) μ x)) ≤ εstar) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ H : CoHyp (fun k => n (φ k)) (fun k => y' (φ k)),
      H.Ke = Ke ∧
      ∃ θ : Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢, BankConv (fun k => θs (φ k)) θ ∧
      ∃ F : Fin 4 → Fin 4 → 𝕋 → 𝔄, ∃ G : Fin 4 → Fin 4 → 𝕋 → 𝔄,
      ∃ P : HiggsHyp (bankData C₀.toData Tj θ) (fun k => y' (φ k)),
      ∃ S : SpinHyp (κid 𝓢) (fun k => y' (φ k)), ∃ u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢),
      -- `eq:Wilson-strong-convergence`
      (∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
        NativeScaling.fieldStrength (n (φ k) : ℝ)⁻¹ (NativeDensity.gauge (y' (φ k))) x μ ν))
        (F μ ν)) ∧
      (∀ μ ν, LpTendsto volume 2
        (fun k => pc (NativeHiggs.DpV μ (NativeDensity.gauge (y' (φ k)) ν))) (G μ ν)) ∧
      (∀ μ ν, F μ ν =ᵐ[MeasureTheory.volume] NativeReconstructed.recCurv H.A₀ G μ ν) ∧
      (∀ μ, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (higgs (y' (φ k)))))
        (fun z => P.K₀ μ z - C₀.ρHL (H.A₀ μ z) (P.H₀ z))) ∧
      (∀ j, ∃ fj : Lp ℂ 2 (MeasureTheory.volume : Measure 𝕋),
        ((fj : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ (S.Ψ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 fj ∧ ∀ μ, (TorusSobolev.weakDeriv μ fj : 𝕋 → ℂ)
          =ᵐ[MeasureTheory.volume] fun z => ((Θ ((u₀ z).1 μ) j : ℝ) : ℂ)) ∧
      -- `eq:native-all-sector-limit` with the cutoff banks
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData C₀.toData Tj (θs (φ k))) (n (φ k)) (y' (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y' (φ k)) τ) -
          NativeAllSector.contAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀
            τ| ≤ ε) ∧
      -- consistency relative to the reconstructed fields
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData C₀.toData Tj (θs (φ k))) (n (φ k)) (y' (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y' (φ k)) τ) -
          NativeReconstructed.recAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w)
            (NativeTrigRec.recon (coframeM (y' (φ k))))
            (fun lam => NativeTrigRec.drecon lam (coframeM (y' (φ k))))
            (fun μ => NativeTrigRec.recon (NativeDensity.gauge (y' (φ k)) μ))
            (fun μ ν => NativeTrigRec.drecon μ (NativeDensity.gauge (y' (φ k)) ν))
            (NativeTrigRec.recon (higgs (y' (φ k))))
            (fun μ => NativeTrigRec.drecon μ (higgs (y' (φ k))))
            (NativeTrigRec.recon (psi (y' (φ k)))) (NativeTrigRec.recon (psiBar (y' (φ k))))
            (NativeTrigRec.recJets (y' (φ k))) τ| ≤ ε) ∧
      -- the distributional Einstein–Standard-Model equations
      (∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
        NativeAllSector.contAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀ τ
          = 0) ∧
      -- the bosonic stress densities
      (∀ (ΘF : M4 → (Fin 4 → Fin 4 → 𝔄) →L[ℝ] (Fin 4 → Fin 4 → 𝔄) →L[ℝ] ℝ)
        (ΘK : M4 → (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ]
          (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ] ℝ) (ΘV : M4 → ℝ),
        ContinuousOn ΘF Ke → ContinuousOn ΘK Ke → ContinuousOn ΘV Ke →
        LpTendsto volume 1
          (fun k z => ΘF (pc (coframeM (y' (φ k))) z) (pc (curvPacket (n (φ k)) (y' (φ k))) z)
              (pc (curvPacket (n (φ k)) (y' (φ k))) z) +
            ΘK (pc (coframeM (y' (φ k))) z)
              (pc (higgsPacket C₀.toData (n (φ k)) (y' (φ k))) z)
              (pc (higgsPacket C₀.toData (n (φ k)) (y' (φ k))) z) +
            ΘV (pc (coframeM (y' (φ k))) z) *
              potential (bankData C₀.toData Tj (θs (φ k))) (pc (higgs (y' (φ k))) z))
          (fun z => ΘF (H.e₀ z) (fun μ ν => F μ ν z) (fun μ ν => F μ ν z) +
            ΘK (H.e₀ z) (fun μ => P.K₀ μ z) (fun μ => P.K₀ μ z) +
            ΘV (H.e₀ z) * potential (bankData C₀.toData Tj θ) (P.H₀ z))) := by
  obtain ⟨εc, hεc, εs, hεs, H⟩ := finite_wilson_zero_defect_of_rootedNorm C₀ ⊤ (top_in_G hG)
    hρH Tj hT toE (rootedNorm_unitary toE hM1 hM2) M hM Θ Θ'
  refine ⟨εc, hεc, εs, hεs, fun n _ y θs hn U hUe o w hadm hplaq hcert Ke hKe hpos hval cm hcm
    hmar hTBe hTBq hrec hFb hKb BH hHb hΩF hΩK B hΨ hKs hΨb hKbd Kθ hKθ hθK hphys hY hF5 => ?_⟩
  obtain ⟨g, y', hgK, rest⟩ := H n y θs hn U hUe (fun _ _ => Subgroup.mem_top _) o w hadm hplaq
    hcert Ke hKe hpos hval cm hcm hmar hTBe hTBq hrec hFb hKb BH hHb hΩF hΩK B hΨ hKs hΨb hKbd Kθ
    hKθ hθK hphys hY hF5
  exact ⟨g, y', fun k x => by obtain ⟨u, -, hu⟩ := hgK k x; exact ⟨u, hu.symm⟩, rest⟩

end Main

/-! ### The Standard-Model gauge group `G_SM = S(U(3) × U(2))` -/

section MainSM

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

/-- The C*-algebra `M₃(ℂ) × M₂(ℂ)` (operator norms) carrying `G_SM`. -/
local notation "𝔄" => StandardModelCoulomb.SMAlg

open scoped Matrix.Norms.L2Operator
open TorusPiecewiseConstantTranslation KolmogorovRieszTorus
open NativeHiggsVar NativeDiracConvergence FiniteWilsonZeroDefect
open NativeDiracConv (CoHyp qM ωM)
open NativeSpinorGraph (spinGraph dualGraph)
open NativeDiracLimit (Dif)

variable {rH : ℕ} [NeZero rH]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {r r' : ℕ} [NeZero r] [NeZero r'] {J : ℕ}

/-- **The rooted normalization property for `G_SM`** (from
`NativeRecordNormSM.rooted_coulomb_normalization_chart_SM`). -/
theorem rootedNorm_SM : RootedNorm NativeRecordNormSM.GSM StandardModelCoulomb.toESM := by
  intro εstar hεstar
  obtain ⟨εc, Cc, hεc, -, H⟩ :=
    NativeRecordNormSM.rooted_coulomb_normalization_chart_SM (ι := Fin 4) (by simp) one_pos
      hεstar
  refine ⟨εc, hεc, fun m _ o w U hUK hadm hplaq hcert => ?_⟩
  have hpos : (0 : ℝ) < (m : ℝ)⁻¹ :=
    inv_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m))
  obtain ⟨g, hgK, hch, -, hcod, -, hsm⟩ := H m (m : ℝ)⁻¹ hpos
    (mul_inv_cancel₀ (inv_pos.1 hpos).ne') o w U hUK hadm hplaq hcert
  exact ⟨g, hgK, hch, hcod, hsm⟩

set_option maxHeartbeats 6400000 in
-- specialization of the general criterion
/-- **`thm:finite-Wilson-zero-defect` for the Standard-Model gauge group**
`G_SM = S(U(3) × U(2))` (`eq:gauge-group`) inside `M₃(ℂ) × M₂(ℂ)` with the invariant Frobenius
metric: `finite_wilson_zero_defect_of_rootedNorm` with the rooted normalization of `G_SM`
(`rootedNorm_SM`); the internal links take values in `G_SM`, and so do the normalizing site
gauges. -/
theorem finite_wilson_zero_defect_SM (C₀ : CovData 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (hG : ∀ u ∈ NativeRecordNormSM.GSM, Unitary.toUnits u ∈ C₀.G)
    (hρH : ∀ k ∈ C₀.G, ∀ v : EuclideanSpace ℝ (Fin rH), ‖C₀.ρH k v‖ = ‖v‖)
    (Tj : Fin J → 𝔄 →L[ℝ] E)
    (hT : ∀ g ∈ C₀.G, ∀ j (X Y : 𝔄),
      ⟪Tj j ((g : 𝔄) * X * ↑g⁻¹), Tj j ((g : 𝔄) * Y * ↑g⁻¹)⟫ = ⟪Tj j X, Tj j Y⟫)
    (M : MassMetric 𝔄 (EuclideanSpace ℝ (Fin rH))) (hM : M.Invariant C₀)
    (Θ : 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (Θ' : CoSpinor 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r')) :
    ∃ εc > 0, ∃ εstar > 0, ∀ (n : ℕ → ℕ) [∀ k, NeZero (n k)]
      (y : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
      (θs : ℕ → Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢), Tendsto n atTop atTop →
      -- the unitary internal links of the records and `(F2)`
      ∀ (U : ∀ k, Grid (n k) × Fin 4 → unitary 𝔄)
        (hUe : ∀ k x μ, (U k (x, μ) : 𝔄) = exp ((n k : ℝ)⁻¹ • NativeDensity.gauge (y k) μ x))
        (hUK : ∀ k e, U k e ∈ NativeRecordNormSM.GSM) (o : ∀ k, Grid (n k))
        (w : ∀ k, ∀ v, LatticeWalk (RootedCoulomb.latSrc (ι := Fin 4) (n := n k))
          RootedCoulomb.latTgt v (o k)),
      (∀ k μ x, ‖((RootedWilson.rootedWord (w k) (U k) (x, μ) : unitary 𝔄) : 𝔄) - 1‖ ≤ 1 / 64) →
      (∀ k μ ν x, ‖RootedCoulomb.litPlaq (U k) μ ν x - 1‖ < 1) →
      (∀ k, CoulombApriori.oneL4 (n k : ℝ)⁻¹ (StandardModelCoulomb.toESM : 𝔄 →L[ℝ] StandardModelCoulomb.SMEuc)
          (RootedCoulomb.treeSeed (n k : ℝ)⁻¹ (w k) (U k)) +
        RootedCoulomb.litCurvL2 StandardModelCoulomb.toESM (n k : ℝ)⁻¹ (U k) ≤ εc) →
      -- `(F1)`
      ∀ (Ke : Set M4), IsCompact Ke → (∀ M ∈ Ke, 0 < Matrix.det (show Mat from M)) →
      (∀ k x, coframeM (y k) x ∈ Ke) → ∀ cm : ℝ, cm ≤ 1 / 64 →
      (∀ k x μ, (n k : ℝ)⁻¹ * ‖ωM (y k) μ x‖ ≤ cm) →
      TotallyBounded (range fun k => pcLp (coframeM (y k))) →
      TotallyBounded (range fun k => pcLp (fun x lam => qM (y k) lam x)) →
      (∀ k z, NativeTrigRec.recon (coframeM (y k)) z ∈ Ke) →
      -- `(F3)`
      (∃ B, ∀ k, gridNorm (curvPacket (n k) (y k)) ≤ B) →
      (∃ B, ∀ k, gridNorm (higgsPacket C₀.toData (n k) (y k)) ≤ B) →
      ∀ BH : ℝ, (∀ k, gridNorm (higgs (y k)) ≤ BH) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (adLinks (n k) (y k) (adUnit_of_links (hUe k))) μ m
          (curvPacket (n k) (y k)) - curvPacket (n k) (y k)) ≤ ε) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (higgsLinks C₀.toData (n k) (y k)
            (higgsUnit_of_links C₀ NativeRecordNormSM.GSM hG hρH (hUe k) (hUK k))) μ m
          (higgsPacket C₀.toData (n k) (y k)) - higgsPacket C₀.toData (n k) (y k)) ≤ ε) →
      -- `(F4)`
      ∀ B : ℝ, (∀ k, gridNorm (psi (y k)) ≤ B) →
      (∀ k μ, gridNorm (fun x => spinGraph C₀.toData (n k : ℝ)⁻¹ (y k) x μ) ≤ B) →
      (∀ k, gridNorm (psiBar (y k)) ≤ B) →
      (∀ k μ, gridNorm (fun x => dualGraph C₀.toData (n k : ℝ)⁻¹ (y k) x μ) ≤ B) →
      ∀ (Kθ : Set (ℝ × ℝ × ℝ × ℝ × (Fin J → ℝ) ×
          (EuclideanSpace ℝ (Fin rH) →L[ℝ] Spin 𝓢))), IsCompact Kθ →
      (∀ k, bankVec (θs k) ∈ Kθ) → (∀ v ∈ Kθ, v.1 ≠ 0 ∧ ∀ j, 0 ≤ v.2.2.2.2.1 j) →
      ∀ (hY : ∀ k, ∀ g ∈ C₀.G, ∀ H : EuclideanSpace ℝ (Fin rH),
        (θs k).Y (C₀.ρH g H) = C₀.ρS g * (θs k).Y H * C₀.ρS ↑g⁻¹),
      -- `(F5)`
      Tendsto (fun k => covNormP (bankCov C₀ Tj (θs k) hT (hY k)) M (n k : ℝ)⁻¹
        (toLinks (n k : ℝ)⁻¹ (y k))) atTop (𝓝 0) →
      ∃ g : ∀ k, Grid (n k) → 𝔄ˣ, ∃ y' : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢,
      (∀ k x, ∃ u ∈ NativeRecordNormSM.GSM, g k x = Unitary.toUnits u) ∧
      (∀ k, y' k = gaugeRecord C₀ (n k : ℝ)⁻¹ (g k) (y k)) ∧
      (∀ k, IsGaugeTransform C₀ (n k : ℝ)⁻¹ (g k) (y k) (y' k)) ∧
      -- exact discrete Coulomb gauge
      (∀ k, NativeCoulomb.codiffT (StandardModelCoulomb.toESM : 𝔄 →L[ℝ] StandardModelCoulomb.SMEuc) (NativeYMBridge.gaugeArr (y' k)) = 0) ∧
      (∀ k μ, NativeCoulomb.g4 (fun x => StandardModelCoulomb.toESM (NativeDensity.gauge (y' k) μ x)) ≤ εstar) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ H : CoHyp (fun k => n (φ k)) (fun k => y' (φ k)),
      H.Ke = Ke ∧
      ∃ θ : Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢, BankConv (fun k => θs (φ k)) θ ∧
      ∃ F : Fin 4 → Fin 4 → 𝕋 → 𝔄, ∃ G : Fin 4 → Fin 4 → 𝕋 → 𝔄,
      ∃ P : HiggsHyp (bankData C₀.toData Tj θ) (fun k => y' (φ k)),
      ∃ S : SpinHyp (κid 𝓢) (fun k => y' (φ k)), ∃ u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢),
      -- `eq:Wilson-strong-convergence`
      (∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
        NativeScaling.fieldStrength (n (φ k) : ℝ)⁻¹ (NativeDensity.gauge (y' (φ k))) x μ ν))
        (F μ ν)) ∧
      (∀ μ ν, LpTendsto volume 2
        (fun k => pc (NativeHiggs.DpV μ (NativeDensity.gauge (y' (φ k)) ν))) (G μ ν)) ∧
      (∀ μ ν, F μ ν =ᵐ[MeasureTheory.volume] NativeReconstructed.recCurv H.A₀ G μ ν) ∧
      (∀ μ, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (higgs (y' (φ k)))))
        (fun z => P.K₀ μ z - C₀.ρHL (H.A₀ μ z) (P.H₀ z))) ∧
      (∀ j, ∃ fj : Lp ℂ 2 (MeasureTheory.volume : Measure 𝕋),
        ((fj : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ (S.Ψ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 fj ∧ ∀ μ, (TorusSobolev.weakDeriv μ fj : 𝕋 → ℂ)
          =ᵐ[MeasureTheory.volume] fun z => ((Θ ((u₀ z).1 μ) j : ℝ) : ℂ)) ∧
      -- `eq:native-all-sector-limit` with the cutoff banks
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData C₀.toData Tj (θs (φ k))) (n (φ k)) (y' (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y' (φ k)) τ) -
          NativeAllSector.contAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀
            τ| ≤ ε) ∧
      -- consistency relative to the reconstructed fields
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData C₀.toData Tj (θs (φ k))) (n (φ k)) (y' (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y' (φ k)) τ) -
          NativeReconstructed.recAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w)
            (NativeTrigRec.recon (coframeM (y' (φ k))))
            (fun lam => NativeTrigRec.drecon lam (coframeM (y' (φ k))))
            (fun μ => NativeTrigRec.recon (NativeDensity.gauge (y' (φ k)) μ))
            (fun μ ν => NativeTrigRec.drecon μ (NativeDensity.gauge (y' (φ k)) ν))
            (NativeTrigRec.recon (higgs (y' (φ k))))
            (fun μ => NativeTrigRec.drecon μ (higgs (y' (φ k))))
            (NativeTrigRec.recon (psi (y' (φ k)))) (NativeTrigRec.recon (psiBar (y' (φ k))))
            (NativeTrigRec.recJets (y' (φ k))) τ| ≤ ε) ∧
      -- the distributional Einstein–Standard-Model equations
      (∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
        NativeAllSector.contAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀ τ
          = 0) ∧
      -- the bosonic stress densities
      (∀ (ΘF : M4 → (Fin 4 → Fin 4 → 𝔄) →L[ℝ] (Fin 4 → Fin 4 → 𝔄) →L[ℝ] ℝ)
        (ΘK : M4 → (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ]
          (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ] ℝ) (ΘV : M4 → ℝ),
        ContinuousOn ΘF Ke → ContinuousOn ΘK Ke → ContinuousOn ΘV Ke →
        LpTendsto volume 1
          (fun k z => ΘF (pc (coframeM (y' (φ k))) z) (pc (curvPacket (n (φ k)) (y' (φ k))) z)
              (pc (curvPacket (n (φ k)) (y' (φ k))) z) +
            ΘK (pc (coframeM (y' (φ k))) z)
              (pc (higgsPacket C₀.toData (n (φ k)) (y' (φ k))) z)
              (pc (higgsPacket C₀.toData (n (φ k)) (y' (φ k))) z) +
            ΘV (pc (coframeM (y' (φ k))) z) *
              potential (bankData C₀.toData Tj (θs (φ k))) (pc (higgs (y' (φ k))) z))
          (fun z => ΘF (H.e₀ z) (fun μ ν => F μ ν z) (fun μ ν => F μ ν z) +
            ΘK (H.e₀ z) (fun μ => P.K₀ μ z) (fun μ => P.K₀ μ z) +
            ΘV (H.e₀ z) * potential (bankData C₀.toData Tj θ) (P.H₀ z))) :=
  finite_wilson_zero_defect_of_rootedNorm C₀ NativeRecordNormSM.GSM hG hρH Tj hT
    StandardModelCoulomb.toESM rootedNorm_SM M hM Θ Θ'

end MainSM

end

end RenewalGeometry.FiniteWilsonClosure
