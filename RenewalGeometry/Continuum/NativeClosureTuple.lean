/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CoupledBootstrapSlabModel
import RenewalGeometry.Analysis.DyadicRateAsymptotics

/-!
# `thm:native-closure` and `cor:native-rate` in the actual-tuple model, from the source bound

Einstein–Standard-Model action-closure manuscript, `thm:native-closure` (`eq:native-total`,
`eq:native-geometry`) and `cor:native-rate`.

The proof of `thm:native-closure` applies `prop:coupled-bootstrap` with
`d = i_{h,k} + γ_{h,k} + 𝒴_k(z_h)` and the source estimate `𝒴_k(z_h) ≤ C F_{h,k}` of
`thm:native-source`.  Here `prop:coupled-bootstrap` is the proved `coupled_bootstrap` for the
concrete slab model `slabModel` of smooth actual field tuples (`i_{h,k}` = initial `H^k` state
distance, `γ_{h,k}` = `harm`, `𝒴_k = resB + resD`).  The source estimate enters as the
hypothesis `hY` (`𝒴_k(z_h) ≤ C₁ F_h` eventually): `NativeSourceThm.native_source` proves it for
the coframe reconstruction `recon n u` of the native grid model (period `2π`, Euler rows of the
local action), and the identification of that reconstruction and its rows `RB`, `RD` with an actual
field tuple and its residuals `bosF`, `dirF` is not in the library.

* **`native_closure_tuple`** — `eq:native-geometry`: there is `C` (uniform over the reference class
  `refSet`) such that along any filter, if `D_h = i_h + γ_h + F_h → 0` and `𝒴_h ≤ C₁ F_h`
  eventually, then eventually `‖𝒰_h - 𝒰_*‖_{C_tH^k} + ‖Riem‖_{L²H^{k-1}} + ‖T^{SM}‖_{L²H^k}
  ≤ C max(1, C₁) D_h`.  No a priori bound on the records is assumed.
* **`native_rate_tuple`** — `cor:native-rate`: with the budget `F_h = forcingBudget` of
  `eq:native-forcing-budget`, `σ_h = O(h)`, `1 ≤ K_h ≤ c₂ h^{-β}`, `β < 1/(k+4)`,
  `eq:native-tail-rate` and `i_h + γ_h = O(h^{1-β(k+4)}(1+|log h|)^{k+1})`, the state, curvature
  and stress differences are `O(h^{1-β(k+4)}(1+|log h|)^{k+1})`.
-/

open MeasureTheory Filter Topology Set Metric Asymptotics
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.CoupledBootstrap.NativeTuple

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy QLDiff QLRecovery FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge
  ActualJetBridge ActualJetCompleteForcing ActualJetState ActualJetRecon SpinorProlongation
  TwistedHalfRicci SlabSemi AposterioriShadow

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

universe u

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
variable {n : ℕ} (eX : (Fin n → ℝ) ≃L[ℝ] StateP m V S S')
variable {na nb : ℕ} (eY : (Fin na → ℝ) ≃L[ℝ] BosP m V) (eYD : (Fin nb → ℝ) ≃L[ℝ] S × S')

/-- **`thm:native-closure`** (`eq:native-geometry`) in the actual-tuple model, with the source
estimate of `thm:native-source` as the hypothesis `𝒴_h ≤ C₁ F_h`. -/
theorem native_closure_tuple (hS : SMSmooth SM)
    (hAsym : ∀ j a b v, Aco SM eX j a b v = Aco SM eX j b a v)
    {k : ℕ} (hk : 4 ≤ k) {T : ℝ} (hT : 0 < T) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKO : K ⊆ chartC eX) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ {ι : Type u} (l : Filter ι) (zh : ι → Tuple m V S S'),
      ∀ zs ∈ refSet SM eX k T K R₁, ∀ (F : ι → ℝ) (C₁ : ℝ),
      (∀ᶠ h in l, 0 ≤ F h) →
      Tendsto (fun h => ‖(slabModel SM eX eY eYD hS k T hT).init (zh h) -
          (slabModel SM eX eY eYD hS k T hT).init zs‖ +
        (slabModel SM eX eY eYD hS k T hT).harm (zh h) + F h) l (𝓝 0) →
      (∀ᶠ h in l, (slabModel SM eX eY eYD hS k T hT).resB (zh h) +
        (slabModel SM eX eY eYD hS k T hT).resD (zh h) ≤ C₁ * F h) →
      ∀ᶠ h in l, dist ((slabModel SM eX eY eYD hS k T hT).obs (zh h))
          ((slabModel SM eX eY eYD hS k T hT).obs zs) ≤
        Cst * max 1 C₁ * (‖(slabModel SM eX eY eYD hS k T hT).init (zh h) -
          (slabModel SM eX eY eYD hS k T hT).init zs‖ +
          (slabModel SM eX eY eYD hS k T hT).harm (zh h) + F h) := by
  obtain ⟨dst, Cst, hdst, hCst, hconc⟩ :=
    coupled_bootstrap SM eX eY eYD hS hAsym hk hT hK hKO hR₁
  refine ⟨Cst, hCst, fun {ι} l zh zs hzs F C₁ hF hD hY => ?_⟩
  set M := slabModel SM eX eY eYD hS k T hT
  set Kc := max 1 C₁ with hKc
  have hK1 : 1 ≤ Kc := le_max_left _ _
  have hK0 : 0 < Kc := lt_of_lt_of_le one_pos hK1
  have hev : ∀ᶠ h in l, ‖M.init (zh h) - M.init zs‖ + M.harm (zh h) + F h < dst / Kc :=
    hD.eventually (gt_mem_nhds (div_pos hdst hK0))
  filter_upwards [hev, hF, hY] with h hh hF0 hY0
  set i := ‖M.init (zh h) - M.init zs‖
  set γ := M.harm (zh h)
  have hi : 0 ≤ i := norm_nonneg _
  have hγ : 0 ≤ γ := M.harm_nonneg _
  have hmis : M.mismatch (zh h) zs = i + γ + (M.resB (zh h) + M.resD (zh h)) := by
    unfold SlabModel.mismatch; ring
  have hdY : M.mismatch (zh h) zs ≤ Kc * (i + γ + F h) := by
    rw [hmis]
    have h1 : C₁ * F h ≤ Kc * F h := mul_le_mul_of_nonneg_right (le_max_right _ _) hF0
    have h2 : i + γ ≤ Kc * (i + γ) := by nlinarith
    nlinarith
  have hsmall : M.mismatch (zh h) zs ≤ dst := by
    calc M.mismatch (zh h) zs ≤ Kc * (i + γ + F h) := hdY
      _ ≤ Kc * (dst / Kc) := mul_le_mul_of_nonneg_left hh.le hK0.le
      _ = dst := by field_simp
  calc dist (M.obs (zh h)) (M.obs zs) ≤ Cst * M.mismatch (zh h) zs :=
        hconc zs hzs (zh h) trivial hsmall
    _ ≤ Cst * (Kc * (i + γ + F h)) := mul_le_mul_of_nonneg_left hdY hCst
    _ = Cst * Kc * (i + γ + F h) := by ring

/-- **`cor:native-rate`** in the actual-tuple model (rate of `eq:native-geometry`), with the source
estimate of `thm:native-source` as the hypothesis `𝒴_h ≤ C₁ F_{h,k}`. -/
theorem native_rate_tuple (hS : SMSmooth SM)
    (hAsym : ∀ j a b v, Aco SM eX j a b v = Aco SM eX j b a v)
    {k : ℕ} (hk : 4 ≤ k) {T : ℝ} (hT : 0 < T) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKO : K ⊆ chartC eX) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ {ι : Type u} (l : Filter ι) (zh : ι → Tuple m V S S'),
      ∀ zs ∈ refSet SM eX k T K R₁, ∀ (h Kh σ τ₂ τm : ι → ℝ) {Ck β c₂ Cσ Cτ C₁ : ℝ},
      0 ≤ Ck → 0 ≤ β → β < 1 / (k + 4) → 0 ≤ Cσ → Tendsto h l (𝓝[>] 0) →
      (∀ᶠ i in l, 0 < h i ∧ h i ≤ 1 ∧ 1 ≤ Kh i ∧ Kh i ≤ c₂ * h i ^ (-β) ∧ 0 ≤ σ i ∧
        σ i ≤ Cσ * h i ∧ 0 ≤ τ₂ i ∧ τ₂ i ≤ Cτ * (h i * Kh i) ∧ 0 ≤ τm i ∧
        τm i ≤ Cτ * (h i * Kh i ^ 2)) →
      (∀ᶠ i in l, (slabModel SM eX eY eYD hS k T hT).resB (zh i) +
        (slabModel SM eX eY eYD hS k T hT).resD (zh i) ≤
          C₁ * NativeRate.forcingBudget k Ck (σ i) (h i) (Kh i) (τ₂ i) (τm i)) →
      (fun i => ‖(slabModel SM eX eY eYD hS k T hT).init (zh i) -
          (slabModel SM eX eY eYD hS k T hT).init zs‖ +
        (slabModel SM eX eY eYD hS k T hT).harm (zh i)) =O[l]
          (fun i => h i ^ (1 - β * (k + 4)) * (1 + |Real.log (h i)|) ^ (k + 1)) →
      (fun i => dist ((slabModel SM eX eY eYD hS k T hT).obs (zh i))
          ((slabModel SM eX eY eYD hS k T hT).obs zs)) =O[l]
        (fun i => h i ^ (1 - β * (k + 4)) * (1 + |Real.log (h i)|) ^ (k + 1)) := by
  obtain ⟨Cst, hCst, hcl⟩ :=
    native_closure_tuple.{u} SM eX eY eYD hS hAsym hk hT hK hKO hR₁
  refine ⟨Cst, hCst, fun {ι} l zh zs hzs h Kh σ τ₂ τm Ck β c₂ Cσ Cτ C₁ hCk hβ hβk hCσ hh hev
    hY hig => ?_⟩
  set M := slabModel SM eX eY eYD hS k T hT
  set F := fun i => NativeRate.forcingBudget k Ck (σ i) (h i) (Kh i) (τ₂ i) (τm i)
  set rate := fun i => h i ^ (1 - β * (k + 4)) * (1 + |Real.log (h i)|) ^ (k + 1)
  have hρ : 0 < 1 - β * (k + 4) := by
    have hk4 : (0 : ℝ) < k + 4 := by positivity
    rw [lt_div_iff₀ hk4] at hβk; linarith
  have hrate : Tendsto rate l (𝓝 0) :=
    (NativeRate.tendsto_rpow_mul_one_add_abs_log_pow hρ (k + 1)).comp hh
  have hFO : F =O[l] rate := NativeRate.forcingBudget_isBigO k hCk hβ hCσ hev
  have hF0 : ∀ᶠ i in l, 0 ≤ F i := by
    filter_upwards [hev] with i ⟨h0, _, hK1, _, hσ0, _, hτ0, _, hτm0, _⟩
    have hE0 : 0 ≤ NativeRate.epsc (σ i) (h i) (Kh i) (τ₂ i) :=
      (by positivity : (0 : ℝ) ≤ h i * Kh i ^ 3).trans (NativeRate.le_epsc hσ0 hτ0)
    have hKp : 0 ≤ Kh i := by linarith
    have hL0 : 0 ≤ NativeRate.logFactor k Ck (Kh i) (NativeRate.epsc (σ i) (h i) (Kh i) (τ₂ i)) := by
      unfold NativeRate.logFactor
      have : 0 ≤ Ck * Kh i ^ (k + 5) / NativeRate.epsc (σ i) (h i) (Kh i) (τ₂ i) := by positivity
      have := Real.log_nonneg (by linarith :
        (1 : ℝ) ≤ 2 + Ck * Kh i ^ (k + 5) / NativeRate.epsc (σ i) (h i) (Kh i) (τ₂ i))
      linarith
    unfold F NativeRate.forcingBudget
    positivity
  have hDO : (fun i => ‖M.init (zh i) - M.init zs‖ + M.harm (zh i) + F i) =O[l] rate :=
    hig.add hFO
  have hD : Tendsto (fun i => ‖M.init (zh i) - M.init zs‖ + M.harm (zh i) + F i) l (𝓝 0) :=
    hDO.trans_tendsto hrate
  have hbound := hcl l zh zs hzs F C₁ hF0 hD hY
  refine (IsBigO.of_bound (Cst * max 1 C₁) ?_).trans hDO
  filter_upwards [hbound, hF0] with i hi hFi
  have hd0 : 0 ≤ dist (M.obs (zh i)) (M.obs zs) := dist_nonneg
  have hD0 : 0 ≤ ‖M.init (zh i) - M.init zs‖ + M.harm (zh i) + F i :=
    add_nonneg (add_nonneg (norm_nonneg _) (M.harm_nonneg _)) hFi
  rw [Real.norm_of_nonneg hd0, Real.norm_of_nonneg hD0]
  exact hi

end RenewalGeometry.CoupledBootstrap.NativeTuple
