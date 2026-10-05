/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.DiscreteEulerConsistency
import RenewalGeometry.Continuum.NativeGravityFirstJet

/-!
# Growing-band consistency of the native Euler row (`prop:native-consistency`)

Einstein–Standard-Model action-closure manuscript, Appendix `app:quantitative-residuals`,
`prop:native-consistency` (`eq:native-consistency`), with the amplitude-preserving scaling of
`lem:native-scaling` (`app:native-scaling`).

## Setting

The unchanged local action `S_h^{loc} = h⁴ Σ_x 𝓛_h(y)(x)` of `app:native-action`
(`NativeDensity.localAction`: Cartan, Yang–Mills, Higgs and Dirac–Yukawa rows of
`eq:native-densities`) on the periodic grid `(ℤ/n)⁴` with mesh `h`; a smooth physical field tuple
`y : ℝ⁴ → (e, A, H, Ψ, Ψ̄)` of period `n h` (the paper's periodic comparison box; trivialised
bundles, one fixed frame), sampled at the nodes (`DiscreteEulerConsistency.samp`).  The raw Euler
row is `E_h^{raw}(y)(x) = h⁻⁴ ∂_{y(x)} S_h^{loc}` (`DiscreteEulerConsistency.eulerRow`).

The continuum Euler density `𝓔₀(y)` is the Euler–Lagrange expression
`∂_w L₀ - Σ_μ ∂_μ ∂_{p_μ} L₀` (`DiscreteEulerConsistency.contEuler`) of the continuum
Einstein–Standard-Model Lagrangian `L₀(w, p) = F^{(1)}_0(w, …, w; p, …, p)`, the `h = 0` value of
the first-jet density of `lem:native-firstjet-normal-form` at the constant jet
(`DiscreteEulerConsistency.limDensity`): its gravitational part is the first-order Palatini
representative `palatiniFirstOrder` (identified in `NativeGravityJet.palatiniFirstOrder_eq`, the
convention of `prop:native-gravity-firstjet`), its gauge part uses `F = ∂A - ∂A + [A, A]`, its
Higgs part `D_A H = ∂H + ρ_H(A) H`, its Dirac part `∇Ψ = ∂Ψ + σ(ω(e, ∂e))Ψ + ρ_S(A)Ψ` with the
torsion-free reader connection `ω(e, ∂e)`.  The Euler expression of a first-order representative
equals that of any density differing from it by a divergence.

## Main results

* `firstJetDensity_jetScale` (**`lem:native-scaling` on first jets**): with `ρ = hK`, `ν = K⁻¹`
  and the amplitudes unchanged, `F^{(1)}(h, (v, K q)) = K² 𝒢(ν, ρ, (v, q))`, where the normalised
  density `𝒢 = F^{(1)}_g + (1 - ν²)(Λ/κ)v + 𝓛̃_{YM} + 𝓛̃_H + ν 𝓛̃_D` (`scaledDensity`) is smooth in
  `(ν, ρ, ξ)` at every point `(ν, 0, ξ)` of the nondegenerate chart (`contDiffAt_scaledDensity`).
* `native_consistency` (**`prop:native-consistency`, `eq:native-consistency`**): for a compact
  coframe chart `K_e ⊂ {det e > 0}` (uniform inverse metric), an amplitude bound `A` and a band
  constant `B`, there are `C` and `c_res > 0` such that for every `K ≥ 1`, every mesh `h > 0`
  with `hK ≤ c_res`, every grid size `n` and every `C³` field `y` of period `n h` with values in
  the chart, `|y| ≤ A` and `‖D^j y‖ ≤ B K^j` (`j = 1, 2, 3`, the growing-band hypothesis
  `eq:growing-derivatives` at the orders used), the samples lie on the Cartan logarithm chart and
  `‖E_h^{raw}(𝖲_h y)(x) - 𝓔₀(y)(x)‖ ≤ C h K³` **at every node**.  The constants depend on the
  chart, `A`, `B` and the coefficient bank, not on `h`, `K`, `n` or `y`.

* `native_cartan_consistency` / `native_cartan_riem` (**`eq:native-Cartan`**): under the same
  hypotheses the literal Cartan plaquette curvature `R^h_{μν}(x)` of the samples is uniformly
  `C h K³`-close, at **every point of the cell** `‖z - h x̃‖ ≤ h` of every node, to the curvature
  `dω + ω ∧ ω` of the torsion-free reader connection (`contCartan`), which equals the Riemann
  tensor of `g = eᵀ η e` in mixed frame/coordinate components, `e Riem_{μν}(g) e⁻¹`
  (`contCartan_eq_riem`, the Cartan structure equation; `riemMat` is the coordinate formula
  `∂_μΓ_ν - ∂_νΓ_μ + [Γ_μ, Γ_ν]` with the Christoffel symbols `readerGamma` of `g`).  This is an
  `L^∞` bound for the piecewise-constant reconstruction `I_h^0 R_h^{raw}`, hence the `L²(Q)` bound
  with the factor `|Q|^{1/2}`.
* `limDensity_firstJetDensity_eq`, `nuFieldStrength_cont`, `nuHiggsLinkJet_cont`,
  `nuDiracDiffJet_cont`, `nuDiracDiffBarJet_cont`: identification of the continuum Lagrangian
  `L₀` sector by sector.
* `native_sigma_of_solution` (fixed scale): for a smooth solution `𝓔₀(y) = 0`, the samples have
  `max_x ‖E_h^{raw}(x)‖ ≤ C h` and `σ_h² = h⁴ Σ_x ‖E_h^{raw}(x)‖² ≤ L⁴ (C h)²` (`eq:native-sigma`).

Disclosed renderings: finite-dimensional gauge algebra and Higgs/spinor fibres (`FiniteDimensional`),
as in the paper; the band hypothesis is used through the first three derivatives (`q ≥ 5` in the
paper only strengthens it); operator norms of `D^j y` in the sup norm of `ℝ⁴`; the Christoffel
formula `readerGamma` uses `∂g = (∂e)ᵀ η e + eᵀ η ∂e` (`NativeScaling.readerG`).
-/

open Finset Filter Topology Metric Set NormedSpace
open scoped ContDiff

namespace RenewalGeometry.NativeEulerConsistency

open ShiftedJetAction (Grid unitVec stencil action)
open NativeScaling (Mat eta metric readerOmega omegaLink)
open ShiftedPlaquette NativeDensity DiscreteEulerConsistency

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

/-! ### Jet scaling -/

/-- The amplitude-preserving jet scaling `(v, q) ↦ (v, K q)`: values unchanged, normalised first
differences multiplied by `K` (`δ⁺_h = K δ⁺_{hK}`). -/
def jetScale (K : ℝ) (ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) : NativeDensity.Jet (Field 𝔄 𝓗 𝓢) :=
  (ξ.1, K • ξ.2)

/-- The coframe jet of a field jet. -/
def cofJet (ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) : NativeGravityJet.JetM :=
  (fun s => (ξ.1 s).1, fun sl => (ξ.2 sl).1)

theorem gravFirstJet_eq_gravCurv (q : ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) :
    gravFirstJet D q = NativeGravityJet.gravCurv D.κ (q.1, cofJet q.2) -
      D.Λ / D.κ * volume (q.2.1 none).1 := by
  unfold gravFirstJet NativeGravityJet.gravCurv remCartan NativeGravityJet.remM jetOmega
    jetOmegaShift jetEm jetPm NativeGravityJet.omegaM NativeGravityJet.omegaShiftM
    NativeGravityJet.emM NativeGravityJet.pmM cofJet
  ring

theorem cofJet_jetScale (K : ℝ) (ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) :
    cofJet (jetScale K ξ) = ((cofJet ξ).1, K • (cofJet ξ).2) := rfl

/-- Gravity: `F_g(h, (v, Kq)) = K² F_g(hK, (v, q)) + (K² - 1)(Λ/κ) v(e)`. -/
theorem gravFirstJet_jetScale (h K : ℝ) (ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) :
    gravFirstJet D (h, jetScale K ξ) =
      K ^ 2 * gravFirstJet D (h * K, ξ) + (K ^ 2 - 1) * (D.Λ / D.κ) * volume (ξ.1 none).1 := by
  rw [gravFirstJet_eq_gravCurv, gravFirstJet_eq_gravCurv, cofJet_jetScale,
    NativeGravityJet.gravCurv_smul]
  simp only [jetScale]
  ring

/-- The removable quotient: `Q̂(h, 1; X, Y, Ka, Kb) = K Q̂(hK, K⁻¹; X, Y, a, b)`. -/
theorem nuQuotientPoly_scale {K : ℝ} (hK : K ≠ 0) (h : ℝ) (X Y a b : 𝔄) :
    nuQuotientPoly h 1 X Y (K • a) (K • b) = K • nuQuotientPoly (h * K) K⁻¹ X Y a b := by
  have e1 : nuQuotientPoly h 1 X Y (K • a) (K • b) = quotientPoly h X Y (K • a) (K • b) := by
    have := quotientPoly_smul h 1 X Y (K • a) (K • b)
    simpa only [one_smul] using this.symm
  have e2 : quotientPoly (h * K) (K⁻¹ • X) (K⁻¹ • Y) (K⁻¹ • a) (K⁻¹ • b) =
      K⁻¹ • nuQuotientPoly (h * K) K⁻¹ X Y a b := quotientPoly_smul _ _ _ _ _ _
  have e3 : quotientPoly h X Y (K • a) (K • b) =
      K ^ 2 • quotientPoly (h * K) (K⁻¹ • X) (K⁻¹ • Y) (K⁻¹ • a) (K⁻¹ • b) := by
    rw [quotientPoly_eq_remQuotient, quotientPoly_eq_remQuotient]
    have hA : (h * K) • (K⁻¹ • a) = K⁻¹ • ((h * K) • a) := smul_comm _ _ _
    have hB : (h * K) • (K⁻¹ • b) = K⁻¹ • ((h * K) • b) := smul_comm _ _ _
    rw [hA, hB, NativeGravityJet.remQuotient_smul, show h * K * K⁻¹ = h by field_simp]
    simp only [smul_add, smul_sub, smul_smul]
    rw [show K ^ 2 * K⁻¹ = K by field_simp, show K ^ 2 * K⁻¹ ^ 2 = 1 by field_simp, one_smul]
  rw [e1, e3, e2, smul_smul, show K ^ 2 * K⁻¹ = K by field_simp]

/-- The ν-normalised field strength: `F̃(h, 1; X, Y, Ka, Kb) = K F̃(hK, K⁻¹; X, Y, a, b)`. -/
theorem jointNuLogPlaquette_scale {K : ℝ} (hK : K ≠ 0) (h : ℝ) (X Y a b : 𝔄) :
    jointNuLogPlaquette (h, 1, X, Y, K • a, K • b) =
      K • jointNuLogPlaquette (h * K, K⁻¹, X, Y, a, b) := by
  unfold jointNuLogPlaquette jointNuQuotient
  simp only []
  rw [nuQuotientPoly_scale hK, smul_smul, smul_mul_assoc]
  congr 2
  field_simp

theorem nuFieldStrength_jetScale {K : ℝ} (hK : K ≠ 0) (h : ℝ)
    (ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) (μ ν : Fin 4) :
    nuFieldStrength μ ν (h, 1, jetScale K ξ) = K • nuFieldStrength μ ν (h * K, K⁻¹, ξ) := by
  unfold nuFieldStrength
  simp only [jetScale, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd]
  exact jointNuLogPlaquette_scale hK h _ _ _ _

/-- Yang–Mills: `𝓛̃_{YM}(h, 1, (v, Kq)) = K² 𝓛̃_{YM}(hK, K⁻¹, (v, q))`. -/
theorem normYM_jetScale {K : ℝ} (hK : K ≠ 0) (h : ℝ) (ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) :
    normYM D (h, 1, jetScale K ξ) = K ^ 2 * normYM D (h * K, K⁻¹, ξ) := by
  unfold normYM
  have hF : (fun μ ν => nuFieldStrength μ ν (h, 1, jetScale K ξ)) =
      fun μ ν => K • nuFieldStrength μ ν (h * K, K⁻¹, ξ) := by
    funext μ ν; exact nuFieldStrength_jetScale hK h ξ μ ν
  rw [hF]
  have hv : ((h, (1 : ℝ), jetScale K ξ) : ℝ × ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)).2.2.1 none =
      ξ.1 none := rfl
  simp only [hv, antisym_smul, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_neg,
    Finset.mul_sum, jetScale]
  congr 1
  refine sum_congr rfl fun μ _ => sum_congr rfl fun ν _ => sum_congr rfl fun ρ _ =>
    sum_congr rfl fun σ _ => ?_
  ring


/-- Higgs link: `K̃(h, 1; A, H⁺, K dH) = K K̃(hK, K⁻¹; A, H⁺, dH)`. -/
theorem nuHiggsLinkJet_jetScale {K : ℝ} (hK : K ≠ 0) (h : ℝ)
    (ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) (μ : Fin 4) :
    nuHiggsLinkJet D μ (h, 1, jetScale K ξ) = K • nuHiggsLinkJet D μ (h * K, K⁻¹, ξ) := by
  unfold nuHiggsLinkJet nuHiggsLink
  simp only [jetScale, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, one_smul, mul_one, smul_add,
    smul_smul, mul_inv_cancel₀ hK, show h * K * K⁻¹ = h by field_simp]

/-- Higgs: `𝓛̃_H(h, 1, (v, Kq)) = K² 𝓛̃_H(hK, K⁻¹, (v, q))`. -/
theorem normHiggs_jetScale {K : ℝ} (hK : K ≠ 0) (h : ℝ) (ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) :
    normHiggs D (h, 1, jetScale K ξ) = K ^ 2 * normHiggs D (h * K, K⁻¹, ξ) := by
  unfold normHiggs
  simp only [nuHiggsLinkJet_jetScale D hK h ξ]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, jetScale]
  rw [mul_sub, mul_neg]
  simp only [Finset.mul_sum]
  congr 1
  · congr 1
    refine sum_congr rfl fun μ _ => sum_congr rfl fun ν _ => ?_
    ring
  · field_simp

/-- The spin-link quotient: `W(h, 1; Kω, A) = K W(hK, K⁻¹; ω, A)`. -/
theorem nuSpinQuot_scale {K : ℝ} (hK : K ≠ 0) (h : ℝ) (om : Mat) (A : 𝔄) :
    nuSpinQuot D h 1 (K • om) A = K • nuSpinQuot D (h * K) K⁻¹ om A := by
  unfold nuSpinQuot
  rw [map_smul, ShiftedPlaquette.linkExp_smul]
  simp only [mul_one, one_smul, smul_add, smul_smul, mul_inv_cancel₀ hK,
    show h * K * K⁻¹ = h by field_simp, smul_mul_assoc, one_smul]
  module

/-- The inverse spin-link quotient: `W'(h, 1; Kω, A) = K W'(hK, K⁻¹; ω, A)`. -/
theorem nuSpinQuotInv_scale {K : ℝ} (hK : K ≠ 0) (h : ℝ) (om : Mat) (A : 𝔄) :
    nuSpinQuotInv D h 1 (K • om) A = K • nuSpinQuotInv D (h * K) K⁻¹ om A := by
  unfold nuSpinQuotInv
  rw [map_smul, ← smul_neg, ShiftedPlaquette.linkExp_smul]
  simp only [mul_one, one_smul, smul_add, smul_smul, mul_inv_cancel₀ hK,
    show h * K * K⁻¹ = h by field_simp, mul_smul_comm, one_smul]
  module

theorem jetOmega_jetScale (K : ℝ) (ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) (μ : Fin 4) :
    jetOmega μ (jetScale K ξ) = K • jetOmega μ ξ := by
  unfold jetOmega
  rw [← NativeScaling.readerOmega_smul]
  rfl

theorem nuDiracDiffJet_jetScale {K : ℝ} (hK : K ≠ 0) (h : ℝ)
    (ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) (μ : Fin 4) :
    nuDiracDiffJet D μ (h, 1, jetScale K ξ) = K • nuDiracDiffJet D μ (h * K, K⁻¹, ξ) := by
  unfold nuDiracDiffJet nuDiracDiff
  simp only []
  rw [jetOmega_jetScale, nuSpinQuot_scale D hK]
  simp only [jetScale, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_add,
    ContinuousLinearMap.smul_apply]

theorem nuDiracDiffBarJet_jetScale {K : ℝ} (hK : K ≠ 0) (h : ℝ)
    (ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) (μ : Fin 4) :
    nuDiracDiffBarJet D μ (h, 1, jetScale K ξ) = K • nuDiracDiffBarJet D μ (h * K, K⁻¹, ξ) := by
  unfold nuDiracDiffBarJet nuDiracDiffBar
  simp only []
  rw [jetOmega_jetScale, nuSpinQuotInv_scale D hK]
  simp only [jetScale, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_add,
    ContinuousLinearMap.comp_smul]

/-- Dirac: `𝓛̃_D(h, 1, (v, Kq)) = K 𝓛̃_D(hK, K⁻¹, (v, q))`. -/
theorem normD_jetScale {K : ℝ} (hK : K ≠ 0) (h : ℝ) (ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) :
    normD D (h, 1, jetScale K ξ) = K * normD D (h * K, K⁻¹, ξ) := by
  unfold normD
  simp only [nuDiracDiffJet_jetScale D hK h ξ, nuDiracDiffBarJet_jetScale D hK h ξ, map_smul,
    ContinuousLinearMap.smul_apply]
  have := dirac_scaling_aux hK (volume ((jetScale K ξ).1 none).1)
    (fun μ => (ξ.1 none).2.2.2.2 (gammaMu D μ (ξ.1 none).1 (nuDiracDiffJet D μ (h * K, K⁻¹, ξ))))
    (fun μ => nuDiracDiffBarJet D μ (h * K, K⁻¹, ξ) (gammaMu D μ (ξ.1 none).1 (ξ.1 none).2.2.2.1))
    ((ξ.1 none).2.2.2.2 (D.yukawa (ξ.1 none).2.2.1 (ξ.1 none).2.2.2.1))
  simp only [jetScale] at this ⊢
  simpa using this

/-! ### The normalised density `𝒢(ν, ρ, ξ)` -/

/-- **The normalised first-jet density** `𝒢(ν, ρ, ξ) = F_g^{(1)}(ρ, ξ) + (1 - ν²)(Λ/κ) v(e)
+ 𝓛̃_{YM}(ρ, ν, ξ) + 𝓛̃_H(ρ, ν, ξ) + ν 𝓛̃_D(ρ, ν, ξ)` of `lem:native-scaling` (bosonic part plus `ν`
times the Dirac part), as a function of `(ν, (ρ, ξ))`. -/
def scaledDensity (p : ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) : ℝ :=
  gravFirstJet D (p.2.1, p.2.2) + (1 - p.1 ^ 2) * (D.Λ / D.κ) * volume (p.2.2.1 none).1 +
    normYM D (p.2.1, p.1, p.2.2) + normHiggs D (p.2.1, p.1, p.2.2) +
    p.1 * normD D (p.2.1, p.1, p.2.2)

/-- **`lem:native-scaling` for the first-jet density** (`eq:native-density-scaling` on jets):
`F^{(1)}(h, (v, K q)) = K² 𝒢(K⁻¹, hK, (v, q))`. -/
theorem firstJetDensity_jetScale {K : ℝ} (hK : K ≠ 0) (h : ℝ)
    (ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) :
    firstJetDensity D (h, jetScale K ξ) = K ^ 2 * scaledDensity D (K⁻¹, (h * K, ξ)) := by
  unfold firstJetDensity scaledDensity
  simp only []
  rw [gravFirstJet_jetScale, normYM_jetScale D hK, normHiggs_jetScale D hK, normD_jetScale D hK]
  field_simp

/-- **Regularity of the normalised density** at the mesh origin, for every `ν`. -/
theorem contDiffAt_scaledDensity {ν : ℝ} {ξ : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)} (hc : JetChart ξ) :
    ContDiffAt ℝ ∞ (scaledDensity D) (ν, ((0 : ℝ), ξ)) := by
  have hg : ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) =>
      gravFirstJet D (p.2.1, p.2.2)) (ν, ((0 : ℝ), ξ)) :=
    ContDiffAt.comp (x := (ν, ((0 : ℝ), ξ))) (g := gravFirstJet D)
      (f := fun p : ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) => (p.2.1, p.2.2))
      (contDiffAt_gravFirstJet D (q := ((0 : ℝ), ξ)) rfl hc) (by fun_prop)
  have hv : ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) =>
      volume (p.2.2.1 none).1) (ν, ((0 : ℝ), ξ)) :=
    ContDiffAt.comp (x := (ν, ((0 : ℝ), ξ))) (g := volume)
      (f := fun p : ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) => (p.2.2.1 none).1)
      (contDiffAt_volume (k := ∞) (hc none)) (by fun_prop)
  have hproj : ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) =>
      ((p.2.1, p.1, p.2.2) : ℝ × ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) (ν, ((0 : ℝ), ξ)) := by
    fun_prop
  have hy : ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) =>
      normYM D (p.2.1, p.1, p.2.2)) (ν, ((0 : ℝ), ξ)) :=
    ContDiffAt.comp (x := (ν, ((0 : ℝ), ξ))) (g := normYM D)
      (contDiffAt_normYM D (p := ((0 : ℝ), ν, ξ)) rfl (hc none)) hproj
  have hH : ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) =>
      normHiggs D (p.2.1, p.1, p.2.2)) (ν, ((0 : ℝ), ξ)) :=
    ContDiffAt.comp (x := (ν, ((0 : ℝ), ξ))) (g := normHiggs D)
      (contDiffAt_normHiggs D (p := ((0 : ℝ), ν, ξ)) (hc none)) hproj
  have hD : ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × NativeDensity.Jet (Field 𝔄 𝓗 𝓢)) =>
      normD D (p.2.1, p.1, p.2.2)) (ν, ((0 : ℝ), ξ)) :=
    ContDiffAt.comp (x := (ν, ((0 : ℝ), ξ))) (g := normD D)
      (contDiffAt_normD D (p := ((0 : ℝ), ν, ξ)) (hc none)) hproj
  unfold scaledDensity
  refine (((hg.add ?_).add hy).add hH).add ?_
  · exact ((contDiffAt_const.sub (contDiffAt_fst.pow 2)).mul contDiffAt_const).mul hv
  · exact contDiffAt_fst.mul hD


/-! ### Shifts, stencils and actions under the scaling -/

/-- Integer lifts of the stencil shifts `0, ±e_μ`. -/
def shiftZ : Shift → Fin 4 → ℤ
  | none => 0
  | some (true, μ) => Pi.single μ 1
  | some (false, μ) => -Pi.single μ 1

variable {n : ℕ} [NeZero n]

theorem castVec_shiftZ : (fun s => castVec (shiftZ s) : Shift → Grid n) = shiftVec n := by
  funext s
  rcases s with _ | ⟨_ | _, μ⟩
  · funext ν; simp [shiftZ, castVec, shiftVec]
  · simp only [shiftZ, shiftVec, castVec_neg, castVec_single]
  · simp only [shiftZ, shiftVec, castVec_single]

theorem abs_shiftZ_le (s : Shift) (μ : Fin 4) : |((shiftZ s μ : ℤ) : ℝ)| ≤ 1 := by
  rcases s with _ | ⟨_ | _, ν⟩
  · simp [shiftZ]
  · by_cases h : μ = ν
    · subst h; simp [shiftZ]
    · simp [shiftZ, Pi.single_apply, h]
  · by_cases h : μ = ν
    · subst h; simp [shiftZ]
    · simp [shiftZ, Pi.single_apply, h]

theorem stencil_jetScale {h K : ℝ} (hK : K ≠ 0) (x : Grid n) (y : Grid n → Field 𝔄 𝓗 𝓢) :
    stencil h (shiftVec n) x y = jetScale K (stencil (h * K) (shiftVec n) x y) := by
  rw [ShiftedJetAction.stencil_apply, ShiftedJetAction.stencil_apply]
  simp only [jetScale]
  congr 1
  funext p
  exact NativeScaling.fwdDiff_scale hK p.2 y _

/-- The first-jet action at mesh `h` is `K² h⁴/ρ⁴` times the normalised action at mesh `ρ = hK`. -/
theorem action_firstJet_eq_scaled {h K : ℝ} (hh : h ≠ 0) (hK : K ≠ 0)
    (y : Grid n → Field 𝔄 𝓗 𝓢) :
    action (fun ξ => firstJetDensity D (h, ξ)) h (shiftVec n) y =
      (h ^ 4 * K ^ 2 / (h * K) ^ 4) *
        action (fun ξ => scaledDensity D (K⁻¹, (h * K, ξ))) (h * K) (shiftVec n) y := by
  unfold action
  simp only [stencil_jetScale (h := h) hK, firstJetDensity_jetScale D hK, ← Finset.mul_sum]
  have : (h * K) ^ 4 ≠ 0 := pow_ne_zero 4 (mul_ne_zero hh hK)
  field_simp

/-- The continuum density is `K²` times the normalised one at the rescaled first jet. -/
theorem limDensity_eq_scaled {K : ℝ} (hK : K ≠ 0) (wp : Field 𝔄 𝓗 𝓢 × (Fin 4 → Field 𝔄 𝓗 𝓢)) :
    limDensity (ι := Shift) (firstJetDensity D) wp =
      K ^ 2 * limDensity (ι := Shift) (fun q => scaledDensity D (K⁻¹, q))
        (scalePE (Field 𝔄 𝓗 𝓢) hK wp) := by
  unfold limDensity
  have hc : (cmap wp : DiscreteEulerConsistency.Jet Shift (Field 𝔄 𝓗 𝓢)) =
      jetScale K (cmap (scalePE (Field 𝔄 𝓗 𝓢) hK wp)) := by
    rw [scalePE_apply]
    simp only [cmap_apply, jetScale]
    congr 1
    funext q
    simp [smul_smul, mul_inv_cancel₀ hK]
  rw [hc, firstJetDensity_jetScale D hK, zero_mul]


/-! ### The Cartan logarithm chart on growing-band samples -/

omit [NeZero n] in
/-- A uniform bound for the torsion-free reader connection on a compact coframe chart. -/
theorem exists_readerOmega_bound {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (B : ℝ) : ∃ R : ℝ, 0 ≤ R ∧ ∀ e ∈ Ke, ∀ q : Fin 4 → Mat, ‖q‖ ≤ B → ∀ μ,
      ‖readerOmega e q μ‖ ≤ R := by
  have hc : IsCompact (Ke ×ˢ closedBall (0 : Fin 4 → Mat) B) := hKe.prod (isCompact_closedBall _ _)
  have hcont : ContinuousOn (fun p : Mat × (Fin 4 → Mat) => ∑ μ, ‖readerOmega p.1 p.2 μ‖)
      (Ke ×ˢ closedBall (0 : Fin 4 → Mat) B) := by
    refine continuousOn_finsetSum _ fun μ _ => ?_
    intro p hp
    have he : p.1.det ≠ 0 := (hdet _ hp.1).ne'
    have hμ : ContinuousAt (fun p : Mat × (Fin 4 → Mat) => readerOmega p.1 p.2 μ) p := by
      refine continuousAt_pi.mpr fun a => continuousAt_pi.mpr fun b => ?_
      exact (contDiffAt_readerOmega_entry μ a b he).continuousAt
    exact hμ.norm.continuousWithinAt
  obtain ⟨R, hR⟩ := hc.exists_bound_of_continuousOn hcont
  refine ⟨max R 0, le_max_right _ _, fun e he q hq μ => ?_⟩
  have h1 := hR (e, q) ⟨he, by rw [mem_closedBall, dist_zero_right]; exact hq⟩
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h1
  exact ((Finset.single_le_sum (f := fun μ => ‖readerOmega e q μ‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ μ)).trans h1).trans (le_max_left _ _)

/-! ### `prop:native-consistency` -/

variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

/-- **`prop:native-consistency` (`eq:native-consistency`), growing-band consistency of the
unchanged finite action.**  Let `K_e` be a compact coframe chart inside `{det e > 0}` (uniformly
bounded inverse metric), `A` an amplitude bound and `B` a band constant.  There are constants `C`
and `c_res > 0` (depending only on the chart, `A`, `B` and the coefficient bank `D`) such that for
every `K ≥ 1`, every mesh `h > 0` with `hK ≤ c_res`, every grid size `n` and every `C³` field tuple
`y : ℝ⁴ → (e, A, H, Ψ, Ψ̄)` of period `n h` with coframe values in `K_e`, `|y| ≤ A` and
`‖D^j y‖ ≤ B K^j` (`j = 1, 2, 3`):
1. the samples `𝖲_h y` lie on the oriented chart and on the Cartan logarithm chart (so the local
   action is evaluated where it is defined);
2. at **every** node `x`,
   `‖E_h^{raw}(𝖲_h y)(x) - 𝓔₀(y)(h x̃)‖ ≤ C h K³`,
where `E_h^{raw}` is the raw Euler row of `S_h^{loc}` (`NativeDensity.localAction`) and `𝓔₀` the
continuum Euler–Lagrange expression of the continuum Lagrangian `L₀ = F^{(1)}_0` (all four
sectors). -/
theorem native_consistency {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (A B : ℝ) :
    ∃ C c_res : ℝ, 0 < c_res ∧ ∀ K : ℝ, 1 ≤ K → ∀ h : ℝ, 0 < h → h * K ≤ c_res →
      ∀ (n : ℕ) [NeZero n] (Y : R4 → Field 𝔄 𝓗 𝓢), ContDiff ℝ 3 Y →
        IsPeriodic ((n : ℝ) * h) Y → (∀ z, (Y z).1 ∈ Ke) → (∀ z, ‖Y z‖ ≤ A) →
        (∀ z, ‖iteratedFDeriv ℝ 1 Y z‖ ≤ B * K) → (∀ z, ‖iteratedFDeriv ℝ 2 Y z‖ ≤ B * K ^ 2) →
        (∀ z, ‖iteratedFDeriv ℝ 3 Y z‖ ≤ B * K ^ 3) →
        (∀ x, 0 < (coframe (samp h Y : Grid n → Field 𝔄 𝓗 𝓢) x).det) ∧
        (∀ x μ ν, ‖cartanPlaquette h (coframe (samp h Y : Grid n → Field 𝔄 𝓗 𝓢)) x μ ν - 1‖ < 1) ∧
        ∀ x : Grid n, ‖eulerRow (localAction D h) h (samp h Y) x -
          contEuler (limDensity (ι := Shift) (firstJetDensity D)) Y (pos h x)‖ ≤ C * h * K ^ 3 := by
  set Bp := max B 0 with hBp
  have hBp0 : 0 ≤ Bp := le_max_right _ _
  -- the compact set of continuum jets
  set Kw : Set (Field 𝔄 𝓗 𝓢) := {w | w.1 ∈ Ke} ∩ closedBall 0 A with hKw
  have hKwc : IsCompact Kw := by
    refine isCompact_of_isClosed_isBounded ?_ (isBounded_closedBall.subset inter_subset_right)
    · exact (hKe.isClosed.preimage continuous_fst).inter isClosed_closedBall
  set S : Set (DiscreteEulerConsistency.Jet Shift (Field 𝔄 𝓗 𝓢)) :=
    (fun wp => cmap wp) '' (Kw ×ˢ closedBall (0 : Fin 4 → Field 𝔄 𝓗 𝓢) Bp) with hS
  have hSc : IsCompact S := (hKwc.prod (isCompact_closedBall _ _)).image cmap.continuous
  have hG : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ c ∈ S, ContDiffAt ℝ 3 (scaledDensity D) (θ, ((0 : ℝ), c)) := by
    rintro θ - c ⟨wp, hwp, rfl⟩
    refine (contDiffAt_scaledDensity D (fun s => ?_)).of_le
      (WithTop.coe_le_coe.mpr le_top)
    exact (hdet _ hwp.1.1).ne'
  obtain ⟨δ, hδ, M₂, M₃, hreg⟩ := exists_densityReg (scaledDensity D) isCompact_Icc hSc hG
  obtain ⟨R, hR0, hR⟩ := exists_readerOmega_bound hKe hdet Bp
  set c₁ := cJet Bp Bp 1
  have hc₁ : 0 ≤ c₁ := by unfold c₁ cJet; positivity
  set c_res := min (δ / (2 * (1 + c₁))) (1 / (64 * (R + 1))) with hcres
  refine ⟨eulerConst M₂ M₃ Bp Bp Bp 1 (Fintype.card Shift), c_res, by positivity, ?_⟩
  intro K hK h hh hhK n _ Y hYs hper hYe hYA h1 h2 h3
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hKne : K ≠ 0 := hK0.ne'
  set ρ := h * K with hρ
  have hρ0 : 0 < ρ := mul_pos hh hK0
  set Yt : R4 → Field 𝔄 𝓗 𝓢 := fun z => Y (K⁻¹ • z) with hYt
  -- field bounds
  have hB : ∀ j : ℕ, ∀ z, ‖iteratedFDeriv ℝ j Y z‖ ≤ B * K ^ j → ‖iteratedFDeriv ℝ j Y z‖ ≤ Bp * K ^ j :=
    fun j z hz => hz.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hFY : FieldBound Y (Bp * K) (Bp * K ^ 2) (Bp * K ^ 3) :=
    fieldBound_of_iteratedFDeriv hYs (fun z => by simpa using hB 1 z (by simpa using h1 z))
      (fun z => hB 2 z (h2 z)) (fun z => hB 3 z (h3 z))
  have hFYt : FieldBound Yt Bp Bp Bp := hFY.rescale hK0 hBp0
  have hpert : IsPeriodic ((n : ℝ) * ρ) Yt := by
    have := hper.rescale (K := K) hKne
    rw [show (n : ℝ) * ρ = K * ((n : ℝ) * h) by rw [hρ]; ring]
    exact this
  have hSY : ∀ z, cmap (jet1 Yt z) ∈ S := by
    intro z
    refine ⟨jet1 Yt z, ⟨⟨hYe _, ?_⟩, ?_⟩, rfl⟩
    · rw [mem_closedBall, dist_zero_right]; exact hYA _
    · rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hBp0]
      intro μ
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [norm_evec, mul_one]
      exact hFYt.b1 z
  have hν : K⁻¹ ∈ Icc (0 : ℝ) 1 := ⟨inv_nonneg.mpr hK0.le, inv_le_one_of_one_le₀ hK⟩
  have hρδ : ρ * (1 + cJet Bp Bp 1) < δ := by
    have h1' : ρ ≤ δ / (2 * (1 + c₁)) := hhK.trans (min_le_left _ _)
    have hpos : 0 < 1 + c₁ := by linarith
    calc ρ * (1 + cJet Bp Bp 1) ≤ δ / (2 * (1 + c₁)) * (1 + c₁) :=
          mul_le_mul_of_nonneg_right h1' hpos.le
      _ = δ / 2 := by field_simp
      _ < δ := by linarith
  -- the generic estimate for the normalised density
  have hmain := norm_eulerRow_sub_contEuler_le (n := n) (hreg K⁻¹ hν) hFYt hSY zero_le_one
    (fun s μ => abs_shiftZ_le s μ) hρ0 hpert hρδ
  rw [castVec_shiftZ, samp_rescale hKne] at hmain
  -- the charts
  set y : Grid n → Field 𝔄 𝓗 𝓢 := samp h Y with hy
  have hdet' : ∀ x, 0 < (coframe y x).det := fun x => hdet _ (hYe _)
  have hdiffb : ∀ (x : Grid n) (lam : Fin 4),
      ‖ShiftedJetAction.fwdDiff ρ lam y x‖ ≤ Bp := by
    intro x lam
    have hst := stencil_samp' (σZ := shiftZ) hpert x
    rw [castVec_shiftZ, samp_rescale hKne] at hst
    have hcomp := congrArg (fun ξ : DiscreteEulerConsistency.Jet Shift (Field 𝔄 𝓗 𝓢) =>
      ξ.2 (none, lam)) hst
    simp only [ShiftedJetAction.stencil_apply, shiftVec_none, add_zero, discJet] at hcomp
    rw [hcomp]
    have hz : realVec (shiftZ none) = 0 := by funext μ; simp [realVec, shiftZ]
    rw [hz, smul_zero, add_zero, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ0.le)]
    have := hFYt.lip0 (pos ρ x) (pos ρ x + ρ • evec lam)
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ0.le, norm_evec, mul_one] at this
    calc ρ⁻¹ * ‖Yt (pos ρ x + ρ • evec lam) - Yt (pos ρ x)‖ ≤ ρ⁻¹ * (Bp * ρ) := by gcongr
      _ = Bp := by field_simp
  have hmar : ∀ x μ, h * ‖omegaLink h (coframe y) x μ‖ ≤ 1 / 64 := by
    intro x μ
    have hω : omegaLink h (coframe y) x μ =
        K • readerOmega (coframe y x) (fun lam => ShiftedJetAction.fwdDiff ρ lam (coframe y) x) μ := by
      unfold omegaLink
      rw [← NativeScaling.readerOmega_smul]
      congr 1
      funext lam
      exact NativeScaling.fwdDiff_scale hKne lam (coframe y) x
    have hq : ‖(fun lam => ShiftedJetAction.fwdDiff ρ lam (coframe y) x)‖ ≤ Bp := by
      rw [pi_norm_le_iff_of_nonneg hBp0]
      intro lam
      rw [← fwdDiff_coframe]
      exact (norm_fst_le _).trans (hdiffb x lam)
    have hRb := hR (coframe y x) (hYe (pos h x)) _ hq μ
    rw [hω, norm_smul, Real.norm_of_nonneg hK0.le, ← mul_assoc]
    have h2' : ρ ≤ 1 / (64 * (R + 1)) := hhK.trans (min_le_right _ _)
    calc h * K * ‖readerOmega (coframe y x) (fun lam => ShiftedJetAction.fwdDiff ρ lam (coframe y) x) μ‖
        ≤ 1 / (64 * (R + 1)) * R := mul_le_mul h2' hRb (norm_nonneg _) (by positivity)
      _ ≤ 1 / 64 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hlog : ∀ x μ ν, ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1 :=
    fun x μ ν => NativeGravityFirstJet.cartan_log_lt hh (le_refl _) (coframe y) hmar x μ ν
  refine ⟨hdet', hlog, fun x => ?_⟩
  -- identification of the two rows
  have hrow : eulerRow (localAction D h) h y x =
      K ^ 2 • eulerRow (action (fun ξ => scaledDensity D (K⁻¹, (ρ, ξ))) ρ (shiftVec n)) ρ y x := by
    have e1 : eulerRow (localAction D h) h y x =
        eulerRow (action (fun ξ => firstJetDensity D (h, ξ)) h (shiftVec n)) h y x := by
      unfold eulerRow
      erw [fderiv_localAction_eq D hh.ne' hdet' hlog]
      rfl
    rw [e1, eulerRow_smul_action (fun y' => action_firstJet_eq_scaled D hh.ne' hKne y') y x
      hρ0.ne' hh.ne']
    congr 1
    rw [hρ]
    field_simp
  have hYY : Y = fun z => Yt (K • z) := by
    funext z; simp only [hYt, smul_smul, inv_mul_cancel₀ hKne, one_smul]
  have hcont : contEuler (limDensity (ι := Shift) (firstJetDensity D)) Y (pos h x) =
      K ^ 2 • contEuler (limDensity (ι := Shift) (fun q => scaledDensity D (K⁻¹, q))) Yt
        (pos ρ x) := by
    rw [hYY, contEuler_scale hKne (limDensity_eq_scaled D hKne) Yt (pos h x), pos_mul]
  rw [hrow, hcont]
  set X := eulerRow (action (fun ξ => scaledDensity D (K⁻¹, (ρ, ξ))) ρ (shiftVec n)) ρ y x
  set Z := contEuler (limDensity (ι := Shift) (fun q => scaledDensity D (K⁻¹, q))) Yt (pos ρ x)
  have e : K ^ 2 • X - K ^ 2 • Z = K ^ 2 • (X - Z) := by module
  rw [e]
  refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
  rw [Real.norm_of_nonneg (by positivity)]
  calc K ^ 2 * ‖eulerRow (action (fun ξ => scaledDensity D (K⁻¹, (ρ, ξ))) ρ (shiftVec n)) ρ y x -
        contEuler (limDensity (ι := Shift) (fun q => scaledDensity D (K⁻¹, q))) Yt (pos ρ x)‖
      ≤ K ^ 2 * (eulerConst M₂ M₃ Bp Bp Bp 1 (Fintype.card Shift) * ρ) := by
        gcongr
        exact hmain x
    _ = eulerConst M₂ M₃ Bp Bp Bp 1 (Fintype.card Shift) * h * K ^ 3 := by rw [hρ]; ring


/-! ### The Cartan clause `eq:native-Cartan` -/

section Cartan

omit [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢] [NeZero n]

theorem norm_cmap_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (wp : V × (Fin 4 → V)) : ‖(cmap wp : DiscreteEulerConsistency.Jet Shift V)‖ ≤ ‖wp‖ := by
  rw [cmap_apply, Prod.norm_def]
  refine max_le ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro _
    exact norm_fst_le wp
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro q
    exact (norm_le_pi_norm wp.2 q.2).trans (norm_snd_le wp)

theorem norm_dJet_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {Y : R4 → V}
    {B₁ B₂ B₃ : ℝ} (hY : FieldBound Y B₁ B₂ B₃) (z : R4) :
    ‖(dJet Y z : R4 →L[ℝ] DiscreteEulerConsistency.Jet Shift V)‖ ≤ B₁ + B₂ := by
  have h2 : ‖fderiv ℝ (fderiv ℝ Y) z‖ ≤ B₂ :=
    norm_fderiv_le_of_lip' ℝ hY.B₂_nonneg (Eventually.of_forall fun x => hY.lip1 z x)
  refine ContinuousLinearMap.opNorm_le_bound _ (add_nonneg hY.B₁_nonneg hY.B₂_nonneg) fun v => ?_
  unfold dJet
  rw [ContinuousLinearMap.comp_apply]
  refine (norm_cmap_le _).trans ?_
  rw [ContinuousLinearMap.prod_apply, Prod.norm_def]
  have hv := norm_nonneg v
  refine max_le ?_ ?_
  · calc ‖fderiv ℝ Y z v‖ ≤ ‖fderiv ℝ Y z‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (B₁ + B₂) * ‖v‖ := by gcongr; linarith [hY.b1 z, hY.B₂_nonneg]
  · rw [pi_norm_le_iff_of_nonneg (by have := hY.B₁_nonneg; have := hY.B₂_nonneg; positivity)]
    intro μ
    simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply]
    calc ‖fderiv ℝ (fderiv ℝ Y) z v (evec μ)‖ ≤ ‖fderiv ℝ (fderiv ℝ Y) z v‖ * ‖evec μ‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ Y) z‖ * ‖v‖) * 1 := by
          rw [norm_evec]; gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (B₁ + B₂) * ‖v‖ := by
          rw [mul_one]; gcongr; linarith [hY.B₁_nonneg]

/-- The torsion-free reader (Levi-Civita spin) connection `ω_μ(z) = Ω_μ(e(z), ∂e(z))` of a smooth
coframe field. -/
def omega0 (e : R4 → Mat) (z : R4) (μ : Fin 4) : Mat :=
  readerOmega (e z) (fun lam => fderiv ℝ e z (evec lam)) μ

/-- **The continuum Cartan curvature** `R_{μν} = ∂_μ ω_ν - ∂_ν ω_μ + [ω_μ, ω_ν]` of the
torsion-free reader connection (the curvature of `g = eᵀ η e` in the coframe, by the Cartan
structure equation), as an operator on `ℝ⁴`. -/
def contCartan (e : R4 → Mat) (z : R4) (μ ν : Fin 4) : Op :=
  matToOp (fderiv ℝ (fun z => omega0 e z ν) z (evec μ) - fderiv ℝ (fun z => omega0 e z μ) z (evec ν) +
    (omega0 e z μ * omega0 e z ν - omega0 e z ν * omega0 e z μ))

theorem omega0_scale {e : R4 → Mat} {K : ℝ} (z : R4) (μ : Fin 4) :
    omega0 (fun z => e (K • z)) z μ = K • omega0 e (K • z) μ := by
  unfold omega0
  rw [← NativeScaling.readerOmega_smul]
  congr 1
  funext lam
  have := fderiv_comp_smul (𝕜 := ℝ) (f := e) (x := z) K
  erw [this]
  rfl

/-- **Scaling of the continuum Cartan curvature**: `R[e(K·)](z) = K² R[e](K z)`. -/
theorem contCartan_scale {e : R4 → Mat} {K : ℝ} (hK : K ≠ 0) (z : R4) (μ ν : Fin 4) :
    contCartan (fun z => e (K • z)) z μ ν = K ^ 2 • contCartan e (K • z) μ ν := by
  haveI : Invertible K := invertibleOfNonzero hK
  have hd : ∀ ν', fderiv ℝ (fun z => omega0 (fun z => e (K • z)) z ν') z =
      K • (K • fderiv ℝ (fun z => omega0 e z ν') (K • z)) := by
    intro ν'
    have h1 : (fun z => omega0 (fun z => e (K • z)) z ν') =
        K • fun z => omega0 e (K • z) ν' := funext fun z => omega0_scale z ν'
    rw [h1]
    have e1 := fderiv_const_smul_of_invertible (𝕜 := ℝ) (f := fun z => omega0 e (K • z) ν')
      (x := z) K
    have e2 := fderiv_comp_smul (𝕜 := ℝ) (f := fun z => omega0 e z ν') (x := z) K
    erw [e1, e2]
    rfl
  unfold contCartan
  rw [hd, hd, omega0_scale, omega0_scale, ← map_smul]
  congr 1
  simp only [ContinuousLinearMap.smul_apply, smul_mul_smul_comm, smul_smul, ← sq, smul_add,
    smul_sub]

end Cartan


/-! ### `eq:native-Cartan` -/

section CartanMain

/-- The jet connection map `q ↦ (ν ↦ ω_ν(q))` as operators on `ℝ⁴`. -/
def omegaJet (q : ℝ × DiscreteEulerConsistency.Jet Shift (Field 𝔄 𝓗 𝓢)) : Fin 4 → Op :=
  fun ν => matToOp (jetOmega ν q.2)

theorem contDiffAt_omegaJet {q : ℝ × DiscreteEulerConsistency.Jet Shift (Field 𝔄 𝓗 𝓢)}
    (hq : (q.2.1 none).1.det ≠ 0) : ContDiffAt ℝ 2 (omegaJet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)) q := by
  refine contDiffAt_pi.mpr fun ν => ?_
  have h1 : ContDiffAt ℝ 2 (fun q : ℝ × DiscreteEulerConsistency.Jet Shift (Field 𝔄 𝓗 𝓢) =>
      jetOmega ν q.2) q :=
    ContDiffAt.comp (x := q) (g := jetOmega ν) (f := Prod.snd)
      ((contDiffAt_jetOmega ν hq).of_le (WithTop.coe_le_coe.mpr le_top)) contDiffAt_snd
  exact (matToOpL.contDiff.contDiffAt (x := jetOmega ν q.2)).comp q h1

/-- The coframe part of a field and the continuum connection. -/
theorem omegaJet_cmap_jet1 {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : Differentiable ℝ Y) (z : R4) :
    omegaJet ((0 : ℝ), cmap (jet1 Y z)) = fun ν => matToOp (omega0 (fun z => (Y z).1) z ν) := by
  funext ν
  have hd : fderiv ℝ (fun z => (Y z).1) z =
      (ContinuousLinearMap.fst ℝ Mat ((Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢)).comp (fderiv ℝ Y z) :=
    ((ContinuousLinearMap.fst ℝ Mat ((Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢)).hasFDerivAt.comp z
      (hY z).hasFDerivAt).fderiv
  have hfun : (fun lam => (fderiv ℝ Y z (evec lam)).1) =
      fun lam => fderiv ℝ (fun z => (Y z).1) z (evec lam) := by
    funext lam; rw [hd]; rfl
  show matToOp (readerOmega (Y z).1 (fun lam => (fderiv ℝ Y z (evec lam)).1) ν) =
    matToOp (readerOmega (Y z).1 (fun lam => fderiv ℝ (fun z => (Y z).1) z (evec lam)) ν)
  rw [hfun]

theorem differentiableAt_omega0 {Y : R4 → Field 𝔄 𝓗 𝓢} {B₁ B₂ B₃ : ℝ}
    (hY : FieldBound Y B₁ B₂ B₃) {z : R4} (hz : (Y z).1.det ≠ 0) (ν : Fin 4) :
    DifferentiableAt ℝ (fun z => omega0 (fun z => (Y z).1) z ν) z := by
  have h1 : (fun z => omega0 (fun z => (Y z).1) z ν) =
      fun z => jetOmega ν (cmap (jet1 Y z) : DiscreteEulerConsistency.Jet Shift (Field 𝔄 𝓗 𝓢)) := by
    funext z'
    have := congrFun (omegaJet_cmap_jet1 (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) hY.diff0 z') ν
    simp only [omegaJet] at this
    exact (matToOp_injective this).symm
  rw [h1]
  exact ((contDiffAt_jetOmega ν hz).differentiableAt (by simp)).comp z
    (hasFDerivAt_jet (ι := Shift) hY z).differentiableAt
where
  matToOp_injective {M N : Mat} (h : matToOp M = matToOp N) : M = N := by
    ext a b
    have := congrArg (fun T => opEntry T a b) h
    simpa [opEntry_matToOp] using this


theorem norm_tuple5_le (a b : ℝ × Op × Op × Op × Op) {M : ℝ} (h1 : ‖a.1 - b.1‖ ≤ M)
    (h2 : ‖a.2.1 - b.2.1‖ ≤ M) (h3 : ‖a.2.2.1 - b.2.2.1‖ ≤ M) (h4 : ‖a.2.2.2.1 - b.2.2.2.1‖ ≤ M)
    (h5 : ‖a.2.2.2.2 - b.2.2.2.2‖ ≤ M) : ‖a - b‖ ≤ M := by
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
  exact max_le h1 (max_le h2 (max_le h3 (max_le h4 h5)))

/-- The continuum Cartan curvature is the `h = 0` plaquette map at the continuum connection. -/
theorem contCartan_eq_jointLogPlaquette (e : R4 → Mat) (z : R4) (μ ν : Fin 4) :
    contCartan e z μ ν = jointLogPlaquette ((0 : ℝ), matToOp (omega0 e z μ),
      matToOp (omega0 e z ν), matToOp (fderiv ℝ (fun z => omega0 e z ν) z (evec μ)),
      matToOp (fderiv ℝ (fun z => omega0 e z μ) z (evec ν))) := by
  rw [← jointLogPlaquette_eq, logPlaquette_zero]
  unfold contCartan curvature
  simp only [map_add, map_sub, map_mul]

set_option maxHeartbeats 2000000 in
/-- **`eq:native-Cartan`, growing-band consistency of the literal Cartan plaquette curvature.**
Under the hypotheses of `native_consistency` there are constants `C`, `c_res > 0` such that the
literal Cartan curvature `R^h_{μν}(x) = h⁻² log(L_μ L_ν L_μ⁻¹ L_ν⁻¹)` of the samples is uniformly
`C h K³`-close to the continuum Cartan curvature `R_{μν} = dω + ω ∧ ω` of the torsion-free
coframe connection, **at every point `z` of the cell** `‖z - h x̃‖ ≤ h` of every node `x`; in
particular the piecewise-constant reconstruction `I_h^0 R_h^{raw}` is within `C h K³` of `R` in
`L^∞`, hence in `L²(Q)` with constant `C |Q|^{1/2}` on every bounded region `Q`. -/
theorem native_cartan_consistency {Ke : Set Mat} (hKe : IsCompact Ke)
    (hdet : ∀ e ∈ Ke, 0 < e.det) (A B : ℝ) :
    ∃ C c_res : ℝ, 0 < c_res ∧ ∀ K : ℝ, 1 ≤ K → ∀ h : ℝ, 0 < h → h * K ≤ c_res →
      ∀ (n : ℕ) [NeZero n] (Y : R4 → Field 𝔄 𝓗 𝓢), ContDiff ℝ 3 Y →
        IsPeriodic ((n : ℝ) * h) Y → (∀ z, (Y z).1 ∈ Ke) → (∀ z, ‖Y z‖ ≤ A) →
        (∀ z, ‖iteratedFDeriv ℝ 1 Y z‖ ≤ B * K) → (∀ z, ‖iteratedFDeriv ℝ 2 Y z‖ ≤ B * K ^ 2) →
        (∀ z, ‖iteratedFDeriv ℝ 3 Y z‖ ≤ B * K ^ 3) →
        ∀ (x : Grid n) (z : R4), ‖z - pos h x‖ ≤ h → ∀ μ ν : Fin 4,
          ‖cartanCurvature h (coframe (samp h Y : Grid n → Field 𝔄 𝓗 𝓢)) x μ ν -
            contCartan (fun z => (Y z).1) z μ ν‖ ≤ C * h * K ^ 3 := by
  set Bp := max B 0 with hBp
  have hBp0 : 0 ≤ Bp := le_max_right _ _
  set Kw : Set (Field 𝔄 𝓗 𝓢) := {w | w.1 ∈ Ke} ∩ closedBall 0 A with hKw
  have hKwc : IsCompact Kw := by
    refine isCompact_of_isClosed_isBounded ?_ (isBounded_closedBall.subset inter_subset_right)
    exact (hKe.isClosed.preimage continuous_fst).inter isClosed_closedBall
  set S : Set (DiscreteEulerConsistency.Jet Shift (Field 𝔄 𝓗 𝓢)) :=
    (fun wp => cmap wp) '' (Kw ×ˢ closedBall (0 : Fin 4 → Field 𝔄 𝓗 𝓢) Bp) with hS
  have hSc : IsCompact S := (hKwc.prod (isCompact_closedBall _ _)).image cmap.continuous
  have hSdet : ∀ c ∈ S, (c.1 none).1.det ≠ 0 := by
    rintro c ⟨wp, hwp, rfl⟩
    exact (hdet _ hwp.1.1).ne'
  -- regularity of the connection map
  have hK0c : IsCompact (({(0 : ℝ)} : Set ℝ) ×ˢ S) := isCompact_singleton.prod hSc
  obtain ⟨δP, hδP, M₂, M₃, hM₂, hM₃, hPb⟩ := exists_C2_ball_bounds
    (f := omegaJet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)) hK0c (by
      rintro ⟨h0, c⟩ ⟨hh0, hc⟩
      rw [mem_singleton_iff] at hh0
      subst hh0
      exact contDiffAt_omegaJet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) (q := ((0 : ℝ), c)) (hSdet c hc))
  have hreg : MapReg (omegaJet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)) S δP M₂ M₃ :=
    ⟨fun c hc q hq => (hPb (0, c) ⟨rfl, hc⟩ q hq).1, fun c hc q hq => (hPb (0, c) ⟨rfl, hc⟩ q hq).2.1,
      fun c hc q hq q' hq' => (hPb (0, c) ⟨rfl, hc⟩ q hq).2.2 q' hq', hM₂, hM₃⟩
  -- bound on the connection values
  have hPcont : ContinuousOn (omegaJet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)) (({(0 : ℝ)} : Set ℝ) ×ˢ S) := by
    rintro ⟨h0, c⟩ ⟨hh0, hc⟩
    rw [mem_singleton_iff] at hh0
    subst hh0
    exact (ContDiffAt.continuousAt (contDiffAt_omegaJet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)
      (q := ((0 : ℝ), c)) (hSdet c hc))).continuousWithinAt
  obtain ⟨RP, hRP⟩ := hK0c.exists_bound_of_continuousOn hPcont
  set c₁ := cJet Bp Bp 1
  set c₂ := cJet' Bp Bp 1
  have hc₁ : 0 ≤ c₁ := by unfold c₁ cJet; positivity
  have hc₂ : 0 ≤ c₂ := by unfold c₂ cJet'; positivity
  set Cd := M₃ * (1 + c₁) * (Bp + Bp) + M₂ * c₂ with hCd
  have hCd0 : 0 ≤ Cd := by positivity
  -- Lipschitz bound of the plaquette map near `{0} × ball`
  set RR := max RP 0 + M₂ * (Bp + Bp) + 1 with hRR
  have hJc : IsCompact (({(0 : ℝ)} : Set ℝ) ×ˢ closedBall (0 : Op × Op × Op × Op) RR) :=
    isCompact_singleton.prod (isCompact_closedBall _ _)
  obtain ⟨δJ, hδJ, LJ, MJ, hLJ, -, hJb⟩ := exists_C2_ball_bounds
    (f := jointLogPlaquette (𝔄 := Op)) hJc (by
      rintro ⟨h0, w⟩ ⟨hh0, -⟩
      rw [mem_singleton_iff] at hh0
      subst hh0
      exact (analyticAt_jointLogPlaquette (by simp)).contDiffAt)
  set Cm := 1 + M₂ * (1 + c₁) + Cd with hCm
  have hCm1 : 1 ≤ Cm := by
    have := mul_nonneg hM₂ (by linarith : (0 : ℝ) ≤ 1 + c₁)
    rw [hCm]; linarith
  set c_res := min (δP / (2 * (1 + c₁))) (δJ / (2 * Cm)) with hcres
  refine ⟨LJ * Cm, c_res, by positivity, ?_⟩
  intro K hK h hh hhK n _ Y hYs hper hYe hYA h1 h2 h3 x z hz μ ν
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hKne : K ≠ 0 := hK0.ne'
  set ρ := h * K with hρ
  have hρ0 : 0 < ρ := mul_pos hh hK0
  set Yt : R4 → Field 𝔄 𝓗 𝓢 := fun z => Y (K⁻¹ • z) with hYt
  have hB : ∀ j : ℕ, ∀ z, ‖iteratedFDeriv ℝ j Y z‖ ≤ B * K ^ j → ‖iteratedFDeriv ℝ j Y z‖ ≤ Bp * K ^ j :=
    fun j z hz => hz.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hFY : FieldBound Y (Bp * K) (Bp * K ^ 2) (Bp * K ^ 3) :=
    fieldBound_of_iteratedFDeriv hYs (fun z => by simpa using hB 1 z (by simpa using h1 z))
      (fun z => hB 2 z (h2 z)) (fun z => hB 3 z (h3 z))
  have hFYt : FieldBound Yt Bp Bp Bp := hFY.rescale hK0 hBp0
  have hpert : IsPeriodic ((n : ℝ) * ρ) Yt := by
    have := hper.rescale (K := K) hKne
    rw [show (n : ℝ) * ρ = K * ((n : ℝ) * h) by rw [hρ]; ring]
    exact this
  have hSY : ∀ z, cmap (jet1 Yt z) ∈ S := by
    intro z
    refine ⟨jet1 Yt z, ⟨⟨hYe _, ?_⟩, ?_⟩, rfl⟩
    · rw [mem_closedBall, dist_zero_right]; exact hYA _
    · rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hBp0]
      intro μ
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [norm_evec, mul_one]
      exact hFYt.b1 z
  have hρδ : ρ * (1 + cJet Bp Bp 1) < δP := by
    have h1' : ρ ≤ δP / (2 * (1 + c₁)) := hhK.trans (min_le_left _ _)
    have hpos : 0 < 1 + c₁ := by linarith
    calc ρ * (1 + cJet Bp Bp 1) ≤ δP / (2 * (1 + c₁)) * (1 + c₁) :=
          mul_le_mul_of_nonneg_right h1' hpos.le
      _ = δP / 2 := by field_simp
      _ < δP := by linarith
  have hρJ : ρ * Cm < δJ := by
    have h2' : ρ ≤ δJ / (2 * Cm) := hhK.trans (min_le_right _ _)
    calc ρ * Cm ≤ δJ / (2 * Cm) * Cm := mul_le_mul_of_nonneg_right h2' (by linarith)
      _ = δJ / 2 := by field_simp
      _ < δJ := by linarith
  -- the scaled point and base points
  set y : Grid n → Field 𝔄 𝓗 𝓢 := samp h Y with hy
  have hyt : y = samp ρ Yt := (samp_rescale hKne).symm
  set ξ := K • z with hξ
  set p₀ := pos ρ x with hp₀
  have hξp : ‖p₀ - ξ‖ ≤ ρ := by
    rw [hp₀, hξ, pos_mul, ← smul_sub, norm_smul, Real.norm_of_nonneg hK0.le, norm_sub_rev, hρ,
      mul_comm h K]
    exact mul_le_mul_of_nonneg_left hz hK0.le
  have hs1 : ∀ i μ, |((shiftZ i μ : ℤ) : ℝ)| ≤ 1 := fun i μ => abs_shiftZ_le i μ
  have hstx : stencil ρ (shiftVec n) x y = discJet shiftZ ρ Yt p₀ := by
    rw [hyt, ← castVec_shiftZ, stencil_samp' hpert]
  have hstxμ : ∀ μ, stencil ρ (shiftVec n) (x + unitVec n μ) y =
      discJet shiftZ ρ Yt (p₀ + ρ • evec μ) := by
    intro μ
    rw [hyt, ← castVec_shiftZ, ← castVec_single, stencil_samp hpert, realVec_single]
  have hωx : ∀ μ, matToOp (omegaLink ρ (coframe y) x μ) =
      omegaJet (ρ, discJet shiftZ ρ Yt p₀) μ := by
    intro μ
    rw [← hstx, ← jetOmega_stencil]
    rfl
  have hωxμ : ∀ μ ν, matToOp (omegaLink ρ (coframe y) (x + unitVec n μ) ν) =
      omegaJet (ρ, discJet shiftZ ρ Yt (p₀ + ρ • evec μ)) ν := by
    intro μ ν
    rw [← hstxμ, ← jetOmega_stencil]
    rfl
  -- continuum side: rescaling
  have hee : (fun z => (Y z).1) = fun z => (fun z => (Yt z).1) (K • z) := by
    funext z; simp only [hYt, smul_smul, inv_mul_cancel₀ hKne, one_smul]
  have hcont : contCartan (fun z => (Y z).1) z μ ν = K ^ 2 • contCartan (fun z => (Yt z).1) ξ μ ν := by
    rw [hee]
    exact contCartan_scale (e := fun z => (Yt z).1) hKne z μ ν
  -- discrete side: rescaling
  have hdisc : cartanCurvature h (coframe y) x μ ν = K ^ 2 • jointLogPlaquette (ρ,
      omegaJet (ρ, discJet shiftZ ρ Yt p₀) μ, omegaJet (ρ, discJet shiftZ ρ Yt p₀) ν,
      ρ⁻¹ • (omegaJet (ρ, discJet shiftZ ρ Yt (p₀ + ρ • evec μ)) ν -
        omegaJet (ρ, discJet shiftZ ρ Yt p₀) ν),
      ρ⁻¹ • (omegaJet (ρ, discJet shiftZ ρ Yt (p₀ + ρ • evec ν)) μ -
        omegaJet (ρ, discJet shiftZ ρ Yt p₀) μ)) := by
    rw [cartanCurvature_eq_scaled hh.ne' hKne, ← hρ]
    congr 2
    simp only [ShiftedJetAction.fwdDiff, map_smul, map_sub, hωx, hωxμ]
  -- continuum values through the jet map
  have hω0 : ∀ ν, matToOp (omega0 (fun z => (Yt z).1) ξ ν) = omegaJet (0, cmap (jet1 Yt ξ)) ν :=
    fun ν => (congrFun (omegaJet_cmap_jet1 hFYt.diff0 ξ) ν).symm
  have hYtdet : ∀ w, (Yt w).1.det ≠ 0 := fun w => (hdet _ (hYe _)).ne'
  have hdω : ∀ μ ν, matToOp (fderiv ℝ (fun z => omega0 (fun z => (Yt z).1) z ν) ξ (evec μ)) =
      (fderiv ℝ omegaJet (0, cmap (jet1 Yt ξ))) (0, dJet Yt ξ (evec μ)) ν := by
    intro μ ν
    have hA := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Op) ν).hasFDerivAt).comp ξ
      (hreg.hasFDerivAt_comp_jet hδP hFYt hSY ξ)
    have hB' := (matToOpL.hasFDerivAt (x := omega0 (fun z => (Yt z).1) ξ ν)).comp ξ
      (differentiableAt_omega0 hFYt (hYtdet ξ) ν).hasFDerivAt
    have hfun : (⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Op) ν) ∘
        fun z => omegaJet ((0 : ℝ), (cmap (jet1 Yt z) : DiscreteEulerConsistency.Jet Shift
          (Field 𝔄 𝓗 𝓢)))) = ⇑matToOpL ∘ fun z => omega0 (fun z => (Yt z).1) z ν := by
      funext w
      simp only [Function.comp_apply, ContinuousLinearMap.proj_apply, matToOpL_apply]
      exact congrFun (omegaJet_cmap_jet1 hFYt.diff0 w) ν
    rw [hfun] at hA
    have := congrArg (fun T => T (evec μ)) (hA.unique hB')
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.inr_apply, matToOpL_apply] at this
    exact this.symm
  -- the comparison
  rw [hdisc, hcont, contCartan_eq_jointLogPlaquette]
  simp only [hω0, hdω]
  set c₀ : ℝ × Op × Op × Op × Op := ((0 : ℝ), omegaJet (0, cmap (jet1 Yt ξ)) μ,
    omegaJet (0, cmap (jet1 Yt ξ)) ν,
    (fderiv ℝ omegaJet (0, cmap (jet1 Yt ξ))) (0, dJet Yt ξ (evec μ)) ν,
    (fderiv ℝ omegaJet (0, cmap (jet1 Yt ξ))) (0, dJet Yt ξ (evec ν)) μ) with hc₀
  set p : ℝ × Op × Op × Op × Op := (ρ, omegaJet (ρ, discJet shiftZ ρ Yt p₀) μ,
    omegaJet (ρ, discJet shiftZ ρ Yt p₀) ν,
    ρ⁻¹ • (omegaJet (ρ, discJet shiftZ ρ Yt (p₀ + ρ • evec μ)) ν -
      omegaJet (ρ, discJet shiftZ ρ Yt p₀) ν),
    ρ⁻¹ • (omegaJet (ρ, discJet shiftZ ρ Yt (p₀ + ρ • evec ν)) μ -
      omegaJet (ρ, discJet shiftZ ρ Yt p₀) μ)) with hp
  -- componentwise estimates
  have hval : ∀ μ', ‖omegaJet (ρ, discJet shiftZ ρ Yt p₀) μ' - omegaJet (0, cmap (jet1 Yt ξ)) μ'‖ ≤
      M₂ * (ρ * (1 + c₁)) := by
    intro μ'
    refine (norm_le_pi_norm (omegaJet (ρ, discJet shiftZ ρ Yt p₀) -
      omegaJet (0, cmap (jet1 Yt ξ))) μ').trans ?_
    exact hreg.norm_value_sub_le hFYt hSY zero_le_one hs1 hρ0 hρδ
      (by linarith [hξp] : ‖p₀ - ξ‖ ≤ ρ * (1 + 1))
  have hdif : ∀ μ' ν', ‖ρ⁻¹ • (omegaJet (ρ, discJet shiftZ ρ Yt (p₀ + ρ • evec μ')) ν' -
      omegaJet (ρ, discJet shiftZ ρ Yt p₀) ν') -
      (fderiv ℝ omegaJet (0, cmap (jet1 Yt ξ))) (0, dJet Yt ξ (evec μ')) ν'‖ ≤ ρ * Cd := by
    intro μ' ν'
    have ha : ‖(p₀ + ρ • evec μ') - ξ‖ ≤ ρ * (1 + 1) := by
      calc ‖(p₀ + ρ • evec μ') - ξ‖ = ‖(p₀ - ξ) + ρ • evec μ'‖ := by congr 1; abel
        _ ≤ ‖p₀ - ξ‖ + ‖ρ • evec μ'‖ := norm_add_le _ _
        _ ≤ ρ + ρ := by
            rw [norm_smul, norm_evec, Real.norm_of_nonneg hρ0.le, mul_one]; linarith
        _ = ρ * (1 + 1) := by ring
    have hmain := hreg.norm_divDiff_sub_le hFYt hSY zero_le_one hs1 hρ0 hρδ μ' ha
      (by linarith [hξp] : ‖p₀ - ξ‖ ≤ ρ * (1 + 1)) (by abel)
    set F := ρ⁻¹ • (omegaJet (ρ, discJet shiftZ ρ Yt p₀) -
        omegaJet (ρ, discJet shiftZ ρ Yt (p₀ + ρ • evec μ'))) +
      (fderiv ℝ omegaJet (0, cmap (jet1 Yt ξ))) (0, dJet Yt ξ (evec μ')) with hFdef
    calc ‖ρ⁻¹ • (omegaJet (ρ, discJet shiftZ ρ Yt (p₀ + ρ • evec μ')) ν' -
          omegaJet (ρ, discJet shiftZ ρ Yt p₀) ν') -
          (fderiv ℝ omegaJet (0, cmap (jet1 Yt ξ))) (0, dJet Yt ξ (evec μ')) ν'‖ = ‖F ν'‖ := by
          rw [← norm_neg]; congr 1
          simp only [hFdef, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_sub]; abel
      _ ≤ ‖F‖ := norm_le_pi_norm F ν'
      _ ≤ ρ * Cd := hmain
  have hM : M₂ * (ρ * (1 + c₁)) ≤ ρ * Cm := by
    have e : ρ * Cm = ρ * 1 + M₂ * (ρ * (1 + c₁)) + ρ * Cd := by rw [hCm]; ring
    have := mul_nonneg hρ0.le hCd0
    linarith
  have hD : ρ * Cd ≤ ρ * Cm := by
    have e : ρ * Cm = ρ * 1 + M₂ * (ρ * (1 + c₁)) + ρ * Cd := by rw [hCm]; ring
    have := mul_nonneg hM₂ (mul_nonneg hρ0.le (by linarith : (0 : ℝ) ≤ 1 + c₁))
    linarith
  have hρm : ρ ≤ ρ * Cm := le_mul_of_one_le_right hρ0.le hCm1
  have hpc : ‖p - c₀‖ ≤ ρ * Cm :=
    norm_tuple5_le p c₀ (by rw [hp, hc₀]; simp only [sub_zero, Real.norm_of_nonneg hρ0.le]; exact hρm)
      ((hval μ).trans hM) ((hval ν).trans hM) ((hdif μ ν).trans hD) ((hdif ν μ).trans hD)
  -- the jet point lies in the compact set and both points in the Lipschitz ball
  have hc₀mem : c₀ ∈ ({(0 : ℝ)} : Set ℝ) ×ˢ closedBall (0 : Op × Op × Op × Op) RR := by
    refine ⟨rfl, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    have hJS : ((0 : ℝ), (cmap (jet1 Yt ξ) : DiscreteEulerConsistency.Jet Shift (Field 𝔄 𝓗 𝓢))) ∈
        ({(0 : ℝ)} : Set ℝ) ×ˢ S := ⟨rfl, hSY ξ⟩
    have hPv : ‖omegaJet ((0 : ℝ), (cmap (jet1 Yt ξ) : DiscreteEulerConsistency.Jet Shift
        (Field 𝔄 𝓗 𝓢)))‖ ≤ max RP 0 := (hRP _ hJS).trans (le_max_left _ _)
    have hDv : ∀ μ', ‖(fderiv ℝ omegaJet (0, cmap (jet1 Yt ξ))) (0, dJet Yt ξ (evec μ'))‖ ≤
        M₂ * (Bp + Bp) := by
      intro μ'
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have hb := hreg.bound _ (hSY ξ) _ (mem_ball_self hδP)
      have hdj : ‖(((0 : ℝ), dJet Yt ξ (evec μ')) : ℝ × DiscreteEulerConsistency.Jet Shift
          (Field 𝔄 𝓗 𝓢))‖ ≤ Bp + Bp := by
        rw [Prod.norm_def, norm_zero]
        refine max_le (by positivity) ?_
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        rw [norm_evec, mul_one]
        exact norm_dJet_le hFYt ξ
      exact mul_le_mul hb hdj (norm_nonneg _) hM₂
    have hR1 : max RP 0 ≤ RR := by
      have := mul_nonneg hM₂ (by positivity : (0 : ℝ) ≤ Bp + Bp)
      rw [hRR]; linarith
    have hR2 : M₂ * (Bp + Bp) ≤ RR := by
      have := le_max_right RP 0
      rw [hRR]; linarith
    simp only [Prod.norm_def]
    refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
    · exact ((norm_le_pi_norm _ μ).trans hPv).trans hR1
    · exact ((norm_le_pi_norm _ ν).trans hPv).trans hR1
    · exact ((norm_le_pi_norm _ ν).trans (hDv μ)).trans hR2
    · exact ((norm_le_pi_norm _ μ).trans (hDv ν)).trans hR2
  have hpball : p ∈ ball c₀ δJ := by
    rw [mem_ball, dist_eq_norm]; exact hpc.trans_lt hρJ
  have hLip := (convex_ball c₀ δJ).norm_image_sub_le_of_norm_fderiv_le
    (f := jointLogPlaquette (𝔄 := Op)) (fun q hq => (hJb c₀ hc₀mem q hq).1)
    (fun q hq => (hJb c₀ hc₀mem q hq).2.1) (mem_ball_self hδJ) hpball
  -- conclusion
  have e : K ^ 2 • jointLogPlaquette p - K ^ 2 • jointLogPlaquette c₀ =
      K ^ 2 • (jointLogPlaquette p - jointLogPlaquette c₀) := by module
  rw [e, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc K ^ 2 * ‖jointLogPlaquette p - jointLogPlaquette c₀‖ ≤ K ^ 2 * (LJ * (ρ * Cm)) := by
        gcongr
        exact hLip.trans (mul_le_mul_of_nonneg_left hpc hLJ)
    _ = LJ * Cm * h * K ^ 3 := by rw [hρ]; ring

end CartanMain


/-! ### Identification of the continuum Lagrangian `L₀` -/

section Identification

omit [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

variable (w : Field 𝔄 𝓗 𝓢) (p : Fin 4 → Field 𝔄 𝓗 𝓢)

/-- The continuum Lagrangian is the sum of the first-order Palatini density and the `h = 0`
Yang–Mills, Higgs and Dirac densities at the continuum first jet. -/
theorem limDensity_firstJetDensity_eq :
    limDensity (ι := Shift) (firstJetDensity D) (w, p) =
      NativeGravityJet.palatiniFirstOrder D.κ D.Λ w.1 (fun μ => (p μ).1) +
        normYM D (0, 1, cmap (w, p)) + normHiggs D (0, 1, cmap (w, p)) +
        normD D (0, 1, cmap (w, p)) := by
  unfold limDensity firstJetDensity
  rw [gravFirstJet_eq_gravCurv]
  rfl

/-- Yang–Mills at `h = 0`: `F_{μν} = ∂_μ A_ν - ∂_ν A_μ + [A_μ, A_ν]`. -/
theorem nuFieldStrength_cont (μ ν : Fin 4) :
    nuFieldStrength μ ν ((0 : ℝ), (1 : ℝ), (cmap (w, p) : NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) =
      (p μ).2.1 ν - (p ν).2.1 μ + (w.2.1 μ * w.2.1 ν - w.2.1 ν * w.2.1 μ) := by
  unfold nuFieldStrength
  have h := logPlaquette_smul_eq (0 : ℝ) (1 : ℝ) (w.2.1 μ) (w.2.1 ν) ((p μ).2.1 ν) ((p ν).2.1 μ)
  simp only [one_smul] at h
  show jointNuLogPlaquette ((0 : ℝ), (1 : ℝ), w.2.1 μ, w.2.1 ν, (p μ).2.1 ν, (p ν).2.1 μ) = _
  rw [← h, logPlaquette_zero]
  rfl

/-- Higgs at `h = 0`: `K_μ = ∂_μ H + ρ_H(A_μ) H`. -/
theorem nuHiggsLinkJet_cont (μ : Fin 4) :
    nuHiggsLinkJet D μ ((0 : ℝ), (1 : ℝ), (cmap (w, p) : NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) =
      D.ρH (w.2.1 μ) w.2.2.1 + (p μ).2.2.1 := by
  unfold nuHiggsLinkJet nuHiggsLink
  simp [linkExp, Data.ρHL_apply, cmap_apply]

/-- Dirac at `h = 0`: `∇_μ Ψ = ∂_μ Ψ + (σ(ω_μ(e, ∂e)) + ρ_S(A_μ)) Ψ`. -/
theorem nuDiracDiffJet_cont (μ : Fin 4) :
    nuDiracDiffJet D μ ((0 : ℝ), (1 : ℝ), (cmap (w, p) : NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) =
      (D.σ (readerOmega w.1 (fun lam => (p lam).1) μ) + D.ρS (w.2.1 μ)) w.2.2.2.1 +
        (p μ).2.2.2.1 := by
  unfold nuDiracDiffJet nuDiracDiff nuSpinQuot jetOmega
  simp [linkExp, Data.ρSL_apply, cmap_apply]

/-- Co-spinor at `h = 0`: `∇_μ Ψ̄ = ∂_μ Ψ̄ - Ψ̄ (ρ_S(A_μ) + σ(ω_μ))`. -/
theorem nuDiracDiffBarJet_cont (μ : Fin 4) :
    nuDiracDiffBarJet D μ ((0 : ℝ), (1 : ℝ), (cmap (w, p) : NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) =
      w.2.2.2.2.comp (-D.ρS (w.2.1 μ) - D.σ (readerOmega w.1 (fun lam => (p lam).1) μ)) +
        (p μ).2.2.2.2 := by
  unfold nuDiracDiffBarJet nuDiracDiffBar nuSpinQuotInv jetOmega
  simp [linkExp, Data.ρSL_apply, cmap_apply, sub_eq_add_neg]

end Identification

/-! ### Fixed-scale consequence: the nodal residual of a smooth solution -/

/-- **Fixed-scale native consistency for a smooth solution** (the `σ_h = O(h)` clause of
`cor:local-calibration-nonempty`): if a smooth periodic field in the chart solves the continuum
Einstein–Standard-Model Euler equations `𝓔₀(y) = 0`, then its samples have raw Euler row
`max_x ‖E_h^{raw}(𝖲_h y)(x)‖ ≤ C h`, hence finite-action covector mass norm
`σ_h² = h⁴ Σ_x ‖E_h^{raw}(x)‖² ≤ L⁴ (C h)²` on the box of side `L = n h`. -/
theorem native_sigma_of_solution {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (A B : ℝ) :
    ∃ C c_res : ℝ, 0 < c_res ∧ ∀ h : ℝ, 0 < h → h ≤ c_res →
      ∀ (n : ℕ) [NeZero n] (Y : R4 → Field 𝔄 𝓗 𝓢), ContDiff ℝ 3 Y →
        IsPeriodic ((n : ℝ) * h) Y → (∀ z, (Y z).1 ∈ Ke) → (∀ z, ‖Y z‖ ≤ A) →
        (∀ z, ‖iteratedFDeriv ℝ 1 Y z‖ ≤ B) → (∀ z, ‖iteratedFDeriv ℝ 2 Y z‖ ≤ B) →
        (∀ z, ‖iteratedFDeriv ℝ 3 Y z‖ ≤ B) →
        (∀ z, contEuler (limDensity (ι := Shift) (firstJetDensity D)) Y z = 0) →
        (∀ x : Grid n, ‖eulerRow (localAction D h) h (samp h Y) x‖ ≤ C * h) ∧
        h ^ 4 * ∑ x : Grid n, ‖eulerRow (localAction D h) h (samp h Y) x‖ ^ 2 ≤
          ((n : ℝ) * h) ^ 4 * (C * h) ^ 2 := by
  obtain ⟨C, c_res, hc, hmain⟩ := native_consistency D hKe hdet A B
  refine ⟨C, c_res, hc, fun h hh hhc n _ Y hYs hper hYe hYA h1 h2 h3 hsol => ?_⟩
  have hK := hmain 1 le_rfl h hh (by simpa using hhc) n Y hYs hper hYe hYA
    (fun z => by simpa using h1 z) (fun z => by simpa using h2 z) (fun z => by simpa using h3 z)
  have hpt : ∀ x : Grid n, ‖eulerRow (localAction D h) h (samp h Y) x‖ ≤ C * h := by
    intro x
    have := hK.2.2 x
    rw [hsol, sub_zero, one_pow, mul_one] at this
    exact this
  refine ⟨hpt, ?_⟩
  have hC0 : 0 ≤ C * h := (norm_nonneg _).trans (hpt 0)
  calc h ^ 4 * ∑ x : Grid n, ‖eulerRow (localAction D h) h (samp h Y) x‖ ^ 2
      ≤ h ^ 4 * ∑ _x : Grid n, (C * h) ^ 2 := by
        gcongr with x
        exact hpt x
    _ = ((n : ℝ) * h) ^ 4 * (C * h) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [ShiftedJetAction.Grid, Fintype.card_fun, ZMod.card, Fintype.card_fin]
        push_cast
        ring

/-! ### Non-vacuity -/

omit [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢] in
/-- The hypothesis packet of `native_consistency` is satisfiable: the flat constant field
(identity coframe, zero gauge, Higgs and spinor fields) has values in the chart `{1}`, any
period, and vanishing derivatives (band constant `B = 0`, any `K ≥ 1`). -/
example (n : ℕ) [NeZero n] (h K : ℝ) :
    let Y : R4 → Field 𝔄 𝓗 𝓢 := fun _ => ((1 : Mat), 0)
    ContDiff ℝ 3 Y ∧ IsPeriodic ((n : ℝ) * h) Y ∧ (∀ z, (Y z).1 ∈ ({1} : Set Mat)) ∧
      (∀ z, ‖Y z‖ ≤ ‖(((1 : Mat), 0) : Field 𝔄 𝓗 𝓢)‖) ∧
      (∀ j : ℕ, 1 ≤ j → ∀ z, ‖iteratedFDeriv ℝ j Y z‖ ≤ 0 * K ^ j) ∧
      IsCompact ({1} : Set Mat) ∧ ∀ e ∈ ({1} : Set Mat), 0 < e.det := by
  intro Y
  refine ⟨contDiff_const, fun z μ => rfl, fun z => rfl, fun z => le_rfl, fun j hj z => ?_,
    isCompact_singleton, fun e he => ?_⟩
  · simp [Y, iteratedFDeriv_const_of_ne (show j ≠ 0 by omega)]
  · rw [mem_singleton_iff] at he; subst he; simp


/-! ### The Cartan structure equation: `R(ω) = e Riem(g) e⁻¹` -/

section Structure

omit [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

/-- The ring identity behind the Cartan structure equation (gauge covariance of curvature under
`ω = E Γ E⁻¹ - (dE) E⁻¹`). -/
theorem structure_identity {R : Type*} [Ring R] (E Ei G1 G2 dG12 dG21 Q1 Q2 dQ dEi1 dEi2 : R)
    (h1 : Ei * E = 1) (hEi1 : dEi1 = -(Ei * Q1 * Ei)) (hEi2 : dEi2 = -(Ei * Q2 * Ei)) :
    ((Q1 * G2 * Ei + E * dG12 * Ei + E * G2 * dEi1) - (dQ * Ei + Q2 * dEi1)) -
      ((Q2 * G1 * Ei + E * dG21 * Ei + E * G1 * dEi2) - (dQ * Ei + Q1 * dEi2)) +
      ((E * G1 * Ei - Q1 * Ei) * (E * G2 * Ei - Q2 * Ei) -
        (E * G2 * Ei - Q2 * Ei) * (E * G1 * Ei - Q1 * Ei)) =
      E * (dG12 - dG21 + (G1 * G2 - G2 * G1)) * Ei := by
  subst hEi1 hEi2
  have k : ∀ X : R, Ei * (E * X) = X := fun X => by rw [← mul_assoc, h1, one_mul]
  simp only [mul_sub, sub_mul, mul_add, add_mul, mul_neg, neg_mul, mul_assoc, k]
  abel

/-- The Christoffel symbols `Γ^ρ_{μσ}` of `g = eᵀ η e` as the matrices `(Γ_μ)^ρ_σ`. -/
def gamMat (e : R4 → Mat) (z : R4) (μ : Fin 4) : Mat :=
  fun ρ σ => NativeScaling.readerGamma (e z) (fun lam => fderiv ℝ e z (evec lam)) ρ μ σ

/-- **The Riemann tensor of `g = eᵀ η e`** in coordinates, `R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ}
+ Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ}`, as the matrix `(R_{μν})^ρ_σ`. -/
def riemMat (e : R4 → Mat) (z : R4) (μ ν : Fin 4) : Mat :=
  fderiv ℝ (fun z => gamMat e z ν) z (evec μ) - fderiv ℝ (fun z => gamMat e z μ) z (evec ν) +
    (gamMat e z μ * gamMat e z ν - gamMat e z ν * gamMat e z μ)

theorem riemMat_apply (e : R4 → Mat) (z : R4) (μ ν ρ σ : Fin 4) :
    riemMat e z μ ν ρ σ = fderiv ℝ (fun z => gamMat e z ν) z (evec μ) ρ σ -
      fderiv ℝ (fun z => gamMat e z μ) z (evec ν) ρ σ +
      ∑ lam, (gamMat e z μ ρ lam * gamMat e z ν lam σ - gamMat e z ν ρ lam * gamMat e z μ lam σ) := by
  simp only [riemMat, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Finset.sum_sub_distrib]

/-- The reader connection in matrix form: `ω_μ = e Γ_μ e⁻¹ - (∂_μ e) e⁻¹`. -/
theorem omega0_eq (e : R4 → Mat) (z : R4) (μ : Fin 4) :
    omega0 e z μ = e z * gamMat e z μ * (e z)⁻¹ - fderiv ℝ e z (evec μ) * (e z)⁻¹ := by
  ext a b
  simp only [omega0, readerOmega, gamMat, Matrix.sub_apply, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem contDiffAt_readerGamma_entry (ρ μ σ : Fin 4) {q : Mat × (Fin 4 → Mat)} (hq : q.1.det ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : Mat × (Fin 4 → Mat) => NativeScaling.readerGamma q.1 q.2 ρ μ σ) q := by
  have hm : (metric q.1).det ≠ 0 := det_metric_ne_zero hq
  simp only [NativeScaling.readerGamma, NativeScaling.readerG, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, ← invEntry_apply]
  fun_prop (disch := assumption)

variable {e : R4 → Mat}

theorem differentiable_jetPair (he : ContDiff ℝ 2 e) :
    Differentiable ℝ (fun z => (e z, fun lam => fderiv ℝ e z (evec lam))) := by
  have h1 : Differentiable ℝ e := he.differentiable (by norm_num)
  have h2 : Differentiable ℝ (fderiv ℝ e) :=
    (he.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  intro z
  refine (h1 z).prodMk (differentiableAt_pi.mpr fun lam => ?_)
  exact (ContinuousLinearMap.apply ℝ Mat (evec lam)).differentiableAt.comp z (h2 z)

theorem differentiableAt_gamMat (he : ContDiff ℝ 2 e) {z : R4} (hz : (e z).det ≠ 0) (μ : Fin 4) :
    DifferentiableAt ℝ (fun z => gamMat e z μ) z := by
  refine differentiableAt_pi.mpr fun ρ => differentiableAt_pi.mpr fun σ => ?_
  show DifferentiableAt ℝ ((fun q : Mat × (Fin 4 → Mat) => NativeScaling.readerGamma q.1 q.2 ρ μ σ) ∘
    (fun z => (e z, fun lam => fderiv ℝ e z (evec lam)))) z
  exact ((contDiffAt_readerGamma_entry ρ μ σ (q := (e z, fun lam => fderiv ℝ e z (evec lam)))
    hz).differentiableAt (by simp)).comp z (differentiable_jetPair he z)

theorem differentiableAt_inv (he : ContDiff ℝ 2 e) {z : R4} (hz : (e z).det ≠ 0) :
    DifferentiableAt ℝ (fun z => (e z)⁻¹) z := by
  refine differentiableAt_pi.mpr fun a => differentiableAt_pi.mpr fun b => ?_
  show DifferentiableAt ℝ (invEntry a b ∘ e) z
  exact ((contDiffAt_invEntry (k := 1) a b hz).differentiableAt (by simp)).comp z
    ((he.differentiable (by norm_num)) z)

theorem differentiableAt_dir (he : ContDiff ℝ 2 e) (z : R4) (μ : Fin 4) :
    DifferentiableAt ℝ (fun z => fderiv ℝ e z (evec μ)) z :=
  (ContinuousLinearMap.apply ℝ Mat (evec μ)).differentiableAt.comp z
    ((he.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z)

/-- Directional derivatives of `matToOp`-images. -/
theorem fderiv_matToOp_apply {f : R4 → Mat} {z : R4} (hf : DifferentiableAt ℝ f z) (v : R4) :
    fderiv ℝ (fun z => matToOp (f z)) z v = matToOp (fderiv ℝ f z v) := by
  have := (matToOpL.hasFDerivAt.comp z hf.hasFDerivAt).fderiv
  rw [show (fun z => matToOp (f z)) = ⇑matToOpL ∘ f from rfl, this]
  rfl

theorem fderiv_mul_apply {f g : R4 → Op} {z : R4} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (v : R4) :
    fderiv ℝ (fun z => f z * g z) z v = fderiv ℝ f z v * g z + f z * fderiv ℝ g z v := by
  rw [(hf.hasFDerivAt.fun_mul' hg.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [add_comm]
  rfl

theorem fderiv_sub_apply' {f g : R4 → Op} {z : R4} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (v : R4) :
    fderiv ℝ (fun z => f z - g z) z v = fderiv ℝ f z v - fderiv ℝ g z v := by
  rw [fderiv_fun_sub hf hg, ContinuousLinearMap.sub_apply]

/-- **The Cartan structure equation**: for a `C²` coframe field with invertible values, the
curvature of the torsion-free reader connection is the Riemann tensor of `g = eᵀ η e` in mixed
frame/coordinate components, `R(ω)_{μν} = e Riem_{μν}(g) e⁻¹`. -/
theorem contCartan_eq_riem (he : ContDiff ℝ 2 e) (hdet : ∀ z, (e z).det ≠ 0) (z : R4)
    (μ ν : Fin 4) : contCartan e z μ ν = matToOp (e z * riemMat e z μ ν * (e z)⁻¹) := by
  -- the pieces as operator-valued functions
  set E : R4 → Op := fun z => matToOp (e z) with hE
  set Ei : R4 → Op := fun z => matToOp (e z)⁻¹ with hEi
  set G : Fin 4 → R4 → Op := fun μ z => matToOp (gamMat e z μ) with hG
  set Q : Fin 4 → R4 → Op := fun μ z => matToOp (fderiv ℝ e z (evec μ)) with hQ
  have hdiffE : ∀ z, DifferentiableAt ℝ E z := fun z =>
    matToOpL.differentiableAt.comp z ((he.differentiable (by norm_num)) z)
  have hdiffEi : ∀ z, DifferentiableAt ℝ Ei z := fun z =>
    matToOpL.differentiableAt.comp z (differentiableAt_inv he (hdet z))
  have hdiffG : ∀ μ z, DifferentiableAt ℝ (G μ) z := fun μ z =>
    matToOpL.differentiableAt.comp z (differentiableAt_gamMat he (hdet z) μ)
  have hdiffQ : ∀ μ z, DifferentiableAt ℝ (Q μ) z := fun μ z =>
    matToOpL.differentiableAt.comp z (differentiableAt_dir he z μ)
  have hEiE : ∀ z, Ei z * E z = 1 := fun z => by
    simp only [hE, hEi, ← map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit (hdet z)), map_one]
  have hEEi : ∀ z, E z * Ei z = 1 := fun z => by
    simp only [hE, hEi, ← map_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet z)), map_one]
  -- derivative of E is Q
  have hdE : ∀ v, fderiv ℝ E z (evec v) = Q v z := fun v =>
    fderiv_matToOp_apply ((he.differentiable (by norm_num)) z) (evec v)
  -- derivative of the inverse
  have hdEi : ∀ v, fderiv ℝ Ei z (evec v) = -(Ei z * Q v z * Ei z) := by
    intro v
    have hconst : (fun z => E z * Ei z) = fun _ => (1 : Op) := funext hEEi
    have h0 := fderiv_mul_apply (hdiffE z) (hdiffEi z) (evec v)
    rw [hconst, fderiv_const_apply, ContinuousLinearMap.zero_apply, hdE] at h0
    have h2 : Ei z * (Q v z * Ei z + E z * fderiv ℝ Ei z (evec v)) = 0 := by rw [← h0, mul_zero]
    have h3 : Ei z * (E z * fderiv ℝ Ei z (evec v)) = fderiv ℝ Ei z (evec v) := by
      rw [← mul_assoc, hEiE, one_mul]
    rw [mul_add, h3] at h2
    rw [eq_neg_iff_add_eq_zero, add_comm, mul_assoc]
    exact h2
  -- the connection in operator form
  have hω : ∀ ν, (fun z => matToOp (omega0 e z ν)) = fun z => E z * G ν z * Ei z - Q ν z * Ei z := by
    intro ν
    funext z
    rw [omega0_eq]
    simp only [hE, hEi, hG, hQ, map_sub, map_mul]
  have hdω : ∀ ν, DifferentiableAt ℝ (fun z => omega0 e z ν) z := by
    intro ν
    refine differentiableAt_pi.mpr fun a => differentiableAt_pi.mpr fun b => ?_
    show DifferentiableAt ℝ ((fun q : Mat × (Fin 4 → Mat) => readerOmega q.1 q.2 ν a b) ∘
      (fun z => (e z, fun lam => fderiv ℝ e z (evec lam)))) z
    exact ((contDiffAt_readerOmega_entry ν a b (q := (e z, fun lam => fderiv ℝ e z (evec lam)))
      (hdet z)).differentiableAt (by simp)).comp z (differentiable_jetPair he z)
  have hderω : ∀ μ ν, matToOp (fderiv ℝ (fun z => omega0 e z ν) z (evec μ)) =
      (Q μ z * G ν z * Ei z + E z * fderiv ℝ (G ν) z (evec μ) * Ei z +
        E z * G ν z * fderiv ℝ Ei z (evec μ)) -
      (fderiv ℝ (Q ν) z (evec μ) * Ei z + Q ν z * fderiv ℝ Ei z (evec μ)) := by
    intro μ ν
    rw [← fderiv_matToOp_apply (hdω ν), hω ν]
    have hEG : DifferentiableAt ℝ (fun z => E z * G ν z) z := (hdiffE z).fun_mul (hdiffG ν z)
    have hA : DifferentiableAt ℝ (fun z => E z * G ν z * Ei z) z := hEG.fun_mul (hdiffEi z)
    have hB : DifferentiableAt ℝ (fun z => Q ν z * Ei z) z := (hdiffQ ν z).fun_mul (hdiffEi z)
    rw [fderiv_sub_apply' hA hB,
      fderiv_mul_apply (f := fun z => E z * G ν z) (g := Ei) hEG (hdiffEi z),
      fderiv_mul_apply (f := E) (g := G ν) (hdiffE z) (hdiffG ν z),
      fderiv_mul_apply (f := Q ν) (g := Ei) (hdiffQ ν z) (hdiffEi z), hdE]
    noncomm_ring
  -- symmetry of the second derivative of `e`
  have hsym : fderiv ℝ (Q ν) z (evec μ) = fderiv ℝ (Q μ) z (evec ν) := by
    have hEC2 : ContDiff ℝ 2 E := matToOpL.contDiff.comp he
    have hQE : ∀ w, Q w = fun z => fderiv ℝ E z (evec w) := fun w => funext fun z' =>
      (fderiv_matToOp_apply ((he.differentiable (by norm_num)) z') (evec w)).symm
    have hd2 : DifferentiableAt ℝ (fderiv ℝ E) z :=
      (hEC2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z
    have hA : ∀ w v, fderiv ℝ (fun z => fderiv ℝ E z (evec w)) z v =
        fderiv ℝ (fderiv ℝ E) z v (evec w) := by
      intro w v
      rw [fderiv_clm_apply hd2 (differentiableAt_const (evec w))]
      simp
    rw [hQE ν, hQE μ, hA, hA]
    exact (hEC2.contDiffAt.isSymmSndFDerivAt (by simp)).eq (evec μ) (evec ν)
  -- assemble
  unfold contCartan
  rw [map_add, map_sub, map_sub, map_mul, map_mul, hderω, hderω]
  have hω0 : ∀ ν, matToOp (omega0 e z ν) = E z * G ν z * Ei z - Q ν z * Ei z :=
    fun ν => congrFun (hω ν) z
  rw [hω0, hω0, hsym]
  have hgoal := structure_identity (E z) (Ei z) (G μ z) (G ν z) (fderiv ℝ (G ν) z (evec μ))
    (fderiv ℝ (G μ) z (evec ν)) (Q μ z) (Q ν z) (fderiv ℝ (Q μ) z (evec ν))
    (fderiv ℝ Ei z (evec μ)) (fderiv ℝ Ei z (evec ν)) (hEiE z) (hdEi μ) (hdEi ν)
  rw [hgoal]
  simp only [hE, hEi, hG, riemMat, map_mul, map_add, map_sub]
  rw [fderiv_matToOp_apply (differentiableAt_gamMat he (hdet z) ν),
    fderiv_matToOp_apply (differentiableAt_gamMat he (hdet z) μ)]

end Structure


/-! ### `eq:native-Cartan` against the Riemann tensor -/

/-- **`eq:native-Cartan` with `Riem(g)`**: under the hypotheses of `native_consistency`, the
literal Cartan plaquette curvature of the samples is uniformly `C h K³`-close, at every point `z` of
the cell of every node, to the Riemann tensor of `g = eᵀ η e` in mixed frame/coordinate components
`e Riem_{μν}(g) e⁻¹` (`R^a_{bμν} = e^a_ρ R^ρ_{σμν} E^σ_b`, Christoffel symbols `readerGamma` of
`g`). -/
theorem native_cartan_riem {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (A B : ℝ) :
    ∃ C c_res : ℝ, 0 < c_res ∧ ∀ K : ℝ, 1 ≤ K → ∀ h : ℝ, 0 < h → h * K ≤ c_res →
      ∀ (n : ℕ) [NeZero n] (Y : R4 → Field 𝔄 𝓗 𝓢), ContDiff ℝ 3 Y →
        IsPeriodic ((n : ℝ) * h) Y → (∀ z, (Y z).1 ∈ Ke) → (∀ z, ‖Y z‖ ≤ A) →
        (∀ z, ‖iteratedFDeriv ℝ 1 Y z‖ ≤ B * K) → (∀ z, ‖iteratedFDeriv ℝ 2 Y z‖ ≤ B * K ^ 2) →
        (∀ z, ‖iteratedFDeriv ℝ 3 Y z‖ ≤ B * K ^ 3) →
        ∀ (x : Grid n) (z : R4), ‖z - pos h x‖ ≤ h → ∀ μ ν : Fin 4,
          ‖cartanCurvature h (coframe (samp h Y : Grid n → Field 𝔄 𝓗 𝓢)) x μ ν -
            matToOp ((Y z).1 * riemMat (fun z => (Y z).1) z μ ν * ((Y z).1)⁻¹)‖ ≤ C * h * K ^ 3 := by
  obtain ⟨C, c_res, hc, hmain⟩ := native_cartan_consistency (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) hKe hdet A B
  refine ⟨C, c_res, hc, fun K hK h hh hhK n _ Y hYs hper hYe hYA h1 h2 h3 x z hz μ ν => ?_⟩
  have he : ContDiff ℝ 2 (fun z => (Y z).1) :=
    ((ContinuousLinearMap.fst ℝ Mat ((Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢)).contDiff.comp
      (hYs.of_le (by norm_num)))
  rw [← contCartan_eq_riem he (fun z => (hdet _ (hYe z)).ne') z μ ν]
  exact hmain K hK h hh hhK n Y hYs hper hYe hYA h1 h2 h3 x z hz μ ν

end

end RenewalGeometry.NativeEulerConsistency
