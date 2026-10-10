/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeMatterEulerRows

/-!
# The Yang–Mills and Higgs Euler rows of the native continuum Lagrangian

Einstein–Standard-Model action-closure manuscript, bridge step P3 of `thm:native-closure`
("the Euler rows of the native Lagrangian are the physical field equations up to smooth
invertible algebraic coefficients"), matter sector, bosonic rows.

The native continuum Lagrangian is `L₀ = limDensity (firstJetDensity D)` (the `h = 0` value of
the first-jet density of `eq:native-densities`).  By
`NativeEulerConsistency.limDensity_firstJetDensity_eq` and the `h = 0` identifications of the
plaquette, link and spin-link quotients it is the sum (`L0_eq`) of
* `Lgc`  — the first-order Palatini density (`PalatiniEuler.Lg`);
* `LYMc` — `-¼ v(e) g^{μρ}g^{νσ}⟨F_{μν}, F_{ρσ}⟩`, `F = ∂A - ∂A + [A, A]` (`FA`);
* `LHc`  — `-v(e) g^{μν}⟨K_μ, K_ν⟩ - v(e)V(H)`, `K_μ = ∂_μH + ρ_H(A_μ)H` (`KH`);
* `LDc`  — `v(e) Re{(i/2)[Ψ̄γ^μ∇_μΨ - (∇_μΨ̄)γ^μΨ] - Ψ̄𝓜(H)Ψ}` with
  `∇_μΨ = ∂_μΨ + (σ(ω_μ) + ρ_S(A_μ))Ψ` (`DPsi`, `DPsiBar`), `ω = Ω(e, ∂e)` the torsion-free
  reader connection.

`L₀` is smooth on the nondegenerate chart (`contDiffOn_L0`).

## Main results (smooth native field `Y = (e, A, H, Ψ, Ψ̄)` on `ℝ⁴`, `det e > 0`; `g = eᵀηe`,
`v = √(-det g)`, `Γ` the Christoffel symbols of `g`)

* `fderiv_L0_A`, `fderiv_L0_dA` — the value and jet partials of `L₀` in the gauge field
  (symmetric, ad-invariant form `⟨·,·⟩_𝐠`);
* **`ym_euler_row`** — `𝓔₀(Y)[(0, X, 0, 0, 0)] = v g^{νσ}⟨X_ν, ∇^μF_{μσ} + [A^μ, F_{μσ}]⟩ + j(X)`
  with the Yang–Mills divergence in Christoffel form (`ymDivN`, from
  `NativeMatterEuler.sum_pd_form_density`) and the matter current covector `j = ∂_A(L_H + L_D)`
  (`gaugeCur`);
* `ymDivN_eq_ymDiv` — `ymDivN` is the slab-model divergence `ActualJetGauge.ymDiv` of the native
  potential jets; **`ym_euler_row_ymRes`** — the gauge row is `v g^{νσ}⟨X_ν, r^A_σ⟩` with the
  slab-model Yang–Mills residual `r^A = ActualJetGauge.ymRes … J` for any current `J`
  representing `-j`;
* `fderiv_L0_H`, `fderiv_L0_dH`, **`higgs_euler_row`** —
  `𝓔₀(Y)[(0, 0, η, 0, 0)] = 2v⟨η, □_AH⟩ - v DV(H)[η] - v Re Ψ̄𝓜_𝐘(η)Ψ` with the covariant wave
  operator in Christoffel form (`waveN`, from `NativeMatterEuler.sum_pd_vec_density`), for gauge
  potentials with values in a set on which `ρ_H` is skew.

Disclosed renderings: the gauge algebra is the associative algebra `𝔄` of `NativeDensity.Data`
with Lie bracket `[a, b] = ab - ba` (`LieRing.ofAssociativeRing`); the invariant form is assumed
symmetric and ad-invariant on `𝔄`; skewness of `ρ_H` is assumed only on the values of the gauge
field (a unital algebra representation cannot be skew on all of `𝔄`).
-/

namespace RenewalGeometry

namespace NativeBosonicEuler

open Finset HarmonicDefect EHJetVariation EHFieldVariation ActualJetSystem PalatiniEuler
  NativeMatterEuler
open NativeScaling (Mat eta metric readerOmega)
open NativeDensity
open NativeEulerConsistency (scaledDensity contDiffAt_scaledDensity)
open DiscreteEulerConsistency (R4 evec jet1 contEuler limDensity cmap cmap_apply)
open Filter Topology Set
open SobolevOpen (pd)
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

/-- The continuum first jets `(w, p)` of native fields. -/
abbrev FJ (𝔄 𝓗 𝓢 : Type*) [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [NormedAddCommGroup 𝓗]
    [NormedSpace ℝ 𝓗] [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] :=
  Field 𝔄 𝓗 𝓢 × (Fin 4 → Field 𝔄 𝓗 𝓢)

/-- **The native continuum Lagrangian** `L₀ = F^{(1)}(0, ·)` on first jets. -/
abbrev L0 : FJ 𝔄 𝓗 𝓢 → ℝ := limDensity (ι := Shift) (firstJetDensity D)

/-! ### The explicit sectors -/

/-- The continuum field strength `F_{μν} = ∂_μA_ν - ∂_νA_μ + [A_μ, A_ν]`. -/
def FA (wp : FJ 𝔄 𝓗 𝓢) (μ ν : Fin 4) : 𝔄 :=
  (wp.2 μ).2.1 ν - (wp.2 ν).2.1 μ + (wp.1.2.1 μ * wp.1.2.1 ν - wp.1.2.1 ν * wp.1.2.1 μ)

theorem FA_anti (wp : FJ 𝔄 𝓗 𝓢) (μ ν : Fin 4) : FA wp ν μ = -FA wp μ ν := by
  unfold FA; abel

theorem antisym_FA (wp : FJ 𝔄 𝓗 𝓢) (μ ν : Fin 4) : antisym (FA wp) μ ν = FA wp μ ν := by
  unfold antisym
  split_ifs with h1 h2
  · rfl
  · rw [FA_anti, neg_neg]
  · have : μ = ν := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
    subst this
    unfold FA; abel

/-- The covariant Higgs derivative `K_μ = ∂_μH + ρ_H(A_μ)H`. -/
def KH (wp : FJ 𝔄 𝓗 𝓢) (μ : Fin 4) : 𝓗 := D.ρH (wp.1.2.1 μ) wp.1.2.2.1 + (wp.2 μ).2.2.1

/-- The torsion-free reader connection `ω_μ = Ω_μ(e, ∂e)`. -/
def omC (wp : FJ 𝔄 𝓗 𝓢) (μ : Fin 4) : Mat := readerOmega wp.1.1 (fun l => (wp.2 l).1) μ

/-- The covariant spinor derivative `∇_μΨ = ∂_μΨ + (σ(ω_μ) + ρ_S(A_μ))Ψ`. -/
def DPsi (wp : FJ 𝔄 𝓗 𝓢) (μ : Fin 4) : 𝓢 :=
  (D.σ (omC wp μ) + D.ρS (wp.1.2.1 μ)) wp.1.2.2.2.1 + (wp.2 μ).2.2.2.1

/-- The covariant co-spinor derivative `∇_μΨ̄ = ∂_μΨ̄ - Ψ̄(ρ_S(A_μ) + σ(ω_μ))`. -/
def DPsiBar (wp : FJ 𝔄 𝓗 𝓢) (μ : Fin 4) : CoSpinor 𝓢 :=
  wp.1.2.2.2.2.comp (-D.ρS (wp.1.2.1 μ) - D.σ (omC wp μ)) + (wp.2 μ).2.2.2.2

/-- The gravitational sector: the first-order Palatini density. -/
def Lgc (wp : FJ 𝔄 𝓗 𝓢) : ℝ :=
  NativeGravityJet.palatiniFirstOrder D.κ D.Λ wp.1.1 (fun μ => (wp.2 μ).1)

/-- The Yang–Mills sector `-¼ v(e) g^{μρ}g^{νσ}⟨F_{μν}, F_{ρσ}⟩`. -/
def LYMc (wp : FJ 𝔄 𝓗 𝓢) : ℝ :=
  -(4⁻¹ * volume wp.1.1 * ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ginv wp.1.1 μ ρ * ginv wp.1.1 ν σ *
    D.ipA (FA wp μ ν) (FA wp ρ σ))

/-- The Higgs sector `-v(e) g^{μν}⟨K_μ, K_ν⟩ - v(e)V(H)`. -/
def LHc (wp : FJ 𝔄 𝓗 𝓢) : ℝ :=
  -(volume wp.1.1 * ∑ μ, ∑ ν, ginv wp.1.1 μ ν * D.hermH (KH D wp μ) (KH D wp ν)) -
    volume wp.1.1 * potential D wp.1.2.2.1

/-- The Dirac–Yukawa sector `v(e) Re{(i/2)[Ψ̄γ^μ∇_μΨ - (∇_μΨ̄)γ^μΨ] - Ψ̄𝓜(H)Ψ}`. -/
def LDc (wp : FJ 𝔄 𝓗 𝓢) : ℝ :=
  volume wp.1.1 *
    (Complex.I / 2 * ∑ μ, (wp.1.2.2.2.2 (gammaMu D μ wp.1.1 (DPsi D wp μ)) -
        DPsiBar D wp μ (gammaMu D μ wp.1.1 wp.1.2.2.2.1)) -
      wp.1.2.2.2.2 (D.yukawa wp.1.2.2.1 wp.1.2.2.2.1)).re

/-- **The native continuum Lagrangian, sector by sector**:
`L₀ = L^{(1)}_{Palatini} + L_{YM} + L_H + L_D`. -/
theorem L0_eq (wp : FJ 𝔄 𝓗 𝓢) : L0 D wp = Lgc D wp + LYMc D wp + LHc D wp + LDc D wp := by
  obtain ⟨w, p⟩ := wp
  rw [L0, NativeEulerConsistency.limDensity_firstJetDensity_eq]
  have hF : ∀ μ ν, antisym (fun μ ν => nuFieldStrength μ ν ((0 : ℝ), (1 : ℝ),
      (cmap (w, p) : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)))) μ ν = FA (w, p) μ ν := by
    intro μ ν
    have : (fun μ ν => nuFieldStrength μ ν ((0 : ℝ), (1 : ℝ),
        (cmap (w, p) : NativeDensity.Jet (Field 𝔄 𝓗 𝓢)))) = FA (w, p) := by
      funext μ ν
      rw [NativeEulerConsistency.nuFieldStrength_cont]
      rfl
    rw [this, antisym_FA]
  have hK : ∀ μ, nuHiggsLinkJet D μ ((0 : ℝ), (1 : ℝ),
      (cmap (w, p) : NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) = KH D (w, p) μ := by
    intro μ
    rw [NativeEulerConsistency.nuHiggsLinkJet_cont]
    unfold KH
    rfl
  have hΨ : ∀ μ, nuDiracDiffJet D μ ((0 : ℝ), (1 : ℝ),
      (cmap (w, p) : NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) = DPsi D (w, p) μ := by
    intro μ
    rw [NativeEulerConsistency.nuDiracDiffJet_cont]
    rfl
  have hΨb : ∀ μ, nuDiracDiffBarJet D μ ((0 : ℝ), (1 : ℝ),
      (cmap (w, p) : NativeDensity.Jet (Field 𝔄 𝓗 𝓢))) = DPsiBar D (w, p) μ := by
    intro μ
    rw [NativeEulerConsistency.nuDiracDiffBarJet_cont]
    rfl
  unfold normYM normHiggs normD
  simp only [hF, hK, hΨ, hΨb]
  unfold Lgc LYMc LHc LDc
  simp only [cmap_apply, one_pow, one_mul, Complex.ofReal_one]

/-! ### Smoothness of `L₀` on the nondegenerate chart -/

/-- The nondegenerate chart of first jets. -/
def chartF : Set (FJ 𝔄 𝓗 𝓢) := {wp | wp.1.1.det ≠ 0}

theorem isOpen_chartF : IsOpen (chartF : Set (FJ 𝔄 𝓗 𝓢)) :=
  isOpen_ne.preimage (Continuous.matrix_det (continuous_fst.comp continuous_fst))

theorem L0_eq_scaled (wp : FJ 𝔄 𝓗 𝓢) :
    L0 D wp = scaledDensity D (1, ((0 : ℝ), (cmap wp : DiscreteEulerConsistency.Jet Shift
      (Field 𝔄 𝓗 𝓢)))) := by
  unfold L0 limDensity firstJetDensity scaledDensity
  simp

theorem contDiffOn_L0 : ContDiffOn ℝ ∞ (L0 D) (chartF : Set (FJ 𝔄 𝓗 𝓢)) := by
  intro wp hwp
  refine ContDiffAt.contDiffWithinAt ?_
  have hfun : L0 D = fun wp => scaledDensity D (1, ((0 : ℝ),
      (cmap wp : DiscreteEulerConsistency.Jet Shift (Field 𝔄 𝓗 𝓢)))) :=
    funext (L0_eq_scaled D)
  rw [hfun]
  have hc : JetChart (cmap wp : DiscreteEulerConsistency.Jet Shift
      (Field 𝔄 𝓗 𝓢)) := fun s => hwp
  have hlin : ContDiffAt ℝ ∞ (fun wp : FJ 𝔄 𝓗 𝓢 => ((1 : ℝ), ((0 : ℝ),
      (cmap wp : DiscreteEulerConsistency.Jet Shift (Field 𝔄 𝓗 𝓢))))) wp :=
    contDiffAt_const.prodMk (contDiffAt_const.prodMk
      (ContinuousLinearMap.contDiff (cmap (ι := Shift) (V := Field 𝔄 𝓗 𝓢))).contDiffAt)
  exact ContDiffAt.comp (g := scaledDensity D) wp (contDiffAt_scaledDensity D (ν := 1) hc) hlin

/-! ### Calculus helpers -/

/-- A derivative of `L` at `x` in direction `d` read off from the line `t ↦ L(x + t d)`. -/
theorem fderiv_apply_of_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : E → ℝ}
    {x d : E} {D' : ℝ} (hL : DifferentiableAt ℝ L x)
    (h : HasDerivAt (fun t : ℝ => L (x + t • d)) D' 0) : fderiv ℝ L x d = D' := by
  have hl : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have := hL.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact this.unique h

theorem hasDerivAt_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c v : E) :
    HasDerivAt (fun t : ℝ => c + t • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add c

theorem hasDerivAt_bilin {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E →L[ℝ] F →L[ℝ] ℝ) {f : ℝ → E} {g : ℝ → F}
    {f' : E} {g' : F} {t : ℝ} (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => B (f s) (g s)) (B f' (g t) + B (f t) g') t := by
  have h1 : HasDerivAt (fun s => B (f s)) (B f') t := B.hasFDerivAt.comp_hasDerivAt t hf
  exact h1.clm_apply hg

theorem pd_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (T : E →L[ℝ] F) {f : R4 → E} {z : R4} (hf : DifferentiableAt ℝ f z)
    (μ : Fin 4) : pd (fun y => T (f y)) μ z = T (pd f μ z) := by
  unfold SobolevOpen.pd
  have : (fun y => T (f y)) = T ∘ f := rfl
  rw [this, fderiv_comp z T.differentiableAt hf]
  simp

/-! ### Symmetrisation of the Yang–Mills variation -/

/-- `-¼ v Σ g g (⟨c_{αβ} - c_{βα}, F_{ρσ}⟩ + ⟨F_{αβ}, c_{ρσ} - c_{σρ}⟩) = -v Σ g g ⟨c_{αβ}, F_{ρσ}⟩`
for a symmetric form, a symmetric `g` and an antisymmetric `F`. -/
theorem ym_sym (B : 𝔄 →L[ℝ] 𝔄 →L[ℝ] ℝ) (hsym : ∀ x y, B x y = B y x)
    (g : Fin 4 → Fin 4 → ℝ) (hg : ∀ a b, g a b = g b a) (F : Fin 4 → Fin 4 → 𝔄)
    (hF : ∀ a b, F b a = -F a b) (c : Fin 4 → Fin 4 → 𝔄) (v : ℝ) :
    -(4⁻¹ * v * ∑ α, ∑ β, ∑ ρ, ∑ σ, g α ρ * g β σ *
        (B (c α β - c β α) (F ρ σ) + B (F α β) (c ρ σ - c σ ρ))) =
      -(v * ∑ α, ∑ β, ∑ ρ, ∑ σ, g α ρ * g β σ * B (c α β) (F ρ σ)) := by
  set S := ∑ α, ∑ β, ∑ ρ, ∑ σ, g α ρ * g β σ * B (c α β) (F ρ σ)
  have e1 : ∑ α, ∑ β, ∑ ρ, ∑ σ, g α ρ * g β σ * B (c β α) (F ρ σ) = -S := by
    have h : ∑ α, ∑ β, ∑ ρ, ∑ σ, g α ρ * g β σ * B (c β α) (F ρ σ) =
        ∑ α, ∑ β, ∑ ρ, ∑ σ, -(g α ρ * g β σ * B (c α β) (F ρ σ)) :=
      sum4_reindex _ _ { toFun := fun x => (x.2.1, x.1, x.2.2.2, x.2.2.1)
                         invFun := fun x => (x.2.1, x.1, x.2.2.2, x.2.2.1)
                         left_inv := fun x => rfl
                         right_inv := fun x => rfl } fun x => by
          simp only [Equiv.coe_fn_mk]
          rw [hF x.2.2.1 x.2.2.2, map_neg]; ring
    rw [h]; simp only [Finset.sum_neg_distrib]; rfl
  have e2 : ∑ α, ∑ β, ∑ ρ, ∑ σ, g α ρ * g β σ * B (F α β) (c ρ σ) = S :=
    sum4_reindex _ _ { toFun := fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1)
                       invFun := fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1)
                       left_inv := fun x => rfl
                       right_inv := fun x => rfl } fun x => by
        simp only [Equiv.coe_fn_mk]
        rw [hsym, hg x.1 x.2.2.1, hg x.2.1 x.2.2.2]
  have e3 : ∑ α, ∑ β, ∑ ρ, ∑ σ, g α ρ * g β σ * B (F α β) (c σ ρ) = -S := by
    have h : ∑ α, ∑ β, ∑ ρ, ∑ σ, g α ρ * g β σ * B (F α β) (c σ ρ) =
        ∑ α, ∑ β, ∑ ρ, ∑ σ, -(g α ρ * g β σ * B (F α β) (c ρ σ)) :=
      sum4_reindex _ _ { toFun := fun x => (x.2.1, x.1, x.2.2.2, x.2.2.1)
                         invFun := fun x => (x.2.1, x.1, x.2.2.2, x.2.2.1)
                         left_inv := fun x => rfl
                         right_inv := fun x => rfl } fun x => by
          simp only [Equiv.coe_fn_mk]
          rw [hF x.1 x.2.1, map_neg, ContinuousLinearMap.neg_apply]; ring
    rw [h]
    simp only [Finset.sum_neg_distrib]
    rw [e2]
  have hsplit : ∑ α, ∑ β, ∑ ρ, ∑ σ, g α ρ * g β σ *
      (B (c α β - c β α) (F ρ σ) + B (F α β) (c ρ σ - c σ ρ)) =
      (∑ α, ∑ β, ∑ ρ, ∑ σ, g α ρ * g β σ * B (c α β) (F ρ σ)) -
        (∑ α, ∑ β, ∑ ρ, ∑ σ, g α ρ * g β σ * B (c β α) (F ρ σ)) +
        (∑ α, ∑ β, ∑ ρ, ∑ σ, g α ρ * g β σ * B (F α β) (c ρ σ)) -
        (∑ α, ∑ β, ∑ ρ, ∑ σ, g α ρ * g β σ * B (F α β) (c σ ρ)) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    ring
  rw [hsplit, e1, e2, e3]
  ring

/-! ### The Yang–Mills row -/

/-- The gauge direction `(0, X, 0, 0, 0)` of the native field space. -/
def gaugeDir (X : Fin 4 → 𝔄) : Field 𝔄 𝓗 𝓢 := (0, X, 0, 0, 0)

/-- The variation of the field strength along a gauge direction (the `t`-linear part of
`F(A + tX)`): `[A_μ, X_ν] - [A_ν, X_μ]`, written as `X_μA_ν + A_μX_ν - (X_νA_μ + A_νX_μ)`. -/
def BA (wp : FJ 𝔄 𝓗 𝓢) (X : Fin 4 → 𝔄) (μ ν : Fin 4) : 𝔄 :=
  X μ * wp.1.2.1 ν + wp.1.2.1 μ * X ν - (X ν * wp.1.2.1 μ + wp.1.2.1 ν * X μ)

/-- **The gauge current covector of the matter sectors**: the derivative of `L_H + L_D` along a
gauge direction (the Higgs current `-v g^{μν}(⟨ρ_H(X_μ)H, K_ν⟩ + ⟨K_μ, ρ_H(X_ν)H⟩)` and the Dirac
current `v Re{(i/2)[Ψ̄γ^μρ_S(X_μ)Ψ + Ψ̄ρ_S(X_μ)γ^μΨ]}`). -/
def gaugeCur (wp : FJ 𝔄 𝓗 𝓢) (X : Fin 4 → 𝔄) : ℝ :=
  -(volume wp.1.1 * ∑ μ, ∑ ν, ginv wp.1.1 μ ν *
      (D.hermH (D.ρH (X μ) wp.1.2.2.1) (KH D wp ν) + D.hermH (KH D wp μ) (D.ρH (X ν) wp.1.2.2.1))) +
    volume wp.1.1 * (Complex.I / 2 * ∑ μ, (wp.1.2.2.2.2 (gammaMu D μ wp.1.1
        (D.ρS (X μ) wp.1.2.2.2.1)) -
      (wp.1.2.2.2.2.comp (-D.ρS (X μ))) (gammaMu D μ wp.1.1 wp.1.2.2.2.1))).re

section GaugeLine

/-- The value line `t ↦ (w + t (0, X, 0, 0, 0), p)` through a first jet. -/
def gLine (wp : FJ 𝔄 𝓗 𝓢) (X : Fin 4 → 𝔄) (t : ℝ) : FJ 𝔄 𝓗 𝓢 :=
  wp + t • ((gaugeDir X : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢))

variable (wp : FJ 𝔄 𝓗 𝓢) (X : Fin 4 → 𝔄) (t : ℝ)

theorem gLine_zero : gLine wp X 0 = wp := by
  unfold gLine
  exact (congrArg (fun q : FJ 𝔄 𝓗 𝓢 => wp + q) (zero_smul ℝ _)).trans (add_zero wp)

theorem gl_e : (gLine wp X t).1.1 = wp.1.1 := by
  simp [gLine, gaugeDir]

theorem gl_A (μ : Fin 4) : (gLine wp X t).1.2.1 μ = wp.1.2.1 μ + t • X μ := by
  simp [gLine, gaugeDir]

theorem gl_H : (gLine wp X t).1.2.2.1 = wp.1.2.2.1 := by
  simp [gLine, gaugeDir]

theorem gl_Ψ : (gLine wp X t).1.2.2.2.1 = wp.1.2.2.2.1 := by
  simp only [gLine, gaugeDir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem gl_Ψb : (gLine wp X t).1.2.2.2.2 = wp.1.2.2.2.2 := by
  simp only [gLine, gaugeDir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem gl_p : (gLine wp X t).2 = wp.2 := by
  simp only [gLine, Prod.snd_add, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

end GaugeLine

/-- The value-line derivative of `L₀` in a gauge direction. -/
theorem hasDerivAt_L0_gaugeLine (wp : FJ 𝔄 𝓗 𝓢) (X : Fin 4 → 𝔄) :
    HasDerivAt (fun t : ℝ => L0 D (gLine wp X t))
      (-(4⁻¹ * volume wp.1.1 * ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ginv wp.1.1 μ ρ * ginv wp.1.1 ν σ *
          (D.ipA (BA wp X μ ν) (FA wp ρ σ) + D.ipA (FA wp μ ν) (BA wp X ρ σ))) +
        gaugeCur D wp X) 0 := by
  -- the field strength along the line
  have hFl : ∀ μ ν, HasDerivAt (fun t : ℝ => FA (gLine wp X t) μ ν) (BA wp X μ ν) 0 := by
    intro μ ν
    have hfun : (fun t : ℝ => FA (gLine wp X t) μ ν) = fun t =>
        (wp.2 μ).2.1 ν - (wp.2 ν).2.1 μ + ((wp.1.2.1 μ + t • X μ) * (wp.1.2.1 ν + t • X ν) -
          (wp.1.2.1 ν + t • X ν) * (wp.1.2.1 μ + t • X μ)) := by
      funext t
      unfold FA
      simp only [gl_A, gl_p]
    rw [hfun]
    have h1 := (hasDerivAt_affine (wp.1.2.1 μ) (X μ)).mul (hasDerivAt_affine (wp.1.2.1 ν) (X ν))
    have h2 := (hasDerivAt_affine (wp.1.2.1 ν) (X ν)).mul (hasDerivAt_affine (wp.1.2.1 μ) (X μ))
    refine ((h1.sub h2).const_add ((wp.2 μ).2.1 ν - (wp.2 ν).2.1 μ)).congr_deriv ?_
    unfold BA
    simp only [zero_smul, add_zero]
  -- Yang–Mills
  have hYM0 : HasDerivAt (fun t : ℝ => ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ginv wp.1.1 μ ρ * ginv wp.1.1 ν σ *
      D.ipA (FA (gLine wp X t) μ ν) (FA (gLine wp X t) ρ σ))
      (∑ μ, ∑ ν, ∑ ρ, ∑ σ, ginv wp.1.1 μ ρ * ginv wp.1.1 ν σ *
          (D.ipA (BA wp X μ ν) (FA wp ρ σ) + D.ipA (FA wp μ ν) (BA wp X ρ σ))) 0 := by
    refine HasDerivAt.fun_sum fun μ _ => HasDerivAt.fun_sum fun ν _ =>
      HasDerivAt.fun_sum fun ρ _ => HasDerivAt.fun_sum fun σ _ => HasDerivAt.const_mul _ ?_
    have h := hasDerivAt_bilin D.ipA (hFl μ ν) (hFl ρ σ)
    rw [gLine_zero] at h
    exact h
  have hYM : HasDerivAt (fun t : ℝ => LYMc D (gLine wp X t))
      (-(4⁻¹ * volume wp.1.1 * ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ginv wp.1.1 μ ρ * ginv wp.1.1 ν σ *
          (D.ipA (BA wp X μ ν) (FA wp ρ σ) + D.ipA (FA wp μ ν) (BA wp X ρ σ)))) 0 := by
    unfold LYMc
    simp only [gl_e]
    exact (hYM0.const_mul _).neg
  -- Higgs
  have hKl : ∀ μ, HasDerivAt (fun t : ℝ => KH D (gLine wp X t) μ) (D.ρH (X μ) wp.1.2.2.1) 0 := by
    intro μ
    have hfun : (fun t : ℝ => KH D (gLine wp X t) μ) =
        fun t => KH D wp μ + t • D.ρH (X μ) wp.1.2.2.1 := by
      funext t
      unfold KH
      rw [gl_A, gl_H, gl_p, map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply]
      abel
    rw [hfun]
    exact hasDerivAt_affine _ _
  have hH0 : HasDerivAt (fun t : ℝ => ∑ μ, ∑ ν, ginv wp.1.1 μ ν *
      D.hermH (KH D (gLine wp X t) μ) (KH D (gLine wp X t) ν))
      (∑ μ, ∑ ν, ginv wp.1.1 μ ν *
        (D.hermH (D.ρH (X μ) wp.1.2.2.1) (KH D wp ν) +
          D.hermH (KH D wp μ) (D.ρH (X ν) wp.1.2.2.1))) 0 := by
    refine HasDerivAt.fun_sum fun μ _ => HasDerivAt.fun_sum fun ν _ => HasDerivAt.const_mul _ ?_
    have h := hasDerivAt_bilin D.hermH (hKl μ) (hKl ν)
    rw [gLine_zero] at h
    exact h
  have hH : HasDerivAt (fun t : ℝ => LHc D (gLine wp X t))
      (-(volume wp.1.1 * ∑ μ, ∑ ν, ginv wp.1.1 μ ν *
        (D.hermH (D.ρH (X μ) wp.1.2.2.1) (KH D wp ν) +
          D.hermH (KH D wp μ) (D.ρH (X ν) wp.1.2.2.1)))) 0 := by
    unfold LHc
    simp only [gl_e, gl_H]
    exact ((hH0.const_mul _).neg).sub_const _
  -- Dirac
  have hDl : ∀ μ t, DPsi D (gLine wp X t) μ = DPsi D wp μ + t • D.ρS (X μ) wp.1.2.2.2.1 := by
    intro μ t
    unfold DPsi omC
    rw [gl_A, gl_e, gl_Ψ, gl_p, map_add, map_smul]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    abel
  have hDbl : ∀ μ t, DPsiBar D (gLine wp X t) μ =
      DPsiBar D wp μ + t • wp.1.2.2.2.2.comp (-D.ρS (X μ)) := by
    intro μ t
    unfold DPsiBar omC
    rw [gl_A, gl_e, gl_Ψb, gl_p, map_add, map_smul]
    ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
      map_add, map_neg, map_sub, map_smul]
    module
  have hΦ0 : HasDerivAt (fun t : ℝ => ∑ μ,
      (wp.1.2.2.2.2 (gammaMu D μ wp.1.1 (DPsi D (gLine wp X t) μ)) -
        DPsiBar D (gLine wp X t) μ (gammaMu D μ wp.1.1 wp.1.2.2.2.1)))
      (∑ μ, (wp.1.2.2.2.2 (gammaMu D μ wp.1.1 (D.ρS (X μ) wp.1.2.2.2.1)) -
        (wp.1.2.2.2.2.comp (-D.ρS (X μ))) (gammaMu D μ wp.1.1 wp.1.2.2.2.1))) 0 := by
    refine HasDerivAt.fun_sum fun μ _ => ?_
    simp only [hDl, hDbl]
    have h1 := ((wp.1.2.2.2.2.comp (gammaMu D μ wp.1.1)).hasFDerivAt).comp_hasDerivAt (0 : ℝ)
      (hasDerivAt_affine (DPsi D wp μ) (D.ρS (X μ) wp.1.2.2.2.1))
    have h2 := (hasDerivAt_affine (DPsiBar D wp μ) (wp.1.2.2.2.2.comp (-D.ρS (X μ)))).clm_apply
      (hasDerivAt_const (0 : ℝ) (gammaMu D μ wp.1.1 wp.1.2.2.2.1))
    refine (h1.sub h2).congr_deriv ?_
    simp
  have hD : HasDerivAt (fun t : ℝ => LDc D (gLine wp X t))
      (volume wp.1.1 * (Complex.I / 2 * ∑ μ, (wp.1.2.2.2.2 (gammaMu D μ wp.1.1
        (D.ρS (X μ) wp.1.2.2.2.1)) -
        (wp.1.2.2.2.2.comp (-D.ρS (X μ))) (gammaMu D μ wp.1.1 wp.1.2.2.2.1))).re) 0 := by
    unfold LDc
    simp only [gl_e, gl_H, gl_Ψ, gl_Ψb]
    exact ((Complex.reCLM.hasFDerivAt).comp_hasDerivAt (0 : ℝ)
      ((hΦ0.const_mul (Complex.I / 2)).sub_const _)).const_mul _
  -- gravity
  have hg : (fun t : ℝ => Lgc D (gLine wp X t)) = fun _ => Lgc D wp := by
    funext t
    unfold Lgc
    rw [gl_e, gl_p]
  have hg' : HasDerivAt (fun t : ℝ => Lgc D (gLine wp X t)) 0 0 := by
    rw [hg]; exact hasDerivAt_const _ _
  have hsum := ((hg'.add hYM).add hH).add hD
  have hfun : (fun t : ℝ => L0 D (gLine wp X t)) = fun t => Lgc D (gLine wp X t) +
      LYMc D (gLine wp X t) + LHc D (gLine wp X t) + LDc D (gLine wp X t) :=
    funext fun t => L0_eq D _
  rw [hfun]
  refine hsum.congr_deriv ?_
  unfold gaugeCur
  ring

section DerivLine

/-- The derivative line `t ↦ (w, p + t e_μ ⊗ (0, X, 0, 0, 0))` through a first jet. -/
def pLine (wp : FJ 𝔄 𝓗 𝓢) (X : Fin 4 → 𝔄) (μ : Fin 4) (t : ℝ) : FJ 𝔄 𝓗 𝓢 :=
  wp + t • ((0 : Field 𝔄 𝓗 𝓢), Pi.single μ (gaugeDir X : Field 𝔄 𝓗 𝓢))

/-- The jet direction `δ_{αβ} = [α = μ] X_β` of `∂_α A_β`. -/
def dJ (X : Fin 4 → 𝔄) (μ α β : Fin 4) : 𝔄 := if α = μ then X β else 0

variable (wp : FJ 𝔄 𝓗 𝓢) (X : Fin 4 → 𝔄) (μ : Fin 4) (t : ℝ)

theorem pLine_zero : pLine wp X μ 0 = wp := by
  unfold pLine
  exact (congrArg (fun q : FJ 𝔄 𝓗 𝓢 => wp + q) (zero_smul ℝ _)).trans (add_zero wp)

theorem pl_w : (pLine wp X μ t).1 = wp.1 := by
  simp only [pLine, Prod.fst_add, Prod.smul_fst]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem single_gaugeDir_apply (α : Fin 4) :
    (Pi.single μ (gaugeDir X : Field 𝔄 𝓗 𝓢) : Fin 4 → Field 𝔄 𝓗 𝓢) α =
      ((0 : Mat), (dJ X μ α), (0 : 𝓗), (0 : 𝓢), (0 : CoSpinor 𝓢)) := by
  by_cases h : α = μ
  · subst h
    rw [Pi.single_eq_same]
    unfold gaugeDir
    congr 2
    funext β
    simp [dJ]
  · rw [Pi.single_eq_of_ne h]
    unfold dJ
    simp only [h, if_false]
    rfl

theorem pl_p (α : Fin 4) : (pLine wp X μ t).2 α =
    wp.2 α + t • ((0 : Mat), (dJ X μ α), (0 : 𝓗), (0 : 𝓢), (0 : CoSpinor 𝓢)) := by
  simp only [pLine, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
    single_gaugeDir_apply]

theorem pl_e (α : Fin 4) : ((pLine wp X μ t).2 α).1 = (wp.2 α).1 := by
  rw [pl_p]
  simp only [Prod.fst_add, Prod.smul_fst]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem pl_A (α β : Fin 4) : ((pLine wp X μ t).2 α).2.1 β = (wp.2 α).2.1 β + t • dJ X μ α β := by
  rw [pl_p]
  simp

theorem pl_H (α : Fin 4) : ((pLine wp X μ t).2 α).2.2.1 = (wp.2 α).2.2.1 := by
  rw [pl_p]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem pl_Ψ (α : Fin 4) : ((pLine wp X μ t).2 α).2.2.2.1 = (wp.2 α).2.2.2.1 := by
  rw [pl_p]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem pl_Ψb (α : Fin 4) : ((pLine wp X μ t).2 α).2.2.2.2 = (wp.2 α).2.2.2.2 := by
  rw [pl_p]
  simp only [Prod.snd_add, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem pl_FA (α β : Fin 4) :
    FA (pLine wp X μ t) α β = FA wp α β + t • (dJ X μ α β - dJ X μ β α) := by
  unfold FA
  rw [pl_w, pl_A, pl_A, smul_sub]
  abel

theorem pl_e' : (fun l => ((pLine wp X μ t).2 l).1) = fun l => (wp.2 l).1 :=
  funext fun l => pl_e wp X μ t l

theorem pl_KH (α : Fin 4) : KH D (pLine wp X μ t) α = KH D wp α := by
  unfold KH; rw [pl_w, pl_H]

theorem pl_DPsi (α : Fin 4) : DPsi D (pLine wp X μ t) α = DPsi D wp α := by
  unfold DPsi omC; rw [pl_w, pl_Ψ, pl_e']

theorem pl_DPsiBar (α : Fin 4) : DPsiBar D (pLine wp X μ t) α = DPsiBar D wp α := by
  unfold DPsiBar omC; rw [pl_w, pl_Ψb, pl_e']

end DerivLine

/-- The derivative-line derivative of `L₀` in the jet direction `∂_μ A ↦ ∂_μ A + tX`. -/
theorem hasDerivAt_L0_pLine (wp : FJ 𝔄 𝓗 𝓢) (X : Fin 4 → 𝔄) (μ : Fin 4) :
    HasDerivAt (fun t : ℝ => L0 D (pLine wp X μ t))
      (-(4⁻¹ * volume wp.1.1 * ∑ α, ∑ β, ∑ ρ, ∑ σ, ginv wp.1.1 α ρ * ginv wp.1.1 β σ *
          (D.ipA (dJ X μ α β - dJ X μ β α) (FA wp ρ σ) +
            D.ipA (FA wp α β) (dJ X μ ρ σ - dJ X μ σ ρ)))) 0 := by
  have hfun : (fun t : ℝ => L0 D (pLine wp X μ t)) = fun t =>
      Lgc D wp + -(4⁻¹ * volume wp.1.1 * ∑ α, ∑ β, ∑ ρ, ∑ σ, ginv wp.1.1 α ρ * ginv wp.1.1 β σ *
        D.ipA (FA wp α β + t • (dJ X μ α β - dJ X μ β α))
          (FA wp ρ σ + t • (dJ X μ ρ σ - dJ X μ σ ρ))) + LHc D wp + LDc D wp := by
    funext t
    rw [L0_eq]
    unfold Lgc LYMc LHc LDc
    simp only [pl_w, pl_e', pl_KH, pl_DPsi, pl_DPsiBar, pl_FA]
  rw [hfun]
  have h0 : HasDerivAt (fun t : ℝ => ∑ α, ∑ β, ∑ ρ, ∑ σ, ginv wp.1.1 α ρ * ginv wp.1.1 β σ *
      D.ipA (FA wp α β + t • (dJ X μ α β - dJ X μ β α))
        (FA wp ρ σ + t • (dJ X μ ρ σ - dJ X μ σ ρ)))
      (∑ α, ∑ β, ∑ ρ, ∑ σ, ginv wp.1.1 α ρ * ginv wp.1.1 β σ *
        (D.ipA (dJ X μ α β - dJ X μ β α) (FA wp ρ σ) +
          D.ipA (FA wp α β) (dJ X μ ρ σ - dJ X μ σ ρ))) 0 := by
    refine HasDerivAt.fun_sum fun α _ => HasDerivAt.fun_sum fun β _ =>
      HasDerivAt.fun_sum fun ρ _ => HasDerivAt.fun_sum fun σ _ => HasDerivAt.const_mul _ ?_
    have h := hasDerivAt_bilin D.ipA (hasDerivAt_affine (FA wp α β) (dJ X μ α β - dJ X μ β α))
      (hasDerivAt_affine (FA wp ρ σ) (dJ X μ ρ σ - dJ X μ σ ρ))
    simpa using h
  have := (((hasDerivAt_const (0 : ℝ) (Lgc D wp)).add
    ((h0.const_mul (4⁻¹ * volume wp.1.1)).neg)).add_const (LHc D wp)).add_const (LDc D wp)
  simpa using this

theorem ginv_symm' (e : Mat) (a b : Fin 4) : ginv e a b = ginv e b a :=
  ginvOf_symm' (g := fun i j => metric e i j) (fun i j => metric_symm e i j) a b

theorem chartF_mem {wp : FJ 𝔄 𝓗 𝓢} (h : wp.1.1.det ≠ 0) : wp ∈ (chartF : Set (FJ 𝔄 𝓗 𝓢)) := h

theorem differentiableAt_L0 {wp : FJ 𝔄 𝓗 𝓢} (h : wp.1.1.det ≠ 0) :
    DifferentiableAt ℝ (L0 D) wp :=
  ((contDiffOn_L0 D).contDiffAt (isOpen_chartF.mem_nhds h)).differentiableAt (by simp)

/-- **The jet partial of `L₀` in `∂_μ A`**:
`∂L₀/∂(∂_μA_ν)[X_ν] = -v g^{μρ}g^{νσ}⟨X_ν, F_{ρσ}⟩` (symmetric invariant form). -/
theorem fderiv_L0_dA (hsym : ∀ x y, D.ipA x y = D.ipA y x) {wp : FJ 𝔄 𝓗 𝓢}
    (h : wp.1.1.det ≠ 0) (X : Fin 4 → 𝔄) (μ : Fin 4) :
    fderiv ℝ (L0 D) wp ((0 : Field 𝔄 𝓗 𝓢), Pi.single μ (gaugeDir X : Field 𝔄 𝓗 𝓢)) =
      -(volume wp.1.1 * ∑ ν, ∑ ρ, ∑ σ, ginv wp.1.1 μ ρ * ginv wp.1.1 ν σ *
        D.ipA (X ν) (FA wp ρ σ)) := by
  have hl : HasDerivAt (fun t : ℝ => L0 D (wp + t • ((0 : Field 𝔄 𝓗 𝓢),
      Pi.single μ (gaugeDir X : Field 𝔄 𝓗 𝓢)))) _ 0 := hasDerivAt_L0_pLine D wp X μ
  refine (fderiv_apply_of_line (differentiableAt_L0 D h) hl).trans ?_
  rw [ym_sym D.ipA hsym (ginv wp.1.1) (ginv_symm' wp.1.1) (FA wp) (FA_anti wp) (dJ X μ)]
  congr 2
  simp only [dJ]
  rw [Finset.sum_eq_single μ (fun α _ hα => by simp [hα]) (by simp)]
  simp

/-- **The value partial of `L₀` in `A`**: with an ad-invariant symmetric form,
`∂L₀/∂A_ν[X_ν] = v g^{αρ}g^{βσ}⟨X_β, [A_α, F_{ρσ}]⟩ + (matter current)`. -/
theorem fderiv_L0_A (hsym : ∀ x y, D.ipA x y = D.ipA y x)
    (hinv : ∀ a x y, D.ipA (a * x - x * a) y = -D.ipA x (a * y - y * a)) {wp : FJ 𝔄 𝓗 𝓢}
    (h : wp.1.1.det ≠ 0) (X : Fin 4 → 𝔄) :
    fderiv ℝ (L0 D) wp ((gaugeDir X : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) =
      volume wp.1.1 * ∑ α, ∑ β, ∑ ρ, ∑ σ, ginv wp.1.1 α ρ * ginv wp.1.1 β σ *
        D.ipA (X β) (wp.1.2.1 α * FA wp ρ σ - FA wp ρ σ * wp.1.2.1 α) + gaugeCur D wp X := by
  have hl : HasDerivAt (fun t : ℝ => L0 D (wp + t • ((gaugeDir X : Field 𝔄 𝓗 𝓢),
      (0 : Fin 4 → Field 𝔄 𝓗 𝓢)))) _ 0 := hasDerivAt_L0_gaugeLine D wp X
  refine (fderiv_apply_of_line (differentiableAt_L0 D h) hl).trans ?_
  have hB : ∀ α β, BA wp X α β = (wp.1.2.1 α * X β - X β * wp.1.2.1 α) -
      (wp.1.2.1 β * X α - X α * wp.1.2.1 β) := fun α β => by unfold BA; abel
  simp only [hB]
  rw [ym_sym D.ipA hsym (ginv wp.1.1) (ginv_symm' wp.1.1) (FA wp) (FA_anti wp)]
  simp only [hinv]
  congr 1
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

/-! ### The Yang–Mills Euler row of a native field -/

/-- The coframe field of a native field. -/
def eF (Y : R4 → Field 𝔄 𝓗 𝓢) : R4 → Mat := fun y => (Y y).1

/-- The field strength `F_{μν}(y)` of a native field. -/
def Ff (Y : R4 → Field 𝔄 𝓗 𝓢) (y : R4) (μ ν : Fin 4) : 𝔄 := FA (jet1 Y y) μ ν

/-- **The Yang–Mills divergence of a native field in Christoffel form**
`g^{μρ}(∇_ρF_{μσ} + [A_ρ, F_{μσ}])`, `∇_ρF_{μσ} = ∂_ρF_{μσ} - Γ^l_{ρμ}F_{lσ} - Γ^l_{ρσ}F_{μl}`
(`Γ` the Christoffel symbols of `g = eᵀηe`; the formula of `ActualJetGauge.ymDiv`). -/
def ymDivN (Y : R4 → Field 𝔄 𝓗 𝓢) (z : R4) (σ : Fin 4) : 𝔄 :=
  ∑ μ, ∑ ρ, ginvOf (gF (eF Y) z) μ ρ • (pd (fun y => Ff Y y μ σ) ρ z -
    ∑ l, (chr (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z) l ρ μ • Ff Y z l σ +
      chr (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z) l ρ σ • Ff Y z μ l) +
    ((Y z).2.1 ρ * Ff Y z μ σ - Ff Y z μ σ * (Y z).2.1 ρ))

theorem contDiff_FA (μ ν : Fin 4) : ContDiff ℝ ∞ (fun wp : FJ 𝔄 𝓗 𝓢 => FA wp μ ν) := by
  unfold FA
  fun_prop

theorem contDiff_Ff {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y) (μ ν : Fin 4) :
    ContDiff ℝ ∞ (fun y => Ff Y y μ ν) :=
  (contDiff_FA μ ν).comp (ContEulerBounds.contDiff_jet1_infty hY)

theorem Ff_anti (Y : R4 → Field 𝔄 𝓗 𝓢) (y : R4) (μ ν : Fin 4) : Ff Y y ν μ = -Ff Y y μ ν :=
  FA_anti _ μ ν

theorem pd_neg_sum {φ : Fin 4 → R4 → ℝ} {z : R4} (hφ : ∀ ν, DifferentiableAt ℝ (φ ν) z)
    (μ : Fin 4) : pd (fun y => -∑ ν, φ ν y) μ z = -∑ ν, pd (φ ν) μ z := by
  have hd : DifferentiableAt ℝ (fun y => -∑ ν, φ ν y) z :=
    (DifferentiableAt.fun_sum fun ν _ => hφ ν).neg
  refine pd_eq_of_line' hd ?_
  exact (HasDerivAt.fun_sum fun ν _ => hasDerivAt_line' μ (hφ ν)).neg

theorem ginv_eF (Y : R4 → Field 𝔄 𝓗 𝓢) (z : R4) (a b : Fin 4) :
    ginv (Y z).1 a b = ginvOf (gF (eF Y) z) a b := rfl

theorem jet1_fst (Y : R4 → Field 𝔄 𝓗 𝓢) (z : R4) : (jet1 Y z).1 = Y z := rfl

theorem FA_jet1 (Y : R4 → Field 𝔄 𝓗 𝓢) (z : R4) (μ ν : Fin 4) : FA (jet1 Y z) μ ν = Ff Y z μ ν :=
  rfl

theorem volume_eF (Y : R4 → Field 𝔄 𝓗 𝓢) (z : R4) : volume (Y z).1 = volume (eF Y z) := rfl

set_option maxHeartbeats 1000000 in
/-- **The Yang–Mills Euler row of the native continuum Lagrangian** (bridge step P3, gauge
sector): for a smooth native field with `det e > 0`, a symmetric ad-invariant form `⟨·,·⟩_𝐠`
and every gauge direction `X`,
`𝓔₀(Y)(z)[(0, X, 0, 0, 0)] = v(e) g^{νσ}⟨X_ν, ∇^μF_{μσ} + [A^μ, F_{μσ}]⟩ + j(X)`,
the Yang–Mills divergence in Christoffel form (`ymDivN`) paired with `X` through the invariant
form and the inverse metric, plus the matter current covector `j = ∂_A(L_H + L_D)` (`gaugeCur`). -/
theorem ym_euler_row (hsym : ∀ x y, D.ipA x y = D.ipA y x)
    (hinv : ∀ a x y, D.ipA (a * x - x * a) y = -D.ipA x (a * y - y * a))
    {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y) (hdet : ∀ z, 0 < ((Y z).1).det) (z : R4)
    (X : Fin 4 → 𝔄) :
    contEuler (L0 D) Y z (gaugeDir X) =
      volume (Y z).1 * ∑ ν, ∑ σ, ginvOf (gF (eF Y) z) ν σ * D.ipA (X ν) (ymDivN Y z σ) +
        gaugeCur D (jet1 Y z) X := by
  have he : ContDiff ℝ ∞ (eF Y) := contDiff_fst.comp hY
  have hdet' : ∀ z, 0 < (eF Y z).det := hdet
  have hJU : ∀ y, jet1 Y y ∈ (chartF : Set (FJ 𝔄 𝓗 𝓢)) := fun y => (hdet y).ne'
  have hE := contEuler_apply (L := L0 D) isOpen_chartF (contDiffOn_L0 D) hY hJU z
    (gaugeDir X : Field 𝔄 𝓗 𝓢)
  refine hE.trans ?_
  have hA := fderiv_L0_A D hsym hinv (wp := jet1 Y z) (hdet z).ne' X
  simp only [jet1_fst, ginv_eF, FA_jet1, volume_eF] at hA
  have hpt : ∀ μ, (fun z' => fderiv ℝ (L0 D) (jet1 Y z') ((0 : Field 𝔄 𝓗 𝓢),
      Pi.single μ (gaugeDir X : Field 𝔄 𝓗 𝓢))) = fun z' => -∑ ν, (volume (eF Y z') *
        ∑ ρ, ∑ σ, ginvOf (gF (eF Y) z') μ ρ * ginvOf (gF (eF Y) z') ν σ *
          D.ipA (X ν) (Ff Y z' ρ σ)) := by
    intro μ
    funext z'
    rw [fderiv_L0_dA D hsym (wp := jet1 Y z') (hdet z').ne' X μ, Finset.mul_sum]
    simp only [jet1_fst, ginv_eF, FA_jet1, volume_eF]
  -- smoothness of the summands
  have hφ : ∀ μ ν, ContDiff ℝ ∞ (fun z' => volume (eF Y z') *
      ∑ ρ, ∑ σ, ginvOf (gF (eF Y) z') μ ρ * ginvOf (gF (eF Y) z') ν σ *
        D.ipA (X ν) (Ff Y z' ρ σ)) := by
    intro μ ν
    refine (contDiff_volume_comp he hdet').mul (ContDiff.sum fun ρ _ => ContDiff.sum fun σ _ =>
      ((contDiff_ginv he hdet' μ ρ).mul (contDiff_ginv he hdet' ν σ)).mul ?_)
    exact (D.ipA (X ν)).contDiff.comp (contDiff_Ff hY ρ σ)
  have hdiv : ∑ μ, pd (fun z' => fderiv ℝ (L0 D) (jet1 Y z') ((0 : Field 𝔄 𝓗 𝓢),
      Pi.single μ (gaugeDir X : Field 𝔄 𝓗 𝓢))) μ z =
      -∑ ν, volume (eF Y z) * ∑ σ, ginvOf (gF (eF Y) z) ν σ * ∑ μ, ∑ ρ,
        ginvOf (gF (eF Y) z) μ ρ * (D.ipA (X ν) (pd (fun y => Ff Y y μ σ) ρ z) -
          ∑ l, (chr (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z) l ρ μ * D.ipA (X ν) (Ff Y z l σ) +
            chr (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z) l ρ σ *
              D.ipA (X ν) (Ff Y z μ l))) := by
    simp only [hpt]
    rw [Finset.sum_congr rfl fun μ _ => pd_neg_sum (fun ν => ((hφ μ ν).differentiable
      (by simp)) z) μ, Finset.sum_neg_distrib, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun ν _ => ?_
    have hf : ∀ ρ σ, ContDiff ℝ ∞ (fun y => D.ipA (X ν) (Ff Y y ρ σ)) := fun ρ σ =>
      (D.ipA (X ν)).contDiff.comp (contDiff_Ff hY ρ σ)
    have hanti : ∀ y ρ σ, D.ipA (X ν) (Ff Y y ρ σ) = -D.ipA (X ν) (Ff Y y σ ρ) := by
      intro y ρ σ; rw [Ff_anti, map_neg]
    refine (sum_pd_form_density he hdet' hf hanti ν z).trans ?_
    refine congrArg _ (Finset.sum_congr rfl fun σ _ => congrArg _ (Finset.sum_congr rfl
      fun μ _ => Finset.sum_congr rfl fun ρ _ => ?_))
    rw [pd_clm (D.ipA (X ν)) ((contDiff_Ff hY μ σ).differentiable (by simp) z)]
  refine (congrArg₂ (· - ·) hA hdiv).trans ?_
  -- the commutator term
  have hcomm : ∑ α, ∑ β, ∑ ρ, ∑ σ, ginvOf (gF (eF Y) z) α ρ * ginvOf (gF (eF Y) z) β σ *
      D.ipA (X β) ((Y z).2.1 α * Ff Y z ρ σ - Ff Y z ρ σ * (Y z).2.1 α) =
      ∑ ν, ∑ σ, ginvOf (gF (eF Y) z) ν σ * ∑ μ, ∑ ρ, ginvOf (gF (eF Y) z) μ ρ *
        D.ipA (X ν) ((Y z).2.1 ρ * Ff Y z μ σ - Ff Y z μ σ * (Y z).2.1 ρ) := by
    simp only [Finset.mul_sum, ← mul_assoc]
    exact sum4_reindex _ _ { toFun := fun x => (x.2.1, x.2.2.2, x.2.2.1, x.1)
                             invFun := fun x => (x.2.2.2, x.1, x.2.2.1, x.2.1)
                             left_inv := fun x => rfl
                             right_inv := fun x => rfl } fun x => by
        simp only [Equiv.coe_fn_mk]
        rw [ginv_symm z x.1 x.2.2.1]
        ring
  -- expand the right-hand side
  have hR : ∑ ν, ∑ σ, ginvOf (gF (eF Y) z) ν σ * D.ipA (X ν) (ymDivN Y z σ) =
      ∑ ν, ∑ σ, ginvOf (gF (eF Y) z) ν σ * ∑ μ, ∑ ρ,
        ginvOf (gF (eF Y) z) μ ρ * (D.ipA (X ν) (pd (fun y => Ff Y y μ σ) ρ z) -
          ∑ l, (chr (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z) l ρ μ * D.ipA (X ν) (Ff Y z l σ) +
            chr (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z) l ρ σ *
              D.ipA (X ν) (Ff Y z μ l))) +
      ∑ ν, ∑ σ, ginvOf (gF (eF Y) z) ν σ * ∑ μ, ∑ ρ, ginvOf (gF (eF Y) z) μ ρ *
        D.ipA (X ν) ((Y z).2.1 ρ * Ff Y z μ σ - Ff Y z μ σ * (Y z).2.1 ρ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← mul_add]
    congr 1
    unfold ymDivN
    simp only [map_sum, map_smul, map_add, map_sub, smul_eq_mul]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    ring
  have hY : ∑ ν, volume (eF Y z) * ∑ σ, ginvOf (gF (eF Y) z) ν σ * ∑ μ, ∑ ρ,
        ginvOf (gF (eF Y) z) μ ρ * (D.ipA (X ν) (pd (fun y => Ff Y y μ σ) ρ z) -
          ∑ l, (chr (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z) l ρ μ * D.ipA (X ν) (Ff Y z l σ) +
            chr (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z) l ρ σ *
              D.ipA (X ν) (Ff Y z μ l))) =
      volume (eF Y z) * ∑ ν, ∑ σ, ginvOf (gF (eF Y) z) ν σ * ∑ μ, ∑ ρ,
        ginvOf (gF (eF Y) z) μ ρ * (D.ipA (X ν) (pd (fun y => Ff Y y μ σ) ρ z) -
          ∑ l, (chr (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z) l ρ μ * D.ipA (X ν) (Ff Y z l σ) +
            chr (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z) l ρ σ *
              D.ipA (X ν) (Ff Y z μ l))) := (Finset.mul_sum _ _ _).symm
  simp only [volume_eF]
  linear_combination hY - volume (eF Y z) * hR + volume (eF Y z) * hcomm

/-! ### Identification with the slab-model Yang–Mills residual -/

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The gauge potential `A_μ(y)` of a native field. -/
def Af (Y : R4 → Field 𝔄 𝓗 𝓢) (y : R4) (μ : Fin 4) : 𝔄 := (Y y).2.1 μ

/-- Its first jet `∂_γA_μ(y)`. -/
def dAf (Y : R4 → Field 𝔄 𝓗 𝓢) (y : R4) (γ μ : Fin 4) : 𝔄 := pd (fun y => Af Y y μ) γ y

/-- Its second jet `∂_α∂_γA_μ(y)`. -/
def ddAf (Y : R4 → Field 𝔄 𝓗 𝓢) (y : R4) (α γ μ : Fin 4) : 𝔄 := pd (fun y => dAf Y y γ μ) α y

/-- The gauge-component projection `Field → (Fin 4 → 𝔄) → 𝔄`. -/
def projA (μ : Fin 4) : Field 𝔄 𝓗 𝓢 →L[ℝ] 𝔄 :=
  (ContinuousLinearMap.proj μ).comp ((ContinuousLinearMap.fst ℝ (Fin 4 → 𝔄) _).comp
    (ContinuousLinearMap.snd ℝ Mat _))

theorem jet1_A {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : Differentiable ℝ Y) (y : R4) (γ μ : Fin 4) :
    ((jet1 Y y).2 γ).2.1 μ = dAf Y y γ μ := by
  have h := pd_clm (projA (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) μ) (hY y) γ
  unfold dAf Af
  exact h.symm

theorem Ff_eq {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : Differentiable ℝ Y) (y : R4) (μ ν : Fin 4) :
    Ff Y y μ ν = ActualJetWriter.fieldStrength (Af Y y) (dAf Y y) μ ν := by
  unfold Ff FA ActualJetWriter.fieldStrength
  rw [jet1_A hY, jet1_A hY, Ring.lie_def]
  rfl

theorem contDiff_Af {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y) (μ : Fin 4) :
    ContDiff ℝ ∞ (fun y => Af Y y μ) :=
  show ContDiff ℝ ∞ (fun y => projA (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) μ (Y y)) from
    (projA (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) μ).contDiff.comp hY

theorem contDiff_dAf {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y) (γ μ : Fin 4) :
    ContDiff ℝ ∞ (fun y => dAf Y y γ μ) :=
  contDiff_pd' (contDiff_Af hY μ) γ

theorem pd_Ff {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y) (z : R4) (ρ μ σ : Fin 4) :
    pd (fun y => Ff Y y μ σ) ρ z = ActualJetGauge.dFm (Af Y z) (dAf Y z) (ddAf Y z) ρ μ σ := by
  have hYd : Differentiable ℝ Y := hY.differentiable (by simp)
  have hfun : (fun y => Ff Y y μ σ) = fun y => dAf Y y μ σ - dAf Y y σ μ +
      (Af Y y μ * Af Y y σ - Af Y y σ * Af Y y μ) := by
    funext y
    rw [Ff_eq hYd]
    unfold ActualJetWriter.fieldStrength
    rw [Ring.lie_def]
  rw [hfun]
  have hA : ∀ ν, DifferentiableAt ℝ (fun y => Af Y y ν) z := fun ν =>
    (contDiff_Af hY ν).differentiable (by simp) z
  have hdA : ∀ γ ν, DifferentiableAt ℝ (fun y => dAf Y y γ ν) z := fun γ ν =>
    (contDiff_dAf hY γ ν).differentiable (by simp) z
  have hd : DifferentiableAt ℝ (fun y => dAf Y y μ σ - dAf Y y σ μ +
      (Af Y y μ * Af Y y σ - Af Y y σ * Af Y y μ)) z :=
    ((hdA μ σ).sub (hdA σ μ)).add (((hA μ).mul (hA σ)).sub ((hA σ).mul (hA μ)))
  refine pd_eq_of_line' hd ?_
  have h1 := hasDerivAt_line' ρ (hdA μ σ)
  have h2 := hasDerivAt_line' ρ (hdA σ μ)
  have h3 := (hasDerivAt_line' ρ (hA μ)).mul (hasDerivAt_line' ρ (hA σ))
  have h4 := (hasDerivAt_line' ρ (hA σ)).mul (hasDerivAt_line' ρ (hA μ))
  refine ((h1.sub h2).add (h3.sub h4)).congr_deriv ?_
  simp only [line_zero]
  unfold ActualJetGauge.dFm ddAf dAf
  simp only [Ring.lie_def]
  abel

/-- **The native Yang–Mills divergence is the slab-model Yang–Mills divergence**
`ActualJetGauge.ymDiv` (Lie bracket of the associative gauge algebra, `[a, b] = ab - ba`) of the
native potential jets `(A, ∂A, ∂∂A)`, with `g⁻¹` and the Christoffel symbols of `g = eᵀηe`. -/
theorem ymDivN_eq_ymDiv {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y) (z : R4) (σ : Fin 4) :
    ymDivN Y z σ = ActualJetGauge.ymDiv (Af Y z) (dAf Y z) (ddAf Y z) (ginvOf (gF (eF Y) z))
      (chr (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z)) σ := by
  have hYd : Differentiable ℝ Y := hY.differentiable (by simp)
  unfold ymDivN ActualJetGauge.ymDiv ActualJetGauge.Fm
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ρ _ => ?_
  rw [pd_Ff hY]
  simp only [Ff_eq hYd, Ring.lie_def]
  rfl

/-- **The Yang–Mills Euler row as the slab-model Yang–Mills residual**: if `J` is a current
represented through the invariant form, `v g^{νσ}⟨X_ν, J_σ⟩ = -j(X)` for all `X` (`gaugeCur`),
then `𝓔₀(Y)(z)[(0, X, 0, 0, 0)] = v(e) g^{νσ}⟨X_ν, r^A_σ⟩` with
`r^A = ActualJetGauge.ymRes A ∂A ∂∂A g⁻¹ Γ J = ∇^μF_{μσ} + [A^μ, F_{μσ}] - J_σ`. -/
theorem ym_euler_row_ymRes (hsym : ∀ x y, D.ipA x y = D.ipA y x)
    (hinv : ∀ a x y, D.ipA (a * x - x * a) y = -D.ipA x (a * y - y * a))
    {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y) (hdet : ∀ z, 0 < ((Y z).1).det) (z : R4)
    (J : Fin 4 → 𝔄)
    (hJ : ∀ X : Fin 4 → 𝔄, volume (Y z).1 * ∑ ν, ∑ σ, ginvOf (gF (eF Y) z) ν σ *
      D.ipA (X ν) (J σ) = -gaugeCur D (jet1 Y z) X) (X : Fin 4 → 𝔄) :
    contEuler (L0 D) Y z (gaugeDir X) =
      volume (Y z).1 * ∑ ν, ∑ σ, ginvOf (gF (eF Y) z) ν σ *
        D.ipA (X ν) (ActualJetGauge.ymRes (Af Y z) (dAf Y z) (ddAf Y z) (ginvOf (gF (eF Y) z))
          (chr (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z)) J σ) := by
  rw [ym_euler_row D hsym hinv hY hdet z X, ← neg_neg (gaugeCur D (jet1 Y z) X), ← hJ X]
  unfold ActualJetGauge.ymRes
  simp only [ymDivN_eq_ymDiv hY, map_sub, mul_sub, Finset.sum_sub_distrib]
  ring

/-! ### The Higgs row -/

/-- The Higgs direction `(0, 0, η, 0, 0)` of the native field space. -/
def higgsDir (η : 𝓗) : Field 𝔄 𝓗 𝓢 := (0, 0, η, 0, 0)

section HiggsLines

/-- The value line `t ↦ (w + t (0, 0, η, 0, 0), p)`. -/
def hLine (wp : FJ 𝔄 𝓗 𝓢) (η : 𝓗) (t : ℝ) : FJ 𝔄 𝓗 𝓢 :=
  wp + t • ((higgsDir η : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢))

/-- The jet direction `[α = μ] η` of `∂_α H`. -/
def dJH (η : 𝓗) (μ α : Fin 4) : 𝓗 := if α = μ then η else 0

/-- The derivative line `t ↦ (w, p + t e_μ ⊗ (0, 0, η, 0, 0))`. -/
def pLineH (wp : FJ 𝔄 𝓗 𝓢) (η : 𝓗) (μ : Fin 4) (t : ℝ) : FJ 𝔄 𝓗 𝓢 :=
  wp + t • ((0 : Field 𝔄 𝓗 𝓢), Pi.single μ (higgsDir η : Field 𝔄 𝓗 𝓢))

variable (wp : FJ 𝔄 𝓗 𝓢) (η : 𝓗) (μ : Fin 4) (t : ℝ)

theorem hLine_zero : hLine wp η 0 = wp := by
  unfold hLine
  exact (congrArg (fun q : FJ 𝔄 𝓗 𝓢 => wp + q) (zero_smul ℝ _)).trans (add_zero wp)

theorem hl_e : (hLine wp η t).1.1 = wp.1.1 := by simp [hLine, higgsDir]

theorem hl_A : (hLine wp η t).1.2.1 = wp.1.2.1 := by simp [hLine, higgsDir]

theorem hl_H : (hLine wp η t).1.2.2.1 = wp.1.2.2.1 + t • η := by simp [hLine, higgsDir]

theorem hl_Ψ : (hLine wp η t).1.2.2.2.1 = wp.1.2.2.2.1 := by
  simp only [hLine, higgsDir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem hl_Ψb : (hLine wp η t).1.2.2.2.2 = wp.1.2.2.2.2 := by
  simp only [hLine, higgsDir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem hl_p : (hLine wp η t).2 = wp.2 := by
  simp only [hLine, Prod.snd_add, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem pLineH_zero : pLineH wp η μ 0 = wp := by
  unfold pLineH
  exact (congrArg (fun q : FJ 𝔄 𝓗 𝓢 => wp + q) (zero_smul ℝ _)).trans (add_zero wp)

theorem ph_w : (pLineH wp η μ t).1 = wp.1 := by
  simp only [pLineH, Prod.fst_add, Prod.smul_fst]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem single_higgsDir_apply (α : Fin 4) :
    (Pi.single μ (higgsDir η : Field 𝔄 𝓗 𝓢) : Fin 4 → Field 𝔄 𝓗 𝓢) α =
      ((0 : Mat), (0 : Fin 4 → 𝔄), dJH η μ α, (0 : 𝓢), (0 : CoSpinor 𝓢)) := by
  by_cases h : α = μ
  · subst h
    rw [Pi.single_eq_same]
    simp [higgsDir, dJH]
  · rw [Pi.single_eq_of_ne h]
    unfold dJH
    simp only [h, if_false]
    rfl

theorem ph_p (α : Fin 4) : (pLineH wp η μ t).2 α =
    wp.2 α + t • ((0 : Mat), (0 : Fin 4 → 𝔄), dJH η μ α, (0 : 𝓢), (0 : CoSpinor 𝓢)) := by
  simp only [pLineH, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
    single_higgsDir_apply]

theorem ph_e (α : Fin 4) : ((pLineH wp η μ t).2 α).1 = (wp.2 α).1 := by
  rw [ph_p]
  simp only [Prod.fst_add, Prod.smul_fst]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem ph_A (α : Fin 4) : ((pLineH wp η μ t).2 α).2.1 = (wp.2 α).2.1 := by
  rw [ph_p]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem ph_H (α : Fin 4) : ((pLineH wp η μ t).2 α).2.2.1 = (wp.2 α).2.2.1 + t • dJH η μ α := by
  rw [ph_p]
  simp

theorem ph_Ψ (α : Fin 4) : ((pLineH wp η μ t).2 α).2.2.2.1 = (wp.2 α).2.2.2.1 := by
  rw [ph_p]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem ph_Ψb (α : Fin 4) : ((pLineH wp η μ t).2 α).2.2.2.2 = (wp.2 α).2.2.2.2 := by
  rw [ph_p]
  simp only [Prod.snd_add, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem ph_e' : (fun l => ((pLineH wp η μ t).2 l).1) = fun l => (wp.2 l).1 :=
  funext fun l => ph_e wp η μ t l

theorem ph_FA (α β : Fin 4) : FA (pLineH wp η μ t) α β = FA wp α β := by
  unfold FA; rw [ph_w, ph_A, ph_A]

theorem ph_KH (α : Fin 4) : KH D (pLineH wp η μ t) α = KH D wp α + t • dJH η μ α := by
  unfold KH; rw [ph_w, ph_H]; abel

theorem ph_DPsi (α : Fin 4) : DPsi D (pLineH wp η μ t) α = DPsi D wp α := by
  unfold DPsi omC; rw [ph_w, ph_Ψ, ph_e']

theorem ph_DPsiBar (α : Fin 4) : DPsiBar D (pLineH wp η μ t) α = DPsiBar D wp α := by
  unfold DPsiBar omC; rw [ph_w, ph_Ψb, ph_e']

theorem hl_FA (α β : Fin 4) : FA (hLine wp η t) α β = FA wp α β := by
  unfold FA; rw [hl_A, hl_p]

theorem hl_KH (α : Fin 4) : KH D (hLine wp η t) α = KH D wp α + t • D.ρH (wp.1.2.1 α) η := by
  unfold KH
  rw [hl_A, hl_H, hl_p, map_add, map_smul]
  abel

theorem hl_e' : (fun l => ((hLine wp η t).2 l).1) = fun l => (wp.2 l).1 := by rw [hl_p]

theorem hl_DPsi (α : Fin 4) : DPsi D (hLine wp η t) α = DPsi D wp α := by
  unfold DPsi omC; rw [hl_e, hl_A, hl_Ψ, hl_e']; rw [hl_p]

theorem hl_DPsiBar (α : Fin 4) : DPsiBar D (hLine wp η t) α = DPsiBar D wp α := by
  unfold DPsiBar omC; rw [hl_e, hl_A, hl_Ψb, hl_e']; rw [hl_p]

end HiggsLines

/-- The Higgs potential gradient `DV(H)[η] = 2λ_H(|H|² - v_H²)(⟨η, H⟩ + ⟨H, η⟩)`. -/
def potGrad (H η : 𝓗) : ℝ :=
  D.lamH * (2 * (D.hermH H H - D.vH ^ 2) * (D.hermH η H + D.hermH H η))

theorem hasDerivAt_potential (H η : 𝓗) :
    HasDerivAt (fun t : ℝ => potential D (H + t • η)) (potGrad D H η) 0 := by
  unfold potential potGrad
  have h := hasDerivAt_bilin D.hermH (hasDerivAt_affine H η) (hasDerivAt_affine H η)
  simp only [zero_smul, add_zero] at h
  have h2 := ((h.sub_const (D.vH ^ 2)).pow 2).const_mul D.lamH
  refine h2.congr_deriv ?_
  simp

/-- The value-line derivative of `L₀` in a Higgs direction. -/
theorem hasDerivAt_L0_hLine (wp : FJ 𝔄 𝓗 𝓢) (η : 𝓗) :
    HasDerivAt (fun t : ℝ => L0 D (hLine wp η t))
      (-(volume wp.1.1 * ∑ μ, ∑ ν, ginv wp.1.1 μ ν *
          (D.hermH (D.ρH (wp.1.2.1 μ) η) (KH D wp ν) +
            D.hermH (KH D wp μ) (D.ρH (wp.1.2.1 ν) η))) -
        volume wp.1.1 * potGrad D wp.1.2.2.1 η -
        volume wp.1.1 * (wp.1.2.2.2.2 (D.yukawa η wp.1.2.2.2.1)).re) 0 := by
  have hK : ∀ μ, HasDerivAt (fun t : ℝ => KH D (hLine wp η t) μ) (D.ρH (wp.1.2.1 μ) η) 0 := by
    intro μ
    simp only [hl_KH]
    exact hasDerivAt_affine _ _
  have hH0 : HasDerivAt (fun t : ℝ => ∑ μ, ∑ ν, ginv wp.1.1 μ ν *
      D.hermH (KH D (hLine wp η t) μ) (KH D (hLine wp η t) ν))
      (∑ μ, ∑ ν, ginv wp.1.1 μ ν *
          (D.hermH (D.ρH (wp.1.2.1 μ) η) (KH D wp ν) +
            D.hermH (KH D wp μ) (D.ρH (wp.1.2.1 ν) η))) 0 := by
    refine HasDerivAt.fun_sum fun μ _ => HasDerivAt.fun_sum fun ν _ => HasDerivAt.const_mul _ ?_
    have h := hasDerivAt_bilin D.hermH (hK μ) (hK ν)
    rw [hLine_zero] at h
    exact h
  have hH : HasDerivAt (fun t : ℝ => LHc D (hLine wp η t))
      (-(volume wp.1.1 * ∑ μ, ∑ ν, ginv wp.1.1 μ ν *
          (D.hermH (D.ρH (wp.1.2.1 μ) η) (KH D wp ν) +
            D.hermH (KH D wp μ) (D.ρH (wp.1.2.1 ν) η))) -
        volume wp.1.1 * potGrad D wp.1.2.2.1 η) 0 := by
    unfold LHc
    simp only [hl_e, hl_H]
    exact ((hH0.const_mul _).neg).sub ((hasDerivAt_potential D _ η).const_mul _)
  have hDy : HasDerivAt (fun t : ℝ => LDc D (hLine wp η t))
      (-(volume wp.1.1 * (wp.1.2.2.2.2 (D.yukawa η wp.1.2.2.2.1)).re)) 0 := by
    unfold LDc
    simp only [hl_e, hl_H, hl_Ψ, hl_Ψb, hl_DPsi, hl_DPsiBar]
    set c : ℂ := Complex.I / 2 * ∑ μ, (wp.1.2.2.2.2 (gammaMu D μ wp.1.1 (DPsi D wp μ)) -
      DPsiBar D wp μ (gammaMu D μ wp.1.1 wp.1.2.2.2.1))
    have hfun : (fun t : ℝ => volume wp.1.1 * (c - wp.1.2.2.2.2
        (D.yukawa (wp.1.2.2.1 + t • η) wp.1.2.2.2.1)).re) =
        fun t => volume wp.1.1 * (c - wp.1.2.2.2.2 (D.yukawa wp.1.2.2.1 wp.1.2.2.2.1)).re +
          t * -(volume wp.1.1 * (wp.1.2.2.2.2 (D.yukawa η wp.1.2.2.2.1)).re) := by
      funext t
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        Complex.sub_re, Complex.add_re, Complex.smul_re, smul_eq_mul]
      ring
    rw [hfun]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
      (-(volume wp.1.1 * (wp.1.2.2.2.2 (D.yukawa η wp.1.2.2.2.1)).re))).const_add
      (volume wp.1.1 * (c - wp.1.2.2.2.2 (D.yukawa wp.1.2.2.1 wp.1.2.2.2.1)).re)
  have hg : (fun t : ℝ => Lgc D (hLine wp η t)) = fun _ => Lgc D wp := by
    funext t; unfold Lgc; rw [hl_e, hl_p]
  have hY : (fun t : ℝ => LYMc D (hLine wp η t)) = fun _ => LYMc D wp := by
    funext t; unfold LYMc; simp only [hl_e, hl_FA]
  have hg' : HasDerivAt (fun t : ℝ => Lgc D (hLine wp η t)) 0 0 := by
    rw [hg]; exact hasDerivAt_const _ _
  have hY' : HasDerivAt (fun t : ℝ => LYMc D (hLine wp η t)) 0 0 := by
    rw [hY]; exact hasDerivAt_const _ _
  have hsum := ((hg'.add hY').add hH).add hDy
  have hfun : (fun t : ℝ => L0 D (hLine wp η t)) = fun t => Lgc D (hLine wp η t) +
      LYMc D (hLine wp η t) + LHc D (hLine wp η t) + LDc D (hLine wp η t) :=
    funext fun t => L0_eq D _
  rw [hfun]
  refine hsum.congr_deriv ?_
  ring

/-- The derivative-line derivative of `L₀` in the jet direction `∂_μ H ↦ ∂_μ H + tη`. -/
theorem hasDerivAt_L0_pLineH (wp : FJ 𝔄 𝓗 𝓢) (η : 𝓗) (μ : Fin 4) :
    HasDerivAt (fun t : ℝ => L0 D (pLineH wp η μ t))
      (-(volume wp.1.1 * ∑ α, ∑ β, ginv wp.1.1 α β *
          (D.hermH (dJH η μ α) (KH D wp β) + D.hermH (KH D wp α) (dJH η μ β)))) 0 := by
  have hfun : (fun t : ℝ => L0 D (pLineH wp η μ t)) = fun t =>
      Lgc D wp + LYMc D wp + (-(volume wp.1.1 * ∑ α, ∑ β, ginv wp.1.1 α β *
        D.hermH (KH D wp α + t • dJH η μ α) (KH D wp β + t • dJH η μ β)) -
        volume wp.1.1 * potential D wp.1.2.2.1) + LDc D wp := by
    funext t
    rw [L0_eq]
    unfold Lgc LYMc LHc LDc
    simp only [ph_w, ph_e', ph_KH, ph_DPsi, ph_DPsiBar, ph_FA]
  rw [hfun]
  have h0 : HasDerivAt (fun t : ℝ => ∑ α, ∑ β, ginv wp.1.1 α β *
      D.hermH (KH D wp α + t • dJH η μ α) (KH D wp β + t • dJH η μ β))
      (∑ α, ∑ β, ginv wp.1.1 α β *
          (D.hermH (dJH η μ α) (KH D wp β) + D.hermH (KH D wp α) (dJH η μ β))) 0 := by
    refine HasDerivAt.fun_sum fun α _ => HasDerivAt.fun_sum fun β _ => HasDerivAt.const_mul _ ?_
    have h := hasDerivAt_bilin D.hermH (hasDerivAt_affine (KH D wp α) (dJH η μ α))
      (hasDerivAt_affine (KH D wp β) (dJH η μ β))
    simpa using h
  have := ((hasDerivAt_const (0 : ℝ) (Lgc D wp + LYMc D wp)).add
    (((h0.const_mul (volume wp.1.1)).neg).sub_const (volume wp.1.1 *
      potential D wp.1.2.2.1))).add_const (LDc D wp)
  simpa using this

/-- **The jet partial of `L₀` in `∂_μ H`**: `∂L₀/∂(∂_μH)[η] = -2v g^{μβ}⟨η, K_β⟩` for a symmetric
Hermitian form. -/
theorem fderiv_L0_dH (hsymH : ∀ x y, D.hermH x y = D.hermH y x) {wp : FJ 𝔄 𝓗 𝓢}
    (h : wp.1.1.det ≠ 0) (η : 𝓗) (μ : Fin 4) :
    fderiv ℝ (L0 D) wp ((0 : Field 𝔄 𝓗 𝓢), Pi.single μ (higgsDir η : Field 𝔄 𝓗 𝓢)) =
      -(2 * volume wp.1.1 * ∑ β, ginv wp.1.1 μ β * D.hermH η (KH D wp β)) := by
  have hl : HasDerivAt (fun t : ℝ => L0 D (wp + t • ((0 : Field 𝔄 𝓗 𝓢),
      Pi.single μ (higgsDir η : Field 𝔄 𝓗 𝓢)))) _ 0 := hasDerivAt_L0_pLineH D wp η μ
  refine (fderiv_apply_of_line (differentiableAt_L0 D h) hl).trans ?_
  simp only [mul_add, Finset.sum_add_distrib]
  have e1 : ∑ α, ∑ β, ginv wp.1.1 α β * D.hermH (dJH η μ α) (KH D wp β) =
      ∑ β, ginv wp.1.1 μ β * D.hermH η (KH D wp β) := by
    rw [Finset.sum_eq_single μ (fun α _ hα => by simp [dJH, hα]) (by simp)]
    simp [dJH]
  have e2 : ∑ α, ∑ β, ginv wp.1.1 α β * D.hermH (KH D wp α) (dJH η μ β) =
      ∑ β, ginv wp.1.1 μ β * D.hermH η (KH D wp β) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single μ (fun α _ hα => by simp [dJH, hα]) (by simp)]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [dJH, if_true]
    rw [ginv_symm' wp.1.1 β μ, hsymH]
  rw [e1, e2]
  ring

/-- **The value partial of `L₀` in `H`** (symmetric Hermitian form, `ρ_H(A_μ)` skew):
`∂L₀/∂H[η] = 2v g^{μν}⟨η, ρ_H(A_μ)K_ν⟩ - v DV(H)[η] - v Re Ψ̄𝓜(η)Ψ`. -/
theorem fderiv_L0_H (hsymH : ∀ x y, D.hermH x y = D.hermH y x)
    {wp : FJ 𝔄 𝓗 𝓢}
    (hskew : ∀ μ x y, D.hermH (D.ρH (wp.1.2.1 μ) x) y = -D.hermH x (D.ρH (wp.1.2.1 μ) y))
    (h : wp.1.1.det ≠ 0) (η : 𝓗) :
    fderiv ℝ (L0 D) wp ((higgsDir η : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) =
      2 * volume wp.1.1 * ∑ μ, ∑ ν, ginv wp.1.1 μ ν * D.hermH η (D.ρH (wp.1.2.1 μ) (KH D wp ν)) -
        volume wp.1.1 * potGrad D wp.1.2.2.1 η -
        volume wp.1.1 * (wp.1.2.2.2.2 (D.yukawa η wp.1.2.2.2.1)).re := by
  have hl : HasDerivAt (fun t : ℝ => L0 D (wp + t • ((higgsDir η : Field 𝔄 𝓗 𝓢),
      (0 : Fin 4 → Field 𝔄 𝓗 𝓢)))) _ 0 := hasDerivAt_L0_hLine D wp η
  refine (fderiv_apply_of_line (differentiableAt_L0 D h) hl).trans ?_
  have e : ∑ μ, ∑ ν, ginv wp.1.1 μ ν * (D.hermH (D.ρH (wp.1.2.1 μ) η) (KH D wp ν) +
      D.hermH (KH D wp μ) (D.ρH (wp.1.2.1 ν) η)) =
      -(2 * ∑ μ, ∑ ν, ginv wp.1.1 μ ν * D.hermH η (D.ρH (wp.1.2.1 μ) (KH D wp ν))) := by
    simp only [mul_add, Finset.sum_add_distrib]
    have e2 : ∑ μ, ∑ ν, ginv wp.1.1 μ ν * D.hermH (KH D wp μ) (D.ρH (wp.1.2.1 ν) η) =
        ∑ μ, ∑ ν, ginv wp.1.1 μ ν * D.hermH (D.ρH (wp.1.2.1 μ) η) (KH D wp ν) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [ginv_symm' wp.1.1 b a, hsymH]
    rw [e2]
    simp only [hskew, mul_neg, Finset.sum_neg_distrib]
    ring
  rw [e]
  ring

/-- The covariant Higgs derivative field `K_μ(y) = ∂_μH + ρ_H(A_μ)H` of a native field. -/
def Kf (Y : R4 → Field 𝔄 𝓗 𝓢) (y : R4) (μ : Fin 4) : 𝓗 := KH D (jet1 Y y) μ

/-- **The covariant wave operator of a native field in Christoffel form**
`□_A H = g^{μρ}(∂_ρK_μ - Γ^l_{ρμ}K_l + ρ_H(A_ρ)K_μ)` (the formula of `ActualJetGauge.waveH` with
the gauge action `ρ_H`). -/
def waveN (Y : R4 → Field 𝔄 𝓗 𝓢) (z : R4) : 𝓗 :=
  ∑ μ, ∑ ρ, ginvOf (gF (eF Y) z) μ ρ • (pd (fun y => Kf D Y y μ) ρ z -
    ∑ l, chr (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z) l ρ μ • Kf D Y z l +
    D.ρH ((Y z).2.1 ρ) (Kf D Y z μ))

theorem contDiff_KH (μ : Fin 4) : ContDiff ℝ ∞ (fun wp : FJ 𝔄 𝓗 𝓢 => KH D wp μ) := by
  have : (fun wp : FJ 𝔄 𝓗 𝓢 => KH D wp μ) =
      fun wp => D.ρHL (wp.1.2.1 μ) wp.1.2.2.1 + (wp.2 μ).2.2.1 := funext fun wp => rfl
  rw [this]
  fun_prop

theorem contDiff_Kf {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y) (μ : Fin 4) :
    ContDiff ℝ ∞ (fun y => Kf D Y y μ) :=
  (contDiff_KH D μ).comp (ContEulerBounds.contDiff_jet1_infty hY)

theorem KH_jet1 (Y : R4 → Field 𝔄 𝓗 𝓢) (z : R4) (μ : Fin 4) : KH D (jet1 Y z) μ = Kf D Y z μ :=
  rfl

theorem pd_neg_two_mul {φ : R4 → ℝ} {z : R4} (hφ : DifferentiableAt ℝ φ z) (μ : Fin 4) :
    pd (fun y => -(2 * φ y)) μ z = -(2 * pd φ μ z) := by
  refine pd_eq_of_line' ((hφ.const_mul 2).neg) ?_
  exact ((hasDerivAt_line' μ hφ).const_mul 2).neg

/-- **The Higgs Euler row of the native continuum Lagrangian** (bridge step P3, Higgs sector):
for a smooth native field with `det e > 0` whose gauge potential takes values in a set `𝔤` on
which `ρ_H` is skew for the symmetric Hermitian form (the gauge Lie algebra inside `𝔄`), and every
Higgs direction `η`,
`𝓔₀(Y)(z)[(0, 0, η, 0, 0)] = 2v(e)⟨η, □_A H⟩ - v(e)DV(H)[η] - v(e) Re Ψ̄𝓜_𝐘(η)Ψ`,
with the covariant wave operator in Christoffel form (`waveN`). -/
theorem higgs_euler_row (hsymH : ∀ x y, D.hermH x y = D.hermH y x)
    (𝔤 : Set 𝔄) (hskew : ∀ a ∈ 𝔤, ∀ x y, D.hermH (D.ρH a x) y = -D.hermH x (D.ρH a y))
    {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y) (hA𝔤 : ∀ z μ, (Y z).2.1 μ ∈ 𝔤)
    (hdet : ∀ z, 0 < ((Y z).1).det) (z : R4) (η : 𝓗) :
    contEuler (L0 D) Y z (higgsDir η) =
      2 * volume (Y z).1 * D.hermH η (waveN D Y z) - volume (Y z).1 * potGrad D (Y z).2.2.1 η -
        volume (Y z).1 * ((Y z).2.2.2.2 (D.yukawa η (Y z).2.2.2.1)).re := by
  have he : ContDiff ℝ ∞ (eF Y) := contDiff_fst.comp hY
  have hdet' : ∀ z, 0 < (eF Y z).det := hdet
  have hJU : ∀ y, jet1 Y y ∈ (chartF : Set (FJ 𝔄 𝓗 𝓢)) := fun y => (hdet y).ne'
  have hE := contEuler_apply (L := L0 D) isOpen_chartF (contDiffOn_L0 D) hY hJU z
    (higgsDir η : Field 𝔄 𝓗 𝓢)
  refine hE.trans ?_
  have hH := fderiv_L0_H D hsymH (wp := jet1 Y z) (fun μ => hskew _ (hA𝔤 z μ)) (hdet z).ne' η
  simp only [jet1_fst, ginv_eF, KH_jet1, volume_eF] at hH
  have hpt : ∀ μ, (fun z' => fderiv ℝ (L0 D) (jet1 Y z') ((0 : Field 𝔄 𝓗 𝓢),
      Pi.single μ (higgsDir η : Field 𝔄 𝓗 𝓢))) = fun z' => -(2 * (volume (eF Y z') *
        ∑ β, ginvOf (gF (eF Y) z') μ β * D.hermH η (Kf D Y z' β))) := by
    intro μ
    funext z'
    rw [fderiv_L0_dH D hsymH (wp := jet1 Y z') (hdet z').ne' η μ]
    simp only [jet1_fst, ginv_eF, KH_jet1, volume_eF]
    ring
  have hW : ∀ ρ, ContDiff ℝ ∞ (fun y => D.hermH η (Kf D Y y ρ)) := fun ρ =>
    (D.hermH η).contDiff.comp (contDiff_Kf D hY ρ)
  have hφ : ∀ μ, ContDiff ℝ ∞ (fun z' => volume (eF Y z') *
      ∑ β, ginvOf (gF (eF Y) z') μ β * D.hermH η (Kf D Y z' β)) := fun μ =>
    (contDiff_volume_comp he hdet').mul (ContDiff.sum fun β _ =>
      (contDiff_ginv he hdet' μ β).mul (hW β))
  have hdiv : ∑ μ, pd (fun z' => fderiv ℝ (L0 D) (jet1 Y z') ((0 : Field 𝔄 𝓗 𝓢),
      Pi.single μ (higgsDir η : Field 𝔄 𝓗 𝓢))) μ z =
      -(2 * (volume (eF Y z) * ∑ μ, ∑ ρ, ginvOf (gF (eF Y) z) μ ρ *
        (D.hermH η (pd (fun y => Kf D Y y μ) ρ z) -
          ∑ l, chr (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z) l ρ μ * D.hermH η (Kf D Y z l)))) := by
    simp only [hpt]
    rw [Finset.sum_congr rfl fun μ _ => pd_neg_two_mul (((hφ μ).differentiable (by simp)) z) μ]
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
    congr 2
    refine (sum_pd_vec_density he hdet' hW z).trans ?_
    refine congrArg _ (Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ρ _ => ?_)
    rw [pd_clm (D.hermH η) ((contDiff_Kf D hY μ).differentiable (by simp) z)]
  refine (congrArg₂ (· - ·) hH hdiv).trans ?_
  have hR : D.hermH η (waveN D Y z) = ∑ μ, ∑ ρ, ginvOf (gF (eF Y) z) μ ρ *
        (D.hermH η (pd (fun y => Kf D Y y μ) ρ z) -
          ∑ l, chr (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z) l ρ μ * D.hermH η (Kf D Y z l)) +
      ∑ μ, ∑ ν, ginvOf (gF (eF Y) z) μ ν * D.hermH η (D.ρH ((Y z).2.1 μ) (Kf D Y z ν)) := by
    have e3 : ∑ μ, ∑ ν, ginvOf (gF (eF Y) z) μ ν * D.hermH η (D.ρH ((Y z).2.1 μ) (Kf D Y z ν)) =
        ∑ μ, ∑ ρ, ginvOf (gF (eF Y) z) μ ρ * D.hermH η (D.ρH ((Y z).2.1 ρ) (Kf D Y z μ)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [ginv_symm z b a]
    rw [e3, ← Finset.sum_add_distrib]
    unfold waveN
    simp only [map_sum, map_smul, map_add, map_sub, smul_eq_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    ring
  rw [hR, volume_eF]
  ring

end

end NativeBosonicEuler

end RenewalGeometry
