/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeLocalCalibrationClosed
import RenewalGeometry.Continuum.NativeModelMap
import RenewalGeometry.Gravity.HomogeneousEinsteinHiggsExact

/-!
# `cor:local-calibration-nonempty`, last sentence: the obstruction of the uncorrected encoding

Einstein–Standard-Model action-closure manuscript, `cor:local-calibration-nonempty`, last
sentence: "A backreacting Einstein–Higgs example is supplied by `prop:homogeneous`, after a regular
gauge change on a smaller slab."

**Status after the encoding correction (g11).**  This file records why the *uncorrected* encoding
(g8–g10) could not realise the sentence: there the hypothesis of
`LocalCalibrationClosed.local_calibration_nonempty` was the **complete** native Euler equations
`𝓔₀(Y) = contEuler (limDensity (firstJetDensity M.toData)) Y = 0`, i.e. the vanishing of the whole
covector on `Field = Mat × (Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢`, in particular in every gauge
direction `X : Fin 4 → 𝔄` of the **associative** algebra `𝔄`.  Since g11 the hypothesis is the
**physical** one, `𝓔₀(Y) ∘ physF πg = 0` (gauge rows only in the gauge Lie algebra `𝔤 = gSub`,
`RecordTuple.comp_physF_eq_zero_iff`), and the budgets and the slab current read only physical
rows; the unit direction below is not a physical direction (`one_not_mem_gLie`), so the
obstruction no longer applies.  The theorems below remain true statements about the complete
(unphysical) system.  Since `ρ_H : 𝔄 →ₐ ℝ (𝓗 →L 𝓗)` is an algebra homomorphism, the unit `1 ∈ 𝔄` acts
on Higgs fields as the identity, and the Euler row in the direction `X = e_σ ⊗ 1` is a
"dilation current" of the Higgs field:

* **`unit_gauge_row`** — for a smooth native field with `det e > 0`, `A ≡ 0` and `Ψ̄ ≡ 0`,
  `𝓔₀(Y)(z)[(0, e_σ ⊗ 1, 0, 0, 0)] = -2 v(e) g^{σν} ⟨H, ∂_νH⟩` (the Yang–Mills divergence vanishes
  with `A`, the Dirac current with `Ψ̄`);
* **`native_euler_higgs_norm`** — hence the native Euler equations at `z` force
  `⟨H, ∂_νH⟩(z) = 0` for every `ν`: the Higgs norm `⟨H, H⟩` is stationary;
* **`native_euler_homogeneous`**, **`native_euler_frozen_higgs`** — for a Higgs field along a fixed
  non-null direction, `H(z) = f(z⁰) h₀`, the native Euler equations on the buffered slab force
  `f ≡ const` on the open buffered time interval (no Higgs motion);
* **`no_backreacting_homogeneous`** — **the backreacting example of `prop:homogeneous` cannot be
  transported into the hypotheses of `local_calibration_nonempty`**: for every solution
  `(a, φ, π, ℋ)` of `eq:homogeneous-ODE` with `π(0) ≠ 0` (the backreacting case,
  `ℋ'(0) = -(κ/2)π(0)² < 0`, `HomogeneousEinsteinHiggs.backreaction_of_pi_ne_zero`), every regular
  time change `T` (`T(s₀) = 0`, `T'(s₀) ≠ 0`, `s₀` in the open buffered slab), every coframe `e`
  (any frame or coordinate gauge, any cut-off and periodic extension), every spinor `Ψ`, `A ≡ 0`,
  `Ψ̄ ≡ 0` and every non-null `h₀`, the field with Higgs component `φ(T(t)) h₀` near `s₀` does
  **not** satisfy the native Euler equations on the buffered slab.
* `one_not_mem_gLie` — the obstructing direction is unphysical: `1 ∉ gLie` (a skew-adjoint unit
  would force `⟨·,·⟩_H = 0`).

So the corollary's last sentence was **not realisable in the uncorrected encoding**: the complete
system imposes the Euler equations also in the non-gauge directions of `𝔄 ≅ gl(m)` (the trace
direction acts on `H` by dilations), which excludes every moving homogeneous Higgs field.  With the
Euler equations restricted to the physical directions (gauge directions in `gLie`, where the
current of a real Higgs field along a fixed vector vanishes by skew-adjointness,
`HomogeneousEinsteinHiggs.gauge_current_re_vanishes`) the obstruction disappears; the slab theory
data `SlabData.toSMData` now carries the `𝔤`-component of the current (`SlabData.Jcur`).
-/

open Filter Topology Set Finset
open scoped ContDiff Real

noncomputable section

namespace RenewalGeometry.CalibrationBackreacting

open SobolevOpen (pd)
open NativeDensity NativeBosonicEuler NativeModel PalatiniEuler ActualJetSystem
open DiscreteEulerConsistency (R4 evec jet1 contEuler limDensity)
open NativeScaling (Mat eta metric)

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (M : Model 𝔄 𝓗 𝓢)

/-- The Higgs component of a native field. -/
def Hc (Y : R4 → Field 𝔄 𝓗 𝓢) (y : R4) : 𝓗 := (Y y).2.2.1

/-- The projection of the native field space onto the Higgs component. -/
def projHc : Field 𝔄 𝓗 𝓢 →L[ℝ] 𝓗 :=
  (ContinuousLinearMap.fst ℝ 𝓗 _).comp ((ContinuousLinearMap.snd ℝ (Fin 4 → 𝔄) _).comp
    (ContinuousLinearMap.snd ℝ Mat _))

theorem jet1_Hc {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : Differentiable ℝ Y) (z : R4) (ν : Fin 4) :
    ((jet1 Y z).2 ν).2.2.1 = pd (Hc Y) ν z :=
  (pd_clm (projHc (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)) (hY z) ν).symm

/-- With `A ≡ 0` the field strength vanishes identically. -/
theorem Ff_zero {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : Differentiable ℝ Y) (hA : ∀ y, (Y y).2.1 = 0)
    (y : R4) (μ ν : Fin 4) : Ff Y y μ ν = 0 := by
  have hAf : ∀ y, Af Y y = fun _ => 0 := fun y => funext fun μ => by simp [Af, hA]
  have hdA : ∀ γ μ, dAf Y y γ μ = 0 := by
    intro γ μ
    unfold dAf
    simp only [hAf]
    simp [SobolevOpen.pd]
  unfold Ff FA
  rw [jet1_A hY, jet1_A hY, hdA, hdA]
  simp [jet1, hA]

variable {M}

/-- `ρ_H` of a unit gauge direction. -/
theorem rhoH_single (σ μ : Fin 4) (H : 𝓗) :
    M.ρH ((Pi.single σ (1 : 𝔄) : Fin 4 → 𝔄) μ) H = if μ = σ then H else 0 := by
  by_cases h : μ = σ
  · subst h; simp
  · simp [h]

/-- **The Euler row in a unit gauge direction** `X = e_σ ⊗ 1` of a native field with `A ≡ 0` and
`Ψ̄ ≡ 0`: `𝓔₀(Y)(z)[(0, e_σ ⊗ 1, 0, 0, 0)] = -2v(e) g^{σν}⟨H, ∂_νH⟩`. -/
theorem unit_gauge_row {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y)
    (hdet : ∀ z, 0 < ((Y z).1).det) (hA : ∀ y, (Y y).2.1 = 0) (hΨb : ∀ y, (Y y).2.2.2.2 = 0)
    (z : R4) (σ : Fin 4) :
    contEuler (L0 M.toData) Y z (gaugeDir (Pi.single σ (1 : 𝔄))) =
      -(2 * volume (Y z).1 * ∑ ν, ginv (Y z).1 σ ν * M.hermH (Hc Y z) (pd (Hc Y) ν z)) := by
  have hYd : Differentiable ℝ Y := hY.differentiable (by simp)
  rw [ym_euler_row M.toData M.ipA_symm M.ipA_inv hY hdet z]
  have hdiv : ∀ σ', ymDivN Y z σ' = 0 := by
    intro σ'
    unfold ymDivN
    have hF : ∀ y μ ν, Ff Y y μ ν = 0 := Ff_zero hYd hA
    simp only [hF, hA]
    simp [SobolevOpen.pd]
  simp only [hdiv, map_zero, mul_zero, Finset.sum_const_zero, zero_add]
  have hK : ∀ ν, KH M.toData (jet1 Y z) ν = pd (Hc Y) ν z := by
    intro ν
    unfold KH
    rw [jet1_Hc hYd]
    simp [jet1, hA]
  unfold gaugeCur
  simp only [hK]
  have hw : (jet1 Y z).1 = Y z := rfl
  simp only [hw, hΨb, ContinuousLinearMap.zero_apply, sub_self, Finset.sum_const_zero, mul_zero,
    Complex.zero_re, add_zero]
  simp only [rhoH_single]
  have hs : ∀ μ ν, ginv (Y z).1 μ ν *
      (M.hermH (if μ = σ then Hc Y z else 0) (pd (Hc Y) ν z) +
        M.hermH (pd (Hc Y) μ z) (if ν = σ then Hc Y z else 0)) =
      (if μ = σ then ginv (Y z).1 σ ν * M.hermH (Hc Y z) (pd (Hc Y) ν z) else 0) +
        (if ν = σ then ginv (Y z).1 σ μ * M.hermH (Hc Y z) (pd (Hc Y) μ z) else 0) := by
    intro μ ν
    rw [mul_add]
    congr 1
    · split_ifs with h
      · subst h; rfl
      · simp
    · split_ifs with h
      · subst h; rw [ginv_symm' _ μ ν, M.hermH_symm]
      · simp
  simp only [Hc] at hs ⊢
  simp only [hs, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, ContinuousLinearMap.zero_comp, ContinuousLinearMap.zero_apply, sub_zero, mul_zero,
    Complex.zero_re, add_zero]
  ring

/-- **The native Euler equations force a stationary Higgs norm** (`A ≡ 0`, `Ψ̄ ≡ 0`):
`𝓔₀(Y)(z) = 0 ⟹ ⟨H, ∂_νH⟩(z) = 0` for every `ν`. -/
theorem native_euler_higgs_norm {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y)
    (hdet : ∀ z, 0 < ((Y z).1).det) (hA : ∀ y, (Y y).2.1 = 0) (hΨb : ∀ y, (Y y).2.2.2.2 = 0)
    {z : R4} (hz : contEuler (limDensity (ι := Shift) (firstJetDensity M.toData)) Y z = 0)
    (ν : Fin 4) : M.hermH (Hc Y z) (pd (Hc Y) ν z) = 0 := by
  set w : Fin 4 → ℝ := fun ν => M.hermH (Hc Y z) (pd (Hc Y) ν z) with hw
  have hv : volume (Y z).1 ≠ 0 := volume_ne_zero_of_pos (hdet z)
  have hrow : ∀ σ, ∑ ν, ginv (Y z).1 σ ν * w ν = 0 := by
    intro σ
    have h := unit_gauge_row (M := M) hY hdet hA hΨb z σ
    have h0 : contEuler (L0 M.toData) Y z (gaugeDir (Pi.single σ (1 : 𝔄))) = 0 := by
      show contEuler (limDensity (ι := Shift) (firstJetDensity M.toData)) Y z _ = 0
      rw [hz]; rfl
    rw [h0] at h
    have h2 : 2 * volume (Y z).1 ≠ 0 := mul_ne_zero two_ne_zero hv
    have := h.symm
    rw [neg_eq_zero, mul_eq_zero] at this
    exact this.resolve_left h2
  -- invert the metric
  set G : Mat := metric (Y z).1 with hG
  have hGdet : G.det ≠ 0 := det_metric_ne_zero (hdet z).ne'
  have hmv : G⁻¹.mulVec w = 0 := by
    funext σ
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    exact hrow σ
  have hw0 : w = 0 := by
    have : G.mulVec (G⁻¹.mulVec w) = w := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.2 hGdet),
        Matrix.one_mulVec]
    rw [← this, hmv, Matrix.mulVec_zero]
  exact congrFun hw0 ν

/-- **Homogeneous Higgs fields**: if `H(y) = f(y) h₀`, the native Euler equations force
`f ∂_νf ⟨h₀, h₀⟩ = 0`. -/
theorem native_euler_homogeneous {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y)
    (hdet : ∀ z, 0 < ((Y z).1).det) (hA : ∀ y, (Y y).2.1 = 0) (hΨb : ∀ y, (Y y).2.2.2.2 = 0)
    {h₀ : 𝓗} {f : R4 → ℝ} (hHf : ∀ y, (Y y).2.2.1 = f y • h₀) {z : R4}
    (hfz : DifferentiableAt ℝ f z)
    (hz : contEuler (limDensity (ι := Shift) (firstJetDensity M.toData)) Y z = 0) (ν : Fin 4) :
    f z * pd f ν z * M.hermH h₀ h₀ = 0 := by
  have h := native_euler_higgs_norm (M := M) hY hdet hA hΨb hz ν
  have hH : Hc Y = fun y => (ContinuousLinearMap.toSpanSingleton ℝ h₀) (f y) := by
    funext y; simp [Hc, hHf]
  have hpd : pd (Hc Y) ν z = pd f ν z • h₀ := by
    rw [hH, pd_clm _ hfz]
    simp
  rw [hpd] at h
  have hz' : Hc Y z = f z • h₀ := hHf z
  rw [hz'] at h
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul] at h
  linear_combination h

/-- The time-only profile `y ↦ φ(y⁰)` has `∂₀ = φ'`. -/
theorem pd_time (φ : ℝ → ℝ) {z : R4} (hφ : DifferentiableAt ℝ φ (z 0)) :
    pd (fun y : R4 => φ (y 0)) 0 z = deriv φ (z 0) := by
  have h1 : HasFDerivAt (fun y : R4 => y 0) (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 4 => ℝ) 0) z := hasFDerivAt_apply 0 z
  have h2 := hφ.hasDerivAt.comp_hasFDerivAt z h1
  unfold SobolevOpen.pd
  rw [show (fun y : R4 => φ (y 0)) = φ ∘ fun y => y 0 from rfl, h2.fderiv]
  simp

/-- A point of the buffered slab at time `s`. -/
def slabPt (s : ℝ) : R4 := Pi.single 0 s

theorem slabPt_mem {a b s : ℝ} (hs : s ∈ Ico a b) :
    slabPt s ∈ NativeZeroSource.bufSlab a b := by
  refine ⟨by simpa [slabPt] using hs, fun i => ?_⟩
  simp [slabPt, Fin.succ_ne_zero, Real.pi_pos.le]
  positivity

/-- **The Higgs profile is frozen**: for a Higgs field `H(y) = φ(y⁰) h₀` along a non-null
direction, the native Euler equations on the buffered slab `[a, b) × [0, 2π)³` (`A ≡ 0`,
`Ψ̄ ≡ 0`) force `φ' = 0` on `(a, b)`. -/
theorem native_euler_frozen_higgs {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y)
    (hdet : ∀ z, 0 < ((Y z).1).det) (hA : ∀ y, (Y y).2.1 = 0) (hΨb : ∀ y, (Y y).2.2.2.2 = 0)
    {h₀ : 𝓗} (hh₀ : M.hermH h₀ h₀ ≠ 0) {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ)
    (hHf : ∀ y, (Y y).2.2.1 = φ (y 0) • h₀) {a b : ℝ}
    (hsol : ∀ z ∈ NativeZeroSource.bufSlab a b,
      contEuler (limDensity (ι := Shift) (firstJetDensity M.toData)) Y z = 0) :
    ∀ s ∈ Ioo a b, deriv φ s = 0 := by
  -- `φ φ' = 0` on the slab
  have hprod : ∀ s ∈ Ioo a b, φ s * deriv φ s = 0 := by
    intro s hs
    have hz := hsol (slabPt s) (slabPt_mem (Ioo_subset_Ico_self hs))
    have hfz : DifferentiableAt ℝ (fun y : R4 => φ (y 0)) (slabPt s) :=
      (hφ _).comp _ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).differentiableAt
    have h := native_euler_homogeneous (M := M) hY hdet hA hΨb (f := fun y => φ (y 0)) hHf hfz hz 0
    have h0 : (slabPt s) 0 = s := by simp [slabPt]
    rw [pd_time φ (hφ _), h0] at h
    have := mul_eq_zero.1 h
    exact this.resolve_right hh₀
  -- hence `φ²` is constant on `(a, b)`
  have hsq : ∀ s ∈ Ioo a b, deriv (fun t => φ t ^ 2) s = 0 := by
    intro s hs
    have : HasDerivAt (fun t => φ t ^ 2) (2 * φ s * deriv φ s) s := by
      simpa using (hφ s).hasDerivAt.fun_pow 2
    rw [this.deriv]
    linear_combination 2 * hprod s hs
  intro s hs
  by_cases hφs : φ s = 0
  · -- `φ² ≡ φ(s)² = 0` near `s`, so `φ ≡ 0` near `s`
    have hc : ∀ t ∈ Ioo a b, φ t ^ 2 = φ s ^ 2 := fun t ht =>
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        ((hφ.pow 2).differentiableOn) (fun x hx => hsq x hx) ht hs
    have hev : φ =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
      have := hc t ht
      rw [hφs] at this
      simpa using this
    rw [hev.deriv_eq]
    simp
  · exact (mul_eq_zero.1 (hprod s hs)).resolve_left hφs

/-- **The backreacting example of `prop:homogeneous` cannot satisfy the native Euler equations of
`local_calibration_nonempty`**: whatever the regular time change `T` (`T(s₀) = 0`, `T'(s₀) ≠ 0`
with `s₀` in the open buffered slab), coframe, spinor and non-null Higgs direction `h₀`, a smooth
native field with `A ≡ 0`, `Ψ̄ ≡ 0`, Higgs component `f(t) h₀` and `f = φ ∘ T` near `s₀`, where
`(a, φ, π, ℋ)` solves `eq:homogeneous-ODE` with `π(0) ≠ 0`, violates the native Euler equations
somewhere on the buffered slab. -/
theorem no_backreacting_homogeneous {κ lamH vH ε : ℝ} {a φ πh ℋ : ℝ → ℝ}
    (sol : HomogeneousEinsteinHiggs.IsSolution κ lamH vH a φ πh ℋ (Ioo (-ε) ε)) (hε : 0 < ε)
    (hπ : πh 0 ≠ 0) {T : ℝ → ℝ} {s₀ c : ℝ} (hT0 : T s₀ = 0) (hT : HasDerivAt T c s₀)
    (hc : c ≠ 0) {t₀ t₁ b : ℝ} (hs₀ : s₀ ∈ Ioo (t₀ - b) (t₁ + b))
    {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y) (hdet : ∀ z, 0 < ((Y z).1).det)
    (hA : ∀ y, (Y y).2.1 = 0) (hΨb : ∀ y, (Y y).2.2.2.2 = 0) {h₀ : 𝓗} (hh₀ : M.hermH h₀ h₀ ≠ 0)
    {f : ℝ → ℝ} (hHf : ∀ y, (Y y).2.2.1 = f (y 0) • h₀) (hfT : f =ᶠ[𝓝 s₀] φ ∘ T) :
    ¬ ∀ z ∈ NativeZeroSource.bufSlab (t₀ - b) (t₁ + b),
        contEuler (limDensity (ι := Shift) (firstJetDensity M.toData)) Y z = 0 := by
  intro hsol
  -- `f` is smooth: it is read off from the Higgs component along `h₀`
  have hf_eq : f = fun s => (M.hermH h₀ h₀)⁻¹ * M.hermH ((Y (slabPt s)).2.2.1) h₀ := by
    funext s
    rw [hHf]
    have h0 : (slabPt s) 0 = s := by simp [slabPt]
    rw [h0, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    field_simp
  have hf : Differentiable ℝ f := by
    rw [hf_eq]
    have hpt : Differentiable ℝ slabPt := by
      unfold slabPt
      exact (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => ℝ) 0).differentiable
    have hH : Differentiable ℝ fun s => (Y (slabPt s)).2.2.1 :=
      (projHc (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)).differentiable.comp
        ((hY.differentiable (by simp)).comp hpt)
    exact (differentiable_const _).mul ((M.hermH.differentiable.comp hH).clm_apply
      (differentiable_const _))
  have hfrozen := native_euler_frozen_higgs (M := M) hY hdet hA hΨb hh₀ hf hHf hsol s₀ hs₀
  -- but the Higgs velocity of the backreacting solution is `π(0) c ≠ 0`
  have hφ0 : HasDerivAt φ (πh (T s₀)) (T s₀) := by
    rw [hT0]
    exact sol.φ_deriv 0 ⟨by linarith, hε⟩
  have hcomp : HasDerivAt (φ ∘ T) (πh (T s₀) * c) s₀ := hφ0.comp s₀ hT
  have hfd : HasDerivAt f (πh (T s₀) * c) s₀ := hcomp.congr_of_eventuallyEq hfT
  rw [hfd.deriv, hT0] at hfrozen
  exact mul_ne_zero hπ hc hfrozen

/-- The obstructing direction is not a gauge direction: `1 ∉ gLie` (a skew-adjoint unit would
force the Higgs form to vanish). -/
theorem one_not_mem_gLie : (1 : 𝔄) ∉ M.gLie := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : 𝓗)
  apply hx
  refine M.hermH_nondeg x fun y => ?_
  have := M.rhoH_skew 1 h y x
  simp only [map_one, ContinuousLinearMap.one_apply] at this
  linarith

/-- **The complete (all-`𝔄`) native Euler equations fail for every transport of the backreacting
`prop:homogeneous` example into a slab model** (the statement of `no_backreacting_homogeneous` for
the native data `M.toData` of a slab model).  This was the hypothesis `hsol` of the uncorrected
`local_calibration_nonempty`; the corrected hypothesis tests only the physical directions. -/
theorem slab_hsol_fails_backreacting {m : ℕ} (M : SlabData.SlabModel 𝔄 𝓗 𝓢 m)
    {κ lamH vH ε : ℝ} {a φ πh ℋ : ℝ → ℝ}
    (sol : HomogeneousEinsteinHiggs.IsSolution κ lamH vH a φ πh ℋ (Ioo (-ε) ε)) (hε : 0 < ε)
    (hπ : πh 0 ≠ 0) {T : ℝ → ℝ} {s₀ c : ℝ} (hT0 : T s₀ = 0) (hT : HasDerivAt T c s₀)
    (hc : c ≠ 0) {t₀ t₁ b : ℝ} (hs₀ : s₀ ∈ Ioo (t₀ - b) (t₁ + b))
    {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ ∞ Y) (hdet : ∀ z, 0 < ((Y z).1).det)
    (hA : ∀ y, (Y y).2.1 = 0) (hΨb : ∀ y, (Y y).2.2.2.2 = 0) {h₀ : 𝓗} (hh₀ : M.hermH h₀ h₀ ≠ 0)
    {f : ℝ → ℝ} (hHf : ∀ y, (Y y).2.2.1 = f (y 0) • h₀) (hfT : f =ᶠ[𝓝 s₀] φ ∘ T) :
    ¬ ∀ z ∈ NativeZeroSource.bufSlab (t₀ - b) (t₁ + b),
        contEuler (limDensity (ι := Shift) (firstJetDensity M.toData)) Y z = 0 :=
  no_backreacting_homogeneous (M := M.toModel) sol hε hπ hT0 hT hc hs₀ hY hdet hA hΨb hh₀ hHf hfT

end RenewalGeometry.CalibrationBackreacting

end
