/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeStressCalculus
import RenewalGeometry.Continuum.ContEulerAlgebra

/-!
# The Dirac stress: the coframe variation of the native Dirac density

Bridge step P3-stress of `thm:native-closure` (Einstein–Standard-Model action-closure
manuscript), Dirac sector.  The native Dirac density
`L_D = v Re{(i/2)[Ψ̄γ^μ(e)∇_μΨ - (∇_μΨ̄)γ^μ(e)Ψ] - Ψ̄𝓜(H)Ψ}` depends on the coframe through
`v(e)`, `γ^μ(e) = e_a^μγ^a` and the spin connection `σ(Ω(e, ∂e))`.

* `coframeDir`, `frozenDir` — the coframe direction `(δ, 0, 0, 0, 0)` and the *frozen metric
  direction* `((Se, 0, …), μ ↦ (S∂_μe, 0, …))` of a first jet: the first-order part of the
  variation `e ↦ (1 + tS)e` with `S` frozen at the point;
* `hasDerivAt_inv_affine` — `d/dt (E + tδ)⁻¹ = -E⁻¹δE⁻¹`;
* `omegaDot_antisym`, `omegaDot_torsion` — the derivative `Ω̇` of the reader connection along
  `(e, q) ↦ ((1+tS)e, (1+tS)q)` is `η`-antisymmetric and has the torsion of `[S, Ω]`, which is
  `η`-symmetric when `ηS` is symmetric (`commutator_symm`);
* **`spin_anticomm_frozen`** — hence (`NativeStressEuler.anticomm_sum_zero`)
  `Σ_μ {γ^μ(e), σ(Ω̇_μ)} = 0`: a metric variation does not move the spin-connection term;
* **`hasDerivAt_LDc_frozen`** — `d/dt L_D = (v/2) T_D^{ab} δg_{ab}` along the frozen metric
  direction, with the Dirac stress `T_D^{ab} = g^{ab} ℓ_D - g^{aμ} Θ_μ{}^b`,
  `ℓ_D = Re{(i/2)[Ψ̄γ^μ∇_μΨ - (∇_μΨ̄)γ^μΨ] - Ψ̄𝓜Ψ}`,
  `Θ_μ{}^b = Re{(i/2)[Ψ̄γ^b∇_μΨ - (∇_μΨ̄)γ^bΨ]}`, `δg = 2eᵀ(ηS)e`;
* **`hasDerivAt_LDc_jetSym`** — a jet direction `∂_μe ↦ ∂_μe + tTe` with `ηT` symmetric does not
  move `L_D` (the same anticommutator identity, now for the jet linearity of `Ω`).

Hypotheses: the Clifford relations `γ^aγ^b + γ^bγ^a = 2η^{ab}` and `σ(ω) = ¼ω_{ab}γ^aγ^b`
(the `NativeModel.Model` fields `cliff`, `sigma_eq`).
-/

namespace RenewalGeometry

namespace NativeStressEuler

open Finset HarmonicDefect PalatiniEuler NativeDiracEuler NativeBosonicEuler EHFieldVariation
open NativeScaling (Mat eta metric readerOmega readerG readerGamma)
open NativeDensity
open Filter Topology
open scoped Matrix

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### The inverse along an affine line -/

theorem eventually_det_ne {E δ : Mat} (hE : E.det ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝 0, (E + t • δ).det ≠ 0 := by
  have hc : Continuous fun t : ℝ => (E + t • δ).det :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have : (fun t : ℝ => (E + t • δ).det) 0 ≠ 0 := by simpa using hE
  exact hc.continuousAt.eventually_ne this

/-- `d/dt (E + tδ)⁻¹ = -E⁻¹δE⁻¹`. -/
theorem hasDerivAt_inv_affine {E : Mat} (hE : E.det ≠ 0) (δ : Mat) :
    HasDerivAt (fun t : ℝ => (E + t • δ)⁻¹) (-(E⁻¹ * δ * E⁻¹)) 0 := by
  have hdiff : ∀ i j, DifferentiableAt ℝ (fun t : ℝ => (E + t • δ)⁻¹ i j) 0 := by
    intro i j
    have h1 : DifferentiableAt ℝ (invEntry i j) ((fun t : ℝ => E + t • δ) 0) :=
      (contDiffAt_invEntry (k := 1) i j (by simpa using hE)).differentiableAt (by norm_num)
    have h2 : DifferentiableAt ℝ (fun t : ℝ => E + t • δ) 0 :=
      (differentiableAt_const _).add (differentiableAt_id.smul_const δ)
    exact h1.comp (0 : ℝ) h2
  set Dm : Mat := fun i j => deriv (fun t : ℝ => (E + t • δ)⁻¹ i j) 0
  have hDi : HasDerivAt (fun t : ℝ => (E + t • δ)⁻¹) Dm 0 :=
    hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => (hdiff i j).hasDerivAt
  have hL : HasDerivAt (fun t : ℝ => E + t • δ) δ 0 := hasDerivAt_affine E δ
  have hprod : ∀ a b, HasDerivAt (fun t : ℝ => ∑ k, (E + t • δ)⁻¹ a k * (E + t • δ) k b)
      (∑ k, (Dm a k * E k b + E⁻¹ a k * δ k b)) 0 := by
    intro a b
    refine HasDerivAt.fun_sum fun k _ => ?_
    have h1 := hasDerivAt_pi.1 (hasDerivAt_pi.1 hDi a) k
    have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 hL k) b
    refine (h1.fun_mul h2).congr_deriv ?_
    simp
  have hzero : Dm * E + E⁻¹ * δ = 0 := by
    ext a b
    have h := hprod a b
    have hev : (fun t : ℝ => ∑ k, (E + t • δ)⁻¹ a k * (E + t • δ) k b) =ᶠ[𝓝 0]
        fun _ => (1 : Mat) a b := by
      filter_upwards [eventually_det_ne (δ := δ) hE] with t ht
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ ht.isUnit]
    have h0 := h.unique ((hasDerivAt_const (0 : ℝ) ((1 : Mat) a b)).congr_of_eventuallyEq hev)
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    simpa using h0
  have hD : Dm = -(E⁻¹ * δ * E⁻¹) := by
    have hEEi : E * E⁻¹ = 1 := Matrix.mul_nonsing_inv E hE.isUnit
    calc Dm = (Dm * E + E⁻¹ * δ) * E⁻¹ - E⁻¹ * δ * E⁻¹ := by
          rw [Matrix.add_mul, Matrix.mul_assoc Dm, hEEi, Matrix.mul_one]; abel
      _ = -(E⁻¹ * δ * E⁻¹) := by rw [hzero, Matrix.zero_mul, zero_sub]
  rw [hD] at hDi
  exact hDi

/-! ### Directions -/

section Directions

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]

/-- The coframe direction `(δ, 0, 0, 0, 0)`. -/
def coframeDir (δ : Mat) : Field 𝔄 𝓗 𝓢 :=
  ContinuousLinearMap.inl ℝ Mat ((Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢) δ

/-- **The frozen metric direction** `((Se, 0, …), μ ↦ (S∂_μe, 0, …))` of a first jet. -/
def frozenDir (S : Mat) (wp : FJ 𝔄 𝓗 𝓢) : FJ 𝔄 𝓗 𝓢 :=
  (coframeDir (S * wp.1.1), fun μ => coframeDir (S * (wp.2 μ).1))

variable (S : Mat) (wp : FJ 𝔄 𝓗 𝓢) (t : ℝ)

theorem fz_e : (wp + t • frozenDir S wp).1.1 = wp.1.1 + t • (S * wp.1.1) := rfl

theorem fz_A : (wp + t • frozenDir S wp).1.2.1 = wp.1.2.1 := by
  funext μ; simp [frozenDir, coframeDir]

theorem fz_H : (wp + t • frozenDir S wp).1.2.2.1 = wp.1.2.2.1 := by
  simp [frozenDir, coframeDir]

theorem fz_Ψ : (wp + t • frozenDir S wp).1.2.2.2.1 = wp.1.2.2.2.1 := by
  simp [frozenDir, coframeDir]

theorem fz_Ψb : (wp + t • frozenDir S wp).1.2.2.2.2 = wp.1.2.2.2.2 := by
  ext x; simp [frozenDir, coframeDir]

theorem fz_pe (μ : Fin 4) :
    ((wp + t • frozenDir S wp).2 μ).1 = (wp.2 μ).1 + t • (S * (wp.2 μ).1) := rfl

theorem fz_pA (μ : Fin 4) : ((wp + t • frozenDir S wp).2 μ).2.1 = (wp.2 μ).2.1 := by
  funext ν; simp [frozenDir, coframeDir]

theorem fz_pH (μ : Fin 4) : ((wp + t • frozenDir S wp).2 μ).2.2.1 = (wp.2 μ).2.2.1 := by
  simp [frozenDir, coframeDir]

theorem fz_pΨ (μ : Fin 4) : ((wp + t • frozenDir S wp).2 μ).2.2.2.1 = (wp.2 μ).2.2.2.1 := by
  simp [frozenDir, coframeDir]

theorem fz_pΨb (μ : Fin 4) : ((wp + t • frozenDir S wp).2 μ).2.2.2.2 = (wp.2 μ).2.2.2.2 := by
  ext x; simp [frozenDir, coframeDir]

theorem fz_FA (μ ν : Fin 4) : FA (wp + t • frozenDir S wp) μ ν = FA wp μ ν := by
  unfold FA; rw [fz_A, fz_pA, fz_pA]

theorem fz_KH (D : Data 𝔄 𝓗 𝓢) (μ : Fin 4) : KH D (wp + t • frozenDir S wp) μ = KH D wp μ := by
  unfold KH; rw [fz_A, fz_H, fz_pH]

theorem fz_omC (μ : Fin 4) : omC (wp + t • frozenDir S wp) μ =
    readerOmega (wp.1.1 + t • (S * wp.1.1)) (fun l => (wp.2 l).1 + t • (S * (wp.2 l).1)) μ :=
  rfl

end Directions

/-! ### The derivative of the reader connection along the frozen metric line -/

section OmegaDot

/-- The reader connection along `(e, q) ↦ (e + tSe, q + tSq)`. -/
def omT (E : Mat) (q : Fin 4 → Mat) (S : Mat) (t : ℝ) (μ : Fin 4) : Mat :=
  readerOmega (E + t • (S * E)) (fun l => q l + t • (S * q l)) μ

/-- Its derivative at `t = 0` (entrywise). -/
def omDot (E : Mat) (q : Fin 4 → Mat) (S : Mat) (μ : Fin 4) : Mat :=
  fun a b => deriv (fun t : ℝ => omT E q S t μ a b) 0

theorem omT_zero (E : Mat) (q : Fin 4 → Mat) (S : Mat) (μ : Fin 4) :
    omT E q S 0 μ = readerOmega E q μ := by
  simp [omT]

theorem hasDerivAt_omT {E : Mat} (hE : E.det ≠ 0) (q : Fin 4 → Mat) (S : Mat) (μ : Fin 4) :
    HasDerivAt (fun t : ℝ => omT E q S t μ) (omDot E q S μ) 0 := by
  refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => ?_
  refine DifferentiableAt.hasDerivAt ?_
  set c : ℝ → Mat × (Fin 4 → Mat) := fun t => (E + t • (S * E), fun l => q l + t • (S * q l))
  have hc : DifferentiableAt ℝ c 0 := by
    refine DifferentiableAt.prodMk ?_ ?_
    · exact (differentiableAt_const _).add (differentiableAt_id.smul_const _)
    · exact differentiableAt_pi.2 fun l =>
        (differentiableAt_const _).add (differentiableAt_id.smul_const _)
  have hc0 : (c 0).1.det ≠ 0 := by simpa [c] using hE
  have h1 := ((NativeDensity.contDiffAt_readerOmega_entry μ a b hc0).differentiableAt
    (by simp)).comp (0 : ℝ) hc
  exact h1

theorem eventually_det_ne_frozen {E : Mat} (hE : E.det ≠ 0) (S : Mat) :
    ∀ᶠ t : ℝ in 𝓝 0, (E + t • (S * E)).det ≠ 0 := eventually_det_ne hE

/-- `Ω̇` is `η`-antisymmetric. -/
theorem omegaDot_antisym {E : Mat} (hE : E.det ≠ 0) (q : Fin 4 → Mat) (S : Mat) (μ : Fin 4) :
    eta * omDot E q S μ + (omDot E q S μ)ᵀ * eta = 0 := by
  have hω := hasDerivAt_omT hE q S μ
  ext a b
  have hF : HasDerivAt (fun t : ℝ => ∑ k, eta a k * omT E q S t μ k b +
      ∑ k, omT E q S t μ k a * eta k b)
      (∑ k, eta a k * omDot E q S μ k b + ∑ k, omDot E q S μ k a * eta k b) 0 := by
    refine (HasDerivAt.fun_sum fun k _ => ?_).fun_add (HasDerivAt.fun_sum fun k _ => ?_)
    · exact (hasDerivAt_pi.1 (hasDerivAt_pi.1 hω k) b).const_mul _
    · exact (hasDerivAt_pi.1 (hasDerivAt_pi.1 hω k) a).mul_const _
  have hev : (fun t : ℝ => ∑ k, eta a k * omT E q S t μ k b +
      ∑ k, omT E q S t μ k a * eta k b) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_det_ne_frozen hE S] with t ht
    have h := congrFun (congrFun (readerOmega_antisym ht (fun l => q l + t • (S * q l)) μ) a) b
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.zero_apply] at h
    simpa [omT, Matrix.transpose_apply] using h
  have h0 := hF.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev)
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.zero_apply]
  simpa [Matrix.transpose_apply] using h0

/-- **Torsion of `Ω̇`**: `(Ω̇_αe)_{aβ} - (Ω̇_βe)_{aα} = (Y_αe)_{aβ} - (Y_βe)_{aα}` with
`Y_α = [S, Ω_α]`. -/
theorem omegaDot_torsion {E : Mat} (hE : E.det ≠ 0) (q : Fin 4 → Mat) (S : Mat)
    (α β a : Fin 4) :
    (omDot E q S α * E) a β - (omDot E q S β * E) a α =
      ((S * readerOmega E q α - readerOmega E q α * S) * E) a β -
        ((S * readerOmega E q β - readerOmega E q β * S) * E) a α := by
  have hωα := hasDerivAt_omT hE q S α
  have hωβ := hasDerivAt_omT hE q S β
  -- the torsion function along the line
  set Tf : ℝ → ℝ := fun t => (omT E q S t α * (E + t • (S * E)) + (q α + t • (S * q α))) a β -
    (omT E q S t β * (E + t • (S * E)) + (q β + t • (S * q β))) a α
  have hTf0 : Tf =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_det_ne_frozen hE S] with t ht
    have h := readerOmega_torsion ht (fun l => q l + t • (S * q l)) α β a
    simp only [Tf, omT]
    rw [h, sub_self]
  have hL : HasDerivAt (fun t : ℝ => E + t • (S * E)) (S * E) 0 := hasDerivAt_affine E (S * E)
  have hprod : ∀ γ c d, HasDerivAt (fun t : ℝ => (omT E q S t γ * (E + t • (S * E)) +
      (q γ + t • (S * q γ))) c d)
      ((omDot E q S γ * E + readerOmega E q γ * (S * E) + S * q γ) c d) 0 := by
    intro γ c d
    have hω := hasDerivAt_omT hE q S γ
    have h1 : HasDerivAt (fun t : ℝ => ∑ k, omT E q S t γ c k * (E + t • (S * E)) k d)
        (∑ k, (omDot E q S γ c k * E k d + readerOmega E q γ c k * (S * E) k d)) 0 := by
      refine HasDerivAt.fun_sum fun k _ => ?_
      have := (hasDerivAt_pi.1 (hasDerivAt_pi.1 hω c) k).fun_mul
        (hasDerivAt_pi.1 (hasDerivAt_pi.1 hL k) d)
      refine this.congr_deriv ?_
      rw [omT_zero]; simp
    have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_affine (q γ) (S * q γ)) c) d
    refine (h1.fun_add h2).congr_deriv ?_
    simp only [Matrix.add_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  have hT := ((hprod α a β).sub (hprod β a α)).unique
    ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hTf0)
  -- the torsion at `t = 0`, multiplied by `S`
  have hS0 : (S * (readerOmega E q α * E + q α)) a β = (S * (readerOmega E q β * E + q β)) a α := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [readerOmega_torsion hE q α β k]
  simp only [Matrix.add_apply] at hT
  simp only [Matrix.mul_add, Matrix.add_apply] at hS0
  simp only [Matrix.sub_mul, Matrix.sub_apply, Matrix.mul_assoc]
  linarith

/-- `η[S, Ω]` is symmetric when `ηS` is symmetric and `ηΩ` antisymmetric. -/
theorem commutator_symm {S Ω : Mat} (hS : (eta * S)ᵀ = eta * S)
    (hΩ : eta * Ω + Ωᵀ * eta = 0) : (eta * (S * Ω - Ω * S))ᵀ = eta * (S * Ω - Ω * S) := by
  have h1 : Sᵀ * eta = eta * S := by
    rw [← hS, Matrix.transpose_mul, PalatiniEuler.eta_transpose]
  have h2 : Ωᵀ * eta = -(eta * Ω) := eq_neg_of_add_eq_zero_right hΩ
  have hee : eta * eta = 1 := PalatiniEuler.eta_mul_eta
  rw [Matrix.transpose_mul, PalatiniEuler.eta_transpose, Matrix.transpose_sub,
    Matrix.transpose_mul, Matrix.transpose_mul]
  calc (Ωᵀ * Sᵀ - Sᵀ * Ωᵀ) * eta = Ωᵀ * (Sᵀ * eta) - Sᵀ * (Ωᵀ * eta) := by noncomm_ring
    _ = Ωᵀ * (eta * S) - Sᵀ * (-(eta * Ω)) := by rw [h1, h2]
    _ = (Ωᵀ * eta) * S + (Sᵀ * eta) * Ω := by noncomm_ring
    _ = -(eta * Ω) * S + (eta * S) * Ω := by rw [h1, h2]
    _ = eta * (S * Ω - Ω * S) := by noncomm_ring

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢]

/-- **The spin-connection term does not move under a metric variation**:
`Σ_μ {γ^μ(e), σ(Ω̇_μ)} = 0` when `ηS` is symmetric. -/
theorem spin_anticomm_frozen (D : Data 𝔄 𝓗 𝓢)
    (hcl : ∀ a b, D.γ a * D.γ b + D.γ b * D.γ a = (2 * eta a b) • 1)
    (hσ : ∀ om, D.σ om = sigmaOf D.γ om) {E : Mat} (hE : E.det ≠ 0) (q : Fin 4 → Mat)
    {S : Mat} (hS : (eta * S)ᵀ = eta * S) :
    ∑ ν, (gammaMu D ν E * D.σ (omDot E q S ν) + D.σ (omDot E q S ν) * gammaMu D ν E) = 0 :=
  anticomm_sum_zero D hcl hσ hE (omDot E q S)
    (fun α => S * readerOmega E q α - readerOmega E q α * S)
    (fun α => omegaDot_antisym hE q S α)
    (fun α => commutator_symm hS (readerOmega_antisym hE q α))
    (fun α β a => omegaDot_torsion hE q S α β a)

/-- **The spin-connection term does not move under a symmetric jet variation**: with
`X_ν = Ω_ν(e, μ ↦ Te)` and `ηT` symmetric, `Σ_ν {γ^ν(e), σ(X_ν)} = 0`. -/
theorem spin_anticomm_jet (D : Data 𝔄 𝓗 𝓢)
    (hcl : ∀ a b, D.γ a * D.γ b + D.γ b * D.γ a = (2 * eta a b) • 1)
    (hσ : ∀ om, D.σ om = sigmaOf D.γ om) {E : Mat} (hE : E.det ≠ 0) (μ : Fin 4)
    {T : Mat} (hT : (eta * T)ᵀ = eta * T) :
    ∑ ν, (gammaMu D ν E * D.σ (readerOmega E (Pi.single μ (T * E)) ν) +
      D.σ (readerOmega E (Pi.single μ (T * E)) ν) * gammaMu D ν E) = 0 := by
  refine anticomm_sum_zero D hcl hσ hE (fun ν => readerOmega E (Pi.single μ (T * E)) ν)
    (fun α => -((Pi.single μ T : Fin 4 → Mat) α)) (fun α => readerOmega_antisym hE _ α) ?_ ?_
  · intro α
    by_cases h : α = μ
    · subst h; simp [hT]
    · simp [h]
  · intro α β a
    have h := readerOmega_torsion hE (Pi.single μ (T * E)) α β a
    have hq : ∀ γ, (Pi.single μ (T * E) : Fin 4 → Mat) γ = (Pi.single μ T : Fin 4 → Mat) γ * E := by
      intro γ
      by_cases h : γ = μ
      · subst h; simp
      · simp [h]
    rw [Matrix.add_apply, Matrix.add_apply, hq α, hq β] at h
    simp only [Matrix.neg_mul, Matrix.neg_apply]
    linarith

end OmegaDot

/-! ### The Dirac stress -/

section DiracStress

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

/-- The Dirac Lagrangian per unit volume
`ℓ_D = Re{(i/2)[Ψ̄γ^μ∇_μΨ - (∇_μΨ̄)γ^μΨ] - Ψ̄𝓜(H)Ψ}`. -/
def diracLag (wp : FJ 𝔄 𝓗 𝓢) : ℝ :=
  (Complex.I / 2 * ∑ μ, (wp.1.2.2.2.2 (gammaMu D μ wp.1.1 (DPsi D wp μ)) -
      DPsiBar D wp μ (gammaMu D μ wp.1.1 wp.1.2.2.2.1)) -
    wp.1.2.2.2.2 (D.yukawa wp.1.2.2.1 wp.1.2.2.2.1)).re

theorem LDc_eq_volume_mul (wp : FJ 𝔄 𝓗 𝓢) : LDc D wp = volume wp.1.1 * diracLag D wp := rfl

/-- The canonical Dirac tensor `Θ_μ{}^b = Re{(i/2)[Ψ̄γ^b∇_μΨ - (∇_μΨ̄)γ^bΨ]}`
(`γ^b = γ^b(e)` the coordinate gamma matrices). -/
def thetaN (wp : FJ 𝔄 𝓗 𝓢) (μ b : Fin 4) : ℝ :=
  (Complex.I / 2 * (wp.1.2.2.2.2 (gammaMu D b wp.1.1 (DPsi D wp μ)) -
    DPsiBar D wp μ (gammaMu D b wp.1.1 wp.1.2.2.2.1))).re

/-- **The Dirac stress** `T_D^{ab} = g^{ab}ℓ_D - g^{aμ}Θ_μ{}^b` (contracted with symmetric
metric variations only its symmetric part matters). -/
def diracStressUp (wp : FJ 𝔄 𝓗 𝓢) (a b : Fin 4) : ℝ :=
  ginv wp.1.1 a b * diracLag D wp - ∑ μ, ginv wp.1.1 a μ * thetaN D wp μ b

/-- `g^{μa}δg_{ab} = 2(e⁻¹Se)^μ_b` for the metric variation `δg = (Se)ᵀηe + eᵀη(Se)`. -/
theorem ginv_metricVar {E : Mat} (hE : E.det ≠ 0) {S : Mat} (hS : (eta * S)ᵀ = eta * S)
    (μ b : Fin 4) :
    ∑ a, ginv E μ a * metricVarM E (S * E) a b = 2 * (E⁻¹ * S * E) μ b := by
  have h1 : Sᵀ * eta = eta * S := by
    rw [← hS, Matrix.transpose_mul, PalatiniEuler.eta_transpose]
  have hk : metricVarM E (S * E) = (2 : ℝ) • (Eᵀ * eta * S * E) := by
    unfold metricVarM
    rw [Matrix.transpose_mul]
    calc Eᵀ * Sᵀ * eta * E + Eᵀ * eta * (S * E) = Eᵀ * (Sᵀ * eta) * E + Eᵀ * eta * S * E := by
          noncomm_ring
      _ = Eᵀ * (eta * S) * E + Eᵀ * eta * S * E := by rw [h1]
      _ = (2 : ℝ) • (Eᵀ * eta * S * E) := by rw [two_smul]; noncomm_ring
  have hEt : (E⁻¹)ᵀ * Eᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv E hE.isUnit, Matrix.transpose_one]
  have hm : (metric E)⁻¹ * metricVarM E (S * E) = (2 : ℝ) • (E⁻¹ * S * E) := by
    rw [hk, metric_inv_eq E hE, Matrix.mul_smul]
    congr 1
    calc E⁻¹ * eta * (E⁻¹)ᵀ * (Eᵀ * eta * S * E) =
          E⁻¹ * eta * ((E⁻¹)ᵀ * Eᵀ) * eta * S * E := by noncomm_ring
      _ = E⁻¹ * (eta * eta) * S * E := by rw [hEt]; noncomm_ring
      _ = E⁻¹ * S * E := by rw [PalatiniEuler.eta_mul_eta]; noncomm_ring
  have h := congrFun (congrFun hm μ) b
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h
  exact h

/-- `γ̇^μ = -(e⁻¹S)^μ_aγ^a = -(e⁻¹Se)^μ_β γ^β(e)`. -/
theorem gammaDot_eq {E : Mat} (hE : E.det ≠ 0) (S : Mat) (μ : Fin 4) :
    ∑ a, (-(E⁻¹ * (S * E) * E⁻¹)) μ a • D.γ a =
      -∑ β, (E⁻¹ * S * E) μ β • gammaMu D β E := by
  have hEEi : E * E⁻¹ = 1 := Matrix.mul_nonsing_inv E hE.isUnit
  have h1 : E⁻¹ * (S * E) * E⁻¹ = E⁻¹ * S * E * E⁻¹ := by noncomm_ring
  unfold gammaMu
  simp only [invEntry, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_smul, ← neg_smul, h1]
  congr 1

theorem sum3_perm {M : Type*} [AddCommMonoid M] (f : Fin 4 → Fin 4 → Fin 4 → M) :
    ∑ a, ∑ b, ∑ μ, f a b μ = ∑ μ, ∑ b, ∑ a, f a b μ := by
  calc ∑ a, ∑ b, ∑ μ, f a b μ = ∑ a, ∑ μ, ∑ b, f a b μ :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ μ, ∑ a, ∑ b, f a b μ := Finset.sum_comm
    _ = ∑ μ, ∑ b, ∑ a, f a b μ := Finset.sum_congr rfl fun μ _ => Finset.sum_comm

variable (S : Mat) (wp : FJ 𝔄 𝓗 𝓢)

theorem fz_DPsi (t : ℝ) (μ : Fin 4) : DPsi D (wp + t • frozenDir S wp) μ =
    (D.σ (omT wp.1.1 (fun l => (wp.2 l).1) S t μ) + D.ρS (wp.1.2.1 μ)) wp.1.2.2.2.1 +
      (wp.2 μ).2.2.2.1 := by
  unfold DPsi
  rw [fz_omC, fz_A, fz_Ψ, fz_pΨ]
  rfl

theorem fz_DPsiBar (t : ℝ) (μ : Fin 4) : DPsiBar D (wp + t • frozenDir S wp) μ =
    wp.1.2.2.2.2.comp (-D.ρS (wp.1.2.1 μ) - D.σ (omT wp.1.1 (fun l => (wp.2 l).1) S t μ)) +
      (wp.2 μ).2.2.2.2 := by
  unfold DPsiBar
  rw [fz_omC, fz_A, fz_Ψb, fz_pΨb]
  rfl

/-- **The Dirac density along the frozen metric direction**: for `ηS` symmetric,
`d/dt L_D(J + t·frozenDir) = (v/2) T_D^{ab} δg_{ab}`, `δg = (Se)ᵀηe + eᵀη(Se)`. -/
theorem hasDerivAt_LDc_frozen (hcl : ∀ a b, D.γ a * D.γ b + D.γ b * D.γ a = (2 * eta a b) • 1)
    (hσ : ∀ om, D.σ om = sigmaOf D.γ om) (hE : wp.1.1.det ≠ 0) {S : Mat}
    (hS : (eta * S)ᵀ = eta * S) :
    HasDerivAt (fun t : ℝ => LDc D (wp + t • frozenDir S wp))
      (volume wp.1.1 / 2 * ∑ a, ∑ b, diracStressUp D wp a b *
        metricVarM wp.1.1 (S * wp.1.1) a b) 0 := by
  set E := wp.1.1 with hEdef
  set q : Fin 4 → Mat := fun l => (wp.2 l).1
  set Ψ := wp.1.2.2.2.1
  set Ψb := wp.1.2.2.2.2
  set G : Fin 4 → Spin 𝓢 := fun μ => gammaMu D μ E
  set Gd : Fin 4 → Spin 𝓢 := fun μ => ∑ a, (-(E⁻¹ * (S * E) * E⁻¹)) μ a • D.γ a
  set σd : Fin 4 → Spin 𝓢 := fun μ => D.σ (omDot E q S μ)
  -- the pieces
  have hG : ∀ μ, HasDerivAt (fun t : ℝ => gammaMu D μ (E + t • (S * E))) (Gd μ) 0 := by
    intro μ
    have hinv := hasDerivAt_inv_affine hE (S * E)
    unfold gammaMu
    simp only [invEntry]
    exact HasDerivAt.fun_sum fun a _ =>
      (hasDerivAt_pi.1 (hasDerivAt_pi.1 hinv μ) a).smul_const (D.γ a)
  have hσt : ∀ μ, HasDerivAt (fun t : ℝ => D.σ (omT E q S t μ)) (σd μ) 0 := fun μ =>
    D.σ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_omT hE q S μ)
  have hDΨ : ∀ μ, HasDerivAt (fun t : ℝ => DPsi D (wp + t • frozenDir S wp) μ) (σd μ Ψ) 0 := by
    intro μ
    have h := (((hσt μ).add_const (D.ρS (wp.1.2.1 μ))).clm_apply
      (hasDerivAt_const (0 : ℝ) Ψ)).add_const ((wp.2 μ).2.2.2.1)
    simp only [fz_DPsi]
    refine h.congr_deriv ?_
    simp
  have hDΨb : ∀ μ, HasDerivAt (fun t : ℝ => DPsiBar D (wp + t • frozenDir S wp) μ)
      (Ψb.comp (-σd μ)) 0 := by
    intro μ
    have h := ((hasDerivAt_const (0 : ℝ) Ψb).clm_comp
      ((hasDerivAt_const (0 : ℝ) (-D.ρS (wp.1.2.1 μ))).sub (hσt μ))).add_const
      ((wp.2 μ).2.2.2.2)
    simp only [fz_DPsiBar]
    refine h.congr_deriv ?_
    simp
  have hE0 : ∀ t : ℝ, (wp + t • frozenDir S wp).1.1 = E + t • (S * E) := fun t => fz_e S wp t
  have hfun : (fun t : ℝ => LDc D (wp + t • frozenDir S wp)) = fun t =>
      volume (E + t • (S * E)) * (Complex.I / 2 * ∑ μ,
        (Ψb (gammaMu D μ (E + t • (S * E)) (DPsi D (wp + t • frozenDir S wp) μ)) -
          DPsiBar D (wp + t • frozenDir S wp) μ (gammaMu D μ (E + t • (S * E)) Ψ)) -
        Ψb (D.yukawa wp.1.2.2.1 Ψ)).re := by
    funext t
    unfold LDc
    rw [hE0, fz_Ψ, fz_Ψb, fz_H]
  rw [hfun]
  have h0 : ∀ μ, DPsi D (wp + (0 : ℝ) • frozenDir S wp) μ = DPsi D wp μ := fun μ => by
    rw [fz_DPsi, omT_zero]; rfl
  have h0b : ∀ μ, DPsiBar D (wp + (0 : ℝ) • frozenDir S wp) μ = DPsiBar D wp μ :=
    fun μ => by rw [fz_DPsiBar, omT_zero]; rfl
  have ht1 : ∀ μ, HasDerivAt (fun t : ℝ =>
      Ψb (gammaMu D μ (E + t • (S * E)) (DPsi D (wp + t • frozenDir S wp) μ)))
      (Ψb (Gd μ (DPsi D wp μ) + G μ (σd μ Ψ))) 0 := by
    intro μ
    have h := Ψb.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hG μ).clm_apply (hDΨ μ))
    simp only [zero_smul, add_zero, h0] at h
    exact h
  have ht2 : ∀ μ, HasDerivAt (fun t : ℝ =>
      DPsiBar D (wp + t • frozenDir S wp) μ (gammaMu D μ (E + t • (S * E)) Ψ))
      (Ψb.comp (-σd μ) (G μ Ψ) + DPsiBar D wp μ (Gd μ Ψ)) 0 := by
    intro μ
    have h := (hDΨb μ).clm_apply ((hG μ).clm_apply (hasDerivAt_const (0 : ℝ) Ψ))
    simp only [zero_smul, add_zero, h0b, map_zero] at h
    exact h
  have hΦ := ((HasDerivAt.fun_sum (u := Finset.univ) fun μ _ => (ht1 μ).sub (ht2 μ)).const_mul
    (Complex.I / 2)).sub_const (Ψb (D.yukawa wp.1.2.2.1 Ψ))
  have hre := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hΦ
  have hv := hasDerivAt_volume_affine hE (S * E)
  have htot := hv.fun_mul hre
  simp only [zero_smul, add_zero] at htot
  refine htot.congr_deriv ?_
  -- the spin-connection part vanishes
  have hanti := spin_anticomm_frozen D hcl hσ hE q hS
  have hspin : ∑ μ, ((Ψb (Gd μ (DPsi D wp μ) + G μ (σd μ Ψ))) -
      (Ψb.comp (-σd μ) (G μ Ψ) + DPsiBar D wp μ (Gd μ Ψ))) =
      ∑ μ, (Ψb (Gd μ (DPsi D wp μ)) - DPsiBar D wp μ (Gd μ Ψ)) := by
    have hz : ∑ μ, (Ψb (G μ (σd μ Ψ)) + Ψb (σd μ (G μ Ψ))) = 0 := by
      have : ∑ μ, (Ψb (G μ (σd μ Ψ)) + Ψb (σd μ (G μ Ψ))) =
          Ψb ((∑ μ, (G μ * σd μ + σd μ * G μ)) Ψ) := by
        rw [_root_.sum_apply, map_sum]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [_root_.add_apply, map_add]
        rfl
      rw [this, hanti]
      simp
    have : ∀ μ, (Ψb (Gd μ (DPsi D wp μ) + G μ (σd μ Ψ))) -
        (Ψb.comp (-σd μ) (G μ Ψ) + DPsiBar D wp μ (Gd μ Ψ)) =
        (Ψb (Gd μ (DPsi D wp μ)) - DPsiBar D wp μ (Gd μ Ψ)) +
          (Ψb (G μ (σd μ Ψ)) + Ψb (σd μ (G μ Ψ))) := by
      intro μ
      simp only [map_add, ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, map_neg]
      ring
    simp only [this, Finset.sum_add_distrib, hz, add_zero]
  -- the canonical part
  set c : Mat := E⁻¹ * S * E
  have hGd : ∀ μ, Gd μ = -∑ β, c μ β • G β := fun μ => gammaDot_eq D hE S μ
  have hcan : (Complex.I / 2 * ∑ μ, (Ψb (Gd μ (DPsi D wp μ)) - DPsiBar D wp μ (Gd μ Ψ))).re =
      -∑ μ, ∑ β, c μ β * thetaN D wp μ β := by
    have hterm : ∀ μ, Ψb (Gd μ (DPsi D wp μ)) - DPsiBar D wp μ (Gd μ Ψ) =
        -∑ β, c μ β • (Ψb (G β (DPsi D wp μ)) - DPsiBar D wp μ (G β Ψ)) := by
      intro μ
      rw [hGd]
      simp only [ContinuousLinearMap.neg_apply, _root_.sum_apply,
        ContinuousLinearMap.smul_apply, map_neg, map_sum, map_smul, smul_sub,
        Finset.sum_sub_distrib]
      abel
    simp only [hterm, Finset.sum_neg_distrib, mul_neg, Complex.neg_re, Finset.mul_sum,
      Complex.re_sum, mul_smul_comm, Complex.smul_re, smul_eq_mul]
    rfl
  -- assemble
  rw [Complex.reCLM_apply, hspin, hcan]
  have hk : ∀ μ b, ∑ a, ginv E a μ * metricVarM E (S * E) a b = 2 * c μ b := by
    intro μ b
    rw [← ginv_metricVar hE hS μ b]
    exact Finset.sum_congr rfl fun a _ => by rw [ginv_symm E a μ]
  have htarget : ∑ a, ∑ b, diracStressUp D wp a b * metricVarM E (S * E) a b =
      diracLag D wp * trG (fun a b => ginv E a b) (fun a b => metricVarM E (S * E) a b) -
        2 * ∑ μ, ∑ b, c μ b * thetaN D wp μ b := by
    unfold diracStressUp trG
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    · rw [sum3_perm (fun a b μ => ginv E a μ * thetaN D wp μ b * metricVarM E (S * E) a b)]
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun b _ => ?_
      have := hk μ b
      calc ∑ a, ginv E a μ * thetaN D wp μ b * metricVarM E (S * E) a b =
            thetaN D wp μ b * ∑ a, ginv E a μ * metricVarM E (S * E) a b := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun a _ => by ring
        _ = 2 * (c μ b * thetaN D wp μ b) := by rw [this]; ring
  rw [htarget]
  have hdl : (⇑Complex.reCLM ∘ fun x : ℝ => Complex.I / 2 * ∑ i,
      ((fun t : ℝ => Ψb ((gammaMu D i (E + t • (S * E))) (DPsi D (wp + t • frozenDir S wp) i))) -
        fun t : ℝ => (DPsiBar D (wp + t • frozenDir S wp) i) ((gammaMu D i (E + t • (S * E))) Ψ))
        x - Ψb ((D.yukawa wp.1.2.2.1) Ψ)) 0 = diracLag D wp := by
    simp only [Function.comp_apply, Pi.sub_apply, zero_smul, add_zero, h0, h0b,
      Complex.reCLM_apply]
    rfl
  rw [hdl]
  ring

end DiracStress

/-! ### Symmetric jet directions -/

section JetSym

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

/-- The coframe jet direction `(0, ν ↦ [ν = μ](m, 0, 0, 0, 0))`. -/
def jetDir (μ : Fin 4) (m : Mat) : FJ 𝔄 𝓗 𝓢 :=
  ContEulerAlg.slot (Field 𝔄 𝓗 𝓢) μ (coframeDir m)

theorem jetDir_eq (μ : Fin 4) (m : Mat) :
    (jetDir μ m : FJ 𝔄 𝓗 𝓢) = (0, Pi.single μ (coframeDir m)) := rfl

variable (wp : FJ 𝔄 𝓗 𝓢) (μ : Fin 4) (m : Mat) (t : ℝ)

theorem smul_zero_field (t : ℝ) : t • (0 : Field 𝔄 𝓗 𝓢) = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · simp
  · funext ν; simp
  · simp
  · simp
  · ext x; simp

theorem jd_1 : (wp + t • (jetDir μ m : FJ 𝔄 𝓗 𝓢)).1 = wp.1 := by
  rw [jetDir_eq, Prod.fst_add, Prod.smul_fst, smul_zero_field, add_zero]

theorem jd_single (l : Fin 4) :
    (Pi.single μ (coframeDir m) : Fin 4 → Field 𝔄 𝓗 𝓢) l =
      coframeDir ((Pi.single μ m : Fin 4 → Mat) l) := by
  by_cases h : l = μ
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, coframeDir, map_zero]

theorem jd_pe (l : Fin 4) : ((wp + t • (jetDir μ m : FJ 𝔄 𝓗 𝓢)).2 l).1 =
    (wp.2 l).1 + t • (Pi.single μ m : Fin 4 → Mat) l := by
  simp only [jetDir_eq, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, jd_single,
    Prod.fst_add, Prod.smul_fst]
  simp [coframeDir]

theorem jd_pΨ (l : Fin 4) :
    ((wp + t • (jetDir μ m : FJ 𝔄 𝓗 𝓢)).2 l).2.2.2.1 = (wp.2 l).2.2.2.1 := by
  simp only [jetDir_eq, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, jd_single]
  simp [coframeDir]

theorem jd_pΨb (l : Fin 4) :
    ((wp + t • (jetDir μ m : FJ 𝔄 𝓗 𝓢)).2 l).2.2.2.2 = (wp.2 l).2.2.2.2 := by
  ext x; simp only [jetDir_eq, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, jd_single]
  simp [coframeDir]

theorem jd_pA (l : Fin 4) :
    ((wp + t • (jetDir μ m : FJ 𝔄 𝓗 𝓢)).2 l).2.1 = (wp.2 l).2.1 := by
  funext ν; simp only [jetDir_eq, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, jd_single]
  simp [coframeDir]

theorem jd_pH (l : Fin 4) :
    ((wp + t • (jetDir μ m : FJ 𝔄 𝓗 𝓢)).2 l).2.2.1 = (wp.2 l).2.2.1 := by
  simp only [jetDir_eq, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, jd_single]
  simp [coframeDir]

theorem jd_omC (ν : Fin 4) : omC (wp + t • (jetDir μ m : FJ 𝔄 𝓗 𝓢)) ν =
    omC wp ν + t • readerOmega wp.1.1 (Pi.single μ m) ν := by
  unfold omC
  rw [jd_1]
  have : (fun l => ((wp + t • (jetDir μ m : FJ 𝔄 𝓗 𝓢)).2 l).1) =
      (fun l => (wp.2 l).1) + t • (Pi.single μ m : Fin 4 → Mat) := by
    funext l; rw [jd_pe]; rfl
  rw [this, NativeScaling.readerOmega_add, NativeScaling.readerOmega_smul]

/-- **A symmetric coframe-jet direction does not move the Dirac density**: for `ηT` symmetric,
`d/dt L_D(J + t (0, [·=μ](Te, 0, …))) = 0`. -/
theorem hasDerivAt_LDc_jetSym (hcl : ∀ a b, D.γ a * D.γ b + D.γ b * D.γ a = (2 * eta a b) • 1)
    (hσ : ∀ om, D.σ om = sigmaOf D.γ om) (hE : wp.1.1.det ≠ 0) {T : Mat}
    (hT : (eta * T)ᵀ = eta * T) :
    HasDerivAt (fun t : ℝ => LDc D (wp + t • (jetDir μ (T * wp.1.1) : FJ 𝔄 𝓗 𝓢))) 0 0 := by
  set E := wp.1.1
  set X : Fin 4 → Mat := fun ν => readerOmega E (Pi.single μ (T * E)) ν
  set Ψ := wp.1.2.2.2.1
  set Ψb := wp.1.2.2.2.2
  have h := hasDerivAt_LDc_line D wp (jetDir μ (T * E))
    (fun t => by rw [jd_1]) (fun t => by rw [jd_1]) 0 (fun t => by rw [jd_1, smul_zero, add_zero])
    0 (fun t => by rw [jd_1]; ext x; simp)
    (fun ν => D.σ (X ν) Ψ)
    (fun t ν => by
      unfold DPsi
      rw [jd_omC, jd_1, jd_pΨ, map_add, map_smul]
      simp only [_root_.add_apply, _root_.smul_apply]
      abel)
    (fun ν => Ψb.comp (-D.σ (X ν)))
    (fun t ν => by
      unfold DPsiBar
      rw [jd_omC, jd_1, jd_pΨb, map_add, map_smul]
      ext x
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
        map_add, map_sub, map_neg, map_smul, Complex.real_smul]
      ring)
  refine h.congr_deriv ?_
  have hanti := spin_anticomm_jet D hcl hσ hE μ hT
  have hz : ∑ ν, ((0 : CoSpinor 𝓢) (gammaMu D ν E (DPsi D wp ν)) +
      Ψb (gammaMu D ν E (D.σ (X ν) Ψ)) -
      ((Ψb.comp (-D.σ (X ν))) (gammaMu D ν E Ψ) + DPsiBar D wp ν (gammaMu D ν E 0))) = 0 := by
    have : ∑ ν, ((0 : CoSpinor 𝓢) (gammaMu D ν E (DPsi D wp ν)) +
        Ψb (gammaMu D ν E (D.σ (X ν) Ψ)) -
        ((Ψb.comp (-D.σ (X ν))) (gammaMu D ν E Ψ) + DPsiBar D wp ν (gammaMu D ν E 0))) =
        Ψb ((∑ ν, (gammaMu D ν E * D.σ (X ν) + D.σ (X ν) * gammaMu D ν E)) Ψ) := by
      rw [_root_.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      simp only [ContinuousLinearMap.zero_apply, zero_add, map_zero, add_zero,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, map_neg, sub_neg_eq_add,
        _root_.add_apply, map_add]
      rfl
    rw [this, hanti]
    simp
  have hz' : ∑ μ', ((0 : CoSpinor 𝓢) ((gammaMu D μ' wp.1.1) (DPsi D wp μ')) +
      wp.1.2.2.2.2 ((gammaMu D μ' wp.1.1) ((D.σ (X μ')) Ψ)) -
      ((Ψb.comp (-D.σ (X μ'))) ((gammaMu D μ' wp.1.1) wp.1.2.2.2.1) +
        (DPsiBar D wp μ') ((gammaMu D μ' wp.1.1) 0))) = 0 := hz
  rw [hz']
  simp

end JetSym

end

end NativeStressEuler

end RenewalGeometry
