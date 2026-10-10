/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeBosonicEulerRows

/-!
# The Dirac identity of the coframe spin connection and the Dirac Euler rows

Einstein–Standard-Model action-closure manuscript, bridge steps P1/P3 of `thm:native-closure`
(Dirac sector of the variational identity "the Euler rows of the native Lagrangian are the
physical field equations up to smooth invertible algebraic coefficients").

## Algebra of the spin representation

For gamma matrices with the Clifford relations `γ^aγ^b + γ^bγ^a = 2η^{ab}` and the spin
representation `σ(ω) = ¼ ω_{ab} γ^aγ^b`, `ω_{ab} = η_{ac}ω^c_b` (`sigmaOf`):
* `clifford_comm` — `[γ^cγ^d, γ^a] = 2η^{da}γ^c - 2η^{ca}γ^d`;
* `sigmaOf_comm` — for `ηω` antisymmetric, `[σ(ω), γ^a] = -ω^a_b γ^b`.

## Geometry of the coframe-derived connection

For a smooth coframe field `e` with `det e > 0`, `ω_μ = Ω_μ(e, ∂e)` (`omega0`):
* `omega0_antisym` — metric compatibility: `η ω_μ` is antisymmetric
  (`ηω_μ + ω_μᵀη = 0`), from the Levi-Civita compatibility `∂g = gΓ + Γᵀg`;
* `frame_div` — the frame divergence `∂_μ(v e_b^μ) = v ω_μ^a_b e_a^μ`
  (`e_b^μ = (e⁻¹)^μ_b`, Jacobi's formula and the derivative of the inverse);
* **`dirac_identity`** — `Σ_μ (v[σ(ω_μ) + ρ_S(A_μ), γ^μ(e)] + ∂_μ(v γ^μ(e))) = 0` when `ρ_S`
  commutes with Clifford multiplication.  This is the identity that turns the Euler rows of the
  first-order symmetric Dirac density into `v(e)` times the Dirac residuals.

## The Dirac Euler rows of `L₀ = limDensity (firstJetDensity D)`

* `fderiv_L0_psiBar`, `fderiv_L0_psi`, `fderiv_L0_dpsiBar`, `fderiv_L0_dpsi` — the four spinor
  partials of the native continuum Lagrangian;
* **`psibar_euler_row`** — `𝓔₀(Y)(z)[(0,0,0,0,φ)] = v(e) Re{iφ(γ^μ∇_μΨ) - φ(𝓜_𝐘(H)Ψ)}`;
* **`psi_euler_row`** — `𝓔₀(Y)(z)[(0,0,0,χ,0)] = -v(e) Re{i(∇_μΨ̄)(γ^μχ) + Ψ̄(𝓜_𝐘(H)χ)}`,
  with `∇_μΨ = ∂_μΨ + (σ(ω_μ) + ρ_S(A_μ))Ψ`, `∇_μΨ̄ = ∂_μΨ̄ - Ψ̄(ρ_S(A_μ) + σ(ω_μ))`.

Disclosed: Clifford relations `γ^aγ^b + γ^bγ^a = 2η^{ab}` and `σ(ω) = ¼(ηω)_{ab}γ^aγ^b` are
hypotheses (the fields of `NativeDensity.Data` are arbitrary linear data); the co-spinor space
is the real-linear one of `Data` (the `ℂ`-linear reading is in `NativeModelMap`).
-/

namespace RenewalGeometry

namespace NativeDiracEuler

open Finset HarmonicDefect EHJetVariation EHFieldVariation ActualJetSystem PalatiniEuler
  NativeMatterEuler NativeBosonicEuler
open NativeScaling (Mat eta metric readerOmega readerG)
open NativeDensity
open NativeEulerConsistency (omega0 omega0_eq gamMat fderiv_matToOp_apply
  fderiv_mul_apply differentiableAt_inv differentiableAt_dir)
open DiscreteEulerConsistency (R4 evec jet1 contEuler)
open Filter Topology Set
open SobolevOpen (pd)
open scoped ContDiff Matrix

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Clifford algebra -/

section Clifford

variable {R : Type*} [Ring R] [Algebra ℝ R]

theorem eta_apply (a b : Fin 4) : eta a b = if a = b then eta a a else 0 := by
  by_cases h : a = b
  · subst h; simp
  · simp [h, eta]

theorem sum_eta_eta (a c : Fin 4) : ∑ d, eta a d * eta d c = if a = c then 1 else 0 := by
  have h := congrFun (congrFun eta_mul_eta a) c
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  exact h

/-- `[γ^cγ^d, γ^a] = 2η^{da}γ^c - 2η^{ca}γ^d` from the Clifford relations. -/
theorem clifford_comm (γ : Fin 4 → R) (hcl : ∀ a b, γ a * γ b + γ b * γ a = (2 * eta a b) • 1)
    (c d a : Fin 4) :
    γ c * γ d * γ a - γ a * (γ c * γ d) = (2 * eta d a) • γ c - (2 * eta c a) • γ d := by
  have h1 : γ d * γ a = (2 * eta d a) • 1 - γ a * γ d := eq_sub_of_add_eq (hcl d a)
  have h2 : γ c * γ a = (2 * eta c a) • 1 - γ a * γ c := eq_sub_of_add_eq (hcl c a)
  calc γ c * γ d * γ a - γ a * (γ c * γ d) = γ c * (γ d * γ a) - γ a * γ c * γ d := by
        noncomm_ring
    _ = γ c * ((2 * eta d a) • 1 - γ a * γ d) - γ a * γ c * γ d := by rw [h1]
    _ = (2 * eta d a) • γ c - γ c * γ a * γ d - γ a * γ c * γ d := by
        rw [mul_sub, mul_smul_comm, mul_one]
        simp only [mul_assoc]
    _ = (2 * eta d a) • γ c - ((2 * eta c a) • 1 - γ a * γ c) * γ d - γ a * γ c * γ d := by
        rw [h2]
    _ = (2 * eta d a) • γ c - (2 * eta c a) • γ d := by
        rw [sub_mul, smul_mul_assoc, one_mul]
        abel

/-- The spin representation `σ(ω) = ¼ ω_{cd}γ^cγ^d`, `ω_{cd} = η_{ce}ω^e_d`. -/
def sigmaOf (γ : Fin 4 → R) (om : Mat) : R :=
  (1 / 4 : ℝ) • ∑ c, ∑ d, (∑ e, eta c e * om e d) • (γ c * γ d)

/-- **`[σ(ω), γ^a] = -ω^a_b γ^b`** for `ηω` antisymmetric. -/
theorem sigmaOf_comm (γ : Fin 4 → R) (hcl : ∀ a b, γ a * γ b + γ b * γ a = (2 * eta a b) • 1)
    (om : Mat) (hom : ∀ c d, ∑ e, eta c e * om e d = -∑ e, eta d e * om e c) (a : Fin 4) :
    sigmaOf γ om * γ a - γ a * sigmaOf γ om = -∑ b, om a b • γ b := by
  set w : Fin 4 → Fin 4 → ℝ := fun c d => ∑ e, eta c e * om e d with hw
  have hexp : sigmaOf γ om * γ a - γ a * sigmaOf γ om =
      (1 / 4 : ℝ) • ∑ c, ∑ d, w c d • ((2 * eta d a) • γ c - (2 * eta c a) • γ d) := by
    unfold sigmaOf
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, ← smul_sub,
      ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [← clifford_comm γ hcl c d a]
  rw [hexp]
  -- the two contractions
  have e1 : ∀ c, ∑ d, w c d * eta d a = -om a c := by
    intro c
    have : ∀ d, w c d * eta d a = -(∑ e, eta a d * eta d e * om e c) := by
      intro d
      rw [hw]
      simp only []
      rw [hom c d, neg_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [eta_symm d a]; ring
    simp only [this, Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, sum_eta_eta, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  have e2 : ∀ d, ∑ c, w c d * eta c a = om a d := by
    intro d
    have : ∀ c, w c d * eta c a = ∑ e, eta a c * eta c e * om e d := by
      intro c
      rw [hw]
      simp only []
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [eta_symm c a]; ring
    simp only [this]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, sum_eta_eta, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  have hsplit : ∑ c, ∑ d, w c d • ((2 * eta d a) • γ c - (2 * eta c a) • γ d) =
      (2 : ℝ) • ∑ c, (∑ d, w c d * eta d a) • γ c -
        (2 : ℝ) • ∑ d, (∑ c, w c d * eta c a) • γ d := by
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, Finset.sum_smul, smul_smul]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      congr 1; ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
      congr 1; ring
  rw [hsplit]
  simp only [e1, e2, neg_smul, Finset.sum_neg_distrib, smul_neg, smul_sub, smul_smul]
  rw [← neg_add', ← add_smul]
  norm_num

end Clifford

/-! ### Metric compatibility of the coframe-derived connection -/

section Geometry

variable {e : R4 → Mat}

/-- Metric compatibility in matrix form: `gΓ_μ + Γ_μᵀg = ∂_μg = (∂_μe)ᵀηe + eᵀη∂_μe`. -/
theorem compat_mat (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) (z : R4) (μ : Fin 4) :
    (e z)ᵀ * eta * e z * gamMat e z μ + (gamMat e z μ)ᵀ * ((e z)ᵀ * eta * e z) =
      (fderiv ℝ e z (evec μ))ᵀ * eta * e z + (e z)ᵀ * eta * fderiv ℝ e z (evec μ) := by
  have hd : Differentiable ℝ e := he.differentiable (by simp)
  have hinv : ∀ a c, ∑ b, gF e z a b * ginvOf (gF e z) b c = if a = c then 1 else 0 :=
    gF_mul_ginvOf hdet z
  have hdg : ∀ α μ ν, dF (gF e) z α μ ν = dF (gF e) z α ν μ := fun α => dF_gF_symm hd z α
  ext ν σ
  have hc := FrameCurvature.metric_compat (gF e z) (ginvOf (gF e z)) (dF (gF e) z) hinv hdg μ ν σ
  rw [dF_gF hd] at hc
  have hR : ((fderiv ℝ e z (evec μ))ᵀ * eta * e z + (e z)ᵀ * eta * fderiv ℝ e z (evec μ)) ν σ =
      readerG (e z) (fun l => fderiv ℝ e z (evec l)) μ ν σ := rfl
  rw [hR, hc, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [gamMat_eq_chr hd, Matrix.transpose_apply, gamMat_eq_chr hd]
  have h1 : ((e z)ᵀ * eta * e z) ν l = gF e z ν l := rfl
  have h2 : ((e z)ᵀ * eta * e z) l σ = gF e z σ l := gF_symm (e := e) z σ l ▸ rfl
  rw [h1, h2]
  ring

/-- **The coframe-derived connection is `η`-antisymmetric**: `ηω_μ + ω_μᵀη = 0`. -/
theorem omega0_antisym_mat (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) (z : R4)
    (μ : Fin 4) : eta * omega0 e z μ + (omega0 e z μ)ᵀ * eta = 0 := by
  set E := e z
  set Q := fderiv ℝ e z (evec μ)
  set G := gamMat e z μ
  have hu : IsUnit E.det := (hdet z).ne'.isUnit
  have hΩ : omega0 e z μ = E * G * E⁻¹ - Q * E⁻¹ := omega0_eq e z μ
  have hc := compat_mat he hdet z μ
  have hEiE : E⁻¹ * E = 1 := Matrix.nonsing_inv_mul E hu
  have hEEi : E * E⁻¹ = 1 := Matrix.mul_nonsing_inv E hu
  set Ω := omega0 e z μ
  have hΩE : Ω * E = E * G - Q := by
    rw [hΩ, Matrix.sub_mul, Matrix.mul_assoc, hEiE, Matrix.mul_one, Matrix.mul_assoc Q, hEiE,
      Matrix.mul_one]
  have h1 : Eᵀ * (eta * Ω) * E = Eᵀ * eta * E * G - Eᵀ * eta * Q := by
    calc Eᵀ * (eta * Ω) * E = Eᵀ * eta * (Ω * E) := by noncomm_ring
      _ = Eᵀ * eta * (E * G - Q) := by rw [hΩE]
      _ = _ := by noncomm_ring
  have h2 : Eᵀ * (Ωᵀ * eta) * E = Gᵀ * (Eᵀ * eta * E) - Qᵀ * eta * E := by
    have hT : Eᵀ * Ωᵀ = (E * G - Q)ᵀ := by rw [← hΩE, Matrix.transpose_mul]
    calc Eᵀ * (Ωᵀ * eta) * E = (Eᵀ * Ωᵀ) * eta * E := by noncomm_ring
      _ = (E * G - Q)ᵀ * eta * E := by rw [hT]
      _ = _ := by rw [Matrix.transpose_sub, Matrix.transpose_mul]; noncomm_ring
  have key : Eᵀ * (eta * Ω + Ωᵀ * eta) * E = 0 := by
    calc Eᵀ * (eta * Ω + Ωᵀ * eta) * E = Eᵀ * (eta * Ω) * E + Eᵀ * (Ωᵀ * eta) * E := by
          noncomm_ring
      _ = (Eᵀ * eta * E * G + Gᵀ * (Eᵀ * eta * E)) - (Qᵀ * eta * E + Eᵀ * eta * Q) := by
          rw [h1, h2]; abel
      _ = 0 := by rw [hc, sub_self]
  have hEt : (Eᵀ)⁻¹ * Eᵀ = 1 := Matrix.nonsing_inv_mul _ (by rw [Matrix.det_transpose]; exact hu)
  calc eta * Ω + Ωᵀ * eta = ((Eᵀ)⁻¹ * Eᵀ) * (eta * Ω + Ωᵀ * eta) * (E * E⁻¹) := by
        rw [hEt, hEEi, Matrix.one_mul, Matrix.mul_one]
    _ = (Eᵀ)⁻¹ * (Eᵀ * (eta * Ω + Ωᵀ * eta) * E) * E⁻¹ := by noncomm_ring
    _ = 0 := by rw [key]; simp

/-- Entrywise antisymmetry `(ηω_μ)_{cd} = -(ηω_μ)_{dc}`. -/
theorem omega0_antisym (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) (z : R4) (μ : Fin 4)
    (c d : Fin 4) :
    ∑ k, eta c k * omega0 e z μ k d = -∑ k, eta d k * omega0 e z μ k c := by
  have h := congrFun (congrFun (omega0_antisym_mat he hdet z μ) c) d
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.zero_apply] at h
  rw [eq_neg_iff_add_eq_zero, ← h]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.transpose_apply, eta_symm d k]
  ring

end Geometry

/-! ### The frame divergence -/

section FrameDiv

variable {e : R4 → Mat}

/-- `∂_μ(e⁻¹) = -e⁻¹(∂_μe)e⁻¹`, entrywise along the coordinate line. -/
theorem hasDerivAt_inv_line (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) (z : R4)
    (μ i j : Fin 4) :
    HasDerivAt (fun s : ℝ => (e (z + s • Pi.single μ 1))⁻¹ i j)
      (-((e z)⁻¹ * fderiv ℝ e z (evec μ) * (e z)⁻¹) i j) 0 := by
  have he2 : ContDiff ℝ 2 e := he.of_le (by norm_cast)
  have hd : Differentiable ℝ e := he.differentiable (by simp)
  have hdi : DifferentiableAt ℝ (fun y => (e y)⁻¹) z := differentiableAt_inv he2 (hdet z).ne'
  set D : Mat := pd (fun y => (e y)⁻¹) μ z
  set E := e z
  set Q := fderiv ℝ e z (evec μ)
  have hu : IsUnit E.det := (hdet z).ne'.isUnit
  have hDi : HasDerivAt (fun s : ℝ => (e (z + s • Pi.single μ 1))⁻¹) D 0 := hasDerivAt_line' μ hdi
  have hE : HasDerivAt (fun s : ℝ => e (z + s • Pi.single μ 1)) Q 0 := hasDerivAt_line' μ (hd z)
  -- differentiate `e⁻¹ e = 1`
  have hprod : ∀ a b, HasDerivAt (fun s : ℝ => ∑ k, (e (z + s • Pi.single μ 1))⁻¹ a k *
      e (z + s • Pi.single μ 1) k b) (∑ k, (D a k * E k b + E⁻¹ a k * Q k b)) 0 := by
    intro a b
    refine HasDerivAt.fun_sum fun k _ => ?_
    have h1 := hasDerivAt_pi.1 (hasDerivAt_pi.1 hDi a) k
    have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 hE k) b
    refine (h1.fun_mul h2).congr_deriv ?_
    simp only [zero_smul, add_zero]
    rfl
  have hconst : ∀ a b, (fun s : ℝ => ∑ k, (e (z + s • Pi.single μ 1))⁻¹ a k *
      e (z + s • Pi.single μ 1) k b) = fun _ => (1 : Mat) a b := by
    intro a b
    funext s
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (hdet _).ne'.isUnit]
  have hzero : D * E + E⁻¹ * Q = 0 := by
    ext a b
    have h := hprod a b
    rw [hconst a b] at h
    have h0 := h.unique (hasDerivAt_const (0 : ℝ) ((1 : Mat) a b))
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    simpa using h0
  have hD : D = -(E⁻¹ * Q * E⁻¹) := by
    have hEEi : E * E⁻¹ = 1 := Matrix.mul_nonsing_inv E hu
    calc D = (D * E + E⁻¹ * Q) * E⁻¹ - E⁻¹ * Q * E⁻¹ := by
          rw [Matrix.add_mul, Matrix.mul_assoc D, hEEi, Matrix.mul_one]; abel
      _ = -(E⁻¹ * Q * E⁻¹) := by rw [hzero, Matrix.zero_mul, zero_sub]
  have h := hasDerivAt_pi.1 (hasDerivAt_pi.1 hDi i) j
  rw [hD] at h
  exact h

/-- **The frame divergence** `∂_μ(v e_b^μ) = v ω_μ^a_b e_a^μ` (`e_b^μ = (e⁻¹)^μ_b`,
`ω_μ = Ω_μ(e, ∂e)` the coframe-derived connection). -/
theorem frame_div (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) (z : R4) (b : Fin 4) :
    ∑ μ, pd (fun y => volume (e y) * (e y)⁻¹ μ b) μ z =
      volume (e z) * ∑ μ, ∑ a, omega0 e z μ a b * (e z)⁻¹ μ a := by
  have he2 : ContDiff ℝ 2 e := he.of_le (by norm_cast)
  have hdi : DifferentiableAt ℝ (fun y => (e y)⁻¹) z := differentiableAt_inv he2 (hdet z).ne'
  have hpd : ∀ μ, pd (fun y => volume (e y) * (e y)⁻¹ μ b) μ z =
      volume (e z) * (∑ a, chr (ginvOf (gF e z)) (dF (gF e) z) a a μ) * (e z)⁻¹ μ b +
        volume (e z) * -((e z)⁻¹ * fderiv ℝ e z (evec μ) * (e z)⁻¹) μ b := by
    intro μ
    have hd : DifferentiableAt ℝ (fun y => volume (e y) * (e y)⁻¹ μ b) z :=
      (differentiableAt_volume he hdet z).mul
        (differentiableAt_pi.1 (differentiableAt_pi.1 hdi μ) b)
    refine pd_eq_of_line' hd ?_
    have h := (hasDerivAt_volume_line he hdet z μ).fun_mul (hasDerivAt_inv_line he hdet z μ μ b)
    refine h.congr_deriv ?_
    simp only [zero_smul, add_zero]
  simp only [hpd]
  have hu : IsUnit (e z).det := (hdet z).ne'.isUnit
  have hR : ∀ μ, ∑ a, omega0 e z μ a b * (e z)⁻¹ μ a =
      (gamMat e z μ * (e z)⁻¹) μ b - ((e z)⁻¹ * fderiv ℝ e z (evec μ) * (e z)⁻¹) μ b := by
    intro μ
    have h1 : ∑ a, omega0 e z μ a b * (e z)⁻¹ μ a = ((e z)⁻¹ * omega0 e z μ) μ b := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    rw [h1, omega0_eq, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.sub_apply, Matrix.mul_assoc]
  simp only [hR]
  have hG : ∑ μ, (gamMat e z μ * (e z)⁻¹) μ b =
      ∑ μ, (∑ a, chr (ginvOf (gF e z)) (dF (gF e) z) a a μ) * (e z)⁻¹ μ b := by
    have hd : Differentiable ℝ e := he.differentiable (by simp)
    simp only [Matrix.mul_apply, gamMat_eq_chr hd, Finset.sum_mul]
    rw [Finset.sum_comm]
  calc ∑ x, ((volume (e z) * ∑ a, chr (ginvOf (gF e z)) (dF (gF e) z) a a x) * (e z)⁻¹ x b +
        volume (e z) * -((e z)⁻¹ * fderiv ℝ e z (evec x) * (e z)⁻¹) x b) =
      volume (e z) * ∑ x, (∑ a, chr (ginvOf (gF e z)) (dF (gF e) z) a a x) * (e z)⁻¹ x b -
        volume (e z) * ∑ x, ((e z)⁻¹ * fderiv ℝ e z (evec x) * (e z)⁻¹) x b := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = volume (e z) * ∑ x, (gamMat e z x * (e z)⁻¹) x b -
        volume (e z) * ∑ x, ((e z)⁻¹ * fderiv ℝ e z (evec x) * (e z)⁻¹) x b := by rw [hG]
    _ = _ := by
        rw [← mul_sub, ← Finset.sum_sub_distrib]

end FrameDiv

/-! ### The Dirac identity -/

section DiracIdentity

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

variable {e : R4 → Mat}

theorem gammaMu_eq (μ : Fin 4) (E : Mat) : gammaMu D μ E = ∑ a, E⁻¹ μ a • D.γ a := rfl

/-- `∂_μ(v γ^μ(e)) = Σ_a ∂_μ(v e_a^μ) γ^a`. -/
theorem pd_vol_gammaMu (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) (z : R4) (μ : Fin 4) :
    pd (fun y => volume (e y) • gammaMu D μ (e y)) μ z =
      ∑ a, pd (fun y => volume (e y) * (e y)⁻¹ μ a) μ z • D.γ a := by
  have he2 : ContDiff ℝ 2 e := he.of_le (by norm_cast)
  have hdi : DifferentiableAt ℝ (fun y => (e y)⁻¹) z := differentiableAt_inv he2 (hdet z).ne'
  have hφ : ∀ a, DifferentiableAt ℝ (fun y => volume (e y) * (e y)⁻¹ μ a) z := fun a =>
    (differentiableAt_volume he hdet z).mul (differentiableAt_pi.1 (differentiableAt_pi.1 hdi μ) a)
  have hfun : (fun y => volume (e y) • gammaMu D μ (e y)) =
      fun y => ∑ a, (volume (e y) * (e y)⁻¹ μ a) • D.γ a := by
    funext y
    rw [gammaMu_eq, Finset.smul_sum]
    simp only [smul_smul]
  rw [hfun]
  have hd : DifferentiableAt ℝ (fun y => ∑ a, (volume (e y) * (e y)⁻¹ μ a) • D.γ a) z :=
    DifferentiableAt.fun_sum fun a _ => (hφ a).smul_const _
  refine pd_eq_of_line' hd ?_
  exact HasDerivAt.fun_sum fun a _ => (hasDerivAt_line' μ (hφ a)).smul_const (D.γ a)

/-- **The Dirac identity of the coframe spin connection**: with the Clifford relations,
`σ(ω) = ¼ω_{ab}γ^aγ^b` and a gauge action commuting with Clifford multiplication,
`Σ_μ (v[σ(ω_μ) + ρ_S(A_μ), γ^μ(e)] + ∂_μ(vγ^μ(e))) = 0` for the coframe-derived connection
`ω_μ = Ω_μ(e, ∂e)` of a smooth coframe field with `det e > 0` and any gauge values `A`. -/
theorem dirac_identity (hcl : ∀ a b, D.γ a * D.γ b + D.γ b * D.γ a = (2 * eta a b) • 1)
    (hσ : ∀ om, D.σ om = sigmaOf D.γ om) (hρ : ∀ A a, D.ρS A * D.γ a = D.γ a * D.ρS A)
    (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) (z : R4) (A : Fin 4 → 𝔄) :
    ∑ μ, (volume (e z) • ((D.σ (omega0 e z μ) + D.ρS (A μ)) * gammaMu D μ (e z) -
        gammaMu D μ (e z) * (D.σ (omega0 e z μ) + D.ρS (A μ))) +
      pd (fun y => volume (e y) • gammaMu D μ (e y)) μ z) = 0 := by
  rw [Finset.sum_add_distrib]
  have hY : ∑ μ, pd (fun y => volume (e y) • gammaMu D μ (e y)) μ z =
      ∑ a, (volume (e z) * ∑ μ, ∑ c, omega0 e z μ c a * (e z)⁻¹ μ c) • D.γ a := by
    simp only [pd_vol_gammaMu D he hdet z]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_smul, frame_div he hdet z a]
  have hcomm : ∀ μ a, (D.σ (omega0 e z μ) + D.ρS (A μ)) * D.γ a -
      D.γ a * (D.σ (omega0 e z μ) + D.ρS (A μ)) = -∑ b, omega0 e z μ a b • D.γ b := by
    intro μ a
    have h1 := sigmaOf_comm D.γ hcl (omega0 e z μ) (omega0_antisym he hdet z μ) a
    rw [← hσ] at h1
    rw [add_mul, mul_add, hρ, ← h1]
    abel
  have hX : ∑ μ, volume (e z) • ((D.σ (omega0 e z μ) + D.ρS (A μ)) * gammaMu D μ (e z) -
        gammaMu D μ (e z) * (D.σ (omega0 e z μ) + D.ρS (A μ))) =
      -∑ b, (volume (e z) * ∑ μ, ∑ a, omega0 e z μ a b * (e z)⁻¹ μ a) • D.γ b := by
    have hμ : ∀ μ, (D.σ (omega0 e z μ) + D.ρS (A μ)) * gammaMu D μ (e z) -
        gammaMu D μ (e z) * (D.σ (omega0 e z μ) + D.ρS (A μ)) =
        ∑ a, (e z)⁻¹ μ a • (-∑ b, omega0 e z μ a b • D.γ b) := by
      intro μ
      rw [gammaMu_eq, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, hcomm]
    simp only [hμ, smul_neg, Finset.sum_neg_distrib, Finset.smul_sum, smul_smul]
    congr 1
    rw [Finset.sum_congr rfl fun μ _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun a _ => ?_
    congr 1
    ring
  rw [hX, hY, neg_add_cancel]

end DiracIdentity

/-! ### Lines in the spinor directions -/

section DiracLines

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

theorem add_smul_zero {M : Type*} [AddCommGroup M] [Module ℝ M] (x : M) (t : ℝ) :
    x + t • (0 : M) = x := by simp

/-- The spinor direction `(0, 0, 0, χ, 0)`. -/
def psiDir (χ : 𝓢) : Field 𝔄 𝓗 𝓢 := (0, 0, 0, χ, 0)

/-- The co-spinor direction `(0, 0, 0, 0, φ)`. -/
def psiBarDir (φ : CoSpinor 𝓢) : Field 𝔄 𝓗 𝓢 := (0, 0, 0, 0, φ)

/-- **The Dirac density along a line on which the coframe, the gauge potential and the Higgs
field are fixed** and the spinor jets move affinely: the derivative is the product rule of the
bilinear Dirac form. -/
theorem hasDerivAt_LDc_line (wp d : FJ 𝔄 𝓗 𝓢) (he : ∀ t : ℝ, (wp + t • d).1.1 = wp.1.1)
    (hH : ∀ t : ℝ, (wp + t • d).1.2.2.1 = wp.1.2.2.1)
    (Ψ' : 𝓢) (hΨ : ∀ t : ℝ, (wp + t • d).1.2.2.2.1 = wp.1.2.2.2.1 + t • Ψ')
    (Ψb' : CoSpinor 𝓢) (hΨb : ∀ t : ℝ, (wp + t • d).1.2.2.2.2 = wp.1.2.2.2.2 + t • Ψb')
    (DΨ' : Fin 4 → 𝓢) (hDΨ : ∀ (t : ℝ) μ, DPsi D (wp + t • d) μ = DPsi D wp μ + t • DΨ' μ)
    (DΨb' : Fin 4 → CoSpinor 𝓢)
    (hDΨb : ∀ (t : ℝ) μ, DPsiBar D (wp + t • d) μ = DPsiBar D wp μ + t • DΨb' μ) :
    HasDerivAt (fun t : ℝ => LDc D (wp + t • d))
      (volume wp.1.1 * (Complex.I / 2 * ∑ μ,
        ((Ψb' (gammaMu D μ wp.1.1 (DPsi D wp μ)) +
            wp.1.2.2.2.2 (gammaMu D μ wp.1.1 (DΨ' μ))) -
          (DΨb' μ (gammaMu D μ wp.1.1 wp.1.2.2.2.1) +
            DPsiBar D wp μ (gammaMu D μ wp.1.1 Ψ'))) -
        (Ψb' (D.yukawa wp.1.2.2.1 wp.1.2.2.2.1) +
          wp.1.2.2.2.2 (D.yukawa wp.1.2.2.1 Ψ'))).re) 0 := by
  unfold LDc
  simp only [he, hH, hΨ, hΨb, hDΨ, hDΨb]
  have hS : ∀ μ, HasDerivAt (fun t : ℝ =>
      (wp.1.2.2.2.2 + t • Ψb') (gammaMu D μ wp.1.1 (DPsi D wp μ + t • DΨ' μ)) -
        (DPsiBar D wp μ + t • DΨb' μ) (gammaMu D μ wp.1.1 (wp.1.2.2.2.1 + t • Ψ')))
      ((Ψb' (gammaMu D μ wp.1.1 (DPsi D wp μ)) + wp.1.2.2.2.2 (gammaMu D μ wp.1.1 (DΨ' μ))) -
        (DΨb' μ (gammaMu D μ wp.1.1 wp.1.2.2.2.1) +
          DPsiBar D wp μ (gammaMu D μ wp.1.1 Ψ'))) 0 := by
    intro μ
    have g1 := ((gammaMu D μ wp.1.1).hasFDerivAt).comp_hasDerivAt (0 : ℝ)
      (hasDerivAt_affine (DPsi D wp μ) (DΨ' μ))
    have g2 := ((gammaMu D μ wp.1.1).hasFDerivAt).comp_hasDerivAt (0 : ℝ)
      (hasDerivAt_affine wp.1.2.2.2.1 Ψ')
    have h1 := (hasDerivAt_affine wp.1.2.2.2.2 Ψb').clm_apply g1
    have h2 := (hasDerivAt_affine (DPsiBar D wp μ) (DΨb' μ)).clm_apply g2
    refine (h1.sub h2).congr_deriv ?_
    simp
  have hY := (hasDerivAt_affine wp.1.2.2.2.2 Ψb').clm_apply
    (((D.yukawa wp.1.2.2.1).hasFDerivAt).comp_hasDerivAt (0 : ℝ)
      (hasDerivAt_affine wp.1.2.2.2.1 Ψ'))
  have hΦ := ((HasDerivAt.fun_sum (u := Finset.univ) fun μ _ => hS μ).const_mul
    (Complex.I / 2)).sub hY
  have hre := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hΦ
  refine (hre.const_mul (volume wp.1.1)).congr_deriv ?_
  simp

end DiracLines

/-! ### Spinor partials of `L₀` -/

section SpinorPartials

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

/-- Along a line fixing the bosonic jets, `L₀` moves only through its Dirac sector. -/
theorem hasDerivAt_L0_of_bos (wp d : FJ 𝔄 𝓗 𝓢) (he : ∀ t : ℝ, (wp + t • d).1.1 = wp.1.1)
    (hA : ∀ t : ℝ, (wp + t • d).1.2.1 = wp.1.2.1) (hH : ∀ t : ℝ, (wp + t • d).1.2.2.1 = wp.1.2.2.1)
    (hp1 : ∀ (t : ℝ) μ, ((wp + t • d).2 μ).1 = (wp.2 μ).1)
    (hp2 : ∀ (t : ℝ) μ, ((wp + t • d).2 μ).2.1 = (wp.2 μ).2.1)
    (hp3 : ∀ (t : ℝ) μ, ((wp + t • d).2 μ).2.2.1 = (wp.2 μ).2.2.1) {f' : ℝ}
    (hD : HasDerivAt (fun t : ℝ => LDc D (wp + t • d)) f' 0) :
    HasDerivAt (fun t : ℝ => L0 D (wp + t • d)) f' 0 := by
  have hc : ∀ t : ℝ, Lgc D (wp + t • d) + LYMc D (wp + t • d) + LHc D (wp + t • d) =
      Lgc D wp + LYMc D wp + LHc D wp := by
    intro t
    have hF : ∀ μ ν, FA (wp + t • d) μ ν = FA wp μ ν := fun μ ν => by
      unfold FA; rw [hA, hp2, hp2]
    have hK : ∀ μ, KH D (wp + t • d) μ = KH D wp μ := fun μ => by
      unfold KH; rw [hA, hH, hp3]
    have hpe : (fun μ => ((wp + t • d).2 μ).1) = fun μ => (wp.2 μ).1 := funext (hp1 t)
    unfold Lgc LYMc LHc
    simp only [he, hpe, hF, hK, hH]
  have hfun : (fun t : ℝ => L0 D (wp + t • d)) =
      fun t => (Lgc D wp + LYMc D wp + LHc D wp) + LDc D (wp + t • d) := by
    funext t
    rw [L0_eq, ← hc t]
  rw [hfun]
  simpa using hD.const_add (Lgc D wp + LYMc D wp + LHc D wp)

/-- The spinor jet direction `[α = μ] v`. -/
def dJS {V : Type*} [Zero V] (v : V) (μ α : Fin 4) : V := if α = μ then v else 0

variable (wp : FJ 𝔄 𝓗 𝓢) (t : ℝ)

theorem single_apply_field (μ α : Fin 4) (v : Field 𝔄 𝓗 𝓢) :
    (Pi.single μ v : Fin 4 → Field 𝔄 𝓗 𝓢) α = if α = μ then v else 0 := Pi.single_apply _ _ _

section Values

variable (φ : CoSpinor 𝓢) (χ : 𝓢)

theorem pbl_e : (wp + t • ((psiBarDir φ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢))).1.1 =
    wp.1.1 := by
  simp only [psiBarDir, Prod.fst_add, Prod.smul_fst]; exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem pbl_A : (wp + t • ((psiBarDir φ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢))).1.2.1 =
    wp.1.2.1 := by
  simp only [psiBarDir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem pbl_H : (wp + t • ((psiBarDir φ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢))).1.2.2.1 =
    wp.1.2.2.1 := by
  simp only [psiBarDir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem pbl_Ψ : (wp + t • ((psiBarDir φ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢))).1.2.2.2.1 =
    wp.1.2.2.2.1 := by
  simp only [psiBarDir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem pbl_Ψb : (wp + t • ((psiBarDir φ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢))).1.2.2.2.2 =
    wp.1.2.2.2.2 + t • φ := by
  simp only [psiBarDir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]

theorem pbl_p : (wp + t • ((psiBarDir φ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢))).2 = wp.2 := by
  simp only [Prod.snd_add, Prod.smul_snd]; exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem psl_e : (wp + t • ((psiDir χ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢))).1.1 =
    wp.1.1 := by
  simp only [psiDir, Prod.fst_add, Prod.smul_fst]; exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem psl_A : (wp + t • ((psiDir χ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢))).1.2.1 =
    wp.1.2.1 := by
  simp only [psiDir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem psl_H : (wp + t • ((psiDir χ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢))).1.2.2.1 =
    wp.1.2.2.1 := by
  simp only [psiDir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem psl_Ψ : (wp + t • ((psiDir χ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢))).1.2.2.2.1 =
    wp.1.2.2.2.1 + t • χ := by
  simp only [psiDir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]

theorem psl_Ψb : (wp + t • ((psiDir χ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢))).1.2.2.2.2 =
    wp.1.2.2.2.2 := by
  simp only [psiDir, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem psl_p : (wp + t • ((psiDir χ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢))).2 = wp.2 := by
  simp only [Prod.snd_add, Prod.smul_snd]; exact (congrArg _ (smul_zero t)).trans (add_zero _)

end Values

section Jets

variable (μ : Fin 4) (φ : CoSpinor 𝓢) (χ : 𝓢)

theorem jl_w (v : Field 𝔄 𝓗 𝓢) :
    (wp + t • ((0 : Field 𝔄 𝓗 𝓢), (Pi.single μ v : Fin 4 → Field 𝔄 𝓗 𝓢))).1 = wp.1 := by
  simp only [Prod.fst_add, Prod.smul_fst]; exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem jl_p (v : Field 𝔄 𝓗 𝓢) (α : Fin 4) :
    (wp + t • ((0 : Field 𝔄 𝓗 𝓢), (Pi.single μ v : Fin 4 → Field 𝔄 𝓗 𝓢))).2 α =
      wp.2 α + t • (if α = μ then v else 0) := by
  simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, single_apply_field]

theorem jlb_p (α : Fin 4) :
    (wp + t • ((0 : Field 𝔄 𝓗 𝓢), (Pi.single μ (psiBarDir φ) : Fin 4 → Field 𝔄 𝓗 𝓢))).2 α =
      ((wp.2 α).1, (wp.2 α).2.1, (wp.2 α).2.2.1, (wp.2 α).2.2.2.1,
        (wp.2 α).2.2.2.2 + t • dJS φ μ α) := by
  rw [jl_p]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  all_goals
    by_cases h : α = μ
    · subst h
      simp only [if_true, dJS, psiBarDir, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd]
      try exact (congrArg _ (smul_zero t)).trans (add_zero _)
    · simp only [h, if_false, dJS, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
      first | rfl | exact (congrArg _ (smul_zero t)).trans (add_zero _)

theorem jls_p (α : Fin 4) :
    (wp + t • ((0 : Field 𝔄 𝓗 𝓢), (Pi.single μ (psiDir χ) : Fin 4 → Field 𝔄 𝓗 𝓢))).2 α =
      ((wp.2 α).1, (wp.2 α).2.1, (wp.2 α).2.2.1, (wp.2 α).2.2.2.1 + t • dJS χ μ α,
        (wp.2 α).2.2.2.2) := by
  rw [jl_p]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  all_goals
    by_cases h : α = μ
    · subst h
      simp only [if_true, dJS, psiDir, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd]
      try exact (congrArg _ (smul_zero t)).trans (add_zero _)
    · simp only [h, if_false, dJS, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
      first | rfl | exact (congrArg _ (smul_zero t)).trans (add_zero _)

end Jets

end SpinorPartials

/-! ### The four spinor partials -/

section SpinorFderiv

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

/-- The connection operator `M_μ = -ρ_S(A_μ) - σ(ω_μ)` acting on co-spinors. -/
def Mop (wp : FJ 𝔄 𝓗 𝓢) (μ : Fin 4) : Spin 𝓢 := -D.ρS (wp.1.2.1 μ) - D.σ (omC wp μ)

/-- `∂L₀/∂Ψ̄[φ] = v Re{(i/2)[φγ^μ∇_μΨ - φM_μγ^μΨ] - φ𝓜Ψ}`. -/
theorem fderiv_L0_psiBar {wp : FJ 𝔄 𝓗 𝓢} (h : wp.1.1.det ≠ 0) (φ : CoSpinor 𝓢) :
    fderiv ℝ (L0 D) wp ((psiBarDir φ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) =
      volume wp.1.1 * (Complex.I / 2 * ∑ μ, (φ (gammaMu D μ wp.1.1 (DPsi D wp μ)) -
        φ (Mop D wp μ (gammaMu D μ wp.1.1 wp.1.2.2.2.1))) -
        φ (D.yukawa wp.1.2.2.1 wp.1.2.2.2.1)).re := by
  set d : FJ 𝔄 𝓗 𝓢 := ((psiBarDir φ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) with hd
  have he : ∀ t : ℝ, (wp + t • d).1.1 = wp.1.1 := fun t => pbl_e wp t φ
  have hA : ∀ t : ℝ, (wp + t • d).1.2.1 = wp.1.2.1 := fun t => pbl_A wp t φ
  have hH : ∀ t : ℝ, (wp + t • d).1.2.2.1 = wp.1.2.2.1 := fun t => pbl_H wp t φ
  have hp : ∀ t : ℝ, (wp + t • d).2 = wp.2 := fun t => pbl_p wp t φ
  have hpe : ∀ t : ℝ, (fun l => ((wp + t • d).2 l).1) = fun l => (wp.2 l).1 := fun t => by
    rw [hp]
  have hl := hasDerivAt_L0_of_bos D wp d he hA hH (fun t μ => by rw [hp]) (fun t μ => by rw [hp])
    (fun t μ => by rw [hp]) (hasDerivAt_LDc_line D wp d he hH 0
      (fun t => by rw [pbl_Ψ wp t φ]; simp) φ (fun t => pbl_Ψb wp t φ) 0
      (fun t μ => by unfold DPsi omC; rw [hA, he t, pbl_Ψ wp t φ, hpe, hp]; simp)
      (fun μ => φ.comp (Mop D wp μ))
      (fun t μ => by
        unfold DPsiBar Mop omC
        rw [hA, he t, pbl_Ψb wp t φ, hpe, hp, ContinuousLinearMap.add_comp,
          ContinuousLinearMap.smul_comp]
        abel))
  refine (fderiv_apply_of_line (differentiableAt_L0 D h) hl).trans ?_
  simp

/-- `∂L₀/∂Ψ[χ] = v Re{(i/2)[Ψ̄γ^μ(σ(ω_μ) + ρ_S(A_μ))χ - (∇_μΨ̄)γ^μχ] - Ψ̄𝓜χ}`. -/
theorem fderiv_L0_psi {wp : FJ 𝔄 𝓗 𝓢} (h : wp.1.1.det ≠ 0) (χ : 𝓢) :
    fderiv ℝ (L0 D) wp ((psiDir χ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) =
      volume wp.1.1 * (Complex.I / 2 * ∑ μ, (wp.1.2.2.2.2 (gammaMu D μ wp.1.1
          ((D.σ (omC wp μ) + D.ρS (wp.1.2.1 μ)) χ)) -
        DPsiBar D wp μ (gammaMu D μ wp.1.1 χ)) -
        wp.1.2.2.2.2 (D.yukawa wp.1.2.2.1 χ)).re := by
  set d : FJ 𝔄 𝓗 𝓢 := ((psiDir χ : Field 𝔄 𝓗 𝓢), (0 : Fin 4 → Field 𝔄 𝓗 𝓢)) with hd
  have he : ∀ t : ℝ, (wp + t • d).1.1 = wp.1.1 := fun t => psl_e wp t χ
  have hA : ∀ t : ℝ, (wp + t • d).1.2.1 = wp.1.2.1 := fun t => psl_A wp t χ
  have hH : ∀ t : ℝ, (wp + t • d).1.2.2.1 = wp.1.2.2.1 := fun t => psl_H wp t χ
  have hp : ∀ t : ℝ, (wp + t • d).2 = wp.2 := fun t => psl_p wp t χ
  have hpe : ∀ t : ℝ, (fun l => ((wp + t • d).2 l).1) = fun l => (wp.2 l).1 := fun t => by
    rw [hp]
  have hl := hasDerivAt_L0_of_bos D wp d he hA hH (fun t μ => by rw [hp]) (fun t μ => by rw [hp])
    (fun t μ => by rw [hp]) (hasDerivAt_LDc_line D wp d he hH χ (fun t => psl_Ψ wp t χ) 0
      (fun t => by
        rw [psl_Ψb wp t χ]; exact ((congrArg _ (smul_zero t)).trans (add_zero _)).symm)
      (fun μ => (D.σ (omC wp μ) + D.ρS (wp.1.2.1 μ)) χ)
      (fun t μ => by
        unfold DPsi omC
        rw [hA, he t, psl_Ψ wp t χ, hpe, hp, map_add, map_smul]
        simp only [ContinuousLinearMap.add_apply]
        abel)
      0
      (fun t μ => by
        unfold DPsiBar omC; rw [hA, he t, psl_Ψb wp t χ, hpe, hp]
        exact ((congrArg _ (smul_zero t)).trans (add_zero _)).symm))
  refine (fderiv_apply_of_line (differentiableAt_L0 D h) hl).trans ?_
  simp

/-- `∂L₀/∂(∂_μΨ̄)[φ] = -v Re{(i/2)φγ^μΨ}`. -/
theorem fderiv_L0_dpsiBar {wp : FJ 𝔄 𝓗 𝓢} (h : wp.1.1.det ≠ 0) (φ : CoSpinor 𝓢) (μ : Fin 4) :
    fderiv ℝ (L0 D) wp ((0 : Field 𝔄 𝓗 𝓢), Pi.single μ (psiBarDir φ : Field 𝔄 𝓗 𝓢)) =
      -(volume wp.1.1 * (Complex.I / 2 * φ (gammaMu D μ wp.1.1 wp.1.2.2.2.1)).re) := by
  set d : FJ 𝔄 𝓗 𝓢 := ((0 : Field 𝔄 𝓗 𝓢), Pi.single μ (psiBarDir φ : Field 𝔄 𝓗 𝓢)) with hd
  have hw : ∀ t : ℝ, (wp + t • d).1 = wp.1 := fun t => jl_w wp t μ _
  have hpq : ∀ (t : ℝ) α, (wp + t • d).2 α = ((wp.2 α).1, (wp.2 α).2.1, (wp.2 α).2.2.1,
      (wp.2 α).2.2.2.1, (wp.2 α).2.2.2.2 + t • dJS φ μ α) := fun t α => jlb_p wp t μ φ α
  have hpe : ∀ t : ℝ, (fun l => ((wp + t • d).2 l).1) = fun l => (wp.2 l).1 := fun t => by
    funext l; rw [hpq]
  have hl := hasDerivAt_L0_of_bos D wp d (fun t => by rw [hw]) (fun t => by rw [hw])
    (fun t => by rw [hw]) (fun t α => by rw [hpq]) (fun t α => by rw [hpq])
    (fun t α => by rw [hpq])
    (hasDerivAt_LDc_line D wp d (fun t => by rw [hw]) (fun t => by rw [hw]) 0
      (fun t => by rw [hw]; exact ((congrArg _ (smul_zero t)).trans (add_zero _)).symm) 0 (fun t => by rw [hw]; exact ((congrArg _ (smul_zero t)).trans (add_zero _)).symm) 0
      (fun t α => by unfold DPsi omC; rw [hw, hpe, hpq]; simp)
      (fun α => dJS φ μ α)
      (fun t α => by unfold DPsiBar omC; rw [hw, hpe, hpq]; abel))
  refine (fderiv_apply_of_line (differentiableAt_L0 D h) hl).trans ?_
  simp only [ContinuousLinearMap.zero_apply, map_zero, add_zero, zero_add, sub_zero]
  rw [Finset.sum_eq_single μ (fun α _ hα => by simp [dJS, hα]) (by simp)]
  simp [dJS, mul_neg]

/-- `∂L₀/∂(∂_μΨ)[χ] = v Re{(i/2)Ψ̄γ^μχ}`. -/
theorem fderiv_L0_dpsi {wp : FJ 𝔄 𝓗 𝓢} (h : wp.1.1.det ≠ 0) (χ : 𝓢) (μ : Fin 4) :
    fderiv ℝ (L0 D) wp ((0 : Field 𝔄 𝓗 𝓢), Pi.single μ (psiDir χ : Field 𝔄 𝓗 𝓢)) =
      volume wp.1.1 * (Complex.I / 2 * wp.1.2.2.2.2 (gammaMu D μ wp.1.1 χ)).re := by
  set d : FJ 𝔄 𝓗 𝓢 := ((0 : Field 𝔄 𝓗 𝓢), Pi.single μ (psiDir χ : Field 𝔄 𝓗 𝓢)) with hd
  have hw : ∀ t : ℝ, (wp + t • d).1 = wp.1 := fun t => jl_w wp t μ _
  have hpq : ∀ (t : ℝ) α, (wp + t • d).2 α = ((wp.2 α).1, (wp.2 α).2.1, (wp.2 α).2.2.1,
      (wp.2 α).2.2.2.1 + t • dJS χ μ α, (wp.2 α).2.2.2.2) := fun t α => jls_p wp t μ χ α
  have hpe : ∀ t : ℝ, (fun l => ((wp + t • d).2 l).1) = fun l => (wp.2 l).1 := fun t => by
    funext l; rw [hpq]
  have hl := hasDerivAt_L0_of_bos D wp d (fun t => by rw [hw]) (fun t => by rw [hw])
    (fun t => by rw [hw]) (fun t α => by rw [hpq]) (fun t α => by rw [hpq])
    (fun t α => by rw [hpq])
    (hasDerivAt_LDc_line D wp d (fun t => by rw [hw]) (fun t => by rw [hw]) 0
      (fun t => by rw [hw]; exact ((congrArg _ (smul_zero t)).trans (add_zero _)).symm) 0 (fun t => by rw [hw]; exact ((congrArg _ (smul_zero t)).trans (add_zero _)).symm)
      (fun α => dJS χ μ α)
      (fun t α => by unfold DPsi omC; rw [hw, hpe, hpq]; abel) 0
      (fun t α => by unfold DPsiBar omC; rw [hw, hpe, hpq]; exact ((congrArg _ (smul_zero t)).trans (add_zero _)).symm))
  refine (fderiv_apply_of_line (differentiableAt_L0 D h) hl).trans ?_
  simp only [ContinuousLinearMap.zero_apply, map_zero, add_zero, zero_add, sub_zero]
  rw [Finset.sum_eq_single μ (fun α _ hα => by simp [dJS, hα]) (by simp)]
  simp [dJS]

end SpinorFderiv

/-! ### The Dirac Euler rows -/

section DiracRows

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

theorem pd_clm_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : R4 → E →L[ℝ] F} {u : R4 → E} {z : R4}
    (hG : DifferentiableAt ℝ G z) (hu : DifferentiableAt ℝ u z) (μ : Fin 4) :
    pd (fun y => G y (u y)) μ z = pd G μ z (u z) + G z (pd u μ z) := by
  unfold SobolevOpen.pd
  rw [fderiv_clm_apply hG hu]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  rw [add_comm]

/-- The projections of a native field. -/
def fstL : Field 𝔄 𝓗 𝓢 →L[ℝ] Mat := ContinuousLinearMap.fst ℝ Mat _

def psiL : Field 𝔄 𝓗 𝓢 →L[ℝ] 𝓢 :=
  (ContinuousLinearMap.fst ℝ 𝓢 (CoSpinor 𝓢)).comp ((ContinuousLinearMap.snd ℝ 𝓗 _).comp
    ((ContinuousLinearMap.snd ℝ (Fin 4 → 𝔄) _).comp (ContinuousLinearMap.snd ℝ Mat _)))

def psiBarL : Field 𝔄 𝓗 𝓢 →L[ℝ] CoSpinor 𝓢 :=
  (ContinuousLinearMap.snd ℝ 𝓢 (CoSpinor 𝓢)).comp ((ContinuousLinearMap.snd ℝ 𝓗 _).comp
    ((ContinuousLinearMap.snd ℝ (Fin 4 → 𝔄) _).comp (ContinuousLinearMap.snd ℝ Mat _)))

variable {Y : R4 → Field 𝔄 𝓗 𝓢}

theorem jet1_e (hY : Differentiable ℝ Y) (z : R4) (μ : Fin 4) :
    ((jet1 Y z).2 μ).1 = fderiv ℝ (eF Y) z (evec μ) := by
  have h := pd_clm (fstL (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)) (hY z) μ
  exact h.symm

theorem jet1_psi (hY : Differentiable ℝ Y) (z : R4) (μ : Fin 4) :
    ((jet1 Y z).2 μ).2.2.2.1 = pd (fun y => (Y y).2.2.2.1) μ z := by
  have h := pd_clm (psiL (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)) (hY z) μ
  exact h.symm

theorem jet1_psiBar (hY : Differentiable ℝ Y) (z : R4) (μ : Fin 4) :
    ((jet1 Y z).2 μ).2.2.2.2 = pd (fun y => (Y y).2.2.2.2) μ z := by
  have h := pd_clm (psiBarL (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)) (hY z) μ
  exact h.symm

theorem omC_jet1 (hY : Differentiable ℝ Y) (z : R4) (μ : Fin 4) :
    omC (jet1 Y z) μ = omega0 (eF Y) z μ := by
  unfold omC omega0
  congr 1
  funext l
  exact jet1_e hY z l

/-- The operator field `G_μ = v(e) γ^μ(e)`. -/
def Gfield (Y : R4 → Field 𝔄 𝓗 𝓢) (μ : Fin 4) (y : R4) : Spin 𝓢 :=
  volume (eF Y y) • gammaMu D μ (eF Y y)

theorem differentiableAt_Gfield (hY : ContDiff ℝ ∞ Y) (hdet : ∀ z, 0 < ((Y z).1).det) (z : R4)
    (μ : Fin 4) : DifferentiableAt ℝ (Gfield D Y μ) z := by
  have he : ContDiff ℝ ∞ (eF Y) := contDiff_fst.comp hY
  have hdet' : ∀ z, 0 < (eF Y z).det := hdet
  have he2 : ContDiff ℝ 2 (eF Y) := he.of_le (by norm_cast)
  have hdi := differentiableAt_inv he2 (hdet' z).ne'
  unfold Gfield
  simp only [gammaMu_eq, Finset.smul_sum]
  refine DifferentiableAt.fun_sum fun a _ => ?_
  refine (differentiableAt_volume he hdet' z).smul ?_
  exact (differentiableAt_pi.1 (differentiableAt_pi.1 hdi μ) a).smul_const _

/-- The real functional `x ↦ Re((i/2) φ(x))`. -/
def reHalfI (φ : CoSpinor 𝓢) : 𝓢 →L[ℝ] ℝ :=
  Complex.reCLM.comp ((ContinuousLinearMap.mul ℝ ℂ (Complex.I / 2)).comp φ)

theorem reHalfI_apply (φ : CoSpinor 𝓢) (x : 𝓢) : reHalfI φ x = (Complex.I / 2 * φ x).re := rfl

/-- **The co-spinor Euler row of the native continuum Lagrangian** (bridge step P3, Dirac
sector): for a smooth native field with `det e > 0`, the Clifford relations,
`σ(ω) = ¼ω_{ab}γ^aγ^b` and a gauge action commuting with Clifford multiplication,
`𝓔₀(Y)(z)[(0, 0, 0, 0, φ)] = v(e) Re{i φ(γ^μ∇_μΨ) - φ(𝓜_𝐘(H)Ψ)}` for every co-spinor
direction `φ`; i.e. the `Ψ̄`-row is `v(e)` times the Dirac residual `iγ^μ∇_μΨ - 𝓜Ψ` paired with
`φ` (`∇_μΨ = ∂_μΨ + (σ(ω_μ) + ρ_S(A_μ))Ψ`, `ω = Ω(e, ∂e)`). -/
theorem psibar_euler_row (hcl : ∀ a b, D.γ a * D.γ b + D.γ b * D.γ a = (2 * eta a b) • 1)
    (hσ : ∀ om, D.σ om = sigmaOf D.γ om) (hρ : ∀ A a, D.ρS A * D.γ a = D.γ a * D.ρS A)
    (hY : ContDiff ℝ ∞ Y) (hdet : ∀ z, 0 < ((Y z).1).det) (z : R4) (φ : CoSpinor 𝓢) :
    contEuler (L0 D) Y z (psiBarDir φ) =
      volume (Y z).1 * (Complex.I * φ (∑ μ, gammaMu D μ (Y z).1 (DPsi D (jet1 Y z) μ)) -
        φ (D.yukawa (Y z).2.2.1 (Y z).2.2.2.1)).re := by
  have hYd : Differentiable ℝ Y := hY.differentiable (by simp)
  have he : ContDiff ℝ ∞ (eF Y) := contDiff_fst.comp hY
  have hdet' : ∀ z, 0 < (eF Y z).det := hdet
  have hJU : ∀ y, jet1 Y y ∈ (chartF : Set (FJ 𝔄 𝓗 𝓢)) := fun y => (hdet y).ne'
  have hE := contEuler_apply (L := L0 D) isOpen_chartF (contDiffOn_L0 D) hY hJU z
    (psiBarDir φ : Field 𝔄 𝓗 𝓢)
  refine hE.trans ?_
  have h1 := fderiv_L0_psiBar D (wp := jet1 Y z) (hdet z).ne' φ
  have hΨd : DifferentiableAt ℝ (fun y => (Y y).2.2.2.1) z :=
    ((psiL (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)).differentiableAt).comp z (hYd z)
  have hpt : ∀ μ, (fun z' => fderiv ℝ (L0 D) (jet1 Y z') ((0 : Field 𝔄 𝓗 𝓢),
      Pi.single μ (psiBarDir φ : Field 𝔄 𝓗 𝓢))) =
      fun z' => -(reHalfI φ (Gfield D Y μ z' ((Y z').2.2.2.1))) := by
    intro μ
    funext z'
    rw [fderiv_L0_dpsiBar D (wp := jet1 Y z') (hdet z').ne' φ μ, reHalfI_apply]
    unfold Gfield
    simp only [ContinuousLinearMap.smul_apply, map_smul, Complex.real_smul]
    congr 1
    show volume (Y z').1 * _ = _
    rw [← Complex.re_ofReal_mul]
    congr 1
    simp only [jet1_fst, eF]
    ring
  have hdiv : ∑ μ, pd (fun z' => fderiv ℝ (L0 D) (jet1 Y z') ((0 : Field 𝔄 𝓗 𝓢),
      Pi.single μ (psiBarDir φ : Field 𝔄 𝓗 𝓢))) μ z =
      -reHalfI φ (∑ μ, (pd (Gfield D Y μ) μ z ((Y z).2.2.2.1) +
        Gfield D Y μ z (pd (fun y => (Y y).2.2.2.1) μ z))) := by
    simp only [hpt]
    rw [map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have hd : DifferentiableAt ℝ (fun z' => Gfield D Y μ z' ((Y z').2.2.2.1)) z :=
      (differentiableAt_Gfield D hY hdet z μ).clm_apply hΨd
    rw [show (fun z' => -(reHalfI φ (Gfield D Y μ z' ((Y z').2.2.2.1)))) =
      fun z' => (-reHalfI φ) (Gfield D Y μ z' ((Y z').2.2.2.1)) from rfl]
    rw [pd_clm (-reHalfI φ) hd μ, pd_clm_apply (differentiableAt_Gfield D hY hdet z μ) hΨd μ]
    rfl
  refine (congrArg₂ (· - ·) h1 hdiv).trans ?_
  -- the Dirac identity applied to `Ψ`
  have hid := dirac_identity D hcl hσ hρ he hdet' z (Y z).2.1
  have hidΨ := congrArg (fun T : Spin 𝓢 => T ((Y z).2.2.2.1)) hid
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.zero_apply] at hidΨ
  -- rewrite all jets in terms of the fields
  simp only [jet1_fst, volume_eF]
  -- notation
  set v := volume (eF Y z) with hv
  set Ψ := (Y z).2.2.2.1 with hΨ
  set S : Fin 4 → Spin 𝓢 := fun μ => D.σ (omega0 (eF Y) z μ) + D.ρS ((Y z).2.1 μ) with hS
  set γm : Fin 4 → Spin 𝓢 := fun μ => gammaMu D μ (eF Y z) with hγm
  set dΨ : Fin 4 → 𝓢 := fun μ => pd (fun y => (Y y).2.2.2.1) μ z with hdΨ
  have hDΨ : ∀ μ, DPsi D (jet1 Y z) μ = S μ Ψ + dΨ μ := by
    intro μ
    unfold DPsi
    rw [omC_jet1 hYd, jet1_psi hYd]
    rfl
  have hM : ∀ μ, Mop D (jet1 Y z) μ = -S μ := by
    intro μ
    unfold Mop
    rw [omC_jet1 hYd, hS]
    simp only [jet1_fst, neg_add_rev]
    abel
  have hG : ∀ μ, pd (Gfield D Y μ) μ z = pd (fun y => volume (eF Y y) • gammaMu D μ (eF Y y)) μ z :=
    fun μ => rfl
  have hG0 : ∀ μ (x : 𝓢), Gfield D Y μ z x = v • γm μ x := fun μ x => rfl
  have hγ : gammaMu D = fun μ E => gammaMu D μ E := rfl
  -- the Dirac identity on `Ψ`
  have hPG : ∑ μ, pd (Gfield D Y μ) μ z Ψ = -∑ μ, v • (S μ (γm μ Ψ) - γm μ (S μ Ψ)) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    simp only [hG]
    rw [← hidΨ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.mul_apply]
    rfl
  -- the vector identity
  have hvec : v • ∑ μ, (γm μ (DPsi D (jet1 Y z) μ) - Mop D (jet1 Y z) μ (γm μ Ψ)) +
      ∑ μ, (pd (Gfield D Y μ) μ z Ψ + Gfield D Y μ z (dΨ μ)) =
      (2 * v) • ∑ μ, γm μ (DPsi D (jet1 Y z) μ) := by
    rw [Finset.sum_add_distrib, hPG]
    simp only [hDΨ, hM, hG0, Finset.smul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [map_add, ContinuousLinearMap.neg_apply]
    module
  have hγz : ∀ μ, gammaMu D μ (Y z).1 = γm μ := fun μ => rfl
  simp only [hγz]
  rw [reHalfI_apply]
  have hφ : φ (v • ∑ μ, (γm μ (DPsi D (jet1 Y z) μ) - Mop D (jet1 Y z) μ (γm μ Ψ)) +
      ∑ μ, (pd (Gfield D Y μ) μ z Ψ + Gfield D Y μ z (dΨ μ))) =
      ((2 * v : ℝ) : ℂ) * φ (∑ μ, γm μ (DPsi D (jet1 Y z) μ)) := by
    rw [hvec, map_smul, Complex.real_smul]
  rw [map_add, map_smul, Complex.real_smul] at hφ
  have hsum : ∑ μ, (φ (γm μ (DPsi D (jet1 Y z) μ)) - φ (Mop D (jet1 Y z) μ (γm μ Ψ))) =
      φ (∑ μ, (γm μ (DPsi D (jet1 Y z) μ) - Mop D (jet1 Y z) μ (γm μ Ψ))) := by
    rw [map_sum]; simp only [map_sub]
  rw [hsum]
  set a := φ (∑ μ, (γm μ (DPsi D (jet1 Y z) μ) - Mop D (jet1 Y z) μ (γm μ Ψ)))
  set b := φ (∑ μ, (pd (Gfield D Y μ) μ z Ψ + Gfield D Y μ z (dΨ μ)))
  set c := φ (∑ μ, γm μ (DPsi D (jet1 Y z) μ))
  set y := φ (D.yukawa (Y z).2.2.1 Ψ)
  have hb : b = ((2 * v : ℝ) : ℂ) * c - (v : ℂ) * a := by rw [← hφ]; ring
  rw [hb]
  simp only [Complex.sub_re, Complex.mul_re, Complex.div_re, Complex.div_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.sub_im]
  norm_num [Complex.normSq_apply]
  try ring

/-- The real functional `w ↦ Re((i/2) w)` on `ℂ`. -/
def reHalfIC : ℂ →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ (Complex.I / 2))

theorem reHalfIC_apply (w : ℂ) : reHalfIC w = (Complex.I / 2 * w).re := rfl

/-- **The spinor Euler row of the native continuum Lagrangian** (bridge step P3, Dirac
sector): under the hypotheses of `psibar_euler_row`, for every spinor direction `χ`,
`𝓔₀(Y)(z)[(0, 0, 0, χ, 0)] = -v(e) Re{i (∇_μΨ̄)γ^μχ + Ψ̄𝓜_𝐘(H)χ}`, i.e. the `Ψ`-row is
`-v(e)` times the dual Dirac residual `i(∇_μΨ̄)γ^μ + Ψ̄𝓜` applied to `χ`
(`∇_μΨ̄ = ∂_μΨ̄ - Ψ̄(ρ_S(A_μ) + σ(ω_μ))`). -/
theorem psi_euler_row (hcl : ∀ a b, D.γ a * D.γ b + D.γ b * D.γ a = (2 * eta a b) • 1)
    (hσ : ∀ om, D.σ om = sigmaOf D.γ om) (hρ : ∀ A a, D.ρS A * D.γ a = D.γ a * D.ρS A)
    (hY : ContDiff ℝ ∞ Y) (hdet : ∀ z, 0 < ((Y z).1).det) (z : R4) (χ : 𝓢) :
    contEuler (L0 D) Y z (psiDir χ) =
      -(volume (Y z).1 * (Complex.I * ∑ μ, DPsiBar D (jet1 Y z) μ (gammaMu D μ (Y z).1 χ) +
        (Y z).2.2.2.2 (D.yukawa (Y z).2.2.1 χ)).re) := by
  have hYd : Differentiable ℝ Y := hY.differentiable (by simp)
  have he : ContDiff ℝ ∞ (eF Y) := contDiff_fst.comp hY
  have hdet' : ∀ z, 0 < (eF Y z).det := hdet
  have hJU : ∀ y, jet1 Y y ∈ (chartF : Set (FJ 𝔄 𝓗 𝓢)) := fun y => (hdet y).ne'
  have hE := contEuler_apply (L := L0 D) isOpen_chartF (contDiffOn_L0 D) hY hJU z
    (psiDir χ : Field 𝔄 𝓗 𝓢)
  refine hE.trans ?_
  have h1 := fderiv_L0_psi D (wp := jet1 Y z) (hdet z).ne' χ
  have hΨbd : DifferentiableAt ℝ (fun y => (Y y).2.2.2.2) z :=
    ((psiBarL (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)).differentiableAt).comp z (hYd z)
  have hGχ : ∀ μ, DifferentiableAt ℝ (fun y => Gfield D Y μ y χ) z := fun μ =>
    (differentiableAt_Gfield D hY hdet z μ).clm_apply (differentiableAt_const χ)
  have hpt : ∀ μ, (fun z' => fderiv ℝ (L0 D) (jet1 Y z') ((0 : Field 𝔄 𝓗 𝓢),
      Pi.single μ (psiDir χ : Field 𝔄 𝓗 𝓢))) =
      fun z' => reHalfIC ((Y z').2.2.2.2 (Gfield D Y μ z' χ)) := by
    intro μ
    funext z'
    rw [fderiv_L0_dpsi D (wp := jet1 Y z') (hdet z').ne' χ μ, reHalfIC_apply]
    unfold Gfield
    simp only [ContinuousLinearMap.smul_apply, map_smul, Complex.real_smul]
    rw [← Complex.re_ofReal_mul]
    congr 1
    simp only [jet1_fst, eF]
    ring
  have hdiv : ∑ μ, pd (fun z' => fderiv ℝ (L0 D) (jet1 Y z') ((0 : Field 𝔄 𝓗 𝓢),
      Pi.single μ (psiDir χ : Field 𝔄 𝓗 𝓢))) μ z =
      reHalfIC (∑ μ, (pd (fun y => (Y y).2.2.2.2) μ z (Gfield D Y μ z χ) +
        (Y z).2.2.2.2 (pd (Gfield D Y μ) μ z χ))) := by
    simp only [hpt]
    rw [map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have hd : DifferentiableAt ℝ (fun z' => (Y z').2.2.2.2 (Gfield D Y μ z' χ)) z :=
      hΨbd.clm_apply (hGχ μ)
    rw [pd_clm reHalfIC hd μ, pd_clm_apply hΨbd (hGχ μ) μ,
      pd_clm_apply (differentiableAt_Gfield D hY hdet z μ) (differentiableAt_const χ) μ]
    congr 2
    have h0 : pd (fun _ : R4 => χ) μ z = 0 := by
      unfold SobolevOpen.pd; simp
    rw [h0, map_zero, add_zero]
  refine (congrArg₂ (· - ·) h1 hdiv).trans ?_
  have hid := dirac_identity D hcl hσ hρ he hdet' z (Y z).2.1
  have hidχ := congrArg (fun T : Spin 𝓢 => T χ) hid
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.zero_apply] at hidχ
  simp only [jet1_fst, volume_eF, omC_jet1 hYd]
  have hG : ∀ μ, pd (Gfield D Y μ) μ z = pd (fun y => volume (eF Y y) • gammaMu D μ (eF Y y)) μ z :=
    fun μ => rfl
  have hG0 : ∀ μ (x : 𝓢), Gfield D Y μ z x = volume (eF Y z) • gammaMu D μ (Y z).1 x :=
    fun μ x => rfl
  have hDb : ∀ μ (x : 𝓢), DPsiBar D (jet1 Y z) μ x =
      -(Y z).2.2.2.2 ((D.σ (omega0 (eF Y) z μ) + D.ρS ((Y z).2.1 μ)) x) +
        pd (fun y => (Y y).2.2.2.2) μ z x := by
    intro μ x
    unfold DPsiBar
    rw [omC_jet1 hYd, jet1_psiBar hYd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, map_sub, map_neg,
      jet1_fst, map_add]
    abel
  have hP : ∑ μ, (Y z).2.2.2.2 (pd (Gfield D Y μ) μ z χ) =
      -((volume (eF Y z) : ℂ) * (∑ μ, (Y z).2.2.2.2 ((D.σ (omega0 (eF Y) z μ) +
          D.ρS ((Y z).2.1 μ)) (gammaMu D μ (Y z).1 χ)) -
        ∑ μ, (Y z).2.2.2.2 (gammaMu D μ (Y z).1 ((D.σ (omega0 (eF Y) z μ) +
          D.ρS ((Y z).2.1 μ)) χ)))) := by
    have h := congrArg (Y z).2.2.2.2 hidχ
    rw [map_zero, map_sum] at h
    simp only [map_add] at h
    rw [Finset.sum_add_distrib] at h
    rw [eq_neg_iff_add_eq_zero, add_comm, ← h]
    congr 1
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.mul_apply, map_smul, map_sub, Complex.real_smul]
    rfl
  have hC : ∑ μ, pd (fun y => (Y y).2.2.2.2) μ z (Gfield D Y μ z χ) =
      (volume (eF Y z) : ℂ) * ∑ μ, pd (fun y => (Y y).2.2.2.2) μ z (gammaMu D μ (Y z).1 χ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hG0, map_smul, Complex.real_smul]
  have hB : ∑ μ, DPsiBar D (jet1 Y z) μ (gammaMu D μ (Y z).1 χ) =
      ∑ μ, pd (fun y => (Y y).2.2.2.2) μ z (gammaMu D μ (Y z).1 χ) -
        ∑ μ, (Y z).2.2.2.2 ((D.σ (omega0 (eF Y) z μ) + D.ρS ((Y z).2.1 μ))
          (gammaMu D μ (Y z).1 χ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hDb]; abel
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hB, hC, hP]
  generalize ∑ μ, (Y z).2.2.2.2 ((D.σ (omega0 (eF Y) z μ) + D.ρS ((Y z).2.1 μ))
    (gammaMu D μ (Y z).1 χ)) = Q
  generalize ∑ μ, (Y z).2.2.2.2 (gammaMu D μ (Y z).1 ((D.σ (omega0 (eF Y) z μ) +
    D.ρS ((Y z).2.1 μ)) χ)) = A
  generalize ∑ μ, pd (fun y => (Y y).2.2.2.2) μ z (gammaMu D μ (Y z).1 χ) = C
  generalize (Y z).2.2.2.2 (D.yukawa (Y z).2.2.1 χ) = y
  rw [reHalfIC_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.div_re,
    Complex.div_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, Complex.sub_im, Complex.add_im, Complex.neg_im]
  norm_num [Complex.normSq_apply]
  try ring

end DiracRows

end

end NativeDiracEuler

end RenewalGeometry
