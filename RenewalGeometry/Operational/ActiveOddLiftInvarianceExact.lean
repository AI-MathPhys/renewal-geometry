/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Spectator-lift invariance of active grading change
  (`thm:active-odd-lift-invariance`, spacetime–gauge duality manuscript)

Let `Z` be a grading on the active carrier with `P± = (1 ± Z)/2`, and let `Φ` be a
linear map on the active carrier.  Its active cross-sign mass is

`μ_Z^act(Φ) = Tr[P₋ Φ(P₊)] + Tr[P₊ Φ(P₋)]`   (`eq:active-cross-sign-mass`).

For an unread spectator with state `σ` (`Tr σ = 1`) and any trace-preserving map `Ψ`
on the spectator, the product lift `Φ ⊗ Ψ` on the joint carrier satisfies

`Tr[(P₋ ⊗ I) (Φ ⊗ Ψ)(P₊ ⊗ σ)] + Tr[(P₊ ⊗ I) (Φ ⊗ Ψ)(P₋ ⊗ σ)] = μ_Z^act(Φ)`

(`eq:active-odd-lift-invariance`).

* `kroneckerLift Φ Ψ` — the product lift `Φ ⊗ Ψ`, defined as a genuine linear map on
  the joint carrier `Matrix (dA × dK) (dA × dK) ℂ` through the matrix-unit basis;
* `kroneckerLift_kronecker` — it acts on elementary tensors by
  `(Φ ⊗ Ψ)(A ⊗ₖ B) = Φ A ⊗ₖ Ψ B`;
* `spectator_lift_trace` — the single-term identity
  `Tr[(P ⊗ I)(Φ ⊗ Ψ)(P' ⊗ σ)] = Tr[P Φ(P')]`;
* `active_odd_lift_invariance` — the boxed identity for `P± = (1 ± Z)/2`.

Rendering disclosed: complete positivity of `Φ`, `Ψ` and positivity of `σ` are not
needed for the identity (only linearity of `Φ`, `Ψ`, trace preservation of `Ψ` and
`Tr σ = 1`), so they are not assumed; the grading properties `Z = Z* = Z⁻¹` are
likewise not used.  The non-identifiability remark refers to
`app:microscopic-odd-lift` and is not part of the claim.
-/

open Matrix
open scoped Kronecker

namespace RenewalGeometry
namespace ActiveOddLift

variable {dA dK : Type*} [Fintype dA] [Fintype dK] [DecidableEq dA] [DecidableEq dK]

/-- The product lift `Φ ⊗ Ψ` of two linear maps on the active and spectator carriers,
as a linear map on the joint carrier, defined through the matrix-unit basis
`E_{ij} ⊗ₖ E_{kl}` (`thm:active-odd-lift-invariance`). -/
noncomputable def kroneckerLift
    (Φ : Matrix dA dA ℂ →ₗ[ℂ] Matrix dA dA ℂ)
    (Ψ : Matrix dK dK ℂ →ₗ[ℂ] Matrix dK dK ℂ) :
    Matrix (dA × dK) (dA × dK) ℂ →ₗ[ℂ] Matrix (dA × dK) (dA × dK) ℂ where
  toFun X := ∑ i : dA, ∑ j : dA, ∑ k : dK, ∑ l : dK,
    X (i, k) (j, l) • (Φ (single i j 1) ⊗ₖ Ψ (single k l 1))
  map_add' X Y := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
      smul_smul]

/-- A matrix is the sum of its scaled matrix units. -/
theorem eq_sum_smul_single {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n ℂ) :
    A = ∑ i, ∑ j, A i j • single i j (1 : ℂ) := by
  conv_lhs => rw [matrix_eq_sum_single A]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [smul_single, smul_eq_mul, mul_one]

/-- A linear map on matrices is determined by its values on matrix units. -/
theorem linearMap_apply_eq_sum {m : Type*} [Fintype m] [DecidableEq m]
    (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ) (A : Matrix m m ℂ) :
    Φ A = ∑ i, ∑ j, A i j • Φ (single i j 1) := by
  conv_lhs => rw [eq_sum_smul_single A]
  simp only [map_sum, map_smul]

/-- The product lift acts on elementary tensors by `(Φ ⊗ Ψ)(A ⊗ₖ B) = Φ A ⊗ₖ Ψ B`. -/
theorem kroneckerLift_kronecker
    (Φ : Matrix dA dA ℂ →ₗ[ℂ] Matrix dA dA ℂ)
    (Ψ : Matrix dK dK ℂ →ₗ[ℂ] Matrix dK dK ℂ)
    (A : Matrix dA dA ℂ) (B : Matrix dK dK ℂ) :
    kroneckerLift Φ Ψ (A ⊗ₖ B) = Φ A ⊗ₖ Ψ B := by
  ext ⟨p, q⟩ ⟨r, s⟩
  rw [kroneckerMap_apply, linearMap_apply_eq_sum Φ A, linearMap_apply_eq_sum Ψ B]
  simp only [kroneckerLift, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply,
    Matrix.smul_apply, kroneckerMap_apply, smul_eq_mul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Single-term spectator collapse: `Tr[(P ⊗ I)(Φ ⊗ Ψ)(P' ⊗ σ)] = Tr[P Φ(P')]` for
trace-preserving `Ψ` and a normalized spectator state `σ`. -/
theorem spectator_lift_trace
    (Φ : Matrix dA dA ℂ →ₗ[ℂ] Matrix dA dA ℂ)
    (Ψ : Matrix dK dK ℂ →ₗ[ℂ] Matrix dK dK ℂ)
    (hΨ : ∀ B, (Ψ B).trace = B.trace)
    (σ : Matrix dK dK ℂ) (hσ : σ.trace = 1)
    (P P' : Matrix dA dA ℂ) :
    ((P ⊗ₖ (1 : Matrix dK dK ℂ)) * kroneckerLift Φ Ψ (P' ⊗ₖ σ)).trace
      = (P * Φ P').trace := by
  rw [kroneckerLift_kronecker, ← mul_kronecker_mul, trace_kronecker, one_mul, hΨ, hσ,
    mul_one]

/-- The grading projector `P₊ = (1 + Z)/2`. -/
noncomputable def gradingPlus (Z : Matrix dA dA ℂ) : Matrix dA dA ℂ :=
  (2 : ℂ)⁻¹ • (1 + Z)

/-- The grading projector `P₋ = (1 − Z)/2`. -/
noncomputable def gradingMinus (Z : Matrix dA dA ℂ) : Matrix dA dA ℂ :=
  (2 : ℂ)⁻¹ • (1 - Z)

/-- The active cross-sign mass `μ_Z^act(Φ) = Tr[P₋ Φ(P₊)] + Tr[P₊ Φ(P₋)]`
(`eq:active-cross-sign-mass`). -/
noncomputable def activeCrossSignMass (Z : Matrix dA dA ℂ)
    (Φ : Matrix dA dA ℂ →ₗ[ℂ] Matrix dA dA ℂ) : ℂ :=
  (gradingMinus Z * Φ (gradingPlus Z)).trace + (gradingPlus Z * Φ (gradingMinus Z)).trace

/-- **`thm:active-odd-lift-invariance`** (`eq:active-odd-lift-invariance`): for an unread
spectator state `σ` and any trace-preserving spectator map `Ψ`, the product lift
`Φ ⊗ Ψ` with active preparations `P± ⊗ σ` and active reads `P∓ ⊗ I` reproduces the
active cross-sign mass `μ_Z^act(Φ)`. -/
theorem active_odd_lift_invariance (Z : Matrix dA dA ℂ)
    (Φ : Matrix dA dA ℂ →ₗ[ℂ] Matrix dA dA ℂ)
    (Ψ : Matrix dK dK ℂ →ₗ[ℂ] Matrix dK dK ℂ)
    (hΨ : ∀ B, (Ψ B).trace = B.trace)
    (σ : Matrix dK dK ℂ) (hσ : σ.trace = 1) :
    ((gradingMinus Z ⊗ₖ (1 : Matrix dK dK ℂ)) *
        kroneckerLift Φ Ψ (gradingPlus Z ⊗ₖ σ)).trace
      + ((gradingPlus Z ⊗ₖ (1 : Matrix dK dK ℂ)) *
        kroneckerLift Φ Ψ (gradingMinus Z ⊗ₖ σ)).trace
      = activeCrossSignMass Z Φ := by
  rw [activeCrossSignMass, spectator_lift_trace Φ Ψ hΨ σ hσ,
    spectator_lift_trace Φ Ψ hΨ σ hσ]

end ActiveOddLift
end RenewalGeometry

