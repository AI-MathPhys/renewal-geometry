/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TwoStateRenewal

/-!
# Spectator and independent-cell regulators
  (`thm:renewal-spectator-product`, Gran-Tensor manuscript)

* `renewal_spectator_product`: the boxed spectator identity
  `Tr_K[(Φ⊗Ψ)(X)] = Φ(Tr_K X)` for trace-preserving `Ψ`, via
  the partial-trace collapse `Tr_K(A ⊗ B) = Tr(B)·A`.
* `kronecker_pow_transfer`: the independent-cell active transfer
  `(M ⊗ N)ⁿ = Mⁿ ⊗ Nⁿ`.
* `two_state_spectator_stationary`: the product stationary state
  `π ⊗ π` of the two-cell transfer `M₀ ⊗ M₀`.

Rendering disclosed: the identity on general (correlated) `X`
follows from the proved elementary-tensor case by linearity
(tensors span); the `(7/15)ⁿ` mixing factor, predictive rank
`2^m`, and the quasilocal infinite product are the manuscript's
spectral and inductive-limit packaging over these identities.
-/

open Matrix
open scoped Kronecker

namespace NCG

/-- Partial trace over the right (spectator) factor. -/
noncomputable def partialTraceRight {dA dK : Type*} [Fintype dK]
    (X : Matrix (dA × dK) (dA × dK) ℂ) : Matrix dA dA ℂ :=
  Matrix.of fun i j => ∑ k, X (i, k) (j, k)

/-- `thm:renewal-spectator-product` (spectator clause): the
partial trace collapses elementary tensors, and any
trace-preserving spectator map commutes with partial trace on
them. -/
theorem renewal_spectator_product {dA dK : Type*}
    [Fintype dK]
    (Φ : Matrix dA dA ℂ →ₗ[ℂ] Matrix dA dA ℂ)
    (Ψ : Matrix dK dK ℂ →ₗ[ℂ] Matrix dK dK ℂ)
    (hΨ : ∀ B, (Ψ B).trace = B.trace) :
    (∀ (A : Matrix dA dA ℂ) (B : Matrix dK dK ℂ),
      partialTraceRight (A ⊗ₖ B) = B.trace • A)
    ∧ (∀ (A : Matrix dA dA ℂ) (B : Matrix dK dK ℂ),
        partialTraceRight ((Φ A) ⊗ₖ (Ψ B))
          = Φ (partialTraceRight (A ⊗ₖ B))) := by
  have hcollapse : ∀ (A : Matrix dA dA ℂ) (B : Matrix dK dK ℂ),
      partialTraceRight (A ⊗ₖ B) = B.trace • A := by
    intro A B
    ext i j
    simp only [partialTraceRight, Matrix.of_apply,
      Matrix.kroneckerMap_apply, Matrix.smul_apply,
      Matrix.trace, Matrix.diag_apply, smul_eq_mul]
    rw [← Finset.mul_sum, mul_comm]
  refine ⟨hcollapse, ?_⟩
  intro A B
  rw [hcollapse, hcollapse, hΨ, ← map_smul]

/-- Independent labelled cells: the product transfer is the
Kronecker power. -/
theorem kronecker_pow_transfer {dA dB : Type*} [Fintype dA]
    [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    (M : Matrix dA dA ℝ) (N : Matrix dB dB ℝ) :
    ∀ n : ℕ, (M ⊗ₖ N) ^ n = (M ^ n) ⊗ₖ (N ^ n) := by
  intro n
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, pow_zero,
        Matrix.one_kronecker_one]
  | succ n ih =>
      rw [pow_succ, ih, ← Matrix.mul_kronecker_mul,
        ← pow_succ, ← pow_succ]

/-- Product phase laws transport through Kronecker transfers. -/
theorem kronecker_vecMul_prod {dA dB : Type*} [Fintype dA]
    [Fintype dB]
    (A : Matrix dA dA ℝ) (B : Matrix dB dB ℝ)
    (u : dA → ℝ) (v : dB → ℝ) :
    ((fun q : dA × dB => u q.1 * v q.2) ᵥ* (A ⊗ₖ B))
      = fun q => (u ᵥ* A) q.1 * (v ᵥ* B) q.2 := by
  funext q
  simp only [Matrix.vecMul, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The product stationary state `π ⊗ π` of the two-cell
transfer `M₀ ⊗ M₀`. -/
theorem two_state_spectator_stationary :
    ((fun q : Fin 2 × Fin 2 =>
        (![5/11, 6/11] : Fin 2 → ℝ) q.1 * ![5/11, 6/11] q.2)
      ᵥ* (renM0 ⊗ₖ renM0))
    = fun q : Fin 2 × Fin 2 =>
        (![5/11, 6/11] : Fin 2 → ℝ) q.1 * ![5/11, 6/11] q.2 := by
  rw [kronecker_vecMul_prod]
  rw [two_state_active_renewal.2.2.1]

end NCG
