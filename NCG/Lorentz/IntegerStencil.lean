/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Integer-stencil second moments (consistency core)

**Lemma `lem:integer-stencil-decomposition`**: every positive-definite
unit-trace `M` decomposes as a convex combination of rank-one
projections along integer directions.  The consistency half proved
here: any stencil datum (unit directions with convex weights)
assembles to a unit-trace (`NCG.stencil_moment_trace`)
positive-semidefinite (`NCG.stencil_moment_psd`) second moment — the
admissible stencil moments are exactly points of the moment body.  The
existence half (density of integer directions on the sphere and the
interior-perturbation argument) is the noted step.
-/

namespace NCG

/-- **Lemma `lem:integer-stencil-decomposition` (trace
consistency)**: a convex combination of rank-one projections along
unit directions has unit trace. -/
theorem stencil_moment_trace {d m : ℕ} (p : Fin m → ℝ)
    (θ : Fin m → Fin d → ℝ)
    (hsum : ∑ a, p a = 1) (hunit : ∀ a, ∑ i, θ a i ^ 2 = 1) :
    Matrix.trace (∑ a, p a • Matrix.vecMulVec (θ a) (θ a)) = 1 := by
  rw [Matrix.trace_sum]
  have h : ∀ a, Matrix.trace (p a • Matrix.vecMulVec (θ a) (θ a))
      = p a := by
    intro a
    rw [Matrix.trace_smul]
    have htr : Matrix.trace (Matrix.vecMulVec (θ a) (θ a))
        = ∑ i, θ a i ^ 2 := by
      simp [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, sq]
    rw [htr, hunit a, smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl (fun a _ => h a), hsum]

/-- **Lemma `lem:integer-stencil-decomposition` (positivity
consistency)**: a convex combination of rank-one projections is
positive semidefinite — `xᵀ M x = Σ pₐ (θₐ·x)² ≥ 0`. -/
theorem stencil_moment_psd {d m : ℕ} (p : Fin m → ℝ)
    (θ : Fin m → Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) (x : Fin d → ℝ) :
    0 ≤ x ⬝ᵥ (∑ a, p a • Matrix.vecMulVec (θ a) (θ a)).mulVec x := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_nonneg fun a _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul,
    Matrix.vecMulVec_mulVec, dotProduct_smul]
  have hsq : 0 ≤ (x ⬝ᵥ θ a) * (θ a ⬝ᵥ x) := by
    rw [dotProduct_comm]
    exact mul_self_nonneg _
  simpa [smul_eq_mul] using
    mul_nonneg (hp a) hsq

end NCG
