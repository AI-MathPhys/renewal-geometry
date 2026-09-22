/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The external tensor factorization `M_{2^m} ≅ M₄ ⊗ M_{2^{m-2}}`

The matrix-algebra step of `thm:external-core`: once the marked
symplectic module splits as `H_prim = W_ext ⟂ H_intr` with
`dim W_ext = 4` (`NCG/Dimension/TemporalPartner.lean`), the active
factor splits as a tensor product of the marked external `M₄(ℂ)`
block and the commuting internal complement:

* `externalFactorSplit` — the algebra isomorphism
  `M_{2^{k+2}}(A) ≅ M₄(A) ⊗ M_{2^k}(A)`-style factorization
  `Matrix (Fin (2^(k+2))) ≃ₐ[R] M₄(R) ⊗[R] M_{2^k}(R)` over any
  commutative ring, assembled from `Matrix.reindexAlgEquiv`
  (regrouping `2^(k+2) = 4·2^k`), `Matrix.compAlgEquiv` (block
  structure), and `matrixEquivTensor` (blocks as a tensor factor);
* `externalFactorSplit'` — the same statement indexed by the total
  primitive half-rank `m ≥ 2`, matching the manuscript's
  `𝒜_act ≅ M₄(ℂ) ⊗ M_{2^{m-2}}(ℂ)`.

The identification of the *marked* generators with the left factor
is the Jordan–Wigner content of `NCG/Algebra/JordanWigner.lean`
(`thm:clifford-factor`); this file supplies the dimension-exact
tensor split used by `thm:external-core`.
-/

namespace NCG

open scoped TensorProduct

variable (R : Type*) [CommRing R]

/-- Regrouping exponents: `2^(k+2) = 4 · 2^k`. -/
theorem two_pow_add_two (k : ℕ) : 2 ^ (k + 2) = 4 * 2 ^ k := by
  rw [pow_add]
  ring

/-- **External tensor factorization** (`thm:external-core`, matrix
step): the total matrix algebra of the primitive Clifford factor
splits as the marked external `M₄` block tensored with the internal
complement, `M_{2^{k+2}}(R) ≅ M₄(R) ⊗[R] M_{2^k}(R)`. -/
noncomputable def externalFactorSplit (k : ℕ) :
    Matrix (Fin (2 ^ (k + 2))) (Fin (2 ^ (k + 2))) R ≃ₐ[R]
      Matrix (Fin 4) (Fin 4) R ⊗[R]
        Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) R :=
  (Matrix.reindexAlgEquiv R R
      ((finCongr (two_pow_add_two k)).trans finProdFinEquiv.symm)).trans
    <| ((Matrix.compAlgEquiv (Fin 4) (Fin (2 ^ k)) R R).symm).trans
    <| (matrixEquivTensor (Fin 4) R
        (Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) R)).trans
    <| Algebra.TensorProduct.comm R _ _

/-- The factorization indexed by the total primitive half-rank
`m ≥ 2`: `M_{2^m}(R) ≅ M₄(R) ⊗[R] M_{2^{m-2}}(R)`.  For `m = 2` the
internal complement is the scalar block `M₁(R) = R`-as-matrices. -/
noncomputable def externalFactorSplit' (m : ℕ) (hm : 2 ≤ m) :
    Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) R ≃ₐ[R]
      Matrix (Fin 4) (Fin 4) R ⊗[R]
        Matrix (Fin (2 ^ (m - 2))) (Fin (2 ^ (m - 2))) R :=
  (Matrix.reindexAlgEquiv R R
      (finCongr (congrArg (2 ^ ·) (by omega : m = m - 2 + 2)))).trans
    (externalFactorSplit R (m - 2))

end NCG
