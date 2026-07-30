/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Generation transparency of the product algebra
(SM_emergence, Phase 2)

`thm:generation-transparency`: every forced-admissible operator has
the product-algebra form `Σ_k X_k ⊗ F_k`, so the finite
spectral-triple factors can dress a cell operator but cannot create
a new generation-space asymmetry absent from the cell algebra.

* `inv_mem_of_isUnit` — Cayley–Hamilton inverse membership: in a
  matrix algebra the inverse of an invertible member of a
  subalgebra stays in the subalgebra, so resolvents and Feshbach
  reductions cannot leave it;
* `kronSpan`, `kronAlgebra` — the product algebra: sums of Kronecker
  products form a subalgebra of the bipartite matrix algebra;
* `kronSpan_conjTranspose_mem`, `kronAlgebra_inv_mem` — closure
  under adjoints and resolvents: the full forced-admissible
  operation set (sums, products, adjoints, resolvents, Feshbach
  reductions) preserves the product form.
-/

namespace NCG

open Matrix Polynomial Kronecker

/-! ## Cayley–Hamilton inverse membership -/

/-- **Inverse membership by Cayley–Hamilton**: in a matrix algebra,
the inverse of an invertible member of a subalgebra lies in the
subalgebra. -/
theorem inv_mem_of_isUnit {n : Type*} [Fintype n] [DecidableEq n]
    {S : Subalgebra ℂ (Matrix n n ℂ)} {M : Matrix n n ℂ}
    (hM : M ∈ S) (hU : IsUnit M) : M⁻¹ ∈ S := by
  have hCH := Matrix.aeval_self_charpoly M
  set p := M.charpoly with hp
  have hsplit : Polynomial.X * p.divX + Polynomial.C (p.coeff 0) = p :=
    Polynomial.X_mul_divX_add p
  have haeval : M * Polynomial.aeval M p.divX
      + (p.coeff 0) • (1 : Matrix n n ℂ) = 0 := by
    have h := congrArg (Polynomial.aeval M) hsplit
    rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
      hCH] at h
    rw [← h]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one]
  have hc0 : p.coeff 0 ≠ 0 := by
    intro h0
    have hdet : M.det = (-1) ^ (Fintype.card n) * p.coeff 0 :=
      Matrix.det_eq_sign_charpoly_coeff M
    rw [h0, mul_zero] at hdet
    exact ((Matrix.isUnit_iff_isUnit_det M).mp hU).ne_zero hdet
  have hMq : M * ((-(p.coeff 0)⁻¹) • Polynomial.aeval M p.divX)
      = 1 := by
    rw [mul_smul_comm]
    have h1 : M * Polynomial.aeval M p.divX
        = -((p.coeff 0) • (1 : Matrix n n ℂ)) :=
      eq_neg_of_add_eq_zero_left haeval
    rw [h1, smul_neg, smul_smul, neg_mul, inv_mul_cancel₀ hc0]
    simp
  rw [Matrix.inv_eq_right_inv hMq]
  apply Subalgebra.smul_mem
  have hadj : ∀ q : Polynomial ℂ, Polynomial.aeval M q ∈ S := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p1 p2 hp1 hp2 =>
      rw [map_add]
      exact add_mem hp1 hp2
    | monomial k c =>
      rw [Polynomial.aeval_monomial]
      exact mul_mem (S.algebraMap_mem c) (pow_mem hM k)
  exact hadj p.divX

/-! ## The product algebra -/

variable (m n : Type*)

/-- The product space: the span of Kronecker products `X ⊗ F`. -/
def kronSpan : Submodule ℂ (Matrix (m × n) (m × n) ℂ) :=
  Submodule.span ℂ
    {M | ∃ X : Matrix m m ℂ, ∃ F : Matrix n n ℂ, M = X ⊗ₖ F}

variable {m n}

theorem kron_mem_kronSpan (X : Matrix m m ℂ) (F : Matrix n n ℂ) :
    X ⊗ₖ F ∈ kronSpan m n :=
  Submodule.subset_span ⟨X, F, rfl⟩

theorem kronSpan_one_mem [DecidableEq m] [DecidableEq n] :
    (1 : Matrix (m × n) (m × n) ℂ) ∈ kronSpan m n := by
  have h : (1 : Matrix m m ℂ) ⊗ₖ (1 : Matrix n n ℂ)
      = (1 : Matrix (m × n) (m × n) ℂ) := Matrix.one_kronecker_one
  rw [← h]
  exact kron_mem_kronSpan 1 1

/-- The product space is closed under multiplication (the mixed
product identity). -/
theorem kronSpan_mul_mem [Fintype m] [Fintype n]
    {A B : Matrix (m × n) (m × n) ℂ}
    (hA : A ∈ kronSpan m n) (hB : B ∈ kronSpan m n) :
    A * B ∈ kronSpan m n := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    induction hB using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨X1, F1, rfl⟩ := hx
      obtain ⟨X2, F2, rfl⟩ := hy
      rw [← Matrix.mul_kronecker_mul]
      exact kron_mem_kronSpan _ _
    | zero =>
      rw [mul_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      rw [mul_add]
      exact add_mem hy hz
    | smul c y _ hy =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ hy
  | zero =>
    rw [zero_mul]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [add_mul]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ hx

/-- `thm:generation-transparency` (structure): the product forms
`Σ_k X_k ⊗ F_k` constitute a subalgebra of the bipartite matrix
algebra — sums and products of forced-admissible operators keep the
product form. -/
def kronAlgebra (m n : Type*) [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] : Subalgebra ℂ (Matrix (m × n) (m × n) ℂ) :=
  Submodule.toSubalgebra (kronSpan m n) kronSpan_one_mem
    fun _ _ hx hy => kronSpan_mul_mem hx hy

/-- Closure under adjoints: `(X ⊗ F)ᴴ = Xᴴ ⊗ Fᴴ`, extended by
antilinearity. -/
theorem kronSpan_conjTranspose_mem {A : Matrix (m × n) (m × n) ℂ}
    (hA : A ∈ kronSpan m n) : Aᴴ ∈ kronSpan m n := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨X, F, rfl⟩ := hx
    have h : (X ⊗ₖ F)ᴴ = Xᴴ ⊗ₖ Fᴴ := by
      ext ⟨i, j⟩ ⟨k, l⟩
      simp [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
    rw [h]
    exact kron_mem_kronSpan _ _
  | zero =>
    rw [Matrix.conjTranspose_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [Matrix.conjTranspose_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [Matrix.conjTranspose_smul]
    exact Submodule.smul_mem _ _ hx

/-- `thm:generation-transparency` (resolvent closure): resolvents
and Feshbach reductions of forced-admissible operators keep the
product form — the finite factors cannot break a generation-channel
symmetry through any admissible operation. -/
theorem kronAlgebra_inv_mem [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    {A : Matrix (m × n) (m × n) ℂ} (hA : A ∈ kronAlgebra m n)
    (hU : IsUnit A) : A⁻¹ ∈ kronAlgebra m n :=
  inv_mem_of_isUnit hA hU

end NCG
