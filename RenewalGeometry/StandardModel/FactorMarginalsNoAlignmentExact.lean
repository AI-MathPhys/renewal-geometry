/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Factor marginals do not fix their relative tensor position

Covers `cth:factor-marginals-no-alignment` of the spacetime–gauge duality manuscript.

On the six-dimensional carrier `ℂ³ ⊗ ℂ²` (index type `Fin 3 × Fin 2`):

* `colourEmb X = X ⊗ I₂` and `weakEmb Y = I₃ ⊗ Y` are injective unital `*`-homomorphisms
  (unital factor embeddings `M₃(ℂ), M₂(ℂ) ↪ M₆(ℂ)`) whose images commute;
* `weakEmb' = U · weakEmb · U*` for the unitary permutation `U` exchanging the basis vectors
  `c₁ ⊗ w₂` and `c₂ ⊗ w₁`; it is again an injective unital `*`-homomorphism, unitarily
  conjugate to `weakEmb`, so every single-factor trace and Hilbert–Schmidt Gram agrees;
* the pair `(colourEmb, weakEmb')` does **not** commute: `[E₁₁ ⊗ I, U (I ⊗ F₁₂) U*] ≠ 0`.

`factor_marginals_no_alignment` assembles the statement.  (The paper's witness uses
`U = exp(iθ D ⊗ X)` for generic `θ`; any unitary producing a non-commuting conjugate gives
the existence claim, and a permutation unitary makes the computation exact.)
-/

open Matrix
open scoped Kronecker

namespace RenewalGeometry
namespace FactorMarginals

/-- The six-dimensional carrier `ℂ³ ⊗ ℂ²`. -/
abbrev Six := Fin 3 × Fin 2

/-- The colour factor embedding `X ↦ X ⊗ I₂`. -/
def colourEmb : Matrix (Fin 3) (Fin 3) ℂ →⋆ₐ[ℂ] Matrix Six Six ℂ where
  toFun X := X ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := one_kronecker_one
  map_mul' X Y := by
    show (X * Y) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) = X ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) *
      Y ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    rw [← mul_kronecker_mul, Matrix.mul_one]
  map_zero' := zero_kronecker _
  map_add' X Y := add_kronecker X Y _
  commutes' r := by
    show (algebraMap ℂ (Matrix (Fin 3) (Fin 3) ℂ) r) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      algebraMap ℂ (Matrix Six Six ℂ) r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_kronecker,
      one_kronecker_one]
  map_star' X := by
    simp [star_eq_conjTranspose, conjTranspose_kronecker]

/-- The weak factor embedding `Y ↦ I₃ ⊗ Y`. -/
def weakEmb : Matrix (Fin 2) (Fin 2) ℂ →⋆ₐ[ℂ] Matrix Six Six ℂ where
  toFun Y := (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ Y
  map_one' := one_kronecker_one
  map_mul' X Y := by
    show (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ (X * Y) = (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ X *
      (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ Y
    rw [← mul_kronecker_mul, Matrix.mul_one]
  map_zero' := kronecker_zero _
  map_add' X Y := kronecker_add _ X Y
  commutes' r := by
    show (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ (algebraMap ℂ (Matrix (Fin 2) (Fin 2) ℂ) r) =
      algebraMap ℂ (Matrix Six Six ℂ) r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, kronecker_smul,
      one_kronecker_one]
  map_star' X := by
    simp [star_eq_conjTranspose, conjTranspose_kronecker]

/-- The basis transposition `c₁ ⊗ w₂ ↔ c₂ ⊗ w₁`. -/
def legSwap : Equiv.Perm Six := Equiv.swap ((0 : Fin 3), (1 : Fin 2)) ((1 : Fin 3), (0 : Fin 2))

/-- Its permutation matrix. -/
def swapMat : Matrix Six Six ℂ := of fun r c => if r = legSwap c then 1 else 0

theorem swapMat_star_mul : star swapMat * swapMat = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [star_eq_conjTranspose, mul_apply, conjTranspose_apply, swapMat, of_apply,
    Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, one_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [legSwap, Equiv.swap_apply_def]

theorem swapMat_mul_star : swapMat * star swapMat = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [star_eq_conjTranspose, mul_apply, conjTranspose_apply, swapMat, of_apply,
    Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, one_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [legSwap, Equiv.swap_apply_def]

/-- The unitary `U` mixing the two tensor legs. -/
def legUnitary : unitary (Matrix Six Six ℂ) :=
  ⟨swapMat, Unitary.mem_iff.mpr ⟨swapMat_star_mul, swapMat_mul_star⟩⟩

/-- The conjugated weak embedding `Y ↦ U (I₃ ⊗ Y) U*`. -/
noncomputable def weakEmb' : Matrix (Fin 2) (Fin 2) ℂ →⋆ₐ[ℂ] Matrix Six Six ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix Six Six ℂ) legUnitary : Matrix Six Six ℂ →⋆ₐ[ℂ] _).comp
    weakEmb

theorem weakEmb'_apply (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    weakEmb' Y = swapMat * weakEmb Y * star swapMat := rfl

theorem colourEmb_injective : Function.Injective colourEmb := by
  intro X Y h
  ext i j
  have := congrFun (congrFun h (i, 0)) (j, 0)
  simpa [colourEmb, kroneckerMap_apply] using this

theorem weakEmb_injective : Function.Injective weakEmb := by
  intro X Y h
  ext i j
  have := congrFun (congrFun h (0, i)) (0, j)
  simpa [weakEmb, kroneckerMap_apply] using this

theorem weakEmb'_injective : Function.Injective weakEmb' := by
  intro X Y h
  apply weakEmb_injective
  have e : ∀ Z, star swapMat * weakEmb' Z * swapMat = weakEmb Z := by
    intro Z
    rw [weakEmb'_apply]
    simp only [← Matrix.mul_assoc]
    rw [swapMat_star_mul, Matrix.one_mul, Matrix.mul_assoc (weakEmb Z), swapMat_star_mul,
      Matrix.mul_one]
  rw [← e X, ← e Y, h]

theorem trace_conj (A : Matrix Six Six ℂ) : (swapMat * A * star swapMat).trace = A.trace := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, swapMat_star_mul, Matrix.one_mul]

theorem gram_conj (A B : Matrix Six Six ℂ) :
    ((swapMat * A * star swapMat)ᴴ * (swapMat * B * star swapMat)).trace = (Aᴴ * B).trace := by
  have hU : swapMatᴴ * swapMat = 1 := swapMat_star_mul
  have hs : star swapMat = swapMatᴴ := rfl
  have : (swapMat * A * swapMatᴴ)ᴴ * (swapMat * B * swapMatᴴ) =
      swapMat * (Aᴴ * B) * swapMatᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc swapMatᴴ swapMat, hU, Matrix.one_mul]
  rw [hs, this, ← hs, trace_conj]

theorem colour_weak_commute (X : Matrix (Fin 3) (Fin 3) ℂ) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    Commute (colourEmb X) (weakEmb Y) := by
  show X ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) * (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ Y =
    (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ Y * X ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul]

/-- The explicit non-commuting pair: `[E₁₁ ⊗ I, U (I ⊗ F₁₂) U*] ≠ 0`. -/
theorem colour_weak'_not_commute :
    ¬ Commute (colourEmb (single 0 0 1)) (weakEmb' (single 0 1 1)) := by
  intro h
  have := congrFun (congrFun h.eq (0, 0)) (1, 0)
  simp only [weakEmb'_apply, colourEmb, weakEmb, StarAlgHom.coe_mk', AlgHom.coe_mk,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_three, Fin.sum_univ_two, kroneckerMap_apply, star_eq_conjTranspose,
    conjTranspose_apply, swapMat, of_apply] at this
  simp [legSwap, Equiv.swap_apply_def, single_apply, one_apply] at this

/-- **Factor marginals do not fix their relative tensor position
(`cth:factor-marginals-no-alignment`).**  On the six-dimensional carrier there are two pairs
of injective unital `*`-embeddings `(α, β)`, `(α', β')` of `M₃(ℂ)` and `M₂(ℂ)` with the same
colour marginal (`α' = α`), unitarily conjugate weak marginals (`β' = U β U*`), hence equal
single-factor traces and Hilbert–Schmidt Grams, such that the first pair commutes and the
second does not. -/
theorem factor_marginals_no_alignment :
    ∃ (α α' : Matrix (Fin 3) (Fin 3) ℂ →⋆ₐ[ℂ] Matrix Six Six ℂ)
      (β β' : Matrix (Fin 2) (Fin 2) ℂ →⋆ₐ[ℂ] Matrix Six Six ℂ) (U : Matrix Six Six ℂ),
      Function.Injective α ∧ Function.Injective α' ∧
      Function.Injective β ∧ Function.Injective β' ∧
      star U * U = 1 ∧ U * star U = 1 ∧
      α' = α ∧ (∀ Y, β' Y = U * β Y * star U) ∧
      (∀ X, (α X).trace = (α' X).trace) ∧
      (∀ X X', ((α X)ᴴ * α X').trace = ((α' X)ᴴ * α' X').trace) ∧
      (∀ Y, (β Y).trace = (β' Y).trace) ∧
      (∀ Y Y', ((β Y)ᴴ * β Y').trace = ((β' Y)ᴴ * β' Y').trace) ∧
      (∀ X Y, Commute (α X) (β Y)) ∧
      ¬ (∀ X Y, Commute (α' X) (β' Y)) := by
  refine ⟨colourEmb, colourEmb, weakEmb, weakEmb', swapMat, colourEmb_injective,
    colourEmb_injective, weakEmb_injective, weakEmb'_injective, swapMat_star_mul,
    swapMat_mul_star, rfl, weakEmb'_apply, fun _ => rfl, fun _ _ => rfl, ?_, ?_,
    colour_weak_commute, fun h => colour_weak'_not_commute (h _ _)⟩
  · intro Y
    rw [weakEmb'_apply, trace_conj]
  · intro Y Y'
    rw [weakEmb'_apply, weakEmb'_apply, gram_conj]

end FactorMarginals
end RenewalGeometry
