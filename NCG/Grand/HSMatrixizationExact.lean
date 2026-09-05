/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.GeoMeanOrderExact

/-!
# Left and right multiplication as Kronecker matrices

Step (D4e) of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: on the Hilbert–Schmidt space `ℂ^{n×n}`
the left multiplication by `A` is `A ⊗ 1`, the right multiplication by
`B` is `1 ⊗ Bᵀ`, they commute, and the spectral calculus passes through
both legs.  Pairing at the entangled vector recovers the trace:
`⟨vec 1, (M ⊗ₖ N) vec 1⟩ = Tr(M Nᵀ)`.

* `matFun_kronR`: `f(A ⊗ 1) = f(A) ⊗ 1`;
* `matFun_transpose`, `matFun_kronL_transpose`: `f(1 ⊗ Bᵀ) = 1 ⊗ f(B)ᵀ`;
* `kronR_posDef`, `one_kron_posDef`: positivity of the two legs;
* `vecOne_pair`: the entangled-vector trace pairing.
-/

open Matrix Unitary Finset Polynomial Kronecker
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {p : Type*} [Fintype p] [DecidableEq p]
variable {A B : Matrix n n ℂ}

/-! ### The mirror Kronecker leg `M ⊗ 1` -/

omit [DecidableEq n] in
theorem kronR_mul (A B : Matrix n n ℂ) :
    (A ⊗ₖ (1 : Matrix p p ℂ)) * (B ⊗ₖ 1) = (A * B) ⊗ₖ 1 := by
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem kronR_pow (A : Matrix n n ℂ) (k : ℕ) :
    (A ⊗ₖ (1 : Matrix p p ℂ)) ^ k = (A ^ k) ⊗ₖ 1 := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Matrix.one_kronecker_one]
  | succ k ih => rw [pow_succ, pow_succ, ih, kronR_mul]

omit [Fintype n] [DecidableEq n] [Fintype p] in
theorem kronR_smul (c : ℝ) (A : Matrix n n ℂ) :
    (c • A) ⊗ₖ (1 : Matrix p p ℂ) = c • (A ⊗ₖ 1) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.kronecker_apply, Matrix.smul_apply]
  rw [smul_mul_assoc]

omit [Fintype n] [DecidableEq n] [Fintype p] in
theorem kronR_sum {ι : Type*} (s : Finset ι) (g : ι → Matrix n n ℂ) :
    (∑ x ∈ s, g x) ⊗ₖ (1 : Matrix p p ℂ) = ∑ x ∈ s, g x ⊗ₖ 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.kronecker_apply, Matrix.sum_apply, Finset.sum_mul]

theorem aeval_kronR (A : Matrix n n ℂ) (P : Polynomial ℝ) :
    Polynomial.aeval (A ⊗ₖ (1 : Matrix p p ℂ)) P =
      Polynomial.aeval A P ⊗ₖ 1 := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    kronR_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [kronR_smul, kronR_pow]

omit [Fintype n] [DecidableEq n] [Fintype p] in
theorem kronR_isHermitian (hA : A.IsHermitian) :
    (A ⊗ₖ (1 : Matrix p p ℂ)).IsHermitian := by
  unfold Matrix.IsHermitian
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [Matrix.conjTranspose_apply, Matrix.kronecker_apply,
    Matrix.kronecker_apply, star_mul']
  rw [← Matrix.conjTranspose_apply A, hA.eq]
  rw [← Matrix.conjTranspose_apply (1 : Matrix p p ℂ),
    Matrix.conjTranspose_one]

/-- `f(A ⊗ 1) = f(A) ⊗ 1`. -/
theorem matFun_kronR (hA : A.IsHermitian)
    (hkron : (A ⊗ₖ (1 : Matrix p p ℂ)).IsHermitian) (f : ℝ → ℝ) :
    matFun hkron f = matFun hA f ⊗ₖ 1 := by
  obtain ⟨P, hPval⟩ := exists_interpolating' f
    ((Finset.image hkron.eigenvalues Finset.univ) ∪
      Finset.image hA.eigenvalues Finset.univ)
  have h1 : matFun hkron f = Polynomial.aeval (A ⊗ₖ (1 : Matrix p p ℂ)) P :=
    matFun_eq_aeval hkron f P fun i => hPval _
      (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have h2 : matFun hA f = Polynomial.aeval A P :=
    matFun_eq_aeval hA f P fun i => hPval _
      (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  rw [h1, h2, aeval_kronR]

/-! ### Transpose transport -/

omit [Fintype n] [DecidableEq n] in
theorem transpose_isHermitian (hB : B.IsHermitian) :
    (Bᵀ).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply,
    Matrix.transpose_apply, ← Matrix.conjTranspose_apply, hB.eq]

theorem aeval_transpose (B : Matrix n n ℂ) (P : Polynomial ℝ) :
    Polynomial.aeval Bᵀ P = (Polynomial.aeval B P)ᵀ := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.transpose_smul, Matrix.transpose_pow]

/-- `f(Bᵀ) = f(B)ᵀ`. -/
theorem matFun_transpose (hB : B.IsHermitian)
    (hBt : (Bᵀ).IsHermitian) (f : ℝ → ℝ) :
    matFun hBt f = (matFun hB f)ᵀ := by
  obtain ⟨P, hPval⟩ := exists_interpolating' f
    ((Finset.image hBt.eigenvalues Finset.univ) ∪
      Finset.image hB.eigenvalues Finset.univ)
  have h1 : matFun hBt f = Polynomial.aeval Bᵀ P :=
    matFun_eq_aeval hBt f P fun i => hPval _
      (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have h2 : matFun hB f = Polynomial.aeval B P :=
    matFun_eq_aeval hB f P fun i => hPval _
      (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  rw [h1, h2, aeval_transpose]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
omit [DecidableEq n] in
theorem transpose_posSemidef (hB : B.PosSemidef) :
    (Bᵀ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (transpose_isHermitian hB.1) fun v => ?_
  have hq := hB.dotProduct_mulVec_nonneg (star v)
  have heq : star v ⬝ᵥ (Bᵀ *ᵥ v) = star (star v) ⬝ᵥ (B *ᵥ star v) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_star,
      Matrix.transpose_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [heq]
  exact hq

/-! ### Positivity of the two legs -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
omit [DecidableEq n] in
theorem kronR_posSemidef (hA : A.PosSemidef) :
    (A ⊗ₖ (1 : Matrix p p ℂ)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (kronR_isHermitian hA.1) fun v => ?_
  have hexp : star v ⬝ᵥ ((A ⊗ₖ (1 : Matrix p p ℂ)) *ᵥ v) =
      ∑ b : p, star (fun i => v (i, b)) ⬝ᵥ (A *ᵥ fun i => v (i, b)) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i₁ _ => ?_
    rw [Finset.sum_eq_single b]
    · change A i i₁ * (1 : Matrix p p ℂ) b b * v (i₁, b) =
        A i i₁ * v (i₁, b)
      rw [Matrix.one_apply_eq, mul_one]
    · intro y _ hy
      change A i i₁ * (1 : Matrix p p ℂ) b y * v (i₁, y) = 0
      rw [Matrix.one_apply_ne (Ne.symm hy), mul_zero, zero_mul]
    · intro hb
      exact absurd (Finset.mem_univ _) hb
  rw [hexp]
  refine Finset.sum_nonneg fun b _ => ?_
  exact hA.dotProduct_mulVec_nonneg _

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
omit [DecidableEq p] in
theorem one_kron_posSemidef {C : Matrix p p ℂ} (hC : C.PosSemidef) :
    ((1 : Matrix n n ℂ) ⊗ₖ C).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (kron_one_isHermitian hC.1) fun v => ?_
  have hexp : star v ⬝ᵥ (((1 : Matrix n n ℂ) ⊗ₖ C) *ᵥ v) =
      ∑ i : n, star (fun b => v (i, b)) ⬝ᵥ (C *ᵥ fun b => v (i, b)) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
    congr 1
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun y _ => ?_
      change (1 : Matrix n n ℂ) i i * C b y * v (i, y) = C b y * v (i, y)
      rw [Matrix.one_apply_eq, one_mul]
    · intro x _ hx
      refine Finset.sum_eq_zero fun y _ => ?_
      change (1 : Matrix n n ℂ) i x * C b y * v (x, y) = 0
      rw [Matrix.one_apply_ne (Ne.symm hx), zero_mul, zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ _) hi
  rw [hexp]
  refine Finset.sum_nonneg fun i _ => ?_
  exact hC.dotProduct_mulVec_nonneg _

/-! ### The entangled trace pairing -/

/-- The entangled vector `vec 1`. -/
def vecOne : n × n → ℂ := fun q => if q.1 = q.2 then 1 else 0

set_option maxHeartbeats 800000 in -- entangled pairing bookkeeping
/-- **The trace pairing**: `⟨vec 1, (M ⊗ₖ N) vec 1⟩ = Tr(M Nᵀ)`. -/
theorem vecOne_pair (M N : Matrix n n ℂ) :
    star vecOne ⬝ᵥ ((M ⊗ₖ N) *ᵥ vecOne) = (M * Nᵀ).trace := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, vecOne,
    Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
    simp only [star_one, one_mul]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, mul_one]
      rfl
    · intro l _ hl
      rw [if_neg (fun h => hl h.symm), mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  · intro j _ hj
    rw [if_neg (fun h => hj h.symm), star_zero, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ _) hi

end QRE
end NCG
