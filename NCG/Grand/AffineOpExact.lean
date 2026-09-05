/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.AffineKernelExact
import NCG.Grand.RelEntropyPerturbExact

/-!
# The affine modular operator of the BKM form

Step (B3c) of the BKM programme for `cor:accepted-BKM-loss` (QS.5): the
Hilbert–Schmidt matrixization of the affine kernel denominator,

`M_t(σ) = t·(σ ⊗ 1) + (1−t)·(1 ⊗ σᵀ)`,

acting on vectorized tangents `vecM v (i,j) = v i j` by
`M_t(σ) vec v = vec(t·σv + (1−t)·vσ)`.  It is **affine in `σ`** — the
property that turns `quadForm_convex` into joint convexity of the BKM
metric.

* `vecM`, `vecM_kron_mulVec`: the vectorization and its kron action;
* `affineOp`: the affine modular operator, Hermitian, linear in `σ`,
  positive definite for faithful `σ` and `t ∈ [0,1]`.
-/

open Matrix Unitary Finset Kronecker
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ v A B : Matrix n n ℂ}

/-! ### Vectorization -/

/-- The Hilbert–Schmidt vectorization of a matrix. -/
def vecM (v : Matrix n n ℂ) : n × n → ℂ := fun p => v p.1 p.2

omit [DecidableEq n] in
/-- The kron action on vectorized matrices:
`(A ⊗ B) vec X = vec (A X Bᵀ)`. -/
theorem vecM_kron_mulVec (A B X : Matrix n n ℂ) :
    (A ⊗ₖ B) *ᵥ vecM X = vecM (A * X * Bᵀ) := by
  funext p
  rcases p with ⟨i, j⟩
  simp only [Matrix.mulVec, dotProduct, vecM, Matrix.kronecker_apply,
    Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

omit [Fintype n] [DecidableEq n] in
theorem vecM_sum_smul {ι : Type*} [Fintype ι] (lam : ι → ℝ)
    (vs : ι → Matrix n n ℂ) :
    vecM (∑ j, lam j • vs j) = ∑ j, (lam j : ℂ) • vecM (vs j) := by
  funext p
  simp [vecM, Matrix.sum_apply, Matrix.smul_apply, Finset.sum_apply,
    Pi.smul_apply, Complex.real_smul]

/-! ### Star of a Kronecker product -/

omit [Fintype n] [DecidableEq n] in
theorem star_kron (A B : Matrix n n ℂ) :
    star (A ⊗ₖ B) = star A ⊗ₖ star B := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.star_apply, Matrix.kronecker_apply, star_mul']

/-! ### The conjugate unitary leg -/

omit [Fintype n] [DecidableEq n] in
theorem star_conj_transpose (U : Matrix n n ℂ) :
    star ((star U)ᵀ) = Uᵀ := by
  ext i j
  simp [Matrix.star_apply, Matrix.transpose_apply]

theorem conj_transpose_unitary_left {U : Matrix n n ℂ}
    (hU : star U * U = 1) : star ((star U)ᵀ) * (star U)ᵀ = 1 := by
  rw [star_conj_transpose, ← Matrix.transpose_mul, ← Matrix.transpose_one]
  congr 1

theorem conj_transpose_unitary_right {U : Matrix n n ℂ}
    (hU : star U * U = 1) : (star U)ᵀ * star ((star U)ᵀ) = 1 :=
  mul_eq_one_comm.mp (conj_transpose_unitary_left hU)

/-! ### The affine modular operator -/

/-- **The affine modular operator**
`M_t(σ) = t·(σ ⊗ 1) + (1−t)·(1 ⊗ σᵀ)`. -/
noncomputable def affineOp (σ : Matrix n n ℂ) (t : ℝ) :
    Matrix (n × n) (n × n) ℂ :=
  t • (σ ⊗ₖ (1 : Matrix n n ℂ)) +
    (1 - t) • ((1 : Matrix n n ℂ) ⊗ₖ σᵀ)

theorem real_smul_isHermitian' {N : Type*} {M : Matrix N N ℂ} (c : ℝ)
    (hM : M.IsHermitian) : (c • M).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, star_trivial, hM.eq]

omit [Fintype n] in
theorem affineOp_isHermitian (hσ : σ.IsHermitian) (t : ℝ) :
    (affineOp σ t).IsHermitian :=
  (real_smul_isHermitian' t (kronR_isHermitian hσ)).add
    (real_smul_isHermitian' (1 - t)
      (kron_one_isHermitian (transpose_isHermitian hσ)))

omit [Fintype n] in
/-- Linearity of the affine modular operator in the state. -/
theorem affineOp_linear {ι : Type*} [Fintype ι] (lam : ι → ℝ)
    (σs : ι → Matrix n n ℂ) (t : ℝ) :
    ∑ j, lam j • affineOp (σs j) t = affineOp (∑ j, lam j • σs j) t := by
  unfold affineOp
  simp only [smul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [kronR_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [kronR_smul]
    exact smul_comm _ _ _
  · rw [Matrix.transpose_sum,
      show (∑ j, (lam j • σs j)ᵀ) = ∑ j, lam j • (σs j)ᵀ from
        Finset.sum_congr rfl fun j _ => Matrix.transpose_smul _ _,
      kron_one_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [kron_one_smul]
    exact smul_comm _ _ _

/-! ### Positivity -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
theorem posDef_smul_real_pos {N : Type*} [Fintype N]
    {M : Matrix N N ℂ} {c : ℝ} (hc : 0 < c) (hM : M.PosDef) :
    (c • M).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨real_smul_isHermitian' c hM.1, fun x hx => ?_⟩
  have h1 : (c • M) *ᵥ x = (c : ℂ) • (M *ᵥ x) := real_smul_mulVec c M x
  rw [h1, dotProduct_smul, smul_eq_mul]
  have h2 : (0 : ℂ) < star x ⬝ᵥ (M *ᵥ x) :=
    (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hx
  calc (0 : ℂ) = (c : ℂ) * 0 := by ring
    _ < (c : ℂ) * (star x ⬝ᵥ (M *ᵥ x)) := by
        refine mul_lt_mul_of_pos_left h2 ?_
        exact_mod_cast hc

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
theorem posDef_add_psd {N : Type*} [Fintype N]
    {M M' : Matrix N N ℂ} (hM : M.PosDef) (hM' : M'.PosSemidef) :
    (M + M').PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hM.1.add hM'.1, fun x hx => ?_⟩
  rw [Matrix.add_mulVec, dotProduct_add]
  exact add_pos_of_pos_of_nonneg
    ((Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hx)
    (hM'.dotProduct_mulVec_nonneg x)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
omit [DecidableEq n] in
theorem transpose_posDef (hσ : σ.PosDef) : (σᵀ).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨transpose_isHermitian hσ.1, fun x hx => ?_⟩
  have hswap : star x ⬝ᵥ (σᵀ *ᵥ x) =
      star (star x) ⬝ᵥ (σ *ᵥ star x) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply,
      Pi.star_apply, star_star, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hswap]
  refine (Matrix.posDef_iff_dotProduct_mulVec.mp hσ).2 fun h0 => hx ?_
  funext i
  have := congrFun h0 i
  simp only [Pi.star_apply, Pi.zero_apply] at this ⊢
  rw [show x i = star (star (x i)) from (star_star _).symm, this, star_zero]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
theorem one_kron_posDef {C : Matrix n n ℂ} (hC : C.PosDef) :
    ((1 : Matrix n n ℂ) ⊗ₖ C).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨kron_one_isHermitian hC.1, fun x hx => ?_⟩
  have hx' : x = vecM (Matrix.of fun i j => x (i, j)) := by
    funext p
    rfl
  have hslice : star x ⬝ᵥ (((1 : Matrix n n ℂ) ⊗ₖ C) *ᵥ x) =
      ∑ i, star (fun b => x (i, b)) ⬝ᵥ (C *ᵥ fun b => x (i, b)) := by
    conv_lhs => rw [hx', vecM_kron_mulVec, Matrix.one_mul]
    simp only [dotProduct, vecM, Fintype.sum_prod_type, Pi.star_apply,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hslice]
  obtain ⟨i0, hi0⟩ : ∃ i0, (fun b => x (i0, b)) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hx
    funext p
    have := congrFun (hall p.1) p.2
    simpa using this
  have hpos : (0 : ℂ) < star (fun b => x (i0, b)) ⬝ᵥ
      (C *ᵥ fun b => x (i0, b)) :=
    (Matrix.posDef_iff_dotProduct_mulVec.mp hC).2 hi0
  have hnn : ∀ i ∈ Finset.univ, (0 : ℂ) ≤ star (fun b => x (i, b)) ⬝ᵥ
      (C *ᵥ fun b => x (i, b)) := fun i _ =>
    hC.posSemidef.dotProduct_mulVec_nonneg _
  exact Finset.sum_pos' hnn ⟨i0, Finset.mem_univ i0, hpos⟩

set_option maxHeartbeats 800000 in -- endpoint case split
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Positivity of the affine modular operator** for faithful `σ` and
`t ∈ [0,1]`. -/
theorem affineOp_posDef (hσ : σ.PosDef) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : (affineOp σ t).PosDef := by
  unfold affineOp
  rcases eq_or_lt_of_le ht0 with h0 | hpos
  · rw [← h0]
    rw [zero_smul, zero_add, sub_zero, one_smul]
    exact one_kron_posDef (transpose_posDef hσ)
  · refine posDef_add_psd (posDef_smul_real_pos hpos (kronR_posDef hσ)) ?_
    exact posSemidef_smul_real (by linarith)
      (one_kron_posSemidef (transpose_posSemidef hσ.posSemidef))

end QRE
end NCG
