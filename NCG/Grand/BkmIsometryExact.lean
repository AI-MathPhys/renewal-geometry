/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.BkmFormExact

/-!
# Isometry invariance of the BKM integral

Step (B4a) of the BKM programme for `cor:accepted-BKM-loss` (QS.5): the
doubled isometry `W = V ⊗ conj V` **intertwines** the affine modular
operators,

`M_t(VσV^*) · W = W · M_t(σ)`,

so the junk spectral inverse transports through the polynomial calculus
with no support conditions, and the affine quadratic forms — hence the
BKM integral — are isometry invariant.

* `vecM_kron_mulVec'`: the rectangular vectorized kron action;
* `affineOp_intertwine`: the boxed intertwining;
* `aeval_intertwine`, `invMat_intertwine`: polynomial transport;
* `tQuad_isometry`, `bkmIntegral_isometry`: **isometry invariance**.
-/

open Matrix Unitary Finset Kronecker Polynomial MeasureTheory
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Type*} [Fintype N] [DecidableEq N]
variable {σ v : Matrix n n ℂ}

/-! ### Rectangular vectorized kron action -/

omit [DecidableEq n] [Fintype N] [DecidableEq N] in
/-- The rectangular kron action on vectorized matrices. -/
theorem vecM_kron_mulVec' (A B : Matrix N n ℂ) (X : Matrix n n ℂ) :
    (A ⊗ₖ B) *ᵥ vecM X = vecM (A * X * Bᵀ) := by
  funext p
  rcases p with ⟨i, j⟩
  simp only [Matrix.mulVec, dotProduct, vecM, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

omit [Fintype n] [DecidableEq n] [Fintype N] [DecidableEq N] in
theorem conjTranspose_kron (A B : Matrix N n ℂ) :
    (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    star_mul']

/-! ### The doubled isometry -/

/-- The doubled isometry `W = V ⊗ conj V`. -/
def doubledIso (V : Matrix N n ℂ) : Matrix (N × N) (n × n) ℂ :=
  V ⊗ₖ ((Vᴴ)ᵀ)

omit [Fintype n] [DecidableEq n] [Fintype N] [DecidableEq N] in
theorem conjTranspose_conj_transpose (V : Matrix N n ℂ) :
    ((Vᴴ)ᵀ)ᴴ = Vᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]

omit [Fintype n] [DecidableEq N] in
theorem doubledIso_isometry {V : Matrix N n ℂ} (hV : Vᴴ * V = 1) :
    (doubledIso V)ᴴ * doubledIso V = 1 := by
  unfold doubledIso
  rw [conjTranspose_kron, ← Matrix.mul_kronecker_mul, hV]
  have hconj : ((Vᴴ)ᵀ)ᴴ * (Vᴴ)ᵀ = 1 := by
    rw [conjTranspose_conj_transpose, ← Matrix.transpose_mul, hV,
      Matrix.transpose_one]
  rw [hconj]
  exact Matrix.one_kronecker_one

/-! ### The intertwining -/

set_option maxHeartbeats 1600000 in -- leg intertwining
/-- **The affine intertwining**: `M_t(VσV^*) · W = W · M_t(σ)`. -/
theorem affineOp_intertwine {V : Matrix N n ℂ} (hV : Vᴴ * V = 1)
    (_hσ : σ.IsHermitian) (t : ℝ) :
    affineOp (V * σ * Vᴴ) t * doubledIso V =
      doubledIso V * affineOp σ t := by
  have hXV : (V * σ * Vᴴ) * V = V * σ := by
    rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  have hconjV : Vᵀ * (Vᴴ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hV, Matrix.transpose_one]
  have hXT : (V * σ * Vᴴ)ᵀ * (Vᴴ)ᵀ = (Vᴴ)ᵀ * σᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    calc (Vᴴ)ᵀ * (σᵀ * Vᵀ) * (Vᴴ)ᵀ
        = (Vᴴ)ᵀ * σᵀ * (Vᵀ * (Vᴴ)ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = (Vᴴ)ᵀ * σᵀ := by
          rw [hconjV, Matrix.mul_one]
  unfold affineOp doubledIso
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_smul]
  congr 1
  · congr 1
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    rw [hXV, Matrix.one_mul, Matrix.mul_one]
  · congr 1
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    rw [hXT, Matrix.one_mul, Matrix.mul_one]

/-! ### Polynomial transport -/

set_option maxHeartbeats 1600000 in -- power induction
/-- Intertwining passes to polynomial evaluation. -/
theorem aeval_intertwine {M' : Matrix (N × N) (N × N) ℂ}
    {M : Matrix (n × n) (n × n) ℂ} {W : Matrix (N × N) (n × n) ℂ}
    (hint : M' * W = W * M) (P : Polynomial ℝ) :
    Polynomial.aeval M' P * W = W * Polynomial.aeval M P := by
  have hpow : ∀ k : ℕ, M' ^ k * W = W * M ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.one_mul, Matrix.mul_one]
    | succ k ih =>
        rw [pow_succ, pow_succ, Matrix.mul_assoc, hint,
          ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, hpow k]

/-- The junk spectral inverse transports along the intertwining. -/
theorem invMat_intertwine {M' : Matrix (N × N) (N × N) ℂ}
    {M : Matrix (n × n) (n × n) ℂ} {W : Matrix (N × N) (n × n) ℂ}
    (hM' : M'.IsHermitian) (hM : M.IsHermitian)
    (hint : M' * W = W * M) :
    invMat hM' * W = W * invMat hM := by
  obtain ⟨P, hPval⟩ := exists_interpolating' (fun x => x⁻¹)
    ((Finset.image hM'.eigenvalues Finset.univ) ∪
      Finset.image hM.eigenvalues Finset.univ)
  have h1 : invMat hM' = Polynomial.aeval M' P :=
    matFun_eq_aeval hM' _ P fun i => hPval _
      (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have h2 : invMat hM = Polynomial.aeval M P :=
    matFun_eq_aeval hM _ P fun i => hPval _
      (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  rw [h1, h2]
  exact aeval_intertwine hint P

/-! ### Isometry invariance of the affine forms -/

omit [DecidableEq n] [Fintype N] [DecidableEq N] in
theorem conj_isHermitian' {V : Matrix N n ℂ} {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : (V * A * Vᴴ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]

omit [DecidableEq n] [DecidableEq N] in
/-- Rectangular adjoint transfer. -/
theorem adjoint_dot_rect (E : Matrix N n ℂ) (x : N → ℂ) (y : n → ℂ) :
    star x ⬝ᵥ (E *ᵥ y) = star (Eᴴ *ᵥ x) ⬝ᵥ y := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum,
    star_mul', Matrix.conjTranspose_apply, star_star, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

set_option maxHeartbeats 1600000 in -- isometry transport assembly
/-- **Isometry invariance of the affine quadratic form**:
`tQuad(VσV^*, VvV^*, t) = tQuad(σ, v, t)`. -/
theorem tQuad_isometry {V : Matrix N n ℂ} (hV : Vᴴ * V = 1)
    (hσ : σ.IsHermitian) (v : Matrix n n ℂ) (t : ℝ)
    (hσ' : (V * σ * Vᴴ).IsHermitian) :
    tQuad hσ' (V * v * Vᴴ) t = tQuad hσ v t := by
  unfold tQuad
  have hWW := doubledIso_isometry hV
  have hvec : doubledIso V *ᵥ vecM v = vecM (V * v * Vᴴ) := by
    unfold doubledIso
    rw [vecM_kron_mulVec', Matrix.transpose_transpose]
  have hint := affineOp_intertwine hV hσ t
  have hinv := invMat_intertwine (affineOp_isHermitian hσ' t)
    (affineOp_isHermitian hσ t) hint
  rw [← hvec]
  rw [Matrix.mulVec_mulVec, hinv, ← Matrix.mulVec_mulVec]
  rw [adjoint_dot_rect (doubledIso V) (doubledIso V *ᵥ vecM v)
    (invMat (affineOp_isHermitian hσ t) *ᵥ vecM v)]
  rw [Matrix.mulVec_mulVec, hWW, Matrix.one_mulVec]

/-! ### The BKM integral functional -/

/-- The BKM integral functional, defined for arbitrary Hermitian base
through the junk spectral inverse. -/
noncomputable def bkmIntegral (hσ : σ.IsHermitian)
    (v : Matrix n n ℂ) : ℝ :=
  ∫ t in (0:ℝ)..1, tQuad hσ v t

/-- On faithful bases the BKM integral is the BKM form. -/
theorem bkmIntegral_eq_form (hσp : σ.PosDef) (v : Matrix n n ℂ) :
    bkmIntegral hσp.1 v = bkmForm hσp.1 v := by
  unfold bkmIntegral
  rw [bkmForm_eq_integral hσp v]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
  exact tQuad_eq_sum hσp v ht.1 ht.2

/-- **Isometry invariance of the BKM integral**. -/
theorem bkmIntegral_isometry {V : Matrix N n ℂ} (hV : Vᴴ * V = 1)
    (hσ : σ.IsHermitian) (v : Matrix n n ℂ)
    (hσ' : (V * σ * Vᴴ).IsHermitian) :
    bkmIntegral hσ' (V * v * Vᴴ) = bkmIntegral hσ v := by
  unfold bkmIntegral
  refine intervalIntegral.integral_congr fun t _ => ?_
  exact tQuad_isometry hV hσ v t hσ'

end QRE
end NCG
