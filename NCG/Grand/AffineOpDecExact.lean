/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.AffineOpExact

/-!
# Diagonalization of the affine modular operator

Step (B3d) of the BKM programme for `cor:accepted-BKM-loss` (QS.5): the
affine modular operator diagonalizes in the doubled eigenbasis
`E = U ⊗ conj U`,

`M_t(σ) = E · diag(t·qᵢ + (1−t)·qⱼ) · E^*`,

and its spectral inverse produces the **t-quadratic form**

`tQuad σ v t = Σᵢⱼ |v̂ᵢⱼ|² (t·qᵢ + (1−t)·qⱼ)⁻¹`.

* `eigU`: the doubled eigenleg, unitary;
* `affineOp_dec`: the diagonalization;
* `invMat_affineOp`: the spectral inverse in closed form;
* `tQuad_eq_sum`: **the boxed spectral formula**.
-/

open Matrix Unitary Finset Kronecker
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ v : Matrix n n ℂ}

/-! ### Adjoint transfer and diagonal quadratics -/

theorem adjoint_dot {N : Type*} [Fintype N] (E : Matrix N N ℂ)
    (x y : N → ℂ) :
    star x ⬝ᵥ (E *ᵥ y) = star (star E *ᵥ x) ⬝ᵥ y := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum,
    star_mul', Matrix.star_apply, star_star, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

theorem diag_quad_re {N : Type*} [Fintype N] [DecidableEq N]
    (d : N → ℝ) (w : N → ℂ) :
    (star w ⬝ᵥ (diagonal (fun p => ((d p : ℝ) : ℂ)) *ᵥ w)).re =
      ∑ p, Complex.normSq (w p) * d p := by
  rw [show star w ⬝ᵥ (diagonal (fun p => ((d p : ℝ) : ℂ)) *ᵥ w) =
      ∑ p, ((Complex.normSq (w p) * d p : ℝ) : ℂ) from ?_]
  · rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    exact Complex.ofReal_re _
  · simp only [dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [diag_mulVec_apply, Complex.star_def]
    have hz : (starRingEnd ℂ) (w p) * w p =
        ((Complex.normSq (w p) : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj]
    calc (starRingEnd ℂ) (w p) * (((d p : ℝ) : ℂ) * w p)
        = ((starRingEnd ℂ) (w p) * w p) * ((d p : ℝ) : ℂ) := by ring
      _ = ((Complex.normSq (w p) * d p : ℝ) : ℂ) := by
          rw [hz]
          push_cast
          ring

/-! ### The doubled eigenleg -/

/-- The doubled eigenleg `E = U ⊗ conj U`. -/
noncomputable def eigU (hσ : σ.IsHermitian) : Matrix (n × n) (n × n) ℂ :=
  (hσ.eigenvectorUnitary : Matrix n n ℂ) ⊗ₖ
    ((star (hσ.eigenvectorUnitary : Matrix n n ℂ))ᵀ)

theorem eigU_star_mul (hσ : σ.IsHermitian) :
    star (eigU hσ) * eigU hσ = 1 := by
  unfold eigU
  rw [star_kron, ← Matrix.mul_kronecker_mul,
    star_mul_coe hσ.eigenvectorUnitary,
    conj_transpose_unitary_left (star_mul_coe hσ.eigenvectorUnitary)]
  exact Matrix.one_kronecker_one

theorem eigU_mul_star (hσ : σ.IsHermitian) :
    eigU hσ * star (eigU hσ) = 1 :=
  mul_eq_one_comm.mp (eigU_star_mul hσ)

/-! ### Diagonalization -/

/-- The affine eigenvalue diagonal. -/
noncomputable def affineDiag (hσ : σ.IsHermitian) (t : ℝ) :
    Matrix (n × n) (n × n) ℂ :=
  diagonal fun p =>
    ((t * hσ.eigenvalues p.1 + (1 - t) * hσ.eigenvalues p.2 : ℝ) : ℂ)

set_option maxHeartbeats 1600000 in -- kron leg assembly
/-- **Diagonalization of the affine modular operator**:
`M_t(σ) = E · diag(t·qᵢ + (1−t)·qⱼ) · E^*`. -/
theorem affineOp_dec (hσ : σ.IsHermitian) (t : ℝ) :
    affineOp σ t = eigU hσ * affineDiag hσ t * star (eigU hσ) := by
  set U : Matrix n n ℂ := (hσ.eigenvectorUnitary : Matrix n n ℂ)
    with hU
  set D : Matrix n n ℂ :=
    diagonal (RCLike.ofReal ∘ hσ.eigenvalues) with hD
  have hdec : σ = U * D * star U := by
    have h := hσ.spectral_theorem
    rw [conjStarAlgAut_apply] at h
    exact h
  have hσT : σᵀ = (star U)ᵀ * D * star ((star U)ᵀ) := by
    rw [star_conj_transpose]
    conv_lhs => rw [hdec]
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    rw [hD, Matrix.diagonal_transpose]
    rw [Matrix.mul_assoc]
  have h1 : eigU hσ * (D ⊗ₖ (1 : Matrix n n ℂ)) * star (eigU hσ) =
      σ ⊗ₖ (1 : Matrix n n ℂ) := by
    unfold eigU
    rw [star_kron, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    rw [← hU]
    rw [Matrix.mul_one,
      conj_transpose_unitary_right (star_mul_coe hσ.eigenvectorUnitary),
      ← hdec]
  have h2 : eigU hσ * ((1 : Matrix n n ℂ) ⊗ₖ D) * star (eigU hσ) =
      (1 : Matrix n n ℂ) ⊗ₖ σᵀ := by
    unfold eigU
    rw [star_kron, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    rw [← hU]
    rw [Matrix.mul_one, coe_mul_star hσ.eigenvectorUnitary, ← hσT]
  unfold affineOp
  rw [← h1, ← h2]
  have hsmul : ∀ (c : ℝ) (A : Matrix (n × n) (n × n) ℂ),
      c • (eigU hσ * A * star (eigU hσ)) =
        eigU hσ * (c • A) * star (eigU hσ) := by
    intro c A
    rw [← Matrix.smul_mul, ← Matrix.mul_smul]
  rw [hsmul, hsmul, ← Matrix.add_mul, ← Matrix.mul_add]
  have hdd : t • (D ⊗ₖ (1 : Matrix n n ℂ)) +
      (1 - t) • ((1 : Matrix n n ℂ) ⊗ₖ D) = affineDiag hσ t := by
    ext p q
    rcases eq_or_ne p q with rfl | hpq
    · simp only [Matrix.add_apply, Matrix.smul_apply,
        Matrix.kroneckerMap_apply, Matrix.one_apply_eq, affineDiag,
        Matrix.diagonal_apply_eq, hD, Function.comp_apply,
        Complex.real_smul]
      simp only [show ∀ x : ℝ, RCLike.ofReal (K := ℂ) x =
        Complex.ofReal x from fun _ => rfl]
      push_cast
      ring
    · have hcase : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
        by_contra hboth
        push Not at hboth
        exact hpq (Prod.ext hboth.1 hboth.2)
      simp only [Matrix.add_apply, Matrix.smul_apply,
        Matrix.kroneckerMap_apply, affineDiag,
        Matrix.diagonal_apply_ne _ hpq, hD, Complex.real_smul]
      rcases hcase with hc | hc
      · rw [Matrix.diagonal_apply_ne _ hc, Matrix.one_apply_ne hc]
        ring
      · rw [Matrix.diagonal_apply_ne _ hc, Matrix.one_apply_ne hc]
        ring
  rw [hdd]

/-! ### The spectral inverse -/

/-- The inverse affine eigenvalue diagonal. -/
noncomputable def affineDiagInv (hσ : σ.IsHermitian) (t : ℝ) :
    Matrix (n × n) (n × n) ℂ :=
  diagonal fun p =>
    (((t * hσ.eigenvalues p.1 + (1 - t) * hσ.eigenvalues p.2)⁻¹ : ℝ) : ℂ)

theorem affineDiag_mul_inv (hσp : σ.PosDef) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    affineDiag hσp.1 t * affineDiagInv hσp.1 t = 1 := by
  unfold affineDiag affineDiagInv
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (1 : Matrix (n × n) (n × n) ℂ) =
    diagonal (fun _ => (1 : ℂ)) from (Matrix.diagonal_one).symm]
  congr 1
  funext p
  have hpos : 0 < t * hσp.1.eigenvalues p.1 +
      (1 - t) * hσp.1.eigenvalues p.2 :=
    affine_pos (hσp.eigenvalues_pos p.1) (hσp.eigenvalues_pos p.2)
      ht0 ht1
  push_cast
  rw [mul_inv_cancel₀]
  exact_mod_cast hpos.ne'

set_option maxHeartbeats 1600000 in -- inverse uniqueness chain
/-- **The spectral inverse of the affine modular operator**. -/
theorem invMat_affineOp (hσp : σ.PosDef) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    invMat (affineOp_isHermitian hσp.1 t) =
      eigU hσp.1 * affineDiagInv hσp.1 t * star (eigU hσp.1) := by
  set C : Matrix (n × n) (n × n) ℂ :=
    eigU hσp.1 * affineDiagInv hσp.1 t * star (eigU hσp.1) with hC
  have hMC : affineOp σ t * C = 1 := by
    rw [affineOp_dec hσp.1 t, hC]
    calc (eigU hσp.1 * affineDiag hσp.1 t * star (eigU hσp.1)) *
          (eigU hσp.1 * affineDiagInv hσp.1 t * star (eigU hσp.1))
        = eigU hσp.1 * affineDiag hσp.1 t *
            (star (eigU hσp.1) * eigU hσp.1) *
            affineDiagInv hσp.1 t * star (eigU hσp.1) := by
          simp only [Matrix.mul_assoc]
      _ = eigU hσp.1 *
            (affineDiag hσp.1 t * affineDiagInv hσp.1 t) *
            star (eigU hσp.1) := by
          rw [eigU_star_mul]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by
          rw [affineDiag_mul_inv hσp ht0 ht1, Matrix.mul_one,
            eigU_mul_star]
  have hMi : affineOp σ t * invMat (affineOp_isHermitian hσp.1 t) = 1 :=
    mul_invMat (affineOp_posDef hσp ht0 ht1)
  calc invMat (affineOp_isHermitian hσp.1 t)
      = invMat (affineOp_isHermitian hσp.1 t) * (affineOp σ t * C) := by
        rw [hMC, Matrix.mul_one]
    _ = (invMat (affineOp_isHermitian hσp.1 t) * affineOp σ t) * C := by
        simp only [Matrix.mul_assoc]
    _ = C := by
        rw [invMat_mul (affineOp_posDef hσp ht0 ht1), Matrix.one_mul]

/-! ### The t-quadratic form -/

/-- **The t-quadratic form** of the affine kernel. -/
noncomputable def tQuad (hσ : σ.IsHermitian) (v : Matrix n n ℂ)
    (t : ℝ) : ℝ :=
  (star (vecM v) ⬝ᵥ
    (invMat (affineOp_isHermitian hσ t) *ᵥ vecM v)).re

/-- The doubled eigenleg maps `vec v` to `vec v̂`. -/
theorem star_eigU_mulVec (hσ : σ.IsHermitian) (v : Matrix n n ℂ) :
    star (eigU hσ) *ᵥ vecM v = vecM (tangentIn hσ v) := by
  unfold eigU tangentIn
  rw [star_kron, vecM_kron_mulVec]
  congr 1
  rw [star_conj_transpose, Matrix.transpose_transpose]

set_option maxHeartbeats 1600000 in -- spectral collapse
/-- **The spectral formula of the t-quadratic form**:
`tQuad σ v t = Σᵢⱼ |v̂ᵢⱼ|² (t·qᵢ + (1−t)·qⱼ)⁻¹`. -/
theorem tQuad_eq_sum (hσp : σ.PosDef) (v : Matrix n n ℂ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    tQuad hσp.1 v t =
      ∑ i, ∑ j, Complex.normSq (tangentIn hσp.1 v i j) *
        (t * hσp.1.eigenvalues i + (1 - t) * hσp.1.eigenvalues j)⁻¹ := by
  unfold tQuad
  rw [invMat_affineOp hσp ht0 ht1]
  have hmove : star (vecM v) ⬝ᵥ
      ((eigU hσp.1 * affineDiagInv hσp.1 t * star (eigU hσp.1)) *ᵥ
        vecM v) =
      star (star (eigU hσp.1) *ᵥ vecM v) ⬝ᵥ
        (affineDiagInv hσp.1 t *ᵥ (star (eigU hσp.1) *ᵥ vecM v)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [adjoint_dot]
  rw [hmove, star_eigU_mulVec]
  unfold affineDiagInv
  rw [diag_quad_re
    (fun p => (t * hσp.1.eigenvalues p.1 +
      (1 - t) * hσp.1.eigenvalues p.2)⁻¹) (vecM (tangentIn hσp.1 v))]
  rw [Fintype.sum_prod_type]
  rfl

end QRE
end NCG
