/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.BkmKernelExact

/-!
# Joint convexity of the inverse quadratic form

Step (B3a) of the BKM programme for `cor:accepted-BKM-loss` (QS.5): the
classical Schur-complement lemma.  For positive definite `P` the block
matrix `[[P, x], [x^*, x^* P⁻¹ x]]` is the Gram matrix of
`[√P, √P⁻¹ x; 0, 0]`, hence PSD; reading the corner of a PSD mixture of
such certificates gives **joint convexity of `(P, x) ↦ x^* P⁻¹ x`** —
the engine of the affine-kernel representation of the BKM metric.

* `invMat`: the spectral inverse, with the two-sided inverse laws;
* `quad_block_posSemidef`: the Gram certificate;
* `corner_ge_quad`: the Schur corner reading;
* `quadForm_convex`: **joint convexity**.
-/

open Matrix Unitary Finset
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {N : Type*} [Fintype N] [DecidableEq N]
variable {P S : Matrix N N ℂ}

/-! ### The spectral inverse -/

/-- The inverse through the spectral calculus (junk `0⁻¹ = 0`). -/
noncomputable def invMat (hS : S.IsHermitian) : Matrix N N ℂ :=
  matFun hS fun x => x⁻¹

theorem invMat_isHermitian (hS : S.IsHermitian) :
    (invMat hS).IsHermitian :=
  Petz.matFun_isHermitian hS _

theorem mul_invMat (hP : P.PosDef) : P * invMat hP.1 = 1 := by
  have hid : P * invMat hP.1 = matFun hP.1 id * invMat hP.1 := by
    rw [Petz.matFun_id hP.1]
  rw [hid]
  unfold invMat
  rw [matFun_mul]
  have h1 : matFun hP.1 (fun x => id x * x⁻¹) =
      matFun hP.1 (fun _ => 1) := by
    refine Petz.matFun_congr hP.1 _ _ fun i => ?_
    simp only [id_eq]
    exact mul_inv_cancel₀ (hP.eigenvalues_pos i).ne'
  rw [h1, Petz.matFun_one]

theorem invMat_mul (hP : P.PosDef) : invMat hP.1 * P = 1 :=
  mul_eq_one_comm.mp (mul_invMat hP)

theorem sqrt_mul_invSqrt (hP : P.PosDef) :
    Petz.sqrtMat hP.1 * Petz.invSqrtMat hP.1 = 1 := by
  unfold Petz.sqrtMat Petz.invSqrtMat
  rw [matFun_mul]
  have h1 : matFun hP.1 (fun x => Real.sqrt x * (Real.sqrt x)⁻¹) =
      matFun hP.1 (fun _ => 1) := by
    refine Petz.matFun_congr hP.1 _ _ fun i => ?_
    have hpos : 0 < Real.sqrt (hP.1.eigenvalues i) :=
      Real.sqrt_pos.mpr (hP.eigenvalues_pos i)
    exact mul_inv_cancel₀ hpos.ne'
  rw [h1, Petz.matFun_one]

theorem invSqrt_mul_sqrt (hP : P.PosDef) :
    Petz.invSqrtMat hP.1 * Petz.sqrtMat hP.1 = 1 :=
  mul_eq_one_comm.mp (sqrt_mul_invSqrt hP)

theorem invSqrt_mul_invSqrt (hP : P.PosDef) :
    Petz.invSqrtMat hP.1 * Petz.invSqrtMat hP.1 = invMat hP.1 := by
  unfold Petz.invSqrtMat invMat
  rw [matFun_mul]
  refine Petz.matFun_congr hP.1 _ _ fun i => ?_
  have hnn : 0 ≤ hP.1.eigenvalues i := (hP.eigenvalues_pos i).le
  rw [← mul_inv, Real.mul_self_sqrt hnn]

/-! ### Column vectors and quadratic entries -/

/-- A vector as an `N × Unit` column matrix. -/
def colVec (x : N → ℂ) : Matrix N Unit ℂ :=
  Matrix.of fun i _ => x i

omit [Fintype N] [DecidableEq N] in
theorem colVec_smul (c : ℝ) (x : N → ℂ) :
    colVec (fun i => (c : ℂ) * x i) = c • colVec x := by
  ext i u
  simp [colVec, Matrix.smul_apply, Complex.real_smul]

omit [DecidableEq N] in
/-- The quadratic entry `(x^* M x)()() = ⟨x, M x⟩`. -/
theorem colVec_quad (M : Matrix N N ℂ) (x : N → ℂ) (u u' : Unit) :
    ((colVec x)ᴴ * M * colVec x) u u' = star x ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, colVec,
    Matrix.of_apply, dotProduct, Matrix.mulVec, Pi.star_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### The Gram certificate -/

set_option maxHeartbeats 1600000 in -- block Gram bookkeeping
/-- **The Schur–Gram certificate**: for faithful `P`,
`[[P, x],[x^*, x^* P⁻¹ x]]` is PSD. -/
theorem quad_block_posSemidef (hP : P.PosDef) (x : N → ℂ) :
    (Matrix.fromBlocks P (colVec x) (colVec x)ᴴ
      ((colVec x)ᴴ * invMat hP.1 * colVec x)).PosSemidef := by
  have hsqrth : (Petz.sqrtMat hP.1).IsHermitian := by
    unfold Petz.sqrtMat
    exact Petz.matFun_isHermitian hP.1 _
  have hinvsqrth : (Petz.invSqrtMat hP.1).IsHermitian := by
    unfold Petz.invSqrtMat
    exact Petz.matFun_isHermitian hP.1 _
  set C : Matrix (N ⊕ Unit) (N ⊕ Unit) ℂ :=
    Matrix.fromBlocks (Petz.sqrtMat hP.1)
      (Petz.invSqrtMat hP.1 * colVec x) 0 0 with hC
  have hCC : Cᴴ * C =
      Matrix.fromBlocks P (colVec x) (colVec x)ᴴ
        ((colVec x)ᴴ * invMat hP.1 * colVec x) := by
    rw [hC, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, add_zero]
      rw [hsqrth.eq, Petz.sqrtMat_mul_self hP.posSemidef]
    · simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, add_zero]
      rw [hsqrth.eq, ← Matrix.mul_assoc, sqrt_mul_invSqrt hP,
        Matrix.one_mul]
    · simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, add_zero]
      rw [Matrix.conjTranspose_mul, hinvsqrth.eq, Matrix.mul_assoc,
        invSqrt_mul_sqrt hP, Matrix.mul_one]
    · simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, add_zero]
      rw [Matrix.conjTranspose_mul, hinvsqrth.eq]
      rw [show (colVec x)ᴴ * Petz.invSqrtMat hP.1 *
          (Petz.invSqrtMat hP.1 * colVec x) =
          (colVec x)ᴴ * (Petz.invSqrtMat hP.1 *
            Petz.invSqrtMat hP.1) * colVec x from by
        simp only [Matrix.mul_assoc]]
      rw [invSqrt_mul_invSqrt hP]
  rw [← hCC]
  exact Matrix.posSemidef_conjTranspose_mul_self C

/-! ### The Schur corner reading -/

set_option maxHeartbeats 1600000 in -- corner extraction
/-- **The Schur corner**: a PSD block `[[P, x],[x^*, Q]]` with faithful
`P` forces `Re⟨x, P⁻¹x⟩ ≤ Re Q`. -/
theorem corner_ge_quad {Q : Matrix Unit Unit ℂ} (hP : P.PosDef)
    {x : N → ℂ}
    (hB : (Matrix.fromBlocks P (colVec x) (colVec x)ᴴ Q).PosSemidef) :
    (star x ⬝ᵥ (invMat hP.1 *ᵥ x)).re ≤ (Q () ()).re := by
  set u : N → ℂ := -(invMat hP.1 *ᵥ x) with hu
  set v : N ⊕ Unit → ℂ := Sum.elim u (fun _ => (1 : ℂ)) with hv
  have hq := hB.dotProduct_mulVec_nonneg v
  have hPu : P *ᵥ u = -x := by
    rw [hu, Matrix.mulVec_neg, Matrix.mulVec_mulVec, mul_invMat hP,
      Matrix.one_mulVec]
  have hsplit : star v ⬝ᵥ
      ((Matrix.fromBlocks P (colVec x) (colVec x)ᴴ Q) *ᵥ v) =
      (star u ⬝ᵥ (P *ᵥ u)) + (star u ⬝ᵥ x) + (star x ⬝ᵥ u) +
        Q () () := by
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, hv,
      Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Pi.star_apply, star_one, colVec,
      Matrix.of_apply, Matrix.conjTranspose_apply,
      Fintype.sum_unique, mul_one, one_mul]
    simp only [mul_add, Finset.sum_add_distrib]
    ring_nf
  rw [hsplit] at hq
  have hcancel : star u ⬝ᵥ (P *ᵥ u) + star u ⬝ᵥ x = 0 := by
    rw [hPu]
    have : star u ⬝ᵥ (-x) = -(star u ⬝ᵥ x) := by
      simp [dotProduct]
    rw [this]
    ring
  have hxu : star x ⬝ᵥ u = -(star x ⬝ᵥ (invMat hP.1 *ᵥ x)) := by
    rw [hu]
    simp [dotProduct, Finset.sum_neg_distrib]
  rw [show star u ⬝ᵥ (P *ᵥ u) + star u ⬝ᵥ x + star x ⬝ᵥ u + Q () () =
      (star u ⬝ᵥ (P *ᵥ u) + star u ⬝ᵥ x) + (star x ⬝ᵥ u + Q () ())
      from by ring, hcancel, zero_add, hxu] at hq
  have hre := Complex.le_def.mp hq
  simp only [Complex.zero_re, Complex.add_re, Complex.neg_re] at hre
  linarith [hre.1]

/-! ### Joint convexity -/

set_option maxHeartbeats 3200000 in -- convexity assembly
/-- **Joint convexity of the inverse quadratic form**: for probability
weights, faithful `Pⱼ` and vectors `xⱼ`,
`Re⟨x̄, P̄⁻¹ x̄⟩ ≤ Σ λⱼ Re⟨xⱼ, Pⱼ⁻¹ xⱼ⟩`. -/
theorem quadForm_convex {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ j, 0 ≤ lam j)
    {Pmat : ι → Matrix N N ℂ} {xvec : ι → N → ℂ}
    (hPj : ∀ j, (Pmat j).PosDef)
    (hPbar : (∑ j, lam j • Pmat j).PosDef) :
    (star (∑ j, (lam j : ℂ) • xvec j) ⬝ᵥ
      (invMat hPbar.1 *ᵥ ∑ j, (lam j : ℂ) • xvec j)).re ≤
      ∑ j, lam j *
        (star (xvec j) ⬝ᵥ (invMat (hPj j).1 *ᵥ xvec j)).re := by
  set xbar : N → ℂ := ∑ j, (lam j : ℂ) • xvec j with hxbar
  have hBsum : (Matrix.fromBlocks (∑ j, lam j • Pmat j) (colVec xbar)
      (colVec xbar)ᴴ
      (∑ j, lam j • ((colVec (xvec j))ᴴ * invMat (hPj j).1 *
        colVec (xvec j)))).PosSemidef := by
    have hsum_eq : Matrix.fromBlocks (∑ j, lam j • Pmat j)
        (colVec xbar) (colVec xbar)ᴴ
        (∑ j, lam j • ((colVec (xvec j))ᴴ * invMat (hPj j).1 *
          colVec (xvec j))) =
        ∑ j, lam j • Matrix.fromBlocks (Pmat j) (colVec (xvec j))
          (colVec (xvec j))ᴴ
          ((colVec (xvec j))ᴴ * invMat (hPj j).1 * colVec (xvec j)) := by
      ext p q
      rcases p with p | p <;> rcases q with q | q <;>
        simp [Matrix.fromBlocks, Matrix.sum_apply, Matrix.smul_apply,
          hxbar, colVec, Matrix.conjTranspose_apply, Finset.sum_apply,
          Pi.smul_apply, Complex.real_smul, star_sum]
    rw [hsum_eq]
    refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb)
      Matrix.PosSemidef.zero fun j _ => ?_
    exact posSemidef_smul_real (hlam j) (quad_block_posSemidef (hPj j) _)
  have hcorner := corner_ge_quad hPbar hBsum
  refine hcorner.trans (le_of_eq ?_)
  rw [Matrix.sum_apply]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, colVec_quad]
  rw [show ((lam j • (star (xvec j) ⬝ᵥ
      (invMat (hPj j).1 *ᵥ xvec j)) : ℂ)).re =
      lam j * (star (xvec j) ⬝ᵥ (invMat (hPj j).1 *ᵥ xvec j)).re from by
    rw [Complex.real_smul, Complex.mul_re]
    simp]

end QRE
end NCG
