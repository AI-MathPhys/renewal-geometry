/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.BkmIsometryExact

/-!
# The Schur convexity at singular data

Step (B4b) of the BKM programme for `cor:accepted-BKM-loss` (QS.5): the
Gram certificate `[[P, x],[x^*, x^* P⁻ x]]` survives at **singular** PSD
`P` when the vector is supported in the range, `Π x = x` for the support
projection `Π = P·P⁻` — exactly the condition the intertwining supplies
for the twirl members.  Reading the corner of a faithful mixture gives
joint convexity of the junk inverse quadratic form at PSD data.

* `supp_proj`: `P · P⁻` is the support projection, `√P·√P⁻ = P·P⁻`;
* `quad_block_posSemidef_psd`: the singular Gram certificate;
* `quadForm_convex_psd`: **joint convexity at supported PSD data**.
-/

open Matrix Unitary Finset
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {N : Type*} [Fintype N] [DecidableEq N]
variable {P : Matrix N N ℂ}

/-! ### Junk square-root products -/

theorem sqrt_mul_invSqrt_junk (hP : P.PosSemidef) :
    Petz.sqrtMat hP.1 * Petz.invSqrtMat hP.1 = P * invMat hP.1 := by
  unfold Petz.sqrtMat Petz.invSqrtMat invMat
  rw [matFun_mul]
  have hid : P * matFun hP.1 (fun x => x⁻¹) =
      matFun hP.1 id * matFun hP.1 (fun x => x⁻¹) := by
    rw [Petz.matFun_id hP.1]
  rw [hid, matFun_mul]
  refine Petz.matFun_congr hP.1 _ _ fun i => ?_
  simp only [id_eq]
  rcases eq_or_lt_of_le (hP.eigenvalues_nonneg i) with h0 | hpos
  · rw [← h0]
    simp
  · rw [mul_inv_cancel₀ (Real.sqrt_pos.mpr hpos).ne',
      mul_inv_cancel₀ hpos.ne']

theorem invSqrt_mul_invSqrt_junk (hP : P.PosSemidef) :
    Petz.invSqrtMat hP.1 * Petz.invSqrtMat hP.1 = invMat hP.1 := by
  unfold Petz.invSqrtMat invMat
  rw [matFun_mul]
  refine Petz.matFun_congr hP.1 _ _ fun i => ?_
  rcases eq_or_lt_of_le (hP.eigenvalues_nonneg i) with h0 | hpos
  · rw [← h0]
    simp
  · rw [← mul_inv, Real.mul_self_sqrt (hP.eigenvalues_nonneg i)]

/-! ### The singular Gram certificate -/

set_option maxHeartbeats 1600000 in -- junk Gram bookkeeping
/-- **The singular Schur–Gram certificate**: for PSD `P` and a vector
supported in its range (`P·P⁻ x = x`), the block
`[[P, x],[x^*, x^* P⁻ x]]` is PSD. -/
theorem quad_block_posSemidef_psd (hP : P.PosSemidef) {x : N → ℂ}
    (hsupp : (P * invMat hP.1) *ᵥ x = x) :
    (Matrix.fromBlocks P (colVec x) (colVec x)ᴴ
      ((colVec x)ᴴ * invMat hP.1 * colVec x)).PosSemidef := by
  have hsqrth : (Petz.sqrtMat hP.1).IsHermitian := by
    unfold Petz.sqrtMat
    exact Petz.matFun_isHermitian hP.1 _
  have hinvsqrth : (Petz.invSqrtMat hP.1).IsHermitian := by
    unfold Petz.invSqrtMat
    exact Petz.matFun_isHermitian hP.1 _
  have hsuppcol : Petz.sqrtMat hP.1 * (Petz.invSqrtMat hP.1 * colVec x) =
      colVec x := by
    rw [← Matrix.mul_assoc, sqrt_mul_invSqrt_junk hP]
    ext i u
    have h := congrFun hsupp i
    simp only [colVec, Matrix.of_apply, Matrix.mul_apply,
      Matrix.mulVec, dotProduct] at h ⊢
    exact h
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
      rw [hsqrth.eq, Petz.sqrtMat_mul_self hP]
    · simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, add_zero]
      rw [hsqrth.eq]
      exact hsuppcol
    · simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, add_zero]
      rw [Matrix.conjTranspose_mul, hinvsqrth.eq]
      calc (colVec x)ᴴ * Petz.invSqrtMat hP.1 * Petz.sqrtMat hP.1
          = ((Petz.sqrtMat hP.1 *
              (Petz.invSqrtMat hP.1 * colVec x))ᴴ) := by
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
              hsqrth.eq, hinvsqrth.eq]
        _ = (colVec x)ᴴ := by rw [hsuppcol]
    · simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, add_zero]
      rw [Matrix.conjTranspose_mul, hinvsqrth.eq]
      rw [show (colVec x)ᴴ * Petz.invSqrtMat hP.1 *
          (Petz.invSqrtMat hP.1 * colVec x) =
          (colVec x)ᴴ * (Petz.invSqrtMat hP.1 *
            Petz.invSqrtMat hP.1) * colVec x from by
        simp only [Matrix.mul_assoc]]
      rw [invSqrt_mul_invSqrt_junk hP]
  rw [← hCC]
  exact Matrix.posSemidef_conjTranspose_mul_self C

/-! ### Joint convexity at supported PSD data -/

set_option maxHeartbeats 3200000 in -- singular convexity assembly
/-- **Joint convexity of the junk inverse quadratic form at PSD data**:
for nonnegative weights, PSD `Pⱼ` with supported vectors `xⱼ`
(`Pⱼ·Pⱼ⁻ xⱼ = xⱼ`) and a faithful mixture,
`Re⟨x̄, P̄⁻¹ x̄⟩ ≤ Σ λⱼ Re⟨xⱼ, Pⱼ⁻ xⱼ⟩`. -/
theorem quadForm_convex_psd {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ j, 0 ≤ lam j)
    {Pmat : ι → Matrix N N ℂ} {xvec : ι → N → ℂ}
    (hPj : ∀ j, (Pmat j).PosSemidef)
    (hsupp : ∀ j, (Pmat j * invMat (hPj j).1) *ᵥ xvec j = xvec j)
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
    exact posSemidef_smul_real (hlam j)
      (quad_block_posSemidef_psd (hPj j) (hsupp j))
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
