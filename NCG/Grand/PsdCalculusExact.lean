/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.LoewnerSqrtExact
import NCG.Grand.RelEntropyKronExact

/-!
# The positive-semidefinite calculus toolkit

Step (D4b) of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: the helper layer for the matrix geometric
mean.

* `commute_matFun_right`: anything commuting with `S` commutes with `f(S)`
  (the spectral calculus is polynomial);
* `eq_zero_of_mulVec_eq_zero`: a matrix annihilating every vector is zero;
* `posSemidef_smul_real`: nonnegative real scalings preserve PSD;
* `schur_corner`: `[[1, Y],[Y, C]] ⪰ 0 → C − Y² ⪰ 0` — the Schur step by
  direct substitution `w := −Yv`;
* `posSemidef_sqrt_unique`: **uniqueness of the PSD square root**.
-/

open Matrix Unitary Finset
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {S P Q : Matrix n n ℂ}

/-! ### Commuting functional calculus -/

theorem commute_aeval_right {X : Matrix n n ℂ} (h : Commute X P)
    (Ppoly : Polynomial ℝ) :
    Commute X (Polynomial.aeval P Ppoly) := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Commute.sum_right _ _ _ fun k _ => ?_
  exact (h.pow_right k).smul_right _

theorem commute_matFun_right {X : Matrix n n ℂ} (hS : S.IsHermitian)
    (f : ℝ → ℝ) (h : Commute X S) : Commute X (matFun hS f) := by
  obtain ⟨Ppoly, hP⟩ := exists_interpolating' f
    (Finset.image hS.eigenvalues Finset.univ)
  rw [matFun_eq_aeval hS f Ppoly fun i => hP _
    (Finset.mem_image_of_mem _ (Finset.mem_univ i))]
  exact commute_aeval_right h Ppoly

/-! ### Matrix-zero criteria -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
theorem eq_zero_of_mulVec_eq_zero {M : Matrix n n ℂ}
    (h : ∀ v, M *ᵥ v = 0) : M = 0 := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  have h2 : (M *ᵥ Pi.single j 1) i = M i j := by
    simp [Matrix.mulVec]
  rw [h2] at h1
  simpa using h1

omit [DecidableEq n] in
theorem mulVec_self_dot_eq_zero {v : n → ℂ}
    (h : star v ⬝ᵥ v = 0) : v = 0 := by
  have hsum : ∑ i, Complex.normSq (v i) = 0 := by
    have hre := congrArg Complex.re h
    simp only [dotProduct, Pi.star_apply, Complex.re_sum,
      Complex.zero_re] at hre
    have hz : ∀ z : ℂ, (star z * z).re = Complex.normSq z := fun z => by
      rw [Complex.star_def, mul_comm, Complex.mul_conj]
      simp
    rw [← hre]
    exact Finset.sum_congr rfl fun i _ => (hz _).symm
  funext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    fun i _ => Complex.normSq_nonneg _).mp hsum i (Finset.mem_univ i)
  simpa using Complex.normSq_eq_zero.mp hi

/-! ### PSD closure properties -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
omit [DecidableEq n] in
theorem posSemidef_smul_real {c : ℝ} (hc : 0 ≤ c) (hP : P.PosSemidef) :
    (c • P).PosSemidef := by
  have hherm : (c • P).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, star_trivial, hP.1.eq]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
  have h := hP.dotProduct_mulVec_nonneg x
  rw [Complex.le_def] at h
  have h1 : 0 ≤ (star x ⬝ᵥ (P *ᵥ x)).re := by simpa using h.1
  have h2 : (star x ⬝ᵥ (P *ᵥ x)).im = 0 := by simpa using h.2.symm
  have hxp : star x ⬝ᵥ ((c • P) *ᵥ x) =
      (c : ℂ) * (star x ⬝ᵥ (P *ᵥ x)) := by
    have hmv : (c • P) *ᵥ x = c • (P *ᵥ x) := by
      funext i
      simp only [Matrix.mulVec, Matrix.smul_apply, Pi.smul_apply,
        dotProduct, Complex.real_smul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hmv, dotProduct_smul, Complex.real_smul]
  rw [hxp, Complex.le_def]
  constructor
  · rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
      zero_mul, sub_zero]
    exact mul_nonneg hc h1
  · rw [Complex.mul_im]
    simp [Complex.ofReal_re, Complex.ofReal_im, h2]

/-! ### The block corner (Schur step by substitution) -/

omit [Fintype n] [DecidableEq n] in
theorem star_sum_elim {a : n → ℂ} {b : n → ℂ} :
    star (Sum.elim a b) = Sum.elim (star a) (star b) := by
  funext i
  cases i <;> rfl

omit [DecidableEq n] in
theorem sum_elim_dot (a b c d : n → ℂ) :
    Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

set_option maxHeartbeats 800000 in -- block quadratic bookkeeping
/-- `[[1, Y],[Y, C]] ⪰ 0 → C − Y² ⪰ 0`, by evaluating the block quadratic
at `(−Yv, v)`. -/
theorem schur_corner {Y C : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hM : (Matrix.fromBlocks 1 Y Y C).PosSemidef) :
    (C - Y * Y).PosSemidef := by
  have hC : C.IsHermitian := by
    have h := hM.1
    unfold Matrix.IsHermitian at h ⊢
    rw [Matrix.fromBlocks_conjTranspose] at h
    have h22 := congrArg Matrix.toBlocks₂₂ h
    simpa [Matrix.toBlocks_fromBlocks₂₂] using h22
  have hherm : (C - Y * Y).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hY.eq, hC.eq]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun v => ?_
  have h := hM.dotProduct_mulVec_nonneg (Sum.elim (-(Y *ᵥ v)) v)
  rw [Matrix.fromBlocks_mulVec, star_sum_elim] at h
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h
  rw [sum_elim_dot] at h
  have hblock1 : (1 : Matrix n n ℂ) *ᵥ (-(Y *ᵥ v)) + Y *ᵥ v = 0 := by
    rw [Matrix.one_mulVec]
    exact neg_add_cancel _
  have hblock2 : Y *ᵥ (-(Y *ᵥ v)) + C *ᵥ v = (C - Y * Y) *ᵥ v := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.sub_mulVec]
    abel
  rw [hblock1, hblock2, dotProduct_zero, zero_add] at h
  exact h

/-! ### Uniqueness of the PSD square root -/

set_option maxHeartbeats 1600000 in -- commuting kernel decomposition
/-- **Uniqueness of the PSD square root**: a PSD matrix squaring to `P` is
the spectral square root of `P`. -/
theorem posSemidef_sqrt_unique (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (hQQ : Q * Q = P) : Q = Petz.sqrtMat hP.1 := by
  have hRP : (Petz.sqrtMat hP.1).PosSemidef := sqrtMat_posSemidef hP
  have hRR : Petz.sqrtMat hP.1 * Petz.sqrtMat hP.1 = P :=
    Petz.sqrtMat_mul_self hP
  have hQP : Commute Q P := by
    rw [← hQQ]
    exact (Commute.refl Q).mul_right (Commute.refl Q)
  have hQR : Commute Q (Petz.sqrtMat hP.1) :=
    commute_matFun_right hP.1 Real.sqrt hQP
  have hD0 : (Q - Petz.sqrtMat hP.1) * (Q + Petz.sqrtMat hP.1) = 0 := by
    have hexp : (Q - Petz.sqrtMat hP.1) * (Q + Petz.sqrtMat hP.1) =
        Q * Q - Petz.sqrtMat hP.1 * Petz.sqrtMat hP.1 +
          (Q * Petz.sqrtMat hP.1 - Petz.sqrtMat hP.1 * Q) := by
      noncomm_ring
    rw [hexp, hQQ, hRR, sub_self, hQR.eq, sub_self, add_zero]
  have hDh : (Q - Petz.sqrtMat hP.1).IsHermitian := hQ.1.sub hRP.1
  have hker : ∀ v, Q *ᵥ ((Q - Petz.sqrtMat hP.1) *ᵥ v) = 0 ∧
      Petz.sqrtMat hP.1 *ᵥ ((Q - Petz.sqrtMat hP.1) *ᵥ v) = 0 := by
    intro v
    have hzero : star ((Q - Petz.sqrtMat hP.1) *ᵥ v) ⬝ᵥ
        ((Q + Petz.sqrtMat hP.1) *ᵥ ((Q - Petz.sqrtMat hP.1) *ᵥ v)) = 0 := by
      calc star ((Q - Petz.sqrtMat hP.1) *ᵥ v) ⬝ᵥ
            ((Q + Petz.sqrtMat hP.1) *ᵥ ((Q - Petz.sqrtMat hP.1) *ᵥ v))
          = star v ⬝ᵥ ((Q - Petz.sqrtMat hP.1) *ᵥ
              ((Q + Petz.sqrtMat hP.1) *ᵥ ((Q - Petz.sqrtMat hP.1) *ᵥ v))) :=
            (hermitian_dotProduct_transfer hDh v _).symm
        _ = star v ⬝ᵥ (((Q - Petz.sqrtMat hP.1) * (Q + Petz.sqrtMat hP.1)) *ᵥ
              ((Q - Petz.sqrtMat hP.1) *ᵥ v)) := by
            rw [Matrix.mulVec_mulVec]
        _ = 0 := by rw [hD0, Matrix.zero_mulVec, dotProduct_zero]
    have hsplit : star ((Q - Petz.sqrtMat hP.1) *ᵥ v) ⬝ᵥ
        (Q *ᵥ ((Q - Petz.sqrtMat hP.1) *ᵥ v)) +
        star ((Q - Petz.sqrtMat hP.1) *ᵥ v) ⬝ᵥ
        (Petz.sqrtMat hP.1 *ᵥ ((Q - Petz.sqrtMat hP.1) *ᵥ v)) = 0 := by
      rw [← dotProduct_add, ← Matrix.add_mulVec]
      exact hzero
    have hq := posSemidef_quadratic_re hQ ((Q - Petz.sqrtMat hP.1) *ᵥ v)
    have hr := posSemidef_quadratic_re hRP ((Q - Petz.sqrtMat hP.1) *ᵥ v)
    have hre := congrArg Complex.re hsplit
    rw [Complex.add_re, Complex.zero_re] at hre
    have hQz : star ((Q - Petz.sqrtMat hP.1) *ᵥ v) ⬝ᵥ
        (Q *ᵥ ((Q - Petz.sqrtMat hP.1) *ᵥ v)) = 0 := by
      rw [Complex.ext_iff]
      constructor
      · simp only [Complex.zero_re]
        linarith [hq.1, hr.1]
      · simp only [Complex.zero_im]
        exact hq.2
    have hRz : star ((Q - Petz.sqrtMat hP.1) *ᵥ v) ⬝ᵥ
        (Petz.sqrtMat hP.1 *ᵥ ((Q - Petz.sqrtMat hP.1) *ᵥ v)) = 0 := by
      rw [Complex.ext_iff]
      constructor
      · simp only [Complex.zero_re]
        linarith [hq.1, hr.1]
      · simp only [Complex.zero_im]
        exact hr.2
    exact ⟨posSemidef_mulVec_eq_zero hQ hQz,
      posSemidef_mulVec_eq_zero hRP hRz⟩
  have hfinal : Q - Petz.sqrtMat hP.1 = 0 := by
    apply eq_zero_of_mulVec_eq_zero
    intro v
    apply mulVec_self_dot_eq_zero
    calc star ((Q - Petz.sqrtMat hP.1) *ᵥ v) ⬝ᵥ
          ((Q - Petz.sqrtMat hP.1) *ᵥ v)
        = star v ⬝ᵥ ((Q - Petz.sqrtMat hP.1) *ᵥ
            ((Q - Petz.sqrtMat hP.1) *ᵥ v)) :=
          (hermitian_dotProduct_transfer hDh v _).symm
      _ = star v ⬝ᵥ (Q *ᵥ ((Q - Petz.sqrtMat hP.1) *ᵥ v) -
            Petz.sqrtMat hP.1 *ᵥ ((Q - Petz.sqrtMat hP.1) *ᵥ v)) := by
          rw [Matrix.sub_mulVec]
      _ = 0 := by
          rw [(hker v).1, (hker v).2, sub_zero, dotProduct_zero]
  exact sub_eq_zero.mp hfinal

end QRE
end NCG
