/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.PetzRecoveryExact

/-!
# Loewner monotonicity of the matrix square root

Step (D4a) of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: the operator toolkit for the matrix
geometric mean.

* `matFun_posSemidef`: the spectral calculus of a nonnegative scalar
  function is positive semidefinite;
* `sqrtMat_posSemidef`: the square root of a PSD matrix is PSD;
* `hermitian_dotProduct_transfer`, `posSemidef_mulVec_eq_zero`: quadratic
  form transfer and the PSD kernel criterion;
* `sqrtMat_monotone` (**Loewner–Heinz for the square root**):
  `0 ⪯ S ⪯ T → √S ⪯ √T`, by the eigenvalue argument on `√T − √S`.
-/

open Matrix Unitary Finset
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {S T P : Matrix n n ℂ}

/-- The spectral calculus of a nonnegative function is PSD. -/
theorem matFun_posSemidef (hS : S.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ i, 0 ≤ f (hS.eigenvalues i)) : (matFun hS f).PosSemidef := by
  have hd : (diagonal (RCLike.ofReal ∘ fun i => f (hS.eigenvalues i)) :
      Matrix n n ℂ).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    rw [Function.comp_apply, Complex.le_def]
    constructor
    · simpa using hf i
    · simp
  unfold matFun
  rw [conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  exact hd.mul_mul_conjTranspose_same _

theorem sqrtMat_posSemidef (hS : S.PosSemidef) :
    (Petz.sqrtMat hS.1).PosSemidef :=
  matFun_posSemidef hS.1 _ fun _ => Real.sqrt_nonneg _

omit [DecidableEq n] in
/-- The quadratic form of a Hermitian matrix transfers across the pairing. -/
theorem hermitian_dotProduct_transfer (hP : P.IsHermitian) (v w : n → ℂ) :
    star v ⬝ᵥ (P *ᵥ w) = star (P *ᵥ v) ⬝ᵥ w := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum,
    star_sum, star_mul', Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have hij : star (P j i) = P i j := by
    rw [← Matrix.conjTranspose_apply, hP.eq]
  rw [hij]
  ring

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **The PSD kernel criterion**: a vanishing quadratic form annihilates the
vector. -/
theorem posSemidef_mulVec_eq_zero (hP : P.PosSemidef) {v : n → ℂ}
    (h : star v ⬝ᵥ (P *ᵥ v) = 0) : P *ᵥ v = 0 := by
  have hQh : (Petz.sqrtMat hP.1).IsHermitian := Petz.sqrtMat_isHermitian hP.1
  have hPv : Petz.sqrtMat hP.1 *ᵥ (Petz.sqrtMat hP.1 *ᵥ v) = P *ᵥ v := by
    rw [Matrix.mulVec_mulVec, Petz.sqrtMat_mul_self hP]
  have hqv : star (Petz.sqrtMat hP.1 *ᵥ v) ⬝ᵥ
      (Petz.sqrtMat hP.1 *ᵥ v) = 0 := by
    calc star (Petz.sqrtMat hP.1 *ᵥ v) ⬝ᵥ (Petz.sqrtMat hP.1 *ᵥ v)
        = star v ⬝ᵥ (Petz.sqrtMat hP.1 *ᵥ (Petz.sqrtMat hP.1 *ᵥ v)) :=
          (hermitian_dotProduct_transfer hQh v _).symm
      _ = star v ⬝ᵥ (P *ᵥ v) := by rw [hPv]
      _ = 0 := h
  have hsum : ∑ i, Complex.normSq ((Petz.sqrtMat hP.1 *ᵥ v) i) = 0 := by
    have hre := congrArg Complex.re hqv
    simp only [dotProduct, Pi.star_apply, Complex.re_sum,
      Complex.zero_re] at hre
    have hz : ∀ z : ℂ, (star z * z).re = Complex.normSq z := fun z => by
      rw [Complex.star_def, mul_comm, Complex.mul_conj]
      simp
    rw [← hre]
    exact Finset.sum_congr rfl fun i _ => (hz _).symm
  have hq0 : Petz.sqrtMat hP.1 *ᵥ v = 0 := by
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      fun i _ => Complex.normSq_nonneg _).mp hsum i (Finset.mem_univ i)
    simpa using Complex.normSq_eq_zero.mp hi
  rw [← hPv, hq0, Matrix.mulVec_zero]

omit [DecidableEq n] in
/-- Nonnegativity of PSD quadratic forms, in real components. -/
theorem posSemidef_quadratic_re (hP : P.PosSemidef) (v : n → ℂ) :
    0 ≤ (star v ⬝ᵥ (P *ᵥ v)).re ∧ (star v ⬝ᵥ (P *ᵥ v)).im = 0 := by
  have h := hP.dotProduct_mulVec_nonneg v
  rw [Complex.le_def] at h
  refine ⟨?_, ?_⟩
  · simpa using h.1
  · simpa using h.2.symm

set_option maxHeartbeats 1600000 in -- eigenvalue-by-eigenvalue sign analysis
/-- **Loewner monotonicity of the matrix square root**:
`0 ⪯ S ⪯ T → √S ⪯ √T`. -/
theorem sqrtMat_monotone (hS : S.PosSemidef) (hT : T.PosSemidef)
    (hST : (T - S).PosSemidef) :
    (Petz.sqrtMat hT.1 - Petz.sqrtMat hS.1).PosSemidef := by
  have hQSh : (Petz.sqrtMat hS.1).IsHermitian := Petz.sqrtMat_isHermitian hS.1
  have hQTh : (Petz.sqrtMat hT.1).IsHermitian := Petz.sqrtMat_isHermitian hT.1
  have hD : (Petz.sqrtMat hT.1 - Petz.sqrtMat hS.1).IsHermitian :=
    hQTh.sub hQSh
  rw [hD.posSemidef_iff_eigenvalues_nonneg]
  intro k
  by_contra hneg
  rw [not_le] at hneg
  set μ : ℝ := hD.eigenvalues k with hμdef
  have hneg' : μ < 0 := by simpa using hneg
  set v : n → ℂ := ⇑(hD.eigenvectorBasis k) with hvdef
  have hvne : v ≠ 0 := by
    intro h0
    apply hD.eigenvectorBasis.orthonormal.ne_zero k
    apply WithLp.ofLp_injective
    funext i
    exact congrFun h0 i
  have hev : (Petz.sqrtMat hT.1 - Petz.sqrtMat hS.1) *ᵥ v = (μ : ℂ) • v := by
    have h := hD.mulVec_eigenvectorBasis k
    rw [hvdef, hμdef]
    calc (Petz.sqrtMat hT.1 - Petz.sqrtMat hS.1) *ᵥ
          ⇑(hD.eigenvectorBasis k)
        = hD.eigenvalues k • ⇑(hD.eigenvectorBasis k) := h
      _ = ((hD.eigenvalues k : ℂ)) • ⇑(hD.eigenvectorBasis k) := by
          funext i
          simp [Complex.real_smul]
  have hTSid : T - S = Petz.sqrtMat hT.1 *
      (Petz.sqrtMat hT.1 - Petz.sqrtMat hS.1) +
      (Petz.sqrtMat hT.1 - Petz.sqrtMat hS.1) * Petz.sqrtMat hS.1 := by
    have h1 : Petz.sqrtMat hT.1 * Petz.sqrtMat hT.1 = T :=
      Petz.sqrtMat_mul_self hT
    have h2 : Petz.sqrtMat hS.1 * Petz.sqrtMat hS.1 = S :=
      Petz.sqrtMat_mul_self hS
    rw [Matrix.mul_sub, Matrix.sub_mul, h1, h2]
    abel
  have hterm : star v ⬝ᵥ ((T - S) *ᵥ v) =
      (μ : ℂ) * (star v ⬝ᵥ (Petz.sqrtMat hT.1 *ᵥ v) +
        star v ⬝ᵥ (Petz.sqrtMat hS.1 *ᵥ v)) := by
    rw [hTSid, Matrix.add_mulVec, dotProduct_add,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hev,
      Matrix.mulVec_smul, dotProduct_smul]
    have h2 : star v ⬝ᵥ ((Petz.sqrtMat hT.1 - Petz.sqrtMat hS.1) *ᵥ
        (Petz.sqrtMat hS.1 *ᵥ v)) =
        (μ : ℂ) * (star v ⬝ᵥ (Petz.sqrtMat hS.1 *ᵥ v)) := by
      rw [hermitian_dotProduct_transfer hD v _, hev]
      have hsmul : star ((μ : ℂ) • v) = (μ : ℂ) • star v := by
        funext i
        simp [Complex.conj_ofReal]
      rw [hsmul, smul_dotProduct]
      rfl
    rw [h2]
    simp only [smul_eq_mul]
    ring
  have hquadT := posSemidef_quadratic_re (sqrtMat_posSemidef hT) v
  have hquadS := posSemidef_quadratic_re (sqrtMat_posSemidef hS) v
  have hquadTS := posSemidef_quadratic_re hST v
  set qT := star v ⬝ᵥ (Petz.sqrtMat hT.1 *ᵥ v) with hqT
  set qS := star v ⬝ᵥ (Petz.sqrtMat hS.1 *ᵥ v) with hqS
  have hre : 0 ≤ μ * (qT.re + qS.re) := by
    have h := hquadTS.1
    rw [hterm] at h
    have hexp : ((μ : ℂ) * (qT + qS)).re = μ * (qT.re + qS.re) := by
      rw [Complex.mul_re]
      simp [hquadT.2, hquadS.2]
    rw [hexp] at h
    exact h
  have hsum0 : qT.re + qS.re ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    nlinarith
  have hTzero : qT.re = 0 := by nlinarith [hquadT.1, hquadS.1]
  have hSzero : qS.re = 0 := by nlinarith [hquadT.1, hquadS.1]
  have hqTzero : qT = 0 := by
    rw [Complex.ext_iff]
    exact ⟨hTzero, hquadT.2⟩
  have hqSzero : qS = 0 := by
    rw [Complex.ext_iff]
    exact ⟨hSzero, hquadS.2⟩
  have hkerT : Petz.sqrtMat hT.1 *ᵥ v = 0 :=
    posSemidef_mulVec_eq_zero (sqrtMat_posSemidef hT) hqTzero
  have hkerS : Petz.sqrtMat hS.1 *ᵥ v = 0 :=
    posSemidef_mulVec_eq_zero (sqrtMat_posSemidef hS) hqSzero
  have hDv : (Petz.sqrtMat hT.1 - Petz.sqrtMat hS.1) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, hkerT, hkerS, sub_zero]
  rw [hev] at hDv
  have hμ0 : (μ : ℂ) = 0 := by
    by_contra hμne
    exact hvne (by
      have := smul_eq_zero.mp hDv
      rcases this with h | h
      · exact absurd h hμne
      · exact h)
  have : μ = 0 := by exact_mod_cast hμ0
  linarith

end QRE
end NCG
