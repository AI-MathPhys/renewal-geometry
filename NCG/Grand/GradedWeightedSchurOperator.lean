/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.WeightedInfluence
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Weighted Schur estimates on a finite orthogonal grading

This is the operator-level completion of `thm:weighted-source-influence`.
The finite Hilbert space is the orthogonal product grading `I × K`; no
one-dimensional-block reduction is made.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NCG

variable {I K : Type*} [Fintype I] [Fintype K]

/-- Euclidean norm of the `i`th orthogonal fiber of a graded vector. -/
noncomputable def gradedFiberNorm (x : I × K → ℂ) (i : I) : ℝ :=
  Real.sqrt (∑ a, Complex.normSq (x (i, a)))

omit [Fintype I] in
theorem gradedFiberNorm_nonneg (x : I × K → ℂ) (i : I) :
    0 ≤ gradedFiberNorm x i := Real.sqrt_nonneg _

omit [Fintype I] in
theorem gradedFiberNorm_sq (x : I × K → ℂ) (i : I) :
    gradedFiberNorm x i ^ 2 = ∑ a, Complex.normSq (x (i, a)) := by
  rw [gradedFiberNorm, Real.sq_sqrt]
  exact Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

/-- Real quadratic pairing between the `i,j` block of an operator and the
corresponding fibers of `x`. -/
def gradedBlockQuadratic (H : Matrix (I × K) (I × K) ℂ)
    (x : I × K → ℂ) (i j : I) : ℝ :=
  (∑ a, ∑ b, star (x (i, a)) * H (i, a) (j, b) * x (j, b)).re

private theorem complex_re_sum {A : Type*} [Fintype A] (f : A → ℂ) :
    (∑ a, f a).re = ∑ a, (f a).re := by
  change Complex.reCLM (∑ a, f a) = _
  rw [map_sum]
  rfl

/-- The quadratic form of a block matrix is the sum of its block pairings. -/
theorem gradedQuadratic_eq_sum_blocks
    (H : Matrix (I × K) (I × K) ℂ) (x : I × K → ℂ) :
    (star x ⬝ᵥ (H *ᵥ x)).re = ∑ i, ∑ j, gradedBlockQuadratic H x i j := by
  classical
  simp only [dotProduct, mulVec, Pi.star_apply, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum, complex_re_sum]
  rw [show (∑ i, ∑ a, ∑ j, ∑ b,
      (star (x (i, a)) * (H (i, a) (j, b) * x (j, b))).re) =
      ∑ i, ∑ j, ∑ a, ∑ b,
      (star (x (i, a)) * (H (i, a) (j, b) * x (j, b))).re by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_comm]]
  simp only [gradedBlockQuadratic]
  simp_rw [complex_re_sum]
  refine Finset.sum_congr rfl fun i _ ↦
    Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun a _ ↦
    Finset.sum_congr rfl fun b _ ↦ ?_
  ring_nf

/-- Squared norm of the whole graded vector is the sum of squared fiber
norms. -/
theorem sum_gradedFiberNorm_sq (x : I × K → ℂ) :
    ∑ i, gradedFiberNorm x i ^ 2 =
      ∑ p, Complex.normSq (x p) := by
  simp_rw [gradedFiberNorm_sq]
  rw [Fintype.sum_prod_type]

private theorem graded_star_dot_self (x : I × K → ℂ) :
    star x ⬝ᵥ x = ((∑ p, Complex.normSq (x p) : ℝ) : ℂ) := by
  rw [dotProduct]
  push_cast
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]

private theorem hermitian_quadratic_im_zero
    (M : Matrix (I × K) (I × K) ℂ) (hM : M.IsHermitian)
    (x : I × K → ℂ) : (star x ⬝ᵥ (M *ᵥ x)).im = 0 := by
  have hreal : star (star x ⬝ᵥ (M *ᵥ x)) = star x ⬝ᵥ (M *ᵥ x) := by
    calc
      star (star x ⬝ᵥ (M *ᵥ x)) = star (M *ᵥ x) ⬝ᵥ x := by
        rw [star_dotProduct]
        simp
      _ = (star x ᵥ* Mᴴ) ⬝ᵥ x := by rw [star_mulVec]
      _ = star x ⬝ᵥ (Mᴴ *ᵥ x) := by rw [dotProduct_mulVec]
      _ = star x ⬝ᵥ (M *ᵥ x) := by rw [hM.eq]
  have him := congrArg Complex.im hreal
  change -(star x ⬝ᵥ (M *ᵥ x)).im = (star x ⬝ᵥ (M *ᵥ x)).im at him
  linarith

/-- Weighted block Schur estimate as a global quadratic-form bound. -/
theorem graded_weighted_schur_quadratic
    (H : Matrix (I × K) (I × K) ℂ)
    (c : I → I → ℝ) (w : I → ℝ) (kappa : ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (hsymm : ∀ i j, c i j = c j i)
    (hw : ∀ i, 0 < w i)
    (hk : ∀ i, ∑ j, c i j * w j ≤ kappa * w i)
    (hblock : ∀ x i j, gradedBlockQuadratic H x i j ≤
      c i j * gradedFiberNorm x i * gradedFiberNorm x j) :
    ∀ x : I × K → ℂ,
      (star x ⬝ᵥ (H *ᵥ x)).re ≤
        kappa * ∑ p, Complex.normSq (x p) := by
  intro x
  rw [gradedQuadratic_eq_sum_blocks]
  calc
    ∑ i, ∑ j, gradedBlockQuadratic H x i j
        ≤ ∑ i, ∑ j,
          c i j * gradedFiberNorm x i * gradedFiberNorm x j :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hblock x i j
    _ ≤ kappa * ∑ i, gradedFiberNorm x i ^ 2 :=
      (weighted_source_influence c w hc hsymm hw).1 kappa hk
        (gradedFiberNorm x) (gradedFiberNorm_nonneg x)
    _ = kappa * ∑ p, Complex.normSq (x p) := by
      rw [sum_gradedFiberNorm_sq]

/-- The weighted block estimate gives the Loewner upper bound
`H ≼ kappa I`. -/
theorem graded_weighted_schur_deficit_posSemidef
    [DecidableEq I] [DecidableEq K]
    (H : Matrix (I × K) (I × K) ℂ) (hH : H.IsHermitian)
    (c : I → I → ℝ) (w : I → ℝ) (kappa : ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (hsymm : ∀ i j, c i j = c j i)
    (hw : ∀ i, 0 < w i)
    (hk : ∀ i, ∑ j, c i j * w j ≤ kappa * w i)
    (hblock : ∀ x i j, gradedBlockQuadratic H x i j ≤
      c i j * gradedFiberNorm x i * gradedFiberNorm x j) :
    (((kappa : ℝ) : ℂ) • (1 : Matrix (I × K) (I × K) ℂ) - H).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · change
      ((((kappa : ℝ) : ℂ) • (1 : Matrix (I × K) (I × K) ℂ) - H)ᴴ) =
        ((kappa : ℂ) • 1 - H)
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hH.eq]
    simp
  · intro x
    have hq := graded_weighted_schur_quadratic H c w kappa hc hsymm hw hk hblock x
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul]
    rw [graded_star_dot_self]
    rw [Complex.nonneg_iff]
    constructor
    · norm_num
      exact hq
    · norm_num
      exact hermitian_quadratic_im_zero H hH x

/-- Operator-norm form of the weighted Schur test for positive operators. -/
theorem graded_weighted_schur_operatorNorm
    [DecidableEq I] [DecidableEq K] [Nonempty I] [Nonempty K]
    (H : Matrix (I × K) (I × K) ℂ) (hH : H.PosSemidef)
    (c : I → I → ℝ) (w : I → ℝ) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hc : ∀ i j, 0 ≤ c i j) (hsymm : ∀ i j, c i j = c j i)
    (hw : ∀ i, 0 < w i)
    (hk : ∀ i, ∑ j, c i j * w j ≤ kappa * w i)
    (hblock : ∀ x i j, gradedBlockQuadratic H x i j ≤
      c i j * gradedFiberNorm x i * gradedFiberNorm x j) :
    ‖H‖ ≤ kappa := by
  letI : CStarAlgebra (Matrix (I × K) (I × K) ℂ) := by
    refine { norm_mul_self_le := fun x ↦
      (CStarRing.norm_star_mul_self (x := x)).ge }
  have hdef := graded_weighted_schur_deficit_posSemidef H hH.1 c w kappa
    hc hsymm hw hk hblock
  apply (CStarAlgebra.norm_le_iff_le_algebraMap H hkappa (ha := hH.nonneg)).2
  rw [Matrix.le_iff]
  have halg : (algebraMap ℝ (Matrix (I × K) (I × K) ℂ)) kappa =
      ((kappa : ℂ) • (1 : Matrix (I × K) (I × K) ℂ)) := by
    rw [Algebra.algebraMap_eq_smul_one]
    ext p q
    simp
  rw [halg]
  exact hdef

/-- Dual weighted diagonal-dominance criterion: if the diagonal part supplies
the weighted floors and the off-diagonal block quadratic forms are bounded by
`c`, the full deficit is positive semidefinite. -/
theorem graded_weighted_diagonal_dominance
    (R : Matrix (I × K) (I × K) ℂ) (hR : R.IsHermitian)
    (c : I → I → ℝ) (w d : I → ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (hsymm : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i = 0) (hw : ∀ i, 0 < w i)
    (hdom : ∀ i, ∑ j, c i j * w j ≤ d i * w i)
    (hquad : ∀ x,
      (∑ i, d i * gradedFiberNorm x i ^ 2) -
        (∑ i, ∑ j, c i j * gradedFiberNorm x i * gradedFiberNorm x j)
        ≤ (star x ⬝ᵥ (R *ᵥ x)).re) :
    R.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hR ?_
  intro x
  have hprofile := (weighted_source_influence c w hc hsymm hw).2 d hdiag hdom
    (gradedFiberNorm x) (gradedFiberNorm_nonneg x)
  rw [Complex.nonneg_iff]
  exact ⟨hprofile.trans (hquad x), (hermitian_quadratic_im_zero R hR x).symm⟩

end NCG
