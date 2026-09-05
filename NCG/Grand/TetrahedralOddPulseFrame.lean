/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Explicit tetrahedral odd pulse frame

Concrete real matrices for the spatial tetrahedral tensor and the two odd
score-plane generators from `thm:SM-tetrahedral-two-pulse-frame`.  All frame
normalizations and the predetermined quarter-turn pulse are checked entry by
entry over the exact rational matrices.
-/

open Matrix Finset

namespace NCG
namespace TetrahedralOddPulseFrame

noncomputable section

/-- The displayed tetrahedral spatial tensor, extended by zero on the constant
line in `ℝ⁴`. -/
def spatialTensor : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 4 : ℝ) •
    !![2, 0, -1, -1;
       0, -2, 1, 1;
       -1, 1, 0, 0;
       -1, 1, 0, 0]

/-- Standard-representation matrix of the tetrahedral transposition `(12)`. -/
def spatialSwap12 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0;
     1, 0, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- Standard-representation matrix of the tetrahedral transposition `(34)`. -/
def spatialSwap34 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- A three-cycle fixing the fourth tetrahedral vertex. -/
def spatialCycle123 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 1, 0;
     1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1]

/-- The inverse three-cycle, written explicitly to keep finite computations
transparent. -/
def spatialCycle132 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0;
     0, 0, 1, 0;
     1, 0, 0, 0;
     0, 0, 0, 1]

theorem spatialCycle_transpose_and_square :
    spatialCycle123.transpose = spatialCycle132 ∧
      spatialCycle123 ^ 2 = spatialCycle132 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [spatialCycle123, spatialCycle132]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [spatialCycle123, spatialCycle132, pow_two, Matrix.mul_apply,
        Fin.sum_univ_succ]

/-- The constant spatial vector whose orthogonal complement is `W₀`. -/
def spatialConstant : Fin 4 → ℝ := fun _ => 1

/-- The odd score generator joining `e₀` to the negative score line `e₂`. -/
def scoreGenerator02 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, -1;
     0, 0, 0;
     1, 0, 0]

/-- The odd score generator joining `e₁` to the negative score line `e₂`. -/
def scoreGenerator12 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0;
     0, 0, -1;
     0, 1, 0]

/-- Positive-score-plane quarter turn fixing `e₂`. -/
def scoreQuarterTurn : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -1, 0;
     1, 0, 0;
     0, 0, 1]

/-- The displayed score grading with two positive and one negative directions. -/
def scoreGrading : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, -1]

/-- Tensor product written on the literal product basis. -/
def tensorMatrix {m n p q : Type*}
    (A : Matrix m n ℝ) (B : Matrix p q ℝ) :
    Matrix (m × p) (n × q) ℝ :=
  fun i j => A i.1 j.1 * B i.2 j.2

/-- The unrotated protected pulse. -/
def pulseZero : Matrix (Fin 4 × Fin 3) (Fin 4 × Fin 3) ℝ :=
  tensorMatrix spatialTensor scoreGenerator12

/-- The predetermined quarter-turn pulse. -/
def pulseQuarterTurn : Matrix (Fin 4 × Fin 3) (Fin 4 × Fin 3) ℝ :=
  -tensorMatrix spatialTensor scoreGenerator02

/-- Real Hilbert--Schmidt pairing on finite matrices. -/
def hilbertSchmidtInner {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- The spatial tensor is symmetric and has Hilbert--Schmidt norm one. -/
theorem spatialTensor_symmetric_and_unit :
    spatialTensor.transpose = spatialTensor ∧
      hilbertSchmidtInner spatialTensor spatialTensor = 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [spatialTensor]
  · norm_num [hilbertSchmidtInner, spatialTensor, Fin.sum_univ_succ]

/-- The displayed spatial tensor satisfies the complete tetrahedral spatial
constraint packet: it kills the constant line, commutes with `(34)`, is odd
under `(12)`, and obeys the three-cycle relation. -/
theorem spatialTensor_satisfies_tetrahedral_relations :
    spatialTensor.mulVec spatialConstant = 0 ∧
      spatialSwap34 * spatialTensor = spatialTensor * spatialSwap34 ∧
      spatialSwap12 * spatialTensor * spatialSwap12 = -spatialTensor ∧
      spatialTensor +
          spatialCycle123 * spatialTensor * spatialCycle123.transpose +
          spatialCycle123 ^ 2 * spatialTensor *
            (spatialCycle123 ^ 2).transpose = 0 := by
  constructor
  · funext i
    fin_cases i <;>
      norm_num [spatialTensor, spatialConstant, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [spatialTensor, spatialSwap34, Matrix.mul_apply,
        Fin.sum_univ_succ]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [spatialTensor, spatialSwap12, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_succ, Fin.isValue]
  · ext i j
    rcases spatialCycle_transpose_and_square with ⟨htranspose, hsquare⟩
    rw [htranspose, hsquare]
    have hinvTranspose : spatialCycle132.transpose = spatialCycle123 := by
      rw [← htranspose, Matrix.transpose_transpose]
    rw [hinvTranspose]
    fin_cases i <;> fin_cases j <;>
      norm_num [spatialTensor, spatialCycle123, spatialCycle132,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
        Fin.isValue]

/-- The symmetric spatial solution of the tetrahedral commutation, oddness,
and mean-zero constraints is exactly the line spanned by `T`.  The cyclic
relation is then automatic by the preceding theorem. -/
theorem symmetricSpatialRelation_unique
    (X : Matrix (Fin 4) (Fin 4) ℝ)
    (hsymmetric : X.transpose = X)
    (hmean : X.mulVec spatialConstant = 0)
    (h34 : spatialSwap34 * X = X * spatialSwap34)
    (h12 : spatialSwap12 * X * spatialSwap12 = -X) :
    ∃! k : ℝ, X = k • spatialTensor := by
  have hs (i j : Fin 4) : X j i = X i j := by
    exact congrFun (congrFun hsymmetric i) j
  have hc02 : X 0 2 = X 0 3 := by
    simpa [spatialSwap34, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h34 0) 2
  have hc12 : X 1 2 = X 1 3 := by
    simpa [spatialSwap34, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h34 1) 2
  have hc22 : X 3 3 = X 2 2 := by
    simpa [spatialSwap34, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h34 2) 3
  have ho00 : X 1 1 = -X 0 0 := by
    simpa [spatialSwap12, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h12 0) 0
  have ho01 : X 1 0 = -X 0 1 := by
    simpa [spatialSwap12, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h12 0) 1
  have ho02 : X 1 2 = -X 0 2 := by
    simpa [spatialSwap12, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h12 0) 2
  have ho22 : X 2 2 = -X 2 2 := by
    simpa [spatialSwap12, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h12 2) 2
  have ho23 : X 2 3 = -X 2 3 := by
    simpa [spatialSwap12, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h12 2) 3
  have hm0 : X 0 0 + X 0 1 + X 0 2 + X 0 3 = 0 := by
    simpa [spatialConstant, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, add_assoc] using congrFun hmean 0
  have hb : X 0 1 = 0 := by linarith [hs 0 1, ho01]
  have ha : X 0 0 = -2 * X 0 2 := by linarith [hm0, hc02]
  have h22 : X 2 2 = 0 := by linarith [ho22]
  have h23 : X 2 3 = 0 := by linarith [ho23]
  have h33 : X 3 3 = 0 := by linarith [hc22, h22]
  refine ⟨-4 * X 0 2, ?_, ?_⟩
  · ext i j
    have h00 : X 0 0 = -2 * X 0 2 := ha
    have h01 : X 0 1 = 0 := hb
    have h02 : X 0 2 = X 0 2 := rfl
    have h03 : X 0 3 = X 0 2 := hc02.symm
    have h10 : X 1 0 = 0 := by linarith [hs 0 1, hb]
    have h11 : X 1 1 = 2 * X 0 2 := by linarith [ho00, ha]
    have h12' : X 1 2 = -X 0 2 := ho02
    have h13 : X 1 3 = -X 0 2 := by linarith [hc12, ho02]
    have h20 : X 2 0 = X 0 2 := hs 0 2
    have h21 : X 2 1 = -X 0 2 := by linarith [hs 1 2, ho02]
    have h30 : X 3 0 = X 0 2 := by linarith [hs 0 3, hc02]
    have h31 : X 3 1 = -X 0 2 := by linarith [hs 1 3, hc12, ho02]
    have h32 : X 3 2 = 0 := by linarith [hs 2 3, h23]
    fin_cases i <;> fin_cases j
    · norm_num [spatialTensor, Matrix.smul_apply]
      ring_nf
      simpa [mul_comm] using h00
    · simpa [spatialTensor, Matrix.smul_apply] using h01
    · simp [spatialTensor, Matrix.smul_apply, Fin.isValue]
      ring
    · norm_num [spatialTensor, Matrix.smul_apply]
      ring_nf
      exact h03
    · simpa [spatialTensor, Matrix.smul_apply] using h10
    · norm_num [spatialTensor, Matrix.smul_apply]
      ring_nf
      simpa [mul_comm] using h11
    · norm_num [spatialTensor, Matrix.smul_apply]
      ring_nf
      exact h12'
    · norm_num [spatialTensor, Matrix.smul_apply]
      ring_nf
      exact h13
    · norm_num [spatialTensor, Matrix.smul_apply]
      ring_nf
      exact h20
    · norm_num [spatialTensor, Matrix.smul_apply]
      ring_nf
      exact h21
    · simpa [spatialTensor, Matrix.smul_apply] using h22
    · simpa [spatialTensor, Matrix.smul_apply] using h23
    · norm_num [spatialTensor, Matrix.smul_apply]
      ring_nf
      exact h30
    · norm_num [spatialTensor, Matrix.smul_apply]
      ring_nf
      exact h31
    · simpa [spatialTensor, Matrix.smul_apply] using h32
    · simpa [spatialTensor, Matrix.smul_apply] using h33
  · intro k hk
    have h02 := congrFun (congrFun hk 0) 2
    simp [spatialTensor, Matrix.smul_apply, Fin.isValue] at h02
    ring_nf at h02
    linarith

/-- A spatial coefficient block satisfying the full tetrahedral packet and
annihilating the constant line on both sides is necessarily a scalar multiple
of `T`; symmetry is a consequence rather than an extra hypothesis. -/
theorem spatialRelation_unique
    (X : Matrix (Fin 4) (Fin 4) ℝ)
    (hrow : X.mulVec spatialConstant = 0)
    (hcol : X.transpose.mulVec spatialConstant = 0)
    (h34 : spatialSwap34 * X = X * spatialSwap34)
    (h12 : spatialSwap12 * X * spatialSwap12 = -X)
    (hcycle : X + spatialCycle123 * X * spatialCycle123.transpose +
      spatialCycle123 ^ 2 * X * (spatialCycle123 ^ 2).transpose = 0) :
    ∃! k : ℝ, X = k • spatialTensor := by
  have hc02 : X 0 2 = X 0 3 := by
    simpa [spatialSwap34, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h34 0) 2
  have hc12 : X 1 2 = X 1 3 := by
    simpa [spatialSwap34, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h34 1) 2
  have hc20 : X 2 0 = X 3 0 := by
    have htmp : X 3 0 = X 2 0 := by
      simpa [spatialSwap34, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_four] using congrFun (congrFun h34 2) 0
    exact htmp.symm
  have hc21 : X 2 1 = X 3 1 := by
    have htmp : X 3 1 = X 2 1 := by
      simpa [spatialSwap34, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_four] using congrFun (congrFun h34 2) 1
    exact htmp.symm
  have hc22 : X 3 3 = X 2 2 := by
    simpa [spatialSwap34, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h34 2) 3
  have hc23 : X 3 2 = X 2 3 := by
    simpa [spatialSwap34, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h34 2) 2
  have ho00 : X 1 1 = -X 0 0 := by
    simpa [spatialSwap12, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h12 0) 0
  have ho01 : X 1 0 = -X 0 1 := by
    simpa [spatialSwap12, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h12 0) 1
  have ho02 : X 1 2 = -X 0 2 := by
    simpa [spatialSwap12, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h12 0) 2
  have ho20 : X 2 1 = -X 2 0 := by
    simpa [spatialSwap12, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h12 2) 0
  have ho22 : X 2 2 = -X 2 2 := by
    simpa [spatialSwap12, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h12 2) 2
  have ho23 : X 2 3 = -X 2 3 := by
    simpa [spatialSwap12, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four] using congrFun (congrFun h12 2) 3
  have hr0 : X 0 0 + X 0 1 + X 0 2 + X 0 3 = 0 := by
    simpa [spatialConstant, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, add_assoc] using congrFun hrow 0
  have hcolumn0 : X 0 0 + X 1 0 + X 2 0 + X 3 0 = 0 := by
    simpa [spatialConstant, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, add_assoc] using congrFun hcol 0
  have hcy01 := congrFun (congrFun hcycle 0) 1
  rcases spatialCycle_transpose_and_square with ⟨htranspose, hsquare⟩
  have hinvTranspose : spatialCycle132.transpose = spatialCycle123 := by
    rw [← htranspose, Matrix.transpose_transpose]
  rw [htranspose, hsquare, hinvTranspose] at hcy01
  simp [spatialCycle123, spatialCycle132, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, Fin.sum_univ_four] at hcy01
  have hb : X 0 1 = 0 := by
    linarith [hcolumn0, hc20, ho01, hcy01]
  have hg : X 2 0 = X 0 2 := by
    linarith [hcolumn0, hc20, ho01, hb, hr0, hc02]
  have ha : X 0 0 = -2 * X 0 2 := by linarith [hr0, hc02, hb]
  have h22 : X 2 2 = 0 := by linarith [ho22]
  have h23 : X 2 3 = 0 := by linarith [ho23]
  have h33 : X 3 3 = 0 := by linarith [hc22, h22]
  have h32 : X 3 2 = 0 := by linarith [hc23, h23]
  refine ⟨-4 * X 0 2, ?_, ?_⟩
  · ext i j
    have h00 : X 0 0 = -2 * X 0 2 := ha
    have h00r : X 0 0 = -(X 0 2 * 2) := by linarith [ha]
    have h01 : X 0 1 = 0 := hb
    have h03 : X 0 3 = X 0 2 := hc02.symm
    have h10 : X 1 0 = 0 := by linarith [ho01, hb]
    have h11 : X 1 1 = 2 * X 0 2 := by linarith [ho00, ha]
    have h11r : X 1 1 = X 0 2 * 2 := by linarith [h11]
    have h12' : X 1 2 = -X 0 2 := ho02
    have h13 : X 1 3 = -X 0 2 := by linarith [hc12, ho02]
    have h20 : X 2 0 = X 0 2 := hg
    have h21 : X 2 1 = -X 0 2 := by linarith [ho20, hg]
    have h30 : X 3 0 = X 0 2 := by linarith [hc20, hg]
    have h31 : X 3 1 = -X 0 2 := by linarith [hc21, ho20, hg]
    fin_cases i <;> fin_cases j
    all_goals simp [spatialTensor, Matrix.smul_apply, Fin.isValue]
    all_goals ring_nf
    all_goals first
      | exact h00r | exact h01 | rfl | exact h03
      | exact h10 | exact h11r | exact h12' | exact h13
      | exact h20 | exact h21 | exact h22 | exact h23
      | exact h30 | exact h31 | exact h32 | exact h33
  · intro k hk
    have h02 := congrFun (congrFun hk 0) 2
    simp [spatialTensor, Matrix.smul_apply, Fin.isValue] at h02
    ring_nf at h02
    linarith

/-- The elementary odd score generators are orthogonal and each has squared
Hilbert--Schmidt norm two. -/
theorem scoreGenerators_orthogonal_frame :
    hilbertSchmidtInner scoreGenerator02 scoreGenerator12 = 0 ∧
      hilbertSchmidtInner scoreGenerator02 scoreGenerator02 = 2 ∧
      hilbertSchmidtInner scoreGenerator12 scoreGenerator12 = 2 := by
  norm_num [hilbertSchmidtInner, scoreGenerator02, scoreGenerator12,
    Fin.sum_univ_succ]

/-- Every real skew score operator odd under the displayed grading is a unique
linear combination of `L₀₂` and `L₁₂`. -/
theorem gradingOdd_skew_score_classification
    (L : Matrix (Fin 3) (Fin 3) ℝ)
    (hskew : L.transpose = -L)
    (hodd : scoreGrading * L * scoreGrading = -L) :
    ∃! ab : ℝ × ℝ,
      L = ab.1 • scoreGenerator02 + ab.2 • scoreGenerator12 := by
  have hs (i j : Fin 3) : L j i = -L i j := by
    have h := congrFun (congrFun hskew i) j
    simpa using h
  have ho (i j : Fin 3) :
      (scoreGrading * L * scoreGrading) i j = -L i j := by
    exact congrFun (congrFun hodd i) j
  refine ⟨(L 2 0, L 2 1), ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [scoreGenerator02, scoreGenerator12, Matrix.add_apply]
    · linarith [hs 0 0]
    · have h := ho 0 1
      norm_num [scoreGrading, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_succ, Fin.isValue] at h
      linarith
    · linarith [hs 0 2]
    · have h := ho 1 0
      norm_num [scoreGrading, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_succ, Fin.isValue] at h
      linarith
    · linarith [hs 1 1]
    · linarith [hs 1 2]
    · linarith [hs 2 2]
  · intro ab hab
    have h20 := congrFun (congrFun hab 2) 0
    have h21 := congrFun (congrFun hab 2) 1
    have hab0 : L 2 0 = ab.1 := by
      simpa [scoreGenerator02, scoreGenerator12, Matrix.smul_apply,
        Matrix.add_apply, Fin.isValue] using h20
    have hab1 : L 2 1 = ab.2 := by
      simpa [scoreGenerator02, scoreGenerator12, Matrix.smul_apply,
        Matrix.add_apply, Fin.isValue] using h21
    exact Prod.ext hab0.symm hab1.symm

/-- A score block of an operator on the spatial/score tensor product. -/
def spatialBlock
    (A : Matrix (Fin 4 × Fin 3) (Fin 4 × Fin 3) ℝ)
    (a b : Fin 3) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => A (i, a) (j, b)

/-- Eigenvalue of the score grading on a coordinate basis vector. -/
def scoreGradingSign (a : Fin 3) : ℝ := if a = 2 then -1 else 1

/-- Complete finite classification of the real tetrahedral odd relation
space.  The spatial group constraints are stated blockwise, which is exactly
their action through `ρ₀ ⊗ I`; score oddness is the diagonal action of
`I ⊗ Z`. -/
theorem tetrahedralOddRelationSpace_complete
    (A : Matrix (Fin 4 × Fin 3) (Fin 4 × Fin 3) ℝ)
    (hskew : A.transpose = -A)
    (hrow : ∀ a b, (spatialBlock A a b).mulVec spatialConstant = 0)
    (hcol : ∀ a b,
      (spatialBlock A a b).transpose.mulVec spatialConstant = 0)
    (h34 : ∀ a b,
      spatialSwap34 * spatialBlock A a b =
        spatialBlock A a b * spatialSwap34)
    (h12 : ∀ a b,
      spatialSwap12 * spatialBlock A a b * spatialSwap12 =
        -spatialBlock A a b)
    (hcycle : ∀ a b,
      spatialBlock A a b +
          spatialCycle123 * spatialBlock A a b * spatialCycle123.transpose +
          spatialCycle123 ^ 2 * spatialBlock A a b *
            (spatialCycle123 ^ 2).transpose = 0)
    (hscore : ∀ i j a b,
      scoreGradingSign a * scoreGradingSign b * A (i, a) (j, b) =
        -A (i, a) (j, b)) :
    ∃! ab : ℝ × ℝ,
      A = ab.1 • tensorMatrix spatialTensor scoreGenerator02 +
        ab.2 • tensorMatrix spatialTensor scoreGenerator12 := by
  have hex : ∀ a b : Fin 3, ∃ k : ℝ,
      spatialBlock A a b = k • spatialTensor := by
    intro a b
    exact (spatialRelation_unique (spatialBlock A a b)
      (hrow a b) (hcol a b) (h34 a b) (h12 a b) (hcycle a b)).exists
  choose coeff hcoeff using hex
  let L : Matrix (Fin 3) (Fin 3) ℝ := fun a b => coeff a b
  have hcoeff_skew : ∀ a b, coeff b a = -coeff a b := by
    intro a b
    have hab := congrFun (congrFun (hcoeff a b) 0) 2
    have hba := congrFun (congrFun (hcoeff b a) 2) 0
    have hA := congrFun (congrFun hskew (0, a)) (2, b)
    simp [spatialBlock, spatialTensor, Matrix.smul_apply, Fin.isValue] at hab hba hA
    ring_nf at hab hba
    linarith
  have hLskew : L.transpose = -L := by
    ext a b
    change coeff b a = -coeff a b
    exact hcoeff_skew a b
  have hcoeff_odd : ∀ a b,
      scoreGradingSign a * scoreGradingSign b * coeff a b = -coeff a b := by
    intro a b
    have hab := congrFun (congrFun (hcoeff a b) 0) 0
    have hs := hscore 0 0 a b
    simp [spatialBlock, spatialTensor, Matrix.smul_apply, Fin.isValue] at hab
    ring_nf at hab
    rw [hab] at hs
    linarith
  have hLodd : scoreGrading * L * scoreGrading = -L := by
    have hleft : ∀ a b, (scoreGrading * L) a b =
        scoreGradingSign a * L a b := by
      intro a b
      change (∑ k : Fin 3, scoreGrading a k * L k b) =
        scoreGradingSign a * L a b
      fin_cases a <;> fin_cases b <;>
        simp [L, scoreGrading, scoreGradingSign, Fin.sum_univ_three, Fin.isValue]
    ext a b
    have hdiag : (scoreGrading * L * scoreGrading) a b =
        scoreGradingSign a * scoreGradingSign b * L a b := by
      change (∑ k : Fin 3, (scoreGrading * L) a k * scoreGrading k b) =
        scoreGradingSign a * scoreGradingSign b * L a b
      simp_rw [hleft]
      fin_cases a <;> fin_cases b <;>
        simp [L, scoreGrading, scoreGradingSign, Fin.sum_univ_three,
          Fin.isValue]
    rw [hdiag]
    change scoreGradingSign a * scoreGradingSign b * coeff a b = -coeff a b
    exact hcoeff_odd a b
  obtain ⟨ab, hab, _⟩ := gradingOdd_skew_score_classification L hLskew hLodd
  have hAform : A = ab.1 • tensorMatrix spatialTensor scoreGenerator02 +
      ab.2 • tensorMatrix spatialTensor scoreGenerator12 := by
    ext ia jb
    rcases ia with ⟨i, a⟩
    rcases jb with ⟨j, b⟩
    have hblock := congrFun (congrFun (hcoeff a b) i) j
    have hblock' : A (i, a) (j, b) = coeff a b * spatialTensor i j := by
      simpa [spatialBlock, Matrix.smul_apply] using hblock
    have hscoreEntry := congrFun (congrFun hab a) b
    simp only [L] at hscoreEntry
    simp [tensorMatrix, Matrix.smul_apply, Matrix.add_apply]
    rw [hblock', hscoreEntry]
    simp [Matrix.smul_apply, Matrix.add_apply]
    ring
  refine ⟨ab, hAform, ?_⟩
  intro cd hcd
  have heq := hcd.symm.trans hAform
  have h20 := congrFun (congrFun heq (0, 2)) (0, 0)
  have h21 := congrFun (congrFun heq (0, 2)) (0, 1)
  simp [tensorMatrix, spatialTensor, scoreGenerator02, scoreGenerator12,
    Matrix.smul_apply, Matrix.add_apply, Fin.isValue] at h20 h21
  exact Prod.ext (by linarith) (by linarith)

/-- The quarter turn sends `L₁₂` to `-L₀₂`, exactly as in the
manuscript's second pulse. -/
theorem scoreQuarterTurn_conjugates_generator :
    scoreQuarterTurn * scoreGenerator12 * scoreQuarterTurn.transpose =
      -scoreGenerator02 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [scoreQuarterTurn, scoreGenerator12, scoreGenerator02,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- The two displayed tetrahedral pulses are an exact orthogonal frame with
squared Hilbert--Schmidt norm two. -/
theorem twoPulse_exact_orthogonal_frame :
    hilbertSchmidtInner pulseZero pulseQuarterTurn = 0 ∧
      hilbertSchmidtInner pulseZero pulseZero = 2 ∧
      hilbertSchmidtInner pulseQuarterTurn pulseQuarterTurn = 2 := by
  norm_num [pulseZero, pulseQuarterTurn, hilbertSchmidtInner, tensorMatrix,
    spatialTensor, scoreGenerator02, scoreGenerator12,
    Fintype.sum_prod_type, Fin.sum_univ_succ]

end
end TetrahedralOddPulseFrame
end NCG
