/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Normal-factor partial trace and branch-purity margin

Finite matrix implementation of the conditional sign effect in
`thm:SMST-one-branch-purity`.  The normal factor is traced out with the exact
`1 / dim(H_N)` normalization, and positivity is inherited block by block.
-/

open Matrix Finset
open scoped ComplexOrder MatrixOrder Kronecker

namespace NCG
namespace NormalBranchPurityMargin

/-- The matter block of an operator at a fixed normal coordinate. -/
def normalDiagonalBlock {n m : Type*}
    (X : Matrix (n × m) (n × m) ℂ) (i : n) : Matrix m m ℂ :=
  X.submatrix (fun a => (i, a)) (fun a => (i, a))

/-- Normalized partial trace over the saturated normal factor. -/
noncomputable def normalizedNormalPartialTrace {n m : Type*}
    [Fintype n] (X : Matrix (n × m) (n × m) ℂ) : Matrix m m ℂ :=
  fun a b => ((Fintype.card n : ℝ)⁻¹ : ℝ) •
    ∑ i, X (i, a) (i, b)

/-- The normalized normal partial trace is unital. -/
theorem normalizedNormalPartialTrace_one
    {n m : Type*} [Fintype n] [Nonempty n] [Fintype m]
    [DecidableEq n] [DecidableEq m] :
    normalizedNormalPartialTrace (n := n) (m := m) 1 = 1 := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [normalizedNormalPartialTrace, Matrix.one_apply,
      Fintype.card_ne_zero]
  · simp [normalizedNormalPartialTrace, normalDiagonalBlock,
      Matrix.one_apply, hab]

/-- The normalized normal partial trace preserves addition. -/
theorem normalizedNormalPartialTrace_add
    {n m : Type*} [Fintype n]
    (X Y : Matrix (n × m) (n × m) ℂ) :
    normalizedNormalPartialTrace (X + Y) =
      normalizedNormalPartialTrace X + normalizedNormalPartialTrace Y := by
  ext a b
  simp [normalizedNormalPartialTrace, Matrix.add_apply,
    Finset.sum_add_distrib]

/-- The normalized normal partial trace commutes with real scalar multiplication. -/
theorem normalizedNormalPartialTrace_real_smul
    {n m : Type*} [Fintype n]
    (r : ℝ) (X : Matrix (n × m) (n × m) ℂ) :
    normalizedNormalPartialTrace (r • X) =
      r • normalizedNormalPartialTrace X := by
  ext a b
  simp [normalizedNormalPartialTrace, Matrix.smul_apply,
    Finset.smul_sum]
  ring

/-- The normalized normal partial trace preserves subtraction. -/
theorem normalizedNormalPartialTrace_sub
    {n m : Type*} [Fintype n]
    (X Y : Matrix (n × m) (n × m) ℂ) :
    normalizedNormalPartialTrace (X - Y) =
      normalizedNormalPartialTrace X - normalizedNormalPartialTrace Y := by
  ext a b
  simp [normalizedNormalPartialTrace, Matrix.sub_apply,
    Finset.sum_sub_distrib]
  ring

/-- The normalized normal partial trace commutes with conjugate transpose. -/
theorem normalizedNormalPartialTrace_conjTranspose
    {n m : Type*} [Fintype n]
    (X : Matrix (n × m) (n × m) ℂ) :
    normalizedNormalPartialTrace Xᴴ =
      (normalizedNormalPartialTrace X)ᴴ := by
  ext a b
  simp [normalizedNormalPartialTrace, Matrix.conjTranspose_apply,
    map_sum]

/-- Positivity passes from the full carrier to the normalized partial trace. -/
theorem normalizedNormalPartialTrace_posSemidef
    {n m : Type*} [Fintype n] [Nonempty n]
    (X : Matrix (n × m) (n × m) ℂ) (hX : X.PosSemidef) :
    (normalizedNormalPartialTrace X).PosSemidef := by
  classical
  have heq : normalizedNormalPartialTrace X =
      ((Fintype.card n : ℝ)⁻¹) • ∑ i, normalDiagonalBlock X i := by
    ext a b
    simp [normalizedNormalPartialTrace, normalDiagonalBlock,
      Finset.sum_apply, Matrix.sum_apply]
  rw [heq]
  have hsum : (∑ i, normalDiagonalBlock X i).PosSemidef := by
    apply Finset.sum_induction
    · intro A B hA hB
      exact hA.add hB
    · exact Matrix.PosSemidef.zero
    · intro i _
      exact hX.submatrix (fun a => (i, a))
  exact hsum.smul (inv_nonneg.mpr (by positivity :
    (0 : ℝ) ≤ Fintype.card n))

/-- Positive sign projection associated with a self-adjoint involution. -/
noncomputable def positiveSignProjection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ((2 : ℂ)⁻¹) • (1 + J)

theorem positiveSignProjection_isHermitian_idempotent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℂ) (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    (positiveSignProjection J)ᴴ = positiveSignProjection J ∧
      positiveSignProjection J * positiveSignProjection J =
        positiveSignProjection J := by
  constructor
  · simp [positiveSignProjection, hJH]
  · simp [positiveSignProjection, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_mul, Matrix.mul_add, hJ2]
    module

theorem positiveSignProjection_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℂ) (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    (positiveSignProjection J).PosSemidef := by
  let P := positiveSignProjection J
  have hP := positiveSignProjection_isHermitian_idempotent J hJH hJ2
  have hsq := Matrix.posSemidef_conjTranspose_mul_self P
  rw [hP.1, hP.2] at hsq
  exact hsq

/-- Conditional sign effect after forgetting the normal factor. -/
noncomputable def conditionalSignEffect {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (J : Matrix (n × m) (n × m) ℂ) : Matrix m m ℂ :=
  normalizedNormalPartialTrace (positiveSignProjection J)

/-- Centered matter sign `T = 2E₊ - I`. -/
noncomputable def centeredMatterSign {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (J : Matrix (n × m) (n × m) ℂ) : Matrix m m ℂ :=
  (2 : ℂ) • conditionalSignEffect J - 1

/-- The conditional sign effect is positive semidefinite. -/
theorem conditionalSignEffect_posSemidef
    {n m : Type*} [Fintype n] [Nonempty n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (J : Matrix (n × m) (n × m) ℂ)
    (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    (conditionalSignEffect J).PosSemidef :=
  normalizedNormalPartialTrace_posSemidef _
    (positiveSignProjection_posSemidef J hJH hJ2)

/-- Operators constant on the normal factor. -/
def normalSeparatedOperator {n m : Type*}
    [Fintype n] [DecidableEq n]
    (S : Matrix m m ℂ) : Matrix (n × m) (n × m) ℂ :=
  (1 : Matrix n n ℂ) ⊗ₖ S

/-- Hilbert--Schmidt pairing on the product carrier, with sums written in
factor order. -/
def productHilbertSchmidtInner {n m : Type*}
    [Fintype n] [Fintype m]
    (X Y : Matrix (n × m) (n × m) ℂ) : ℂ :=
  ∑ i, ∑ a, ∑ j, ∑ b, star (X (i, a) (j, b)) * Y (i, a) (j, b)

/-- Hilbert--Schmidt pairing on the matter factor. -/
def matterHilbertSchmidtInner {m : Type*} [Fintype m]
    (X Y : Matrix m m ℂ) : ℂ :=
  ∑ a, ∑ b, star (X a b) * Y a b

/-- Pairing with a normal-separated operator is exactly the pairing after
normalized partial trace, multiplied by the normal dimension. -/
theorem productHilbertSchmidtInner_normalSeparated
    {n m : Type*} [Fintype n] [Nonempty n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (X : Matrix (n × m) (n × m) ℂ) (S : Matrix m m ℂ) :
    productHilbertSchmidtInner X (normalSeparatedOperator S) =
      (Fintype.card n : ℂ) *
        matterHilbertSchmidtInner (normalizedNormalPartialTrace X) S := by
  classical
  have hcard : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcancel (z : n → ℂ) :
      (Fintype.card n : ℂ) *
          (∑ i, (Fintype.card n : ℂ)⁻¹ * z i) = ∑ i, z i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hcard]
  simp [productHilbertSchmidtInner, matterHilbertSchmidtInner,
    normalSeparatedOperator, normalizedNormalPartialTrace,
    Matrix.one_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  calc
    (∑ i, star (X (i, a) (i, b)) * S a b) =
        (∑ i, star (X (i, a) (i, b))) * S a b := by
          rw [Finset.sum_mul]
    _ = ((Fintype.card n : ℂ) *
          ∑ i, (Fintype.card n : ℂ)⁻¹ * star (X (i, a) (i, b))) * S a b := by
          rw [hcancel (fun i => star (X (i, a) (i, b)))]
    _ = (Fintype.card n : ℂ) *
          ((∑ i, (Fintype.card n : ℂ)⁻¹ * star (X (i, a) (i, b))) * S a b) := by
          ring

/-- A separated operator has the prescribed normalized partial trace. -/
theorem normalizedNormalPartialTrace_normalSeparated
    {n m : Type*} [Fintype n] [Nonempty n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (S : Matrix m m ℂ) :
    normalizedNormalPartialTrace (normalSeparatedOperator (n := n) S) = S := by
  ext a b
  simp [normalizedNormalPartialTrace, normalSeparatedOperator,
    Matrix.one_apply, Fintype.card_ne_zero]

/-- Product-factor Hilbert--Schmidt pairing is the usual trace pairing. -/
theorem trace_conjTranspose_mul_eq_productHilbertSchmidtInner
    {n m : Type*} [Fintype n] [Fintype m]
    (X Y : Matrix (n × m) (n × m) ℂ) :
    Matrix.trace (Xᴴ * Y) = productHilbertSchmidtInner X Y := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, productHilbertSchmidtInner,
    Matrix.conjTranspose_apply, ← Finset.univ_product_univ,
    Finset.sum_product]
  simp only [starRingEnd_apply]
  have h₁ :
      (∑ i : n, ∑ a : m, ∑ j : n, ∑ b : m,
          star (X (j, b) (i, a)) * Y (j, b) (i, a)) =
        ∑ i : n, ∑ j : n, ∑ a : m, ∑ b : m,
          star (X (j, b) (i, a)) * Y (j, b) (i, a) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [h₁, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have h₂ :
      (∑ i : n, ∑ a : m, ∑ b : m,
          star (X (j, b) (i, a)) * Y (j, b) (i, a)) =
        ∑ i : n, ∑ b : m, ∑ a : m,
          star (X (j, b) (i, a)) * Y (j, b) (i, a) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [h₂, Finset.sum_comm]

/-- Vanishing product-factor Hilbert--Schmidt square detects the zero matrix. -/
theorem productHilbertSchmidtInner_self_eq_zero_iff
    {n m : Type*} [Fintype n] [Fintype m]
    (X : Matrix (n × m) (n × m) ℂ) :
    productHilbertSchmidtInner X X = 0 ↔ X = 0 := by
  rw [← trace_conjTranspose_mul_eq_productHilbertSchmidtInner]
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff

lemma productHilbertSchmidtInner_add_left
    {n m : Type*} [Fintype n] [Fintype m]
    (X Y Z : Matrix (n × m) (n × m) ℂ) :
    productHilbertSchmidtInner (X + Y) Z =
      productHilbertSchmidtInner X Z + productHilbertSchmidtInner Y Z := by
  simp [productHilbertSchmidtInner, Matrix.add_apply, star_add, add_mul,
    Finset.sum_add_distrib]

lemma productHilbertSchmidtInner_add_right
    {n m : Type*} [Fintype n] [Fintype m]
    (X Y Z : Matrix (n × m) (n × m) ℂ) :
    productHilbertSchmidtInner X (Y + Z) =
      productHilbertSchmidtInner X Y + productHilbertSchmidtInner X Z := by
  simp [productHilbertSchmidtInner, Matrix.add_apply, mul_add,
    Finset.sum_add_distrib]

lemma productHilbertSchmidtInner_conjSymm
    {n m : Type*} [Fintype n] [Fintype m]
    (X Y : Matrix (n × m) (n × m) ℂ) :
    star (productHilbertSchmidtInner X Y) =
      productHilbertSchmidtInner Y X := by
  simp [productHilbertSchmidtInner, star_sum, star_mul', mul_comm]

/-- The residual from the normal-separated conditional expectation. -/
noncomputable def normalSeparationResidual
    {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (X : Matrix (n × m) (n × m) ℂ) : Matrix (n × m) (n × m) ℂ :=
  X - normalSeparatedOperator (normalizedNormalPartialTrace X)

theorem normalizedNormalPartialTrace_residual
    {n m : Type*} [Fintype n] [Nonempty n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (X : Matrix (n × m) (n × m) ℂ) :
    normalizedNormalPartialTrace (normalSeparationResidual X) = 0 := by
  rw [normalSeparationResidual, normalizedNormalPartialTrace_sub,
    normalizedNormalPartialTrace_normalSeparated, sub_self]

/-- The normal-separation residual is Hilbert--Schmidt orthogonal to every
operator constant on the normal factor. -/
theorem normalSeparationResidual_orthogonal
    {n m : Type*} [Fintype n] [Nonempty n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (X : Matrix (n × m) (n × m) ℂ) (S : Matrix m m ℂ) :
    productHilbertSchmidtInner (normalSeparationResidual X)
      (normalSeparatedOperator S) = 0 := by
  rw [productHilbertSchmidtInner_normalSeparated]
  rw [normalizedNormalPartialTrace_residual]
  simp [matterHilbertSchmidtInner]

/-- Pythagoras for the conditional expectation onto normal-separated
operators. -/
theorem normalSeparation_pythagoras
    {n m : Type*} [Fintype n] [Nonempty n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (X : Matrix (n × m) (n × m) ℂ) :
    productHilbertSchmidtInner X X =
      productHilbertSchmidtInner (normalSeparationResidual X)
          (normalSeparationResidual X) +
        productHilbertSchmidtInner
          (normalSeparatedOperator (n := n) (normalizedNormalPartialTrace X))
          (normalSeparatedOperator (n := n) (normalizedNormalPartialTrace X)) := by
  let R := normalSeparationResidual X
  let Q := normalSeparatedOperator (n := n) (normalizedNormalPartialTrace X)
  have hX : X = R + Q := by
    simp [R, Q, normalSeparationResidual]
  have hRQ : productHilbertSchmidtInner R Q = 0 :=
    normalSeparationResidual_orthogonal X _
  have hQR : productHilbertSchmidtInner Q R = 0 := by
    have h := congrArg star hRQ
    rwa [productHilbertSchmidtInner_conjSymm, star_zero] at h
  calc
    productHilbertSchmidtInner X X =
        productHilbertSchmidtInner (R + Q) (R + Q) := by rw [hX]
    _ = productHilbertSchmidtInner R R +
        productHilbertSchmidtInner Q Q := by
      rw [productHilbertSchmidtInner_add_left,
        productHilbertSchmidtInner_add_right,
        productHilbertSchmidtInner_add_right, hRQ, hQR]
      simp
    _ = _ := rfl

/-- The centered sign obtained from `E₊` is exactly the normalized partial
trace of the locked grading. -/
theorem centeredMatterSign_eq_normalizedNormalPartialTrace
    {n m : Type*} [Fintype n] [Nonempty n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (J : Matrix (n × m) (n × m) ℂ) :
    centeredMatterSign J = normalizedNormalPartialTrace J := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [centeredMatterSign, conditionalSignEffect,
      normalizedNormalPartialTrace, positiveSignProjection,
      Fintype.card_ne_zero, Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
    ring
  · simp [centeredMatterSign, conditionalSignEffect,
      normalizedNormalPartialTrace, positiveSignProjection, hab]
    rw [← Finset.mul_sum]
    ring

/-- Matter-factor Hilbert--Schmidt pairing is the trace pairing. -/
theorem trace_conjTranspose_mul_eq_matterHilbertSchmidtInner
    {m : Type*} [Fintype m]
    (X Y : Matrix m m ℂ) :
    Matrix.trace (Xᴴ * Y) = matterHilbertSchmidtInner X Y := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, matterHilbertSchmidtInner,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

/-- For a self-adjoint involution, the displayed branch margin is exactly the
Hilbert--Schmidt square of the non-separated normal residual. -/
theorem involution_branchMargin_eq_residual
    {n m : Type*} [Fintype n] [Nonempty n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (J : Matrix (n × m) (n × m) ℂ)
    (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    let T := normalizedNormalPartialTrace J
    productHilbertSchmidtInner (normalSeparationResidual J)
        (normalSeparationResidual J) =
      (Fintype.card n : ℂ) * Matrix.trace (1 - T * T) := by
  dsimp
  have hT : (normalizedNormalPartialTrace J)ᴴ =
      normalizedNormalPartialTrace J := by
    rw [← normalizedNormalPartialTrace_conjTranspose, hJH]
  have hJJ : productHilbertSchmidtInner J J =
      (Fintype.card n : ℂ) * (Fintype.card m : ℂ) := by
    rw [← trace_conjTranspose_mul_eq_productHilbertSchmidtInner,
      hJH, hJ2]
    simp [Matrix.trace, Fintype.card_prod]
  have hsep :
      productHilbertSchmidtInner
          (normalSeparatedOperator (n := n) (normalizedNormalPartialTrace J))
          (normalSeparatedOperator (n := n) (normalizedNormalPartialTrace J)) =
        (Fintype.card n : ℂ) *
          Matrix.trace (normalizedNormalPartialTrace J *
            normalizedNormalPartialTrace J) := by
    rw [productHilbertSchmidtInner_normalSeparated,
      normalizedNormalPartialTrace_normalSeparated,
      ← trace_conjTranspose_mul_eq_matterHilbertSchmidtInner,
      hT]
  have hpyth := normalSeparation_pythagoras J
  rw [hJJ, hsep] at hpyth
  rw [Matrix.trace_sub]
  have hone : Matrix.trace (1 : Matrix m m ℂ) = Fintype.card m := by
    simp [Matrix.trace]
  rw [hone]
  linear_combination -hpyth

/-- Zero branch margin is equivalent to exact separation of the locked
grading over the normal factor. -/
theorem zeroBranchMargin_iff_normalSeparated
    {n m : Type*} [Fintype n] [Nonempty n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (J : Matrix (n × m) (n × m) ℂ)
    (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    let T := normalizedNormalPartialTrace J
    (Fintype.card n : ℂ) * Matrix.trace (1 - T * T) = 0 ↔
      J = normalSeparatedOperator T := by
  dsimp
  rw [← involution_branchMargin_eq_residual J hJH hJ2,
    productHilbertSchmidtInner_self_eq_zero_iff]
  exact sub_eq_zero

/-- Algebraic equality of the two displayed branch-margin formulas. -/
theorem branchMargin_formula
    {m : Type*} [Fintype m] [DecidableEq m]
    (d : ℝ) (E : Matrix m m ℂ) :
    (4 * d : ℂ) * Matrix.trace (E - E * E) =
      (d : ℂ) * Matrix.trace
        (1 - ((2 : ℂ) • E - 1) * ((2 : ℂ) • E - 1)) := by
  simp [Matrix.trace_sub, Matrix.trace_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul]
  ring

/-- Sharpness of `E₊` is algebraically equivalent to involutivity of
`T = 2E₊ - I`. -/
theorem projection_iff_centeredSign_involutive
    {m : Type*} [Fintype m] [DecidableEq m]
    (E : Matrix m m ℂ) :
    E * E = E ↔ ((2 : ℂ) • E - 1) * ((2 : ℂ) • E - 1) = 1 := by
  constructor
  · intro hE
    simp [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, hE]
    module
  · intro hT
    ext i j
    have hij := congrFun (congrFun hT i) j
    simp [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul] at hij
    have hmul := congrFun (congrFun (show
      ((2 : ℂ) • E) * ((2 : ℂ) • E) = (4 : ℂ) • (E * E) by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        norm_num) i) j
    simp at hmul
    linear_combination (1 / 4 : ℂ) * hij

/-- Reversing the sign of an involution exchanges its two spectral
projections. -/
theorem one_sub_positiveSignProjection_eq_negative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℂ) :
    1 - positiveSignProjection J = positiveSignProjection (-J) := by
  ext i j
  by_cases hij : i = j <;>
    simp [positiveSignProjection, Matrix.one_apply, hij] <;> ring

/-- The conditional sign effect is an operator interval element:
`0 ≼ E₊ ≼ I`.  The second component is the positive-semidefiniteness of
`I - E₊`. -/
theorem conditionalSignEffect_between_zero_and_one
    {n m : Type*} [Fintype n] [Nonempty n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (J : Matrix (n × m) (n × m) ℂ)
    (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    (conditionalSignEffect J).PosSemidef ∧
      (1 - conditionalSignEffect J).PosSemidef := by
  constructor
  · exact conditionalSignEffect_posSemidef J hJH hJ2
  · have hnegH : (-J)ᴴ = -J := by simp [hJH]
    have hneg2 : (-J) * (-J) = 1 := by
      simp [hJ2]
    have hprojection :
        (1 - positiveSignProjection J).PosSemidef := by
      rw [one_sub_positiveSignProjection_eq_negative]
      exact positiveSignProjection_posSemidef (-J) hnegH hneg2
    have htrace := normalizedNormalPartialTrace_posSemidef
      (1 - positiveSignProjection J) hprojection
    rw [normalizedNormalPartialTrace_sub,
      normalizedNormalPartialTrace_one] at htrace
    exact htrace

/-- Normal-separated operators multiply entirely on the matter factor. -/
theorem normalSeparatedOperator_mul
    {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (A B : Matrix m m ℂ) :
    normalSeparatedOperator (n := n) A * normalSeparatedOperator B =
      normalSeparatedOperator (A * B) := by
  simp [normalSeparatedOperator, ← Matrix.mul_kronecker_mul]

/-- If an involution is normal-separated, then its matter factor is itself an
involution. -/
theorem separated_involution_has_involutive_matter_factor
    {n m : Type*} [Fintype n] [Nonempty n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (J : Matrix (n × m) (n × m) ℂ) (T : Matrix m m ℂ)
    (hJ2 : J * J = 1) (hsep : J = normalSeparatedOperator T) :
    T * T = 1 := by
  have hproduct : normalSeparatedOperator (n := n) (T * T) = 1 := by
    rw [← normalSeparatedOperator_mul, ← hsep, hJ2]
  have htrace := congrArg normalizedNormalPartialTrace hproduct
  rw [normalizedNormalPartialTrace_normalSeparated,
    normalizedNormalPartialTrace_one] at htrace
  exact htrace

/-- The one-positive-branch theorem in its manuscript form.  With
`E₊ = d_N⁻¹ Tr_{H_N} P₊` and `T = 2E₊ - I`, the branch margin vanishes exactly
when `E₊` is a projection, exactly when `T` is an involution, and exactly when
the locked grading is constant on the normal factor. -/
theorem onePositiveBranch_zeroMargin_equivalences
    {n m : Type*} [Fintype n] [Nonempty n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (J : Matrix (n × m) (n × m) ℂ)
    (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    let E := conditionalSignEffect J
    let T := centeredMatterSign J
    ((4 * Fintype.card n : ℂ) * Matrix.trace (E - E * E) = 0 ↔
        E * E = E) ∧
      (E * E = E ↔ T * T = 1) ∧
      (T * T = 1 ↔ J = normalSeparatedOperator T) := by
  dsimp
  have hcenter := centeredMatterSign_eq_normalizedNormalPartialTrace J
  have hprojection :=
    projection_iff_centeredSign_involutive (conditionalSignEffect J)
  have hseparation :
      centeredMatterSign J * centeredMatterSign J = 1 ↔
        J = normalSeparatedOperator (centeredMatterSign J) := by
    constructor
    · intro hT2
      have hzero :
          (Fintype.card n : ℂ) * Matrix.trace
            (1 - normalizedNormalPartialTrace J *
              normalizedNormalPartialTrace J) = 0 := by
        rw [← hcenter, hT2]
        simp
      have hsep := (zeroBranchMargin_iff_normalSeparated J hJH hJ2).mp hzero
      rwa [← hcenter] at hsep
    · intro hsep
      exact separated_involution_has_involutive_matter_factor J
        (centeredMatterSign J) hJ2 hsep
  have hmargin :
      (4 * Fintype.card n : ℂ) * Matrix.trace
          (conditionalSignEffect J -
            conditionalSignEffect J * conditionalSignEffect J) = 0 ↔
        centeredMatterSign J * centeredMatterSign J = 1 := by
    rw [show (4 * Fintype.card n : ℂ) =
      (4 * (Fintype.card n : ℝ) : ℂ) by norm_num]
    rw [branchMargin_formula (Fintype.card n : ℝ)
      (conditionalSignEffect J)]
    change ((Fintype.card n : ℂ) * Matrix.trace
      (1 - centeredMatterSign J * centeredMatterSign J) = 0 ↔ _)
    rw [hseparation]
    rw [hcenter]
    exact zeroBranchMargin_iff_normalSeparated J hJH hJ2
  exact ⟨hmargin.trans hprojection.symm, hprojection, hseparation⟩

/-- A saturated synthesis matrix reconstructs every inserted operator from its
Gram compression.  In the manuscript, `Wdagger` is the Moore--Penrose inverse;
only the saturation identity `W Wdagger = I` is needed for this formula. -/
theorem saturatedGram_reconstructs_insertedOperator
    {h k : Type*} [Fintype h] [Fintype k] [DecidableEq h]
    (W : Matrix h k ℂ) (Wdagger : Matrix k h ℂ)
    (P : Matrix h h ℂ) (hsaturated : W * Wdagger = 1) :
    Wdaggerᴴ * (Wᴴ * P * W) * Wdagger = P := by
  calc
    Wdaggerᴴ * (Wᴴ * P * W) * Wdagger =
        (W * Wdagger)ᴴ * P * (W * Wdagger) := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = P := by rw [hsaturated]; simp

end NormalBranchPurityMargin
end NCG
