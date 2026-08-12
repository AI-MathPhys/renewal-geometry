/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Finite Naimark dilation of a matrix POVM

For a finite family of positive effects summing to the identity, this file
constructs the standard explicit Naimark dilation on `ι × E`. The isometry
stacks the positive square roots of the effects and the sharp outcomes are
the coordinate projections.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

set_option linter.unusedDecidableInType false

/-- The analysis isometry of a finite POVM, obtained by stacking the square
roots of all effects. -/
noncomputable def finiteNaimarkIsometry {ι E : Type*} [Fintype ι]
    [Fintype E] [DecidableEq E] (F : ι → Matrix E E ℂ) :
    Matrix (ι × E) E ℂ :=
  fun ie e => (CFC.sqrt (F ie.1)) ie.2 e

/-- The sharp coordinate projection associated with one Naimark outcome. -/
def finiteNaimarkProjection {ι E : Type*} [DecidableEq ι]
    [DecidableEq E] (i : ι) : Matrix (ι × E) (ι × E) ℂ :=
  Matrix.diagonal fun je => if je.1 = i then 1 else 0

/-- Positive POVM effects summing to one make the stacked square-root map an
isometry. -/
theorem finiteNaimarkIsometry_isometry {ι E : Type*} [Fintype ι]
    [Fintype E] [DecidableEq ι] [DecidableEq E]
    (F : ι → Matrix E E ℂ) (hF : ∀ i, (F i).PosSemidef)
    (hsum : ∑ i, F i = 1) :
    (finiteNaimarkIsometry F)ᴴ * finiteNaimarkIsometry F = 1 := by
  classical
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    finiteNaimarkIsometry, Fintype.sum_prod_type]
  calc
    ∑ i, ∑ e, star ((CFC.sqrt (F i)) e x) *
          (CFC.sqrt (F i)) e y =
        ∑ i, (CFC.sqrt (F i) * CFC.sqrt (F i)) x y := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Matrix.mul_apply]
          congr 1
          funext e
          have hs := sqrt_isHermitian (F i)
          exact congrArg (fun M : Matrix E E ℂ => M x e) hs ▸ rfl
    _ = ∑ i, (F i) x y := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [sqrt_mul_self_eq (F i) (hF i)]
    _ = (1 : Matrix E E ℂ) x y := by
          simpa only [Matrix.sum_apply] using
            congrArg (fun M : Matrix E E ℂ => M x y) hsum

/-- Every sharp Naimark outcome is a positive projection. -/
theorem finiteNaimarkProjection_positive_idempotent
    {ι E : Type*} [Fintype ι] [Fintype E]
    [DecidableEq ι] [DecidableEq E] (i : ι) :
    (finiteNaimarkProjection (E := E) i).PosSemidef
      ∧ finiteNaimarkProjection (E := E) i *
          finiteNaimarkProjection (E := E) i =
            finiteNaimarkProjection (E := E) i := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro je
    by_cases h : je.1 = i <;> simp [h]
  · rw [finiteNaimarkProjection, Matrix.diagonal_mul_diagonal]
    congr 1
    funext je
    by_cases h : je.1 = i <;> simp [h]

/-- Distinct sharp Naimark outcomes are orthogonal. -/
theorem finiteNaimarkProjection_orthogonal
    {ι E : Type*} [Fintype ι] [Fintype E]
    [DecidableEq ι] [DecidableEq E] {i j : ι} (hij : i ≠ j) :
    finiteNaimarkProjection (E := E) i *
        finiteNaimarkProjection (E := E) j = 0 := by
  rw [finiteNaimarkProjection, finiteNaimarkProjection,
    Matrix.diagonal_mul_diagonal]
  ext je ke
  by_cases hEq : je = ke
  · subst ke
    rw [Matrix.diagonal_apply_eq]
    simp only [Matrix.zero_apply]
    by_cases hji : je.1 = i
    · have hjj : je.1 ≠ j := by
        intro h
        exact hij (hji.symm.trans h)
      simp [hji, hjj, hij]
    · simp [hji]
  · rw [Matrix.diagonal_apply_ne _ hEq]
    rfl

/-- The sharp Naimark outcomes resolve the identity. -/
theorem finiteNaimarkProjection_sum_one
    {ι E : Type*} [Fintype ι] [Fintype E]
    [DecidableEq ι] [DecidableEq E] :
    ∑ i : ι, finiteNaimarkProjection (E := E) i = 1 := by
  ext je ke
  by_cases h : je = ke
  · subst ke
    simp [Matrix.sum_apply, finiteNaimarkProjection,
      Matrix.diagonal_apply_eq]
  · simp [Matrix.sum_apply, finiteNaimarkProjection,
      Matrix.diagonal_apply, h]

/-- Compression of the sharp coordinate outcome recovers the original POVM
effect. -/
theorem finiteNaimarkProjection_compression
    {ι E : Type*} [Fintype ι] [Fintype E]
    [DecidableEq ι] [DecidableEq E]
    (F : ι → Matrix E E ℂ) (hF : ∀ i, (F i).PosSemidef) (i : ι) :
    (finiteNaimarkIsometry F)ᴴ * finiteNaimarkProjection (E := E) i *
        finiteNaimarkIsometry F = F i := by
  classical
  rw [Matrix.mul_assoc]
  ext x y
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
    finiteNaimarkIsometry, finiteNaimarkProjection,
    Matrix.diagonal_apply, Fintype.sum_prod_type]
  calc
    ∑ e, star ((CFC.sqrt (F i)) e x) * (CFC.sqrt (F i)) e y =
        (CFC.sqrt (F i) * CFC.sqrt (F i)) x y := by
          rw [Matrix.mul_apply]
          apply Finset.sum_congr rfl
          intro e he
          have hs := sqrt_isHermitian (F i)
          exact congrArg (fun M : Matrix E E ℂ => M x e) hs ▸ rfl
    _ = (F i) x y := by rw [sqrt_mul_self_eq (F i) (hF i)]

/-- Full finite Naimark theorem: the explicit dilation is isometric, its
outcomes are positive orthogonal projections resolving one, and every effect
is recovered by compression. -/
theorem finiteNaimarkDilation
    {ι E : Type*} [Fintype ι] [Fintype E]
    [DecidableEq ι] [DecidableEq E]
    (F : ι → Matrix E E ℂ) (hF : ∀ i, (F i).PosSemidef)
    (hsum : ∑ i, F i = 1) :
    (finiteNaimarkIsometry F)ᴴ * finiteNaimarkIsometry F = 1
      ∧ (∀ i : ι, (finiteNaimarkProjection (E := E) i).PosSemidef)
      ∧ (∀ i : ι, finiteNaimarkProjection (E := E) i *
          finiteNaimarkProjection (E := E) i =
            finiteNaimarkProjection (E := E) i)
      ∧ (∀ i j : ι, i ≠ j → finiteNaimarkProjection (E := E) i *
          finiteNaimarkProjection (E := E) j = 0)
      ∧ (∑ i : ι, finiteNaimarkProjection (E := E) i = 1)
      ∧ (∀ i : ι, (finiteNaimarkIsometry F)ᴴ *
          finiteNaimarkProjection (E := E) i *
            finiteNaimarkIsometry F = F i) := by
  refine ⟨finiteNaimarkIsometry_isometry F hF hsum, ?_, ?_, ?_,
    finiteNaimarkProjection_sum_one (ι := ι) (E := E), ?_⟩
  · intro i
    exact (finiteNaimarkProjection_positive_idempotent
      (ι := ι) (E := E) i).1
  · intro i
    exact (finiteNaimarkProjection_positive_idempotent
      (ι := ι) (E := E) i).2
  · intro i j hij
    exact finiteNaimarkProjection_orthogonal
      (ι := ι) (E := E) hij
  · intro i
    exact finiteNaimarkProjection_compression F hF i

end NCG
