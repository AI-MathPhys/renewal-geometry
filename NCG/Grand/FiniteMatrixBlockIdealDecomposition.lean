/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SourceIdealSplit
import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.Ideal.Basic

/-!
# Central supports of ideals in finite matrix-block algebras

This file proves the finite-dimensional structure-theory content of
`thm:central-source-decomposition`.  For an arbitrary two-sided ideal in a
finite product of full complex matrix algebras, its active blocks determine a
central self-adjoint projection.  Matrix units show that every active block
unit belongs to the ideal, so the ideal is exactly the range of that central
projection.  The complementary Peirce decomposition and uniqueness follow.
-/

open Matrix

namespace NCG

section MatrixBlocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (d : ι → Type*) [∀ b, Fintype (d b)] [∀ b, DecidableEq (d b)]

/-- A finite direct product of full complex matrix blocks. -/
abbrev FiniteMatrixBlockAlgebra := ∀ b, Matrix (d b) (d b) ℂ

/-- The block support of a two-sided ideal. -/
def matrixBlockIdealSupport
    (I : Ideal (FiniteMatrixBlockAlgebra d)) : Set ι :=
  {b | ∃ x ∈ I, x b ≠ 0}

/-- The central indicator of the matrix blocks on which an ideal is nonzero. -/
noncomputable def matrixBlockCentralSupport
    (I : Ideal (FiniteMatrixBlockAlgebra d)) : FiniteMatrixBlockAlgebra d :=
  by
    classical
    exact fun b => if b ∈ matrixBlockIdealSupport d I then 1 else 0

private theorem activeBlock_matrixUnit_mem
    (I : Ideal (FiniteMatrixBlockAlgebra d)) [I.IsTwoSided]
    {b : ι} (hb : b ∈ matrixBlockIdealSupport d I) (p q : d b) :
    Pi.single b (Matrix.single p q 1) ∈ I := by
  classical
  rcases hb with ⟨x, hxI, hxb⟩
  have hentry : ∃ i j, x b i j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hxb
    ext i j
    exact h i j
  rcases hentry with ⟨i, j, hij⟩
  let L : FiniteMatrixBlockAlgebra d :=
    Pi.single b (Matrix.single p i (x b i j)⁻¹)
  let R : FiniteMatrixBlockAlgebra d :=
    Pi.single b (Matrix.single j q 1)
  have hprod : L * x * R ∈ I :=
    Ideal.mul_mem_right R I (I.mul_mem_left L hxI)
  have heq : L * x * R = Pi.single b (Matrix.single p q 1) := by
    funext c
    by_cases hcb : c = b
    · subst c
      simp [L, R, Pi.single_apply, Matrix.single_mul_mul_single, hij]
    · simp [L, R, Pi.single_apply, hcb]
  rwa [heq] at hprod

private theorem activeBlock_unit_mem
    (I : Ideal (FiniteMatrixBlockAlgebra d)) [I.IsTwoSided]
    {b : ι} (hb : b ∈ matrixBlockIdealSupport d I) :
    Pi.single b (1 : Matrix (d b) (d b) ℂ) ∈ I := by
  classical
  rw [← Matrix.sum_single_one]
  have hsum : Pi.single b (∑ p, Matrix.single p p (1 : ℂ)) =
      ∑ p, (Pi.single b (Matrix.single p p (1 : ℂ)) :
        FiniteMatrixBlockAlgebra d) := by
    funext c
    by_cases hcb : c = b
    · subst c
      simp
    · simp [hcb]
  rw [hsum]
  exact Submodule.sum_mem I fun p _ => activeBlock_matrixUnit_mem d I hb p p

private theorem matrixBlockCentralSupport_mem
    (I : Ideal (FiniteMatrixBlockAlgebra d)) [I.IsTwoSided] :
    matrixBlockCentralSupport d I ∈ I := by
  classical
  have hsum : matrixBlockCentralSupport d I =
      ∑ b, if hb : b ∈ matrixBlockIdealSupport d I then
        (Pi.single b (1 : Matrix (d b) (d b) ℂ) :
          FiniteMatrixBlockAlgebra d) else 0 := by
    funext c
    rw [Finset.sum_apply, Finset.sum_eq_single c]
    · by_cases hc : c ∈ matrixBlockIdealSupport d I <;>
        simp [matrixBlockCentralSupport, hc]
    · intro b _ hbc
      by_cases hb : b ∈ matrixBlockIdealSupport d I
      · rw [dif_pos hb]
        exact Pi.single_eq_of_ne' hbc _
      · rw [dif_neg hb]
        rfl
    · simp
  rw [hsum]
  exact Submodule.sum_mem I fun b _ => by
    split_ifs with hb
    · exact activeBlock_unit_mem d I hb
    · exact I.zero_mem

@[simp] theorem matrixBlockCentralSupport_apply_of_mem
    (I : Ideal (FiniteMatrixBlockAlgebra d)) {b : ι}
    (hb : b ∈ matrixBlockIdealSupport d I) :
    matrixBlockCentralSupport d I b = 1 := by
  classical
  simp [matrixBlockCentralSupport, hb]

@[simp] theorem matrixBlockCentralSupport_apply_of_not_mem
    (I : Ideal (FiniteMatrixBlockAlgebra d)) {b : ι}
    (hb : b ∉ matrixBlockIdealSupport d I) :
    matrixBlockCentralSupport d I b = 0 := by
  classical
  simp [matrixBlockCentralSupport, hb]

/-- The support indicator is a central self-adjoint projection. -/
theorem matrixBlockCentralSupport_isCentralProjection
    (I : Ideal (FiniteMatrixBlockAlgebra d)) :
    matrixBlockCentralSupport d I * matrixBlockCentralSupport d I =
        matrixBlockCentralSupport d I
      ∧ star (matrixBlockCentralSupport d I) = matrixBlockCentralSupport d I
      ∧ ∀ a, matrixBlockCentralSupport d I * a =
          a * matrixBlockCentralSupport d I := by
  classical
  constructor
  · funext b
    change matrixBlockCentralSupport d I b * matrixBlockCentralSupport d I b =
      matrixBlockCentralSupport d I b
    by_cases hb : b ∈ matrixBlockIdealSupport d I
    · rw [matrixBlockCentralSupport_apply_of_mem d I hb]
      simp
    · rw [matrixBlockCentralSupport_apply_of_not_mem d I hb]
      simp
  constructor
  · funext b i j
    change (matrixBlockCentralSupport d I b)ᴴ i j =
      matrixBlockCentralSupport d I b i j
    by_cases hb : b ∈ matrixBlockIdealSupport d I
    · rw [matrixBlockCentralSupport_apply_of_mem d I hb]
      by_cases hij : i = j
      · subst j
        simp [Matrix.conjTranspose_apply, Matrix.one_apply]
      · simp [Matrix.conjTranspose_apply, Matrix.one_apply, hij, Ne.symm hij]
    · rw [matrixBlockCentralSupport_apply_of_not_mem d I hb]
      simp [Matrix.conjTranspose_apply]
  · intro a
    funext b
    change matrixBlockCentralSupport d I b * a b =
      a b * matrixBlockCentralSupport d I b
    by_cases hb : b ∈ matrixBlockIdealSupport d I
    · rw [matrixBlockCentralSupport_apply_of_mem d I hb]
      simp
    · rw [matrixBlockCentralSupport_apply_of_not_mem d I hb]
      simp

/-- Membership in a two-sided ideal of a finite matrix-block algebra is
equivalent to belonging to the range of its canonical central support. -/
theorem matrixBlockIdeal_eq_centralSupport_range
    (I : Ideal (FiniteMatrixBlockAlgebra d)) [I.IsTwoSided] (x) :
    x ∈ I ↔ ∃ a, x = matrixBlockCentralSupport d I * a := by
  classical
  let z := matrixBlockCentralSupport d I
  have hzI : z ∈ I := matrixBlockCentralSupport_mem d I
  constructor
  · intro hxI
    refine ⟨x, ?_⟩
    funext b
    change x b = z b * x b
    by_cases hb : b ∈ matrixBlockIdealSupport d I
    · rw [show z b = 1 from matrixBlockCentralSupport_apply_of_mem d I hb]
      simp
    · have hxb : x b = 0 := by
        by_contra hne
        exact hb ⟨x, hxI, hne⟩
      rw [show z b = 0 from matrixBlockCentralSupport_apply_of_not_mem d I hb]
      simp [hxb]
  · rintro ⟨a, rfl⟩
    exact Ideal.mul_mem_right a I hzI

/-- Every two-sided ideal in a finite product of full matrix algebras has the
unique central support projection asserted by the canonical source-ideal
decomposition theorem. -/
theorem finiteMatrixBlock_centralIdeal_decomposition
    (I : Ideal (FiniteMatrixBlockAlgebra d)) [I.IsTwoSided] :
    ∃! z : FiniteMatrixBlockAlgebra d,
      z * z = z ∧ star z = z ∧ (∀ a, z * a = a * z)
      ∧ (∀ x, x ∈ I ↔ ∃ a, x = z * a)
      ∧ (∀ a, a = z * a + (1 - z) * a) := by
  classical
  let z := matrixBlockCentralSupport d I
  rcases matrixBlockCentralSupport_isCentralProjection d I with ⟨hz, hstar, hcen⟩
  refine ⟨z, ⟨hz, hstar, hcen, matrixBlockIdeal_eq_centralSupport_range d I,
    fun a => (central_source_decomposition z hz hcen).1 a⟩, ?_⟩
  intro z' hz'
  rcases hz' with ⟨hz'id, -, hz'cen, hz'range, -⟩
  symm
  apply (central_source_decomposition z hz hcen).2.2 z' hz'id hz'cen
  · intro a
    have hza : z * a ∈ I :=
      (matrixBlockIdeal_eq_centralSupport_range d I (z * a)).2 ⟨a, rfl⟩
    rcases (hz'range (z * a)).1 hza with ⟨b, hb⟩
    exact ⟨b, hb⟩
  · intro a
    have hz'a : z' * a ∈ I := (hz'range (z' * a)).2 ⟨a, rfl⟩
    rcases (matrixBlockIdeal_eq_centralSupport_range d I (z' * a)).1 hz'a with ⟨b, hb⟩
    exact ⟨b, hb⟩

end MatrixBlocks

end NCG
