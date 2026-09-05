/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCommutantPoincareGap
import NCG.Grand.GTMonoidalTransport
import NCG.Grand.SMSTRelativeWriter

/-!
# Exact relative-writer orthogonal selection

This file supplies the missing SMW.8 three-way orthogonal writer split and combines it with the
already proved holonomy pricing/kernel identity and the word-level monoidal residual gate.
-/

open Matrix Finset
open scoped ComplexOrder

namespace NCG

/-- Flat relative-holonomy intertwiners: `P γ B = B T γ` for every measured cycle. -/
def relativeHolonomyFlatSubspace {G n m : Type} [Fintype G] [Fintype n] [Fintype m]
    (P : G → Matrix n n ℂ) (T : G → Matrix m m ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (n × m)) where
  carrier := {B | ∀ g, P g * l2Matrix B = l2Matrix B * T g}
  zero_mem' := by
    intro g
    change P g * (0 : Matrix n m ℂ) = (0 : Matrix n m ℂ) * T g
    simp
  add_mem' := by
    intro B C hB hC g
    rw [l2Matrix_add, Matrix.mul_add, Matrix.add_mul, hB g, hC g]
  smul_mem' := by
    intro c B hB g
    rw [l2Matrix_smul, Matrix.mul_smul, Matrix.smul_mul, hB g]

/-- The flat residual writer space is the intersection of the Read kernel with the relative
holonomy-intertwiner space. -/
def flatResidualWriterSubspace {G n m F : Type} [Fintype G] [Fintype n] [Fintype m]
    [AddCommMonoid F] [Module ℂ F]
    (P : G → Matrix n n ℂ) (T : G → Matrix m m ℂ)
    (R : EuclideanSpace ℂ (n × m) →ₗ[ℂ] F) :
    Submodule ℂ (EuclideanSpace ℂ (n × m)) :=
  R.ker ⊓ relativeHolonomyFlatSubspace P T
/-- Positive weighted squared relative-holonomy defect. -/
def relativeHolonomyAction {G n m : Type} [Fintype G] [Fintype n] [Fintype m]
    (P : G → Matrix n n ℂ) (T : G → Matrix m m ℂ)
    (a : G → ℝ) (B : Matrix n m ℂ) : ℝ :=
  ∑ g, a g * ∑ i, ∑ j, Complex.normSq ((P g * B - B * T g) i j)

/-- **SMW.8.** Every finite writer is the sum of a Read-forced adjoint-range vector, a
Read-invisible but holonomy-nonflat vector, and a flat residual intertwiner.  The three terms are
pairwise orthogonal. -/
theorem relativeWriter_threeWay_orthogonal_split
    {G n m F : Type} [Fintype G] [Fintype n] [Fintype m]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (P : G → Matrix n n ℂ) (T : G → Matrix m m ℂ)
    (R : EuclideanSpace ℂ (n × m) →ₗ[ℂ] F)
    (B : EuclideanSpace ℂ (n × m)) :
    ∃ BRead Bnonflat Bflat : EuclideanSpace ℂ (n × m),
      BRead ∈ R.adjoint.range
      ∧ Bnonflat ∈ R.ker ⊓ (flatResidualWriterSubspace P T R)ᗮ
      ∧ Bflat ∈ flatResidualWriterSubspace P T R
      ∧ B = BRead + Bnonflat + Bflat
      ∧ inner ℂ BRead Bnonflat = 0
      ∧ inner ℂ BRead Bflat = 0
      ∧ inner ℂ Bnonflat Bflat = 0 := by
  let K : Submodule ℂ (EuclideanSpace ℂ (n × m)) := R.ker
  let Q : Submodule ℂ (EuclideanSpace ℂ (n × m)) := flatResidualWriterSubspace P T R
  obtain ⟨Bk, hBk, BRead, hBRead, hsplit⟩ := K.exists_add_mem_mem_orthogonal B
  obtain ⟨Bflat, hBflat, Bnonflat, hBnonflat, hksplit⟩ :=
    Q.exists_add_mem_mem_orthogonal Bk
  have hQK : Q ≤ K := by
    intro x hx
    exact hx.1
  have hnonflatK : Bnonflat ∈ K := by
    have heq : Bnonflat = Bk - Bflat := by
      rw [hksplit]
      abel
    rw [heq]
    exact K.sub_mem hBk (hQK hBflat)
  have hreadRange : BRead ∈ R.adjoint.range := by
    rw [← LinearMap.orthogonal_ker]
    exact hBRead
  refine ⟨BRead, Bnonflat, Bflat, hreadRange, ⟨hnonflatK, hBnonflat⟩,
    hBflat, ?_, ?_, ?_, ?_⟩
  · rw [hsplit, hksplit]
    abel
  · exact Submodule.inner_left_of_mem_orthogonal hnonflatK hBRead
  · exact Submodule.inner_left_of_mem_orthogonal (hQK hBflat) hBRead
  · exact Submodule.inner_left_of_mem_orthogonal hBflat hBnonflat

/-- **Relative action--unit holonomy and residual writer selection
(`thm:SMST-relative-writer-selection`).**  The exact three-way split, positive pricing with flat
kernel, and the actual word-residual Gram gate hold simultaneously. -/
theorem relativeActionUnitHolonomy_residualWriterSelection
    {G n m p q F : Type} [Fintype G] [Fintype n] [Fintype m]
    [Fintype p] [Fintype q]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (P : G → Matrix n n ℂ) (T : G → Matrix m m ℂ)
    (a : G → ℝ) (ha : ∀ g, 0 < a g)
    (R : EuclideanSpace ℂ (n × m) →ₗ[ℂ] F) (B : Matrix n m ℂ)
    (wordResidual : Matrix p q ℂ) :
    (∃ BRead Bnonflat Bflat : EuclideanSpace ℂ (n × m),
      BRead ∈ R.adjoint.range
      ∧ Bnonflat ∈ R.ker ⊓ (flatResidualWriterSubspace P T R)ᗮ
      ∧ Bflat ∈ flatResidualWriterSubspace P T R
      ∧ matrixL2 B = BRead + Bnonflat + Bflat
      ∧ inner ℂ BRead Bnonflat = 0
      ∧ inner ℂ BRead Bflat = 0
      ∧ inner ℂ Bnonflat Bflat = 0)
    ∧ (0 ≤ relativeHolonomyAction P T a B)
    ∧ (relativeHolonomyAction P T a B = 0 ↔ ∀ g, P g * B = B * T g)
    ∧ (wordResidualᴴ * wordResidual).PosSemidef
    ∧ (wordResidualᴴ * wordResidual = 0 ↔ wordResidual = 0) := by
  refine ⟨relativeWriter_threeWay_orthogonal_split P T R (matrixL2 B), ?_⟩
  obtain ⟨hpos, hzero⟩ := smst_relative_writer_selection P T a ha B
  obtain ⟨hpsd, hres⟩ := gt_monoidal_innovation wordResidual
  exact ⟨by simpa [relativeHolonomyAction] using hpos,
    by simpa [relativeHolonomyAction] using hzero, hpsd, hres⟩

end NCG




