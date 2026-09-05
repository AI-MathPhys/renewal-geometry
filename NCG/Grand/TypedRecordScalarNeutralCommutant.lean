/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TypedRecordCommutantCoordinates

/-!
# Commutant of the corrected typed record algebra

The corrected typed record algebra has six one-dimensional atoms and one
scalar algebra acting with multiplicity two on the neutral doublet.  This
module computes its commutant directly: an operator commutes with every record
exactly when it is diagonal on the six simple atoms and arbitrary on the
neutral two-dimensional multiplicity space.

This is the concrete algebraic clause required by
`thm:SM-typed-occurrence-RN` after replacing the former full neutral `M₂(ℂ)`
summand by a scalar summand of multiplicity two.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace TypedRecordScalarNeutralCommutant

/-- The corrected typed record action: six independent scalar atoms and one
scalar acting identically on the neutral doublet. -/
def scalarNeutralRecord (a : Fin 6 → ℂ) (z : ℂ) :
    Matrix (Fin 6 ⊕ Fin 2) (Fin 6 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks (Matrix.diagonal a) 0 0 (z • 1)

/-- Every operator in the commutant of the corrected record algebra has six
scalar coordinates and one unrestricted neutral `2 × 2` block. -/
theorem commutant_has_scalarNeutralBlockForm
    (K : Matrix (Fin 6 ⊕ Fin 2) (Fin 6 ⊕ Fin 2) ℂ)
    (hcomm : ∀ (a : Fin 6 → ℂ) (z : ℂ),
      scalarNeutralRecord a z * K = K * scalarNeutralRecord a z) :
    ∃ (k : Fin 6 → ℂ) (N : Matrix (Fin 2) (Fin 2) ℂ),
      K = Matrix.fromBlocks (Matrix.diagonal k) 0 0 N := by
  obtain ⟨A, B, C, D, rfl⟩ :
      ∃ A B C D, K = Matrix.fromBlocks A B C D :=
    ⟨K.toBlocks₁₁, K.toBlocks₁₂, K.toBlocks₂₁, K.toBlocks₂₂,
      (Matrix.fromBlocks_toBlocks K).symm⟩
  have hP := hcomm 0 1
  simp only [scalarNeutralRecord, one_smul] at hP
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hP
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul,
    Matrix.mul_one, add_zero, zero_add] at hP
  have hB : B = 0 := by
    have h12 := congrArg Matrix.toBlocks₁₂ hP
    simpa using h12.symm
  have hC : C = 0 := by
    have h21 := congrArg Matrix.toBlocks₂₁ hP
    simpa using h21
  subst B
  subst C
  have hA : ∀ a : Fin 6 → ℂ,
      Matrix.diagonal a * A = A * Matrix.diagonal a := by
    intro a
    have h := hcomm a 0
    rw [scalarNeutralRecord, zero_smul,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h
    have h11 := congrArg Matrix.toBlocks₁₁ h
    simpa using h11
  let k : Fin 6 → ℂ := fun i => A i i
  have hAdiag : A = Matrix.diagonal k := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [k]
    · have hentry := congrFun (congrFun
        (hA (Pi.single i (1 : ℂ) : Fin 6 → ℂ)) i) j
      simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
      have hii : (Pi.single i (1 : ℂ) : Fin 6 → ℂ) i = 1 := by simp
      have hij0 : (Pi.single i (1 : ℂ) : Fin 6 → ℂ) j = 0 := by
        simp [hij]
      rw [hii, hij0, one_mul, mul_zero] at hentry
      simpa [Matrix.diagonal_apply_ne _ hij] using hentry
  exact ⟨k, D, by rw [hAdiag]⟩

/-- Conversely, every six-scalar-plus-neutral-block operator commutes with the
corrected record algebra. -/
theorem scalarNeutralBlockForm_mem_commutant
    (k : Fin 6 → ℂ) (N : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ (a : Fin 6 → ℂ) (z : ℂ),
      scalarNeutralRecord a z *
          Matrix.fromBlocks (Matrix.diagonal k) 0 0 N =
        Matrix.fromBlocks (Matrix.diagonal k) 0 0 N *
          scalarNeutralRecord a z := by
  intro a z
  rw [scalarNeutralRecord, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  congr 1
  · ext i j
    simp [mul_comm]
  · simp
  · simp
  · ext i j
    simp [Matrix.smul_apply]

/-- Exact iff-form of the corrected typed-record commutant calculation. -/
theorem mem_commutant_iff_scalarNeutralBlockForm
    (K : Matrix (Fin 6 ⊕ Fin 2) (Fin 6 ⊕ Fin 2) ℂ) :
    (∀ (a : Fin 6 → ℂ) (z : ℂ),
      scalarNeutralRecord a z * K = K * scalarNeutralRecord a z) ↔
      ∃ (k : Fin 6 → ℂ) (N : Matrix (Fin 2) (Fin 2) ℂ),
        K = Matrix.fromBlocks (Matrix.diagonal k) 0 0 N := by
  constructor
  · exact commutant_has_scalarNeutralBlockForm K
  · rintro ⟨k, N, rfl⟩
    exact scalarNeutralBlockForm_mem_commutant k N

private theorem star_sum_elim {a b : Type*} (x : a → ℂ) (y : b → ℂ) :
    star (Sum.elim x y) = Sum.elim (star x) (star y) := by
  funext i
  cases i <;> rfl

private theorem posSemidef_leftPrincipal
    {a b : Type*} [Finite a] [Finite b]
    {A : Matrix a a ℂ} {B : Matrix a b ℂ}
    {C : Matrix b a ℂ} {D : Matrix b b ℂ}
    (h : (Matrix.fromBlocks A B C D).PosSemidef) : A.PosSemidef := by
  letI := Fintype.ofFinite a
  letI := Fintype.ofFinite b
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · change Aᴴ = A
    have hh := congrArg Matrix.toBlocks₁₁ h.1
    simpa [Matrix.fromBlocks_conjTranspose] using hh
  · intro x
    have hq := h.dotProduct_mulVec_nonneg (Sum.elim x 0)
    rw [Matrix.fromBlocks_mulVec, star_sum_elim,
      sumElim_dotProduct_sumElim] at hq
    simpa using hq

private theorem posSemidef_rightPrincipal
    {a b : Type*} [Finite a] [Finite b]
    {A : Matrix a a ℂ} {B : Matrix a b ℂ}
    {C : Matrix b a ℂ} {D : Matrix b b ℂ}
    (h : (Matrix.fromBlocks A B C D).PosSemidef) : D.PosSemidef := by
  letI := Fintype.ofFinite a
  letI := Fintype.ofFinite b
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · change Dᴴ = D
    have hh := congrArg Matrix.toBlocks₂₂ h.1
    simpa [Matrix.fromBlocks_conjTranspose] using hh
  · intro y
    have hq := h.dotProduct_mulVec_nonneg (Sum.elim 0 y)
    rw [Matrix.fromBlocks_mulVec, star_sum_elim,
      sumElim_dotProduct_sumElim] at hq
    simpa using hq

/-- A nondemolition effect has six scalar effects and one genuine neutral
`2 × 2` effect, including positivity of both blocks and their complements. -/
theorem commutingEffect_has_scalarNeutralEffectForm
    (K : Matrix (Fin 6 ⊕ Fin 2) (Fin 6 ⊕ Fin 2) ℂ)
    (hK : K.PosSemidef)
    (hcomp : ((1 : Matrix (Fin 6 ⊕ Fin 2) (Fin 6 ⊕ Fin 2) ℂ) - K).PosSemidef)
    (hcomm : ∀ (a : Fin 6 → ℂ) (z : ℂ),
      scalarNeutralRecord a z * K = K * scalarNeutralRecord a z) :
    ∃ (k : Fin 6 → ℂ) (N : Matrix (Fin 2) (Fin 2) ℂ),
      K = Matrix.fromBlocks (Matrix.diagonal k) 0 0 N ∧
      (Matrix.diagonal k).PosSemidef ∧
      ((1 : Matrix (Fin 6) (Fin 6) ℂ) - Matrix.diagonal k).PosSemidef ∧
      N.PosSemidef ∧ ((1 : Matrix (Fin 2) (Fin 2) ℂ) - N).PosSemidef := by
  obtain ⟨k, N, rfl⟩ := commutant_has_scalarNeutralBlockForm K hcomm
  have hleft := posSemidef_leftPrincipal hK
  have hright := posSemidef_rightPrincipal hK
  have hcompeq :
      (1 : Matrix (Fin 6 ⊕ Fin 2) (Fin 6 ⊕ Fin 2) ℂ) -
          Matrix.fromBlocks (Matrix.diagonal k) 0 0 N =
        Matrix.fromBlocks (1 - Matrix.diagonal k) 0 0 (1 - N) := by
    rw [← Matrix.fromBlocks_one]
    rw [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
    congr 1 <;> simp
  rw [hcompeq] at hcomp
  exact ⟨k, N, rfl, hleft, posSemidef_leftPrincipal hcomp,
    hright, posSemidef_rightPrincipal hcomp⟩

/-- The corrected commutant has the manuscript's ten real effect
coordinates: six real scalar coordinates and four Hermitian neutral-block
coordinates. -/
theorem correctedTypedRecordEffectCoordinates_finrank :
    Module.finrank ℝ TypedRecordEffectCoordinates = 10 :=
  typedRecordEffectCoordinates_finrank

/-- Fixing one nonzero real conductance removes exactly one coordinate. -/
theorem correctedTypedRecordConductanceKernel_finrank
    (g : Fin 10 → ℝ) (hg : g ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (typedConductanceFunctional g)) = 9 :=
  typedConductanceKernel_finrank_nine g hg

end TypedRecordScalarNeutralCommutant
end NCG
