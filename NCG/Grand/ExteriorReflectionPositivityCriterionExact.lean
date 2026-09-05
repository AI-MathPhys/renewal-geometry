/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCompoundMatrixExteriorPower
import NCG.Grand.PsdCalculusExact

/-!
# Exact exterior reflection-positivity criterion

This is the finite wedge-basis realization of
`thm:SMQG-exterior-positivity`.  Positivity of fermionic second
quantization is encoded componentwise on every exterior grade.  The forward
implication is the compound-matrix square-root factorization; the converse is
not assumed: it is recovered from the literal grade-one principal block.

The final theorem also records the vacuum-safe scalar trichotomy.  The grade
zero block forces a real scalar weight to be nonnegative; if it is strictly
positive, the grade-one block recovers positivity of the one-particle
covariance.  Thus the only alternatives are zero weight or positive weight
and positive covariance.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace ExteriorReflectionPositivityCriterion

open FiniteCompoundMatrixExteriorPower

/-- The grade-one wedge basis vector corresponding to a one-particle basis
vector. -/
def singletonGrade {d : ℕ} (i : Fin d) : GradeIdx 1 d :=
  ⟨{i}, by simp⟩

/-- On the singleton wedge basis, the first compound matrix is literally the
original matrix. -/
theorem cmpd_one_submatrix {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) :
    (cmpd 1 P).submatrix singletonGrade singletonGrade = P := by
  ext i j
  rw [Matrix.submatrix_apply, cmpd_apply, Matrix.det_fin_one]
  simp [singletonGrade, sel]

/-- Componentwise positivity of the fermionic second quantization
`Γ_∧(P) = ⊕ᵣ ⋀^r P`. -/
def ExteriorPositive {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ r : ℕ, (cmpd r P).PosSemidef

/-- Exact exterior reflection-positivity criterion: all exterior grades are
positive if and only if the one-particle covariance is positive. -/
theorem exteriorPositive_iff {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) :
    ExteriorPositive P ↔ P.PosSemidef := by
  constructor
  · intro h
    have h1 := (h 1).submatrix singletonGrade
    simpa only [cmpd_one_submatrix] using h1
  · intro hP r
    exact cmpd_posSemidef hP

/-- Positivity of a real scalar multiple of the full exterior hierarchy.  The
vacuum grade `r = 0` is included. -/
def ScalarExteriorPositive {d : ℕ} (q : ℝ)
    (P : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ r : ℕ, (((q : ℂ) • cmpd r P)).PosSemidef

/-- The zeroth compound is the one-dimensional identity, independently of
the one-particle matrix. -/
theorem cmpd_zero {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) :
    cmpd 0 P = 1 := by
  ext S T
  have hS : S = T := by
    apply Subtype.ext
    rw [Finset.card_eq_zero.mp S.2, Finset.card_eq_zero.mp T.2]
  subst T
  rw [cmpd_apply, Matrix.one_apply, if_pos rfl]
  exact Matrix.det_isEmpty

/-- The vacuum matrix detects nonnegativity of its real scalar weight. -/
theorem scalar_nonneg_of_vacuum_posSemidef {d : ℕ}
    (P : Matrix (Fin d) (Fin d) ℂ) (q : ℝ)
    (h0 : (((q : ℂ) • cmpd 0 P)).PosSemidef) : 0 ≤ q := by
  rw [cmpd_zero] at h0
  let i : GradeIdx 0 d := ⟨∅, by simp⟩
  have hdiag := h0.2 (Finsupp.single i 1)
  simpa [dotProduct, Matrix.mulVec, i] using (Complex.le_def.mp hdiag).1

/-- **`thm:SMQG-exterior-positivity`, scalar clause.**  With the vacuum
word retained, a real scalar multiple of the complete exterior covariance is
positive exactly in the zero branch or in the strictly-positive scalar and
positive one-particle branch. -/
theorem scalarExteriorPositive_iff {d : ℕ} (q : ℝ)
    (P : Matrix (Fin d) (Fin d) ℂ) :
    ScalarExteriorPositive q P ↔ q = 0 ∨ (0 < q ∧ P.PosSemidef) := by
  constructor
  · intro h
    have hq : 0 ≤ q := scalar_nonneg_of_vacuum_posSemidef P q (h 0)
    rcases hq.eq_or_lt with hq0 | hqpos
    · exact Or.inl hq0.symm
    · refine Or.inr ⟨hqpos, ?_⟩
      have hscaled := (h 1).submatrix singletonGrade
      have hsub :
          (((q : ℂ) • cmpd 1 P).submatrix singletonGrade singletonGrade) =
            ((q : ℂ) • P) := by
        ext i j
        have hij := congrFun (congrFun (cmpd_one_submatrix P) i) j
        exact congrArg (fun z : ℂ => (q : ℂ) * z) hij
      have hscaled' : (((q : ℂ) • P)).PosSemidef := by
        rw [← hsub]
        exact hscaled
      have hinv : 0 ≤ q⁻¹ := inv_nonneg.mpr hqpos.le
      have hrescaled := QRE.posSemidef_smul_real hinv hscaled'
      simpa [smul_smul, hqpos.ne'] using hrescaled
  · rintro (rfl | ⟨hq, hP⟩) r
    · simpa using (Matrix.PosSemidef.zero :
        (0 : Matrix (GradeIdx r d) (GradeIdx r d) ℂ).PosSemidef)
    · exact QRE.posSemidef_smul_real hq.le (cmpd_posSemidef hP)

/-- Positivity of a complex scalar multiple of every exterior grade.  Since
positive-semidefinite complex matrices are Hermitian, the included vacuum
grade detects and excludes every nonreal scalar. -/
def ComplexScalarExteriorPositive {d : ℕ} (q : ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ r : ℕ, (q • cmpd r P).PosSemidef

/-- Full complex scalar trichotomy from the manuscript: the scalar is zero,
or it is a strictly positive real number and the one-particle covariance is
positive.  In particular a nonreal scalar fails already on the vacuum word,
and a negative real scalar has the vacuum as a negative witness. -/
theorem complexScalarExteriorPositive_iff {d : ℕ} (q : ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) :
    ComplexScalarExteriorPositive q P ↔
      q = 0 ∨ (0 < q.re ∧ q.im = 0 ∧ P.PosSemidef) := by
  constructor
  · intro h
    let i : GradeIdx 0 d := ⟨∅, by simp⟩
    have h0 := h 0
    rw [cmpd_zero] at h0
    have hdiag := h0.2 (Finsupp.single i 1)
    have hqorder : (0 : ℂ) ≤ q := by
      simpa [dotProduct, Matrix.mulVec, i] using hdiag
    have hqre : 0 ≤ q.re := (Complex.le_def.mp hqorder).1
    have hqim : q.im = 0 := (Complex.le_def.mp hqorder).2.symm
    rcases hqre.eq_or_lt with hz | hp
    · left
      apply Complex.ext
      · simpa using hz.symm
      · simpa [hqim]
    · right
      refine ⟨hp, hqim, ?_⟩
      have hq : q = (q.re : ℂ) := by
        apply Complex.ext <;> simp [hqim]
      have hreal : ScalarExteriorPositive q.re P := by
        intro r
        have hr := h r
        rw [hq] at hr
        exact hr
      exact ((scalarExteriorPositive_iff q.re P).mp hreal).resolve_left hp.ne' |>.2
  · rintro (rfl | ⟨hq, hqim, hP⟩) r
    · simpa using (Matrix.PosSemidef.zero :
        (0 : Matrix (GradeIdx r d) (GradeIdx r d) ℂ).PosSemidef)
    · have hqeq : q = (q.re : ℂ) := by
        apply Complex.ext <;> simp [hqim]
      rw [hqeq]
      exact QRE.posSemidef_smul_real hq.le (cmpd_posSemidef hP)

/-- Consolidated exact finite statement: reflection positivity of every
Grassmann grade, positivity of the second-quantized covariance, and positivity
of the one-particle covariance are equivalent, with the vacuum scalar
trichotomy. -/
theorem smqg_exterior_reflection_positivity {d : ℕ}
    (P : Matrix (Fin d) (Fin d) ℂ) (q : ℂ) :
    (ExteriorPositive P ↔ P.PosSemidef) ∧
      (ComplexScalarExteriorPositive q P ↔
        q = 0 ∨ (0 < q.re ∧ q.im = 0 ∧ P.PosSemidef)) :=
  ⟨exteriorPositive_iff P, complexScalarExteriorPositive_iff q P⟩

end ExteriorReflectionPositivityCriterion
end NCG
