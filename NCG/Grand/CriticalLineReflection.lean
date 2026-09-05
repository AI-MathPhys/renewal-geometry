/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.GrandSpectralDet

/-!
# Critical-line reflection of spectral-determinant zeros

This module supplies the zero-multiset reflection clause of
`thm:critical-line-circle`.  An equivalence of the finite eigenvalue index set
records multiplicity preservation under `lambda ↦ c / conj lambda`.
-/

open Matrix

namespace NCG

/-- Reflection in the vertical line `Re s = (log c / l) / 2`. -/
noncomputable def criticalReflection (l c : ℝ) (s : ℂ) : ℂ :=
  ((Real.log c / l : ℝ) : ℂ) - star s

@[simp]
theorem criticalReflection_involutive (l c : ℝ) (s : ℂ) :
    criticalReflection l c (criticalReflection l c s) = s := by
  simp [criticalReflection]

/-- Reciprocal-conjugate eigenvalues carry resonances to reflected
resonances, with the eigenvalue equivalence preserving multiplicity. -/
theorem reflectedEigenvalueResonance {n : Type*}
    (lam : n → ℂ) (σ : n ≃ n) (l c : ℝ) (hl : l ≠ 0) (hc : 0 < c)
    (hσ : ∀ j, lam (σ j) = (c : ℂ) / star (lam j))
    (j : n) (s : ℂ)
    (hres : Complex.exp (-(l : ℂ) * s) * lam j = 1) :
    Complex.exp (-(l : ℂ) * criticalReflection l c s) * lam (σ j) = 1 := by
  have hlam : lam j ≠ 0 := by
    intro h
    rw [h, mul_zero] at hres
    exact one_ne_zero hres.symm
  have hexp : Complex.exp (-(l : ℂ) * s) ≠ 0 := Complex.exp_ne_zero _
  have hlamExp : lam j = Complex.exp ((l : ℂ) * s) := by
    calc
      lam j = 1 / Complex.exp (-(l : ℂ) * s) := by
        apply (eq_div_iff hexp).2
        simpa [mul_comm] using hres
      _ = (Complex.exp (-(l : ℂ) * s))⁻¹ := one_div _
      _ = Complex.exp (-(-(l : ℂ) * s)) := (Complex.exp_neg _).symm
      _ = Complex.exp ((l : ℂ) * s) := by congr 2 <;> ring
  have hconjExp : star (lam j) =
      Complex.exp ((l : ℂ) * star s) := by
    rw [hlamExp]
    simpa using (Complex.exp_conj ((l : ℂ) * s)).symm
  have haexp : Complex.exp
      (-(l : ℂ) * ((Real.log c / l : ℝ) : ℂ)) = (c : ℂ)⁻¹ := by
    have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast hl
    rw [show -(l : ℂ) * ((Real.log c / l : ℝ) : ℂ) =
        -(Real.log c : ℂ) by
      push_cast
      field_simp]
    rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hc]
  rw [hσ]
  have hsplit : -(l : ℂ) * criticalReflection l c s =
      (-(l : ℂ) * ((Real.log c / l : ℝ) : ℂ)) +
        (l : ℂ) * star s := by
    simp [criticalReflection]
    ring
  rw [hsplit, Complex.exp_add, haexp, ← hconjExp]
  have hconj : star (lam j) ≠ 0 := by
    intro hs
    apply hlam
    have := congrArg star hs
    simpa using this
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  field_simp [hcC, hconj]

/-- The determinant zero set is invariant under the critical reflection.  The
finite equivalence `σ` is the with-multiplicity pairing of eigenvalues. -/
theorem criticalLineZeroReflection {n : Type*} [Fintype n] [DecidableEq n]
    (lam : n → ℂ) (σ : n ≃ n) (l c : ℝ) (hl : l ≠ 0) (hc : 0 < c)
    (hσ : ∀ j, lam (σ j) = (c : ℂ) / star (lam j)) (s : ℂ) :
    Matrix.det (1 - Complex.exp (-(l : ℂ) * s) • Matrix.diagonal lam) = 0
      ↔ Matrix.det (1 - Complex.exp
          (-(l : ℂ) * criticalReflection l c s) • Matrix.diagonal lam) = 0 := by
  constructor
  · intro hs
    obtain ⟨j, hj⟩ := (det_zero_iff lam _).mp hs
    exact (det_zero_iff lam _).mpr
      ⟨σ j, reflectedEigenvalueResonance lam σ l c hl hc hσ j s hj⟩
  · intro hrs
    obtain ⟨j, hj⟩ := (det_zero_iff lam _).mp hrs
    have href := reflectedEigenvalueResonance lam σ l c hl hc hσ j
      (criticalReflection l c s) hj
    rw [criticalReflection_involutive] at href
    exact (det_zero_iff lam _).mpr ⟨σ j, href⟩

end NCG
