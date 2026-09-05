/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BoundarySpectralShift

/-!
# Zero lines of a finite spectral determinant

This file proves `thm:eigenvalue-zero-lines` for an arbitrary complex square
matrix.  The eigenvalues are the roots of the characteristic polynomial,
counted with algebraic multiplicity.  No normality or diagonalizability
hypothesis is used.
-/

open Matrix

namespace NCG

/-- The finite spectral determinant `D_A(s) = det(I - exp(-ell s) A)`. -/
noncomputable def finiteSpectralDeterminant {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (ell : ℝ) (s : ℂ) : ℂ :=
  Matrix.det (1 - Complex.exp (-(ell : ℂ) * s) • A)

/-- The zero associated with a nonzero eigenvalue `mu` and logarithmic branch
`k`.  Its real and imaginary parts are computed below in the exact form used
in the manuscript. -/
noncomputable def eigenvalueZero (ell : ℝ) (mu : ℂ) (k : ℤ) : ℂ :=
  (Complex.log mu - (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) / ell

theorem eigenvalueZero_re (ell : ℝ) (hell : ell ≠ 0) (mu : ℂ) (k : ℤ) :
    (eigenvalueZero ell mu k).re = Real.log ‖mu‖ / ell := by
  simp [eigenvalueZero, Complex.div_re, Complex.log_re]
  field_simp

theorem eigenvalueZero_im (ell : ℝ) (hell : ell ≠ 0) (mu : ℂ) (k : ℤ) :
    (eigenvalueZero ell mu k).im =
      (mu.arg - 2 * Real.pi * (k : ℝ)) / ell := by
  simp [eigenvalueZero, Complex.div_im, Complex.log_im, hell]
  field_simp

/-- A scalar spectral determinant vanishes exactly at a logarithmic branch of
the resonating nonzero eigenvalue. -/
theorem exponential_resonance_iff_eigenvalueZero
    (ell : ℝ) (hell : ell ≠ 0) (mu s : ℂ) (hmu : mu ≠ 0) :
    Complex.exp (-(ell : ℂ) * s) * mu = 1 ↔
      ∃ k : ℤ, s = eigenvalueZero ell mu k := by
  have hellC : (ell : ℂ) ≠ 0 := by exact_mod_cast hell
  constructor
  · intro h
    have hexp : Complex.exp (-(ell : ℂ) * s) =
        Complex.exp (-Complex.log mu) := by
      rw [Complex.exp_neg, Complex.exp_log hmu]
      apply (mul_right_cancel₀ hmu)
      rw [h, inv_mul_cancel₀ hmu]
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    refine ⟨k, ?_⟩
    unfold eigenvalueZero
    apply (eq_div_iff hellC).2
    linear_combination -hk
  · rintro ⟨k, rfl⟩
    unfold eigenvalueZero
    have hcancel : (-(ell : ℂ)) *
        ((Complex.log mu - (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) /
          (ell : ℂ)) =
        -Complex.log mu + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      field_simp
      ring
    rw [hcancel, Complex.exp_add, Complex.exp_neg, Complex.exp_log hmu,
      Complex.exp_int_mul_two_pi_mul_I]
    simpa using inv_mul_cancel₀ hmu

/-- Determinant singularity is equivalent to resonance with a root of the
characteristic polynomial.  Thus this is the diagonal-to-general-matrix step
that was previously missing from the spectral-determinant development. -/
theorem finiteSpectralDeterminant_zero_iff_resonance {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (ell : ℝ) (s : ℂ) :
    finiteSpectralDeterminant A ell s = 0 ↔
      ∃ mu ∈ A.charpoly.roots,
        Complex.exp (-(ell : ℂ) * s) * mu = 1 := by
  let c : ℂ := Complex.exp (-(ell : ℂ) * s)
  have hc : c ≠ 0 := Complex.exp_ne_zero _
  have hmatrix : (1 : Matrix (Fin n) (Fin n) ℂ) - c • A =
      c • (Matrix.scalar (Fin n) c⁻¹ - A) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.scalar_apply]
      field_simp
    · simp [Matrix.scalar_apply, Matrix.one_apply, hij]
  change Matrix.det ((1 : Matrix (Fin n) (Fin n) ℂ) - c • A) = 0 ↔ _
  rw [hmatrix, Matrix.det_smul, mul_eq_zero]
  simp only [pow_ne_zero _ hc, false_or]
  rw [← Matrix.eval_charpoly]
  constructor
  · intro hz
    have hroot : c⁻¹ ∈ A.charpoly.roots :=
      (Polynomial.mem_roots A.charpoly_monic.ne_zero).2 hz
    refine ⟨c⁻¹, hroot, ?_⟩
    change c * c⁻¹ = 1
    exact mul_inv_cancel₀ hc
  · rintro ⟨mu, hmu, hres⟩
    change c * mu = 1 at hres
    have hmueq : mu = c⁻¹ := by
      apply (mul_left_cancel₀ hc)
      rw [hres, mul_inv_cancel₀ hc]
    rw [← hmueq]
    exact (Polynomial.mem_roots A.charpoly_monic.ne_zero).1 hmu

/-- **Eigenvalue modulus--vertical-line theorem.**  The complete zero set of
`D_A` is indexed by the nonzero characteristic roots and the integer branches
of the logarithm. -/
theorem finiteSpectralDeterminant_zero_iff_eigenvalueZero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (ell : ℝ) (hell : 0 < ell) (s : ℂ) :
    finiteSpectralDeterminant A ell s = 0 ↔
      ∃ mu ∈ A.charpoly.roots, mu ≠ 0 ∧
        ∃ k : ℤ, s = eigenvalueZero ell mu k := by
  rw [finiteSpectralDeterminant_zero_iff_resonance]
  constructor
  · rintro ⟨mu, hroot, hres⟩
    have hmu : mu ≠ 0 := by
      intro h
      simp [h] at hres
    exact ⟨mu, hroot, hmu,
      (exponential_resonance_iff_eigenvalueZero ell hell.ne' mu s hmu).1 hres⟩
  · rintro ⟨mu, hroot, hmu, hk⟩
    exact ⟨mu, hroot,
      (exponential_resonance_iff_eigenvalueZero ell hell.ne' mu s hmu).2 hk⟩

/-- Consequently every determinant zero has real part
`log ‖mu‖ / ell` for a nonzero eigenvalue `mu`. -/
theorem finiteSpectralDeterminant_zero_realPart {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (ell : ℝ) (hell : 0 < ell) (s : ℂ)
    (hs : finiteSpectralDeterminant A ell s = 0) :
    ∃ mu ∈ A.charpoly.roots, mu ≠ 0 ∧
      s.re = Real.log ‖mu‖ / ell := by
  obtain ⟨mu, hroot, hmu, k, rfl⟩ :=
    (finiteSpectralDeterminant_zero_iff_eigenvalueZero A ell hell _).1 hs
  exact ⟨mu, hroot, hmu, eigenvalueZero_re ell hell.ne' mu k⟩

end NCG
