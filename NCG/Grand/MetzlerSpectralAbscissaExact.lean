/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MetzlerPerronExponentExact
import NCG.Grand.NonnegativeMatrixComplexEigenvalueBoundExact

/-!
# The canonical Metzler Perron exponent is the complex spectral abscissa

The positive Perron eigenpair and a weighted complex eigenvalue bound show
that the canonical exponent is an attained maximum of the real parts of the
actual complex spectrum. This identifies the manuscript's spectral bound
without defining it to be the Perron exponent.
-/

namespace NCG.MetzlerSpectralAbscissa

open _root_.Matrix MetzlerExponentialPositivity MetzlerPerronExponent
open NonnegativeMatrixComplexEigenvalueBound

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The real-part supremum of the actual spectrum of the complexified matrix. -/
def spectralAbscissa (A : Matrix S S ℝ) : ℝ :=
  sSup (Complex.re '' spectrum ℂ (A.map Complex.ofReal))

/-- The diagonal shift acts on a complex vector by adding the scalar shift. -/
theorem complex_diagonalShift_mulVec (A : Matrix S S ℝ) (c : ℝ) (z : S → ℂ) :
    ((diagonalShift A c).map Complex.ofReal).mulVec z =
      (A.map Complex.ofReal).mulVec z + (c : ℂ) • z := by
  have hmap : (diagonalShift A c).map Complex.ofReal =
      A.map Complex.ofReal + (c : ℂ) • (1 : Matrix S S ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [diagonalShift, Matrix.one_apply, hij]
  rw [hmap, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- Every complex eigenvalue lies to the left of the canonical Perron exponent. -/
theorem re_eigenvalue_le_exponent [Nonempty S]
    (A : Matrix S S ℝ) (hA : IsIrreducibleMetzler A)
    (lam : ℂ) (z : S → ℂ) (hz : z ≠ 0)
    (heig : (A.map Complex.ofReal).mulVec z = lam • z) :
    lam.re ≤ exponent A := by
  obtain ⟨_, ell, _, hell, _, hleft, _⟩ :=
    exists_normalized_positive_left_right_eigenvectors A hA
  let c := canonicalDiagonalShift A
  let B := diagonalShift A c
  have hB : ∀ i j, 0 ≤ B i j := hA.nonneg
  have hleftB : B.vecMul ell = (exponent A + c) • ell := by
    simp only [B, diagonalShift, Matrix.vecMul_add, Matrix.vecMul_smul,
      Matrix.vecMul_one, hleft, add_smul]
  have heigB : (B.map Complex.ofReal).mulVec z = (lam + (c : ℂ)) • z := by
    change ((diagonalShift A c).map Complex.ofReal).mulVec z = _
    rw [complex_diagonalShift_mulVec, heig, add_smul]
  have hb := norm_eigenvalue_le B hB ell hell (exponent A + c)
    hleftB (lam + (c : ℂ)) z hz heigB
  have hre := Complex.re_le_norm (lam + (c : ℂ))
  simp only [Complex.add_re, Complex.ofReal_re] at hre
  linarith

/-- Every member of the actual complex spectrum satisfies the spectral bound. -/
theorem re_le_exponent_of_mem_spectrum [Nonempty S]
    (A : Matrix S S ℝ) (hA : IsIrreducibleMetzler A)
    (lam : ℂ) (hlam : lam ∈ spectrum ℂ (A.map Complex.ofReal)) :
    lam.re ≤ exponent A := by
  have hlin : lam ∈ spectrum ℂ (A.map Complex.ofReal).toLin' := by
    simpa only [Matrix.spectrum_toLin'] using hlam
  obtain ⟨z, hz⟩ :=
    (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hlin).exists_hasEigenvector
  exact re_eigenvalue_le_exponent A hA lam z hz.2
    (by simpa only [Matrix.toLin'_apply] using hz.apply_eq_smul)

/-- The canonical real Perron exponent itself belongs to the complex spectrum. -/
theorem exponent_mem_spectrum [Nonempty S]
    (A : Matrix S S ℝ) (hA : IsIrreducibleMetzler A) :
    (exponent A : ℂ) ∈ spectrum ℂ (A.map Complex.ofReal) := by
  obtain ⟨r, hr, heig⟩ := exists_positive_eigenvector A hA
  let z : S → ℂ := fun i => (r i : ℂ)
  have hz : z ≠ 0 := by
    intro hzero
    obtain ⟨i⟩ := ‹Nonempty S›
    have hi := congrFun hzero i
    exact (ne_of_gt (hr i)) (Complex.ofReal_eq_zero.mp hi)
  have hcomplex : (A.map Complex.ofReal).mulVec z = (exponent A : ℂ) • z := by
    ext i
    have hi := congrArg Complex.ofReal (congrFun heig i)
    simpa [Matrix.mulVec, dotProduct, z] using hi
  have hvec : Module.End.HasEigenvector (A.map Complex.ofReal).toLin'
      (exponent A : ℂ) z :=
    ⟨Module.End.mem_eigenspace_iff.mpr (by
      simpa only [Matrix.toLin'_apply] using hcomplex), hz⟩
  have hmem := (Module.End.hasEigenvalue_of_hasEigenvector hvec).mem_spectrum
  simpa only [Matrix.spectrum_toLin'] using hmem

/-- The Perron exponent is an attained maximum of real parts of the complex spectrum. -/
theorem isGreatest_re_spectrum [Nonempty S]
    (A : Matrix S S ℝ) (hA : IsIrreducibleMetzler A) :
    IsGreatest (Complex.re '' spectrum ℂ (A.map Complex.ofReal)) (exponent A) := by
  refine ⟨⟨(exponent A : ℂ), exponent_mem_spectrum A hA, rfl⟩, ?_⟩
  rintro _ ⟨lam, hlam, rfl⟩
  exact re_le_exponent_of_mem_spectrum A hA lam hlam

/-- Identification with the independently defined spectral abscissa. -/
theorem spectralAbscissa_eq_exponent [Nonempty S]
    (A : Matrix S S ℝ) (hA : IsIrreducibleMetzler A) :
    spectralAbscissa A = exponent A :=
  (isGreatest_re_spectrum A hA).csSup_eq

end

end NCG.MetzlerSpectralAbscissa
