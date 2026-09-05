/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MetzlerSpectralAbscissaExact
import NCG.Grand.PerronAlgebraicSimplicityExact

/-!
# The singleton-generator spectral branch

The standard one-state CTMC is irreducible even when its generator is zero.
It must not be excluded by a positive-length-loop irreducibility convention.
Direct scalar spectrum and characteristic-polynomial calculations provide
the exact analytic simple SCGF for this case.
-/

open Matrix Set
open scoped BigOperators Topology

namespace NCG.SingletonGeneratorSpectral

open DrivenProcess MetzlerSpectralAbscissa

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S] [Subsingleton S]

theorem univ_eq_singleton (x₀ : S) : (Finset.univ : Finset S) = {x₀} := by
  ext i
  simp [Subsingleton.elim i x₀]

/-- Every generator on a singleton carrier is identically zero. -/
theorem generator_eq_zero (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S) : L = 0 := by
  have hz := hL.row_sum x₀
  rw [univ_eq_singleton x₀, Finset.sum_singleton] at hz
  ext i j
  have hi : i = x₀ := Subsingleton.elim _ _
  have hj : j = x₀ := Subsingleton.elim _ _
  simpa [hi, hj] using hz

/-- A singleton matrix has precisely its only entry as its actual complex spectrum. -/
theorem complex_spectrum_eq_singleton (A : Matrix S S ℝ) (x₀ : S) :
    spectrum ℂ (A.map Complex.ofReal) = {(A x₀ x₀ : ℂ)} := by
  letI : Nonempty S := ⟨x₀⟩
  have hmap : A.map Complex.ofReal = algebraMap ℂ (Matrix S S ℂ) (A x₀ x₀ : ℂ) := by
    ext i j
    have hi : i = x₀ := Subsingleton.elim _ _
    have hj : j = x₀ := Subsingleton.elim _ _
    simp [hi, hj, Algebra.algebraMap_eq_smul_one, Matrix.one_apply]
  rw [hmap, spectrum.scalar_eq]

theorem spectralAbscissa_eq_entry (A : Matrix S S ℝ) (x₀ : S) :
    spectralAbscissa A = A x₀ x₀ := by
  unfold spectralAbscissa
  rw [complex_spectrum_eq_singleton A x₀]
  simp

/-- The tilted singleton pressure is exactly linear. -/
theorem spectralAbscissa_tilt_eq (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    spectralAbscissa (tilt L v g k) = k * v x₀ := by
  rw [spectralAbscissa_eq_entry _ x₀, tilt_apply_self, generator_eq_zero L hL x₀]
  simp

theorem analyticAt_spectralAbscissa_tilt (L : Matrix S S ℝ) (hL : IsGenerator L) (x₀ : S)
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) :
    AnalyticAt ℝ (fun q => spectralAbscissa (tilt L v g q)) k := by
  have hfun : (fun q => spectralAbscissa (tilt L v g q)) = (fun q => q * v x₀) :=
    funext fun q => spectralAbscissa_tilt_eq L hL x₀ v g q
  rw [hfun]
  exact analyticAt_id.mul analyticAt_const

/-- Singleton characteristic polynomial, over any commutative coefficient ring. -/
theorem charpoly_eq_X_sub_C {R : Type*} [CommRing R] (A : Matrix S S R) (x₀ : S) :
    A.charpoly = Polynomial.X - Polynomial.C (A x₀ x₀) := by
  have hA : A = Matrix.diagonal (fun _ : S => A x₀ x₀) := by
    ext i j
    have hi : i = x₀ := Subsingleton.elim _ _
    have hj : j = x₀ := Subsingleton.elim _ _
    simp [hi, hj]
  rw [hA, Matrix.charpoly_diagonal, univ_eq_singleton x₀, Finset.prod_singleton]
  simp

/-- The singleton spectral root is algebraically simple after complexification. -/
theorem complex_rootMultiplicity_spectralAbscissa_eq_one (A : Matrix S S ℝ) (x₀ : S) :
    (A.map Complex.ofReal).charpoly.rootMultiplicity (spectralAbscissa A : ℂ) = 1 := by
  rw [charpoly_eq_X_sub_C _ x₀, spectralAbscissa_eq_entry A x₀]
  exact Polynomial.rootMultiplicity_X_sub_C_self

end

end NCG.SingletonGeneratorSpectral
