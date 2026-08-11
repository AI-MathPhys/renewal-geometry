/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteSpectralDeterminantZeroLines
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Normal transfer gaps and zero-free half-planes

This is the general normal-matrix form of `thm:gap-zero-free`.  It combines
the arbitrary-matrix zero-line theorem with the C-star spectral-radius theorem
for normal matrices.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NCG

/-- Real parts of the zeros of the finite spectral determinant. -/
def spectralDeterminantZeroRealParts {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) : Set ℝ :=
  {x | ∃ s : ℂ, finiteSpectralDeterminant A tau s = 0 ∧ x = s.re}

set_option maxHeartbeats 800000 in
/-- For a nonzero normal matrix, `log ‖A‖ / tau` is not merely an upper
bound: it is attained by a determinant zero. -/
theorem normalFiniteSpectralDeterminant_zeroRealParts_isGreatest {n : ℕ}
    [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℂ) [IsStarNormal A]
    (tau : ℝ) (htau : 0 < tau) (hA : 0 < ‖A‖) :
    IsGreatest (spectralDeterminantZeroRealParts A tau)
      (Real.log ‖A‖ / tau) := by
  letI : CStarAlgebra (Matrix (Fin n) (Fin n) ℂ) := {}
  have hchar : A.charpoly ≠ 0 := A.charpoly_monic.ne_zero
  constructor
  · obtain ⟨mu, hmuspec, hmuRad⟩ :=
      spectrum.exists_nnnorm_eq_spectralRadius A
    have hrad := IsStarNormal.spectralRadius_eq_nnnorm A
    have hmuENN : (↑‖mu‖₊ : ENNReal) = (↑‖A‖₊ : ENNReal) :=
      hmuRad.trans hrad
    have hmunorm : ‖mu‖ = ‖A‖ := by
      exact congrArg (fun x : NNReal => (x : ℝ))
        (ENNReal.coe_injective hmuENN)
    have hmuRoot : mu ∈ A.charpoly.roots := by
      apply (Polynomial.mem_roots hchar).2
      exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hmuspec
    have hmu : mu ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hmunorm
      linarith
    let s := eigenvalueZero tau mu 0
    refine ⟨s, ?_, ?_⟩
    · apply (finiteSpectralDeterminant_zero_iff_eigenvalueZero
        A tau htau s).2
      exact ⟨mu, hmuRoot, hmu, 0, rfl⟩
    · rw [eigenvalueZero_re tau htau.ne' mu 0, hmunorm]
  · rintro x ⟨s, hs, rfl⟩
    obtain ⟨mu, hmuRoot, hmu, hre⟩ :=
      finiteSpectralDeterminant_zero_realPart A tau htau s hs
    rw [hre]
    have hmuspec : mu ∈ spectrum ℂ A :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
        ((Polynomial.mem_roots hchar).1 hmuRoot)
    have hnorm : ‖mu‖ ≤ ‖A‖ := spectrum.norm_le_norm_of_mem hmuspec
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (norm_pos_iff.mpr hmu) hnorm) htau.le

/-- Exact mass-gap statement: the spectral determinant is zero-free strictly
to the right of the line selected by the operator norm. -/
theorem normalFiniteSpectralDeterminant_zeroFree {n : ℕ}
    [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℂ) [IsStarNormal A]
    (tau : ℝ) (htau : 0 < tau) (hA : 0 < ‖A‖) :
    ∀ s : ℂ, Real.log ‖A‖ / tau < s.re →
      finiteSpectralDeterminant A tau s ≠ 0 := by
  intro s hs hzero
  have hle := (normalFiniteSpectralDeterminant_zeroRealParts_isGreatest
    A tau htau hA).2 ⟨s, hzero, rfl⟩
  linarith

/-- Converse zero-free criterion.  If the half-plane to the right of
`-Delta0` contains no zero, normality forces the claimed exponential norm
bound. -/
theorem normalFiniteSpectralDeterminant_zeroFree_converse {n : ℕ}
    [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℂ) [IsStarNormal A]
    (tau Delta0 : ℝ) (htau : 0 < tau)
    (hfree : ∀ s : ℂ, -Delta0 < s.re →
      finiteSpectralDeterminant A tau s ≠ 0) :
    ‖A‖ ≤ Real.exp (-tau * Delta0) := by
  by_contra hnot
  have hlt : Real.exp (-tau * Delta0) < ‖A‖ := lt_of_not_ge hnot
  have hA : 0 < ‖A‖ := (Real.exp_pos _).trans hlt
  obtain ⟨hmem, -⟩ :=
    normalFiniteSpectralDeterminant_zeroRealParts_isGreatest A tau htau hA
  obtain ⟨s, hs, hre⟩ := hmem
  have hline : -Delta0 < s.re := by
    rw [← hre]
    have hlog : -tau * Delta0 < Real.log ‖A‖ := by
      rw [← Real.log_exp (-tau * Delta0)]
      exact Real.strictMonoOn_log (Real.exp_pos _) hA hlt
    rw [lt_div_iff₀ htau]
    linarith
  exact hfree s hline hs

/-- The manuscript's notation `Delta = -tau⁻¹ log q`: the greatest zero real
part is exactly `-Delta`. -/
theorem normalFiniteSpectralDeterminant_massGap_duality {n : ℕ}
    [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℂ) [IsStarNormal A]
    (tau : ℝ) (htau : 0 < tau) (hA : 0 < ‖A‖)
    (Delta : ℝ) (hDelta : Delta = -(tau⁻¹ * Real.log ‖A‖)) :
    IsGreatest (spectralDeterminantZeroRealParts A tau) (-Delta) := by
  have hgreat :=
    normalFiniteSpectralDeterminant_zeroRealParts_isGreatest A tau htau hA
  convert hgreat using 1
  rw [hDelta]
  field_simp

end NCG
