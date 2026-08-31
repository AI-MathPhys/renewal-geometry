/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TrineMeasureAcquisitionExact
import NCG.Grand.LockedPrivateProvenanceCompiler
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Analysis.Matrix.Normed

/-!
# Positive matrix-valued carrier for trine acquisition

This supplies the literal `2 × 2` matrix layer of
`thm:GT-trine-complex-measure`.  The manuscript's scalar completion predicate
is proved equivalent to Mathlib's genuine matrix `PosSemidef` predicate.  The
balanced density therefore integrates to an honest matrix-valued vector
measure, and the general imbalance parameter has exactly the determinant
constraint stated in (TRI.1).
-/

open Matrix Set Filter
open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.Elementwise MeasureTheory

namespace NCG
namespace TrineMatrixCarrier

open MeasureTheory
open TrineComplexAcquisitionAndTransport
open LockedPrivateProvenanceCompiler

abbrev TrineMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- Hermitian completion with trace `t`, complex coordinate `x + i y`, and
diagonal imbalance `d`. -/
noncomputable def completionMatrix (t x y d : ℝ) : TrineMatrix :=
  !![((t + d) / 2 : ℂ), (x : ℂ) + Complex.I * y;
     (x : ℂ) - Complex.I * y, ((t - d) / 2 : ℂ)]

theorem completionMatrix_hermitian (t x y d : ℝ) :
    (completionMatrix t x y d)ᴴ = completionMatrix t x y d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [completionMatrix, Matrix.conjTranspose_apply] <;> ring

theorem completionMatrix_trace (t x y d : ℝ) :
    (completionMatrix t x y d).trace = (t : ℂ) := by
  simp [completionMatrix, Matrix.trace_fin_two]
  ring

theorem completionMatrix_det (t x y d : ℝ) :
    (completionMatrix t x y d).det =
      (((t ^ 2 - d ^ 2) / 4 - (x ^ 2 + y ^ 2) : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [completionMatrix, Matrix.det_fin_two] <;> norm_cast <;> ring

/-- Literal matrix positivity is exactly the scalar completion predicate used
throughout the trine acquisition development. -/
theorem completionMatrix_posSemidef_iff (t x y d : ℝ) :
    (completionMatrix t x y d).PosSemidef ↔
      PositiveTrineCompletion t x y d := by
  constructor
  · intro hM
    have htrace := hM.trace_nonneg
    have hdet := hM.det_nonneg
    have ht : 0 ≤ t := by
      rw [completionMatrix_trace] at htrace
      exact Complex.zero_le_real.mp htrace
    have hdetR : 0 ≤ (t ^ 2 - d ^ 2) / 4 - (x ^ 2 + y ^ 2) := by
      rw [completionMatrix_det] at hdet
      exact Complex.zero_le_real.mp hdet
    apply (positiveTrineCompletion_iff ht).mpr
    nlinarith
  · intro h
    have ht : 0 ≤ t := by linarith [h.1, h.2.1]
    apply (finTwo_posSemidef_iff_trace_det_nonneg
      (completionMatrix t x y d) (completionMatrix_hermitian t x y d)).2
    constructor
    · rw [completionMatrix_trace]
      exact_mod_cast ht
    · rw [completionMatrix_det]
      exact_mod_cast (show (0 : ℝ) ≤
        (t ^ 2 - d ^ 2) / 4 - (x ^ 2 + y ^ 2) by nlinarith [h.2.2])

/-- The balanced matrix is positive exactly on the manuscript disk. -/
theorem balancedMatrix_posSemidef_iff {t x y : ℝ} (ht : 0 ≤ t) :
    (completionMatrix t x y 0).PosSemidef ↔
      4 * (x ^ 2 + y ^ 2) ≤ t ^ 2 := by
  rw [completionMatrix_posSemidef_iff, balanced_completion_iff ht]

/-- The general diagonal entries `p,q` are the imbalance parameterization
`t=p+q`, `d=p-q`. -/
theorem completionMatrix_trace_imbalance_parameterization
    (p q x y : ℝ) :
    completionMatrix (p + q) x y (p - q) =
      !![(p : ℂ), (x : ℂ) + Complex.I * y;
         (x : ℂ) - Complex.I * y, (q : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [completionMatrix] <;> ring

/-- Equation (TRI.1): at unit trace, positive completions are exactly the
imbalance interval `d² ≤ 1 - 4|g|²`. -/
theorem unitTrace_completion_posSemidef_iff (x y d : ℝ) :
    (completionMatrix 1 x y d).PosSemidef ↔
      d ^ 2 ≤ 1 - 4 * (x ^ 2 + y ^ 2) := by
  rw [completionMatrix_posSemidef_iff,
    positiveTrineCompletion_iff (show (0 : ℝ) ≤ 1 by norm_num)]
  constructor <;> intro h <;> nlinarith

/-- Pointwise balanced matrix density. -/
noncomputable def balancedMatrixDensity {Ω : Type*}
    (t x y : Ω → ℝ) (ω : Ω) : TrineMatrix :=
  completionMatrix (t ω) (x ω) (y ω) 0

/-- Genuine matrix-valued measure carried by the balanced density. -/
noncomputable def balancedMatrixMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (t x y : Ω → ℝ) : VectorMeasure Ω TrineMatrix :=
  μ.withDensityᵥ (balancedMatrixDensity t x y)

/-- Positivity of the balanced matrix-valued density is exactly the scalar
trine positivity condition almost everywhere. -/
theorem ae_balancedMatrix_posSemidef_iff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (t x y : Ω → ℝ) (ht : ∀ᵐ ω ∂μ, 0 ≤ t ω) :
    (∀ᵐ ω ∂μ, (balancedMatrixDensity t x y ω).PosSemidef) ↔
      ∀ᵐ ω ∂μ, 4 * (x ω ^ 2 + y ω ^ 2) ≤ t ω ^ 2 := by
  constructor
  · intro h
    filter_upwards [ht, h] with ω htω hω
    exact (balancedMatrix_posSemidef_iff htω).mp hω
  · intro h
    filter_upwards [ht, h] with ω htω hω
    exact (balancedMatrix_posSemidef_iff htω).mpr hω

/-- Every measurable positive imbalance density integrates to a genuine
matrix-valued vector measure; the positivity certificate remains pointwise
almost everywhere. -/
theorem positive_completion_matrix_measure
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (t x y d : Ω → ℝ)
    (hpos : ∀ᵐ ω ∂μ, PositiveTrineCompletion (t ω) (x ω) (y ω) (d ω)) :
    ∀ᵐ ω ∂μ,
      (completionMatrix (t ω) (x ω) (y ω) (d ω)).PosSemidef := by
  filter_upwards [hpos] with ω hω
  exact (completionMatrix_posSemidef_iff _ _ _ _).mpr hω

end TrineMatrixCarrier
end NCG
