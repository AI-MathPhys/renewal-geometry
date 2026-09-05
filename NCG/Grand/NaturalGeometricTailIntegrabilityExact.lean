/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Exponential integrability from geometric tails of natural-valued observables

The proof uses the actual pushforward distribution and summability of its
weighted atoms. It establishes integrability, not merely an identity between
potentially undefined Bochner integrals.
-/

open MeasureTheory

namespace NCG.NaturalGeometricTailIntegrability

noncomputable section

/-- A geometric upper tail with ratio smaller than `exp(-c)` gives a finite
exponential moment with coefficient `c`. -/
theorem integrable_exp_of_geometric_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (N : Ω → ℕ) (hN : Measurable N) (C q c : ℝ)
    (hq : 0 ≤ q) (hqc : q * Real.exp c < 1)
    (htail : ∀ n, μ.real {ω | n ≤ N ω} ≤ C * q ^ n) :
    Integrable (fun ω => Real.exp (c * (N ω : ℝ))) μ := by
  let ν := μ.map N
  letI : IsFiniteMeasure ν := Measure.isFiniteMeasure_map _ _
  have hatom (n : ℕ) : ν.real {n} ≤ C * q ^ n := by
    have heq : ν.real {n} = μ.real {ω | N ω = n} := by
      simp only [ν, measureReal_def, Measure.map_apply hN (measurableSet_singleton n)]
      rfl
    rw [heq]
    exact (measureReal_mono (fun ω hω => le_of_eq hω.symm)).trans (htail n)
  have hseries : Summable (fun n : ℕ => C * (q * Real.exp c) ^ n) :=
    (summable_geometric_of_lt_one (mul_nonneg hq (Real.exp_pos c).le) hqc).mul_left C
  have hsummable : Summable (fun n : ℕ => (ν {n}).toReal * ‖Real.exp (c * (n : ℝ))‖) := by
    apply hseries.of_nonneg_of_le
    · intro n
      positivity
    · intro n
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ (C * q ^ n) * Real.exp (c * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (hatom n) (Real.exp_pos _).le
        _ = C * (q * Real.exp c) ^ n := by
          rw [mul_comm c (n : ℝ), Real.exp_nat_mul, mul_pow]
          ring
  have hi : Integrable (fun n : ℕ => Real.exp (c * (n : ℝ))) ν := by
    rw [← Measure.sum_smul_dirac ν]
    exact integrable_sum_dirac (fun n => measure_ne_top ν {n}) hsummable
  exact (integrable_map_measure (measurable_of_countable
    (fun n : ℕ => Real.exp (c * (n : ℝ)))).aestronglyMeasurable hN.aemeasurable).mp hi

end

end NCG.NaturalGeometricTailIntegrability
