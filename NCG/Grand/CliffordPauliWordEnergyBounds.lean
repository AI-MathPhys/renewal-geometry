/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CliffordPauliWordSpectralCertificate

/-!
# Sharp energy bounds for the Clifford Pauli-word decomposition

This module turns the explicit Pauli-word sign certificate into the sharp
coefficient-level spectral window used by the Clifford matter audit.  The
identity word is removed because it is exactly the multiplicity-commutant
component.
-/

namespace NCG
namespace CliffordPauliWordEnergyBounds

open CliffordPauliWordSpectralCertificate

noncomputable section

/-- Hilbert--Schmidt energy outside the scalar Pauli word. -/
def offScalarEnergy (c : WordIndex → ℂ) : ℝ :=
  4 * ∑ w, if w = (0, 0) then 0 else Complex.normSq (c w)

/-- Sum of the four Clifford-axis commutator energies. -/
def commutatorEnergy (c : WordIndex → ℂ) : ℝ :=
  ∑ μ, 4 * ∑ w, Complex.normSq (axisCoefficient μ c w)

/-- A fixed Pauli word contributes four times its norm-square for every axis
with which it anticommutes. -/
theorem axisCoefficient_energy_sum (c : WordIndex → ℂ) (w : WordIndex) :
    (∑ μ, Complex.normSq (axisCoefficient μ c w)) =
      4 * anticommutationCount w * Complex.normSq (c w) := by
  rcases w with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [axisCoefficient, anticommutesAxis, anticommutationCount,
      Fin.sum_univ_four, Complex.normSq_mul, Matrix.cons_val_two,
      Matrix.cons_val_three] <;> ring

/-- Exact diagonal form of the Clifford commutator energy. -/
theorem commutatorEnergy_eq_weighted (c : WordIndex → ℂ) :
    commutatorEnergy c =
      16 * ∑ w, anticommutationCount w * Complex.normSq (c w) := by
  unfold commutatorEnergy
  calc
    (∑ μ, 4 * ∑ w, Complex.normSq (axisCoefficient μ c w)) =
        4 * ∑ μ, ∑ w, Complex.normSq (axisCoefficient μ c w) :=
      (Finset.mul_sum Finset.univ
        (fun μ => ∑ w, Complex.normSq (axisCoefficient μ c w)) 4).symm
    _ = 4 * ∑ w, ∑ μ, Complex.normSq (axisCoefficient μ c w) := by
      rw [Finset.sum_comm]
    _ = 16 * ∑ w, anticommutationCount w * Complex.normSq (c w) := by
      simp_rw [axisCoefficient_energy_sum]
      have hfactor :
          (∑ w, 4 * (anticommutationCount w : ℝ) * Complex.normSq (c w)) =
            4 * ∑ w, anticommutationCount w * Complex.normSq (c w) := by
        calc
          (∑ w, 4 * (anticommutationCount w : ℝ) * Complex.normSq (c w)) =
              ∑ w, 4 * ((anticommutationCount w : ℝ) *
                Complex.normSq (c w)) := by
            apply Finset.sum_congr rfl
            intro w _
            ring
          _ = 4 * ∑ w, anticommutationCount w * Complex.normSq (c w) :=
            (Finset.mul_sum Finset.univ
              (fun w => (anticommutationCount w : ℝ) *
                Complex.normSq (c w)) 4).symm
      rw [hfactor]
      ring

/-- Every nonidentity Pauli word meets between one and four Clifford axes.
Consequently the commutator energy has the sharp spectral window `[4,16]`
relative to the off-scalar Hilbert--Schmidt energy. -/
theorem commutatorEnergy_bounds (c : WordIndex → ℂ) :
    4 * offScalarEnergy c ≤ commutatorEnergy c ∧
      commutatorEnergy c ≤ 16 * offScalarEnergy c := by
  rw [commutatorEnergy_eq_weighted]
  have hlower :
      (∑ w, if w = (0, 0) then 0 else Complex.normSq (c w)) ≤
        ∑ w, anticommutationCount w * Complex.normSq (c w) := by
    apply Finset.sum_le_sum
    intro w _
    by_cases hw : w = (0, 0)
    · subst w
      simp [anticommutationCount]
    · rw [if_neg hw]
      have hb := (anticommutationCount_bounds w hw).1
      have hq := Complex.normSq_nonneg (c w)
      calc
        Complex.normSq (c w) = 1 * Complex.normSq (c w) := by ring
        _ ≤ (anticommutationCount w : ℝ) * Complex.normSq (c w) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hb) hq
  have hupper :
      (∑ w, anticommutationCount w * Complex.normSq (c w)) ≤
        4 * ∑ w, if w = (0, 0) then 0 else Complex.normSq (c w) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w _
    by_cases hw : w = (0, 0)
    · subst w
      simp [anticommutationCount]
    · rw [if_neg hw]
      have hb := (anticommutationCount_bounds w hw).2
      have hq := Complex.normSq_nonneg (c w)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hb) hq
  unfold offScalarEnergy
  constructor <;> nlinarith

end
end CliffordPauliWordEnergyBounds
end NCG
