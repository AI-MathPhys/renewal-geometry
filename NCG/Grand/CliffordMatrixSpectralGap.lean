/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CliffordPauliWordEnergyBounds

/-!
# Sharp Clifford spectral gap on the primitive matrix cell

The coefficient certificate is converted here into the invariant matrix
statement: distance from the scalar commutant is controlled, with sharp
constants, by the four gamma commutators.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace CliffordMatrixSpectralGap

open CommonOrigin
open CliffordPauliWordSpectralCertificate
open CliffordPauliWordEnergyBounds

noncomputable section

def scalarExpectation (X : Matrix C4 C4 ℂ) : Matrix C4 C4 ℂ :=
  ((4 : ℂ)⁻¹ * X.trace) • 1

def scalarResidual (X : Matrix C4 C4 ℂ) : Matrix C4 C4 ℂ :=
  X - scalarExpectation X

def gammaCommutator (X : Matrix C4 C4 ℂ) (μ : Fin 4) : Matrix C4 C4 ℂ :=
  X * gamma μ - gamma μ * X

theorem pauliWord_zero : pauliWord (0, 0) = (1 : Matrix C4 C4 ℂ) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [pauliWord, pauliAt, Matrix.kroneckerMap_apply,
      Matrix.one_apply]

def offScalarCoefficient (c : WordIndex → ℂ) (w : WordIndex) : ℂ :=
  if w = (0, 0) then 0 else c w

def scalarOnlyCoefficient (c : WordIndex → ℂ) (w : WordIndex) : ℂ :=
  if w = (0, 0) then c (0, 0) else 0

theorem synthesis_scalarOnly (c : WordIndex → ℂ) :
    pauliSynthesis (scalarOnlyCoefficient c) = c (0, 0) • 1 := by
  classical
  unfold pauliSynthesis scalarOnlyCoefficient
  simp [pauliWord_zero]

theorem synthesis_offScalar (c : WordIndex → ℂ) :
    pauliSynthesis (offScalarCoefficient c) =
      pauliSynthesis c - c (0, 0) • 1 := by
  have hsplit : c = scalarOnlyCoefficient c + offScalarCoefficient c := by
    funext w
    by_cases hw : w = (0, 0) <;>
      simp [scalarOnlyCoefficient, offScalarCoefficient, hw]
  have hadd : pauliSynthesis c =
      pauliSynthesis (scalarOnlyCoefficient c) +
        pauliSynthesis (offScalarCoefficient c) := by
    calc
      pauliSynthesisLinear c = pauliSynthesisLinear
          (scalarOnlyCoefficient c + offScalarCoefficient c) :=
        congrArg pauliSynthesisLinear hsplit
      _ = pauliSynthesisLinear (scalarOnlyCoefficient c) +
          pauliSynthesisLinear (offScalarCoefficient c) :=
        map_add pauliSynthesisLinear _ _
  rw [hadd, synthesis_scalarOnly]
  abel

theorem coefficient_zero_eq_trace (c : WordIndex → ℂ)
    (hc : pauliSynthesis c = X) :
    c (0, 0) = (4 : ℂ)⁻¹ * X.trace := by
  rw [← hc, ← pauliCoefficient_synthesis c (0, 0)]
  unfold pauliCoefficient
  rw [pauliWord_zero, Matrix.one_mul]

theorem scalarResidual_eq_synthesis_offScalar (c : WordIndex → ℂ)
    (hc : pauliSynthesis c = X) :
    scalarResidual X = pauliSynthesis (offScalarCoefficient c) := by
  have hcoef := coefficient_zero_eq_trace c hc
  unfold scalarResidual scalarExpectation
  rw [← hcoef, ← hc, synthesis_offScalar]

theorem scalarResidual_trace_energy (c : WordIndex → ℂ)
    (hc : pauliSynthesis c = X) :
    Matrix.trace ((scalarResidual X)ᴴ * scalarResidual X) =
      (offScalarEnergy c : ℂ) := by
  rw [scalarResidual_eq_synthesis_offScalar c hc,
    pauliSynthesis_trace_square]
  unfold offScalarEnergy offScalarCoefficient
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w = (0, 0)
  · simp [hw]
  · simp only [hw, ↓reduceIte]
    simpa only [RCLike.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := c w)).symm

theorem gammaCommutator_trace_energy (c : WordIndex → ℂ)
    (hc : pauliSynthesis c = X) :
    (∑ μ, Matrix.trace ((gammaCommutator X μ)ᴴ * gammaCommutator X μ)) =
      (commutatorEnergy c : ℂ) := by
  rw [← hc]
  simp_rw [gammaCommutator, pauliSynthesis_commutator,
    twistedSynthesis_trace_square]
  unfold commutatorEnergy
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_ofNat]
  apply Finset.sum_congr rfl
  intro μ _
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  simpa only [RCLike.star_def] using
    (Complex.normSq_eq_conj_mul_self
      (z := axisCoefficient μ c w)).symm

/-- Sharp primitive-cell spectral window. -/
theorem gammaCommutator_trace_bounds (X : Matrix C4 C4 ℂ) :
    (4 : ℂ) * Matrix.trace ((scalarResidual X)ᴴ * scalarResidual X) ≤
        ∑ μ, Matrix.trace ((gammaCommutator X μ)ᴴ * gammaCommutator X μ) ∧
      (∑ μ, Matrix.trace ((gammaCommutator X μ)ᴴ * gammaCommutator X μ)) ≤
        (16 : ℂ) * Matrix.trace ((scalarResidual X)ᴴ * scalarResidual X) := by
  obtain ⟨c, hc, -⟩ := exists_pauli_expansion X
  rw [scalarResidual_trace_energy c hc,
    gammaCommutator_trace_energy c hc]
  exact_mod_cast commutatorEnergy_bounds c

end
end CliffordMatrixSpectralGap
end NCG
