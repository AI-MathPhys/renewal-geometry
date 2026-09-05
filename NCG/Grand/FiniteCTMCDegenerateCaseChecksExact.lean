/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteFeynmanKacLargeDeviationsExact
import NCG.Grand.FiniteCTMCPhysicalRewardFidelityExact

/-!
# Degenerate-case checks for the full Feynman--Kac/LDP compiler

The theorem is instantiated on a genuine two-state absorbing generator and
on the singleton zero generator. These checks ensure that no positive-escape
or nontrivial-carrier premise has survived in the all-carrier interface.
-/

open MeasureTheory
open scoped BigOperators

namespace NCG.FiniteCTMCDegenerateCaseChecks

open DrivenProcess DrivenProcess.FinitePath FiniteCTMCGeneralPathLaw
open FiniteCTMCGeneralRewardLaw FiniteCTMCSCGFConvexity FiniteGeneratorCommunication

noncomputable section

/-- One transient state jumps at rate one to an absorbing state. -/
def absorbingGenerator : Matrix Bool Bool ℝ :=
  fun i j => if i = false then if j = false then -1 else 1 else 0

theorem absorbingGenerator_isGenerator : IsGenerator absorbingGenerator where
  offDiag_nonneg := by
    intro i j hij
    cases i <;> cases j <;> simp_all [absorbingGenerator]
  row_sum := by
    intro i
    cases i <;> simp [absorbingGenerator]

theorem absorbingGenerator_has_zero_escape : escapeRate absorbingGenerator true = 0 := by
  simp [escapeRate, absorbingGenerator]

/-- The complete theorem's unconditional Feynman--Kac clause applies to an
absorbing generator with arbitrary state and directed jump rewards. -/
theorem absorbing_feynmanKac
    (p : Bool → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (v : Bool → ℝ) (g : Bool → Bool → ℝ) (k T : ℝ) (f : Bool → ℝ) (hT : 0 ≤ T) :
    physicalPathMoment absorbingGenerator absorbingGenerator_isGenerator false p v g k T f =
      ∑ x, p x * Matrix.mulVec (Matrix.exponentialEntry (T • tilt absorbingGenerator v g k)) f x :=
  (FiniteFeynmanKacLargeDeviations.finite_feynmanKac_scgf_largeDeviations
    absorbingGenerator absorbingGenerator_isGenerator false p hp hsum v g).1 k T f hT

theorem singleton_zero_isGenerator : IsGenerator (0 : Matrix (Fin 1) (Fin 1) ℝ) where
  offDiag_nonneg := by intro i j hij; simp
  row_sum := by intro i; simp

/-- The singleton zero generator satisfies the standard irreducibility predicate. -/
theorem singleton_zero_isCommunicating : IsCommunicating (0 : Matrix (Fin 1) (Fin 1) ℝ) :=
  isCommunicating_of_subsingleton _

/-- The exact all-carrier compiler proves the singleton process's full LDP. -/
theorem singleton_zero_hasLargeDeviationPrinciple
    (v : Fin 1 → ℝ) (g : Fin 1 → Fin 1 → ℝ) :
    RealTimeLargeDeviations.HasLargeDeviationPrinciple
      (fun T => physicalRewardLaw (0 : Matrix (Fin 1) (Fin 1) ℝ) singleton_zero_isGenerator
        0 (fun _ => 1) v g T) (spectralRate (0 : Matrix (Fin 1) (Fin 1) ℝ) v g) := by
  exact FiniteFeynmanKacLargeDeviations.hasLargeDeviationPrinciple
    0 singleton_zero_isGenerator singleton_zero_isCommunicating 0 (fun _ => 1)
    (fun _ => zero_le_one) (by simp) v g

end

end NCG.FiniteCTMCDegenerateCaseChecks
