/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SaturatedFiniteDiracGenerator
import NCG.Grand.CenteredCommutantNormal

/-!
# Saturated generator and finite-Dirac projection assembly

This file composes the finite mechanisms of
`thm:SMST-generator-projections` for one common reconstructed generator:
first Krylov stabilization, reduction by the saturated carrier, constructive
innovation, the grading-even/odd and finite-Dirac Hilbert--Schmidt budget,
zero-defect provenance, and the scalar-commutant normal conclusion.
-/

noncomputable section

open Matrix
open scoped ComplexOrder

namespace NCG
namespace SMSTGeneratorProjectionsAssembly

variable {d e : ℕ} {k : Type*} [Fintype k] [DecidableEq k]

/-- Complete certificate for the finite generator/projection theorem on one
common generator and one saturated source carrier. -/
structure Certificate
    (G Gamma Pi : Matrix (Fin d) (Fin d) ℂ)
    (W : Matrix (Fin d) k ℂ)
    (K : ℕ → Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    (selected : Matrix (Fin d) (Fin e) ℂ)
    (completeOdd : Matrix (Fin d) (Fin d) ℂ) : Prop where
  firstStabilization :
    ∃ nStar,
      (∀ m, m < nStar → K m ≠ K (m + 1)) ∧
      K nStar = K (nStar + 1) ∧
      Submodule.map (Matrix.toEuclideanLin G) (K nStar) ≤ K nStar
  saturatedCarrierReduces :
    let P := W * Wᴴ
    ((1 : Matrix (Fin d) (Fin d) ℂ) - P) * G * P = 0 ∧
      P * G * ((1 : Matrix (Fin d) (Fin d) ℂ) - P) = 0 ∧
      P * G = G * P
  innovationConstructsMissingLayer :
    let innovation :=
      Wᴴ * (G * G) * W - (Wᴴ * G * W) * (Wᴴ * G * W)
    innovation = (((1 : Matrix (Fin d) (Fin d) ℂ) - W * Wᴴ) * G * W)ᴴ *
        (((1 : Matrix (Fin d) (Fin d) ℂ) - W * Wᴴ) * G * W) ∧
      innovation.PosSemidef ∧
      innovation.rank =
        (((1 : Matrix (Fin d) (Fin d) ℂ) - W * Wᴴ) * G * W).rank ∧
      (innovation = 0 ↔
        ((1 : Matrix (Fin d) (Fin d) ℂ) - W * Wᴴ) * G * W = 0)
  gradedFiniteDiracBudget :
    let evenPart := (2 : ℂ)⁻¹ • (G + Gamma * G * Gamma)
    let oddPart := (2 : ℂ)⁻¹ • (G - Gamma * G * Gamma)
    let canonicalDirac := Pi * oddPart
    let extraOdd := ((1 : Matrix (Fin d) (Fin d) ℂ) - Pi) * oddPart
    (Gᴴ * G).trace = (evenPartᴴ * evenPart).trace +
      (canonicalDiracᴴ * canonicalDirac).trace +
      (extraOddᴴ * extraOdd).trace
  zeroProvenance :
    Pi * completeOdd = completeOdd ∧
      ((1 : Matrix (Fin d) (Fin d) ℂ) - Pi) * completeOdd = 0 ∧
      ∃ coefficients : Matrix (Fin e) (Fin d) ℂ,
        completeOdd = selected * coefficients
  zeroProvenanceBudget :
    let canonicalDirac := Pi * completeOdd
    let extraOdd := ((1 : Matrix (Fin d) (Fin d) ℂ) - Pi) * completeOdd
    (completeOddᴴ * completeOdd).trace =
        (canonicalDiracᴴ * canonicalDirac).trace +
          (extraOddᴴ * extraOdd).trace ∧
      canonicalDirac = completeOdd ∧ extraOdd = 0

/-- Exact same-generator assembly.  No projector, innovation, or
finite-Dirac conclusion is supplied as an assumption. -/
theorem generator_projections_exact
    (G Gamma Pi : Matrix (Fin d) (Fin d) ℂ)
    (W : Matrix (Fin d) k ℂ)
    (K : ℕ → Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    (selected : Matrix (Fin d) (Fin e) ℂ)
    (completeOdd : Matrix (Fin d) (Fin d) ℂ)
    (hKmono : ∀ n, K n ≤ K (n + 1))
    (hKforward : ∀ n,
      Submodule.map (Matrix.toEuclideanLin G) (K n) ≤ K (n + 1))
    (hW : Wᴴ * W = 1) (hG : Gᴴ = G)
    (hinvariant : ∃ C : Matrix k k ℂ, G * W = W * C)
    (hGammaH : Gammaᴴ = Gamma) (hGamma2 : Gamma * Gamma = 1)
    (hPiH : Piᴴ = Pi) (hPi2 : Pi * Pi = Pi)
    (hselected : Pi * selected = selected)
    (hprovenance : oddProvenanceDefect selected completeOdd = 0) :
    Certificate G Gamma Pi W K selected completeOdd := by
  refine {
    firstStabilization :=
      finiteKrylovChain_firstStabilization K
        (Matrix.toEuclideanLin G) hKmono hKforward
    saturatedCarrierReduces :=
      stabilizedIsometricCarrier_reduces W G hW hG hinvariant
    innovationConstructsMissingLayer :=
      finiteKrylovInnovation_detectsStabilization W G hW hG
    gradedFiniteDiracBudget :=
      gradedFiniteDirac_hilbertSchmidtBudget
        G Gamma Pi hGammaH hGamma2 hPiH hPi2
    zeroProvenance :=
      zeroOddProvenance_fixesFiniteDiracProjection
        Pi selected completeOdd hselected hprovenance
    zeroProvenanceBudget :=
      zeroOddProvenance_finiteDiracBudget
        Pi selected completeOdd hPiH hPi2 hselected hprovenance }

/-- The last clause of the theorem: after the same even generator has been
projected to a scalar commutant and its trace part removed, the normal
component vanishes. -/
theorem scalarCommutant_normalComponent_zero
    [Nonempty (Fin d)] {a : Type*}
    (kinematic : a → Matrix (Fin d) (Fin d) ℂ)
    (G Gamma expectedEven : Matrix (Fin d) (Fin d) ℂ)
    (hrange : ∀ i, expectedEven * kinematic i =
      kinematic i * expectedEven)
    (hscalar : ∀ Z : Matrix (Fin d) (Fin d) ℂ,
      (∀ i, Z * kinematic i = kinematic i * Z) →
        ∃ c : ℂ, Z = c • 1)
    (htrace : expectedEven.trace =
      ((2 : ℂ)⁻¹ • (G + Gamma * G * Gamma)).trace) :
    centeredCommutantNormal expectedEven
      ((2 : ℂ)⁻¹ • (G + Gamma * G * Gamma)) = 0 :=
  scalarCommutant_centeredExpectation_zero
    kinematic _ expectedEven hrange hscalar htrace

end SMSTGeneratorProjectionsAssembly
end NCG
