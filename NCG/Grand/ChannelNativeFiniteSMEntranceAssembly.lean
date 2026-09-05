/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMSTChannelNativeEntranceExact
import NCG.Grand.SaturatedFiniteDiracGenerator
import NCG.Grand.RelativeHoweGramSpectralCertificateExact
import NCG.Grand.TypedTransitionGeneratorAudit
import NCG.Grand.SMSTCommutant

/-!
# Channel-native finite Standard-Model entrance

This module assembles the two paragraphs of
`cor:SMST-channel-native-entrance` into one theorem.  The analytic channel
entrance is joined to the exact finite-Dirac projection, the actual relative
Howe Gram certificate, the five protected type-residue kernel, and the global
finite multiplicity-quiver commutant.  Thus the promotion clause is a compiled
result rather than a list of cross-citations.
-/

noncomputable section

open Filter Set Matrix
open scoped ComplexOrder

namespace NCG
namespace ChannelNativeFiniteSMEntrance

/-- **Channel-native finite-SM entrance and promotion.**  A compiled channel
whose Hamiltonian error tends to zero enters through a nonzero source-core
generator.  If the odd provenance defect vanishes, that complete odd generator
is exactly fixed by the finite-Dirac projector and factors through its selected
source.  In the same assembly, the relative Howe Gram detects the proposed
commutant with an attained spectral margin, the three positive typed edges have
exactly the five-type constant kernel, and the ambient typed-quiver commutant is
exactly the endomorphism algebra of the multiplicity quiver. -/
theorem channel_native_finiteSM_entrance_and_promotion
    {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (Hh : ℝ → Matrix d d ℂ) (Dtl : Matrix d d ℂ) (comparisonConstant : ℝ)
    (sourceError : ℝ → ℝ)
    (hSource : Tendsto sourceError (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hHerm : ∀ h, (Hh h - Dtl)ᴴ = Hh h - Dtl)
    (hTrace : ∀ h, (Hh h - Dtl).trace = 0)
    (hProjection : ∀ h,
      adSuperHSNorm (Hh h - Dtl) ≤ comparisonConstant * sourceError h)
    (hTarget : Dtl ≠ 0)
    {dOdd eOdd kOdd : ℕ}
    (Pi : Matrix (Fin dOdd) (Fin dOdd) ℂ)
    (selected : Matrix (Fin dOdd) (Fin eOdd) ℂ)
    (completeOdd : Matrix (Fin dOdd) (Fin kOdd) ℂ)
    (hSelected : Pi * selected = selected)
    (hProvenance : oddProvenanceDefect selected completeOdd = 0)
    {n : Type*} [Fintype n] {s : ℕ}
    (generators : Fin s → Matrix n n ℂ)
    (proposedCommutant : Submodule ℂ (EuclideanSpace ℂ (n × n)))
    (hCommutant : proposedCommutant ≤
      LinearMap.ker (jointCommutatorL2 generators))
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (x : TypedTransitionGeneratorAudit.StandardModelType → ℝ)
    {A J : Type*} [Fintype J]
    (V N : A → Type*) [∀ q, Fintype (V q)] [∀ q, Fintype (N q)]
    [∀ q, DecidableEq (V q)] [∀ q, Nonempty (N q)]
    (src dst : J → A)
    (arrows : ∀ j, V (dst j) → V (src j) →
      Matrix (N (dst j)) (N (src j)) ℂ)
    (multiplicity : ∀ q, Matrix (N q) (N q) ℂ) :
    -- genuine channel entrance
    (Tendsto (fun h => matrixHSNorm (Hh h - Dtl))
        (nhdsWithin 0 (Ioi 0)) (nhds 0)
      ∧ ∀ᶠ h in nhdsWithin (0 : ℝ) (Ioi 0), Hh h ≠ 0)
    ∧
    -- source-native finite-Dirac membership and coefficient factorization
    (Pi * completeOdd = completeOdd
      ∧ ((1 : Matrix (Fin dOdd) (Fin dOdd) ℂ) - Pi) * completeOdd = 0
      ∧ ∃ coefficients : Matrix (Fin eOdd) (Fin kOdd) ℂ,
          completeOdd = selected * coefficients)
    ∧
    -- relative Howe positivity, exact commutant, and spectral margin
    (((∀ X ∈ proposedCommutantᗮ, X ≠ 0 →
          0 < ‖jointCommutatorL2 generators X‖ ^ 2)
        ↔ LinearMap.ker (jointCommutatorL2 generators) = proposedCommutant)
      ∧ (∀ X : Matrix n n ℂ,
          matrixL2 X ∈ LinearMap.ker (jointCommutatorL2 generators)
            ↔ ∀ j, generators j * X = X * generators j)
      ∧ (LinearMap.ker (jointCommutatorL2 generators) = proposedCommutant →
          (LinearMap.ker (jointCommutatorL2 generators))ᗮ =
            proposedCommutantᗮ)
      ∧ RelativeHoweSpectralMargin generators)
    ∧
    -- the five protected type residues have precisely the expected kernel
    (TypedTransitionGeneratorAudit.fiveTypePotentialEnergy a b c x = 0 ↔
      x .Q = x .u ∧ x .Q = x .d ∧ x .L = x .e)
    ∧
    -- the multiplicity commutant is the endomorphism algebra of the quiver
    ((∀ j,
        quiverMatMul (quiverResidual (multiplicity (dst j)))
            (quiverAssemble (arrows j)) =
          quiverMatMul (quiverAssemble (arrows j))
            (quiverResidual (multiplicity (src j))))
      ↔ ∀ j vb va,
          multiplicity (dst j) * arrows j vb va =
            arrows j vb va * multiplicity (src j)) := by
  refine ⟨SMSTChannel.channel_native_entrance Hh Dtl comparisonConstant
      sourceError hSource hHerm hTrace hProjection hTarget, ?_⟩
  refine ⟨zeroOddProvenance_fixesFiniteDiracProjection
      Pi selected completeOdd hSelected hProvenance, ?_⟩
  refine ⟨relativeHoweGram_exact_certificate_and_margin
      generators proposedCommutant hCommutant, ?_⟩
  refine ⟨TypedTransitionGeneratorAudit.fiveTypePotentialEnergy_eq_zero_iff
      a b c ha hb hc x, ?_⟩
  exact finite_typed_quiver_commutant_iff_endomorphism
    V N src dst arrows multiplicity

end ChannelNativeFiniteSMEntrance
end NCG
