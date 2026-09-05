/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CanonicalLoadedSubhierarchyAssembly
import NCG.Grand.CompletionConservative
import NCG.Grand.SaturatedFiniteDiracGenerator
import NCG.Grand.SMSTChannelNativeEntranceExact
import NCG.Grand.SMTensorGeneration

/-!
# Finite SM--spacetime loaded emergence

This is the E1--E7 assembly theorem for the reduced finite mixed-word tensor.
The hierarchy component is constructed by the canonical loaded-subhierarchy
theorem.  The two finite-Dirac entrance branches, conservative fallback, and
positive residual criterion are then attached with their exact finite proofs.
-/

open Matrix Filter Set
open scoped ComplexOrder Kronecker

namespace NCG

/-- Raw literal-source data for promotion of the complete odd generator to
the selected finite-Dirac relation space. -/
structure LiteralFiniteDiracInput (d e k : ℕ) where
  projector : Matrix (Fin d) (Fin d) ℂ
  selected : Matrix (Fin d) (Fin e) ℂ
  completeOdd : Matrix (Fin d) (Fin k) ℂ
  selected_fixed : projector * selected = selected
  provenance_zero : oddProvenanceDefect selected completeOdd = 0

/-- The conclusion derived on the literal source-native branch. -/
def LiteralFiniteDiracConclusion {d e k : ℕ}
    (B : LiteralFiniteDiracInput d e k) : Prop :=
  B.projector * B.completeOdd = B.completeOdd ∧
    ((1 : Matrix (Fin d) (Fin d) ℂ) - B.projector) * B.completeOdd = 0 ∧
    ∃ coefficients : Matrix (Fin e) (Fin k) ℂ,
      B.completeOdd = B.selected * coefficients

/-- Raw weak-channel data.  The estimate hypotheses are the output interface
of the already proved direct/bracket channel compilers, not the desired
convergence conclusion. -/
structure WeakChannelInput (d : Type) [Fintype d] [DecidableEq d] [Nonempty d] where
  compiled : ℝ → Matrix d d ℂ
  target : Matrix d d ℂ
  comparisonConstant : ℝ
  sourceError : ℝ → ℝ
  sourceError_tendsto : Tendsto sourceError (nhdsWithin 0 (Ioi 0)) (nhds 0)
  error_hermitian : ∀ h, (compiled h - target)ᴴ = compiled h - target
  error_traceless : ∀ h, (compiled h - target).trace = 0
  commutator_control : ∀ h,
    adSuperHSNorm (compiled h - target) ≤ comparisonConstant * sourceError h
  target_nonzero : target ≠ 0

/-- Exact weak-channel entrance conclusion. -/
def WeakChannelConclusion {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (B : WeakChannelInput d) : Prop :=
  Tendsto (fun h => matrixHSNorm (B.compiled h - B.target))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) ∧
    ∀ᶠ h in nhdsWithin (0 : ℝ) (Ioi 0), B.compiled h ≠ 0

/-- Exact E1--E7 certificate.  E5 is stated branchwise, just as in the
manuscript: literal data imply exact finite-Dirac promotion, while weak-channel
compiler estimates imply convergence to the same nonzero odd target. -/
structure FiniteSMSTLoadedEmergenceCertificate
    {h e panel selected A B eY : Type}
    [Fintype h] [Fintype e] [Fintype panel] [Fintype eY]
    [Ring A] [StarRing A] [Ring B] [StarRing B]
    (L : AdmissibleLoadedSubhierarchyData h e panel selected A B eY) : Prop where
  /-- E1--E4 and the cutoff part of E7. -/
  canonicalMixedWordHierarchy : CanonicalLoadedSubhierarchyCertificate L
  /-- E5, fixed representation-theoretic matter packet. -/
  matterPacket :
    tensorExteriorCentralWeights (-2) 3 =
      (fun i => ((SMTensorGeneration.generatedMatterLabels i).charge : ℚ)) ∧
    Nat.choose 3 2 = 3 ∧ Nat.choose 2 2 = 1
  /-- E5, literal source-native finite-Dirac promotion. -/
  literalFiniteDirac : ∀ {d e k} (D : LiteralFiniteDiracInput d e k),
    LiteralFiniteDiracConclusion D
  /-- E5, weak-channel direct/bracket entrance. -/
  weakChannel : ∀ {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (D : WeakChannelInput d), WeakChannelConclusion D
  /-- E6, exact conservative record fallback. -/
  conservativeFallback : ∀ {d r : Type} [Fintype d] [Fintype r]
      [DecidableEq d] [DecidableEq r] [Nonempty r],
    (∀ (A : Matrix d d ℂ) (W : Matrix r r ℂ), W.trace = 1 →
      partialTraceRight (dA := d) (dK := r) (A ⊗ₖ W) = A) ∧
    (∀ a b : Matrix d d ℂ,
      (a * b) ⊗ₖ (1 : Matrix r r ℂ) =
        (a ⊗ₖ (1 : Matrix r r ℂ)) * (b ⊗ₖ (1 : Matrix r r ℂ))) ∧
    ((1 : Matrix d d ℂ) ⊗ₖ (1 : Matrix r r ℂ) =
      (1 : Matrix (d × r) (d × r) ℂ)) ∧
    (∀ a : Matrix d d ℂ,
      aᴴ ⊗ₖ (1 : Matrix r r ℂ) = (a ⊗ₖ (1 : Matrix r r ℂ))ᴴ) ∧
    (∀ a b : Matrix d d ℂ,
      a ⊗ₖ (1 : Matrix r r ℂ) = b ⊗ₖ (1 : Matrix r r ℂ) → a = b)
  /-- E7, every stronger finite identity is equivalent to vanishing of its
  positive residual ledger. -/
  zeroResidualCriterion : ∀ {ι E : Type} [Zero E]
      (s : Finset ι) (p : ι → E) (q : E → ℝ),
    (∀ v, 0 ≤ q v) → (∀ v, q v = 0 → v = 0) → q 0 = 0 →
      ((∑ r ∈ s, q (p r)) = 0 ↔ ∀ r ∈ s, p r = 0)

/-- `thm:SMST-loaded-emergence`: exact finite E1--E7 assembly from an
admissible joint loading packet. -/
theorem finiteSMSTLoadedEmergence
    {h e panel selected A B eY : Type}
    [Fintype h] [Fintype e] [Fintype panel] [Fintype eY]
    [Ring A] [StarRing A] [Ring B] [StarRing B]
    (L : AdmissibleLoadedSubhierarchyData h e panel selected A B eY) :
    FiniteSMSTLoadedEmergenceCertificate L := by
  refine {
    canonicalMixedWordHierarchy := canonicalLoadedSubhierarchyAssembly L
    matterPacket := ?_
    literalFiniteDirac := ?_
    weakChannel := ?_
    conservativeFallback := ?_
    zeroResidualCriterion := ?_ }
  · exact ⟨SMTensorGeneration.generatedMatter_charge_table, by norm_num, by norm_num⟩
  · intro d e k D
    exact zeroOddProvenance_fixesFiniteDiracProjection
      D.projector D.selected D.completeOdd D.selected_fixed D.provenance_zero
  · intro d _ _ _ D
    exact SMSTChannel.channel_native_entrance
      D.compiled D.target D.comparisonConstant D.sourceError
      D.sourceError_tendsto D.error_hermitian D.error_traceless
      D.commutator_control D.target_nonzero
  · intro d r _ _ _ _ _
    exact sm_completion_conservative
  · intro ι E _ s p q hnn hdef hq0
    exact zero_loading_relations s p q hnn hdef hq0

end NCG
