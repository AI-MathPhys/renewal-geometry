/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactResolventStrongCofinalMarkedRenewalLimitExact
import NCG.Grand.SpectralCompressionStrictQuasidiagonalEquivalenceExact
import NCG.Grand.L2FiniteCoordinateScreensStrongConvergenceExact
import NCG.Grand.ToeplitzFiniteRankDiagonalProjectionExact
import NCG.Grand.ToeplitzNumberOperatorShiftCommutatorExact

/-!
# Essential-image trichotomy for Renewal spectralization

This module assembles the three independently proved category-dependent image
statements.  The finite marked branch is constructive, the strong branch uses
the actual finite resolvent eigenspace screens of the target triple, and the
strict branch is characterized exactly by two-sided quasidiagonal corner
decay.  The Toeplitz number-operator/shift system records compact resolvent,
strong finite screens, and the uniform norm obstruction to strictness.
-/

open Complex Filter Module Set Topology
open scoped lp

noncomputable section

namespace NCG.SpectralizationEssentialImageTrichotomyExact

universe u v

open NCG.CoordinateFiniteSpectralPacketMarkedRenewalRealizationExact
open NCG.CompactResolventStrongCofinalMarkedRenewalLimitExact
open NCG.SpectralCompression
open NCG.ToeplitzScreenObstruction

/-- The strict image is characterized by quasidiagonal corner decay, and its
multiplicativity defect is exactly the SP.28 off-diagonal corner. -/
structure StrictNormMonoidalImageCertificate
    {B : Type u} [CStarAlgebra B] {X : Type v}
    (P : X → B) (l : Filter X) : Prop where
  idempotent : ∀ n, P n * P n = P n
  selfAdjoint : ∀ n, star (P n) = P n
  criterion : NormMultiplicativeAlong P l ↔ QuasidiagonalAlong P l
  compressionDefect : ∀ n (a b : B),
    compress (P n) (a * b) - compress (P n) a * compress (P n) b =
      P n * a * (1 - P n) * b * P n

/-- The explicit analytic witness showing that the strict subclass is proper:
the number operator has compact two-sided resolvent; canonical finite screens
and all bounded compressions converge strongly; but every nonzero finite-rank
idempotent commuting with the number operator has shift-commutator norm at
least one. -/
structure ToeplitzStrongNotStrictCertificate : Prop where
  denseDomain : Dense (numberOperator.domain : Set H)
  compactTwoSidedResolvent :
    ∃ (R : H →L[ℂ] H) (hmem : ∀ y : H, R y ∈ numberOperator.domain),
      IsCompactOperator (R : H → H) ∧
      (∀ y : H,
        numberOperator ⟨R y, hmem y⟩ - Complex.I • R y = y) ∧
      (∀ x : numberOperator.domain,
        R (numberOperator x - Complex.I • (x : H)) = x)
  finiteScreensCompact : ∀ n,
    IsCompactOperator
      ((l2FinsetScreen (E := ℂ) (Finset.range n) : H →L[ℂ] H) : H → H)
  screensStrong : ∀ x : H,
    Tendsto
      (fun n : ℕ => l2FinsetScreen (E := ℂ) (Finset.range n) x)
      atTop (𝓝 x)
  compressionsStrong : ∀ (T : H →L[ℂ] H) (x : H),
    Tendsto
      (fun n : ℕ =>
        NCG.screenCompression
          (l2FinsetScreen (E := ℂ) (Finset.range n)) T x)
      atTop (𝓝 (T x))
  productDefectsStrong : ∀ (T U : H →L[ℂ] H) (x : H),
    Tendsto
      (fun n : ℕ =>
        NCG.screenCompression
            (l2FinsetScreen (E := ℂ) (Finset.range n)) T
            (NCG.screenCompression
              (l2FinsetScreen (E := ℂ) (Finset.range n)) U x) -
          NCG.screenCompression
            (l2FinsetScreen (E := ℂ) (Finset.range n)) (T.comp U) x)
      atTop (𝓝 0)
  shiftCommutatorOnBasis : ∀ n,
    numberOperator
        ⟨unilateralShift (basisVector n), by
          rw [unilateralShift_basisVector]
          exact basisVector_mem_numberOperatorDomain (n + 1)⟩ -
      unilateralShift
        (numberOperator
          ⟨basisVector n, basisVector_mem_numberOperatorDomain n⟩) =
        unilateralShift (basisVector n)
  strictObstruction : ∀ (Q : H →L[ℂ] H)
      [FiniteDimensional ℂ (LinearMap.range Q.toLinearMap)],
    ∀ (hpres : ∀ n, Q (basisVector n) ∈ numberOperator.domain),
    (∀ n,
      numberOperator
        ⟨Q (basisVector n), hpres n⟩ =
          Q (numberOperator
            ⟨basisVector n, basisVector_mem_numberOperatorDomain n⟩)) →
    Q.comp Q = Q → Q ≠ 0 →
      1 ≤ ‖Q.comp unilateralShift - unilateralShift.comp Q‖

/-- The Toeplitz number-operator/shift system lies in the strong screen class
and is excluded from the strict norm-monoidal class. -/
theorem toeplitz_strong_not_strict : ToeplitzStrongNotStrictCertificate where
  denseDomain := numberOperator_dense_domain
  compactTwoSidedResolvent := numberOperator_compact_resolvent
  finiteScreensCompact := fun n =>
    NCG.l2FinsetScreen_isCompactOperator (E := ℂ) (Finset.range n)
  screensStrong := NCG.tendsto_l2FinsetScreen_range_apply
  compressionsStrong :=
    NCG.tendsto_screenCompression_l2FinsetScreen_range_apply
  productDefectsStrong :=
    NCG.tendsto_screenCompression_multiplicativity_defect_apply
  shiftCommutatorOnBasis :=
    numberOperator_comm_unilateralShift_basisVector
  strictObstruction := by
    intro Q _ hpres hcomm hidem hne
    exact
      one_le_norm_commutator_of_finiteRank_idempotent_commutes_numberOperator
        Q hpres hcomm hidem hne

/-- Exact assembly of the manuscript's three essential-image clauses.  The
parameters are arbitrary, so the first two conjuncts express the universal
finite and compact-resolvent claims; the third is the exact strict criterion,
and the final conjunct supplies properness. -/
theorem spectralization_essentialImage_trichotomy
    {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    {K : Type} [Fintype K] [DecidableEq K]
    (finitePacket : CoordinateFiniteSpectralPacket A K)
    {Htarget : Type v} [NormedAddCommGroup Htarget]
      [InnerProductSpace ℂ Htarget] [CompleteSpace Htarget]
    (compactPacket : SpectralTriple A Htarget)
    {B : Type u} [CStarAlgebra B] {X : Type v}
    (P : X → B) (l : Filter X)
    (hP : ∀ n, P n * P n = P n)
    (hPstar : ∀ n, star (P n) = P n) :
    Nonempty (MarkedRenewalRealization finitePacket) ∧
      StrongCofinalMarkedRenewalLimit compactPacket ∧
      StrictNormMonoidalImageCertificate P l ∧
      ToeplitzStrongNotStrictCertificate := by
  refine ⟨
    every_finiteSpectralPacket_has_finiteMarkedRenewalRealization finitePacket,
    every_compactResolventSpectralTriple_is_strongCofinalMarkedRenewalLimit
      compactPacket,
    ?_,
    toeplitz_strong_not_strict⟩
  exact {
    idempotent := hP
    selfAdjoint := hPstar
    criterion := normMultiplicativeAlong_iff_quasidiagonalAlong P l hP hPstar
    compressionDefect := fun n a b =>
      compress_mul_sub_mul_compress (P n) a b (hP n) }

end NCG.SpectralizationEssentialImageTrichotomyExact
