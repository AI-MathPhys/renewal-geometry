/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteSpectralScreenMarkedRenewalRealizationExact
import NCG.Grand.CompactResolventSpectralProjectionTransferExact

/-!
# Strong cofinal marked Renewal limits for compact-resolvent triples

The compact normal resolvent supplies a directed family of finite orthogonal
spectral screens.  This file proves the stability statement needed for the
strong category: applying a screen to a convergent net preserves its limit.
Consequently every bounded operator, every product of bounded operators, and
every fixed matrix coefficient is recovered by the corresponding finite
compressions.  Each one of these same screens carries the finite marked
Renewal realization constructed in the companion module.
-/

open Complex Filter Module Set Topology

noncomputable section

namespace NCG.CompactResolventStrongCofinalMarkedRenewalLimitExact

universe u

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

open NCG.CompactResolventDiracSpectralScreensExact
open NCG.CompactResolventSpectralProjectionTransferExact
open NCG.CoordinateFiniteSpectralPacketMarkedRenewalRealizationExact
open NCG.FiniteSpectralScreenMarkedRenewalRealizationExact

/-- Two-sided compression by the finite resolvent screen. -/
def finiteSpectralCompression (S : SpectralTriple A H) (s : Finset ℂ)
    (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (diracSpectralScreen S s).comp
    (T.comp (diracSpectralScreen S s))

/-- Every bounded operator is recovered strongly from its finite spectral
compressions.  In particular this applies to the compact resolvent and to
each bounded commutator extension. -/
theorem tendsto_finiteSpectralCompression_apply
    (S : SpectralTriple A H) (T : H →L[ℂ] H) (x : H) :
    Tendsto (fun s : Finset ℂ => finiteSpectralCompression S s T x)
      atTop (𝓝 (T x)) := by
  have hinner : Tendsto
      (fun s : Finset ℂ => T (diracSpectralScreen S s x))
      atTop (𝓝 (T x)) :=
    T.continuous.continuousAt.tendsto.comp
      (tendsto_diracSpectralScreen_apply S x)
  simpa [finiteSpectralCompression] using
    tendsto_diracSpectralScreen_apply_of_tendsto S hinner

/-- Every fixed matrix coefficient of a compressed bounded operator converges
to the corresponding coefficient of the target operator. -/
theorem tendsto_finiteSpectralCompression_matrixCoefficient
    (S : SpectralTriple A H) (T : H →L[ℂ] H) (x y : H) :
    Tendsto
      (fun s : Finset ℂ => inner ℂ (finiteSpectralCompression S s T x) y)
      atTop (𝓝 (inner ℂ (T x) y)) :=
  (tendsto_finiteSpectralCompression_apply S T x).inner tendsto_const_nhds

/-- Products of finite compressed operators converge strongly to the target
product. -/
theorem tendsto_product_finiteSpectralCompressions_apply
    (S : SpectralTriple A H) (T U : H →L[ℂ] H) (x : H) :
    Tendsto
      (fun s : Finset ℂ =>
        finiteSpectralCompression S s T
          (finiteSpectralCompression S s U x))
      atTop (𝓝 (T (U x))) := by
  have hU := tendsto_finiteSpectralCompression_apply S U x
  have hinnerScreen : Tendsto
      (fun s : Finset ℂ => diracSpectralScreen S s
        (finiteSpectralCompression S s U x))
      atTop (𝓝 (U x)) :=
    tendsto_diracSpectralScreen_apply_of_tendsto S hU
  have hT : Tendsto
      (fun s : Finset ℂ => T (diracSpectralScreen S s
        (finiteSpectralCompression S s U x)))
      atTop (𝓝 (T (U x))) :=
    T.continuous.continuousAt.tendsto.comp hinnerScreen
  simpa [finiteSpectralCompression] using
    tendsto_diracSpectralScreen_apply_of_tendsto S hT

/-- Multiplicativity defects vanish strongly even though they need not vanish
in operator norm. -/
theorem tendsto_finiteSpectralCompression_multiplicativityDefect_apply
    (S : SpectralTriple A H) (T U : H →L[ℂ] H) (x : H) :
    Tendsto
      (fun s : Finset ℂ =>
        finiteSpectralCompression S s T
            (finiteSpectralCompression S s U x) -
          finiteSpectralCompression S s (T.comp U) x)
      atTop (𝓝 0) := by
  have hproduct :=
    tendsto_product_finiteSpectralCompressions_apply S T U x
  have hcomposition :=
    tendsto_finiteSpectralCompression_apply S (T.comp U) x
  simpa only [ContinuousLinearMap.comp_apply, sub_self] using
    hproduct.sub hcomposition

/-- The exact data asserting that a compact-resolvent spectral triple is a
strong cofinal marked Renewal limit of its finite spectral screens. -/
structure StrongCofinalMarkedRenewalLimit (S : SpectralTriple A H) : Prop where
  finiteProjection : ∀ s,
    (diracSpectralScreen S s).IsSymmetricProjection
  finiteRange : ∀ s, FiniteDimensional ℂ
    (LinearMap.range (diracSpectralScreen S s).toLinearMap)
  markedRealization : ∀ s,
    Nonempty (MarkedRenewalRealization (screenPacket S s))
  preservesDomain : ∀ s (x : S.dirac.domain),
    diracSpectralScreen S s (x : H) ∈ S.dirac.domain
  commutesDirac : ∀ s (x : S.dirac.domain),
    S.dirac ⟨diracSpectralScreen S s (x : H),
        diracSpectralScreen_mem_domain S s x⟩ =
      diracSpectralScreen S s (S.dirac x)
  projectionsStrong : ∀ x,
    Tendsto (fun s : Finset ℂ => diracSpectralScreen S s x)
      atTop (𝓝 x)
  compressionsStrong : ∀ (T : H →L[ℂ] H) x,
    Tendsto (fun s : Finset ℂ => finiteSpectralCompression S s T x)
      atTop (𝓝 (T x))
  matrixCoefficientsStrong : ∀ (T : H →L[ℂ] H) x y,
    Tendsto
      (fun s : Finset ℂ => inner ℂ (finiteSpectralCompression S s T x) y)
      atTop (𝓝 (inner ℂ (T x) y))
  productDefectsStrong : ∀ (T U : H →L[ℂ] H) x,
    Tendsto
      (fun s : Finset ℂ =>
        finiteSpectralCompression S s T
            (finiteSpectralCompression S s U x) -
          finiteSpectralCompression S s (T.comp U) x)
      atTop (𝓝 0)

/-- Essential-image alternative I2: every compact-resolvent spectral triple
(hence, in particular, every separable one) is a strong cofinal marked Renewal
limit obtained from its actual finite spectral screens. -/
theorem every_compactResolventSpectralTriple_is_strongCofinalMarkedRenewalLimit
    (S : SpectralTriple A H) :
    StrongCofinalMarkedRenewalLimit S where
  finiteProjection := diracSpectralScreen_isSymmetricProjection S
  finiteRange := diracSpectralScreen_range_finiteDimensional S
  markedRealization :=
    every_finiteSpectralScreen_has_markedRenewalRealization S
  preservesDomain := diracSpectralScreen_mem_domain S
  commutesDirac := diracSpectralScreen_commutes_dirac S
  projectionsStrong := tendsto_diracSpectralScreen_apply S
  compressionsStrong := tendsto_finiteSpectralCompression_apply S
  matrixCoefficientsStrong :=
    tendsto_finiteSpectralCompression_matrixCoefficient S
  productDefectsStrong :=
    tendsto_finiteSpectralCompression_multiplicativityDefect_apply S

end NCG.CompactResolventStrongCofinalMarkedRenewalLimitExact
