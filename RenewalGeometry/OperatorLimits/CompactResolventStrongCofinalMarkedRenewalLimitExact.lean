/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Spectralization.FiniteSpectralScreenMarkedRenewalRealizationExact
import MathPhys.NCG.OperatorLimits.CompactResolventSpectralProjectionTransferExact
import MathPhys.NCG.OperatorLimits.FiniteSpectralCompression

open MathPhys
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

namespace RenewalGeometry.CompactResolventStrongCofinalMarkedRenewalLimitExact
open MathPhys.CompactResolventStrongCofinalMarkedRenewalLimitExact

universe u

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

open MathPhys.CompactResolventDiracSpectralScreensExact
open MathPhys.CompactResolventSpectralProjectionTransferExact
open RenewalGeometry.CoordinateFiniteSpectralPacketMarkedRenewalRealizationExact
open RenewalGeometry.FiniteSpectralScreenMarkedRenewalRealizationExact

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

end RenewalGeometry.CompactResolventStrongCofinalMarkedRenewalLimitExact
