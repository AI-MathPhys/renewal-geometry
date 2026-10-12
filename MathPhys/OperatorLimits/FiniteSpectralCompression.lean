/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import MathPhys.OperatorLimits.CompactResolventSpectralProjectionTransferExact

open MathPhys
/-!
# Finite spectral compressions of bounded operators

Split out of `MathPhys.OperatorLimits.CompactResolventStrongCofinalMarkedRenewalLimitExact`:
for a compact-resolvent spectral triple, the two-sided compression of a bounded operator by
the finite resolvent screens (`finiteSpectralCompression`) recovers it strongly
(`tendsto_finiteSpectralCompression_apply`), together with every matrix coefficient, every
product of two operators, and the vanishing of multiplicativity defects in the strong
topology.
-/

open Complex Filter Module Set Topology

noncomputable section

namespace MathPhys.CompactResolventStrongCofinalMarkedRenewalLimitExact

universe u

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

open MathPhys.CompactResolventDiracSpectralScreensExact
open MathPhys.CompactResolventSpectralProjectionTransferExact

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

end MathPhys.CompactResolventStrongCofinalMarkedRenewalLimitExact
