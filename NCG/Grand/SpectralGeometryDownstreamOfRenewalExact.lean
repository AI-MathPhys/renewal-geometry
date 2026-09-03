/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SpectralizationEssentialImageTrichotomyExact

/-!
# Spectral geometry downstream of Renewal geometry

This is the precise typed corollary of the essential-image trichotomy.  It
retains strong marked essential surjectivity and the proper strict selection
rule, while deliberately containing no assertion that a single fixed austere
Renewal source realizes every target.
-/

open Complex Filter

noncomputable section

namespace NCG.SpectralGeometryDownstreamOfRenewalExact

universe u v

open NCG.CompactResolventStrongCofinalMarkedRenewalLimitExact
open NCG.SpectralizationEssentialImageTrichotomyExact

/-- The formal content of spectral geometry being downstream of Renewal
geometry in the marked strong category, but selected in the strict category. -/
structure DownstreamMeaningCertificate
    {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H]
    (S : SpectralTriple A H)
    {B : Type u} [CStarAlgebra B] {X : Type v}
    (P : X → B) (l : Filter X) : Prop where
  strongMarkedPreimage : StrongCofinalMarkedRenewalLimit S
  strictSelection : StrictNormMonoidalImageCertificate P l
  strictSelectionProper : ToeplitzStrongNotStrictCertificate

/-- Precise downstream-meaning corollary: every compact-resolvent target has
a strong cofinal marked preimage, whereas strict norm-monoidality is the proper
quasidiagonal selection rule. -/
theorem spectralGeometry_is_downstream_of_Renewal
    {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H]
    (S : SpectralTriple A H)
    {B : Type u} [CStarAlgebra B] {X : Type v}
    (P : X → B) (l : Filter X)
    (hP : ∀ n, P n * P n = P n)
    (hPstar : ∀ n, star (P n) = P n) :
    DownstreamMeaningCertificate S P l where
  strongMarkedPreimage :=
    every_compactResolventSpectralTriple_is_strongCofinalMarkedRenewalLimit S
  strictSelection := {
    idempotent := hP
    selfAdjoint := hPstar
    criterion :=
      NCG.SpectralCompression.normMultiplicativeAlong_iff_quasidiagonalAlong
        P l hP hPstar
    compressionDefect := fun n a b =>
      NCG.SpectralCompression.compress_mul_sub_mul_compress
        (P n) a b (hP n) }
  strictSelectionProper := toeplitz_strong_not_strict

end NCG.SpectralGeometryDownstreamOfRenewalExact
