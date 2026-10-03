/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Spectralization.FiniteHodgeDiracDatumExact
import RenewalGeometry.Spectralization.EssentialImageReconstructionExact
/-!
# Finite Hodge--Dirac reconstruction and commutant coordinates (`thm:summary-finite`)

Re-assembly of `thm:summary-finite` of `predictive_spectral_geometry` from the
datum-level results of `FiniteHodgeDiracDatumExact`:

* (i) every finite real differential datum `(A, τ, δ)` determines the real even
  KO-dimension-`0` Hodge--Dirac triple `Packet.ofDatum` (all packet laws derived), functorially
  under trace- and differential-preserving `*`-isomorphisms (`DatumIso`,
  `ofDatumTransport`, with identity and composition laws);
* (ii) the algebra and trace do not determine the Dirac scale (`no_scale`:
  `δ ↦ s δ` keeps `(A, τ)` and gives `D ↦ s D ≠ D` for `δ ≠ 0`, `s ≠ 1`), and a fixed
  commutator derivation determines the compatible Dirac operator exactly modulo `c_S`;
* (iii) the marked commutant coordinates and essential images
  (`EssentialImageReconstruction.summary_finite_marked`).
-/

open Matrix CategoryTheory
open scoped Matrix.Norms.L2Operator

namespace RenewalGeometry
namespace FiniteHodgeDiracSummary

open FiniteRealEvenSpectralizationExact FiniteRealEvenSpectralizationExact.Packet
  FiniteHodgeDiracDatum AustereUnitZeroMode FiniteSpectralizationFunctorScaleExact
  EssentialImageReconstruction ReconstructionCategories MarkedCommutantCoordinates
  SpectralCompressionsSequential ToeplitzScreenObstruction

noncomputable section

section Predicate

variable {A I J : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
  [StarModule ℂ A] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The axioms of a real even finite spectral triple of KO-dimension `0`, in
coordinates (`thm:finite-Hodge-Dirac`): faithful `π`, `D = D^*`, the grading
axioms, antiunitary `J` with `J² = I`, `JD = DJ`, `Jγ = γJ`, the opposite
representation, order zero and first order. -/
def IsRealEvenKO0Triple (P : FiniteRealEvenSpectralizationExact.Packet (A := A) (I := I) (J := J)) :
    Prop :=
  Function.Injective P.representation ∧ P.dirac.IsHermitian ∧
  P.grading.IsHermitian ∧ P.grading * P.grading = 1 ∧
  (∀ a, P.grading * P.representation a = P.representation a * P.grading) ∧
  P.dirac * P.grading + P.grading * P.dirac = 0 ∧
  P.realMatrixᴴ * P.realMatrix = 1 ∧ P.realMatrix * P.realMatrix.map star = 1 ∧
  P.realMatrix * P.dirac.map star = P.dirac * P.realMatrix ∧
  P.realMatrix * P.grading.map star = P.grading * P.realMatrix ∧
  (∀ b, P.realMatrix * (P.representation (star b)).map star * P.realMatrix.map star =
    P.oppositeRepresentation b) ∧
  (∀ a b, P.commutator (P.representation a) (P.oppositeRepresentation b) = 0) ∧
  (∀ a b, P.commutator (P.commutator P.dirac (P.representation a))
    (P.oppositeRepresentation b) = 0)

end Predicate

variable {n n' : ℕ} {A A' K K' : Type*}
  [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [StarModule ℂ A] [FiniteDimensional ℂ A]
  [NormedRing A'] [NormedAlgebra ℂ A'] [StarRing A'] [StarModule ℂ A'] [FiniteDimensional ℂ A']
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
  {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Every datum determines a real even KO-dimension-`0` triple. -/
theorem ofDatum_isRealEvenKO0Triple (D : FiniteRealDifferentialDatum n A K)
    (τ : FaithfulTracialState A) (b₀ : OrthonormalBasis I ℂ (TracialL2 τ))
    (b₁ : OrthonormalBasis J ℂ D.sourceMinimalCarrier) :
    IsRealEvenKO0Triple (ofDatum D τ b₀ b₁) := by
  obtain ⟨h1, h2, ⟨h3, h4, h5, h6⟩, h7, h8, h9, h10, h11, h12, h13, -⟩ :=
    finite_hodge_dirac D τ b₀ b₁
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- **`thm:summary-finite`.**

* (i) For every finite real differential datum `D` on `(A, τ)` (and orthonormal bases of
  `H₀ = L²(A, τ)` and `H₁(δ)`) the Hodge packet `ofDatum D τ b₀ b₁` is a real even
  KO-dimension-`0` finite spectral triple; every trace- and differential-preserving
  `*`-isomorphism `F` to another datum induces a unitary intertwining `π`, `D`, `γ`, `J`
  and `π°`, and these unitaries respect identity and composition.
* (ii) If `δ ≠ 0`, for every `s > 0`, `s ≠ 1`, the datum `s δ` on the same `(A, τ)` has
  Dirac operator `s D ≠ D` (so `A` and `τ` do not determine the scale); and for every marked
  finite triple a fixed commutator derivation determines the compatible Dirac operator
  exactly modulo `c_S`.
* (iii) `EssentialImageReconstruction.summary_finite_marked`: injective commutant
  coordinates with exactly `q_S` components, their sharpness, and the three essential images
  with Toeplitz strictness. -/
theorem summary_finite {ι : Type*} (D : FiniteRealDifferentialDatum n A K)
    (τ : FaithfulTracialState A) (b₀ : OrthonormalBasis I ℂ (TracialL2 τ))
    (b₁ : OrthonormalBasis J ℂ D.sourceMinimalCarrier) :
    -- (i) the Hodge triple
    IsRealEvenKO0Triple (ofDatum D τ b₀ b₁) ∧
    -- (i) functoriality
    (∀ (D' : FiniteRealDifferentialDatum n' A' K') (τ' : FaithfulTracialState A')
      (F : DatumIso D τ D' τ') (b₀' : OrthonormalBasis I ℂ (TracialL2 τ'))
      (b₁' : OrthonormalBasis J ℂ D'.sourceMinimalCarrier),
      (ofDatumTransport F b₀ b₁ b₀' b₁').unitaryᴴ * (ofDatumTransport F b₀ b₁ b₀' b₁').unitary
        = 1 ∧
      (∀ a, (ofDatumTransport F b₀ b₁ b₀' b₁').unitary * (ofDatum D τ b₀ b₁).representation a =
        (ofDatum D' τ' b₀' b₁').representation (F.alg a) *
          (ofDatumTransport F b₀ b₁ b₀' b₁').unitary) ∧
      (ofDatumTransport F b₀ b₁ b₀' b₁').unitary * (ofDatum D τ b₀ b₁).dirac =
        (ofDatum D' τ' b₀' b₁').dirac * (ofDatumTransport F b₀ b₁ b₀' b₁').unitary ∧
      (ofDatumTransport F b₀ b₁ b₀' b₁').unitary * (ofDatum D τ b₀ b₁).grading =
        (ofDatum D' τ' b₀' b₁').grading * (ofDatumTransport F b₀ b₁ b₀' b₁').unitary ∧
      (ofDatumTransport F b₀ b₁ b₀' b₁').unitary * (ofDatum D τ b₀ b₁).realMatrix =
        (ofDatum D' τ' b₀' b₁').realMatrix *
          (ofDatumTransport F b₀ b₁ b₀' b₁').unitary.map star ∧
      (∀ a, (ofDatumTransport F b₀ b₁ b₀' b₁').unitary *
          (ofDatum D τ b₀ b₁).oppositeRepresentation a =
        (ofDatum D' τ' b₀' b₁').oppositeRepresentation (F.alg a) *
          (ofDatumTransport F b₀ b₁ b₀' b₁').unitary)) ∧
    (ofDatumTransport (DatumIso.refl D τ) b₀ b₁ b₀ b₁).U0 = 1 ∧
    (ofDatumTransport (DatumIso.refl D τ) b₀ b₁ b₀ b₁).U1 = 1 ∧
    -- (ii) no intrinsic scale
    (D.packet.delta ≠ 0 → ∀ (s : ℝ) (hs : 0 < s), s ≠ 1 →
      (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs.ne')).dirac =
        (s : ℂ) • (ofDatum D τ b₀ b₁).dirac ∧
      (ofDatum (D.scale s) τ b₀ (scaleBasis D b₁ hs.ne')).dirac ≠ (ofDatum D τ b₀ b₁).dirac) ∧
    -- (ii) commutant fibre and (iii)
    ((∀ (K : Type) [Fintype K] [DecidableEq K] (S : MarkedFiniteSpectralTriple A K ι)
      (X : Matrix K K ℂ),
      S.IsCompatibleImplementer X ↔ ∃ C ∈ S.commutantSpace, X = S.dirac + C) ∧
    (∀ (K : Type) [Fintype K] [DecidableEq K] (S : MarkedFiniteSpectralTriple A K ι),
      ∃ α : S.CommutantCoordinateMap S.commutantDim, Function.Injective α ∧
        ∀ S' : MarkedFiniteSpectralTriple A K ι, S.SameCommutatorData S' →
          α (S.commutantProjectionMem S'.dirac) = α (S.commutantProjectionMem S.dirac) →
            S' = S) ∧
    (∀ (K : Type) [Fintype K] [DecidableEq K] (S : MarkedFiniteSpectralTriple A K ι) (m : ℕ),
      m < S.commutantDim → ∀ α : S.CommutantCoordinateMap m,
        ∃ S' : MarkedFiniteSpectralTriple A K ι, S.SameCommutatorData S' ∧ S' ≠ S ∧
          α (S.commutantProjectionMem S'.dirac) = α (S.commutantProjectionMem S.dirac)) ∧
    (∀ S : FiniteMarkedObject A ι, (finiteReconstruction (A := A) (ι := ι)).essImage S) ∧
    (∀ X : CompactMarkedObject A ι, (strongReconstruction (A := A) (ι := ι)).essImage X) ∧
    (∀ X : CompactMarkedObject A ι, (normReconstruction (A := A) (ι := ι)).essImage X ↔
      SpectrallyQuasidiagonal X.triple.toSpectralTriple) ∧
    ((strongReconstruction (A := ToeplitzSmoothAlgebra) (ι := ι)).essImage (toeplitzObject ι) ∧
      ¬ (normReconstruction (A := ToeplitzSmoothAlgebra) (ι := ι)).essImage
        (toeplitzObject ι))) := by
  refine ⟨ofDatum_isRealEvenKO0Triple D τ b₀ b₁,
    fun D' τ' F b₀' b₁' => finite_hodge_dirac_functorial F b₀ b₁ b₀' b₁',
    (ofDatumTransport_refl b₀ b₁).1, (ofDatumTransport_refl b₀ b₁).2,
    fun hδ s hs hs1 => ⟨ofDatum_scale_dirac D τ b₀ b₁ hs.ne',
      ofDatum_scale_dirac_ne D τ b₀ b₁ hδ hs hs1⟩,
    summary_finite_marked⟩

end

end FiniteHodgeDiracSummary
end RenewalGeometry
