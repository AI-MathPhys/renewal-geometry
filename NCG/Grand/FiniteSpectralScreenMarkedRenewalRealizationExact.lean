/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactResolventDiracSpectralScreensExact
import NCG.Grand.CoordinateFiniteSpectralPacketMarkedRenewalRealizationExact
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Marked realizations of compact-resolvent finite spectral screens

Each finite resolvent eigenspace screen is made into an exact finite spectral
packet.  Its represented coefficients are orthogonal compressions, while its
Dirac operator is the exact restriction of the ambient unbounded operator.
A canonical orthonormal basis converts these endomorphisms to matrices, so
the arbitrary finite marked-realization theorem applies to the actual screen.
-/

open Complex Filter Module Set Topology

noncomputable section

namespace NCG.FiniteSpectralScreenMarkedRenewalRealizationExact

universe u

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

open NCG.CompactResolventDiracSpectralScreensExact
open NCG.CoordinateFiniteSpectralPacketMarkedRenewalRealizationExact

abbrev ScreenSpace (S : SpectralTriple A H) (s : Finset ℂ) :=
  LinearMap.range (diracSpectralScreen S s).toLinearMap

noncomputable instance screenSpaceFiniteDimensional
    (S : SpectralTriple A H) (s : Finset ℂ) :
    FiniteDimensional ℂ (ScreenSpace S s) :=
  diracSpectralScreen_range_finiteDimensional S s

/-- A symmetric spectral projection fixes every vector in its range. -/
theorem diracSpectralScreen_apply_screenVector
    (S : SpectralTriple A H) (s : Finset ℂ) (x : ScreenSpace S s) :
    diracSpectralScreen S s (x : H) = x := by
  let P := diracSpectralScreen S s
  obtain ⟨y, hy⟩ := x.property
  have hidem : IsIdempotentElem (diracSpectralScreen S s).toLinearMap :=
    (diracSpectralScreen_isSymmetricProjection S s).isIdempotentElem
  change P (x : H) = (x : H)
  rw [← hy]
  change P.toLinearMap (P.toLinearMap y) = P.toLinearMap y
  rw [← Module.End.mul_apply]
  rw [show IsIdempotentElem P.toLinearMap by simpa [P] using hidem]

/-- Orthogonal compression of one represented coefficient to a finite
spectral screen. -/
def compressedRepresentationEndomorphism
    (S : SpectralTriple A H) (s : Finset ℂ) (a : A) :
    ScreenSpace S s →ₗ[ℂ] ScreenSpace S s where
  toFun x := ⟨diracSpectralScreen S s (S.rep a (x : H)),
    ⟨S.rep a (x : H), rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' z x := by
    apply Subtype.ext
    simp

/-- The inclusion of a spectral screen into the domain of the ambient
unbounded Dirac operator. -/
def screenToDiracDomain (S : SpectralTriple A H) (s : Finset ℂ) :
    ScreenSpace S s →ₗ[ℂ] S.dirac.domain where
  toFun x := ⟨x, diracSpectralScreen_range_le_domain S s x.property⟩
  map_add' x y := rfl
  map_smul' z x := rfl

/-- The ambient Dirac applied to a finite-screen vector. -/
def screenDiracAmbient (S : SpectralTriple A H) (s : Finset ℂ) :
    ScreenSpace S s →ₗ[ℂ] H :=
  S.dirac.toFun.comp (screenToDiracDomain S s)

theorem screenDiracAmbient_mem_screen
    (S : SpectralTriple A H) (s : Finset ℂ) (x : ScreenSpace S s) :
    screenDiracAmbient S s x ∈ ScreenSpace S s := by
  let P := diracSpectralScreen S s
  let xd : S.dirac.domain := screenToDiracDomain S s x
  have hfix : P (x : H) = x :=
    diracSpectralScreen_apply_screenVector S s x
  have hsub :
      (⟨P (xd : H), diracSpectralScreen_mem_domain S s xd⟩ :
          S.dirac.domain) = xd := by
    apply Subtype.ext
    simpa [xd, screenToDiracDomain] using hfix
  have hcomm := diracSpectralScreen_commutes_dirac S s xd
  rw [hsub] at hcomm
  refine ⟨screenDiracAmbient S s x, ?_⟩
  simpa [P, screenDiracAmbient, xd] using hcomm.symm

/-- Exact finite-dimensional restriction of the ambient Dirac operator. -/
def screenDiracEndomorphism (S : SpectralTriple A H) (s : Finset ℂ) :
    ScreenSpace S s →ₗ[ℂ] ScreenSpace S s :=
  (screenDiracAmbient S s).codRestrict (ScreenSpace S s)
    (screenDiracAmbient_mem_screen S s)

theorem screenDiracEndomorphism_isSymmetric
    (S : SpectralTriple A H) (s : Finset ℂ) :
    (screenDiracEndomorphism S s).IsSymmetric := by
  intro x y
  simpa [screenDiracEndomorphism, screenDiracAmbient,
    screenToDiracDomain] using
    S.symmetric (screenToDiracDomain S s x) (screenToDiracDomain S s y)

/-- Canonical orthonormal coordinates on a finite spectral screen. -/
def screenOrthonormalBasis (S : SpectralTriple A H) (s : Finset ℂ) :
    OrthonormalBasis (Fin (Module.finrank ℂ (ScreenSpace S s))) ℂ
      (ScreenSpace S s) :=
  stdOrthonormalBasis ℂ (ScreenSpace S s)

/-- The actual compressed finite spectral packet on a resolvent screen. -/
def screenPacket (S : SpectralTriple A H) (s : Finset ℂ) :
    CoordinateFiniteSpectralPacket A
      (Fin (Module.finrank ℂ (ScreenSpace S s))) where
  representation a := LinearMap.toMatrixOrthonormal
    (screenOrthonormalBasis S s)
    (compressedRepresentationEndomorphism S s a)
  dirac := LinearMap.toMatrixOrthonormal (screenOrthonormalBasis S s)
    (screenDiracEndomorphism S s)
  dirac_isHermitian := by
    change Matrix.conjTranspose (LinearMap.toMatrix
      (screenOrthonormalBasis S s).toBasis
      (screenOrthonormalBasis S s).toBasis
      (screenDiracEndomorphism S s)) =
      LinearMap.toMatrix (screenOrthonormalBasis S s).toBasis
        (screenOrthonormalBasis S s).toBasis
        (screenDiracEndomorphism S s)
    rw [← LinearMap.toMatrix_adjoint]
    rw [(screenDiracEndomorphism_isSymmetric S s).adjoint_eq]

/-- Every finite spectral screen of a compact-resolvent spectral triple has
an exact finite marked Renewal realization. -/
theorem every_finiteSpectralScreen_has_markedRenewalRealization
    (S : SpectralTriple A H) (s : Finset ℂ) :
    Nonempty (MarkedRenewalRealization (screenPacket S s)) :=
  every_finiteSpectralPacket_has_finiteMarkedRenewalRealization
    (screenPacket S s)

end NCG.FiniteSpectralScreenMarkedRenewalRealizationExact
