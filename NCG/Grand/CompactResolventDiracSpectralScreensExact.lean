/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.SpectralTriple.Basic
import NCG.Grand.CompactNormalFiniteSpectralScreensExact

/-!
# Finite Dirac screens from a compact normal resolvent

The eigenspace screens of the compact normal resolvent `(D - i)⁻¹` are
finite-rank orthogonal projections converging strongly to the identity.  The
two inverse identities transfer commutation with the resolvent to exact
domain preservation and commutation with the unbounded Dirac operator.
-/

open Complex Filter Module Set Topology

noncomputable section

namespace NCG.CompactResolventDiracSpectralScreensExact

universe u

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

open NCG.CompactNormalFiniteSpectralScreensExact

/-- A two-sided resolvent is injective. -/
theorem resolvent_injective (S : SpectralTriple A H) :
    Function.Injective S.resolvent := by
  intro x y hxy
  have hsub :
      (⟨S.resolvent x, S.resolvent_mem_domain x⟩ : S.dirac.domain) =
        ⟨S.resolvent y, S.resolvent_mem_domain y⟩ :=
    Subtype.ext hxy
  calc
    x = S.dirac ⟨S.resolvent x, S.resolvent_mem_domain x⟩ -
        Complex.I • S.resolvent x := (S.resolvent_right_inverse x).symm
    _ = S.dirac ⟨S.resolvent y, S.resolvent_mem_domain y⟩ -
        Complex.I • S.resolvent y := by rw [hsub, hxy]
    _ = y := S.resolvent_right_inverse y

/-- The finite spectral projection obtained from a finite set of resolvent
eigenvalues. -/
def diracSpectralScreen (S : SpectralTriple A H) (s : Finset ℂ) :
    H →L[ℂ] H :=
  spectralScreen S.resolvent S.resolvent_isCompact
    (resolvent_injective S) s

theorem diracSpectralScreen_isSymmetricProjection
    (S : SpectralTriple A H) (s : Finset ℂ) :
    (diracSpectralScreen S s).IsSymmetricProjection :=
  spectralScreen_isSymmetricProjection S.resolvent S.resolvent_isCompact
    (resolvent_injective S) s

theorem diracSpectralScreen_range_finiteDimensional
    (S : SpectralTriple A H) (s : Finset ℂ) :
    FiniteDimensional ℂ
      (LinearMap.range (diracSpectralScreen S s).toLinearMap) :=
  spectralScreen_range_finiteDimensional S.resolvent S.resolvent_isCompact
    (resolvent_injective S) s

theorem diracSpectralScreen_commutes_resolvent
    (S : SpectralTriple A H) (s : Finset ℂ) :
    Commute S.resolvent (diracSpectralScreen S s) :=
  spectralScreen_commutes S.resolvent S.resolvent_isCompact
    S.resolvent_isStarNormal (resolvent_injective S) s

/-- Every resolvent eigenspace lies in the Dirac domain.  Injectivity excludes
the zero eigenspace; for a nonzero eigenvalue, the vector is a scalar multiple
of a resolvent output. -/
theorem resolventEigenspace_le_diracDomain
    (S : SpectralTriple A H) (μ : ℂ) :
    Module.End.eigenspace S.resolvent.toLinearMap μ ≤ S.dirac.domain := by
  intro x hx
  by_cases hμ : μ = 0
  · subst μ
    have hxker : S.resolvent x = 0 := by
      simpa using Module.End.mem_eigenspace_iff.mp hx
    have hx0 : x = 0 := (resolvent_injective S) (by simpa using hxker)
    simpa [hx0]
  · have heig : S.resolvent x = μ • x :=
      Module.End.mem_eigenspace_iff.mp hx
    have hmux : μ • x ∈ S.dirac.domain := by
      rw [← heig]
      exact S.resolvent_mem_domain x
    have hscale := S.dirac.domain.smul_mem (μ⁻¹) hmux
    simpa [inv_smul_smul₀ hμ] using hscale

/-- The whole range of a finite resolvent spectral screen lies in the domain
of the unbounded Dirac operator. -/
theorem diracSpectralScreen_range_le_domain
    (S : SpectralTriple A H) (s : Finset ℂ) :
    LinearMap.range (diracSpectralScreen S s).toLinearMap ≤
      S.dirac.domain := by
  change LinearMap.range
      (spectralScreen S.resolvent S.resolvent_isCompact
        (resolvent_injective S) s).toLinearMap ≤ S.dirac.domain
  rw [spectralScreen_range S.resolvent S.resolvent_isCompact
    (resolvent_injective S) s]
  exact Finset.sup_le fun μ _ => resolventEigenspace_le_diracDomain S μ

/-- Every resolvent spectral screen preserves the domain of `D`. -/
theorem diracSpectralScreen_mem_domain
    (S : SpectralTriple A H) (s : Finset ℂ) (x : S.dirac.domain) :
    diracSpectralScreen S s (x : H) ∈ S.dirac.domain := by
  let P := diracSpectralScreen S s
  let y : H := S.dirac x - Complex.I • (x : H)
  have hleft : S.resolvent y = (x : H) := S.resolvent_left_inverse x
  have hcomm := diracSpectralScreen_commutes_resolvent S s
  have hcommApply : S.resolvent (P y) = P (S.resolvent y) := by
    simpa [P, ContinuousLinearMap.mul_apply] using
      congrArg (fun T : H →L[ℂ] H => T y) hcomm.eq
  have hPx : P (x : H) = S.resolvent (P y) := by
    rw [← hleft, hcommApply]
  rw [hPx]
  exact S.resolvent_mem_domain (P y)

/-- The finite resolvent screens commute exactly with the unbounded Dirac
operator on its domain. -/
theorem diracSpectralScreen_commutes_dirac
    (S : SpectralTriple A H) (s : Finset ℂ) (x : S.dirac.domain) :
    S.dirac ⟨diracSpectralScreen S s (x : H),
        diracSpectralScreen_mem_domain S s x⟩ =
      diracSpectralScreen S s (S.dirac x) := by
  let P := diracSpectralScreen S s
  let y : H := S.dirac x - Complex.I • (x : H)
  have hleft : S.resolvent y = (x : H) := S.resolvent_left_inverse x
  have hcomm := diracSpectralScreen_commutes_resolvent S s
  have hcommApply : S.resolvent (P y) = P (S.resolvent y) := by
    simpa [P, ContinuousLinearMap.mul_apply] using
      congrArg (fun T : H →L[ℂ] H => T y) hcomm.eq
  have hPx : P (x : H) = S.resolvent (P y) := by
    rw [← hleft, hcommApply]
  have hsub :
      (⟨P (x : H), diracSpectralScreen_mem_domain S s x⟩ :
          S.dirac.domain) =
        ⟨S.resolvent (P y), S.resolvent_mem_domain (P y)⟩ :=
    Subtype.ext hPx
  have hright := S.resolvent_right_inverse (P y)
  rw [← hsub] at hright
  rw [← hPx] at hright
  change S.dirac ⟨P (x : H), diracSpectralScreen_mem_domain S s x⟩ -
      Complex.I • P (x : H) =
    P (S.dirac x - Complex.I • (x : H)) at hright
  rw [map_sub, map_smul] at hright
  exact sub_left_inj.mp hright

theorem tendsto_diracSpectralScreen_apply
    (S : SpectralTriple A H) (x : H) :
    Tendsto (fun s : Finset ℂ => diracSpectralScreen S s x)
      atTop (𝓝 x) :=
  tendsto_spectralScreen_apply S.resolvent S.resolvent_isCompact
    S.resolvent_isStarNormal (resolvent_injective S) x

/-- A compact-resolvent spectral triple admits cofinal finite-rank orthogonal
Dirac screens which preserve the domain, commute with `D`, and converge
strongly to the identity. -/
theorem compactResolventSpectralTriple_has_cofinal_finiteDiracScreens
    (S : SpectralTriple A H) :
    (∀ s, (diracSpectralScreen S s).IsSymmetricProjection) ∧
    (∀ s, FiniteDimensional ℂ
      (LinearMap.range (diracSpectralScreen S s).toLinearMap)) ∧
    (∀ s (x : S.dirac.domain),
      diracSpectralScreen S s (x : H) ∈ S.dirac.domain) ∧
    (∀ s (x : S.dirac.domain),
      S.dirac ⟨diracSpectralScreen S s (x : H),
          diracSpectralScreen_mem_domain S s x⟩ =
        diracSpectralScreen S s (S.dirac x)) ∧
    (∀ x, Tendsto (fun s : Finset ℂ => diracSpectralScreen S s x)
      atTop (𝓝 x)) := by
  exact ⟨diracSpectralScreen_isSymmetricProjection S,
    diracSpectralScreen_range_finiteDimensional S,
    diracSpectralScreen_mem_domain S,
    diracSpectralScreen_commutes_dirac S,
    tendsto_diracSpectralScreen_apply S⟩

end NCG.CompactResolventDiracSpectralScreensExact
