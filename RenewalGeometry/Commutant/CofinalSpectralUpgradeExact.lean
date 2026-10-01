/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Commutant.CoerciveContinuumHoweDualityExact
/-!
# Compact spectral upgrade

Covers `cor:cofinal-spectral-upgrade` of the spacetime–gauge duality paper, in the
varying-Hilbert graph-screen rendering of `coerciveContinuumHoweDuality_exact`.

`protectedGap` is the attained first positive eigenvalue `λ_{m+1}(𝓛_X)` of the cutoff
commutant Laplacian (the least positive eigenvalue clause of the parent theorem).
`cofinalSpectralUpgrade_exact` re-exports the parent's clauses — norm convergence of the
transported kernel projections `Π_X → Π_∞`, eventual identification of their ranges with
the joint-commutator kernels, a strictly positive limit gap `γ_∞ = μlim` with
`λ_{m+1}(𝓛_X) → γ_∞` (`eq:cofinal-spectral-upgrade`) — and adds the two clauses of the
corollary that the parent does not display:

* `eq:limit-gap`: `γ_∞ ≥ γ_*` under the rendering of the uniform late-cutoff gap (D3) of
  `thm:cofinal-duality` as `γ_* ≤ λ_{m+1}(𝓛_X)` for all late cutoffs (at a finite cutoff
  with `Ker 𝓛_X = M_X`, `q_X(A) ≥ γ_* ‖(I − P_{M_X})A‖²` for all `A` is exactly this
  eigenvalue bound);
* `eq:cofinal-coercivity` for **every** `0 < γ_0 < γ_∞`: for all late cutoffs and every
  energy/residual pair dominated by the cutoff gap, `energy ≥ γ_0 · residual`.
-/

open Complex Filter Set Topology

noncomputable section

namespace RenewalGeometry.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- The attained first positive eigenvalue `λ_{m+1}(𝓛_X)` of the cutoff commutant
Laplacian, read off the complement-compressed transported resolvent at shift `b`. -/
def protectedGap {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : RenewalGeometry.VaryingHilbert.System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (b : ℝ) (P : ℕ → H →L[ℂ] H) (cutoff : ℕ) : ℝ :=
  ‖RenewalGeometry.SpectralGap.complementCompression
    (J.compressedOperator (RenewalGeometry.jointCommutatorResolventFamily c b) cutoff)
    (P cutoff)‖⁻¹ - b

/-- **Compact spectral upgrade (`cor:cofinal-spectral-upgrade`), graph-screen rendering.**
Beyond the parent clauses (projection convergence `Π_X → Π_∞`, eventual kernel
identification, positive limit gap `γ_∞`, `λ_{m+1}(𝓛_X) → γ_∞`, least-positive-eigenvalue
identification), the limit gap dominates the uniform late-cutoff constant `γ_*` of (D3)
(`eq:limit-gap`), and for every `0 < γ_0 < γ_∞` the coercivity `eq:cofinal-coercivity`
holds at all sufficiently late cutoffs. -/
theorem cofinalSpectralUpgrade_exact
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : RenewalGeometry.VaryingHilbert.System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (L : RenewalGeometry.VaryingHilbert.System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun cutoff ↦ WithLp 2
        (EuclideanSpace ℂ (d cutoff × d cutoff) ×
          EuclideanSpace ℂ (Fin s × (d cutoff × d cutoff)))))
    (A : H →L[ℂ] F)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff, EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ y ∈ D, J.StronglyConverges (source y) y)
    (hcore : ∀ y ∈ D, J.StronglyConverges
      (fun cutoff ↦ RenewalGeometry.jointCommutatorResolventFamily c lam0 cutoff
        (source y cutoff))
      (boundedOperatorNormalResolventFamily A lam0 y))
    (a : ℝ) (ha : 0 < a)
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (hcompact : ∀ cutoff, IsCompactOperator (screen cutoff))
    (htail : ∀ ε > 0, ∃ screenIndex, ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (RenewalGeometry.jointCommutatorCLM (c cutoff)))
        (RenewalGeometry.jointCommutatorResolventFamily c a cutoff) a ha
        (RenewalGeometry.jointCommutatorResolventFamily_resolventEquation c a ha cutoff)),
      ‖y - screen screenIndex y‖ < ε)
    (hfst : ∀ cutoff y, J.embedding cutoff y.fst = (L.embedding cutoff y).fst)
    (b : ℝ) (hb : 0 < b)
    (P : ℕ → H →L[ℂ] H)
    (hprotected : ∀ᶠ cutoff in atTop,
      LinearMap.range (P cutoff).toLinearMap ≤
        (LinearMap.ker (RenewalGeometry.jointCommutatorCLM (c cutoff)).toLinearMap).map
          (J.embedding cutoff).toLinearMap)
    (hprotectedRank : ∀ᶠ cutoff in atTop,
      Module.finrank ℂ (LinearMap.range (P cutoff).toLinearMap) =
        Module.finrank ℂ (LinearMap.ker A.toLinearMap))
    (hstarP : ∀ᶠ cutoff in atTop, IsStarProjection (P cutoff))
    (hinfinite : ¬FiniteDimensional ℂ H)
    (γstar : ℝ)
    (hD3 : ∀ᶠ cutoff in atTop, γstar ≤ protectedGap c J b P cutoff) :
    ∃ (projectionRadius gapRadius μlim : ℝ),
      0 < projectionRadius ∧
      (0 : ℂ) ∉ Metric.closedBall (((1 / b : ℝ) : ℂ)) projectionRadius ∧
      Tendsto P atTop
        (nhds (RenewalGeometry.ResolventStability.circleRieszProjection
          (boundedOperatorNormalResolventFamily A b)
          (((1 / b : ℝ) : ℂ)) projectionRadius)) ∧
      (∀ᶠ cutoff in atTop,
        LinearMap.range (P cutoff).toLinearMap =
          (LinearMap.ker (RenewalGeometry.jointCommutatorCLM (c cutoff)).toLinearMap).map
            (J.embedding cutoff).toLinearMap) ∧
      0 < gapRadius ∧
      (0 : ℂ) ∉ Metric.closedBall (((1 / b : ℝ) : ℂ)) gapRadius ∧
      0 < μlim ∧
      Tendsto (protectedGap c J b P) atTop (nhds μlim) ∧
      (∀ᶠ cutoff in atTop,
        0 < protectedGap c J b P cutoff ∧
          Module.End.HasEigenvalue
            (RenewalGeometry.commutantLaplacianCLM (c cutoff)).toLinearMap
            ((protectedGap c J b P cutoff : ℝ) : ℂ) ∧
          ∀ ν : ℝ, 0 < ν →
            Module.End.HasEigenvalue
              (RenewalGeometry.commutantLaplacianCLM (c cutoff)).toLinearMap (ν : ℂ) →
              protectedGap c J b P cutoff ≤ ν) ∧
      γstar ≤ μlim ∧
      ∀ γ0 : ℝ, 0 < γ0 → γ0 < μlim →
        ∀ (energy residual : ℕ → H → ℝ),
          (∀ cutoff x, 0 ≤ residual cutoff x) →
          (∀ cutoff x, protectedGap c J b P cutoff * residual cutoff x ≤ energy cutoff x) →
          ∀ᶠ cutoff in atTop, ∀ x, γ0 * residual cutoff x ≤ energy cutoff x := by
  obtain ⟨projectionRadius, gapRadius, μlim, hProjectionRadius, hProjectionZero, hPconv,
    hKernel, _hCommutant, hGapRadius, hGapZero, hμlim, hGap, hLeast, _hhalf, _hUniform,
    _hcoercive⟩ :=
    J.coerciveContinuumHoweDuality_exact c L A lam0 hlam0 D hD source hsource hcore a ha
      screen hcompact htail hfst b hb P hprotected hprotectedRank hstarP hinfinite
  have hGap' : Tendsto (protectedGap c J b P) atTop (nhds μlim) := hGap
  refine ⟨projectionRadius, gapRadius, μlim, hProjectionRadius, hProjectionZero, hPconv,
    hKernel, hGapRadius, hGapZero, hμlim, hGap', ?_, ?_, ?_⟩
  · exact hLeast
  · exact ge_of_tendsto hGap' hD3
  · intro γ0 _ hγ0 energy residual hResidual hCoercive
    filter_upwards [hGap'.eventually (Ioi_mem_nhds hγ0)] with cutoff hcut
    intro x
    exact (mul_le_mul_of_nonneg_right hcut.le (hResidual cutoff x)).trans
      (hCoercive cutoff x)

end RenewalGeometry.VaryingHilbert.System
