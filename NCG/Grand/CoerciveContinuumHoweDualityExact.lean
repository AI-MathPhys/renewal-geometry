/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ContinuumHoweProtectedCommutantExact
import NCG.Grand.JointCommutatorFirstPositiveEigenvalueConvergenceFromDenseSourcesAndGraphScreens
import NCG.Grand.ConvergentSpectralGapCoercivity
import NCG.Grand.SMSTContinuumHoweExact

/-!
# Coercive continuum Howe duality

This file assembles the exact generator-level form of
`thm:SMST-continuum-Howe`.  The varying-Hilbert Mosco/compact-screen compiler
provides kernel and spectral stability; the protected-kernel theorem identifies
the stabilized space with the literal screened matrix commutant; and positivity
of the limiting gap supplies one uniform half-gap and the no-soft-mode
consequence for every cutoffwise spectral-floor realization.
-/

open Complex Filter Set Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- **Coercive continuum Howe duality, exact generator form.**  The first
Riesz circle records norm convergence of the protected commutant projections;
the second records the convergent attained positive cutoff gap.  The two
circles need not be chosen identically, since both isolate the same protected
zero-mode multiplicity and their numerical radii are auxiliary. -/
theorem coerciveContinuumHoweDuality_exact
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : NCG.VaryingHilbert.System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (L : NCG.VaryingHilbert.System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun cutoff ↦ WithLp 2
        (EuclideanSpace ℂ (d cutoff × d cutoff) ×
          EuclideanSpace ℂ (Fin s × (d cutoff × d cutoff)))))
    (A : H →L[ℂ] F)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff, EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ y ∈ D, J.StronglyConverges (source y) y)
    (hcore : ∀ y ∈ D, J.StronglyConverges
      (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam0 cutoff
        (source y cutoff))
      (boundedOperatorNormalResolventFamily A lam0 y))
    (a : ℝ) (ha : 0 < a)
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (hcompact : ∀ cutoff, IsCompactOperator (screen cutoff))
    (htail : ∀ ε > 0, ∃ screenIndex, ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
        (NCG.jointCommutatorResolventFamily c a cutoff) a ha
        (NCG.jointCommutatorResolventFamily_resolventEquation c a ha cutoff)),
      ‖y - screen screenIndex y‖ < ε)
    (hfst : ∀ cutoff y, J.embedding cutoff y.fst = (L.embedding cutoff y).fst)
    (b : ℝ) (hb : 0 < b)
    (P : ℕ → H →L[ℂ] H)
    (hprotected : ∀ᶠ cutoff in atTop,
      LinearMap.range (P cutoff).toLinearMap ≤
        (LinearMap.ker (NCG.jointCommutatorCLM (c cutoff)).toLinearMap).map
          (J.embedding cutoff).toLinearMap)
    (hprotectedRank : ∀ᶠ cutoff in atTop,
      Module.finrank ℂ (LinearMap.range (P cutoff).toLinearMap) =
        Module.finrank ℂ (LinearMap.ker A.toLinearMap))
    (hstarP : ∀ᶠ cutoff in atTop, IsStarProjection (P cutoff))
    (hinfinite : ¬FiniteDimensional ℂ H) :
    ∃ (projectionRadius gapRadius μlim : ℝ),
      0 < projectionRadius ∧
      (0 : ℂ) ∉ Metric.closedBall (((1 / b : ℝ) : ℂ)) projectionRadius ∧
      Tendsto P atTop
        (nhds (NCG.ResolventStability.circleRieszProjection
          (boundedOperatorNormalResolventFamily A b)
          (((1 / b : ℝ) : ℂ)) projectionRadius)) ∧
      (∀ᶠ cutoff in atTop,
        LinearMap.range (P cutoff).toLinearMap =
          (LinearMap.ker (NCG.jointCommutatorCLM (c cutoff)).toLinearMap).map
            (J.embedding cutoff).toLinearMap) ∧
      (∀ᶠ cutoff in atTop,
        ∀ X : Matrix (d cutoff) (d cutoff) ℂ,
          J.embedding cutoff (NCG.matrixL2 X) ∈
              LinearMap.range (P cutoff).toLinearMap ↔
            ∀ j, c cutoff j * X = X * c cutoff j) ∧
      0 < gapRadius ∧
      (0 : ℂ) ∉ Metric.closedBall (((1 / b : ℝ) : ℂ)) gapRadius ∧
      0 < μlim ∧
      Tendsto
        (fun cutoff ↦
          ‖NCG.SpectralGap.complementCompression
            (J.compressedOperator (NCG.jointCommutatorResolventFamily c b) cutoff)
            (P cutoff)‖⁻¹ - b)
        atTop (nhds μlim) ∧
      (∀ᶠ cutoff in atTop,
        let μ := ‖NCG.SpectralGap.complementCompression
          (J.compressedOperator (NCG.jointCommutatorResolventFamily c b) cutoff)
          (P cutoff)‖⁻¹ - b
        0 < μ ∧
          Module.End.HasEigenvalue
            (NCG.commutantLaplacianCLM (c cutoff)).toLinearMap (μ : ℂ) ∧
          ∀ ν : ℝ, 0 < ν →
            Module.End.HasEigenvalue
              (NCG.commutantLaplacianCLM (c cutoff)).toLinearMap (ν : ℂ) → μ ≤ ν) ∧
      0 < μlim / 2 ∧
      (∀ᶠ cutoff in atTop,
        μlim / 2 ≤
          ‖NCG.SpectralGap.complementCompression
            (J.compressedOperator (NCG.jointCommutatorResolventFamily c b) cutoff)
            (P cutoff)‖⁻¹ - b) ∧
      ∀ (energy residual : ℕ → H → ℝ),
        (∀ cutoff x, 0 ≤ residual cutoff x) →
        (∀ cutoff x,
          (‖NCG.SpectralGap.complementCompression
            (J.compressedOperator (NCG.jointCommutatorResolventFamily c b) cutoff)
            (P cutoff)‖⁻¹ - b) * residual cutoff x ≤ energy cutoff x) →
        (∀ᶠ cutoff in atTop, ∀ x,
          μlim / 2 * residual cutoff x ≤ energy cutoff x) ∧
        ∀ xseq : ℕ → H,
          Tendsto (fun cutoff ↦ energy cutoff (xseq cutoff)) atTop (nhds 0) →
            Tendsto (fun cutoff ↦ residual cutoff (xseq cutoff)) atTop (nhds 0) := by
  obtain ⟨projectionRadius, hProjectionRadius, hProjectionZero, hPconv,
    hKernel, hCommutant⟩ :=
    J.jointCommutator_protectedCommutant_tendsto_of_denseSources_of_graphScreens
      c L A lam0 hlam0 D hD source hsource hcore a ha screen hcompact htail hfst
        b hb P hprotected hprotectedRank hstarP
  obtain ⟨gapRadius, μlim, hGapRadius, hGapZero, hμlim, _hKernelAgain,
    hGap, hLeast⟩ :=
    J.jointCommutator_firstPositiveEigenvalue_tendsto_of_denseSources_of_graphScreens
      c L A lam0 hlam0 D hD source hsource hcore a ha screen hcompact htail hfst
        b hb P hprotected hprotectedRank hstarP hinfinite
  let gap : ℕ → ℝ := fun cutoff ↦
    ‖NCG.SpectralGap.complementCompression
      (J.compressedOperator (NCG.jointCommutatorResolventFamily c b) cutoff)
      (P cutoff)‖⁻¹ - b
  have hhalf : 0 < μlim / 2 := half_pos hμlim
  have hUniformGap : ∀ᶠ cutoff in atTop, μlim / 2 ≤ gap cutoff := by
    have hstrict : μlim / 2 < μlim := by linarith
    exact (hGap.eventually (Ioi_mem_nhds hstrict)).mono fun _ h ↦ h.le
  refine ⟨projectionRadius, gapRadius, μlim, hProjectionRadius, hProjectionZero,
    hPconv, hKernel, hCommutant, hGapRadius, hGapZero, hμlim, hGap, hLeast,
    hhalf, ?_, ?_⟩
  · simpa only [gap] using hUniformGap
  · intro energy residual hResidual hCoercive
    have hCoercive' : ∀ cutoff x, gap cutoff * residual cutoff x ≤ energy cutoff x := by
      simpa only [gap] using hCoercive
    constructor
    · exact NCG.SpectralGap.eventually_uniform_coercivity_of_gap_tendsto
        energy residual gap μlim hResidual hCoercive' hGap hμlim |>.2
    · intro xseq hEnergy
      exact NCG.SpectralGap.residual_tendsto_zero_of_gap_tendsto
        energy residual xseq gap μlim hResidual hCoercive' hGap hμlim hEnergy

end NCG.VaryingHilbert.System
