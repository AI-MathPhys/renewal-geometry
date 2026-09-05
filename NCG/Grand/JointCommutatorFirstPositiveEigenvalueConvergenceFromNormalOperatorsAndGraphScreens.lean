/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorDenseCoreConvergenceFromResidual
import NCG.Grand.JointCommutatorFirstPositiveEigenvalueConvergenceFromDenseSourcesAndGraphScreens

/-!
# Howe eigenvalue convergence from normal operators and graph screens

Strong convergence of the literal cutoff commutant Laplacians supplies the dense-core resolvent
premise automatically.  This module composes that fact with the protected-kernel and numerical
graph-screen compiler, leaving only a raw normal-operator limit and the compact-screen tail.
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

/-- Raw strong convergence of the cutoff commutant Laplacians plus compact graph screens proves
convergence of their attained first positive eigenvalues to a positive continuum Howe gap. -/
theorem jointCommutator_firstPositiveEigenvalue_tendsto_of_normalOperatorConvergence_of_graphScreens
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun cutoff ↦ WithLp 2
        (EuclideanSpace ℂ (d cutoff × d cutoff) ×
          EuclideanSpace ℂ (Fin s × (d cutoff × d cutoff)))))
    (A : H →L[ℂ] F)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff, EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ y ∈ D, J.StronglyConverges (source y) y)
    (hnormal : J.StrongOperatorConverges J
      (fun cutoff ↦ NCG.commutantLaplacianCLM (c cutoff))
      ((ContinuousLinearMap.adjoint A).comp A))
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
    ∃ (radius μlim : ℝ), 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall (((1 / b : ℝ) : ℂ)) radius ∧
      0 < μlim ∧
      (∀ᶠ cutoff in atTop,
        LinearMap.range (P cutoff).toLinearMap =
          (LinearMap.ker (NCG.jointCommutatorCLM (c cutoff)).toLinearMap).map
            (J.embedding cutoff).toLinearMap) ∧
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
              (NCG.commutantLaplacianCLM (c cutoff)).toLinearMap (ν : ℂ) → μ ≤ ν) := by
  have hcore : ∀ y ∈ D, J.StronglyConverges
      (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam0 cutoff
        (source y cutoff))
      (boundedOperatorNormalResolventFamily A lam0 y) :=
    J.jointCommutator_denseCoreConvergence_of_commutantLaplacianStrongConvergence
      c A lam0 hlam0 D hD source hsource hnormal
  exact J.jointCommutator_firstPositiveEigenvalue_tendsto_of_denseSources_of_graphScreens
    c L A lam0 hlam0 D hD source hsource hcore a ha screen hcompact htail hfst
      b hb P hprotected hprotectedRank hstarP hinfinite

end NCG.VaryingHilbert.System
