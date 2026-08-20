/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BoundedOperatorNormalResolventFamily
import NCG.Grand.JointCommutatorKernelSpectralConsequencesFromDenseSourcesAndGraphScreens

/-!
# Bounded continuum kernel spectrum from dense sources and graph screens

The continuum resolvents are the canonical inverses of `A† A + λ I`.  Thus
dense-core convergence of one finite resolvent shift and compact graph screens
give the complete kernel Riesz package with no separately supplied continuum
resolvent or normal-equation hypotheses.
-/

open Complex Filter Set Topology
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v x

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- Dense-core convergence to the canonical bounded normal resolvent and
compact graph screens imply the complete limiting kernel spectral package. -/
theorem jointCommutator_boundedKernelSpectralConsequences_of_denseSources_of_graphScreens
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    {iota : Type x}
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
        (NCG.jointCommutatorResolventFamily_resolventEquation
          c a ha cutoff)),
      ‖y - screen screenIndex y‖ < ε)
    (hfst : ∀ cutoff y, J.embedding cutoff y.fst =
      (L.embedding cutoff y).fst)
    (b : ℝ) (hb : 0 < b)
    (v : ℕ → iota → H) (vlim : iota → H)
    (hv : ∀ i, Tendsto (fun cutoff ↦ v cutoff i) atTop (nhds (vlim i))) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall (((1 / b : ℝ) : ℂ)) radius ∧
      (∀ z ∈ Metric.sphere (((1 / b : ℝ) : ℂ)) radius,
        z ∈ resolventSet ℂ (boundedOperatorNormalResolventFamily A b)) ∧
      IsCompactOperator (boundedOperatorNormalResolventFamily A b) ∧
      LinearMap.range
          (NCG.ResolventStability.circleRieszProjection
            (boundedOperatorNormalResolventFamily A b)
            (((1 / b : ℝ) : ℂ)) radius).toLinearMap =
        LinearMap.ker A.toLinearMap ∧
      Tendsto
        (J.compressedOperator (NCG.jointCommutatorResolventFamily c b))
        atTop (nhds (boundedOperatorNormalResolventFamily A b)) ∧
      Tendsto
        (fun cutoff ↦ NCG.ResolventStability.circleRieszProjection
          (J.compressedOperator
            (NCG.jointCommutatorResolventFamily c b) cutoff)
          (((1 / b : ℝ) : ℂ)) radius) atTop
        (nhds (NCG.ResolventStability.circleRieszProjection
          (boundedOperatorNormalResolventFamily A b)
          (((1 / b : ℝ) : ℂ)) radius)) ∧
      (∀ᶠ cutoff in atTop,
        Module.finrank ℂ
            (LinearMap.range
              (NCG.ResolventStability.circleRieszProjection
                (J.compressedOperator
                  (NCG.jointCommutatorResolventFamily c b) cutoff)
                (((1 / b : ℝ) : ℂ)) radius).toLinearMap) =
          Module.finrank ℂ
            (LinearMap.range
              (NCG.ResolventStability.circleRieszProjection
                (boundedOperatorNormalResolventFamily A b)
                (((1 / b : ℝ) : ℂ)) radius).toLinearMap)) ∧
      Tendsto
        (fun cutoff ↦ NCG.SpectralApproximation.sourceGram
          (NCG.ResolventStability.circleRieszProjection
            (J.compressedOperator
              (NCG.jointCommutatorResolventFamily c b) cutoff)
            (((1 / b : ℝ) : ℂ)) radius) (v cutoff)) atTop
        (nhds (NCG.SpectralApproximation.sourceGram
          (NCG.ResolventStability.circleRieszProjection
            (boundedOperatorNormalResolventFamily A b)
            (((1 / b : ℝ) : ℂ)) radius) vlim)) := by
  exact J.jointCommutator_kernelSpectralConsequences_of_denseSources_of_graphScreens
    c L A (boundedOperatorNormalResolventFamily A)
    lam0 hlam0 D hD source hsource hcore
    (boundedOperatorNormalResolventFamily_normalEquation A)
    a ha screen hcompact htail hfst b hb v vlim hv

end NCG.VaryingHilbert.System
