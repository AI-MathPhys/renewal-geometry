/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorKernelSpectralConsequencesFromOneStrongResolventAndGraphScreens
import NCG.Grand.JointCommutatorResolventDenseSourceConvergence
import NCG.Grand.VaryingHilbertAsymptoticDensityFromDenseSources

/-!
# Joint-commutator spectrum from dense sources and graph screens

Compatible lifts and resolvent convergence on a dense source set supply all
varying-Hilbert density and cofinal strong-convergence inputs.  Compact graph
screens then give the continuum kernel Riesz projection, norm convergence,
eventual rank stability, and source-Gram convergence.
-/

open Complex Filter Set Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v x

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- Dense-core convergence of one canonical resolvent and compact graph
screens imply the complete limiting kernel spectral package. -/
theorem jointCommutator_kernelSpectralConsequences_of_denseSources_of_graphScreens
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    {iota : Type x}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun cutoff ↦ WithLp 2
        (EuclideanSpace ℂ (d cutoff × d cutoff) ×
          EuclideanSpace ℂ (Fin s × (d cutoff × d cutoff)))))
    (A : H →L[ℂ] F) (T : ℝ → H →L[ℂ] H)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff, EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ y ∈ D, J.StronglyConverges (source y) y)
    (hcore : ∀ y ∈ D, J.StronglyConverges
      (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam0 cutoff
        (source y cutoff))
      (T lam0 y))
    (hlimitNormal : ∀ lam, 0 < lam → ∀ f : H,
      (A† ∘L A) (T lam f) + (lam : ℂ) • T lam f = f)
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
        z ∈ resolventSet ℂ (T b)) ∧
      IsCompactOperator (T b) ∧
      LinearMap.range
          (NCG.ResolventStability.circleRieszProjection
            (T b) (((1 / b : ℝ) : ℂ)) radius).toLinearMap =
        LinearMap.ker A.toLinearMap ∧
      Tendsto
        (J.compressedOperator (NCG.jointCommutatorResolventFamily c b))
        atTop (nhds (T b)) ∧
      Tendsto
        (fun cutoff ↦ NCG.ResolventStability.circleRieszProjection
          (J.compressedOperator
            (NCG.jointCommutatorResolventFamily c b) cutoff)
          (((1 / b : ℝ) : ℂ)) radius) atTop
        (nhds (NCG.ResolventStability.circleRieszProjection
          (T b) (((1 / b : ℝ) : ℂ)) radius)) ∧
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
                (T b) (((1 / b : ℝ) : ℂ)) radius).toLinearMap)) ∧
      Tendsto
        (fun cutoff ↦ NCG.SpectralApproximation.sourceGram
          (NCG.ResolventStability.circleRieszProjection
            (J.compressedOperator
              (NCG.jointCommutatorResolventFamily c b) cutoff)
            (((1 / b : ℝ) : ℂ)) radius) (v cutoff)) atTop
        (nhds (NCG.SpectralApproximation.sourceGram
          (NCG.ResolventStability.circleRieszProjection
            (T b) (((1 / b : ℝ) : ℂ)) radius) vlim)) := by
  have hdense := J.isAsymptoticallyDense_of_denseSources
    D hD source hsource
  have hT0 :=
    J.jointCommutatorResolvent_cofinalStrongOperatorConverges_of_denseSources
      c (T lam0) lam0 hlam0 D hD source hsource hcore
  exact
    J.jointCommutator_kernelSpectralConsequences_of_oneStrongResolvent_of_graphScreens
      c L A T hdense lam0 hlam0 hT0 hlimitNormal
      a ha screen hcompact htail hfst b hb v vlim hv

end NCG.VaryingHilbert.System
