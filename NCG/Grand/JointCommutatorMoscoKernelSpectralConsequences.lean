/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorResolventFamily
import NCG.Grand.OperatorGraphMoscoKernelSpectralConsequencesFromGraphScreens

/-!
# Kernel spectral consequences for joint-commutator cutoffs

This model-facing theorem feeds the canonical finite joint-commutator graph
operators and resolvents into the compact graph-screen spectral compiler.  It
removes every finite-stage resolvent equation from the hypotheses and returns
the continuum kernel Riesz projection, norm convergence, eventual rank
stability, and convergence of all prescribed source Gram matrices.
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

/-- Compact graph screens and graph Mosco convergence for the finite joint
commutator energies imply the complete automatic kernel spectral package. -/
theorem jointCommutatorMosco_kernelSpectralConsequences_of_graphScreens
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    {iota : Type x}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun cutoff ↦ WithLp 2
        (EuclideanSpace ℂ (d cutoff × d cutoff) ×
          EuclideanSpace ℂ (Fin s × (d cutoff × d cutoff)))))
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] F)
    (R : ℝ → H →L[ℂ] H)
    (hmosco : J.CofinalMoscoConverges
      (fun cutoff ↦ ennrealOperatorGraphEnergy
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff))))
      (ennrealOperatorGraphEnergy D A))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f))
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
    (hdense : J.IsAsymptoticallyDense)
    (b : ℝ) (hb : 0 < b)
    (v : ℕ → iota → H) (vlim : iota → H)
    (hv : ∀ i, Tendsto (fun cutoff ↦ v cutoff i) atTop (nhds (vlim i))) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall (((1 / b : ℝ) : ℂ)) radius ∧
      (∀ z ∈ Metric.sphere (((1 / b : ℝ) : ℂ)) radius,
        z ∈ resolventSet ℂ (R b)) ∧
      IsCompactOperator (R b) ∧
      LinearMap.range
          (NCG.ResolventStability.circleRieszProjection
            (R b) (((1 / b : ℝ) : ℂ)) radius).toLinearMap =
        operatorGraphKernel D A ∧
      Tendsto
        (J.compressedOperator (NCG.jointCommutatorResolventFamily c b))
        atTop (nhds (R b)) ∧
      Tendsto
        (fun cutoff ↦ NCG.ResolventStability.circleRieszProjection
          (J.compressedOperator
            (NCG.jointCommutatorResolventFamily c b) cutoff)
          (((1 / b : ℝ) : ℂ)) radius) atTop
        (nhds (NCG.ResolventStability.circleRieszProjection
          (R b) (((1 / b : ℝ) : ℂ)) radius)) ∧
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
                (R b) (((1 / b : ℝ) : ℂ)) radius).toLinearMap)) ∧
      Tendsto
        (fun cutoff ↦ NCG.SpectralApproximation.sourceGram
          (NCG.ResolventStability.circleRieszProjection
            (J.compressedOperator
              (NCG.jointCommutatorResolventFamily c b) cutoff)
            (((1 / b : ℝ) : ℂ)) radius) (v cutoff)) atTop
        (nhds (NCG.SpectralApproximation.sourceGram
          (NCG.ResolventStability.circleRieszProjection
            (R b) (((1 / b : ℝ) : ℂ)) radius) vlim)) := by
  exact J.operatorGraphMosco_kernelSpectralConsequences_of_graphScreens
    L
    (fun cutoff ↦
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff))))
    (fun cutoff ↦ boundedOperatorGraphMap
      (NCG.jointCommutatorCLM (c cutoff)))
    D A (NCG.jointCommutatorResolventFamily c) R hmosco
    (fun lam hlam cutoff f ↦
      NCG.jointCommutatorResolventFamily_resolventEquation
        c lam hlam cutoff f)
    hlimitEquation a ha screen hcompact htail hfst hdense b hb v vlim hv

end NCG.VaryingHilbert.System
