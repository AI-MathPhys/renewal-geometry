/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BoundedOperatorGraphKernel
import NCG.Grand.JointCommutatorCofinalMoscoFromOneStrongResolvent
import NCG.Grand.JointCommutatorMoscoKernelSpectralConsequences

/-!
# Joint-commutator spectrum from one resolvent and graph screens

For a bounded continuum commutator, cofinal convergence at one positive shift
and compact graph screens produce the full kernel spectral package.  Mosco
convergence and all finite and continuum weak equations are generated
internally, and the Riesz range is stated as the ordinary kernel of the limit
operator.
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

/-- Cofinal one-shift convergence and compact graph screens give the complete
kernel Riesz package for the limiting bounded commutator. -/
theorem jointCommutator_kernelSpectralConsequences_of_oneStrongResolvent_of_graphScreens
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
    (hdense : J.IsAsymptoticallyDense)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hT0 : ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop →
      (J.reindex φ).StrongOperatorConverges (J.reindex φ)
        (fun cutoff ↦
          NCG.jointCommutatorResolventFamily c lam0 (φ cutoff))
        (T lam0))
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
  have hmoscoEnergy :=
    J.jointCommutatorEnergy_cofinalMoscoConverges_of_oneStrongResolvent
      c A T hdense lam0 hlam0 hT0 hlimitNormal
  have hmoscoGraph : J.CofinalMoscoConverges
      (fun cutoff ↦ ennrealOperatorGraphEnergy
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff))))
      (ennrealOperatorGraphEnergy (⊤ : Submodule ℂ H)
        (boundedOperatorGraphMap A)) := by
    simpa only [ennrealOperatorGraphEnergy_top] using hmoscoEnergy
  have hresult :=
    J.jointCommutatorMosco_kernelSpectralConsequences_of_graphScreens
      c L (⊤ : Submodule ℂ H) (boundedOperatorGraphMap A) T
      hmoscoGraph
      (fun lam hlam f ↦
        boundedOperatorGraph_resolventEquation_of_normalEquation
          A lam f (T lam f) (hlimitNormal lam hlam f))
      a ha screen hcompact htail hfst hdense b hb v vlim hv
  simpa only [operatorGraphKernel_top_boundedOperatorGraphMap] using hresult

end NCG.VaryingHilbert.System
