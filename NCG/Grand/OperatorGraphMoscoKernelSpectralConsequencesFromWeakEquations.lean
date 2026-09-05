/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphMoscoKernelSpectralConsequences
import NCG.Grand.OperatorGraphResolventDenseRange

/-!
# Graph-kernel spectral consequences directly from weak equations

The weak graph-resolvent equations already force every stage and limit resolvent to be symmetric.
This wrapper removes those redundant hypotheses from the automatic compact/Riesz kernel compiler.
-/

open Complex Filter Set Topology
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w x z

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type z} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
variable {Hn : ℕ → Type w} {Fn : ℕ → Type z}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, InnerProductSpace ℝ (Hn n)] [∀ n, IsScalarTower ℝ ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace ℂ (Fn n)]
  [∀ n, NormedSpace ℝ (Fn n)] [∀ n, IsScalarTower ℝ ℂ (Fn n)]

/-- Graph Mosco convergence, weak resolvent equations, asymptotic density, and collective
compactness at one shift give the complete automatic kernel Riesz package.  Symmetry of all
resolvents is derived internally from the weak equations. -/
theorem operatorGraphMosco_kernelSpectralConsequences_of_weakEquations
    {iota : Type x}
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Dn : ∀ n, Submodule ℂ (Hn n))
    (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] F)
    (Rn : ℝ → ∀ n, Hn n →L[ℂ] Hn n) (R : ℝ → H →L[ℂ] H)
    (hmosco : J.CofinalMoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A))
    (hstageEquation : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Rn lam n f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (a : ℝ) (haPos : 0 < a)
    (hdense : J.IsAsymptoticallyDense)
    (haCompact : J.CollectivelyCompact (Rn a))
    (b : ℝ) (hbPos : 0 < b)
    (v : ℕ → iota → H) (vlim : iota → H)
    (hv : ∀ i, Tendsto (fun n ↦ v n i) atTop (nhds (vlim i))) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall (((1 / b : ℝ) : ℂ)) radius ∧
      (∀ z ∈ Metric.sphere (((1 / b : ℝ) : ℂ)) radius,
        z ∈ resolventSet ℂ (R b)) ∧
      IsCompactOperator (R b) ∧
      LinearMap.range
          (NCG.ResolventStability.circleRieszProjection
            (R b) (((1 / b : ℝ) : ℂ)) radius).toLinearMap =
        operatorGraphKernel D A ∧
      Tendsto (J.compressedOperator (Rn b)) atTop (nhds (R b)) ∧
      Tendsto
        (fun n ↦ NCG.ResolventStability.circleRieszProjection
          (J.compressedOperator (Rn b) n) (((1 / b : ℝ) : ℂ)) radius) atTop
        (nhds (NCG.ResolventStability.circleRieszProjection
          (R b) (((1 / b : ℝ) : ℂ)) radius)) ∧
      (∀ᶠ n in atTop,
        Module.finrank ℂ
            (LinearMap.range
              (NCG.ResolventStability.circleRieszProjection
                (J.compressedOperator (Rn b) n)
                  (((1 / b : ℝ) : ℂ)) radius).toLinearMap) =
          Module.finrank ℂ
            (LinearMap.range
              (NCG.ResolventStability.circleRieszProjection
                (R b) (((1 / b : ℝ) : ℂ)) radius).toLinearMap)) ∧
      Tendsto
        (fun n ↦ NCG.SpectralApproximation.sourceGram
          (NCG.ResolventStability.circleRieszProjection
            (J.compressedOperator (Rn b) n)
              (((1 / b : ℝ) : ℂ)) radius) (v n)) atTop
        (nhds (NCG.SpectralApproximation.sourceGram
          (NCG.ResolventStability.circleRieszProjection
            (R b) (((1 / b : ℝ) : ℂ)) radius) vlim)) := by
  apply J.operatorGraphMosco_kernelSpectralConsequences
    Dn An D A Rn R hmosco hstageEquation hlimitEquation a haPos hdense haCompact
  · intro c hc n
    exact operatorGraphResolvent_isSymmetric
      (Dn n) (An n) c (Rn c n) (hstageEquation c hc n)
  · intro c hc
    exact operatorGraphResolvent_isSymmetric
      D A c (R c) (hlimitEquation c hc)
  · exact hbPos
  · exact hv

end NCG.VaryingHilbert.System
