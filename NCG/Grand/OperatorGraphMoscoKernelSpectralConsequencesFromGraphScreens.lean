/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphResolventGraphScreen
import NCG.Grand.OperatorGraphMoscoKernelSpectralConsequencesFromWeakEquations

/-!
# Kernel spectral consequences directly from compact graph screens

The manuscript-style compact graph-screen tail is converted internally into
collective compactness of one positive-shift resolvent family.  Combined with
graph Mosco convergence and weak resolvent equations, this yields the complete
automatic kernel Riesz package.
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
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
variable {Hn : ℕ → Type w} {Fn : ℕ → Type z}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, InnerProductSpace ℝ (Hn n)] [∀ n, IsScalarTower ℝ ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace ℂ (Fn n)]
  [∀ n, NormedSpace ℝ (Fn n)] [∀ n, IsScalarTower ℝ ℂ (Fn n)]

/-- Graph Mosco convergence, weak resolvent equations, asymptotic density, and
a compact screen tail for the canonical graph outputs give the complete
automatic kernel Riesz package. -/
theorem operatorGraphMosco_kernelSpectralConsequences_of_graphScreens
    {iota : Type x}
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
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
    (a : ℝ) (ha : 0 < a)
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (hcompact : ∀ cutoff, IsCompactOperator (screen cutoff))
    (htail : ∀ ε > 0, ∃ cutoff, ∀ y ∈ L.embeddedUnitBallOutputs
      (fun n ↦ operatorGraphResolventHilbertGraph
        (Dn n) (An n) (Rn a n) a ha (hstageEquation a ha n)),
      ‖y - screen cutoff y‖ < ε)
    (hfst : ∀ n y, J.embedding n y.fst = (L.embedding n y).fst)
    (hdense : J.IsAsymptoticallyDense)
    (b : ℝ) (hb : 0 < b)
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
  have haCollectivelyCompact : J.CollectivelyCompact (Rn a) :=
    J.operatorGraphResolvent_collectivelyCompact_of_graphScreenTails
      L Dn An (Rn a) a ha (hstageEquation a ha) screen
        hcompact htail hfst
  exact J.operatorGraphMosco_kernelSpectralConsequences_of_weakEquations
    Dn An D A Rn R hmosco hstageEquation hlimitEquation
      a ha hdense haCollectivelyCompact b hb v vlim hv

end NCG.VaryingHilbert.System
