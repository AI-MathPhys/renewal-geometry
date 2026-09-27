/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.OperatorLimits.OperatorGraphMoscoKernelSpectralConsequencesFromGraphScreens
import RenewalGeometry.OperatorLimits.OperatorGraphResolventPositivity
import RenewalGeometry.OperatorLimits.LowSpectrumConvergence

/-!
# Compact Mosco convergence: norm-resolvent convergence and low-spectrum convergence

This file closes `prop:compact-mosco-resolvent` of the spacetime–gauge duality paper.

Under cofinal Mosco convergence of the operator-graph energies with weak resolvent equations,
asymptotic density, and a compact graph-screen tail (the rendering of asymptotic form
compactness), the graph-screen kernel package
`operatorGraphMosco_kernelSpectralConsequences_of_graphScreens` already provides operator-norm
convergence of the transported resolvents `‖R_X - R_∞‖ → 0`, compactness of `R_∞`, and the
norm convergence and eventual rank equality of the kernel-cluster Riesz projections.  Here the
package is completed by the **ordered eigenvalue convergence**: the limiting resolvent is
positive, its ordered eigenvalues `μ_{k,∞}` (Courant–Fischer values, which by
`orderedEigenvalues_spec_of_compact_isPositive` are the positive eigenvalues repeated with
multiplicity) are the limits of the stage values `μ_{k,X}`, and the screened eigenvalues
`λ_{k,X} = 1/μ_{k,X} - b → λ_{k,∞}` for every index with `μ_{k,∞} > 0`.
-/

open Complex Filter Set Topology
open scoped ENNReal
open RenewalGeometry.LowSpectrum

noncomputable section

namespace RenewalGeometry.VaryingHilbert.System

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

/-- **Compact Mosco convergence implies norm-resolvent convergence and low-spectrum
convergence** (`prop:compact-mosco-resolvent`).  Graph Mosco convergence, weak resolvent
equations, asymptotic density, and a compact screen tail for the canonical graph outputs give:
the transported resolvents converge in operator norm to the compact positive limit resolvent
`R b`; the kernel-cluster Riesz projections converge in norm with eventually equal ranks; and for
every fixed index `k` the ordered eigenvalues converge, `μ_{k,X} → μ_{k,∞}`, hence
`λ_{k,X} = 1/μ_{k,X} - b → λ_{k,∞}` whenever the limiting eigenvalue is finite
(`0 < μ_{k,∞}`). -/
theorem operatorGraphMosco_lowSpectrumConvergence_of_graphScreens
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
      (R b).IsPositive ∧
      LinearMap.range
          (RenewalGeometry.ResolventStability.circleRieszProjection
            (R b) (((1 / b : ℝ) : ℂ)) radius).toLinearMap =
        operatorGraphKernel D A ∧
      Tendsto (J.compressedOperator (Rn b)) atTop (nhds (R b)) ∧
      Tendsto
        (fun n ↦ RenewalGeometry.ResolventStability.circleRieszProjection
          (J.compressedOperator (Rn b) n) (((1 / b : ℝ) : ℂ)) radius) atTop
        (nhds (RenewalGeometry.ResolventStability.circleRieszProjection
          (R b) (((1 / b : ℝ) : ℂ)) radius)) ∧
      (∀ᶠ n in atTop,
        Module.finrank ℂ
            (LinearMap.range
              (RenewalGeometry.ResolventStability.circleRieszProjection
                (J.compressedOperator (Rn b) n)
                  (((1 / b : ℝ) : ℂ)) radius).toLinearMap) =
          Module.finrank ℂ
            (LinearMap.range
              (RenewalGeometry.ResolventStability.circleRieszProjection
                (R b) (((1 / b : ℝ) : ℂ)) radius).toLinearMap)) ∧
      Tendsto
        (fun n ↦ RenewalGeometry.SpectralApproximation.sourceGram
          (RenewalGeometry.ResolventStability.circleRieszProjection
            (J.compressedOperator (Rn b) n)
              (((1 / b : ℝ) : ℂ)) radius) (v n)) atTop
        (nhds (RenewalGeometry.SpectralApproximation.sourceGram
          (RenewalGeometry.ResolventStability.circleRieszProjection
            (R b) (((1 / b : ℝ) : ℂ)) radius) vlim)) ∧
      (∀ k : ℕ, Tendsto (fun n ↦ orderedEigenvalue (J.compressedOperator (Rn b) n) k) atTop
        (nhds (orderedEigenvalue (R b) k))) ∧
      (∀ k : ℕ, 0 < orderedEigenvalue (R b) k →
        Tendsto (fun n ↦ (orderedEigenvalue (J.compressedOperator (Rn b) n) k)⁻¹ - b) atTop
          (nhds ((orderedEigenvalue (R b) k)⁻¹ - b))) := by
  obtain ⟨radius, hradius, hzero, hcontour, hcompactR, hrange, hconv, hproj, hrank, hgram⟩ :=
    J.operatorGraphMosco_kernelSpectralConsequences_of_graphScreens L Dn An D A Rn R hmosco
      hstageEquation hlimitEquation a ha screen hcompact htail hfst hdense b hb v vlim hv
  have hposR : (R b).IsPositive :=
    operatorGraphResolvent_isPositive D A b hb.le (R b) (hlimitEquation b hb)
  exact ⟨radius, hradius, hzero, hcontour, hcompactR, hposR, hrange, hconv, hproj, hrank, hgram,
    fun k ↦ tendsto_orderedEigenvalue hconv k,
    fun k hk ↦ tendsto_shiftedInverse_orderedEigenvalue hconv b k hk⟩

end RenewalGeometry.VaryingHilbert.System
