/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphMoscoSpectralConsequencesAutomaticCircle
import NCG.Grand.OperatorGraphResolventEigenspace

/-!
# Graph-Mosco kernel spectral consequences

At positive shift `b`, the kernel of a graph operator is the `b⁻¹`-eigenspace of its bounded
resolvent.  The automatic compact-symmetric Riesz circle around that canonical center therefore
has range exactly equal to the limiting graph kernel.  No center, radius, gap, or endpoint input
remains in this specialization.
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

/-- Graph Mosco convergence, weak resolvent equations, and collective compactness at one shift
give an automatically selected Riesz projection whose limiting range is exactly the limiting
graph-operator kernel, together with operator-norm, rank, and source-Gram convergence. -/
theorem operatorGraphMosco_kernelSpectralConsequences
    {ι : Type x}
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
    (hsymm : ∀ b, 0 < b → ∀ n,
      LinearMap.IsSymmetric (Rn b n).toLinearMap)
    (hlimSymm : ∀ b, 0 < b → LinearMap.IsSymmetric (R b).toLinearMap)
    (b : ℝ) (hbPos : 0 < b)
    (v : ℕ → ι → H) (vlim : ι → H)
    (hv : ∀ i, Tendsto (fun n ↦ v n i) atTop (𝓝 (vlim i))) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall (((1 / b : ℝ) : ℂ)) radius ∧
      (∀ z ∈ Metric.sphere (((1 / b : ℝ) : ℂ)) radius,
        z ∈ resolventSet ℂ (R b)) ∧
      IsCompactOperator (R b) ∧
      LinearMap.range
          (NCG.ResolventStability.circleRieszProjection
            (R b) (((1 / b : ℝ) : ℂ)) radius).toLinearMap =
        operatorGraphKernel D A ∧
      Tendsto (J.compressedOperator (Rn b)) atTop (𝓝 (R b)) ∧
      Tendsto
        (fun n ↦ NCG.ResolventStability.circleRieszProjection
          (J.compressedOperator (Rn b) n) (((1 / b : ℝ) : ℂ)) radius) atTop
        (𝓝 (NCG.ResolventStability.circleRieszProjection
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
        (𝓝 (NCG.SpectralApproximation.sourceGram
          (NCG.ResolventStability.circleRieszProjection
            (R b) (((1 / b : ℝ) : ℂ)) radius) vlim)) := by
  have hbNe : b ≠ 0 := ne_of_gt hbPos
  have hcenter : (((1 / b : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast one_div_ne_zero hbNe
  obtain ⟨radius, hR, hzero, hcontour, hcompact, hRangeEig,
      hop, hproj, hrank, hgram⟩ :=
    J.operatorGraphMosco_spectralConsequences_automaticCircle
      Dn An D A Rn R hmosco hstageEquation hlimitEquation a haPos hdense
        haCompact hsymm hlimSymm b hbPos (1 / b) hcenter v vlim hv
  have hRangeKernel :
      LinearMap.range
          (NCG.ResolventStability.circleRieszProjection
            (R b) (((1 / b : ℝ) : ℂ)) radius).toLinearMap =
        operatorGraphKernel D A := by
    rw [hRangeEig]
    simpa [one_div] using
      (operatorGraphKernel_eq_resolventEigenspace
        D A b hbPos (R b) (hlimitEquation b hbPos)).symm
  exact ⟨radius, hR, hzero, hcontour, hcompact, hRangeKernel,
    hop, hproj, hrank, hgram⟩

end NCG.VaryingHilbert.System
