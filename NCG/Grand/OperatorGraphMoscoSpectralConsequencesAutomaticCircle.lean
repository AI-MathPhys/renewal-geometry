/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphMoscoSpectralConsequences
import NCG.Grand.CompactSymmetricRieszEigenspace

/-!
# Graph-Mosco spectral consequences with automatic circles

The limit graph equation gives the second resolvent identity.  Compactness of one limiting
resolvent therefore propagates directly to every positive shift, where compact symmetric
spectral isolation chooses a Riesz circle automatically.  This removes the radius and endpoint
premises from the graph-Mosco spectral compiler.
-/

open Complex Filter Set Topology
open NCG.ResolventStability
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

/-- Cofinal Mosco convergence of squared operator graphs, weak resolvent equations, and
collective compactness at one shift automatically select an admissible real-centered Riesz
circle at every positive shift and yield all compact spectral-screen consequences. -/
theorem operatorGraphMosco_spectralConsequences_automaticCircle
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
    (center : ℝ) (hcenter : (center : ℂ) ≠ 0)
    (v : ℕ → ι → H) (vlim : ι → H)
    (hv : ∀ i, Tendsto (fun n ↦ v n i) atTop (𝓝 (vlim i))) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall (center : ℂ) radius ∧
      (∀ z ∈ Metric.sphere (center : ℂ) radius,
        z ∈ resolventSet ℂ (R b)) ∧
      IsCompactOperator (R b) ∧
      LinearMap.range
          (NCG.ResolventStability.circleRieszProjection
            (R b) (center : ℂ) radius).toLinearMap =
        Module.End.eigenspace (R b).toLinearMap (center : ℂ) ∧
      Tendsto (J.compressedOperator (Rn b)) atTop (𝓝 (R b)) ∧
      Tendsto
        (fun n ↦ NCG.ResolventStability.circleRieszProjection
          (J.compressedOperator (Rn b) n) (center : ℂ) radius) atTop
        (𝓝 (NCG.ResolventStability.circleRieszProjection
          (R b) (center : ℂ) radius)) ∧
      (∀ᶠ n in atTop,
        Module.finrank ℂ
            (LinearMap.range
              (NCG.ResolventStability.circleRieszProjection
                (J.compressedOperator (Rn b) n) (center : ℂ) radius).toLinearMap) =
          Module.finrank ℂ
            (LinearMap.range
              (NCG.ResolventStability.circleRieszProjection
                (R b) (center : ℂ) radius).toLinearMap)) ∧
      Tendsto
        (fun n ↦ NCG.SpectralApproximation.sourceGram
          (NCG.ResolventStability.circleRieszProjection
            (J.compressedOperator (Rn b) n) (center : ℂ) radius) (v n)) atTop
        (𝓝 (NCG.SpectralApproximation.sourceGram
          (NCG.ResolventStability.circleRieszProjection
            (R b) (center : ℂ) radius) vlim)) := by
  let q : H → ℝ≥0∞ := ennrealOperatorGraphEnergy D A
  have hlimitFinite : ∀ lam, 0 < lam → ∀ f : H,
      q (R lam f) ≠ ∞ := by
    intro lam hlam f
    simpa [q] using (hlimitEquation lam hlam f).mem
  have hlimitMin : ∀ lam, 0 < lam → ∀ (f z : H), q z ≠ ∞ →
      resolventObjective (K := ℂ) (fun w ↦ (q w).toReal) lam f (R lam f) ≤
        resolventObjective (K := ℂ) (fun w ↦ (q w).toReal) lam f z := by
    intro lam hlam f z hz
    apply operatorGraph_resolventObjective_minimizer
      D A lam hlam.le f (R lam f) (hlimitEquation lam hlam f) z
    simpa [q] using hz
  have hlimitConvex :
      ConvexOn ℝ {z : H | q z ≠ ∞} (fun z ↦ (q z).toReal) := by
    simpa [q] using convexOn_ennrealOperatorGraphEnergy D A
  have hlimitIdentity :
      R a - R b = ((b - a : ℝ) : ℂ) • ((R a).comp (R b)) :=
    realSecondResolventIdentity_of_convexMinimizers
      q R hlimitConvex hlimitFinite hlimitMin a b haPos hbPos
  have haStrong : J.StrongOperatorConverges J (Rn a) (R a) :=
    J.operatorGraphMosco_strongResolvents_allPositive
      Dn An D A Rn R hmosco hstageEquation hlimitEquation a haPos
  have haCompressedStrong : ∀ y : H,
      Tendsto (fun n ↦ J.compressedOperator (Rn a) n y) atTop (𝓝 (R a y)) :=
    J.compressedOperator_tendsto (Rn a) (R a) hdense haStrong
  have haCompressedCompact :
      (NCG.VaryingHilbert.constantSystem ℂ H).CollectivelyCompact
        (J.compressedOperator (Rn a)) :=
    haCompact.compressedOperator J (Rn a)
  have hRaCompact : IsCompactOperator (R a) :=
    haCompressedCompact.isCompactOperator_limit
      (J.compressedOperator (Rn a)) (R a) haCompressedStrong
  have hcomp : IsCompactOperator ((R a).comp (R b)) :=
    hRaCompact.comp_clm (R b)
  have hdiff : IsCompactOperator (R a - R b) := by
    rw [hlimitIdentity]
    exact hcomp.smul (((b - a : ℝ) : ℂ))
  have hRbCompact : IsCompactOperator (R b) := by
    have hrewrite : R b = R a - (R a - R b) := by abel
    rw [hrewrite]
    exact hRaCompact.sub hdiff
  obtain ⟨radius, hR, hzero, hcontour, hlimitRange⟩ :=
    exists_circleRieszProjection_range_eq_eigenspace_of_compact_of_isSymmetric
      (R b) hRbCompact (hlimSymm b hbPos) (center : ℂ) hcenter
  have hleftSphere : ((center - radius : ℝ) : ℂ) ∈
      Metric.sphere (center : ℂ) radius := by
    rw [Metric.mem_sphere, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
    have : center - radius - center = -radius := by ring
    rw [this, abs_neg, abs_of_pos hR]
  have hrightSphere : ((center + radius : ℝ) : ℂ) ∈
      Metric.sphere (center : ℂ) radius := by
    rw [Metric.mem_sphere, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
    have : center + radius - center = radius := by ring
    rw [this, abs_of_pos hR]
  have hleft := hcontour _ hleftSphere
  have hright := hcontour _ hrightSphere
  have hspectral := J.operatorGraphMosco_spectralConsequences
    Dn An D A Rn R hmosco hstageEquation hlimitEquation a haPos hdense
      haCompact hsymm hlimSymm b hbPos center radius hR hzero hleft hright
        v vlim hv
  exact ⟨radius, hR, hzero, hcontour, hRbCompact, hlimitRange, hspectral.2⟩

end NCG.VaryingHilbert.System
