/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphNormCarrier
import NCG.Grand.FiniteDimensionalUniformGraphScreenAlternative
import NCG.Grand.VaryingHilbertCollectiveCompactOperations
import NCG.Grand.CollectivelyCompactTransport

/-!
# Compact graph-energy balls imply compact resolvents

This module applies compact screens to the entire graph-norm unit ball, not
merely to the image of the resolvent unit ball.  At finite cutoffs the graph
carrier is finite-dimensional.  Screen tightness therefore makes the graph
inclusions collectively compact; the uniformly bounded weak-resolvent lift
then gives collective compactness of graph outputs and, by first-coordinate
projection, of the physical resolvents.
-/

open Filter Set

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w z z'

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, FiniteDimensional K (Hn n)]
variable {F : Type z} [NormedAddCommGroup F] [InnerProductSpace K F]
  [CompleteSpace F]
variable {Fn : ℕ → Type z'}
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace K (Fn n)]

omit [CompleteSpace H] [∀ n, FiniteDimensional K (Hn n)] [CompleteSpace F] in
/-- Embedded graph inclusions map their unit balls into the common graph
unit ball, because both the inclusion and the varying-space embeddings are
isometries. -/
theorem embeddedUnitBallOutputs_operatorGraphNormInclusion_subset_closedBall
    (L : System (K := K) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Dn : ∀ n, Submodule K (Hn n))
    (An : ∀ n, Dn n →ₗ[K] Fn n) :
    L.embeddedUnitBallOutputs
        (fun n ↦ operatorGraphNormInclusion (Dn n) (An n)) ⊆
      Metric.closedBall 0 1 := by
  intro y hy
  change y ∈ ⋃ n, L.embeddedOperator
    (fun n ↦ operatorGraphNormInclusion (Dn n) (An n)) n '' Metric.closedBall 0 1 at hy
  obtain ⟨n, u, hu, rfl⟩ := Set.mem_iUnion.mp hy
  change dist (L.embedding n
    (operatorGraphNormInclusion (Dn n) (An n) u)) 0 ≤ 1
  simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometry.norm_map,
    operatorGraphNormInclusion_apply, Submodule.coe_norm] using hu

/-- Uniform compact-screen tightness of the full graph-energy unit balls
makes the Hilbert graph-output resolvents collectively compact. -/
theorem operatorGraphResolventHilbertGraph_collectivelyCompact_of_graphNormScreenTight
    (L : System (K := K) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Dn : ∀ n, Submodule K (Hn n))
    (An : ∀ n, Dn n →ₗ[K] Fn n)
    (Rn : ∀ n, Hn n →L[K] Hn n)
    (lam : ℝ) (hlam : 0 < lam)
    (hEquation : ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Rn n f))
    (screen : ℕ → WithLp 2 (H × F) →L[K] WithLp 2 (H × F))
    (hcompact : ∀ radius, IsCompactOperator (screen radius))
    (htight : NCG.VaryingHilbert.UniformGraphScreenTight
      (fun n u ↦ L.embedding n
        (operatorGraphNormInclusion (Dn n) (An n) u))
      (fun radius y ↦ y - screen radius y)
      (fun _ u ↦ ‖u‖ ≤ 1)) :
    L.CollectivelyCompact
      (fun n ↦ operatorGraphResolventHilbertGraph
        (Dn n) (An n) (Rn n) lam hlam (hEquation n)) := by
  let graphInclusion :=
    fun n ↦ operatorGraphNormInclusion (Dn n) (An n)
  have hgraphCarrier : L.CollectivelyCompact graphInclusion := by
    apply L.collectivelyCompact_of_uniformGraphScreenTight_of_finiteDimensional
      graphInclusion screen 1
    · simpa only [graphInclusion] using
        embeddedUnitBallOutputs_operatorGraphNormInclusion_subset_closedBall
          L Dn An
    · exact hcompact
    · simpa only [graphInclusion] using htight
  let graphResolvent := fun n ↦
    operatorGraphResolventNormCarrier
      (Dn n) (An n) (Rn n) lam hlam (hEquation n)
  have hprecomp := hgraphCarrier.precomp_uniformlyBounded L
    (2 * (1 + 1 / lam)) (by positivity)
    (fun n ↦ by
      simpa only [graphResolvent] using
        norm_operatorGraphResolventNormCarrier_le
          (Dn n) (An n) (Rn n) lam hlam (hEquation n))
  simpa only [graphInclusion, graphResolvent,
    operatorGraphNormInclusion_comp_resolventNormCarrier] using hprecomp

/-- The same full graph-energy screen hypothesis yields collective
compactness of the physical resolvents after compatible first-coordinate
projection. -/
theorem operatorGraphResolvent_collectivelyCompact_of_graphNormScreenTight
    (J : System (K := K) (H := H) (Hn := Hn))
    (L : System (K := K) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Dn : ∀ n, Submodule K (Hn n))
    (An : ∀ n, Dn n →ₗ[K] Fn n)
    (Rn : ∀ n, Hn n →L[K] Hn n)
    (lam : ℝ) (hlam : 0 < lam)
    (hEquation : ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Rn n f))
    (screen : ℕ → WithLp 2 (H × F) →L[K] WithLp 2 (H × F))
    (hcompact : ∀ radius, IsCompactOperator (screen radius))
    (htight : NCG.VaryingHilbert.UniformGraphScreenTight
      (fun n u ↦ L.embedding n
        (operatorGraphNormInclusion (Dn n) (An n) u))
      (fun radius y ↦ y - screen radius y)
      (fun _ u ↦ ‖u‖ ≤ 1))
    (hfst : ∀ n y, J.embedding n y.fst = (L.embedding n y).fst) :
    J.CollectivelyCompact Rn := by
  let graphRn := fun n ↦ operatorGraphResolventHilbertGraph
    (Dn n) (An n) (Rn n) lam hlam (hEquation n)
  have hgraph : L.CollectivelyCompact graphRn := by
    simpa only [graphRn] using
      L.operatorGraphResolventHilbertGraph_collectivelyCompact_of_graphNormScreenTight
        Dn An Rn lam hlam hEquation screen hcompact htight
  have hphysical := hgraph.postcomp L J graphRn
    (fun n ↦ WithLp.fstL 2 K (Hn n) (Fn n))
    (WithLp.fstL 2 K H F) hfst
  simpa only [graphRn, fstL_comp_operatorGraphResolventHilbertGraph] using hphysical

omit [∀ n, FiniteDimensional K (Hn n)] in
/-- A not-necessarily-monotone compact-screen tail estimate on the union of
all embedded graph-energy unit balls makes the Hilbert graph resolvents
collectively compact. -/
theorem operatorGraphResolventHilbertGraph_collectivelyCompact_of_graphNormScreenTails
    (L : System (K := K) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Dn : ∀ n, Submodule K (Hn n))
    (An : ∀ n, Dn n →ₗ[K] Fn n)
    (Rn : ∀ n, Hn n →L[K] Hn n)
    (lam : ℝ) (hlam : 0 < lam)
    (hEquation : ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Rn n f))
    (screen : ℕ → WithLp 2 (H × F) →L[K] WithLp 2 (H × F))
    (hcompact : ∀ radius, IsCompactOperator (screen radius))
    (htail : ∀ ε > 0, ∃ radius, ∀ y ∈
      L.embeddedUnitBallOutputs
        (fun n ↦ operatorGraphNormInclusion (Dn n) (An n)),
      ‖y - screen radius y‖ < ε) :
    L.CollectivelyCompact
      (fun n ↦ operatorGraphResolventHilbertGraph
        (Dn n) (An n) (Rn n) lam hlam (hEquation n)) := by
  let graphInclusion :=
    fun n ↦ operatorGraphNormInclusion (Dn n) (An n)
  have hgraphCarrier : L.CollectivelyCompact graphInclusion := by
    apply L.collectivelyCompact_of_compactOperator_screens
      graphInclusion screen 1
    · simpa only [graphInclusion] using
        embeddedUnitBallOutputs_operatorGraphNormInclusion_subset_closedBall
          L Dn An
    · exact hcompact
    · simpa only [graphInclusion] using htail
  let graphResolvent := fun n ↦
    operatorGraphResolventNormCarrier
      (Dn n) (An n) (Rn n) lam hlam (hEquation n)
  have hprecomp := hgraphCarrier.precomp_uniformlyBounded L
    (2 * (1 + 1 / lam)) (by positivity)
    (fun n ↦ by
      simpa only [graphResolvent] using
        norm_operatorGraphResolventNormCarrier_le
          (Dn n) (An n) (Rn n) lam hlam (hEquation n))
  simpa only [graphInclusion, graphResolvent,
    operatorGraphNormInclusion_comp_resolventNormCarrier] using hprecomp

omit [∀ n, FiniteDimensional K (Hn n)] in
/-- A compact-screen tail estimate on the full embedded graph-energy unit
balls gives collective compactness of the physical resolvents after
compatible first-coordinate projection. -/
theorem operatorGraphResolvent_collectivelyCompact_of_graphNormScreenTails
    (J : System (K := K) (H := H) (Hn := Hn))
    (L : System (K := K) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Dn : ∀ n, Submodule K (Hn n))
    (An : ∀ n, Dn n →ₗ[K] Fn n)
    (Rn : ∀ n, Hn n →L[K] Hn n)
    (lam : ℝ) (hlam : 0 < lam)
    (hEquation : ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Rn n f))
    (screen : ℕ → WithLp 2 (H × F) →L[K] WithLp 2 (H × F))
    (hcompact : ∀ radius, IsCompactOperator (screen radius))
    (htail : ∀ ε > 0, ∃ radius, ∀ y ∈
      L.embeddedUnitBallOutputs
        (fun n ↦ operatorGraphNormInclusion (Dn n) (An n)),
      ‖y - screen radius y‖ < ε)
    (hfst : ∀ n y, J.embedding n y.fst = (L.embedding n y).fst) :
    J.CollectivelyCompact Rn := by
  let graphRn := fun n ↦ operatorGraphResolventHilbertGraph
    (Dn n) (An n) (Rn n) lam hlam (hEquation n)
  have hgraph : L.CollectivelyCompact graphRn := by
    simpa only [graphRn] using
      L.operatorGraphResolventHilbertGraph_collectivelyCompact_of_graphNormScreenTails
        Dn An Rn lam hlam hEquation screen hcompact htail
  have hphysical := hgraph.postcomp L J graphRn
    (fun n ↦ WithLp.fstL 2 K (Hn n) (Fn n))
    (WithLp.fstL 2 K H F) hfst
  simpa only [graphRn, fstL_comp_operatorGraphResolventHilbertGraph] using hphysical

/-- Compact graph-energy balls give compact physical resolvents; failure of
uniform screen tightness gives an exact cofinal graph-energy mass-escape
witness with one fixed positive margin. -/
theorem operatorGraphResolvent_collectivelyCompact_or_graphNormMassEscape
    (J : System (K := K) (H := H) (Hn := Hn))
    (L : System (K := K) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Dn : ∀ n, Submodule K (Hn n))
    (An : ∀ n, Dn n →ₗ[K] Fn n)
    (Rn : ∀ n, Hn n →L[K] Hn n)
    (lam : ℝ) (hlam : 0 < lam)
    (hEquation : ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Rn n f))
    (screen : ℕ → WithLp 2 (H × F) →L[K] WithLp 2 (H × F))
    (hcompact : ∀ radius, IsCompactOperator (screen radius))
    (hfst : ∀ n y, J.embedding n y.fst = (L.embedding n y).fst) :
    J.CollectivelyCompact Rn ∨
      ∃ ε > 0, ∃ radius cutoff : ℕ → ℕ,
        ∃ u : ∀ j, operatorGraphNormCarrier
            (Dn (cutoff j)) (An (cutoff j)),
          Tendsto radius Filter.atTop Filter.atTop ∧
          Tendsto cutoff Filter.atTop Filter.atTop ∧
          ∀ j, ‖u j‖ ≤ 1 ∧
            ε ≤ ‖L.embedding (cutoff j)
                (operatorGraphNormInclusion
                  (Dn (cutoff j)) (An (cutoff j)) (u j)) -
              screen (radius j)
                (L.embedding (cutoff j)
                  (operatorGraphNormInclusion
                    (Dn (cutoff j)) (An (cutoff j)) (u j)))‖ := by
  let graphInclusion :=
    fun n ↦ operatorGraphNormInclusion (Dn n) (An n)
  have halt :=
    L.collectivelyCompact_or_massEscape_of_finiteDimensional_graphScreens
      graphInclusion screen 1
      (by
        simpa only [graphInclusion] using
          embeddedUnitBallOutputs_operatorGraphNormInclusion_subset_closedBall
            L Dn An)
      hcompact
  rcases halt with hgraphCarrier | hescape
  · left
    let graphResolvent := fun n ↦
      operatorGraphResolventNormCarrier
        (Dn n) (An n) (Rn n) lam hlam (hEquation n)
    have hprecomp := hgraphCarrier.precomp_uniformlyBounded L
      (2 * (1 + 1 / lam)) (by positivity)
      (fun n ↦ by
        simpa only [graphResolvent] using
          norm_operatorGraphResolventNormCarrier_le
            (Dn n) (An n) (Rn n) lam hlam (hEquation n))
    let graphRn := fun n ↦ operatorGraphResolventHilbertGraph
      (Dn n) (An n) (Rn n) lam hlam (hEquation n)
    have hgraphRn : L.CollectivelyCompact graphRn := by
      simpa only [graphInclusion, graphResolvent, graphRn,
        operatorGraphNormInclusion_comp_resolventNormCarrier] using hprecomp
    have hphysical := hgraphRn.postcomp L J graphRn
      (fun n ↦ WithLp.fstL 2 K (Hn n) (Fn n))
      (WithLp.fstL 2 K H F) hfst
    simpa only [graphRn, fstL_comp_operatorGraphResolventHilbertGraph] using hphysical
  · right
    simpa only [graphInclusion] using hescape

end NCG.VaryingHilbert.System
