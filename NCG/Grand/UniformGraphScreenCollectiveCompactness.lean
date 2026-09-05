/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactScreenCollectiveCompactness
import NCG.Grand.GraphScreenMassEscape

/-!
# Uniform graph screens and collective compactness

This module states the compact-screen alternative directly for a varying family of graph-output
operators. The stage carrier may itself carry the graph norm, so its closed unit ball is exactly
the form-energy unit ball from the manuscript. Monotone eventual tail tightness yields collective
compactness after absorbing finitely many early stages; failure yields a cofinal mass-escape
witness with a fixed positive tail.
-/

open Filter Set Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w v' w'

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable {G : Type v'} [NormedAddCommGroup G] [InnerProductSpace K G]
  [CompleteSpace G]
variable {Gn : ℕ → Type w'}
variable [∀ n, NormedAddCommGroup (Gn n)] [∀ n, InnerProductSpace K (Gn n)]

/-- Monotone eventual tightness of the embedded stage-unit-ball graph outputs under compact
screens implies collective compactness of the graph-output family. -/
theorem collectivelyCompact_of_uniformGraphScreenTight
    (L : System (K := K) (H := G) (Hn := Gn))
    (graphTn : ∀ n, Hn n →L[K] Gn n)
    (screen : ℕ → G →L[K] G) (B : ℝ)
    (hbounded : L.embeddedUnitBallOutputs graphTn ⊆ Metric.closedBall 0 B)
    (hstage : ∀ n, IsCompactOperator (L.embeddedOperator graphTn n))
    (hcompact : ∀ radius, IsCompactOperator (screen radius))
    (htight : NCG.VaryingHilbert.UniformGraphScreenTight
      (fun n u ↦ L.embedding n (graphTn n u))
      (fun radius y ↦ y - screen radius y)
      (fun _ u ↦ ‖u‖ ≤ 1)) :
    L.CollectivelyCompact graphTn := by
  apply L.collectivelyCompact_of_eventually_compactOperator_screens
    graphTn screen B hbounded hstage hcompact
  intro ε hε
  obtain ⟨radius, hradius⟩ := htight ε hε
  refine ⟨radius, ?_⟩
  filter_upwards [hradius radius le_rfl] with n hn
  intro y hy
  obtain ⟨u, hu, rfl⟩ := hy
  apply hn u
  simpa only [Metric.mem_closedBall, dist_zero_right] using hu

/-- Exact graph-output compactness alternative. The negative branch gives cofinal radii and
cutoffs, unit-bounded stage vectors, and one fixed escaped graph-tail margin. -/
theorem collectivelyCompact_or_massEscape_of_graphScreens
    (L : System (K := K) (H := G) (Hn := Gn))
    (graphTn : ∀ n, Hn n →L[K] Gn n)
    (screen : ℕ → G →L[K] G) (B : ℝ)
    (hbounded : L.embeddedUnitBallOutputs graphTn ⊆ Metric.closedBall 0 B)
    (hstage : ∀ n, IsCompactOperator (L.embeddedOperator graphTn n))
    (hcompact : ∀ radius, IsCompactOperator (screen radius)) :
    L.CollectivelyCompact graphTn ∨
      ∃ ε > 0, ∃ radius cutoff : ℕ → ℕ,
        ∃ u : ∀ j, Hn (cutoff j),
          Tendsto radius atTop atTop ∧ Tendsto cutoff atTop atTop ∧
          ∀ j, ‖u j‖ ≤ 1 ∧
            ε ≤ ‖L.embedding (cutoff j)
                (graphTn (cutoff j) (u j)) -
              screen (radius j)
                (L.embedding (cutoff j)
                  (graphTn (cutoff j) (u j)))‖ := by
  let graph : ∀ n, Hn n → G := fun n u ↦ L.embedding n (graphTn n u)
  let tail : ℕ → G → G := fun radius y ↦ y - screen radius y
  let admissible : ∀ n, Hn n → Prop := fun _ u ↦ ‖u‖ ≤ 1
  by_cases htight : NCG.VaryingHilbert.UniformGraphScreenTight
      graph tail admissible
  · left
    apply L.collectivelyCompact_of_uniformGraphScreenTight
      graphTn screen B hbounded hstage hcompact
    simpa only [graph, tail, admissible] using htight
  · right
    simpa only [graph, tail, admissible] using
      NCG.VaryingHilbert.massEscape_of_not_uniformGraphScreenTight
        graph tail admissible htight

end NCG.VaryingHilbert.System
