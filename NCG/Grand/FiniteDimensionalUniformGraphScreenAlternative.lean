/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.UniformGraphScreenCollectiveCompactness
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Finite-cutoff graph-screen alternative

At finite-dimensional cutoffs every graph-output operator is automatically compact. Thus the
general asymptotic graph-screen alternative requires only boundedness and compactness of the
screens: stagewise compactness is discharged by the finite-dimensional carrier itself.
-/

open Filter Set Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w v' w'

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, FiniteDimensional K (Hn n)]
variable {G : Type v'} [NormedAddCommGroup G] [InnerProductSpace K G]
  [CompleteSpace G]
variable {Gn : ℕ → Type w'}
variable [∀ n, NormedAddCommGroup (Gn n)] [∀ n, InnerProductSpace K (Gn n)]

/-- At finite-dimensional cutoffs, monotone eventual compact-screen tightness automatically
implies collective compactness of the graph-output family. -/
theorem collectivelyCompact_of_uniformGraphScreenTight_of_finiteDimensional
    (L : System (K := K) (H := G) (Hn := Gn))
    (graphTn : ∀ n, Hn n →L[K] Gn n)
    (screen : ℕ → G →L[K] G) (B : ℝ)
    (hbounded : L.embeddedUnitBallOutputs graphTn ⊆ Metric.closedBall 0 B)
    (hcompact : ∀ radius, IsCompactOperator (screen radius))
    (htight : NCG.VaryingHilbert.UniformGraphScreenTight
      (fun n u ↦ L.embedding n (graphTn n u))
      (fun radius y ↦ y - screen radius y)
      (fun _ u ↦ ‖u‖ ≤ 1)) :
    L.CollectivelyCompact graphTn := by
  apply L.collectivelyCompact_of_uniformGraphScreenTight
    graphTn screen B hbounded
      (fun n ↦ by
        letI : ProperSpace (Hn n) :=
          FiniteDimensional.proper_rclike K (Hn n)
        exact isCompactOperator_of_locallyCompactSpace_rng
          (L.embeddedOperator graphTn n))
    hcompact htight

/-- Finite-dimensional graph cutoffs satisfy the exact compactness-or-mass-escape alternative
without a separate stagewise compactness premise. -/
theorem collectivelyCompact_or_massEscape_of_finiteDimensional_graphScreens
    (L : System (K := K) (H := G) (Hn := Gn))
    (graphTn : ∀ n, Hn n →L[K] Gn n)
    (screen : ℕ → G →L[K] G) (B : ℝ)
    (hbounded : L.embeddedUnitBallOutputs graphTn ⊆ Metric.closedBall 0 B)
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
  exact L.collectivelyCompact_or_massEscape_of_graphScreens
    graphTn screen B hbounded
      (fun n ↦ by
        letI : ProperSpace (Hn n) :=
          FiniteDimensional.proper_rclike K (Hn n)
        exact isCompactOperator_of_locallyCompactSpace_rng
          (L.embeddedOperator graphTn n))
    hcompact

end NCG.VaryingHilbert.System
