/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CollectivelyCompactTransport
import NCG.Grand.CompressedOperatorNormConvergence

/-!
# Graph screens imply norm convergence of compressed resolvents

This file assembles the positive compact-screen mechanism in the exact common-carrier form used
by the manuscript.  Compact screens make the graph-output family collectively compact; a
compatible physical-coordinate projection transfers compactness to the stage resolvents; and
symmetric strong convergence then becomes operator-norm convergence of `Jₙ Tₙ Jₙ†`.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w v' w'

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable {G : Type v'} [NormedAddCommGroup G] [InnerProductSpace K G]
  [CompleteSpace G]
variable {Gn : ℕ → Type w'}
variable [∀ n, NormedAddCommGroup (Gn n)] [∀ n, InnerProductSpace K (Gn n)]

/-- Compact graph screens plus symmetric varying-space strong convergence imply operator-norm
convergence of the literal compressed resolvents on the common Hilbert carrier. -/
theorem compressedOperator_tendsto_operatorNorm_of_graphScreens
    (J : System (K := K) (H := H) (Hn := Hn))
    (L : System (K := K) (H := G) (Hn := Gn))
    (graphTn : ∀ n, Hn n →L[K] Gn n)
    (screen : ℕ → G →L[K] G) (B : ℝ)
    (Pn : ∀ n, Gn n →L[K] Hn n) (P : G →L[K] H)
    (T : H →L[K] H)
    (hbounded : L.embeddedUnitBallOutputs graphTn ⊆ Metric.closedBall 0 B)
    (hcompact : ∀ R, IsCompactOperator (screen R))
    (htail : ∀ ε > 0, ∃ R, ∀ y ∈ L.embeddedUnitBallOutputs graphTn,
      ‖y - screen R y‖ < ε)
    (hcommute : ∀ n y, J.embedding n (Pn n y) = P (L.embedding n y))
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J
      (fun n ↦ (Pn n).comp (graphTn n)) T)
    (hsymm : ∀ n,
      LinearMap.IsSymmetric ((Pn n).comp (graphTn n)).toLinearMap)
    (hlimSymm : LinearMap.IsSymmetric T.toLinearMap) :
    Tendsto
      (J.compressedOperator (fun n ↦ (Pn n).comp (graphTn n)))
      atTop (nhds T) := by
  have hprojected :
      J.CollectivelyCompact (fun n ↦ (Pn n).comp (graphTn n)) :=
    L.collectivelyCompact_postcomp_of_compactOperator_screens J
      graphTn screen B Pn P hbounded hcompact htail hcommute
  exact J.compressedOperator_tendsto_operatorNorm
    (fun n ↦ (Pn n).comp (graphTn n)) T
    hdense hstrong hprojected hsymm hlimSymm

end NCG.VaryingHilbert.System
