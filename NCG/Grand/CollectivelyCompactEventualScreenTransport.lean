/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CollectivelyCompactTransport

/-!
# Transporting eventual compact-screen control

The manuscript's graph-screen profile is asymptotic in the cutoff. Finitely many early stages do
not affect collective compactness when each individual stage output is compact. This module
combines that observation with compatible postcomposition, allowing an eventual graph-screen
tail to produce collective compactness of the physical-coordinate family.
-/

open Filter Set Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w v' w' v'' w''

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable {G : Type v'} [NormedAddCommGroup G] [InnerProductSpace K G]
variable {Gn : ℕ → Type w'}
variable [∀ n, NormedAddCommGroup (Gn n)] [∀ n, InnerProductSpace K (Gn n)]
variable {F : Type v''} [NormedAddCommGroup F] [InnerProductSpace K F]
variable {Fn : ℕ → Type w''}
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace K (Fn n)]

/-- Eventual compact-screen tails for a stagewise compact output family remain collectively
compact after a compatible bounded output projection. -/
theorem collectivelyCompact_postcomp_of_eventually_compactOperator_screens
    [CompleteSpace G]
    (L : System (K := K) (H := G) (Hn := Gn))
    (M : System (K := K) (H := F) (Hn := Fn))
    (Tn : ∀ n, Hn n →L[K] Gn n)
    (screen : ℕ → G →L[K] G) (B : ℝ)
    (Sn : ∀ n, Gn n →L[K] Fn n) (S : G →L[K] F)
    (hbounded : L.embeddedUnitBallOutputs Tn ⊆ Metric.closedBall 0 B)
    (hstage : ∀ n, IsCompactOperator (L.embeddedOperator Tn n))
    (hcompact : ∀ R, IsCompactOperator (screen R))
    (htail : ∀ ε > 0, ∃ R,
      ∀ᶠ n in atTop, ∀ y ∈
        L.embeddedOperator Tn n '' Metric.closedBall 0 1,
          ‖y - screen R y‖ < ε)
    (hcommute : ∀ n y, M.embedding n (Sn n y) = S (L.embedding n y)) :
    M.CollectivelyCompact (fun n ↦ (Sn n).comp (Tn n)) := by
  have hgraph : L.CollectivelyCompact Tn :=
    L.collectivelyCompact_of_eventually_compactOperator_screens
      Tn screen B hbounded hstage hcompact htail
  exact hgraph.postcomp L M Tn Sn S hcommute

end NCG.VaryingHilbert.System
