/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactScreenCollectiveCompactness

/-!
# Transporting collective compactness through output maps

Collective compactness is preserved when the stage outputs are mapped compatibly into another
varying Hilbert system.  In particular, a collectively compact family of graph vectors yields a
collectively compact resolvent family after applying the physical-coordinate projection.
-/

open Set

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

/-- A collectively compact output family stays collectively compact after a compatible bounded
linear map of its varying and limiting output spaces. -/
theorem CollectivelyCompact.postcomp
    (L : System (K := K) (H := G) (Hn := Gn))
    (M : System (K := K) (H := F) (Hn := Fn))
    (Tn : ∀ n, Hn n →L[K] Gn n)
    (Sn : ∀ n, Gn n →L[K] Fn n) (S : G →L[K] F)
    (hT : L.CollectivelyCompact Tn)
    (hcommute : ∀ n y, M.embedding n (Sn n y) = S (L.embedding n y)) :
    M.CollectivelyCompact (fun n ↦ (Sn n).comp (Tn n)) := by
  obtain ⟨C, hC, hTC⟩ := hT
  refine ⟨S '' C, hC.image S.continuous, ?_⟩
  intro n y hy
  obtain ⟨x, hx, rfl⟩ := hy
  change M.embedding n (Sn n (Tn n x)) ∈ S '' C
  rw [hcommute]
  exact ⟨L.embedding n (Tn n x), hTC n ⟨x, hx, rfl⟩, rfl⟩

/-- Compact screens for a graph-output family imply collective compactness after any compatible
bounded output projection.  Taking `S` and `Sn` to be first-coordinate maps gives the direct
graph-screen-to-resolvent compactness bridge. -/
theorem collectivelyCompact_postcomp_of_compactOperator_screens
    [CompleteSpace G]
    (L : System (K := K) (H := G) (Hn := Gn))
    (M : System (K := K) (H := F) (Hn := Fn))
    (Tn : ∀ n, Hn n →L[K] Gn n)
    (screen : ℕ → G →L[K] G) (B : ℝ)
    (Sn : ∀ n, Gn n →L[K] Fn n) (S : G →L[K] F)
    (hbounded : L.embeddedUnitBallOutputs Tn ⊆ Metric.closedBall 0 B)
    (hcompact : ∀ R, IsCompactOperator (screen R))
    (htail : ∀ ε > 0, ∃ R, ∀ y ∈ L.embeddedUnitBallOutputs Tn,
      ‖y - screen R y‖ < ε)
    (hcommute : ∀ n y, M.embedding n (Sn n y) = S (L.embedding n y)) :
    M.CollectivelyCompact (fun n ↦ (Sn n).comp (Tn n)) := by
  exact (L.collectivelyCompact_of_compactOperator_screens
    Tn screen B hbounded hcompact htail).postcomp L M Tn Sn S hcommute

end NCG.VaryingHilbert.System
