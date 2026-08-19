/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCollectiveCompactOperations

/-!
# Propagation of collective compactness between resolvent shifts

A reversed resolvent identity expresses the resolvent at a new shift as the sum of the original
resolvent and its composition with the uniformly bounded new resolvent.  Thus collective
compactness at one shift propagates simultaneously to every positive shift.
-/

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]

/-- Collective compactness at one positive real resolvent shift propagates to all positive
shifts, provided the shifted resolvents are uniformly bounded and satisfy the reversed
resolvent identity. -/
theorem CollectivelyCompact.allPositiveRealResolventShifts
    (J : System (K := K) (H := H) (Hn := Hn))
    (Rn : ℝ → ∀ n, Hn n →L[K] Hn n) (a : ℝ)
    (ha : J.CollectivelyCompact (Rn a))
    (hbound : ∀ b, 0 < b → ∃ C : ℝ, ∀ n, ‖Rn b n‖ ≤ C)
    (hidentity : ∀ b, 0 < b → ∀ n,
      Rn b n = Rn a n + (((a - b : ℝ) : K)) •
        ((Rn a n).comp (Rn b n))) :
    ∀ b, 0 < b → J.CollectivelyCompact (Rn b) := by
  intro b hbPos
  obtain ⟨C, hC⟩ := hbound b hbPos
  let B : ℝ := max C 1
  have hBPos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  have hbBound : ∀ n, ‖Rn b n‖ ≤ B := by
    intro n
    exact (hC n).trans (le_max_left C 1)
  exact ha.of_reversed_resolvent_identity J Rn a b B hBPos hbBound
    (hidentity b hbPos)

end NCG.VaryingHilbert.System
