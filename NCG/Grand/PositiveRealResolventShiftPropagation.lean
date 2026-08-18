/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RealResolventShiftPropagation

/-!
# Propagation among positive real resolvent shifts

Variational resolvents are naturally specified only for positive shifts.  This wrapper propagates
strong operator convergence from one positive shift to every positive shift without asking for
identities or bounds at nonpositive parameters.
-/

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Convergence at one positive real shift propagates to all positive shifts. -/
theorem StrongOperatorConverges.allPositiveRealResolventShifts
    (Rn : ℝ → ∀ n, Hn n →L[K] Hn n) (R : ℝ → H →L[K] H)
    (a : ℝ) (haPos : 0 < a)
    (hdense : J.IsAsymptoticallyDense)
    (ha : J.StrongOperatorConverges J (Rn a) (R a))
    (hbound : ∀ b, 0 < b → ∃ C : ℝ, ∀ n, ‖Rn b n‖ ≤ C)
    (hstage : ∀ a b, 0 < a → 0 < b → ∀ n,
      Rn b n - Rn a n = (((a - b : ℝ) : K)) • ((Rn b n).comp (Rn a n)))
    (hlimit : ∀ a b, 0 < a → 0 < b →
      R a - R b = (((b - a : ℝ) : K)) • ((R a).comp (R b))) :
    ∀ b, 0 < b → J.StrongOperatorConverges J (Rn b) (R b) := by
  intro b hbPos
  obtain ⟨C, hbBound⟩ := hbound b hbPos
  exact StrongOperatorConverges.realResolventShift J Rn R a b
    hdense ha C hbBound (hstage a b haPos hbPos) (hlimit a b haPos hbPos)

end NCG.VaryingHilbert.System
