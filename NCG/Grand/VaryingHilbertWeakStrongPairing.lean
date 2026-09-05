/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertMosco

/-!
# Pairing weak and strong sequences on varying Hilbert spaces

A norm-bounded weakly convergent dependent sequence can be paired against a strongly convergent
dependent sequence, and the inner products converge.  This supplies the moving source-term limit
in the variational proof of Mosco-to-resolvent convergence.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Weak convergence may be tested against a moving strongly convergent vector when the weak
sequence has a uniform norm bound. -/
theorem WeaklyConverges.inner_strong
    {x y : ∀ n, Hn n} {xlim ylim : H}
    (hx : J.WeaklyConverges x xlim)
    (hy : J.StronglyConverges y ylim)
    (C : ℝ) (hbound : ∀ n, ‖x n‖ ≤ C) :
    Tendsto (fun n ↦ inner K (J.embedding n (x n)) (J.embedding n (y n))) atTop
      (𝓝 (inner K xlim ylim)) := by
  have hyDiff :
      Tendsto (fun n ↦ ‖J.embedding n (y n) - ylim‖) atTop (𝓝 0) := by
    simpa [StronglyConverges, tendsto_iff_norm_sub_tendsto_zero] using hy
  have herror :
      Tendsto
        (fun n ↦ inner K (J.embedding n (x n))
          (J.embedding n (y n) - ylim)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n ↦ C * ‖J.embedding n (y n) - ylim‖) ?_ ?_
    · intro n
      calc
        ‖inner K (J.embedding n (x n)) (J.embedding n (y n) - ylim)‖ ≤
            ‖J.embedding n (x n)‖ * ‖J.embedding n (y n) - ylim‖ :=
          norm_inner_le_norm _ _
        _ ≤ C * ‖J.embedding n (y n) - ylim‖ := by
          gcongr
          simpa using hbound n
    · simpa using (tendsto_const_nhds.mul hyDiff :
        Tendsto (fun n ↦ C * ‖J.embedding n (y n) - ylim‖) atTop (𝓝 (C * 0)))
  have hsum := herror.add (hx ylim)
  convert hsum using 1
  · funext n
    rw [← inner_add_right]
    simp
  · simp

end NCG.VaryingHilbert.System
