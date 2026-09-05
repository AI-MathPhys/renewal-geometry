/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertMosco
import Mathlib.Analysis.Real.Sqrt

/-!
# Radon--Riesz principle on varying Hilbert spaces

Weak convergence in the common carrier plus convergence of norms implies strong convergence.
This is the Hilbert-space step used in the variational proof that Mosco convergence forces
strong convergence of resolvent minimizers.
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

/-- The varying-space Radon--Riesz property: weak convergence together with convergence of the
stage norms implies strong convergence in the common carrier. -/
theorem WeaklyConverges.strong_of_norm
    {x : ∀ n, Hn n} {xlim : H}
    (hweak : J.WeaklyConverges x xlim)
    (hnorm : Tendsto (fun n ↦ ‖x n‖) atTop (𝓝 ‖xlim‖)) :
    J.StronglyConverges x xlim := by
  have hnormEmb :
      Tendsto (fun n ↦ ‖J.embedding n (x n)‖) atTop (𝓝 ‖xlim‖) := by
    simpa using hnorm
  have hinnerRe :
      Tendsto (fun n ↦ RCLike.re (inner K (J.embedding n (x n)) xlim)) atTop
        (𝓝 (RCLike.re (inner K xlim xlim))) := by
    exact RCLike.reCLM.continuous.continuousAt.tendsto.comp (hweak xlim)
  have hsquare :
      Tendsto (fun n ↦ ‖J.embedding n (x n) - xlim‖ ^ 2) atTop (𝓝 0) := by
    have hcalc := (hnormEmb.pow 2).sub (hinnerRe.const_mul 2) |>.add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ‖xlim‖ ^ 2) atTop (𝓝 (‖xlim‖ ^ 2)))
    convert hcalc using 1
    · funext n
      exact norm_sub_sq (J.embedding n (x n)) xlim
    · rw [inner_self_eq_norm_sq]
      ring_nf
  have hnormDiff :
      Tendsto (fun n ↦ ‖J.embedding n (x n) - xlim‖) atTop (𝓝 0) := by
    have hsqrt := hsquare.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using hsqrt
  simpa [StronglyConverges, tendsto_iff_norm_sub_tendsto_zero] using hnormDiff

end NCG.VaryingHilbert.System
