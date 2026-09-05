/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertMosco
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Uniform boundedness of strongly convergent varying-space sequences

Strong convergence in the common carrier automatically supplies one positive bound for all stage
norms.  This small bridge feeds moving source families into the coercive resolvent estimates.
-/

open Filter Topology Set

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- A strongly convergent dependent sequence admits a positive uniform stage-norm bound. -/
theorem StronglyConverges.exists_pos_uniform_norm_bound
    {x : ∀ n, Hn n} {xlim : H} (hx : J.StronglyConverges x xlim) :
    ∃ C > 0, ∀ n, ‖x n‖ ≤ C := by
  have hrange : Bornology.IsBounded (range fun n ↦ J.embedding n (x n)) :=
    Metric.isBounded_range_of_tendsto _ hx
  obtain ⟨C, hC, hnorm⟩ := hrange.exists_pos_norm_le
  refine ⟨C, hC, fun n ↦ ?_⟩
  simpa using hnorm (J.embedding n (x n)) ⟨n, rfl⟩

end NCG.VaryingHilbert.System
