/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertMosco
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Uniform boundedness of weakly convergent varying-space sequences

Weak convergence in the common Hilbert carrier is pointwise convergence of the associated inner
product functionals.  Banach--Steinhaus therefore supplies a uniform norm bound for the embedded
vectors, hence for the original stage vectors.
-/

open Filter Topology Set

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H] [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Every weakly convergent dependent sequence is uniformly norm bounded. -/
theorem WeaklyConverges.exists_uniform_norm_bound
    {x : ∀ n, Hn n} {xlim : H} (hx : J.WeaklyConverges x xlim) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖x n‖ ≤ C := by
  have hpoint : ∀ y : H, ∃ C : ℝ, ∀ n,
      ‖(innerSL K (J.embedding n (x n))) y‖ ≤ C := by
    intro y
    have hrange : Bornology.IsBounded
        (range fun n ↦ (innerSL K (J.embedding n (x n))) y) :=
      Metric.isBounded_range_of_tendsto _ (hx y)
    obtain ⟨C, -, hnorm⟩ := hrange.exists_pos_norm_le
    exact ⟨C, fun n ↦ hnorm _ ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus
    (g := fun n ↦ innerSL K (J.embedding n (x n))) hpoint
  refine ⟨C, (norm_nonneg _).trans (hC 0), fun n ↦ ?_⟩
  simpa only [innerSL_apply_norm, LinearIsometry.norm_map] using hC n

end NCG.VaryingHilbert.System
