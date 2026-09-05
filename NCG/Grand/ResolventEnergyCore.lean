/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ResolventCoreMoscoRecovery
import Mathlib.Topology.Sequences

/-!
# Resolvent energy cores from dense range

For bounded forms, the energy-core condition in the converse Mosco theorem follows from two
standard facts: the limit resolvent has dense range and the form is norm-continuous.  The result
below packages the closure/sequence argument and produces the source sequence expected by the
diagonal recovery theorem.
-/

open Filter Topology Set

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]

/-- Dense resolvent range and norm-continuity of the form give an energy-convergent sequence of
resolvent images approximating any prescribed vector. -/
theorem exists_resolventCore_approximation_of_denseRange_of_continuous
    (q : E → ℝ) (T : E →L[K] E) (hT : DenseRange T) (hq : Continuous q)
    (x : E) :
    ∃ source : ℕ → E,
      Tendsto (fun m ↦ T (source m)) atTop (𝓝 x) ∧
        Tendsto (fun m ↦ q (T (source m))) atTop (𝓝 (q x)) := by
  have hx : x ∈ closure (range T) := by
    rw [hT.closure_range]
    exact mem_univ x
  obtain ⟨y, hyRange, hy⟩ := mem_closure_iff_seq_limit.mp hx
  choose source hsource using hyRange
  refine ⟨source, ?_, ?_⟩
  · simpa only [hsource] using hy
  · exact hq.continuousAt.tendsto.comp (by simpa only [hsource] using hy)

/-- Dense range of a fixed limit resolvent supplies the energy-core hypothesis for every vector
when the limit form is norm-continuous. -/
theorem resolventEnergyCore_of_denseRange_of_continuous
    (q : E → ℝ) (T : E →L[K] E) (hT : DenseRange T) (hq : Continuous q) :
    ∀ x : E, ∃ source : ℕ → E,
      Tendsto (fun m ↦ T (source m)) atTop (𝓝 x) ∧
        Tendsto (fun m ↦ q (T (source m))) atTop (𝓝 (q x)) :=
  fun x ↦ exists_resolventCore_approximation_of_denseRange_of_continuous
    (K := K) q T hT hq x

/-- Surjectivity is a convenient sufficient condition for the same bounded-form energy core. -/
theorem resolventEnergyCore_of_surjective_of_continuous
    (q : E → ℝ) (T : E →L[K] E) (hT : Function.Surjective T) (hq : Continuous q) :
    ∀ x : E, ∃ source : ℕ → E,
      Tendsto (fun m ↦ T (source m)) atTop (𝓝 x) ∧
        Tendsto (fun m ↦ q (T (source m))) atTop (𝓝 (q x)) :=
  resolventEnergyCore_of_denseRange_of_continuous (K := K) q T hT.denseRange hq

end NCG.VaryingHilbert
