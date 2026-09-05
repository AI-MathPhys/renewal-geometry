/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Order.Filter.Finite

/-!
# Uniform convergence on finite families

Pointwise convergence is uniform on a fixed finite set.  These elementary
filter lemmas package the quantifier shape used by finite Fourier-box
arguments: one late stage works simultaneously for every retained mode.
-/

open Filter Topology

namespace NCG

variable {α ι β : Type*} [PseudoMetricSpace β]
  {l : Filter α} {f : α → ι → β} {g : ι → β}

/-- Pointwise convergence on a finite set gives one eventual distance bound
simultaneously at every point of that set. -/
theorem eventually_forall_mem_finset_dist_lt_of_tendsto
    (s : Finset ι)
    (h : ∀ i ∈ s, Tendsto (fun n => f n i) l (𝓝 (g i)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in l, ∀ i ∈ s, dist (f n i) (g i) < ε := by
  rw [eventually_all_finset]
  intro i hi
  exact (Metric.tendsto_nhds.1 (h i hi) ε hε)

/-- Pointwise convergence on a finite set is uniform convergence on that
set, viewed as a subset of the index type. -/
theorem tendstoUniformlyOn_finset_of_tendsto
    (s : Finset ι)
    (h : ∀ i ∈ s, Tendsto (fun n => f n i) l (𝓝 (g i))) :
    TendstoUniformlyOn f g l (s : Set ι) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_forall_mem_finset_dist_lt_of_tendsto s h hε]
    with n hn
  intro i hi
  simpa only [dist_comm] using hn i hi

end NCG
