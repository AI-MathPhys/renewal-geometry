/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ClosedLinearPMapWeakLimit
import NCG.Grand.WeakSpaceProductConvergence

/-!
# Mixed strong--weak limits in closed operator graphs

A norm-closed linear graph contains the limit whenever the inputs converge strongly and the
operator values converge weakly.
-/

open Filter Topology

noncomputable section

namespace NCG

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace K F]

/-- Closed unbounded-operator graphs are stable under strong convergence in the domain variable
and weak convergence in the range variable. -/
theorem LinearPMap.IsClosed.mem_graph_of_strong_weak_limit
    {T : E →ₗ.[K] F} (hT : T.IsClosed)
    {ι : Type*} {l : Filter ι} [NeBot l]
    {x : ι → E} {xlim : E} {y : ι → F} {ylim : F}
    (hgraph : ∀ᶠ i in l, (x i, y i) ∈ T.graph)
    (hx : Tendsto x l (𝓝 xlim))
    (hy : Tendsto (fun i ↦ toWeakSpace K F (y i)) l
      (𝓝 (toWeakSpace K F ylim))) :
    (xlim, ylim) ∈ T.graph := by
  apply LinearPMap.IsClosed.mem_graph_of_tendsto_toWeakSpace_canonical hT hgraph
  exact tendsto_toWeakSpace_prod_of_strong_of_weak hx hy

end NCG
