/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ClosedLinearPMapWeakGraph

/-!
# Weak limits in closed unbounded-operator graphs

This module turns weak closedness of a linear graph into the corresponding filter-limit rule.
-/

open Set Topology Filter

noncomputable section

namespace NCG

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace K F]

/-- A weak limit of points in a norm-closed linear graph remains in the graph. -/
theorem LinearPMap.IsClosed.mem_graph_of_tendsto_toWeakSpace
    [NormedSpace ℝ E] [IsScalarTower ℝ K E]
    [NormedSpace ℝ F] [IsScalarTower ℝ K F]
    {T : E →ₗ.[K] F} (hT : T.IsClosed)
    {ι : Type*} {l : Filter ι} [NeBot l]
    {p : ι → E × F} {q : E × F}
    (hp : ∀ᶠ i in l, p i ∈ T.graph)
    (hpq : Tendsto (fun i ↦ toWeakSpace K (E × F) (p i)) l
      (𝓝 (toWeakSpace K (E × F) q))) : q ∈ T.graph := by
  have hweakMem : toWeakSpace K (E × F) q ∈
      (toWeakSpace K (E × F)) '' (T.graph : Set (E × F)) :=
    (LinearPMap.IsClosed.isClosed_toWeakSpace_graph (K := K) hT).mem_of_tendsto hpq
      (hp.mono fun i hi ↦ ⟨p i, hi, rfl⟩)
  rcases hweakMem with ⟨q', hq', hq'eq⟩
  have hqeq : q' = q := (toWeakSpace K (E × F)).injective hq'eq
  simpa [hqeq] using hq'

/-- Canonically realified weak-limit form of graph closedness. -/
theorem LinearPMap.IsClosed.mem_graph_of_tendsto_toWeakSpace_canonical
    {T : E →ₗ.[K] F} (hT : T.IsClosed)
    {ι : Type*} {l : Filter ι} [NeBot l]
    {p : ι → E × F} {q : E × F}
    (hp : ∀ᶠ i in l, p i ∈ T.graph)
    (hpq : Tendsto (fun i ↦ toWeakSpace K (E × F) (p i)) l
      (𝓝 (toWeakSpace K (E × F) q))) : q ∈ T.graph := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ K E
  haveI : IsScalarTower ℝ K E := IsScalarTower.restrictScalars ℝ K E
  letI : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ K F
  haveI : IsScalarTower ℝ K F := IsScalarTower.restrictScalars ℝ K F
  exact LinearPMap.IsClosed.mem_graph_of_tendsto_toWeakSpace (K := K) hT hp hpq

end NCG
