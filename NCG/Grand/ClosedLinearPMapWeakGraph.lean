/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Weak closedness of closed unbounded-operator graphs

The graph of a partial linear map is convex.  The Hahn--Banach weak-closure theorem therefore
upgrades norm closedness of the graph to closedness in the weak topology.  This is the key
topological input for lower semicontinuity of closed-operator graph energies.
-/

open Set Topology

noncomputable section

namespace NCG

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace K F]

/-- A norm-closed linear graph is closed after transporting it to the weak topology. -/
theorem LinearPMap.IsClosed.isClosed_toWeakSpace_graph
    [NormedSpace ℝ E] [IsScalarTower ℝ K E]
    [NormedSpace ℝ F] [IsScalarTower ℝ K F]
    {T : E →ₗ.[K] F} (hT : T.IsClosed) :
    IsClosed ((toWeakSpace K (E × F)) '' (T.graph : Set (E × F))) := by
  have hconvex : Convex ℝ (T.graph : Set (E × F)) :=
    (T.graph.restrictScalars ℝ).convex
  rw [← closure_eq_iff_isClosed]
  rw [← hconvex.toWeakSpace_closure K, hT.closure_eq]

/-- Canonically realified form of weak closedness for real or complex normed spaces. -/
theorem LinearPMap.IsClosed.isClosed_toWeakSpace_graph_canonical
    {T : E →ₗ.[K] F} (hT : T.IsClosed) :
    IsClosed ((toWeakSpace K (E × F)) '' (T.graph : Set (E × F))) := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ K E
  haveI : IsScalarTower ℝ K E := IsScalarTower.restrictScalars ℝ K E
  letI : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ K F
  haveI : IsScalarTower ℝ K F := IsScalarTower.restrictScalars ℝ K F
  exact LinearPMap.IsClosed.isClosed_toWeakSpace_graph (K := K) hT

end NCG
