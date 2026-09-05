/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ProtectedPCHGraphWriter

/-!
# Finite protected Palatini--Cartan--Holst functional

The graph-writer module proves conservativity once an analytic function is
given.  Here the function itself is assembled from the finite protected
coframe/curvature and boundary contractions.  The curvature coordinates are
the output of the selected nondegenerate matrix-logarithm branch; analyticity
of those primitive branch coordinates is the local branch certificate, not an
assumption that the final PCH action is analytic.
-/

open scoped BigOperators

namespace NCG

/-- Protected scalar contractions entering a finite PCH bulk-plus-boundary
functional.  `bulkCoframe` represents the contracted `e ∧ e` coordinate,
`bulkCurvature` the selected logarithmic curvature coordinate, and the two
boundary coordinates represent the oriented normal/coframe and connection
contractions. -/
structure ProtectedPCHBranchData
    (Theta Bulk Boundary : Type*) [Fintype Bulk] [Fintype Boundary]
    [NormedAddCommGroup Theta] [NormedSpace Real Theta] where
  bulkCoefficient : Bulk -> Real
  bulkCoframe : Bulk -> Theta -> Real
  bulkCurvature : Bulk -> Theta -> Real
  boundaryCoefficient : Boundary -> Real
  boundaryFrame : Boundary -> Theta -> Real
  boundaryConnection : Boundary -> Theta -> Real
  bulkCoframe_analytic : forall i,
    AnalyticOnNhd Real (bulkCoframe i) Set.univ
  bulkCurvature_analytic : forall i,
    AnalyticOnNhd Real (bulkCurvature i) Set.univ
  boundaryFrame_analytic : forall i,
    AnalyticOnNhd Real (boundaryFrame i) Set.univ
  boundaryConnection_analytic : forall i,
    AnalyticOnNhd Real (boundaryConnection i) Set.univ

/-- The finite Palatini--Cartan--Holst bulk sum. -/
def protectedPCHBulk
    {Theta Bulk Boundary : Type*} [Fintype Bulk] [Fintype Boundary]
    [NormedAddCommGroup Theta] [NormedSpace Real Theta]
    (P : ProtectedPCHBranchData Theta Bulk Boundary) (theta : Theta) : Real :=
  ∑ i, P.bulkCoefficient i * P.bulkCoframe i theta * P.bulkCurvature i theta

/-- The finite oriented boundary/corner completion. -/
def protectedPCHBoundary
    {Theta Bulk Boundary : Type*} [Fintype Bulk] [Fintype Boundary]
    [NormedAddCommGroup Theta] [NormedSpace Real Theta]
    (P : ProtectedPCHBranchData Theta Bulk Boundary) (theta : Theta) : Real :=
  ∑ i, P.boundaryCoefficient i * P.boundaryFrame i theta *
    P.boundaryConnection i theta

/-- The complete finite protected PCH functional. -/
def protectedPCHFunctional
    {Theta Bulk Boundary : Type*} [Fintype Bulk] [Fintype Boundary]
    [NormedAddCommGroup Theta] [NormedSpace Real Theta]
    (P : ProtectedPCHBranchData Theta Bulk Boundary) (theta : Theta) : Real :=
  protectedPCHBulk P theta + protectedPCHBoundary P theta

/-- The bulk contraction sum is real analytic on the selected logarithm
branch. -/
theorem protectedPCHBulk_analytic
    {Theta Bulk Boundary : Type*} [Fintype Bulk] [Fintype Boundary]
    [NormedAddCommGroup Theta] [NormedSpace Real Theta]
    (P : ProtectedPCHBranchData Theta Bulk Boundary) :
    AnalyticOnNhd Real (protectedPCHBulk P) Set.univ := by
  classical
  change AnalyticOnNhd ℝ (fun theta => ∑ i : Bulk,
    P.bulkCoefficient i * P.bulkCoframe i theta * P.bulkCurvature i theta) Set.univ
  exact Finset.univ.analyticOnNhd_fun_sum (fun i _ =>
      (((show AnalyticOnNhd ℝ (fun _ : Theta => P.bulkCoefficient i) Set.univ
          from analyticOnNhd_const).mul (P.bulkCoframe_analytic i)).mul
        (P.bulkCurvature_analytic i)))

/-- The boundary contraction sum is real analytic on the selected branch. -/
theorem protectedPCHBoundary_analytic
    {Theta Bulk Boundary : Type*} [Fintype Bulk] [Fintype Boundary]
    [NormedAddCommGroup Theta] [NormedSpace Real Theta]
    (P : ProtectedPCHBranchData Theta Bulk Boundary) :
    AnalyticOnNhd Real (protectedPCHBoundary P) Set.univ := by
  classical
  change AnalyticOnNhd ℝ (fun theta => ∑ i : Boundary,
    P.boundaryCoefficient i * P.boundaryFrame i theta *
      P.boundaryConnection i theta) Set.univ
  exact Finset.univ.analyticOnNhd_fun_sum (fun i _ =>
      (((show AnalyticOnNhd ℝ (fun _ : Theta => P.boundaryCoefficient i) Set.univ
          from analyticOnNhd_const).mul (P.boundaryFrame_analytic i)).mul
        (P.boundaryConnection_analytic i)))

/-- `thm:SMST-PCH-graph-writer`: the PCH function is constructed as the
displayed bulk-plus-boundary sum, proved analytic from its protected branch
coordinates, and its graph extension is exactly conservative and
record-algebra preserving. -/
theorem finite_pch_graph_writer
    {Theta Bulk Boundary : Type*} [Fintype Bulk] [Fintype Boundary]
    [NormedAddCommGroup Theta] [NormedSpace Real Theta]
    (P : ProtectedPCHBranchData Theta Bulk Boundary) :
    (forall theta, protectedPCHFunctional P theta =
      protectedPCHBulk P theta + protectedPCHBoundary P theta) ∧
    AnalyticOnNhd Real
      (fun theta => (theta, protectedPCHFunctional P theta)) Set.univ ∧
    Function.Injective (protectedGraphWriter (protectedPCHFunctional P)) ∧
    (forall z, protectedGraphWriter (protectedPCHFunctional P)
      (protectedGraphDiscard z) = z) ∧
    (forall (Beta : Type*) (f : Theta -> Beta) theta,
      f (protectedGraphDiscard
        (protectedGraphWriter (protectedPCHFunctional P) theta)) = f theta) ∧
    (exists e : (Theta -> Real) ≃ₐ[Real]
        (ProtectedGraphRecord (protectedPCHFunctional P) -> Real),
      forall f theta,
        e f (protectedGraphWriter (protectedPCHFunctional P) theta) = f theta) := by
  have hg : AnalyticOnNhd Real (protectedPCHFunctional P) Set.univ :=
    (protectedPCHBulk_analytic P).add (protectedPCHBoundary_analytic P)
  have hgraph := protected_pch_graph_writer (protectedPCHFunctional P) hg
  exact ⟨fun _ => rfl, hgraph⟩

end NCG
