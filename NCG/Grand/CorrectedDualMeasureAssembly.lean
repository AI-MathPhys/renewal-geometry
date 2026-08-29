/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CorrectedDualMeasureCriterion

/-!
# Correct dual-line and independent-measure assembly

This file packages the finite graph-line sign table with the independent
measure cancellation criterion and strengthens the real/Pfaffian endpoint:
global triviality is equivalent to the absence of every negative protected
loop, rather than merely unfolding a definition.
-/

namespace NCG
namespace CorrectedDualMeasureCriterion

/-- On a locally real Pfaffian branch, global triviality is equivalent to the
absence of a negative sign holonomy on every protected loop. -/
theorem realPfaffian_global_trivial_iff_no_negative
    {Tangent TwoForm Loop : Type*}
    (line : RealPfaffianMeasureLine Tangent TwoForm Loop)
    (_hlocal : LocallyRealPfaffian line) :
    GloballyTrivialRealLine line ↔
      ¬ ∃ loop, line.signHolonomy loop = true := by
  constructor
  · intro hglobal hnegative
    obtain ⟨loop, hloop⟩ := hnegative
    have := hglobal loop
    rw [hloop] at this
    contradiction
  · intro hnone loop
    cases h : line.signHolonomy loop with
    | false => rfl
    | true => exact False.elim (hnone ⟨loop, h⟩)

/-- The complete line-level consequence: a repeated Nambu/transpose copy
cannot cancel a nonzero phase response, while an independently sourced dual
factor cancels both the connection and all protected holonomies. -/
theorem independent_dual_not_nambu_certificate
    {Tangent Loop : Type*}
    (line : ComplexMeasureLine Tangent Loop)
    (x : Tangent) (hresponse : line.connection x ≠ 0) :
    PhaseTrivial (tensorMeasureLine line (dualMeasureLine line))
      ∧ ¬ PhaseTrivial (tensorMeasureLine line line) := by
  exact ⟨independent_dual_factor_cancels line,
    repeated_nambu_line_does_not_cancel line x hresponse⟩

/-- Exact graph-line sign table, including curvature, vertical moment, and
protected periods, assembled with the scalar transpose counterexample. -/
theorem corrected_dual_graph_line_exact
    {E F I X TwoForm Vertical Loop : Type*}
    [Fintype E] [Fintype F] [Fintype I]
    (calculus : GraphDifferentialCalculus X TwoForm Vertical Loop)
    (weight : I → ℝ)
    (A B : X → I → Matrix F E ℂ) :
    GraphLineEquivalent
        (graphPhaseLine calculus
          (weightedGraphConnection weight (conjugateFamily A)
            (conjugateFamily B)))
        (dualGraphPhaseLine
          (graphPhaseLine calculus (weightedGraphConnection weight A B)))
      ∧ GraphLineEquivalent
        (graphPhaseLine calculus
          (weightedGraphConnection weight (transposeDualFamily A)
            (transposeDualFamily B)))
        (graphPhaseLine calculus (weightedGraphConnection weight A B))
      ∧ (weightedGraphConnection
        (E := Fin 1) (F := Fin 1) (I := Fin 1) (X := Unit)
        (fun _ => (1 : ℝ))
        (fun _ _ => (1 : Matrix (Fin 1) (Fin 1) ℂ))
        (fun _ _ => Complex.I •
          (1 : Matrix (Fin 1) (Fin 1) ℂ))) () = 1 := by
  exact ⟨conjugateGraphLine_equivalent_dual calculus weight A B,
    transposeDualGraphLine_equivalent_original calculus weight A B,
    scalar_phase_tangent_graphConnection⟩

end CorrectedDualMeasureCriterion
end NCG
