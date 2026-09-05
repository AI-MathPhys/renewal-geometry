/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.EntropicHodgeContinuumExact
import NCG.Grand.PrimitiveInformationGeometryExact

/-!
# Hessian of the primitive routed entropy action

This file supplies the model-specific Hessian clause in
`thm:entropic-Hodge-continuum`.  The edge action is the actual Bregman/KL
action of the primitive exponential family along the routed physical
coordinate difference.  Its first variation is the expectation-coordinate
difference, and its second variation at the primitive law is exactly the
`G₀` quadratic form.  Finite edge summation then gives the routed Hodge form
without a per-edge Hessian hypothesis.
-/

open Finset Matrix

noncomputable section

namespace NCG
namespace PrimitiveRoutedEntropy

/-- The primitive entropic action along a routed physical-coordinate
difference `v`.  By the exact Bregman identity this is
`D(p₀ || p_{s v})`. -/
def edgeAction (v : Fin 3 → ℝ) (s : ℝ) : ℝ :=
  primitiveLogPartition (primitiveParameterLine 0 v s) -
    primitiveLogPartition 0 - s * (v ⬝ᵥ primitiveExpectation 0)

/-- First variation of the primitive routed edge action. -/
def edgeFirstVariation (v : Fin 3 → ℝ) (s : ℝ) : ℝ :=
  v ⬝ᵥ primitiveExpectation (primitiveParameterLine 0 v s) -
    v ⬝ᵥ primitiveExpectation 0

theorem edgeAction_hasDerivAt (v : Fin 3 → ℝ) (s : ℝ) :
    HasDerivAt (edgeAction v) (edgeFirstVariation v s) s := by
  exact primitiveBregmanSegment_line_hasDerivAt 0 v s

theorem edgeFirstVariation_hasDerivAt (v : Fin 3 → ℝ) (s : ℝ) :
    HasDerivAt (edgeFirstVariation v)
      (fisherQuadratic (primitiveFisher (primitiveParameterLine 0 v s)) v) s := by
  exact (primitiveExpectationPairing_line_hasDerivAt 0 v s).sub_const
    (v ⬝ᵥ primitiveExpectation 0)

/-- At the primitive law, the second variation is the exact baseline
physical Fisher quadratic form `⟨v,G₀v⟩`. -/
theorem edgeFirstVariation_hasDerivAt_zero (v : Fin 3 → ℝ) :
    HasDerivAt (edgeFirstVariation v)
      (fisherQuadratic primitivePhysicalGram v) 0 := by
  simpa [primitiveParameterLine_zero, primitiveFisher_zero_eq_physicalGram]
    using edgeFirstVariation_hasDerivAt v 0

variable {E : Type*} [Fintype E]

/-- The finite routed primitive entropy action, with edge conductances
`κ e` and routed coordinate differences `d e`. -/
def routedAction (κ : E → ℝ) (d : E → Fin 3 → ℝ) (s : ℝ) : ℝ :=
  ∑ e, κ e * edgeAction (d e) s

/-- First variation of the finite routed primitive entropy action. -/
def routedFirstVariation (κ : E → ℝ) (d : E → Fin 3 → ℝ) (s : ℝ) : ℝ :=
  ∑ e, κ e * edgeFirstVariation (d e) s

/-- The routed baseline Hodge quadratic form
`Σ_e κ_e ⟨d_e,G₀d_e⟩`. -/
def routedHodgeForm (κ : E → ℝ) (d : E → Fin 3 → ℝ) : ℝ :=
  ∑ e, κ e * fisherQuadratic primitivePhysicalGram (d e)

theorem routedAction_hasDerivAt
    (κ : E → ℝ) (d : E → Fin 3 → ℝ) (s : ℝ) :
    HasDerivAt (routedAction κ d) (routedFirstVariation κ d s) s := by
  exact HasDerivAt.fun_sum fun e _ =>
    (edgeAction_hasDerivAt (d e) s).const_mul (κ e)

/-- **Exact Hessian clause of `thm:entropic-Hodge-continuum`.**  The second
variation of the actual finite routed primitive entropy action is the routed
`G₀` Hodge form, with no local-Hessian assumption. -/
theorem routedAction_secondVariation_at_primitive
    (κ : E → ℝ) (d : E → Fin 3 → ℝ) :
    (∀ s, HasDerivAt (routedAction κ d) (routedFirstVariation κ d s) s) ∧
      HasDerivAt (routedFirstVariation κ d) (routedHodgeForm κ d) 0 := by
  constructor
  · exact routedAction_hasDerivAt κ d
  · exact HasDerivAt.fun_sum fun e _ =>
      (edgeFirstVariation_hasDerivAt_zero (d e)).const_mul (κ e)

end PrimitiveRoutedEntropy
end NCG
