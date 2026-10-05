/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.OperationalEntranceCategory
import RenewalGeometry.Predictive.TypedStateFactorization
import RenewalGeometry.Gravity.FastClockBound

/-!
# Relative primitive-basis minimality with the complete (R1) inputs
  (`thm:supp-relative-primitive-floor`, emergent-spacetime manuscript)

`OperationalEntrance.relative_primitive_floor` proves (R2)–(R4) and the own part of (R1) over
the anchored entrance groupoid.  The (R1) sufficiency proof additionally cites
`cor:supp-derived-state-machine` (the product formula along the derived quotient state path)
and `lem:supp-fast-clock` (the absolute kinetic scale on the ADM branch).  Both are now proved
(`TypedStateMachine.derived_state_machine`, `FastClock.fast_clock_bound`,
`FastClock.fast_clock_collapse`); `relative_primitive_floor_complete` bundles them:

* the full statement of `relative_primitive_floor`;
* for every anchored grammar and every model `M`, the predictive row `ℙ⁺ = M.law` yields the
  derived state machine on `Z^min` — `κ_{X,a}`, `T_{X,a}` well defined (positive-probability
  branch) and `p_X(w | h) = ∏_j κ_{X,a_j}(z_{j-1})`;
* the fast-clock bound `∑_a (k_a^+ + k_a^-) ≥ 3c/(R²h²)` for every finite root family.
-/

namespace RenewalGeometry
namespace RelativePrimitiveFloorComplete

open FiniteTypedEventGrammar OperationalEntrance

/-- `thm:supp-relative-primitive-floor`, with the (R1) sufficiency inputs
`cor:supp-derived-state-machine` and `lem:supp-fast-clock` included. -/
theorem relative_primitive_floor_complete :
    (type_of% @relative_primitive_floor) ∧
    (∀ (𝔊 : AnchoredGrammar) (M : Model 𝔊),
      (∀ {x y : 𝔊.grammar.CutType} (a : 𝔊.grammar.Letter x y) {h h' : 𝔊.grammar.History x},
          M.law.project h = M.law.project h' → M.law.prob h.word a = M.law.prob h'.word a) ∧
      (∀ {x y : 𝔊.grammar.CutType} (a : 𝔊.grammar.Letter x y) {h h' : 𝔊.grammar.History x}
          (_hh : M.law.project h = M.law.project h') (hpos : 0 < M.law.prob h.word a)
          (hpos' : 0 < M.law.prob h'.word a),
          M.law.project (h.snoc a (M.law.admissible_of_prob_pos hpos))
            = M.law.project (h'.snoc a (M.law.admissible_of_prob_pos hpos'))) ∧
      (∀ {x z : 𝔊.grammar.CutType} (h : 𝔊.grammar.History x)
          (w : TypedWord 𝔊.grammar.Letter x z),
          M.law.wordProb h.word w
            = (TypedStateMachine.stateFactors M.law (some (M.law.project h)) w).prod)) ∧
    (∀ {ι : Type} [Fintype ι] (h c R : ℝ) (kp km : ι → ℝ) (r : ι → Fin 3 → ℝ),
      0 < h → 0 < R → (∀ a, 0 ≤ kp a) → (∀ a, 0 ≤ km a) →
      (∀ a, ∑ i, r a i ^ 2 ≤ R ^ 2) →
      (∀ v : Fin 3 → ℝ, c * (∑ i, v i ^ 2)
        ≤ dotProduct v (Matrix.mulVec (FastClock.bracket h kp km r) v)) →
      3 * c / (R ^ 2 * h ^ 2) ≤ ∑ a, (kp a + km a)) :=
  ⟨relative_primitive_floor,
    fun _ M => TypedStateMachine.derived_state_machine M.law,
    fun h c R kp km r hh hR hkp hkm hr hB =>
      FastClock.fast_clock_bound h c R kp km r hh hR hkp hkm hr hB⟩

end RelativePrimitiveFloorComplete
end RenewalGeometry
