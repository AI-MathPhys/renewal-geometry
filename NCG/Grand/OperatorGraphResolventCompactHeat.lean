/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphResolventEulerFunctionalCalculus
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compact heat operators from one compact graph resolvent

Compactness of one positive-shift graph resolvent propagates to every positive shift by the
second resolvent identity.  Hence every actual implicit-Euler power is compact.  Their
operator-norm convergence to the canonical one-resolvent heat calculus and closedness of compact
operators then make every positive-time heat operator compact.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert

universe v w

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

omit [CompleteSpace E] in
/-- Compactness of one positive-shift weak graph resolvent propagates to every positive shift. -/
theorem operatorGraphResolvent_isCompact_of_oneShift
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (R : ℝ → E →L[ℂ] E)
    (hequation : ∀ lam, 0 < lam → ∀ f : E,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (b : ℝ) (hb : 0 < b) (hcompact : IsCompactOperator (R b)) :
    ∀ a, 0 < a → IsCompactOperator (R a) := by
  intro a ha
  have hid := operatorGraph_secondResolventIdentity
    D A R hequation a b ha hb
  have hcomp : IsCompactOperator ((R a).comp (R b)) :=
    hcompact.clm_comp (R a)
  have hdiff : IsCompactOperator (R a - R b) := by
    rw [hid]
    exact hcomp.smul (((b - a : ℝ) : ℂ))
  have hreconstruct : R a = (R a - R b) + R b := by abel
  rw [hreconstruct]
  exact hdiff.add hcompact

/-- Every positive-time canonical heat operator is compact when one reference graph resolvent is
compact. -/
theorem operatorGraphResolventHeat_isCompact_of_oneShift
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (R : ℝ → E →L[ℂ] E)
    (hequation : ∀ lam, 0 < lam → ∀ f : E,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (b t : ℝ) (hb : 0 < b) (ht : 0 < t)
    (hcompact : IsCompactOperator (R b)) :
    IsCompactOperator (operatorGraphResolventHeat (R b) b t) := by
  apply isCompactOperator_of_tendsto
    (tendsto_scaled_operatorGraphResolvent_succ_pow_heat
      D A R hequation b t hb ht)
  apply Filter.Eventually.of_forall
  intro m
  let T : E →L[ℂ] E :=
    (((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
      R (((m + 1 : ℕ) : ℝ) / t)
  have hmShift : 0 < ((m + 1 : ℕ) : ℝ) / t :=
    div_pos (by positivity) ht
  have hRcompact : IsCompactOperator
      (R (((m + 1 : ℕ) : ℝ) / t)) :=
    operatorGraphResolvent_isCompact_of_oneShift
      D A R hequation b hb hcompact _ hmShift
  have hTcompact : IsCompactOperator T :=
    hRcompact.smul (((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ))
  change IsCompactOperator (T ^ (m + 1))
  rw [pow_succ, ContinuousLinearMap.mul_def]
  exact hTcompact.clm_comp (T ^ m)

end NCG.VaryingHilbert
