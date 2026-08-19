/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Normed.Algebra.Exponential
import NCG.Grand.FiniteSourceGramConvergence

/-!
# Norm convergence of bounded semigroups

The Banach-algebra exponential is continuous.  Thus operator-norm convergence of bounded
generators gives operator-norm convergence of their exponential semigroups, even when the time
parameter moves simultaneously.  Applying the convergent exponentials to moving vectors and
finite source families gives the corresponding strong and Gram-matrix consequences.

This is the bounded functional-calculus layer used after a graph compression or a fixed Euler
resolvent approximation; genuinely unbounded generators are handled by the separate uniform
Euler-resolvent compiler.
-/

open Filter Topology

noncomputable section

namespace NCG.Semigroup

universe u v w

variable {A : Type u} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Banach-algebra exponentials preserve simultaneous convergence of the scalar time and the
bounded generator. -/
theorem exp_smul_tendsto
    {I : Type v} {l : Filter I} (aSeq : I → A) (a : A)
    (ha : Tendsto aSeq l (𝓝 a)) (cSeq : I → ℂ) (c : ℂ)
    (hc : Tendsto cSeq l (𝓝 c)) :
    Tendsto (fun i ↦ NormedSpace.exp (cSeq i • aSeq i)) l
      (𝓝 (NormedSpace.exp (c • a))) :=
  (hc.smul ha).exp

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance : NormedAlgebra ℚ (H →L[ℂ] H) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

/-- Operator-norm convergence of bounded generators implies operator-norm convergence of the
associated exponential semigroups at a fixed real time. -/
theorem boundedSemigroup_operatorNorm_tendsto
    {I : Type v} {l : Filter I} (T : I → H →L[ℂ] H) (Tlim : H →L[ℂ] H)
    (hT : Tendsto T l (𝓝 Tlim)) (t : ℝ) :
    Tendsto (fun i ↦ NormedSpace.exp ((-(t : ℂ)) • T i)) l
      (𝓝 (NormedSpace.exp ((-(t : ℂ)) • Tlim))) :=
  exp_smul_tendsto T Tlim hT (fun _ ↦ -(t : ℂ)) (-(t : ℂ)) tendsto_const_nhds

/-- The same conclusion with a simultaneously moving real time parameter. -/
theorem boundedSemigroup_operatorNorm_tendsto_of_time_tendsto
    {I : Type v} {l : Filter I} (T : I → H →L[ℂ] H) (Tlim : H →L[ℂ] H)
    (hT : Tendsto T l (𝓝 Tlim)) (t : I → ℝ) (tlim : ℝ)
    (ht : Tendsto t l (𝓝 tlim)) :
    Tendsto (fun i ↦ NormedSpace.exp ((-(t i : ℂ)) • T i)) l
      (𝓝 (NormedSpace.exp ((-(tlim : ℂ)) • Tlim))) :=
  exp_smul_tendsto T Tlim hT (fun i ↦ -(t i : ℂ)) (-(tlim : ℂ)) ht.ofReal.neg

/-- Convergent bounded semigroups applied to a convergent moving vector converge strongly. -/
theorem boundedSemigroup_apply_tendsto
    {I : Type v} {l : Filter I} (T : I → H →L[ℂ] H) (Tlim : H →L[ℂ] H)
    (hT : Tendsto T l (𝓝 Tlim)) (t : I → ℝ) (tlim : ℝ)
    (ht : Tendsto t l (𝓝 tlim)) (x : I → H) (xlim : H)
    (hx : Tendsto x l (𝓝 xlim)) :
    Tendsto (fun i ↦ NormedSpace.exp ((-(t i : ℂ)) • T i) (x i)) l
      (𝓝 (NormedSpace.exp ((-(tlim : ℂ)) • Tlim) xlim)) := by
  exact (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
    ((boundedSemigroup_operatorNorm_tendsto_of_time_tendsto
      T Tlim hT t tlim ht).prodMk_nhds hx)

/-- Every finite source Gram matrix propagated by a norm-convergent bounded semigroup converges. -/
theorem boundedSemigroup_sourceGram_tendsto
    {ι : Type*}
    (T : ℕ → H →L[ℂ] H) (Tlim : H →L[ℂ] H)
    (hT : Tendsto T atTop (𝓝 Tlim)) (t : ℕ → ℝ) (tlim : ℝ)
    (ht : Tendsto t atTop (𝓝 tlim)) (x : ℕ → ι → H) (xlim : ι → H)
    (hx : ∀ j, Tendsto (fun n ↦ x n j) atTop (𝓝 (xlim j))) :
    Tendsto
      (fun n ↦ NCG.SpectralApproximation.sourceGram
        (NormedSpace.exp ((-(t n : ℂ)) • T n)) (x n)) atTop
      (𝓝 (NCG.SpectralApproximation.sourceGram
        (NormedSpace.exp ((-(tlim : ℂ)) • Tlim)) xlim)) := by
  exact NCG.SpectralApproximation.sourceGram_tendsto
    (boundedSemigroup_operatorNorm_tendsto_of_time_tendsto T Tlim hT t tlim ht) hx

end NCG.Semigroup
