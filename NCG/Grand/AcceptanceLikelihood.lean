/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The acceptance bit is the unique state-independent likelihood
  coordinate (`cor:acceptance-likelihood`, Gran-Tensor
  manuscript)

* `acceptance_likelihood`: if the exponentially reweighted
  partition operator over a linearly independent accepted-effect
  family is scalar (proportional to the total effect) on a
  nonempty open interval of tilts, then all accepted scores are
  equal.

Rendering disclosed: "scalar partition function" is rendered by
proportionality to the summed effect (`Σ E_j = I` on the
accepted block); the normalization "s(∅)=0, s(j)=1 up to affine
gauge" is the manuscript's affine-gauge reading of the proved
equal-scores conclusion.
-/

namespace NCG

/-- `cor:acceptance-likelihood`. -/
theorem acceptance_likelihood {J : Type*} [Fintype J]
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (E : J → V) (hlin : LinearIndependent ℝ E)
    (s : J → ℝ) (a b : ℝ) (hab : a < b) (w : ℝ → ℝ)
    (hscalar : ∀ q ∈ Set.Ioo a b,
      ∑ j, Real.exp (q * s j) • E j = w q • ∑ j, E j) :
    ∀ j k, s j = s k := by
  -- pick a nonzero tilt in the interval
  obtain ⟨q, hq, hq0⟩ : ∃ q ∈ Set.Ioo a b, q ≠ 0 := by
    by_cases h0 : (a + b) / 2 = 0
    · refine ⟨b / 2, ⟨by linarith, by linarith⟩, ?_⟩
      have hb : 0 < b := by linarith
      positivity
    · exact ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, h0⟩
  have h := hscalar q hq
  rw [Finset.smul_sum] at h
  have hzero : ∑ j, (Real.exp (q * s j) - w q) • E j = 0 := by
    rw [show (fun j => (Real.exp (q * s j) - w q) • E j)
        = fun j => Real.exp (q * s j) • E j - w q • E j from by
      funext j
      rw [sub_smul]]
    rw [Finset.sum_sub_distrib, h, sub_self]
  have hcoeff : ∀ j, Real.exp (q * s j) - w q = 0 := by
    have hli := Fintype.linearIndependent_iff.mp hlin
    exact hli _ hzero
  intro j k
  have hj := hcoeff j
  have hk := hcoeff k
  have hexp : Real.exp (q * s j) = Real.exp (q * s k) := by
    linarith
  have hqs : q * s j = q * s k := Real.exp_injective hexp
  exact mul_left_cancel₀ hq0 hqs

end NCG
