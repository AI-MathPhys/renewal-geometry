/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Packet selection
  (`lemma:packet-selection`, arithmetic monograph)

For every `s₀ = α + iγ` with `α > 0` there is a fixed smooth,
compactly supported packet `C` with `H_C(s₀) = ∫ C(u)e^{s₀u} du ≠ 0`.
The manuscript's construction: take a nonnegative nonzero bump `φ`
and set `C(u) = e^{−iγu}φ(u)`, so that
`H_C(s₀) = ∫ φ(u)e^{αu} du > 0`.

(The hypothesis `α > 0` is not needed for the argument — the same
packet works for every real `α` — but it is kept to match the
manuscript statement.)
-/

open MeasureTheory Complex

namespace NCG

/-- `lemma:packet-selection`: for every `s₀` with `Re s₀ > 0` there
is a smooth compactly supported packet `C` with
`H_C(s₀) = ∫ C(u)e^{s₀u} du ≠ 0`. -/
theorem packet_selection (s₀ : ℂ) (_hα : 0 < s₀.re) :
    ∃ C : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) C ∧ HasCompactSupport C ∧
      (∫ u : ℝ, C u * Complex.exp (s₀ * u)) ≠ 0 := by
  classical
  set φ : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
    with hφ
  refine ⟨fun u => (φ u : ℂ) *
    Complex.exp (-(s₀.im : ℂ) * Complex.I * u), ?_, ?_, ?_⟩
  · -- smoothness
    have h1 : ContDiff ℝ (⊤ : ℕ∞) fun u : ℝ => ((φ u : ℝ) : ℂ) :=
      ContDiff.comp Complex.ofRealCLM.contDiff φ.contDiff
    have h0 : ContDiff ℝ (⊤ : ℕ∞) fun u : ℝ => ((u : ℝ) : ℂ) :=
      Complex.ofRealCLM.contDiff
    have h2 : ContDiff ℝ (⊤ : ℕ∞) fun u : ℝ =>
        Complex.exp (-(s₀.im : ℂ) * Complex.I * u) :=
      ContDiff.comp Complex.contDiff_exp
        (ContDiff.mul contDiff_const h0)
    exact ContDiff.mul h1 h2
  · -- compact support
    have h1 : HasCompactSupport fun u : ℝ => ((φ u : ℝ) : ℂ) :=
      φ.hasCompactSupport.comp_left Complex.ofReal_zero
    exact h1.mul_right
  · -- the packet transform is a positive real integral
    have hmerge : ∀ u : ℝ,
        ((φ u : ℝ) : ℂ) * Complex.exp (-(s₀.im : ℂ) * Complex.I * u)
            * Complex.exp (s₀ * u)
          = ((φ u * Real.exp (s₀.re * u) : ℝ) : ℂ) := by
      intro u
      have h1 : (-(s₀.im : ℂ) * Complex.I * u) + s₀ * u
          = (s₀.re : ℂ) * u := by
        linear_combination (-(u : ℂ)) * (Complex.re_add_im s₀)
      rw [show ((φ u : ℝ) : ℂ)
            * Complex.exp (-(s₀.im : ℂ) * Complex.I * u)
            * Complex.exp (s₀ * u)
          = ((φ u : ℝ) : ℂ)
            * (Complex.exp (-(s₀.im : ℂ) * Complex.I * u)
              * Complex.exp (s₀ * u)) from by ring,
        ← Complex.exp_add, h1]
      push_cast
      ring
    have hconv : (∫ u : ℝ, ((φ u : ℝ) : ℂ)
          * Complex.exp (-(s₀.im : ℂ) * Complex.I * u)
          * Complex.exp (s₀ * u))
        = ((∫ u : ℝ, φ u * Real.exp (s₀.re * u) : ℝ) : ℂ) := by
      simp only [hmerge]
      rw [← RCLike.ofReal_eq_complex_ofReal]
      exact integral_ofReal
    rw [hconv]
    refine Complex.ofReal_ne_zero.mpr (ne_of_gt ?_)
    have hnn : (0 : ℝ → ℝ) ≤ fun u => φ u * Real.exp (s₀.re * u) :=
      fun u => mul_nonneg (φ.nonneg' u) (Real.exp_pos _).le
    have hint : Integrable fun u : ℝ => φ u * Real.exp (s₀.re * u) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · exact φ.continuous.mul (by fun_prop)
      · exact φ.hasCompactSupport.mul_right
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    have hsupp : (Function.support fun u : ℝ =>
        φ u * Real.exp (s₀.re * u)) = Metric.ball (0 : ℝ) 2 := by
      have hs2 : Function.support φ = Metric.ball (0 : ℝ) 2 := by
        rw [φ.support_eq]
      rw [← hs2]
      ext u
      simp [Function.mem_support, Real.exp_ne_zero]
    rw [hsupp]
    exact Metric.measure_ball_pos _ _ (by norm_num)

end NCG
