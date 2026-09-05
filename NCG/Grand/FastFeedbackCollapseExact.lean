/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FastFeedback

/-!
# Exact fast-feedback collapse package

This assembles the three proved branches of
`thm:fast-feedback-collapse` into one theorem: uniform collapse of the
perturbed Euler scheme, exact geometric feedback resummation, and
disappearance of an `o(h)` feedback mass at generator scale.
-/

namespace NCG

/-- The exact three-part conclusion of fast loaded feedback collapse. -/
theorem fast_feedback_collapse_exact
    {A : Type*} [NormedRing A] [CompleteSpace A]
    (h ε : ℕ → ℝ) (Ctime T : ℝ)
    (hh : ∀ m, 0 < h m) (hCtime : 0 ≤ Ctime) (hT : 0 ≤ T)
    (hε0 : ∀ m, 0 ≤ ε m)
    (hsmall : Filter.Tendsto (fun m => ε m / h m)
      Filter.atTop (nhds 0))
    (err : ℕ → ℕ → ℝ)
    (herr : ∀ m (n : ℕ), (n : ℝ) * h m ≤ T →
      err m n ≤ (n : ℝ) * (Real.exp (Ctime * h m)) ^ n * ε m)
    (B D C : A) (hD : ‖D‖ < 1)
    (kernelMass step η : ℝ) (hstep : 0 < step)
    (hvanish : kernelMass ≤ step * η) :
    (∀ δ > 0, ∃ m0, ∀ m ≥ m0, ∀ (n : ℕ),
      (n : ℝ) * h m ≤ T → err m n < δ)
    ∧ ((1 - D) * (∑' k : ℕ, D ^ k) = 1
      ∧ (∑' k : ℕ, B * D ^ k * C)
        = B * (∑' k : ℕ, D ^ k) * C)
    ∧ kernelMass / step ≤ η := by
  exact ⟨fast_feedback_uniform_collapse h ε Ctime T hh hCtime hT
      hε0 hsmall err herr,
    geometric_feedback_resummation B D C hD,
    disappearing_feedback_generator_scale kernelMass step η hstep hvanish⟩

end NCG
