/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The diamond pair is a linear-curvature datum
  (`prop:diamond-linear-datum`, GR_emergence)

The diamond response is degree one in the Riemann tensor, while the
Wilson triple `(c₁,c₂,c₃)` multiplies the curvature-squared basis
`{R², Ric², Weyl²}`, which is degree two:

* `curvature_degree_separation` — a linear-curvature functional
  that agrees with a curvature-squared functional under every
  curvature rescaling `Riem ↦ t·Riem` has all coefficients zero:
  degree-one and degree-two responses share no nonzero datum;
* `linear_datum_not_wilson` — hence the diamond coefficients
  `(α_R, α_{R_uu})` cannot reproduce a nonzero Wilson triple.

The Riemann-normal-coordinate volume-expansion input (the
curvature-squared sector first enters at `O(|x|⁴)`, absent at the
cited truncation) is the declared geometric layer.
-/

namespace NCG

/-- Degree separation: if a linear-in-curvature response equals a
curvature-squared response under every rescaling `Riem ↦ t·Riem`,
then every coefficient on both sides vanishes. -/
theorem curvature_degree_separation
    (aR aRuu c1 c2 c3 : ℝ)
    (h : ∀ t R Ruu R2 Ric2 W2 : ℝ,
      aR * (t * R) + aRuu * (t * Ruu)
        = c1 * (t ^ 2 * R2) + c2 * (t ^ 2 * Ric2)
          + c3 * (t ^ 2 * W2)) :
    (aR = 0 ∧ aRuu = 0) ∧ (c1 = 0 ∧ c2 = 0 ∧ c3 = 0) := by
  have hR := h 1 1 0 0 0 0
  have hRuu := h 1 0 1 0 0 0
  have hc1 := h 1 0 0 1 0 0
  have hc2 := h 1 0 0 0 1 0
  have hc3 := h 1 0 0 0 0 1
  norm_num at hR hRuu hc1 hc2 hc3
  exact ⟨⟨hR, hRuu⟩, hc1.symm, hc2.symm, hc3.symm⟩

/-- `prop:diamond-linear-datum`: a degree-one curvature datum
cannot be a nonzero Wilson triple — if the diamond response
reproduced `(c₁,c₂,c₃)·{R²,Ric²,Weyl²}` under curvature rescaling,
the triple would vanish. -/
theorem linear_datum_not_wilson (aR aRuu c1 c2 c3 : ℝ)
    (hnz : c1 ≠ 0 ∨ c2 ≠ 0 ∨ c3 ≠ 0) :
    ¬ ∀ t R Ruu R2 Ric2 W2 : ℝ,
      aR * (t * R) + aRuu * (t * Ruu)
        = c1 * (t ^ 2 * R2) + c2 * (t ^ 2 * Ric2)
          + c3 * (t ^ 2 * W2) := by
  intro h
  obtain ⟨-, hc1, hc2, hc3⟩ := curvature_degree_separation
    aR aRuu c1 c2 c3 h
  rcases hnz with h1 | h2 | h3
  · exact h1 hc1
  · exact h2 hc2
  · exact h3 hc3

end NCG
