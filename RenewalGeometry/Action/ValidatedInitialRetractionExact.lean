/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.InitialConstraintRetractionExact

/-!
# Validated constraint evaluation with an explicit error budget
  (`cor:validated-initial-retraction`, Einstein–SM action closure)

Setting: an exact finite-dimensional constraint reduction
`R : ExactInitialConstraintReduction Ck x0 m r B` (`def:exact-initial-reduction`)
with exact retained map `Φ_h = R.retained`, together with an *evaluated* `C¹`
reduced map `Φ̃_h : ℝ^{m_h} → ℝ^{m_h}` and its frozen derivative
`Ã_h = D_λΦ̃_h(x_h, 0)` (derivatives taken within the correction ball
`|λ| ≤ r_*`, where the maps are `C¹`).

* `validatedInitialRetraction` — under the margins
  `eq:validated-initial-margins` (`σ_min(Ã_h) ≥ γ_*`, rendered as
  `γ_* ‖v‖ ≤ ‖Ã_h v‖`; `‖DΦ̃_h - Ã_h‖ ≤ γ_*/4`; `‖DΦ_h - DΦ̃_h‖ ≤ γ_*/4`;
  `|Φ_h(0) - Φ̃_h(0)| ≤ ζ₀`) and the budget `eq:validated-initial-budget`
  (`β^eff = |Φ̃_h(0)| + ζ₀`, `2γ_*⁻¹β^eff ≤ r_*`), the exact reduced map has a
  unique zero in the closed ball of radius `2γ_*⁻¹β^eff`, and the corrected
  datum lies in the exact constraint set with displacement at most
  `2B_*γ_*⁻¹β^eff`.  Proof as in the paper: the triangle inequality gives
  `‖DΦ_h - Ã_h‖ ≤ γ_*/2` and `|Φ_h(0)| ≤ β^eff`, and
  `initialConstraintRetraction` (`prop:initial-constraint-retraction`) is
  applied to the exact map with the frozen matrix `Ã_h`.

Scoped hypothesis disclosed: `0 ≤ B_*` (implicit for a Lipschitz constant).
The `C¹` regularity of `Φ̃_h` is recorded as a hypothesis but not needed by
the argument.
-/

namespace RenewalGeometry

open Metric

section ValidatedInitialRetraction

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

/-- `cor:validated-initial-retraction`: with an evaluated `C¹` reduced map
`Φ̃_h`, frozen matrix `Ã_h = DΦ̃_h(0)` satisfying `σ_min(Ã_h) ≥ γ_*`, the
derivative margins `‖DΦ̃_h(λ) - Ã_h‖ ≤ γ_*/4`, `‖DΦ_h(λ) - DΦ̃_h(λ)‖ ≤ γ_*/4`
on the correction ball, the evaluation error `|Φ_h(0) - Φ̃_h(0)| ≤ ζ₀` and the
budget `2γ_*⁻¹β^eff ≤ r_*` with `β^eff = |Φ̃_h(0)| + ζ₀`, the retraction and
displacement conclusions of `prop:initial-constraint-retraction` hold for the
exact map with `β^eff` in place of `β_h`. -/
theorem validatedInitialRetraction {Ck : X → Y} {x0 : X} {m : ℕ} {r B : ℝ}
    (R : ExactInitialConstraintReduction Ck x0 m r B)
    (Φt : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (_hΦt : ContDiffOn ℝ 1 Φt (closedBall 0 r)) {γ ζ₀ : ℝ} (hγ : 0 < γ)
    (hA : ∀ v, γ * ‖v‖ ≤ ‖fderivWithin ℝ Φt (closedBall 0 r) 0 v‖)
    (hmarginEval : ∀ l ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) r,
      ‖fderivWithin ℝ Φt (closedBall 0 r) l - fderivWithin ℝ Φt (closedBall 0 r) 0‖ ≤ γ / 4)
    (hmarginExact : ∀ l ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) r,
      ‖fderivWithin ℝ R.retained (closedBall 0 r) l - fderivWithin ℝ Φt (closedBall 0 r) l‖ ≤
        γ / 4)
    (hζ : ‖R.retained 0 - Φt 0‖ ≤ ζ₀)
    (hrad : 2 * γ⁻¹ * (‖Φt 0‖ + ζ₀) ≤ r) (hB : 0 ≤ B) :
    (∃! l, l ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) (2 * γ⁻¹ * (‖Φt 0‖ + ζ₀)) ∧
        R.retained l = 0) ∧
      ∀ l ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) (2 * γ⁻¹ * (‖Φt 0‖ + ζ₀)),
        R.retained l = 0 →
          Ck (R.corr l) = 0 ∧ ‖R.corr l - x0‖ ≤ 2 * B * γ⁻¹ * (‖Φt 0‖ + ζ₀) := by
  refine initialConstraintRetraction R (fderivWithin ℝ Φt (closedBall 0 r) 0) hγ hA ?_ ?_ hrad hB
  · intro l hl
    calc ‖fderivWithin ℝ R.retained (closedBall 0 r) l - fderivWithin ℝ Φt (closedBall 0 r) 0‖
        = ‖(fderivWithin ℝ R.retained (closedBall 0 r) l - fderivWithin ℝ Φt (closedBall 0 r) l)
            + (fderivWithin ℝ Φt (closedBall 0 r) l - fderivWithin ℝ Φt (closedBall 0 r) 0)‖ := by
          congr 1; abel
      _ ≤ γ / 4 + γ / 4 := (norm_add_le _ _).trans (add_le_add (hmarginExact l hl)
          (hmarginEval l hl))
      _ = γ / 2 := by ring
  · calc ‖R.retained 0‖ = ‖Φt 0 + (R.retained 0 - Φt 0)‖ := by congr 1; abel
      _ ≤ ‖Φt 0‖ + ‖R.retained 0 - Φt 0‖ := norm_add_le _ _
      _ ≤ ‖Φt 0‖ + ζ₀ := by linarith

end ValidatedInitialRetraction

end RenewalGeometry
