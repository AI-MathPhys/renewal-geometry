/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertResolventObjective

/-!
# Sharp operator bounds from the resolvent energy identity

For a nonnegative extended form, the Euler energy identity alone makes every positive-shift
resolvent a contraction after multiplication by the shift.  In particular, stage-uniform bounds
need not be included as separate data in Mosco converse theorems.
-/

open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]

/-- The Euler energy identity for a nonnegative extended form gives the sharp pointwise
resolvent estimate. -/
theorem ennrealResolvent_norm_le_inv_mul
    (q : E → ENNReal) (T : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (henergy : ∀ f : E,
      (q (T f)).toReal + lam * ‖T f‖ ^ 2 =
        RCLike.re (inner K (T f) f))
    (f : E) :
    ‖T f‖ ≤ (1 / lam) * ‖f‖ := by
  have hre : RCLike.re (inner K (T f) f) ≤ ‖T f‖ * ‖f‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm (T f) f)
  have hq : 0 ≤ (q (T f)).toReal := ENNReal.toReal_nonneg
  have hquad : lam * ‖T f‖ ^ 2 ≤ ‖T f‖ * ‖f‖ := by
    nlinarith [henergy f]
  by_cases hzero : ‖T f‖ = 0
  · rw [hzero]
    positivity
  have hpos : 0 < ‖T f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
  have hlinear : lam * ‖T f‖ ≤ ‖f‖ := by
    nlinarith
  calc
    ‖T f‖ ≤ ‖f‖ / lam := (le_div_iff₀ hlam).2 (by simpa [mul_comm] using hlinear)
    _ = (1 / lam) * ‖f‖ := by ring

/-- Every positive-shift resolvent satisfying the Euler energy identity has operator norm at
most the inverse shift. -/
theorem ennrealResolvent_opNorm_le_inv
    (q : E → ENNReal) (T : E →L[K] E)
    (lam : ℝ) (hlam : 0 < lam)
    (henergy : ∀ f : E,
      (q (T f)).toReal + lam * ‖T f‖ ^ 2 =
        RCLike.re (inner K (T f) f)) :
    ‖T‖ ≤ 1 / lam := by
  apply T.opNorm_le_bound
  · positivity
  intro f
  exact ennrealResolvent_norm_le_inv_mul q T lam hlam henergy f

end NCG.VaryingHilbert
