/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealResolventEnvelopeLiminf

/-!
# ENNReal resolvent-envelope determination from duality

This is the extended-valued analogue of shifted Fenchel--Moreau determination.  Strict finite
lower levels handle finite and infinite form values uniformly.
-/

open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]

/-- Every strict finite lower level of a shifted extended form is witnessed by a finite dual
resolvent envelope. -/
def HasENNRealResolventEnvelopeDuality
    (q : E → ENNReal) (F : ℝ → E → ℝ) : Prop :=
  ∀ lam : ℝ, 0 < lam → ∀ x : E, ∀ r : ℝ,
    ENNReal.ofReal r < q x → ∃ f : E,
      r ≤ F lam f + 2 * RCLike.re (inner K x f) - lam * ‖x‖ ^ 2

/-- Shifted ENNReal envelope duality implies the determination predicate used by the strong
resolvent Mosco converse. -/
theorem HasENNRealResolventEnvelopeDuality.isDeterminedByENNRealResolventEnvelopes
    {q : E → ENNReal} {F : ℝ → E → ℝ}
    (hdual : HasENNRealResolventEnvelopeDuality (K := K) q F) :
    IsDeterminedByENNRealResolventEnvelopes (K := K) q F := by
  intro x C hC a ha
  obtain ⟨b, hab, hbq⟩ := exists_between ha
  have haFinite : a ≠ ∞ := ne_top_of_lt (ha.trans_le le_top)
  have hbFinite : b ≠ ∞ := ne_top_of_lt (hbq.trans_le le_top)
  have hgap : 0 < b.toReal - a.toReal := by
    have := ENNReal.toReal_strict_mono hbFinite hab
    linarith
  let D : ℝ := 2 * (C ^ 2 + ‖x‖ ^ 2 + 1)
  have hD : 0 < D := by
    dsimp [D]
    positivity
  let lam : ℝ := (b.toReal - a.toReal) / D
  have hlam : 0 < lam := div_pos hgap hD
  have hlamD : lam * D = b.toReal - a.toReal :=
    div_mul_cancel₀ _ hD.ne'
  have hcost : lam * (C ^ 2 - ‖x‖ ^ 2) < b.toReal - a.toReal := by
    have hsmall : C ^ 2 - ‖x‖ ^ 2 < D := by
      dsimp [D]
      nlinarith [sq_nonneg C, sq_nonneg ‖x‖]
    nlinarith [mul_lt_mul_of_pos_left hsmall hlam]
  have hbOfReal : ENNReal.ofReal b.toReal = b := ENNReal.ofReal_toReal hbFinite
  obtain ⟨f, hf⟩ := hdual lam hlam x b.toReal (by simpa [hbOfReal] using hbq)
  refine ⟨lam, hlam, f, ?_⟩
  rw [← ENNReal.ofReal_toReal haFinite]
  apply ENNReal.ofReal_le_ofReal
  nlinarith

end NCG.VaryingHilbert
