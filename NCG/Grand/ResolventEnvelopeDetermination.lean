/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ResolventEnvelopeFormLiminf

/-!
# Sufficient conditions for resolvent-envelope determination

The converse Mosco theorem asks that positive-shift envelopes recover the limit form through
dual lower bounds.  This file separates the standard Fenchel--Moreau input from the elementary
small-shift argument: approximate envelope duality at each positive shift implies precisely the
determination property consumed by the converse theorem.
-/

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]

/-- Approximate dual representation of the shifted form by its resolvent envelope.

For a lower-semicontinuous closed quadratic form this is the usual Fenchel--Moreau identity for
`q x + lam * ‖x‖²`.  Keeping it separate makes that analytic theorem independently reusable. -/
def HasResolventEnvelopeDuality
    (q : E → ℝ) (T : ℝ → E →L[K] E) : Prop :=
  ∀ lam : ℝ, 0 < lam → ∀ x : E, ∀ ε > 0, ∃ f : E,
    q x + lam * ‖x‖ ^ 2 - ε ≤
      resolventEnvelope (K := K) q lam (T lam) f +
        2 * RCLike.re (inner K x f)

/-- Approximate shifted-envelope duality implies determination by positive resolvent envelopes.
The shift is chosen small enough that the prescribed ambient norm penalty costs less than half
the requested error. -/
theorem HasResolventEnvelopeDuality.isDeterminedByResolventEnvelopes
    {q : E → ℝ} {T : ℝ → E →L[K] E}
    (hdual : HasResolventEnvelopeDuality (K := K) q T) :
    IsDeterminedByResolventEnvelopes (K := K) q T := by
  intro x C _hC ε hε
  let lam : ℝ := ε / (2 * (C ^ 2 + 1))
  have hden : 0 < 2 * (C ^ 2 + 1) := by positivity
  have hlam : 0 < lam := div_pos hε hden
  have hlamEq : lam * (2 * (C ^ 2 + 1)) = ε := by
    exact div_mul_cancel₀ ε hden.ne'
  have hpenalty : lam * C ^ 2 < ε / 2 := by
    nlinarith [sq_nonneg C]
  obtain ⟨f, hf⟩ := hdual lam hlam x (ε / 2) (by positivity)
  refine ⟨lam, hlam, f, ?_⟩
  have hnorm : 0 ≤ lam * ‖x‖ ^ 2 := mul_nonneg hlam.le (sq_nonneg ‖x‖)
  linarith

/-- If every positive-shift resolvent is surjective, its envelope realizes the shifted duality
exactly (and hence determines the form).  This covers bounded finite-dimensional form operators
without invoking a separate convex-duality theorem. -/
theorem hasResolventEnvelopeDuality_of_surjective
    (q : E → ℝ) (T : ℝ → E →L[K] E)
    (hsurj : ∀ lam, 0 < lam → Function.Surjective (T lam)) :
    HasResolventEnvelopeDuality (K := K) q T := by
  intro lam hlam x ε hε
  obtain ⟨f, hf⟩ := hsurj lam hlam x
  refine ⟨f, ?_⟩
  simp only [resolventEnvelope, resolventObjective, hf]
  linarith

/-- Surjective positive-shift resolvents are sufficient for envelope determination. -/
theorem isDeterminedByResolventEnvelopes_of_surjective
    (q : E → ℝ) (T : ℝ → E →L[K] E)
    (hsurj : ∀ lam, 0 < lam → Function.Surjective (T lam)) :
    IsDeterminedByResolventEnvelopes (K := K) q T :=
  (hasResolventEnvelopeDuality_of_surjective (K := K) q T hsurj).isDeterminedByResolventEnvelopes

end NCG.VaryingHilbert
