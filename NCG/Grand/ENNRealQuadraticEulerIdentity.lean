/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertResolventObjective

/-!
# Euler identities for extended quadratic forms

The Euler energy identity of a resolvent minimizer is automatic when the extended form is
two-homogeneous along real scalar multiples.  The proof uses only one-dimensional variations,
so it applies to closed quadratic forms without a differentiability API.
-/

open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]

/-- An extended nonnegative form is two-homogeneous along real scalar multiples on its effective
domain. -/
structure IsENNRealTwoHomogeneous (q : E → ENNReal) : Prop where
  smul_ne_top : ∀ (r : ℝ) (x : E), q x ≠ ∞ → q (((r : ℝ) : K) • x) ≠ ∞
  toReal_smul : ∀ (r : ℝ) (x : E), q x ≠ ∞ →
    (q (((r : ℝ) : K) • x)).toReal = r ^ 2 * (q x).toReal

/-- The resolvent objective restricted to a real line through a finite-energy point is an exact
quadratic polynomial. -/
theorem resolventObjective_real_smul_of_twoHomogeneous
    (q : E → ENNReal) (hq : IsENNRealTwoHomogeneous (K := K) q)
    (lam : ℝ) (f x : E) (hx : q x ≠ ∞) (r : ℝ) :
    resolventObjective (K := K) (fun z ↦ (q z).toReal) lam f
        ((((r : ℝ) : K)) • x) =
      r ^ 2 * ((q x).toReal + lam * ‖x‖ ^ 2) -
        2 * r * RCLike.re (inner K x f) := by
  rw [resolventObjective, hq.toReal_smul r x hx]
  simp only [norm_smul, RCLike.norm_ofReal, inner_smul_real_left, RCLike.smul_re]
  rw [mul_pow, sq_abs]
  ring

/-- A finite resolvent minimizer of a positive-shift two-homogeneous extended form satisfies the
Euler energy identity. -/
theorem ennrealResolvent_energy_eq_inner_of_twoHomogeneous
    (q : E → ENNReal) (hq : IsENNRealTwoHomogeneous (K := K) q)
    (T : E →L[K] E) (lam : ℝ) (hlam : 0 < lam)
    (hfinite : ∀ f : E, q (T f) ≠ ∞)
    (hmin : ∀ (f z : E), q z ≠ ∞ →
      resolventObjective (K := K) (fun w ↦ (q w).toReal) lam f (T f) ≤
        resolventObjective (K := K) (fun w ↦ (q w).toReal) lam f z)
    (f : E) :
    (q (T f)).toReal + lam * ‖T f‖ ^ 2 =
      RCLike.re (inner K (T f) f) := by
  let x : E := T f
  let A : ℝ := (q x).toReal + lam * ‖x‖ ^ 2
  let p : ℝ := RCLike.re (inner K x f)
  have hx : q x ≠ ∞ := hfinite f
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg ENNReal.toReal_nonneg (mul_nonneg hlam.le (sq_nonneg ‖x‖))
  by_cases hAzero : A = 0
  · have hzero := hmin f ((((0 : ℝ) : K)) • x) (hq.smul_ne_top 0 x hx)
    have htwo := hmin f ((((2 : ℝ) : K)) • x) (hq.smul_ne_top 2 x hx)
    rw [resolventObjective_real_smul_of_twoHomogeneous q hq lam f x hx 0] at hzero
    rw [resolventObjective_real_smul_of_twoHomogeneous q hq lam f x hx 2] at htwo
    change A - 2 * p ≤ _ at hzero htwo
    have hp : p = 0 := by
      norm_num [hAzero] at hzero htwo
      linarith
    simp [x, A, p, hAzero, hp]
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
    let r : ℝ := p / A
    have hr := hmin f ((((r : ℝ) : K)) • x) (hq.smul_ne_top r x hx)
    rw [resolventObjective_real_smul_of_twoHomogeneous q hq lam f x hx r] at hr
    change A - 2 * p ≤ r ^ 2 * A - 2 * r * p at hr
    have hpoly : r ^ 2 * A - 2 * r * p = -(p ^ 2 / A) := by
      dsimp [r]
      field_simp [hAzero]
      ring
    rw [hpoly] at hr
    have hdiv : (A - p) ^ 2 / A ≤ 0 := by
      have hident :
          (A - p) ^ 2 / A = A - 2 * p + p ^ 2 / A := by
        field_simp [hAzero]
        ring
      rw [hident]
      nlinarith
    have hsquare : (A - p) ^ 2 ≤ 0 := by
      rcases (div_nonpos_iff.mp hdiv) with hbad | hgood
      · exact (not_le_of_gt hApos hbad.2).elim
      · exact hgood.1
    have hAp : A = p := by nlinarith [sq_nonneg (A - p)]
    simpa [x, A, p] using hAp

end NCG.VaryingHilbert
