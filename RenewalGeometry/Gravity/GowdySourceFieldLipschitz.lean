/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.GowdySplittingConsistencyExact

/-!
# An explicit Lipschitz constant of the Gowdy source field on a bounded chart
  (`thm:supp-gowdy-momentum`, consistency clause, emergent-spacetime supplement)

The second-order residual of the implicit-midpoint source half-step
(`GowdyStaggered.sourceStep_residual`) takes as hypothesis that the vector
source field `localFieldVec` (`eq:supp-gowdy-source-flow`) is `L`-Lipschitz on a
chart `K`.  This file discharges it on the concrete bounded smooth reference
chart with `t ≥ t₀ > 0` of the manuscript:

* `gowdyChart t₀ R = {(U, P, Q, t) : t ≥ t₀, |u_i| ≤ R, |P| ≤ R}` (`Q` enters the
  field only through `dQ/ds`, so it is unconstrained);
* `gowdyLipschitz t₀ R` is the explicit constant
  `1/(2t₀) + R/(2t₀²) + 4R/√t₀ + R²/(t₀√t₀) + eᴿ(R+1)/√t₀ + R eᴿ/(2t₀√t₀)`,
  obtained from the elementary bounds `|1/(2t) - 1/(2t')| ≤ |t-t'|/(2t₀²)`,
  `|1/√t - 1/√t'| ≤ |t-t'|/(2t₀√t₀)`, `|ab - a'b'| ≤ |a-a'||b| + |a'||b-b'|` and
  `|e^{-P} - e^{-P'}| ≤ eᴿ|P-P'|` on the chart;
* `localFieldVec_lipschitz_on_chart`: for `x, y ∈ gowdyChart t₀ R`,
  `‖localFieldVec x - localFieldVec y‖ ≤ gowdyLipschitz t₀ R * ‖x - y‖`
  (sup norms on the product state space);
* `sourceStep_residual_chart`: the implicit-midpoint residual bound of
  `sourceStep_residual` with `hLip` discharged, i.e. with the explicit constant.
-/

open Set
open scoped BigOperators

namespace RenewalGeometry.GowdyStaggered

noncomputable section

/-! ### Elementary difference bounds on `{t ≥ t₀ > 0}` -/

section Elementary

/-- `|1/(2t) - 1/(2t')| ≤ |t - t'| / (2 t₀²)` for `t, t' ≥ t₀ > 0`. -/
theorem abs_inv_two_mul_sub_le {t₀ t t' : ℝ} (h0 : 0 < t₀) (ht : t₀ ≤ t) (ht' : t₀ ≤ t') :
    |1 / (2 * t) - 1 / (2 * t')| ≤ |t - t'| / (2 * t₀ ^ 2) := by
  have htp : 0 < t := lt_of_lt_of_le h0 ht
  have htp' : 0 < t' := lt_of_lt_of_le h0 ht'
  have heq : 1 / (2 * t) - 1 / (2 * t') = (t' - t) / (2 * t * t') := by
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos (mul_pos two_pos htp) htp'), abs_sub_comm]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
  nlinarith [mul_le_mul ht ht' h0.le htp.le]

/-- `|1/√t - 1/√t'| ≤ |t - t'| / (2 t₀ √t₀)` for `t, t' ≥ t₀ > 0`. -/
theorem abs_inv_sqrt_sub_le {t₀ t t' : ℝ} (h0 : 0 < t₀) (ht : t₀ ≤ t) (ht' : t₀ ≤ t') :
    |1 / Real.sqrt t - 1 / Real.sqrt t'| ≤ |t - t'| / (2 * t₀ * Real.sqrt t₀) := by
  have htp : 0 < t := lt_of_lt_of_le h0 ht
  have htp' : 0 < t' := lt_of_lt_of_le h0 ht'
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr htp
  have hs' : 0 < Real.sqrt t' := Real.sqrt_pos.mpr htp'
  have hs0 : 0 < Real.sqrt t₀ := Real.sqrt_pos.mpr h0
  have h0s : Real.sqrt t₀ ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
  have h0s' : Real.sqrt t₀ ≤ Real.sqrt t' := Real.sqrt_le_sqrt ht'
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt htp.le
  have hsq' : Real.sqrt t' * Real.sqrt t' = t' := Real.mul_self_sqrt htp'.le
  have hsq0 : Real.sqrt t₀ * Real.sqrt t₀ = t₀ := Real.mul_self_sqrt h0.le
  have hnum : (Real.sqrt t' - Real.sqrt t) * (Real.sqrt t' + Real.sqrt t) = t' - t := by
    nlinarith [hsq, hsq']
  have habs : |1 / Real.sqrt t - 1 / Real.sqrt t'|
      = |t - t'| / (Real.sqrt t * Real.sqrt t' * (Real.sqrt t' + Real.sqrt t)) := by
    rw [div_sub_div _ _ hs.ne' hs'.ne', one_mul, mul_one, abs_div, abs_of_pos (mul_pos hs hs')]
    have : |Real.sqrt t' - Real.sqrt t| = |t - t'| / (Real.sqrt t' + Real.sqrt t) := by
      rw [eq_div_iff (add_pos hs' hs).ne', ← abs_of_pos (add_pos hs' hs),
        ← abs_mul, hnum, abs_sub_comm]
    rw [this, div_div]
    ring
  rw [habs]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos (mul_pos two_pos h0) hs0)
  have h1 : t₀ ≤ Real.sqrt t * Real.sqrt t' := by nlinarith
  have h2 : 2 * Real.sqrt t₀ ≤ Real.sqrt t' + Real.sqrt t := by linarith
  nlinarith [mul_le_mul h1 h2 (by linarith) (mul_pos hs hs').le]

/-- `|a/(2t) - a'/(2t')| ≤ |a - a'|/(2t₀) + R |t - t'|/(2t₀²)` when `|a'| ≤ R`. -/
theorem abs_div_two_mul_sub_le {t₀ t t' a a' R : ℝ} (h0 : 0 < t₀) (ht : t₀ ≤ t) (ht' : t₀ ≤ t')
    (ha' : |a'| ≤ R) :
    |a / (2 * t) - a' / (2 * t')| ≤ |a - a'| / (2 * t₀) + R * (|t - t'| / (2 * t₀ ^ 2)) := by
  have htp : 0 < t := lt_of_lt_of_le h0 ht
  have htp' : 0 < t' := lt_of_lt_of_le h0 ht'
  have heq : a / (2 * t) - a' / (2 * t')
      = (a - a') * (1 / (2 * t)) + a' * (1 / (2 * t) - 1 / (2 * t')) := by
    field_simp
    ring
  rw [heq]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (one_div_pos.mpr (mul_pos two_pos htp)),
      div_eq_mul_one_div (|a - a'|) (2 * t₀)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact one_div_le_one_div_of_le (mul_pos two_pos h0) (by linarith)
  · rw [abs_mul]
    exact mul_le_mul ha' (abs_inv_two_mul_sub_le h0 ht ht') (abs_nonneg _)
      ((abs_nonneg _).trans ha')

/-- `|q/√t - q'/√t'| ≤ |q - q'|/√t₀ + |q'| |t - t'|/(2t₀√t₀)`. -/
theorem abs_div_sqrt_sub_le {t₀ t t' q q' : ℝ} (h0 : 0 < t₀) (ht : t₀ ≤ t) (ht' : t₀ ≤ t') :
    |q / Real.sqrt t - q' / Real.sqrt t'|
      ≤ |q - q'| / Real.sqrt t₀ + |q'| * (|t - t'| / (2 * t₀ * Real.sqrt t₀)) := by
  have htp : 0 < t := lt_of_lt_of_le h0 ht
  have htp' : 0 < t' := lt_of_lt_of_le h0 ht'
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr htp
  have hs' : 0 < Real.sqrt t' := Real.sqrt_pos.mpr htp'
  have hs0 : 0 < Real.sqrt t₀ := Real.sqrt_pos.mpr h0
  have h0s : Real.sqrt t₀ ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
  have heq : q / Real.sqrt t - q' / Real.sqrt t'
      = (q - q') * (1 / Real.sqrt t) + q' * (1 / Real.sqrt t - 1 / Real.sqrt t') := by
    field_simp
    ring
  rw [heq]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (one_div_pos.mpr hs), div_eq_mul_one_div (|q - q'|) (Real.sqrt t₀)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact one_div_le_one_div_of_le hs0 h0s
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_inv_sqrt_sub_le h0 ht ht') (abs_nonneg _)

/-- `|ab - a'b'| ≤ |a - a'| |b| + |a'| |b - b'|`. -/
theorem abs_mul_sub_mul_le (a a' b b' : ℝ) :
    |a * b - a' * b'| ≤ |a - a'| * |b| + |a'| * |b - b'| := by
  have heq : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [heq]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]

/-- `|e^{-P} - e^{-P'}| ≤ eᴿ |P - P'|` for `|P|, |P'| ≤ R`. -/
theorem abs_exp_neg_sub_exp_neg_le {P P' R : ℝ} (hP : |P| ≤ R) (hP' : |P'| ≤ R) :
    |Real.exp (-P) - Real.exp (-P')| ≤ Real.exp R * |P - P'| := by
  have hmem : ∀ x : ℝ, |x| ≤ R → -x ∈ Icc (-R) R := by
    intro x hx
    rw [abs_le] at hx
    exact ⟨by linarith, by linarith⟩
  have h := (convex_Icc (-R) R).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.exp) (f' := Real.exp) (C := Real.exp R)
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x hx => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]; exact Real.exp_le_exp.mpr hx.2)
    (hmem P' hP') (hmem P hP)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  refine h.trans ?_
  rw [show -P - -P' = -(P - P') by ring, abs_neg]

end Elementary

/-! ### The chart and the constant -/

/-- The bounded smooth reference chart `{t ≥ t₀, |u_i| ≤ R, |P| ≤ R}` of the local
`(U, P, Q, t)` state space. -/
def gowdyChart (t₀ R : ℝ) : Set StateVec :=
  {v | t₀ ≤ v.2.2.2 ∧ (∀ i, |v.1 i| ≤ R) ∧ |v.2.1| ≤ R}

/-- The explicit Lipschitz constant of the source field on `gowdyChart t₀ R`. -/
def gowdyLipschitz (t₀ R : ℝ) : ℝ :=
  1 / (2 * t₀) + R / (2 * t₀ ^ 2) + 4 * R / Real.sqrt t₀ + R ^ 2 / (t₀ * Real.sqrt t₀) +
    Real.exp R * (R + 1) / Real.sqrt t₀ + R * Real.exp R / (2 * t₀ * Real.sqrt t₀)

theorem gowdyLipschitz_nonneg {t₀ R : ℝ} (h0 : 0 < t₀) (hR : 0 ≤ R) :
    0 ≤ gowdyLipschitz t₀ R := by
  unfold gowdyLipschitz
  have := Real.sqrt_pos.mpr h0
  have := Real.exp_pos R
  positivity

theorem sourceField_apply_zero (t : ℝ) (u : Fin 4 → ℝ) :
    sourceField t u 0 = -(u 0) / (2 * t) + (u 2 ^ 2 - u 3 ^ 2) / Real.sqrt t := by
  simp [sourceField]

theorem sourceField_apply_one (t : ℝ) (u : Fin 4 → ℝ) :
    sourceField t u 1 = u 1 / (2 * t) := by
  simp [sourceField]

theorem sourceField_apply_two (t : ℝ) (u : Fin 4 → ℝ) :
    sourceField t u 2 = -(u 2) / (2 * t) + (-(u 0) * u 2 + u 1 * u 3) / Real.sqrt t := by
  simp [sourceField]

theorem sourceField_apply_three (t : ℝ) (u : Fin 4 → ℝ) :
    sourceField t u 3 = u 3 / (2 * t) + (u 0 * u 3 - u 1 * u 2) / Real.sqrt t := by
  simp [sourceField]

theorem localFieldVec_eq (v : StateVec) :
    localFieldVec v = (sourceField v.2.2.2 v.1, v.1 0 / Real.sqrt v.2.2.2,
      Real.exp (-v.2.1) * v.1 2 / Real.sqrt v.2.2.2, 1) := rfl

/-! ### The Lipschitz bound -/

/-- Bound for a component of the form `a/(2t) + q/√t` on the chart, in terms of bounds on
the differences of `a`, `q`, `t` and on `|a'|`, `|q'|`. -/
theorem abs_component_le {t₀ t t' a a' q q' R Rq δ : ℝ} (h0 : 0 < t₀) (ht : t₀ ≤ t) (ht' : t₀ ≤ t')
    (ha' : |a'| ≤ R) (hq' : |q'| ≤ Rq) (hδa : |a - a'| ≤ δ) (hδq : |q - q'| ≤ 4 * R * δ)
    (hδt : |t - t'| ≤ δ) (hR : 0 ≤ R) (hRq : 0 ≤ Rq) (_hδ : 0 ≤ δ) :
    |a / (2 * t) + q / Real.sqrt t - (a' / (2 * t') + q' / Real.sqrt t')|
      ≤ (1 / (2 * t₀) + R / (2 * t₀ ^ 2) + 4 * R / Real.sqrt t₀ +
          Rq / (2 * t₀ * Real.sqrt t₀)) * δ := by
  have hs0 : 0 < Real.sqrt t₀ := Real.sqrt_pos.mpr h0
  have heq : a / (2 * t) + q / Real.sqrt t - (a' / (2 * t') + q' / Real.sqrt t')
      = (a / (2 * t) - a' / (2 * t')) + (q / Real.sqrt t - q' / Real.sqrt t') := by ring
  rw [heq]
  refine (abs_add_le _ _).trans ?_
  have h1 := abs_div_two_mul_sub_le (a := a) h0 ht ht' ha'
  have h2 := abs_div_sqrt_sub_le (q := q) (q' := q') h0 ht ht'
  have h3 : |a - a'| / (2 * t₀) + R * (|t - t'| / (2 * t₀ ^ 2))
      ≤ δ / (2 * t₀) + R * (δ / (2 * t₀ ^ 2)) := by gcongr
  have h4 : |q - q'| / Real.sqrt t₀ + |q'| * (|t - t'| / (2 * t₀ * Real.sqrt t₀))
      ≤ (4 * R * δ) / Real.sqrt t₀ + Rq * (δ / (2 * t₀ * Real.sqrt t₀)) := by gcongr
  calc |a / (2 * t) - a' / (2 * t')| + |q / Real.sqrt t - q' / Real.sqrt t'|
      ≤ (δ / (2 * t₀) + R * (δ / (2 * t₀ ^ 2))) +
          ((4 * R * δ) / Real.sqrt t₀ + Rq * (δ / (2 * t₀ * Real.sqrt t₀))) :=
        add_le_add (h1.trans h3) (h2.trans h4)
    _ = (1 / (2 * t₀) + R / (2 * t₀ ^ 2) + 4 * R / Real.sqrt t₀ +
          Rq / (2 * t₀ * Real.sqrt t₀)) * δ := by ring

/-- **The Gowdy source field is Lipschitz on the bounded chart `{t ≥ t₀ > 0}`**, with the
explicit constant `gowdyLipschitz t₀ R`. -/
theorem localFieldVec_lipschitz_on_chart {t₀ R : ℝ} (h0 : 0 < t₀) (hR : 0 ≤ R) :
    ∀ x ∈ gowdyChart t₀ R, ∀ y ∈ gowdyChart t₀ R,
      ‖localFieldVec x - localFieldVec y‖ ≤ gowdyLipschitz t₀ R * ‖x - y‖ := by
  rintro ⟨u, P, Q, t⟩ ⟨ht, hu, hP⟩ ⟨u', P', Q', t'⟩ ⟨ht', hu', hP'⟩
  simp only at ht hu hP ht' hu' hP'
  set δ := ‖((u, P, Q, t) : StateVec) - (u', P', Q', t')‖ with hδdef
  have hδ : 0 ≤ δ := norm_nonneg _
  -- the coordinate differences are bounded by `δ`
  have hδu : ∀ i, |u i - u' i| ≤ δ := by
    intro i
    have h1 := norm_le_pi_norm (u - u') i
    have h2 := norm_fst_le (((u, P, Q, t) : StateVec) - (u', P', Q', t'))
    rw [Pi.sub_apply, Real.norm_eq_abs] at h1
    exact h1.trans h2
  have hδP : |P - P'| ≤ δ := by
    have h1 := norm_fst_le ((((u, P, Q, t) : StateVec) - (u', P', Q', t')).2)
    have h2 := norm_snd_le (((u, P, Q, t) : StateVec) - (u', P', Q', t'))
    rw [Real.norm_eq_abs] at h1
    exact h1.trans h2
  have hδt : |t - t'| ≤ δ := by
    have h1 := norm_snd_le (((((u, P, Q, t) : StateVec) - (u', P', Q', t')).2).2)
    have h2 := norm_snd_le ((((u, P, Q, t) : StateVec) - (u', P', Q', t')).2)
    have h3 := norm_snd_le (((u, P, Q, t) : StateVec) - (u', P', Q', t'))
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (h2.trans h3)
  -- positivity facts
  have hs0 : 0 < Real.sqrt t₀ := Real.sqrt_pos.mpr h0
  have hexp : 0 < Real.exp R := Real.exp_pos R
  have hL := gowdyLipschitz_nonneg h0 hR
  -- the nonnegative pieces of the constant
  have hc1 : 0 ≤ 1 / (2 * t₀) := by positivity
  have hc2 : 0 ≤ R / (2 * t₀ ^ 2) := by positivity
  have hc3 : 0 ≤ 4 * R / Real.sqrt t₀ := by positivity
  have hc4 : 0 ≤ R ^ 2 / (t₀ * Real.sqrt t₀) := by positivity
  have hc5 : 0 ≤ Real.exp R * (R + 1) / Real.sqrt t₀ := by positivity
  have hc6 : 0 ≤ R * Real.exp R / (2 * t₀ * Real.sqrt t₀) := by positivity
  -- reduce to components
  rw [localFieldVec_eq, localFieldVec_eq]
  simp only [Prod.mk_sub_mk, Prod.norm_def, Real.norm_eq_abs, sub_self, abs_zero]
  refine max_le ?_ (max_le ?_ (max_le ?_ (by nlinarith)))
  · -- the frame components
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [Pi.sub_apply, Real.norm_eq_abs]
    -- squares and products on the chart
    have hsq : ∀ i j, |u i * u j - u' i * u' j| ≤ 2 * R * δ := by
      intro i j
      have := abs_mul_sub_mul_le (u i) (u' i) (u j) (u' j)
      refine this.trans ?_
      have h1 : |u i - u' i| * |u j| ≤ δ * R := mul_le_mul (hδu i) (hu j) (abs_nonneg _) hδ
      have h2 : |u' i| * |u j - u' j| ≤ R * δ := mul_le_mul (hu' i) (hδu j) (abs_nonneg _) hR
      linarith
    have hprod' : ∀ i j, |u' i * u' j| ≤ R ^ 2 := by
      intro i j
      rw [abs_mul, sq]
      exact mul_le_mul (hu' i) (hu' j) (abs_nonneg _) hR
    fin_cases i
    · -- `u₀`
      simp only [Fin.zero_eta, Fin.isValue]
      rw [sourceField_apply_zero, sourceField_apply_zero]
      have hq : |(u 2 ^ 2 - u 3 ^ 2) - (u' 2 ^ 2 - u' 3 ^ 2)| ≤ 4 * R * δ := by
        have h1 := hsq 2 2
        have h2 := hsq 3 3
        rw [← sq, ← sq] at h1 h2
        calc |(u 2 ^ 2 - u 3 ^ 2) - (u' 2 ^ 2 - u' 3 ^ 2)|
            = |(u 2 ^ 2 - u' 2 ^ 2) - (u 3 ^ 2 - u' 3 ^ 2)| := by ring_nf
          _ ≤ |u 2 ^ 2 - u' 2 ^ 2| + |u 3 ^ 2 - u' 3 ^ 2| := abs_sub _ _
          _ ≤ 4 * R * δ := by linarith
      have hq' : |u' 2 ^ 2 - u' 3 ^ 2| ≤ 2 * R ^ 2 := by
        have h1 := hprod' 2 2
        have h2 := hprod' 3 3
        rw [← sq] at h1 h2
        exact (abs_sub _ _).trans (by linarith)
      have ha' : |-(u' 0)| ≤ R := by rw [abs_neg]; exact hu' 0
      have hδa : |-(u 0) - -(u' 0)| ≤ δ := by
        rw [show -(u 0) - -(u' 0) = -(u 0 - u' 0) by ring, abs_neg]; exact hδu 0
      have := abs_component_le h0 ht ht' ha' hq' hδa hq hδt hR (by positivity) hδ
      refine this.trans ?_
      unfold gowdyLipschitz
      have : 2 * R ^ 2 / (2 * t₀ * Real.sqrt t₀) = R ^ 2 / (t₀ * Real.sqrt t₀) := by
        field_simp
      rw [this]
      nlinarith
    · -- `u₁`
      simp only [Fin.mk_one, Fin.isValue]
      rw [sourceField_apply_one, sourceField_apply_one]
      have := abs_div_two_mul_sub_le (a := u 1) h0 ht ht' (hu' 1)
      refine this.trans ?_
      have h3 : |u 1 - u' 1| / (2 * t₀) + R * (|t - t'| / (2 * t₀ ^ 2))
          ≤ δ / (2 * t₀) + R * (δ / (2 * t₀ ^ 2)) := by gcongr; exact hδu 1
      refine h3.trans ?_
      have hfac : δ / (2 * t₀) + R * (δ / (2 * t₀ ^ 2)) = (1 / (2 * t₀) + R / (2 * t₀ ^ 2)) * δ := by
        ring
      rw [hfac]
      refine mul_le_mul_of_nonneg_right ?_ hδ
      unfold gowdyLipschitz
      linarith
    · -- `u₂`
      simp only [Fin.reduceFinMk, Fin.isValue]
      rw [sourceField_apply_two, sourceField_apply_two]
      have hq : |(-(u 0) * u 2 + u 1 * u 3) - (-(u' 0) * u' 2 + u' 1 * u' 3)| ≤ 4 * R * δ := by
        have h1 := hsq 0 2
        have h2 := hsq 1 3
        calc |(-(u 0) * u 2 + u 1 * u 3) - (-(u' 0) * u' 2 + u' 1 * u' 3)|
            = |(u 1 * u 3 - u' 1 * u' 3) - (u 0 * u 2 - u' 0 * u' 2)| := by ring_nf
          _ ≤ |u 1 * u 3 - u' 1 * u' 3| + |u 0 * u 2 - u' 0 * u' 2| := abs_sub _ _
          _ ≤ 4 * R * δ := by linarith
      have hq' : |-(u' 0) * u' 2 + u' 1 * u' 3| ≤ 2 * R ^ 2 := by
        have h1 := hprod' 0 2
        have h2 := hprod' 1 3
        calc |-(u' 0) * u' 2 + u' 1 * u' 3| = |u' 1 * u' 3 - u' 0 * u' 2| := by ring_nf
          _ ≤ |u' 1 * u' 3| + |u' 0 * u' 2| := abs_sub _ _
          _ ≤ 2 * R ^ 2 := by linarith
      have ha' : |-(u' 2)| ≤ R := by rw [abs_neg]; exact hu' 2
      have hδa : |-(u 2) - -(u' 2)| ≤ δ := by
        rw [show -(u 2) - -(u' 2) = -(u 2 - u' 2) by ring, abs_neg]; exact hδu 2
      have := abs_component_le h0 ht ht' ha' hq' hδa hq hδt hR (by positivity) hδ
      refine this.trans ?_
      unfold gowdyLipschitz
      have : 2 * R ^ 2 / (2 * t₀ * Real.sqrt t₀) = R ^ 2 / (t₀ * Real.sqrt t₀) := by
        field_simp
      rw [this]
      nlinarith
    · -- `u₃`
      simp only [Fin.reduceFinMk, Fin.isValue]
      rw [sourceField_apply_three, sourceField_apply_three]
      have hq : |(u 0 * u 3 - u 1 * u 2) - (u' 0 * u' 3 - u' 1 * u' 2)| ≤ 4 * R * δ := by
        have h1 := hsq 0 3
        have h2 := hsq 1 2
        calc |(u 0 * u 3 - u 1 * u 2) - (u' 0 * u' 3 - u' 1 * u' 2)|
            = |(u 0 * u 3 - u' 0 * u' 3) - (u 1 * u 2 - u' 1 * u' 2)| := by ring_nf
          _ ≤ |u 0 * u 3 - u' 0 * u' 3| + |u 1 * u 2 - u' 1 * u' 2| := abs_sub _ _
          _ ≤ 4 * R * δ := by linarith
      have hq' : |u' 0 * u' 3 - u' 1 * u' 2| ≤ 2 * R ^ 2 := by
        have h1 := hprod' 0 3
        have h2 := hprod' 1 2
        exact (abs_sub _ _).trans (by linarith)
      have := abs_component_le h0 ht ht' (hu' 3) hq' (hδu 3) hq hδt hR (by positivity) hδ
      refine this.trans ?_
      unfold gowdyLipschitz
      have : 2 * R ^ 2 / (2 * t₀ * Real.sqrt t₀) = R ^ 2 / (t₀ * Real.sqrt t₀) := by
        field_simp
      rw [this]
      nlinarith
  · -- `P`: `u₀/√t`
    have := abs_div_sqrt_sub_le (q := u 0) (q' := u' 0) h0 ht ht'
    refine this.trans ?_
    have h4 : |u 0 - u' 0| / Real.sqrt t₀ + |u' 0| * (|t - t'| / (2 * t₀ * Real.sqrt t₀))
        ≤ δ / Real.sqrt t₀ + R * (δ / (2 * t₀ * Real.sqrt t₀)) := by
      gcongr
      · exact hδu 0
      · exact hu' 0
    refine h4.trans ?_
    have hexpR : 1 ≤ Real.exp R := Real.one_le_exp hR
    have hfac : δ / Real.sqrt t₀ + R * (δ / (2 * t₀ * Real.sqrt t₀))
        = (1 / Real.sqrt t₀ + R / (2 * t₀ * Real.sqrt t₀)) * δ := by ring
    rw [hfac]
    refine mul_le_mul_of_nonneg_right ?_ hδ
    have e1 : 1 / Real.sqrt t₀ ≤ Real.exp R * (R + 1) / Real.sqrt t₀ :=
      div_le_div_of_nonneg_right (by nlinarith) hs0.le
    have e2 : R / (2 * t₀ * Real.sqrt t₀) ≤ R * Real.exp R / (2 * t₀ * Real.sqrt t₀) :=
      div_le_div_of_nonneg_right (le_mul_of_one_le_right hR hexpR)
        (mul_pos (mul_pos two_pos h0) hs0).le
    unfold gowdyLipschitz
    linarith
  · -- `Q`: `e^{-P} u₂/√t`
    have := abs_div_sqrt_sub_le (q := Real.exp (-P) * u 2) (q' := Real.exp (-P') * u' 2) h0 ht ht'
    refine this.trans ?_
    have hexpP : Real.exp (-P') ≤ Real.exp R := by
      rw [abs_le] at hP'
      exact Real.exp_le_exp.mpr (by linarith)
    have hq : |Real.exp (-P) * u 2 - Real.exp (-P') * u' 2| ≤ Real.exp R * (R + 1) * δ := by
      refine (abs_mul_sub_mul_le _ _ _ _).trans ?_
      have h1 : |Real.exp (-P) - Real.exp (-P')| * |u 2| ≤ Real.exp R * δ * R := by
        have := abs_exp_neg_sub_exp_neg_le hP hP'
        calc |Real.exp (-P) - Real.exp (-P')| * |u 2|
            ≤ (Real.exp R * |P - P'|) * R := mul_le_mul this (hu 2) (abs_nonneg _) (by positivity)
          _ ≤ (Real.exp R * δ) * R := by gcongr
      have h2 : |Real.exp (-P')| * |u 2 - u' 2| ≤ Real.exp R * δ := by
        rw [abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul hexpP (hδu 2) (abs_nonneg _) hexp.le
      nlinarith
    have hq' : |Real.exp (-P') * u' 2| ≤ R * Real.exp R := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-P') * |u' 2| ≤ Real.exp R * R :=
            mul_le_mul hexpP (hu' 2) (abs_nonneg _) hexp.le
        _ = R * Real.exp R := by ring
    have h4 : |Real.exp (-P) * u 2 - Real.exp (-P') * u' 2| / Real.sqrt t₀ +
          |Real.exp (-P') * u' 2| * (|t - t'| / (2 * t₀ * Real.sqrt t₀))
        ≤ (Real.exp R * (R + 1) * δ) / Real.sqrt t₀ +
          (R * Real.exp R) * (δ / (2 * t₀ * Real.sqrt t₀)) := by gcongr
    refine h4.trans ?_
    unfold gowdyLipschitz
    have e1 : (Real.exp R * (R + 1) * δ) / Real.sqrt t₀
        = Real.exp R * (R + 1) / Real.sqrt t₀ * δ := by ring
    have e2 : (R * Real.exp R) * (δ / (2 * t₀ * Real.sqrt t₀))
        = R * Real.exp R / (2 * t₀ * Real.sqrt t₀) * δ := by ring
    rw [e1, e2, ← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ hδ
    linarith

/-- **Second-order local consistency of the implicit-midpoint source step on the bounded
chart `{t ≥ t₀ > 0, |u_i| ≤ R, |P| ≤ R}`** (`thm:supp-gowdy-momentum`, consistency clause,
source part, with the Lipschitz hypothesis of `sourceStep_residual` discharged): a `C³`
trajectory of the local source flow whose midpoints lie in the chart satisfies the
implicit-midpoint relation of duration `σ = b - a` up to a residual of norm at most
`σ³ (M₃/24 + gowdyLipschitz t₀ R · M₂/8)`. -/
theorem sourceStep_residual_chart {t₀ R : ℝ} (h0 : 0 < t₀) (hR : 0 ≤ R)
    (Z : ℝ → LocalState) (V'' V''' : ℝ → StateVec)
    (a b M₂ M₃ : ℝ) (hab : a ≤ b)
    (h1 : ∀ s, HasDerivAt (fun s => (Z s).toVec) ((localField (Z s)).toVec) s)
    (h2 : ∀ s, HasDerivAt (fun s => (localField (Z s)).toVec) (V'' s) s)
    (h3 : ∀ s, HasDerivAt V'' (V''' s) s)
    (hM₂ : ∀ s ∈ Icc a b, ‖V'' s‖ ≤ M₂) (hM₃ : ∀ s ∈ Icc a b, ‖V''' s‖ ≤ M₃)
    (hmid : (Z ((a + b) / 2)).toVec ∈ gowdyChart t₀ R)
    (hmid' : (midpoint (Z a) (Z b)).toVec ∈ gowdyChart t₀ R) :
    ‖(Z b).toVec - ((Z a).toVec + (b - a) • (localField (midpoint (Z a) (Z b))).toVec)‖ ≤
      (b - a) ^ 3 * (M₃ / 24 + gowdyLipschitz t₀ R * M₂ / 8) :=
  sourceStep_residual Z V'' V''' (gowdyChart t₀ R) a b M₂ M₃ (gowdyLipschitz t₀ R) hab
    (gowdyLipschitz_nonneg h0 hR) h1 h2 h3 hM₂ hM₃ (localFieldVec_lipschitz_on_chart h0 hR)
    hmid hmid'

end

end RenewalGeometry.GowdyStaggered
