/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Certified semantic-moment inversion and cut-minor error
  (`prop:semantic-moment-error-master`,
   `lem:cut-minor-error-master`, flagship manuscript)

* Boxed inversion error bound: if `V̂ = V + ΔV`,
  `m̂ = m + Δm`, `η = ‖V⁻¹‖·‖ΔV‖ < 1`, and `V̂p̂ = m̂`, `Vp = m`,
  then `‖p̂ - p‖ ≤ (‖V⁻¹‖/(1-η))·(‖Δm‖ + ‖ΔV‖·‖p‖)`
  (`semantic_moment_error`, on a Banach space with the operator
  norm; the perturbed system is solvable because
  `V̂ = V(1 + V⁻¹ΔV)` is invertible by the Neumann series).
  Every depth-two determinant and loading difference therefore has
  an explicit propagated error bar (prose consequence).

* Boxed cut-minor error: with `F₀₀ = 1`, `|F_{ab}| ≤ 1`,
  `D_{ab} = F_{ab} - F_{a0}F_{0b}`, and entrywise measurement
  error `ε`, one has `|D_{ab}| ≤ |D̂_{ab}| + 3ε + ε²`
  (`cut_minor_error`).
-/

open NormedSpace

namespace NCG

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- `prop:semantic-moment-error-master`, boxed bound: the
perturbed Vandermonde system is solvable and its solution carries
the explicit propagated error bar. -/
theorem semantic_moment_error (V W : E →L[ℝ] E) (Vinv : E →L[ℝ] E)
    (hVl : Vinv ∘L V = ContinuousLinearMap.id ℝ E)
    (_hVr : V ∘L Vinv = ContinuousLinearMap.id ℝ E)
    (p phat m mhat : E)
    (hsys : V p = m) (hsyshat : W phat = mhat)
    (η : ℝ) (hη : ‖Vinv‖ * ‖W - V‖ ≤ η) (hη1 : η < 1) :
    ‖phat - p‖ ≤ ‖Vinv‖ / (1 - η)
      * (‖mhat - m‖ + ‖W - V‖ * ‖p‖) := by
  have hη0 : (0 : ℝ) ≤ η :=
    le_trans (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hη
  -- the key algebraic identity: (1 + Vinv(W - V))(p̂ - p)
  --   = Vinv((m̂ - m) - (W - V)p)
  set T : E →L[ℝ] E := Vinv ∘L (W - V) with hT
  have hTnorm : ‖T‖ ≤ η :=
    le_trans (ContinuousLinearMap.opNorm_comp_le _ _) hη
  have hkey : (phat - p) + T (phat - p)
      = Vinv ((mhat - m) - (W - V) p) := by
    have h1 : W (phat - p) = (mhat - m) - (W - V) p := by
      rw [map_sub, hsyshat]
      have h2 : (W - V) p = W p - m := by
        rw [show (W - V) p = W p - V p from rfl, hsys]
      rw [h2]
      abel
    have h3 : Vinv (W (phat - p)) = (phat - p) + T (phat - p) := by
      have h4 : W = V + (W - V) := by abel
      calc Vinv (W (phat - p))
          = Vinv ((V + (W - V)) (phat - p)) := by rw [← h4]
        _ = Vinv (V (phat - p)) + Vinv ((W - V) (phat - p)) := by
            rw [show (V + (W - V)) (phat - p)
              = V (phat - p) + (W - V) (phat - p) from rfl, map_add]
        _ = (phat - p) + T (phat - p) := by
            congr 1
            have h5 := congrArg (fun φ : E →L[ℝ] E => φ (phat - p))
              hVl
            simpa using h5
    rw [← h3, h1]
  -- norm estimate: (1-η)‖p̂-p‖ ≤ ‖RHS‖
  have hlow : (1 - η) * ‖phat - p‖
      ≤ ‖(phat - p) + T (phat - p)‖ := by
    have h1 : ‖phat - p‖
        ≤ ‖(phat - p) + T (phat - p)‖ + ‖T (phat - p)‖ := by
      have h0 := norm_sub_le ((phat - p) + T (phat - p))
        (T (phat - p))
      have harg : ((phat - p) + T (phat - p)) - T (phat - p)
          = phat - p := by abel
      rwa [harg] at h0
    have h2 : ‖T (phat - p)‖ ≤ η * ‖phat - p‖ :=
      le_trans (T.le_opNorm _)
        (mul_le_mul_of_nonneg_right hTnorm (norm_nonneg _))
    nlinarith [norm_nonneg (phat - p)]
  have hup : ‖Vinv ((mhat - m) - (W - V) p)‖
      ≤ ‖Vinv‖ * (‖mhat - m‖ + ‖W - V‖ * ‖p‖) := by
    refine le_trans (Vinv.le_opNorm _) ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖(W - V) p‖ ≤ ‖W - V‖ * ‖p‖ := (W - V).le_opNorm p
    linarith
  have h1mη : (0 : ℝ) < 1 - η := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h1mη]
  calc ‖phat - p‖ * (1 - η) = (1 - η) * ‖phat - p‖ := by ring
    _ ≤ ‖(phat - p) + T (phat - p)‖ := hlow
    _ = ‖Vinv ((mhat - m) - (W - V) p)‖ := by rw [hkey]
    _ ≤ ‖Vinv‖ * (‖mhat - m‖ + ‖W - V‖ * ‖p‖) := hup

/-- `lem:cut-minor-error-master`, boxed bound:
`|D_{ab}| ≤ |D̂_{ab}| + 3ε + ε²`. -/
theorem cut_minor_error (F Fhat : ℕ → ℕ → ℝ) (a b : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hbound : ∀ x y, |F x y| ≤ 1)
    (hmeas : ∀ x y, |Fhat x y - F x y| ≤ ε) :
    |F a b - F a 0 * F 0 b|
      ≤ |Fhat a b - Fhat a 0 * Fhat 0 b| + 3 * ε + ε ^ 2 := by
  have h1 : |(F a b - F a 0 * F 0 b)
      - (Fhat a b - Fhat a 0 * Fhat 0 b)| ≤ 3 * ε + ε ^ 2 := by
    have hab := hmeas a b
    have ha0 := hmeas a 0
    have h0b := hmeas 0 b
    have hFa0 := hbound a 0
    have hF0b := hbound 0 b
    have hprod : |F a 0 * F 0 b - Fhat a 0 * Fhat 0 b|
        ≤ 2 * ε + ε ^ 2 := by
      have hsplit : F a 0 * F 0 b - Fhat a 0 * Fhat 0 b
          = F a 0 * (F 0 b - Fhat 0 b)
            + (F a 0 - Fhat a 0) * Fhat 0 b := by ring
      rw [hsplit]
      refine le_trans (abs_add_le _ _) ?_
      have hb1 : |F a 0 * (F 0 b - Fhat 0 b)| ≤ 1 * ε := by
        rw [abs_mul]
        refine mul_le_mul hFa0 ?_ (abs_nonneg _) (by norm_num)
        rw [abs_sub_comm]
        exact h0b
      have hFhat0b : |Fhat 0 b| ≤ 1 + ε := by
        calc |Fhat 0 b| = |F 0 b + (Fhat 0 b - F 0 b)| := by
              ring_nf
          _ ≤ |F 0 b| + |Fhat 0 b - F 0 b| := abs_add_le _ _
          _ ≤ 1 + ε := add_le_add hF0b h0b
      have hb2 : |(F a 0 - Fhat a 0) * Fhat 0 b| ≤ ε * (1 + ε) := by
        rw [abs_mul]
        refine mul_le_mul ?_ hFhat0b (abs_nonneg _) hε
        rw [abs_sub_comm]
        exact ha0
      nlinarith
    calc |(F a b - F a 0 * F 0 b)
        - (Fhat a b - Fhat a 0 * Fhat 0 b)|
        = |(F a b - Fhat a b)
          - (F a 0 * F 0 b - Fhat a 0 * Fhat 0 b)| := by ring_nf
      _ = |(F a b - Fhat a b)
          + -(F a 0 * F 0 b - Fhat a 0 * Fhat 0 b)| := by ring_nf
      _ ≤ |F a b - Fhat a b|
          + |-(F a 0 * F 0 b - Fhat a 0 * Fhat 0 b)| := abs_add_le _ _
      _ = |F a b - Fhat a b|
          + |F a 0 * F 0 b - Fhat a 0 * Fhat 0 b| := by
          rw [abs_neg]
      _ ≤ ε + (2 * ε + ε ^ 2) := by
          refine add_le_add ?_ hprod
          rw [abs_sub_comm]
          exact hab
      _ = 3 * ε + ε ^ 2 := by ring
  calc |F a b - F a 0 * F 0 b|
      ≤ |Fhat a b - Fhat a 0 * Fhat 0 b|
        + |(F a b - F a 0 * F 0 b)
          - (Fhat a b - Fhat a 0 * Fhat 0 b)| := by
        have := abs_sub_abs_le_abs_sub (F a b - F a 0 * F 0 b)
          (Fhat a b - Fhat a 0 * Fhat 0 b)
        linarith [abs_nonneg ((F a b - F a 0 * F 0 b)
          - (Fhat a b - Fhat a 0 * Fhat 0 b))]
    _ ≤ |Fhat a b - Fhat a 0 * Fhat 0 b| + (3 * ε + ε ^ 2) := by
        linarith
    _ = |Fhat a b - Fhat a 0 * Fhat 0 b| + 3 * ε + ε ^ 2 := by ring

end NCG
