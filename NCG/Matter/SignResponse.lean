/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical sign response (`thm:v5-sign-response`, SM manuscript)

Let `u` be the (nonzero) native sign source and `M` the stable
future transport with `‖M‖ ≤ θ < 1` on a complex Banach space.  If
`M` commutes with the central sign projector `P` and `P u = u`,
then the resolvent image `v = (I - M)⁻¹ u` — the unique solution of
`v - M v = u` — satisfies

  `P v = v`,  `v ≠ 0`,  and
  `‖u‖²/(1+θ)² ≤ ‖v‖² ≤ ‖u‖²/(1-θ)²`:

stable equivariant transport cannot erase an already loaded sign
source.  Existence of the resolvent comes from the Neumann series
(`Units.oneSub` in the Banach algebra of endomorphisms); the energy
bounds are the elementary inverse-singular-value estimates.
-/

namespace NCG

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

/-- `thm:v5-sign-response`: the resolvent image
`v = (I - M)⁻¹ u` of a sign source `u` fixed by a central
projector commuting with the stable transport `M` is again fixed,
nonzero, unique, and satisfies the two-sided energy bound. -/
theorem sign_response (M P : E →L[ℂ] E) (u : E) (θ : ℝ)
    (hθ : θ < 1) (hM : ‖M‖ ≤ θ)
    (hcomm : P * M = M * P) (hPu : P u = u) (hu : u ≠ 0) :
    ∃ v : E, (v - M v = u) ∧ (∀ w : E, w - M w = u → w = v)
      ∧ P v = v ∧ v ≠ 0
      ∧ ‖u‖ ^ 2 / (1 + θ) ^ 2 ≤ ‖v‖ ^ 2
      ∧ ‖v‖ ^ 2 ≤ ‖u‖ ^ 2 / (1 - θ) ^ 2 := by
  have hθ0 : (0 : ℝ) ≤ θ := le_trans (norm_nonneg M) hM
  have hM1 : ‖M‖ < 1 := lt_of_le_of_lt hM hθ
  -- the Neumann-series unit `1 - M`
  let W : (E →L[ℂ] E)ˣ := Units.oneSub M hM1
  have hWval : (↑W : E →L[ℂ] E) = 1 - M := rfl
  have hWW : ∀ w : E, (↑W⁻¹ : E →L[ℂ] E) ((↑W : E →L[ℂ] E) w) = w := by
    intro w
    change ((↑W⁻¹ * ↑W : E →L[ℂ] E)) w = w
    rw [W.inv_mul]
    rfl
  have hWW' : ∀ w : E, (↑W : E →L[ℂ] E) ((↑W⁻¹ : E →L[ℂ] E) w) = w := by
    intro w
    change ((↑W * ↑W⁻¹ : E →L[ℂ] E)) w = w
    rw [W.mul_inv]
    rfl
  set v : E := (↑W⁻¹ : E →L[ℂ] E) u with hv
  -- `v` solves the resolvent equation
  have hsol : v - M v = u := by
    have h1 : (↑W : E →L[ℂ] E) v = u := hWW' u
    rw [hWval] at h1
    simpa using h1
  -- uniqueness
  have huniq : ∀ w : E, w - M w = u → w = v := by
    intro w hw
    have h1 : (↑W : E →L[ℂ] E) w = u := by
      rw [hWval]
      simpa using hw
    have h2 := congrArg (fun x => (↑W⁻¹ : E →L[ℂ] E) x) h1
    rw [hWW w] at h2
    rw [h2, hv]
  -- the sign projector fixes `v`
  have hPv : P v = v := by
    have hcW : Commute P (↑W : E →L[ℂ] E) := by
      rw [hWval]
      exact (Commute.one_right P).sub_right hcomm
    have hcWinv : Commute P (↑W⁻¹ : E →L[ℂ] E) := hcW.units_inv_right
    have h : (P * (↑W⁻¹ : E →L[ℂ] E)) u
        = ((↑W⁻¹ : E →L[ℂ] E) * P) u := by
      rw [hcWinv.eq]
    rw [hv]
    change (P * (↑W⁻¹ : E →L[ℂ] E)) u = (↑W⁻¹ : E →L[ℂ] E) u
    rw [h]
    change (↑W⁻¹ : E →L[ℂ] E) (P u) = (↑W⁻¹ : E →L[ℂ] E) u
    rw [hPu]
  -- nonvanishing
  have hvne : v ≠ 0 := by
    intro h0
    apply hu
    rw [← hsol, h0]
    simp
  -- elementary two-sided norm bounds
  have hMv : ‖M v‖ ≤ θ * ‖v‖ :=
    le_trans (M.le_opNorm v)
      (mul_le_mul_of_nonneg_right hM (norm_nonneg v))
  have hlow : (1 - θ) * ‖v‖ ≤ ‖u‖ := by
    have h1 : ‖v‖ - ‖M v‖ ≤ ‖v - M v‖ := norm_sub_norm_le v (M v)
    rw [hsol] at h1
    linarith
  have hup : ‖u‖ ≤ (1 + θ) * ‖v‖ := by
    have h1 : ‖v - M v‖ ≤ ‖v‖ + ‖M v‖ := norm_sub_le v (M v)
    rw [hsol] at h1
    linarith
  refine ⟨v, hsol, huniq, hPv, hvne, ?_, ?_⟩
  · have hpos : (0 : ℝ) < (1 + θ) ^ 2 :=
      pow_pos (by linarith) 2
    rw [div_le_iff₀ hpos]
    have h2 := mul_self_le_mul_self (norm_nonneg u) hup
    nlinarith [norm_nonneg v]
  · have hpos : (0 : ℝ) < (1 - θ) ^ 2 :=
      pow_pos (by linarith) 2
    rw [le_div_iff₀ hpos]
    have h2 := mul_self_le_mul_self
      (mul_nonneg (by linarith) (norm_nonneg v)) hlow
    nlinarith [norm_nonneg u]

end NCG
