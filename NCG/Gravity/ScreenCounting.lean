/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Screen-entropy counting and Newton normalization
(GR_emergence, Phase 1)

* `k4EntropyRate`, `k4_entropy_rate` — `cor:uniform-k4-screen`: the
  quantum entropy per cell of the uniform `K₄` regenerative screen
  is the Markov entropy rate of its transition matrix,
  `h(Π) = log 3` (three equiprobable admissible successors from
  each resolved state);
* `newton_from_screen_density` — `prop:newton-from-screen-density`:
  `G_ren = 1/(4η_scr)` is the unique coupling with `4Gη = 1`;
* `k4_newton_normalization`, `k4_epsilon_squared` —
  `cor:k4-newton-normalization`: `η = h(Π)/(N ε^{d-1})` gives
  `G = N ε^{d-1}/(4h(Π))`, and at the `d = 3`, `N∂ = 1` endpoint
  `ε² = 4 log 3 · G`;
* `screen_law_bulk_stable` — `cor:microscopic-screen-law`: the
  boundary-local area law is stable under adding the bulk-state
  entropy.
-/

namespace NCG

open Real

/-- The entropy rate of the uniform `K₄` regenerative record: state
space `Fin 4`, uniform stationary law, and uniform transitions to
the three other states. -/
noncomputable def k4EntropyRate : ℝ :=
  -∑ x : Fin 4, ∑ y : Fin 4,
    (4:ℝ)⁻¹ * (if x ≠ y then (3:ℝ)⁻¹ else 0)
      * Real.log (if x ≠ y then (3:ℝ)⁻¹ else 0)

/-- `cor:uniform-k4-screen`: `h_scr^q = h(Π) = log 3`. -/
theorem k4_entropy_rate : k4EntropyRate = Real.log 3 := by
  have hterm : ∀ x y : Fin 4,
      (4:ℝ)⁻¹ * (if x ≠ y then (3:ℝ)⁻¹ else 0)
          * Real.log (if x ≠ y then (3:ℝ)⁻¹ else 0)
      = if x ≠ y then -((12:ℝ)⁻¹ * Real.log 3) else 0 := by
    intro x y
    by_cases h : x ≠ y
    · simp only [if_pos h]
      rw [Real.log_inv]
      ring
    · simp only [if_neg h]
      ring
  unfold k4EntropyRate
  simp only [hterm]
  rw [Fin.sum_univ_four]
  simp only [Fin.sum_univ_four]
  norm_num [Fin.ext_iff]
  ring

/-- `prop:newton-from-screen-density`: the coupling `G = 1/(4η)` is
the unique solution of the calibration `4 G η = 1`. -/
theorem newton_from_screen_density (eta G : ℝ) (heta : eta ≠ 0) :
    4 * G * eta = 1 ↔ G = 1 / (4 * eta) := by
  rw [eq_div_iff (by simpa using heta)]
  constructor <;> intro h <;> linarith

/-- `cor:k4-newton-normalization`: with cell area `a_ε = N ε^{d-1}`
and predictive-pure entropy density `η = h(Π)/(N ε^{d-1})`, the
coupling is `G = N ε^{d-1}/(4 h(Π))`. -/
theorem k4_newton_normalization (h N eps : ℝ) (d : ℕ)
    (hh : h ≠ 0) (hN : N ≠ 0) (heps : eps ≠ 0) :
    1 / (4 * (h / (N * eps ^ (d - 1))))
      = N * eps ^ (d - 1) / (4 * h) := by
  have hpow : eps ^ (d - 1) ≠ 0 := pow_ne_zero _ heps
  field_simp

/-- `cor:k4-newton-normalization`, `d = 3` endpoint with the
normalized screen-area convention `N∂ = 1`: `ε² = 4 log 3 · G`. -/
theorem k4_epsilon_squared (eps G : ℝ)
    (hG : G = 1 * eps ^ 2 / (4 * Real.log 3)) :
    eps ^ 2 = 4 * Real.log 3 * G := by
  have h3 : Real.log 3 ≠ 0 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 3)
    linarith
  rw [hG]
  field_simp

/-- `cor:microscopic-screen-law`: adding the bulk-state entropy
preserves the boundary-local area law with the same error budget:
if `|S_split - η·Area - B_r| ≤ E` then
`|S_scr - η·Area - S_bulk - B_r| ≤ E` for `S_scr = S_split + S_bulk`. -/
theorem screen_law_bulk_stable (S Sbulk eta area Br E : ℝ)
    (hS : |S - (eta * area + Br)| ≤ E) :
    |(S + Sbulk) - (eta * area + Sbulk + Br)| ≤ E := by
  have h1 : (S + Sbulk) - (eta * area + Sbulk + Br)
      = S - (eta * area + Br) := by ring
  rw [h1]
  exact hS

end NCG
