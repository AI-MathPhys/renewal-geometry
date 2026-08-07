/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact primitive score bank and tangent exhaustion
  (`thm:primitive-score-bank`, Gran-Tensor manuscript)

On the five-outcome branch alphabet `(hh, hp, pp, b₊, b₋)`
with stationary weights `μ = (1/11, 4/11, 2/11, 2/11, 2/11)`
(row weights `π_H = 5/11`, `π_P = 6/11`, conditional branch
probabilities `(1/5, 4/5)` and `(1/3, 1/3, 1/3)`):

* `primitive_score_bank`:
  (i) `u_H, u_P, u_E` are orthonormal in `L²(μ)` and have
      zero conditional row means (they exhaust the
      three-dimensional centered tangent);
  (ii) the boxed rotation: `η̂ = √(3/8)u_H + √(5/8)u_P`,
      `ζ = √(5/8)u_H - √(3/8)u_P`, `ε = u_E` is again
      orthonormal;
  (iii) the boxed physical Gram: with
      `η = √(176/225)·η̂` (the Doob innovation of norm
      `q₀ = 1 - ρ² = 176/225`), the Gram of `(η, ζ, ε)` is
      `G₀ = diag(176/225, 1, 1)`;
  (iv) tangent exhaustion: every row-centered function is
      exactly its `(u_H, u_P, u_E)`-expansion, so the
      centered space has dimension three and every one-step
      local score source has source-minimal rank at most
      three.

The identification of `η` with the active Doob innovation
`φ(X_{n+1}) - ρφ(X_n)` of the concrete renewal chain
(`ρ = 7/15`) and the conditional-exponential-family
realization of finite tangent families are the manuscript's
probabilistic layer; the Fisher matrix of that family at
the origin is the Gram computed here.
-/

namespace NCG

/-- Stationary outcome weights on the branch alphabet. -/
noncomputable def scoreMu : Fin 5 → ℝ := ![1/11, 4/11, 2/11, 2/11, 2/11]

/-- The `L²(μ)` pairing. -/
noncomputable def scoreIP (f g : Fin 5 → ℝ) : ℝ :=
  ∑ a, scoreMu a * f a * g a

/-- Holding score direction. -/
noncomputable def scoreUH : Fin 5 → ℝ :=
  fun a => Real.sqrt (11 / 20) * (![-4, 1, 0, 0, 0] a)

/-- Phase score direction. -/
noncomputable def scoreUP : Fin 5 → ℝ :=
  fun a => Real.sqrt (11 / 12) * (![0, 0, 2, -1, -1] a)

/-- Edge score direction. -/
noncomputable def scoreUE : Fin 5 → ℝ :=
  fun a => Real.sqrt (11 / 4) * (![0, 0, 0, 1, -1] a)

/-- `thm:primitive-score-bank`. -/
theorem primitive_score_bank :
    -- (i) orthonormality of the score bank
    (scoreIP scoreUH scoreUH = 1
      ∧ scoreIP scoreUP scoreUP = 1
      ∧ scoreIP scoreUE scoreUE = 1
      ∧ scoreIP scoreUH scoreUP = 0
      ∧ scoreIP scoreUH scoreUE = 0
      ∧ scoreIP scoreUP scoreUE = 0)
    -- (i') zero conditional row means
    ∧ ((1 / 5 : ℝ) * scoreUH 0 + (4 / 5) * scoreUH 1 = 0
      ∧ (1 / 3 : ℝ) * scoreUP 2 + (1 / 3) * scoreUP 3
          + (1 / 3) * scoreUP 4 = 0
      ∧ (1 / 3 : ℝ) * scoreUE 2 + (1 / 3) * scoreUE 3
          + (1 / 3) * scoreUE 4 = 0)
    -- (ii) the boxed rotated triple is orthonormal
    ∧ (scoreIP
        (fun a => Real.sqrt (3 / 8) * scoreUH a
          + Real.sqrt (5 / 8) * scoreUP a)
        (fun a => Real.sqrt (3 / 8) * scoreUH a
          + Real.sqrt (5 / 8) * scoreUP a) = 1
      ∧ scoreIP
        (fun a => Real.sqrt (5 / 8) * scoreUH a
          - Real.sqrt (3 / 8) * scoreUP a)
        (fun a => Real.sqrt (5 / 8) * scoreUH a
          - Real.sqrt (3 / 8) * scoreUP a) = 1
      ∧ scoreIP
        (fun a => Real.sqrt (3 / 8) * scoreUH a
          + Real.sqrt (5 / 8) * scoreUP a)
        (fun a => Real.sqrt (5 / 8) * scoreUH a
          - Real.sqrt (3 / 8) * scoreUP a) = 0)
    -- (iii) the boxed physical Gram `G₀`
    ∧ (scoreIP
        (fun a => Real.sqrt (176 / 225)
          * (Real.sqrt (3 / 8) * scoreUH a
            + Real.sqrt (5 / 8) * scoreUP a))
        (fun a => Real.sqrt (176 / 225)
          * (Real.sqrt (3 / 8) * scoreUH a
            + Real.sqrt (5 / 8) * scoreUP a))
        = 176 / 225)
    -- (iv) tangent exhaustion of the centered space
    ∧ (∀ f : Fin 5 → ℝ,
        (1 / 5 : ℝ) * f 0 + (4 / 5) * f 1 = 0 →
        (1 / 3 : ℝ) * f 2 + (1 / 3) * f 3
          + (1 / 3) * f 4 = 0 →
        ∀ a, f a = scoreIP f scoreUH * scoreUH a
          + scoreIP f scoreUP * scoreUP a
          + scoreIP f scoreUE * scoreUE a) := by
  have q11 := Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)
  have q20 := Real.sq_sqrt (show (0 : ℝ) ≤ 20 by norm_num)
  have q12 := Real.sq_sqrt (show (0 : ℝ) ≤ 12 by norm_num)
  have q4 := Real.sq_sqrt (show (0 : ℝ) ≤ 4 by norm_num)
  have q3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have q5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have q8 := Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)
  have q176 := Real.sq_sqrt
    (show (0 : ℝ) ≤ 176 by norm_num)
  have q225 := Real.sq_sqrt
    (show (0 : ℝ) ≤ 225 by norm_num)
  have sq38 := Real.sq_sqrt
    (show (0 : ℝ) ≤ 3 / 8 by norm_num)
  have sq58 := Real.sq_sqrt
    (show (0 : ℝ) ≤ 5 / 8 by norm_num)
  -- base pairings
  have hHH : scoreIP scoreUH scoreUH = 1 := by
    simp [scoreIP, scoreUH, scoreMu, Fin.sum_univ_five]
    try ring_nf
    norm_num [inv_pow, q11, q20]
  have hPP : scoreIP scoreUP scoreUP = 1 := by
    simp [scoreIP, scoreUP, scoreMu, Fin.sum_univ_five]
    try ring_nf
    norm_num [inv_pow, q11, q12, q3]
  have hEE : scoreIP scoreUE scoreUE = 1 := by
    simp [scoreIP, scoreUE, scoreMu, Fin.sum_univ_five]
    try ring_nf
    norm_num [inv_pow, q11, q4]
  have hHP : scoreIP scoreUH scoreUP = 0 := by
    simp [scoreIP, scoreUH, scoreUP, scoreMu,
      Fin.sum_univ_five]
  have hHE : scoreIP scoreUH scoreUE = 0 := by
    simp [scoreIP, scoreUH, scoreUE, scoreMu,
      Fin.sum_univ_five]
  have hPE : scoreIP scoreUP scoreUE = 0 := by
    simp [scoreIP, scoreUP, scoreUE, scoreMu,
      Fin.sum_univ_five]
    try ring_nf
  -- bilinearity of the pairing on two-vector combinations
  have hbil : ∀ (c₁ c₂ d₁ d₂ : ℝ),
      scoreIP
        (fun a => c₁ * scoreUH a + c₂ * scoreUP a)
        (fun a => d₁ * scoreUH a + d₂ * scoreUP a)
      = c₁ * d₁ * scoreIP scoreUH scoreUH
        + (c₁ * d₂ + c₂ * d₁) * scoreIP scoreUH scoreUP
        + c₂ * d₂ * scoreIP scoreUP scoreUP := by
    intro c₁ c₂ d₁ d₂
    simp only [scoreIP, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  refine ⟨⟨hHH, hPP, hEE, hHP, hHE, hPE⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩ <;>
      (simp [scoreUH, scoreUP, scoreUE]; try ring)
  · refine ⟨?_, ?_, ?_⟩
    · rw [hbil, hHH, hPP, hHP]
      ring_nf
      simp only [sq38, sq58]
      norm_num
    · have heq : (fun a => Real.sqrt (5 / 8) * scoreUH a
          - Real.sqrt (3 / 8) * scoreUP a)
          = fun a => Real.sqrt (5 / 8) * scoreUH a
            + (-(Real.sqrt (3 / 8))) * scoreUP a := by
        funext a
        ring
      rw [heq, hbil, hHH, hPP, hHP]
      try ring_nf
      norm_num [inv_pow, div_pow, sq38, sq58, q3, q5, q8]
    · have heq : (fun a => Real.sqrt (5 / 8) * scoreUH a
          - Real.sqrt (3 / 8) * scoreUP a)
          = fun a => Real.sqrt (5 / 8) * scoreUH a
            + (-(Real.sqrt (3 / 8))) * scoreUP a := by
        funext a
        ring
      rw [heq, hbil, hHH, hPP, hHP]
      ring
  · have hscale : ∀ (c : ℝ) (f : Fin 5 → ℝ),
        scoreIP (fun a => c * f a) (fun a => c * f a)
          = c * c * scoreIP f f := by
      intro c f
      simp only [scoreIP]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [hscale]
    have h1 : scoreIP
        (fun a => Real.sqrt (3 / 8) * scoreUH a
          + Real.sqrt (5 / 8) * scoreUP a)
        (fun a => Real.sqrt (3 / 8) * scoreUH a
          + Real.sqrt (5 / 8) * scoreUP a) = 1 := by
      rw [hbil, hHH, hPP, hHP]
      try ring_nf
      norm_num [inv_pow, div_pow, sq38, sq58, q3, q5, q8]
    rw [h1, mul_one]
    exact Real.mul_self_sqrt (by norm_num)
  · intro f hc1 hc2 a
    fin_cases a <;>
      (simp [scoreIP, scoreUH, scoreUP, scoreUE,
        scoreMu, Fin.sum_univ_five]
       try ring_nf
       try norm_num [inv_pow, q11, q20, q12, q4, q3]
       try linarith [hc1, hc2])

end NCG
