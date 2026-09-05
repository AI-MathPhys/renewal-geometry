/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SharpTrotterCommutator

/-!
# The group-commutator approximation with explicit constant

The cubic estimate behind the bracket branch of
`thm:SMST-channel-direct-bracket`: for contractive exponentials
with `‖X‖, ‖Y‖ ≤ β`,

`‖e^X·e^Y·e^{-X}·e^{-Y} - e^{[X,Y]}‖ ≤ 28·β³`.

Proof: the interpolation curve
`K(s) = e^{(1-s²)•C}·Γ(s)` with `C = [X,Y]` and
`Γ(s) = e^{s•X}e^{s•Y}e^{-s•X}e^{-s•Y}` satisfies
`K' = e^{(1-s²)•C}·(Γ'(s) - 2s•(C·Γ(s)))`, and the defect
`Γ' - 2s•CΓ` decomposes into two first-order conjugation errors
(`≤ 10sβ³` each, by the commutator integral bound
`exp_comm_le` and `exp_sub_one_le_contr`) plus two second-order
commutator remainders (`≤ 4s²β³` each, by
`comm_exp_second_order`), for a total integrand bound
`28s²β³ ≤ 28β³`.  Integrating over `[0,1]` gives the constant
`28` — comfortably inside the manuscript's boxed `64` after the
channel-level Ad-Lipschitz doubling. -/

open Set intervalIntegral NormedSpace

namespace NCG
namespace SharpTrotter

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]
  [CompleteSpace A] [NormedAlgebra ℚ A]

set_option maxHeartbeats 1000000 in
-- The interpolation-curve proof elaborates one large FTC
-- integrand with four exponential factors; the default
-- heartbeat budget is insufficient for its `whnf` checks.
/-- **Group-commutator approximation**: for contractive
exponentials with `‖X‖, ‖Y‖ ≤ β`,
`‖e^X e^Y e^{-X} e^{-Y} - e^{[X,Y]}‖ ≤ 28β³`. -/
theorem group_comm_exp_bound (X Y : A) (β : ℝ) (hβ : 0 ≤ β)
    (hXβ : ‖X‖ ≤ β) (hYβ : ‖Y‖ ≤ β)
    (hcX : ∀ u : ℝ, ‖exp (u • X)‖ ≤ 1)
    (hcY : ∀ u : ℝ, ‖exp (u • Y)‖ ≤ 1)
    (hcC : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖exp (u • (X * Y - Y * X))‖ ≤ 1) :
    ‖exp X * exp Y * exp (-X) * exp (-Y)
        - exp (X * Y - Y * X)‖
      ≤ 28 * β ^ 3 := by
  set C : A := X * Y - Y * X with hCdef
  clear_value C
  have hcX' : ∀ u : ℝ, ‖exp (u • (-X))‖ ≤ 1 := by
    intro u
    have h : u • (-X) = (-u) • X := by module
    rw [h]
    exact hcX (-u)
  have hcY' : ∀ u : ℝ, ‖exp (u • (-Y))‖ ≤ 1 := by
    intro u
    have h : u • (-Y) = (-u) • Y := by module
    rw [h]
    exact hcY (-u)
  have hcomm2 : ∀ P Q : A, ‖P * Q - Q * P‖ ≤ 2 * ‖P‖ * ‖Q‖ := by
    intro P Q
    have h₁ := norm_mul_le P Q
    have h₂ := norm_mul_le Q P
    have h₃ := norm_sub_le (P * Q) (Q * P)
    have h₄ : ‖Q‖ * ‖P‖ = ‖P‖ * ‖Q‖ := mul_comm _ _
    linarith
  have hCβ : ‖C‖ ≤ 2 * β ^ 2 := by
    have hXn := norm_nonneg X
    have hYn := norm_nonneg Y
    rw [hCdef]
    calc ‖X * Y - Y * X‖ ≤ 2 * ‖X‖ * ‖Y‖ := hcomm2 X Y
      _ ≤ 2 * β ^ 2 := by nlinarith
  set Γ : ℝ → A := fun s =>
    exp (s • X) * exp (s • Y) * exp (s • (-X)) * exp (s • (-Y))
    with hΓdef
  set K : ℝ → A := fun s => exp ((1 - s * s) • C) * Γ s
    with hKdef
  have hK0 : K 0 = exp C := by
    simp [hKdef, hΓdef, exp_zero]
  have hK1 : K 1
      = exp X * exp Y * exp (-X) * exp (-Y) := by
    simp [hKdef, hΓdef, exp_zero]
  -- derivative of Γ
  have hΓderiv : ∀ s : ℝ, HasDerivAt Γ
      (exp (s • X)
        * (X * exp (s • Y) - exp (s • Y) * X)
        * exp (s • (-X)) * exp (s • (-Y))
      + exp (s • X) * exp (s • Y)
        * (Y * exp (s • (-X)) - exp (s • (-X)) * Y)
        * exp (s • (-Y))) s := by
    intro s
    have h₁ := hasDerivAt_exp_smul_const' X s
    have h₂ := hasDerivAt_exp_smul_const' Y s
    have h₃ := hasDerivAt_exp_smul_const' (-X) s
    have h₄ := hasDerivAt_exp_smul_const' (-Y) s
    have hmul := ((h₁.mul h₂).mul h₃).mul h₄
    simp only [Pi.mul_apply] at hmul
    have hgen : ∀ eA eB eA2 eB2 : A,
        eA * X = X * eA → eB * Y = Y * eB →
        ((X * eA * eB + eA * (Y * eB)) * eA2
            + eA * eB * (-X * eA2)) * eB2
          + eA * eB * eA2 * (-Y * eB2)
        = eA * (X * eB - eB * X) * eA2 * eB2
          + eA * eB * (Y * eA2 - eA2 * Y) * eB2 := by
      intro eA eB eA2 eB2 hA hB
      have r₁ : X * eA * eB = eA * (X * eB) := by
        rw [← hA]
        noncomm_ring
      have r₂ : eA * (Y * eB) = eA * eB * Y := by
        rw [← hB]
        noncomm_ring
      rw [r₁, r₂]
      noncomm_ring
    have hval := hgen (exp (s • X)) (exp (s • Y))
      (exp (s • (-X))) (exp (s • (-Y)))
      (expCurve_comm X s) (expCurve_comm Y s)
    rw [hval] at hmul
    exact hmul
  -- derivative of the weight
  have hEderiv : ∀ s : ℝ, HasDerivAt
      (fun s : ℝ => exp ((1 - s * s) • C))
      (-((s + s) • (C * exp ((1 - s * s) • C)))) s := by
    intro s
    have hinner : HasDerivAt (fun s : ℝ => 1 - s * s)
        (-(s + s)) s := by
      have hsq : HasDerivAt (fun x : ℝ => x * x)
          (1 * s + s * 1) s :=
        (hasDerivAt_id s).mul (hasDerivAt_id s)
      have := hsq.const_sub 1
      simpa using this
    have h := (hasDerivAt_exp_smul_const' C (1 - s * s)).scomp
      s hinner
    rw [neg_smul] at h
    exact h
  -- derivative of K
  have hKderiv : ∀ s : ℝ, HasDerivAt K
      (exp ((1 - s * s) • C)
        * ((exp (s • X)
            * (X * exp (s • Y) - exp (s • Y) * X)
            * exp (s • (-X)) * exp (s • (-Y))
          + exp (s • X) * exp (s • Y)
            * (Y * exp (s • (-X)) - exp (s • (-X)) * Y)
            * exp (s • (-Y)))
          - (s + s) • (C * Γ s))) s := by
    intro s
    have hmul := (hEderiv s).mul (hΓderiv s)
    have hgen2 : ∀ e g dd : A, C * e = e * C →
        -((s + s) • (C * e)) * g + e * dd
        = e * (dd - (s + s) • (C * g)) := by
      intro e g dd hc
      rw [neg_mul, smul_mul_assoc, hc, mul_assoc, mul_sub,
        mul_smul_comm]
      abel
    have hc : C * exp ((1 - s * s) • C)
        = exp ((1 - s * s) • C) * C :=
      (expCurve_comm C (1 - s * s)).symm
    have hval := hgen2 (exp ((1 - s * s) • C)) (Γ s)
      (exp (s • X)
        * (X * exp (s • Y) - exp (s • Y) * X)
        * exp (s • (-X)) * exp (s • (-Y))
      + exp (s • X) * exp (s • Y)
        * (Y * exp (s • (-X)) - exp (s • (-X)) * Y)
        * exp (s • (-Y))) hc
    rw [hval] at hmul
    exact hmul
  -- continuity of the K-derivative
  have cX := continuous_expCurve (A := A) X
  have cY := continuous_expCurve (A := A) Y
  have cX' := continuous_expCurve (A := A) (-X)
  have cY' := continuous_expCurve (A := A) (-Y)
  have cC : Continuous fun s : ℝ =>
      exp ((1 - s * s) • C) :=
    (continuous_expCurve C).comp
      (continuous_const.sub (continuous_id.mul continuous_id))
  have cΓ : Continuous Γ := by
    rw [hΓdef]
    exact ((cX.mul cY).mul cX').mul cY'
  have hcontK : Continuous fun s : ℝ =>
      exp ((1 - s * s) • C)
        * ((exp (s • X)
            * (X * exp (s • Y) - exp (s • Y) * X)
            * exp (s • (-X)) * exp (s • (-Y))
          + exp (s • X) * exp (s • Y)
            * (Y * exp (s • (-X)) - exp (s • (-X)) * Y)
            * exp (s • (-Y)))
          - (s + s) • (C * Γ s)) := by
    refine cC.mul (Continuous.sub ?_ ?_)
    · refine Continuous.add ?_ ?_
      · exact ((cX.mul ((continuous_const.mul cY).sub
          (cY.mul continuous_const))).mul cX').mul cY'
      · exact ((cX.mul cY).mul
          ((continuous_const.mul cX').sub
            (cX'.mul continuous_const))).mul cY'
    · exact (continuous_id.add continuous_id).smul
        (continuous_const.mul cΓ)
  have hftc :
      (∫ s in (0 : ℝ)..1,
        exp ((1 - s * s) • C)
          * ((exp (s • X)
              * (X * exp (s • Y) - exp (s • Y) * X)
              * exp (s • (-X)) * exp (s • (-Y))
            + exp (s • X) * exp (s • Y)
              * (Y * exp (s • (-X)) - exp (s • (-X)) * Y)
              * exp (s • (-Y)))
            - (s + s) • (C * Γ s)))
      = K 1 - K 0 :=
    integral_eq_sub_of_hasDerivAt
      (fun s _ => hKderiv s) (hcontK.intervalIntegrable 0 1)
  rw [← hK1, ← hK0, ← hftc]
  -- ===== the integrand bound `28s²β³ ≤ 28β³` =====
  have hbound : ∀ s ∈ uIoc (0 : ℝ) 1,
      ‖exp ((1 - s * s) • C)
        * ((exp (s • X)
            * (X * exp (s • Y) - exp (s • Y) * X)
            * exp (s • (-X)) * exp (s • (-Y))
          + exp (s • X) * exp (s • Y)
            * (Y * exp (s • (-X)) - exp (s • (-X)) * Y)
            * exp (s • (-Y)))
          - (s + s) • (C * Γ s))‖ ≤ 28 * β ^ 3 := by
    intro s hs
    rw [uIoc_of_le zero_le_one] at hs
    have hs0 : (0 : ℝ) ≤ s := hs.1.le
    have hs1 : s ≤ 1 := hs.2
    have hEC : ‖exp ((1 - s * s) • C)‖ ≤ 1 :=
      hcC (1 - s * s) ⟨by nlinarith, by nlinarith⟩
    -- second-order remainders
    have hRY := comm_exp_second_order Y X s hs0
      (fun u _ => hcY u)
    have hRX := comm_exp_second_order (-X) Y s hs0
      (fun u _ => hcX' u)
    have hnegC : (-X) * Y - Y * (-X) = -C := by
      rw [hCdef, neg_mul, mul_neg]
      abel
    have hYXC : ‖Y * X - X * Y‖ = ‖C‖ := by
      have h : Y * X - X * Y = -C := by
        rw [hCdef]
        abel
      rw [h, norm_neg]
    rw [hnegC, norm_neg, norm_neg] at hRX
    rw [hYXC] at hRY
    set RY : A := exp (s • Y) * X - X * exp (s • Y)
      - s • (Y * X - X * Y) with hRYdef
    set RX : A := exp (s • (-X)) * Y - Y * exp (s • (-X))
      - s • (-C) with hRXdef
    clear_value RY RX
    -- first-order identities
    have hI₁ : X * exp (s • Y) - exp (s • Y) * X
        = s • C - RY := by
      rw [hRYdef, hCdef]
      have h : s • (Y * X - X * Y)
          = -(s • (X * Y - Y * X)) := by
        rw [← smul_neg]
        congr 1
        abel
      rw [h]
      abel
    have hI₂ : Y * exp (s • (-X)) - exp (s • (-X)) * Y
        = s • C - RX := by
      rw [hRXdef]
      module
    -- distribute
    have hG₁ : exp (s • X)
        * (X * exp (s • Y) - exp (s • Y) * X)
        * exp (s • (-X)) * exp (s • (-Y))
        = s • (exp (s • X) * C * exp (s • (-X))
            * exp (s • (-Y)))
          - exp (s • X) * RY * exp (s • (-X))
            * exp (s • (-Y)) := by
      rw [hI₁]
      simp only [mul_sub, sub_mul, mul_smul_comm,
        smul_mul_assoc]
    have hG₂ : exp (s • X) * exp (s • Y)
        * (Y * exp (s • (-X)) - exp (s • (-X)) * Y)
        * exp (s • (-Y))
        = s • (exp (s • X) * exp (s • Y) * C
            * exp (s • (-Y)))
          - exp (s • X) * exp (s • Y) * RX
            * exp (s • (-Y)) := by
      rw [hI₂]
      simp only [mul_sub, sub_mul, mul_smul_comm,
        smul_mul_assoc]
    -- master decomposition
    have hmaster :
        (exp (s • X)
            * (X * exp (s • Y) - exp (s • Y) * X)
            * exp (s • (-X)) * exp (s • (-Y))
          + exp (s • X) * exp (s • Y)
            * (Y * exp (s • (-X)) - exp (s • (-X)) * Y)
            * exp (s • (-Y)))
          - (s + s) • (C * Γ s)
        = s • (exp (s • X) * C * exp (s • (-X))
              * exp (s • (-Y)) - C * Γ s)
          + s • (exp (s • X) * exp (s • Y) * C
              * exp (s • (-Y)) - C * Γ s)
          - exp (s • X) * RY * exp (s • (-X))
            * exp (s • (-Y))
          - exp (s • X) * exp (s • Y) * RX
            * exp (s • (-Y)) := by
      rw [hG₁, hG₂]
      module
    -- P₁ bound
    have hInvX : exp (s • X) * exp (s • (-X)) = 1 := by
      have hcm : Commute (s • X) (s • (-X)) :=
        (((Commute.refl X).neg_right).smul_left s).smul_right s
      rw [← exp_add_of_commute hcm]
      have h0 : s • X + s • (-X) = 0 := by module
      rw [h0, exp_zero]
    have hsubone : ∀ (Z : A), ‖Z‖ ≤ β →
        (∀ u : ℝ, ‖exp (u • Z)‖ ≤ 1) →
        ‖exp (s • Z) - 1‖ ≤ s * β := by
      intro Z hZ hcZ
      have h := exp_sub_one_le_contr Z s hs0 (fun u _ => hcZ u)
      calc ‖exp (s • Z) - 1‖ ≤ s * ‖Z‖ := h
        _ ≤ s * β := mul_le_mul_of_nonneg_left hZ hs0
    have hEX1 : ‖exp (s • X) - 1‖ ≤ s * β := hsubone X hXβ hcX
    have hEY1 : ‖exp (s • Y) - 1‖ ≤ s * β := hsubone Y hYβ hcY
    have hEX'1 : ‖exp (s • (-X)) - 1‖ ≤ s * β := by
      refine hsubone (-X) ?_ hcX'
      rw [norm_neg]
      exact hXβ
    -- ‖e^{-s•Y} - Γ‖ ≤ 3sβ
    have htail : ‖exp (s • (-Y)) - Γ s‖ ≤ 3 * (s * β) := by
      have hid : exp (s • (-Y)) - Γ s
          = -(((exp (s • X) - 1) * exp (s • Y)
                * exp (s • (-X))
              + (exp (s • Y) - 1) * exp (s • (-X))
              + (exp (s • (-X)) - 1))
            * exp (s • (-Y))) := by
        simp only [hΓdef]
        noncomm_ring
      rw [hid, norm_neg]
      have h₁ : ‖(exp (s • X) - 1) * exp (s • Y)
          * exp (s • (-X))‖ ≤ s * β := by
        calc ‖(exp (s • X) - 1) * exp (s • Y)
              * exp (s • (-X))‖
            ≤ ‖(exp (s • X) - 1) * exp (s • Y)‖
              * ‖exp (s • (-X))‖ := norm_mul_le _ _
          _ ≤ ‖exp (s • X) - 1‖ * ‖exp (s • Y)‖
              * ‖exp (s • (-X))‖ :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _)
                (norm_nonneg _)
          _ ≤ s * β * 1 * 1 := by
              refine mul_le_mul (mul_le_mul hEX1 (hcY s)
                (norm_nonneg _) ?_) (hcX' s)
                (norm_nonneg _) ?_
              · positivity
              · positivity
          _ = s * β := by ring
      have h₂ : ‖(exp (s • Y) - 1) * exp (s • (-X))‖
          ≤ s * β := by
        calc ‖(exp (s • Y) - 1) * exp (s • (-X))‖
            ≤ ‖exp (s • Y) - 1‖ * ‖exp (s • (-X))‖ :=
              norm_mul_le _ _
          _ ≤ s * β * 1 :=
              mul_le_mul hEY1 (hcX' s) (norm_nonneg _)
                (by positivity)
          _ = s * β := mul_one _
      have hsum : ‖(exp (s • X) - 1) * exp (s • Y)
            * exp (s • (-X))
          + (exp (s • Y) - 1) * exp (s • (-X))
          + (exp (s • (-X)) - 1)‖ ≤ 3 * (s * β) := by
        calc ‖(exp (s • X) - 1) * exp (s • Y)
              * exp (s • (-X))
            + (exp (s • Y) - 1) * exp (s • (-X))
            + (exp (s • (-X)) - 1)‖
            ≤ ‖(exp (s • X) - 1) * exp (s • Y)
                * exp (s • (-X))
              + (exp (s • Y) - 1) * exp (s • (-X))‖
              + ‖exp (s • (-X)) - 1‖ := norm_add_le _ _
          _ ≤ ‖(exp (s • X) - 1) * exp (s • Y)
                * exp (s • (-X))‖
              + ‖(exp (s • Y) - 1) * exp (s • (-X))‖
              + ‖exp (s • (-X)) - 1‖ := by
              have := norm_add_le
                ((exp (s • X) - 1) * exp (s • Y)
                  * exp (s • (-X)))
                ((exp (s • Y) - 1) * exp (s • (-X)))
              linarith
          _ ≤ 3 * (s * β) := by linarith
      calc ‖((exp (s • X) - 1) * exp (s • Y)
            * exp (s • (-X))
          + (exp (s • Y) - 1) * exp (s • (-X))
          + (exp (s • (-X)) - 1))
          * exp (s • (-Y))‖
          ≤ ‖(exp (s • X) - 1) * exp (s • Y)
              * exp (s • (-X))
            + (exp (s • Y) - 1) * exp (s • (-X))
            + (exp (s • (-X)) - 1)‖
            * ‖exp (s • (-Y))‖ := norm_mul_le _ _
        _ ≤ 3 * (s * β) * 1 := by
            refine mul_le_mul hsum (hcY' s) (norm_nonneg _) ?_
            positivity
        _ = 3 * (s * β) := mul_one _
    -- commutator conjugation defects
    have hXC : ‖exp (s • X) * C - C * exp (s • X)‖
        ≤ 4 * (s * β ^ 3) := by
      have h := exp_comm_le X C s hs0 (fun u _ => hcX u)
      have h₂ : ‖X * C - C * X‖ ≤ 2 * β * (2 * β ^ 2) := by
        calc ‖X * C - C * X‖ ≤ 2 * ‖X‖ * ‖C‖ := hcomm2 X C
          _ ≤ 2 * β * (2 * β ^ 2) := by
              have := norm_nonneg X
              have := norm_nonneg C
              nlinarith
      calc ‖exp (s • X) * C - C * exp (s • X)‖
          ≤ s * ‖X * C - C * X‖ := h
        _ ≤ s * (2 * β * (2 * β ^ 2)) :=
            mul_le_mul_of_nonneg_left h₂ hs0
        _ = 4 * (s * β ^ 3) := by ring
    have hYC : ‖exp (s • Y) * C - C * exp (s • Y)‖
        ≤ 4 * (s * β ^ 3) := by
      have h := exp_comm_le Y C s hs0 (fun u _ => hcY u)
      have h₂ : ‖Y * C - C * Y‖ ≤ 2 * β * (2 * β ^ 2) := by
        calc ‖Y * C - C * Y‖ ≤ 2 * ‖Y‖ * ‖C‖ := hcomm2 Y C
          _ ≤ 2 * β * (2 * β ^ 2) := by
              have := norm_nonneg Y
              have := norm_nonneg C
              nlinarith
      calc ‖exp (s • Y) * C - C * exp (s • Y)‖
          ≤ s * ‖Y * C - C * Y‖ := h
        _ ≤ s * (2 * β * (2 * β ^ 2)) :=
            mul_le_mul_of_nonneg_left h₂ hs0
        _ = 4 * (s * β ^ 3) := by ring
    -- P₁: ‖e^{sX}·C·e^{-sX}·e^{-sY} - C·Γ‖ ≤ 10sβ³
    have hP₁ : ‖exp (s • X) * C * exp (s • (-X))
        * exp (s • (-Y)) - C * Γ s‖
        ≤ 10 * (s * β ^ 3) := by
      have hEq : exp (s • X) * C * exp (s • (-X))
          * exp (s • (-Y)) - C * Γ s
          = (exp (s • X) * C - C * exp (s • X))
              * exp (s • (-X)) * exp (s • (-Y))
            + C * (exp (s • (-Y)) - Γ s) := by
        have hchain : C * exp (s • X) * exp (s • (-X))
            * exp (s • (-Y)) = C * exp (s • (-Y)) := by
          rw [mul_assoc C (exp (s • X)) (exp (s • (-X))),
            hInvX, mul_one]
        rw [sub_mul, sub_mul, mul_sub, hchain]
        abel
      rw [hEq]
      have h₁ : ‖(exp (s • X) * C - C * exp (s • X))
          * exp (s • (-X)) * exp (s • (-Y))‖
          ≤ 4 * (s * β ^ 3) := by
        calc ‖(exp (s • X) * C - C * exp (s • X))
              * exp (s • (-X)) * exp (s • (-Y))‖
            ≤ ‖(exp (s • X) * C - C * exp (s • X))
                * exp (s • (-X))‖ * ‖exp (s • (-Y))‖ :=
              norm_mul_le _ _
          _ ≤ ‖exp (s • X) * C - C * exp (s • X)‖
              * ‖exp (s • (-X))‖ * ‖exp (s • (-Y))‖ :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _)
                (norm_nonneg _)
          _ ≤ 4 * (s * β ^ 3) * 1 * 1 := by
              refine mul_le_mul (mul_le_mul hXC (hcX' s)
                (norm_nonneg _) ?_) (hcY' s)
                (norm_nonneg _) ?_
              · positivity
              · positivity
          _ = 4 * (s * β ^ 3) := by ring
      have h₂ : ‖C * (exp (s • (-Y)) - Γ s)‖
          ≤ 6 * (s * β ^ 3) := by
        calc ‖C * (exp (s • (-Y)) - Γ s)‖
            ≤ ‖C‖ * ‖exp (s • (-Y)) - Γ s‖ := norm_mul_le _ _
          _ ≤ 2 * β ^ 2 * (3 * (s * β)) := by
              refine mul_le_mul hCβ htail (norm_nonneg _) ?_
              positivity
          _ = 6 * (s * β ^ 3) := by ring
      calc ‖(exp (s • X) * C - C * exp (s • X))
            * exp (s • (-X)) * exp (s • (-Y))
          + C * (exp (s • (-Y)) - Γ s)‖
          ≤ ‖(exp (s • X) * C - C * exp (s • X))
              * exp (s • (-X)) * exp (s • (-Y))‖
            + ‖C * (exp (s • (-Y)) - Γ s)‖ := norm_add_le _ _
        _ ≤ 10 * (s * β ^ 3) := by linarith
    -- P₂: ‖e^{sX}e^{sY}·C·e^{-sY} - C·Γ‖ ≤ 10sβ³
    have hP₂ : ‖exp (s • X) * exp (s • Y) * C
        * exp (s • (-Y)) - C * Γ s‖
        ≤ 10 * (s * β ^ 3) := by
      have hEq : exp (s • X) * exp (s • Y) * C
          * exp (s • (-Y)) - C * Γ s
          = (exp (s • X) * (exp (s • Y) * C
                - C * exp (s • Y))
              + (exp (s • X) * C - C * exp (s • X))
                * exp (s • Y)) * exp (s • (-Y))
            + C * (exp (s • X) * exp (s • Y)
                * exp (s • (-Y)) - Γ s) := by
        simp only [hΓdef]
        noncomm_ring
      rw [hEq]
      have h₁ : ‖(exp (s • X) * (exp (s • Y) * C
            - C * exp (s • Y))
          + (exp (s • X) * C - C * exp (s • X))
            * exp (s • Y)) * exp (s • (-Y))‖
          ≤ 8 * (s * β ^ 3) := by
        have ha : ‖exp (s • X) * (exp (s • Y) * C
            - C * exp (s • Y))‖ ≤ 4 * (s * β ^ 3) := by
          calc ‖exp (s • X) * (exp (s • Y) * C
                - C * exp (s • Y))‖
              ≤ ‖exp (s • X)‖ * ‖exp (s • Y) * C
                  - C * exp (s • Y)‖ := norm_mul_le _ _
            _ ≤ 1 * (4 * (s * β ^ 3)) := by
                refine mul_le_mul (hcX s) hYC
                  (norm_nonneg _) zero_le_one
            _ = 4 * (s * β ^ 3) := one_mul _
        have hb : ‖(exp (s • X) * C - C * exp (s • X))
            * exp (s • Y)‖ ≤ 4 * (s * β ^ 3) := by
          calc ‖(exp (s • X) * C - C * exp (s • X))
                * exp (s • Y)‖
              ≤ ‖exp (s • X) * C - C * exp (s • X)‖
                * ‖exp (s • Y)‖ := norm_mul_le _ _
            _ ≤ 4 * (s * β ^ 3) * 1 := by
                refine mul_le_mul hXC (hcY s)
                  (norm_nonneg _) ?_
                positivity
            _ = 4 * (s * β ^ 3) := mul_one _
        calc ‖(exp (s • X) * (exp (s • Y) * C
              - C * exp (s • Y))
            + (exp (s • X) * C - C * exp (s • X))
              * exp (s • Y)) * exp (s • (-Y))‖
            ≤ ‖exp (s • X) * (exp (s • Y) * C
                - C * exp (s • Y))
              + (exp (s • X) * C - C * exp (s • X))
                * exp (s • Y)‖ * ‖exp (s • (-Y))‖ :=
              norm_mul_le _ _
          _ ≤ (4 * (s * β ^ 3) + 4 * (s * β ^ 3)) * 1 := by
              refine mul_le_mul ?_ (hcY' s) (norm_nonneg _) ?_
              · refine (norm_add_le _ _).trans ?_
                linarith
              · positivity
          _ = 8 * (s * β ^ 3) := by ring
      have h₂ : ‖C * (exp (s • X) * exp (s • Y)
          * exp (s • (-Y)) - Γ s)‖ ≤ 2 * (s * β ^ 3) := by
        have hmid : ‖exp (s • X) * exp (s • Y)
            * exp (s • (-Y)) - Γ s‖ ≤ s * β := by
          have hid : exp (s • X) * exp (s • Y)
              * exp (s • (-Y)) - Γ s
              = exp (s • X) * exp (s • Y)
                * (1 - exp (s • (-X))) * exp (s • (-Y)) := by
            simp only [hΓdef]
            noncomm_ring
          rw [hid]
          have hone : ‖(1 : A) - exp (s • (-X))‖ ≤ s * β := by
            rw [← norm_neg]
            have h : -((1 : A) - exp (s • (-X)))
                = exp (s • (-X)) - 1 := by abel
            rw [h]
            exact hEX'1
          calc ‖exp (s • X) * exp (s • Y)
                * (1 - exp (s • (-X))) * exp (s • (-Y))‖
              ≤ ‖exp (s • X) * exp (s • Y)
                  * (1 - exp (s • (-X)))‖
                * ‖exp (s • (-Y))‖ := norm_mul_le _ _
            _ ≤ ‖exp (s • X) * exp (s • Y)‖
                * ‖(1 : A) - exp (s • (-X))‖
                * ‖exp (s • (-Y))‖ :=
                mul_le_mul_of_nonneg_right (norm_mul_le _ _)
                  (norm_nonneg _)
            _ ≤ 1 * (s * β) * 1 := by
                have hxy : ‖exp (s • X) * exp (s • Y)‖
                    ≤ 1 := by
                  calc ‖exp (s • X) * exp (s • Y)‖
                      ≤ ‖exp (s • X)‖ * ‖exp (s • Y)‖ :=
                        norm_mul_le _ _
                    _ ≤ 1 := by
                        have := hcX s
                        have := hcY s
                        have := norm_nonneg (exp (s • X))
                        have := norm_nonneg (exp (s • Y))
                        nlinarith
                refine mul_le_mul (mul_le_mul hxy hone
                  (norm_nonneg _) zero_le_one) (hcY' s)
                  (norm_nonneg _) ?_
                positivity
            _ = s * β := by ring
        calc ‖C * (exp (s • X) * exp (s • Y)
            * exp (s • (-Y)) - Γ s)‖
            ≤ ‖C‖ * ‖exp (s • X) * exp (s • Y)
                * exp (s • (-Y)) - Γ s‖ := norm_mul_le _ _
          _ ≤ 2 * β ^ 2 * (s * β) := by
              refine mul_le_mul hCβ hmid (norm_nonneg _) ?_
              positivity
          _ = 2 * (s * β ^ 3) := by ring
      calc ‖(exp (s • X) * (exp (s • Y) * C
            - C * exp (s • Y))
          + (exp (s • X) * C - C * exp (s • X))
            * exp (s • Y)) * exp (s • (-Y))
          + C * (exp (s • X) * exp (s • Y)
              * exp (s • (-Y)) - Γ s)‖
          ≤ ‖(exp (s • X) * (exp (s • Y) * C
              - C * exp (s • Y))
            + (exp (s • X) * C - C * exp (s • X))
              * exp (s • Y)) * exp (s • (-Y))‖
            + ‖C * (exp (s • X) * exp (s • Y)
                * exp (s • (-Y)) - Γ s)‖ := norm_add_le _ _
        _ ≤ 10 * (s * β ^ 3) := by linarith
    -- remainder wrappers
    have hWY : ‖exp (s • X) * RY * exp (s • (-X))
        * exp (s • (-Y))‖ ≤ 4 * (s ^ 2 * β ^ 3) := by
      have hRYb : ‖RY‖ ≤ 4 * (s ^ 2 * β ^ 3) := by
        have hprod : ‖Y‖ * ‖C‖ ≤ β * (2 * β ^ 2) :=
          mul_le_mul hYβ hCβ (norm_nonneg C) hβ
        calc ‖RY‖ ≤ 2 * s ^ 2 * ‖Y‖ * ‖C‖ := hRY
          _ = 2 * s ^ 2 * (‖Y‖ * ‖C‖) := by ring
          _ ≤ 2 * s ^ 2 * (β * (2 * β ^ 2)) := by
              refine mul_le_mul_of_nonneg_left hprod ?_
              positivity
          _ = 4 * (s ^ 2 * β ^ 3) := by ring
      calc ‖exp (s • X) * RY * exp (s • (-X))
            * exp (s • (-Y))‖
          ≤ ‖exp (s • X) * RY * exp (s • (-X))‖
            * ‖exp (s • (-Y))‖ := norm_mul_le _ _
        _ ≤ ‖exp (s • X) * RY‖ * ‖exp (s • (-X))‖
            * ‖exp (s • (-Y))‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _)
              (norm_nonneg _)
        _ ≤ ‖exp (s • X)‖ * ‖RY‖ * ‖exp (s • (-X))‖
            * ‖exp (s • (-Y))‖ := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
                (norm_nonneg _)) (norm_nonneg _)
        _ ≤ 1 * (4 * (s ^ 2 * β ^ 3)) * 1 * 1 := by
            refine mul_le_mul (mul_le_mul (mul_le_mul (hcX s)
              hRYb (norm_nonneg _) zero_le_one) (hcX' s)
              (norm_nonneg _) ?_) (hcY' s) (norm_nonneg _) ?_
            · positivity
            · positivity
        _ = 4 * (s ^ 2 * β ^ 3) := by ring
    have hWX : ‖exp (s • X) * exp (s • Y) * RX
        * exp (s • (-Y))‖ ≤ 4 * (s ^ 2 * β ^ 3) := by
      have hRXb : ‖RX‖ ≤ 4 * (s ^ 2 * β ^ 3) := by
        have hprod : ‖X‖ * ‖C‖ ≤ β * (2 * β ^ 2) :=
          mul_le_mul hXβ hCβ (norm_nonneg C) hβ
        calc ‖RX‖ ≤ 2 * s ^ 2 * ‖X‖ * ‖C‖ := hRX
          _ = 2 * s ^ 2 * (‖X‖ * ‖C‖) := by ring
          _ ≤ 2 * s ^ 2 * (β * (2 * β ^ 2)) := by
              refine mul_le_mul_of_nonneg_left hprod ?_
              positivity
          _ = 4 * (s ^ 2 * β ^ 3) := by ring
      calc ‖exp (s • X) * exp (s • Y) * RX
            * exp (s • (-Y))‖
          ≤ ‖exp (s • X) * exp (s • Y) * RX‖
            * ‖exp (s • (-Y))‖ := norm_mul_le _ _
        _ ≤ ‖exp (s • X) * exp (s • Y)‖ * ‖RX‖
            * ‖exp (s • (-Y))‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _)
              (norm_nonneg _)
        _ ≤ 1 * (4 * (s ^ 2 * β ^ 3)) * 1 := by
            have hxy : ‖exp (s • X) * exp (s • Y)‖ ≤ 1 := by
              calc ‖exp (s • X) * exp (s • Y)‖
                  ≤ ‖exp (s • X)‖ * ‖exp (s • Y)‖ :=
                    norm_mul_le _ _
                _ ≤ 1 := by
                    have := hcX s
                    have := hcY s
                    have := norm_nonneg (exp (s • X))
                    have := norm_nonneg (exp (s • Y))
                    nlinarith
            refine mul_le_mul (mul_le_mul hxy hRXb
              (norm_nonneg _) zero_le_one) (hcY' s)
              (norm_nonneg _) ?_
            positivity
        _ = 4 * (s ^ 2 * β ^ 3) := by ring
    -- assemble the integrand bound
    have hinner : ‖(exp (s • X)
          * (X * exp (s • Y) - exp (s • Y) * X)
          * exp (s • (-X)) * exp (s • (-Y))
        + exp (s • X) * exp (s • Y)
          * (Y * exp (s • (-X)) - exp (s • (-X)) * Y)
          * exp (s • (-Y)))
        - (s + s) • (C * Γ s)‖ ≤ 28 * β ^ 3 := by
      rw [hmaster]
      have hsm₁ : ‖s • (exp (s • X) * C * exp (s • (-X))
          * exp (s • (-Y)) - C * Γ s)‖
          ≤ 10 * (s ^ 2 * β ^ 3) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
        calc s * ‖exp (s • X) * C * exp (s • (-X))
              * exp (s • (-Y)) - C * Γ s‖
            ≤ s * (10 * (s * β ^ 3)) :=
              mul_le_mul_of_nonneg_left hP₁ hs0
          _ = 10 * (s ^ 2 * β ^ 3) := by ring
      have hsm₂ : ‖s • (exp (s • X) * exp (s • Y) * C
          * exp (s • (-Y)) - C * Γ s)‖
          ≤ 10 * (s ^ 2 * β ^ 3) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
        calc s * ‖exp (s • X) * exp (s • Y) * C
              * exp (s • (-Y)) - C * Γ s‖
            ≤ s * (10 * (s * β ^ 3)) :=
              mul_le_mul_of_nonneg_left hP₂ hs0
          _ = 10 * (s ^ 2 * β ^ 3) := by ring
      have htotal : ‖s • (exp (s • X) * C * exp (s • (-X))
            * exp (s • (-Y)) - C * Γ s)
          + s • (exp (s • X) * exp (s • Y) * C
              * exp (s • (-Y)) - C * Γ s)
          - exp (s • X) * RY * exp (s • (-X))
            * exp (s • (-Y))
          - exp (s • X) * exp (s • Y) * RX
            * exp (s • (-Y))‖
          ≤ 28 * (s ^ 2 * β ^ 3) := by
        have t₁ := norm_sub_le
          (s • (exp (s • X) * C * exp (s • (-X))
              * exp (s • (-Y)) - C * Γ s)
            + s • (exp (s • X) * exp (s • Y) * C
                * exp (s • (-Y)) - C * Γ s)
            - exp (s • X) * RY * exp (s • (-X))
              * exp (s • (-Y)))
          (exp (s • X) * exp (s • Y) * RX * exp (s • (-Y)))
        have t₂ := norm_sub_le
          (s • (exp (s • X) * C * exp (s • (-X))
              * exp (s • (-Y)) - C * Γ s)
            + s • (exp (s • X) * exp (s • Y) * C
                * exp (s • (-Y)) - C * Γ s))
          (exp (s • X) * RY * exp (s • (-X))
            * exp (s • (-Y)))
        have t₃ := norm_add_le
          (s • (exp (s • X) * C * exp (s • (-X))
              * exp (s • (-Y)) - C * Γ s))
          (s • (exp (s • X) * exp (s • Y) * C
              * exp (s • (-Y)) - C * Γ s))
        linarith
      have hs2 : s ^ 2 * β ^ 3 ≤ β ^ 3 := by
        have hb3 : (0 : ℝ) ≤ β ^ 3 := by positivity
        have hsq : s ^ 2 ≤ 1 := by nlinarith
        have := mul_le_mul_of_nonneg_right hsq hb3
        linarith
      linarith
    calc ‖exp ((1 - s * s) • C)
          * ((exp (s • X)
              * (X * exp (s • Y) - exp (s • Y) * X)
              * exp (s • (-X)) * exp (s • (-Y))
            + exp (s • X) * exp (s • Y)
              * (Y * exp (s • (-X)) - exp (s • (-X)) * Y)
              * exp (s • (-Y)))
            - (s + s) • (C * Γ s))‖
        ≤ ‖exp ((1 - s * s) • C)‖
          * ‖(exp (s • X)
              * (X * exp (s • Y) - exp (s • Y) * X)
              * exp (s • (-X)) * exp (s • (-Y))
            + exp (s • X) * exp (s • Y)
              * (Y * exp (s • (-X)) - exp (s • (-X)) * Y)
              * exp (s • (-Y)))
            - (s + s) • (C * Γ s)‖ := norm_mul_le _ _
      _ ≤ 1 * (28 * β ^ 3) := by
          refine mul_le_mul hEC hinner (norm_nonneg _)
            zero_le_one
      _ = 28 * β ^ 3 := one_mul _
  calc ‖∫ s in (0 : ℝ)..1,
        exp ((1 - s * s) • C)
          * ((exp (s • X)
              * (X * exp (s • Y) - exp (s • Y) * X)
              * exp (s • (-X)) * exp (s • (-Y))
            + exp (s • X) * exp (s • Y)
              * (Y * exp (s • (-X)) - exp (s • (-X)) * Y)
              * exp (s • (-Y)))
            - (s + s) • (C * Γ s))‖
      ≤ 28 * β ^ 3 * |1 - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          hbound
    _ = 28 * β ^ 3 := by
        norm_num

end SharpTrotter
end NCG
