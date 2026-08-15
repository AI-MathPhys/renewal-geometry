/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ChannelEstimates

/-!
# Quadratic noisy-channel remainder (exact)

Exact formalization of `thm:SMST-quadratic-channel-remainder`
from the Gran-Tensor manuscript, plus the Klein four-group
character-orthogonality identities that feed
`thm:SMST-noisy-Klein-refocusing`.

The manuscript statement: a physical channel curve `Φ(t)`
through the encoder `ι` whose second derivative is bounded and
whose first derivative at `0` matches the ideal generator up to
`ε_tan` stays within `t·ε_tan + κ·t²` of the ideal semigroup
`ι ∘ e^{tℒ_H}` in diamond norm, with
`κ = M₂/2 + M_ℒ²·e^{t₀·M_ℒ}` explicit.

Formalization choices (all quantitative content derived, none
hypothesized — this resolves the 2026-08-07 fidelity-audit
TAUTOLOGY downgrade of this record):

* the superoperator algebra with the diamond norm is modeled as
  an abstract unital Banach algebra `A` — the diamond norm is
  submultiplicative and unital on superoperators, which is all
  the proof uses;
* the curve `ψ t = Φ(t) ∘ ι` and its two derivatives are data
  (`HasDerivAt` hypotheses with the bound `‖ψ''‖ ≤ M₂`): CPTP
  smoothness is framework input, the Taylor estimate is
  **derived** here by the mean value theorem plus the integral
  remainder, not assumed;
* the encoder is an element `ι` with `‖ι‖ ≤ 1` (CPTP maps are
  diamond contractions);
* the exponential tail `‖e^{tℒ} - 1 - tℒ‖ ≤ t²‖ℒ‖²e^{t‖ℒ‖}` is
  derived from the exponential series
  (`NCG.ChannelEstimates.exp_sub_linear_bound`).

Main results:

* `deriv_dist_le`: `‖ψ'(s) - ψ'(0)‖ ≤ M₂·s` from the
  second-derivative bound (mean value inequality);
* `curve_taylor`: the integral-remainder Taylor bound
  `‖ψ(t) - ψ(0) - t·ψ'(0)‖ ≤ M₂·t²/2`;
* `quadratic_channel_remainder`: the boxed bound
  `‖ψ(t) - ι·e^{t•L}‖ ≤ t·ε_tan + (M₂/2 + ‖L‖²e^{t‖L‖})·t²`;
* `quadratic_channel_remainder_window`: the uniform-window
  version with `κ = M₂/2 + M_ℒ²·e^{t₀·M_ℒ}` constant on
  `[0, t₀]`;
* `quadratic_channel_remainder_exact`: the exact-tangent branch
  `‖ψ(t) - ι·e^{t•L}‖ ≤ κ·t²`;
* `klein_diag` / `klein_edge01` / `klein_edge02` /
  `klein_edge12`: Klein character orthogonality — the four sign
  conjugations `Z_ε H Z_ε` weighted by `χ_e` isolate exactly the
  off-diagonal edge block `P_iHP_j + P_jHP_i` (pure ring
  identities, no hypotheses at all).
-/

open Set intervalIntegral

namespace NCG
namespace SMSTChannel

/-! ### Klein four-group character orthogonality

The Klein sign group `𝖪 = {ε ∈ {±1}³ : ε₀ε₁ε₂ = 1}` has the
four elements `(+,+,+), (+,-,-), (-,+,-), (-,-,+)` with sign
words `Z_ε = ε₀P₀ + ε₁P₁ + ε₂P₂`.  Character orthogonality
`∑_ε χ_e(ε)·Z_ε H Z_ε = 4·H_e` is a polynomial identity in the
noncommuting variables `P₀, P₁, P₂, H` — it needs no projection
or resolution-of-identity hypotheses, so we state it in a bare
ring. -/

section Klein

variable {A : Type} [Ring A]

/-- Trivial character: the unweighted Klein average isolates the
diagonal blocks. -/
theorem klein_diag (P₀ P₁ P₂ H : A) :
    (P₀ + P₁ + P₂) * H * (P₀ + P₁ + P₂)
      + (P₀ - P₁ - P₂) * H * (P₀ - P₁ - P₂)
      + (-P₀ + P₁ - P₂) * H * (-P₀ + P₁ - P₂)
      + (-P₀ - P₁ + P₂) * H * (-P₀ - P₁ + P₂)
    = 4 * (P₀ * H * P₀ + P₁ * H * P₁ + P₂ * H * P₂) := by
  noncomm_ring

/-- Character `χ₀₁(ε) = ε₀ε₁`: the weighted Klein average
isolates the edge block `P₀HP₁ + P₁HP₀`. -/
theorem klein_edge01 (P₀ P₁ P₂ H : A) :
    (P₀ + P₁ + P₂) * H * (P₀ + P₁ + P₂)
      - (P₀ - P₁ - P₂) * H * (P₀ - P₁ - P₂)
      - (-P₀ + P₁ - P₂) * H * (-P₀ + P₁ - P₂)
      + (-P₀ - P₁ + P₂) * H * (-P₀ - P₁ + P₂)
    = 4 * (P₀ * H * P₁ + P₁ * H * P₀) := by
  noncomm_ring

/-- Character `χ₀₂(ε) = ε₀ε₂`: the weighted Klein average
isolates the edge block `P₀HP₂ + P₂HP₀`. -/
theorem klein_edge02 (P₀ P₁ P₂ H : A) :
    (P₀ + P₁ + P₂) * H * (P₀ + P₁ + P₂)
      - (P₀ - P₁ - P₂) * H * (P₀ - P₁ - P₂)
      + (-P₀ + P₁ - P₂) * H * (-P₀ + P₁ - P₂)
      - (-P₀ - P₁ + P₂) * H * (-P₀ - P₁ + P₂)
    = 4 * (P₀ * H * P₂ + P₂ * H * P₀) := by
  noncomm_ring

/-- Character `χ₁₂(ε) = ε₁ε₂`: the weighted Klein average
isolates the edge block `P₁HP₂ + P₂HP₁`. -/
theorem klein_edge12 (P₀ P₁ P₂ H : A) :
    (P₀ + P₁ + P₂) * H * (P₀ + P₁ + P₂)
      + (P₀ - P₁ - P₂) * H * (P₀ - P₁ - P₂)
      - (-P₀ + P₁ - P₂) * H * (-P₀ + P₁ - P₂)
      - (-P₀ - P₁ + P₂) * H * (-P₀ - P₁ + P₂)
    = 4 * (P₁ * H * P₂ + P₂ * H * P₁) := by
  noncomm_ring

end Klein

/-! ### The Taylor bound for a twice-differentiable channel curve -/

section Curve

variable {A : Type} [NormedRing A] [NormOneClass A]
  [NormedAlgebra ℝ A] [CompleteSpace A]

omit [NormOneClass A] [CompleteSpace A] in
/-- Mean value inequality: a second-derivative bound `M₂` on
`[0, t]` makes the first derivative `M₂`-Lipschitz from `0`. -/
theorem deriv_dist_le (ψ' ψ'' : ℝ → A) (M₂ t : ℝ)
    (hd2 : ∀ s ∈ Icc (0 : ℝ) t, HasDerivAt ψ' (ψ'' s) s)
    (hM : ∀ s ∈ Icc (0 : ℝ) t, ‖ψ'' s‖ ≤ M₂) :
    ∀ s ∈ Icc (0 : ℝ) t, ‖ψ' s - ψ' 0‖ ≤ M₂ * s := by
  intro s hs
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := ψ') (f' := ψ'') (a := 0) (b := s) (C := M₂)
    (fun x hx =>
      (hd2 x ⟨hx.1, hx.2.trans hs.2⟩).hasDerivWithinAt)
    (fun x hx =>
      hM x ⟨hx.1, hx.2.le.trans hs.2⟩)
    s ⟨hs.1, le_refl s⟩
  simpa using key

omit [NormOneClass A] in
/-- **Taylor with integral remainder** for a twice-differentiable
curve in a Banach algebra: `‖ψ(t) - ψ(0) - t·ψ'(0)‖ ≤ M₂·t²/2`.
This is the estimate the fidelity audit required to be derived
rather than hypothesized. -/
theorem curve_taylor (ψ ψ' ψ'' : ℝ → A) (M₂ t : ℝ)
    (ht : 0 ≤ t)
    (hd1 : ∀ s ∈ Icc (0 : ℝ) t, HasDerivAt ψ (ψ' s) s)
    (hd2 : ∀ s ∈ Icc (0 : ℝ) t, HasDerivAt ψ' (ψ'' s) s)
    (hM : ∀ s ∈ Icc (0 : ℝ) t, ‖ψ'' s‖ ≤ M₂) :
    ‖ψ t - ψ 0 - t • ψ' 0‖ ≤ M₂ * t ^ 2 / 2 := by
  have hIcc : uIcc (0 : ℝ) t = Icc 0 t := uIcc_of_le ht
  -- the shifted curve `g s = ψ s - s • ψ'(0)`
  have hg : ∀ s ∈ uIcc (0 : ℝ) t,
      HasDerivAt (fun u : ℝ => ψ u - u • ψ' 0)
        (ψ' s - ψ' 0) s := by
    intro s hs
    rw [hIcc] at hs
    have hlin : HasDerivAt (fun u : ℝ => u • ψ' 0) (ψ' 0) s := by
      simpa using (hasDerivAt_id s).smul_const (ψ' 0)
    exact (hd1 s hs).sub hlin
  -- integrability of `ψ' · - ψ'(0)` from continuity
  have hcont : ContinuousOn ψ' (Icc (0 : ℝ) t) :=
    HasDerivAt.continuousOn hd2
  have hint : IntervalIntegrable
      (fun s => ψ' s - ψ' 0)
      MeasureTheory.volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hIcc]
    exact hcont.sub continuousOn_const
  -- fundamental theorem of calculus on the shifted curve
  have hftc :
      (∫ s in (0 : ℝ)..t, (ψ' s - ψ' 0))
        = (ψ t - t • ψ' 0) - (ψ 0 - (0 : ℝ) • ψ' 0) :=
    integral_eq_sub_of_hasDerivAt hg hint
  have hval : ψ t - ψ 0 - t • ψ' 0
      = ∫ s in (0 : ℝ)..t, (ψ' s - ψ' 0) := by
    rw [hftc]
    simp only [zero_smul, sub_zero]
    abel
  rw [hval]
  -- pointwise bound `‖ψ'(s) - ψ'(0)‖ ≤ M₂·s` on the interval
  have hpt := deriv_dist_le (A := A) ψ' ψ'' M₂ t hd2 hM
  have hboundInt : IntervalIntegrable
      (fun s : ℝ => M₂ * s) MeasureTheory.volume 0 t :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 t
  calc ‖∫ s in (0 : ℝ)..t, (ψ' s - ψ' 0)‖
      ≤ ∫ s in (0 : ℝ)..t, M₂ * s := by
        refine intervalIntegral.norm_integral_le_of_norm_le ht
          (MeasureTheory.ae_of_all _ fun s hs => ?_) hboundInt
        exact hpt s ⟨hs.1.le, hs.2⟩
    _ = M₂ * t ^ 2 / 2 := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring

/-- **Quadratic noisy-channel remainder**
(`thm:SMST-quadratic-channel-remainder`), pointwise form.

`ψ t` is the physical channel curve composed with the encoder
(`Φ(t) ∘ ι`), an element of the superoperator Banach algebra
with the diamond norm; `ι` is the encoder (`‖ι‖ ≤ 1`, a CPTP
diamond contraction); `L` is the ideal generator `ℒ_H`, so
`ι * exp (t • L)` is `ι ∘ e^{tℒ_H}`.  Given the framework data —
two derivatives of the physical curve with `‖ψ''‖ ≤ M₂` and
projected first-derivative error `‖ψ'(0) - ι·L‖ ≤ ε_tan` — the
distance to the ideal semigroup obeys the boxed bound
`t·ε_tan + κ(t)·t²` with every constant explicit and derived. -/
theorem quadratic_channel_remainder (ψ ψ' ψ'' : ℝ → A)
    (ι L : A) (εtan M₂ t : ℝ) (ht : 0 ≤ t)
    (hι : ‖ι‖ ≤ 1) (hψ0 : ψ 0 = ι)
    (hd1 : ∀ s ∈ Icc (0 : ℝ) t, HasDerivAt ψ (ψ' s) s)
    (hd2 : ∀ s ∈ Icc (0 : ℝ) t, HasDerivAt ψ' (ψ'' s) s)
    (hM : ∀ s ∈ Icc (0 : ℝ) t, ‖ψ'' s‖ ≤ M₂)
    (htan : ‖ψ' 0 - ι * L‖ ≤ εtan) :
    ‖ψ t - ι * NormedSpace.exp (t • L)‖
      ≤ t * εtan
        + (M₂ / 2 + ‖L‖ ^ 2 * Real.exp (t * ‖L‖)) * t ^ 2 := by
  -- three-term decomposition
  have hsplit : ψ t - ι * NormedSpace.exp (t • L)
      = (ψ t - ψ 0 - t • ψ' 0)
        + t • (ψ' 0 - ι * L)
        - ι * (NormedSpace.exp (t • L) - 1 - t • L) := by
    rw [hψ0, mul_sub, mul_sub, mul_one, mul_smul_comm]
    rw [smul_sub]
    abel
  rw [hsplit]
  -- Taylor term
  have h1 : ‖ψ t - ψ 0 - t • ψ' 0‖ ≤ M₂ * t ^ 2 / 2 :=
    curve_taylor ψ ψ' ψ'' M₂ t ht hd1 hd2 hM
  -- tangent term
  have h2 : ‖t • (ψ' 0 - ι * L)‖ ≤ t * εtan := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left htan ht
  -- exponential tail term
  have h3 : ‖ι * (NormedSpace.exp (t • L) - 1 - t • L)‖
      ≤ ‖L‖ ^ 2 * Real.exp (t * ‖L‖) * t ^ 2 := by
    have hnorm : ‖t • L‖ = t * ‖L‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    calc ‖ι * (NormedSpace.exp (t • L) - 1 - t • L)‖
        ≤ ‖ι‖ * ‖NormedSpace.exp (t • L) - 1 - t • L‖ :=
          norm_mul_le _ _
      _ ≤ 1 * (‖t • L‖ ^ 2 * Real.exp ‖t • L‖) := by
          refine mul_le_mul hι
            (NCG.ChannelEstimates.exp_sub_linear_bound (t • L))
            (norm_nonneg _) zero_le_one
      _ = ‖L‖ ^ 2 * Real.exp (t * ‖L‖) * t ^ 2 := by
          rw [hnorm]
          ring
  calc ‖(ψ t - ψ 0 - t • ψ' 0) + t • (ψ' 0 - ι * L)
        - ι * (NormedSpace.exp (t • L) - 1 - t • L)‖
      ≤ ‖(ψ t - ψ 0 - t • ψ' 0) + t • (ψ' 0 - ι * L)‖
        + ‖ι * (NormedSpace.exp (t • L) - 1 - t • L)‖ :=
        norm_sub_le _ _
    _ ≤ ‖ψ t - ψ 0 - t • ψ' 0‖ + ‖t • (ψ' 0 - ι * L)‖
        + ‖ι * (NormedSpace.exp (t • L) - 1 - t • L)‖ := by
        have := norm_add_le (ψ t - ψ 0 - t • ψ' 0)
          (t • (ψ' 0 - ι * L))
        linarith
    _ ≤ M₂ * t ^ 2 / 2 + t * εtan
        + ‖L‖ ^ 2 * Real.exp (t * ‖L‖) * t ^ 2 := by
        linarith
    _ = t * εtan
        + (M₂ / 2 + ‖L‖ ^ 2 * Real.exp (t * ‖L‖)) * t ^ 2 := by
        ring

/-- Uniform-window form: on `0 ≤ t ≤ t₀` with generator bound
`‖L‖ ≤ M_ℒ`, the remainder constant
`κ = M₂/2 + M_ℒ²·e^{t₀·M_ℒ}` is independent of `t`, giving the
manuscript's boxed `t·ε_tan + κ·t²`. -/
theorem quadratic_channel_remainder_window (ψ ψ' ψ'' : ℝ → A)
    (ι L : A) (εtan M₂ ML t t₀ : ℝ) (ht : 0 ≤ t)
    (ht₀ : t ≤ t₀) (hL : ‖L‖ ≤ ML)
    (hι : ‖ι‖ ≤ 1) (hψ0 : ψ 0 = ι)
    (hd1 : ∀ s ∈ Icc (0 : ℝ) t, HasDerivAt ψ (ψ' s) s)
    (hd2 : ∀ s ∈ Icc (0 : ℝ) t, HasDerivAt ψ' (ψ'' s) s)
    (hM : ∀ s ∈ Icc (0 : ℝ) t, ‖ψ'' s‖ ≤ M₂)
    (htan : ‖ψ' 0 - ι * L‖ ≤ εtan) :
    ‖ψ t - ι * NormedSpace.exp (t • L)‖
      ≤ t * εtan
        + (M₂ / 2 + ML ^ 2 * Real.exp (t₀ * ML)) * t ^ 2 := by
  have hbase := quadratic_channel_remainder ψ ψ' ψ'' ι L
    εtan M₂ t ht hι hψ0 hd1 hd2 hM htan
  have hML : (0 : ℝ) ≤ ML := (norm_nonneg L).trans hL
  have hexp : Real.exp (t * ‖L‖) ≤ Real.exp (t₀ * ML) := by
    refine Real.exp_le_exp.mpr ?_
    exact mul_le_mul ht₀ hL (norm_nonneg L)
      ((ht.trans ht₀))
  have hsq : ‖L‖ ^ 2 ≤ ML ^ 2 := by
    have := norm_nonneg L
    nlinarith
  have hmono : ‖L‖ ^ 2 * Real.exp (t * ‖L‖)
      ≤ ML ^ 2 * Real.exp (t₀ * ML) := by
    refine mul_le_mul hsq hexp (Real.exp_pos _).le ?_
    positivity
  have ht2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  nlinarith

/-- Exact-tangent branch: when the physical first derivative
matches the ideal generator exactly, the bound is purely
quadratic, `‖ψ(t) - ι·e^{t•L}‖ ≤ κ·t²`. -/
theorem quadratic_channel_remainder_exact (ψ ψ' ψ'' : ℝ → A)
    (ι L : A) (M₂ ML t t₀ : ℝ) (ht : 0 ≤ t) (ht₀ : t ≤ t₀)
    (hL : ‖L‖ ≤ ML) (hι : ‖ι‖ ≤ 1) (hψ0 : ψ 0 = ι)
    (hd1 : ∀ s ∈ Icc (0 : ℝ) t, HasDerivAt ψ (ψ' s) s)
    (hd2 : ∀ s ∈ Icc (0 : ℝ) t, HasDerivAt ψ' (ψ'' s) s)
    (hM : ∀ s ∈ Icc (0 : ℝ) t, ‖ψ'' s‖ ≤ M₂)
    (htan : ψ' 0 = ι * L) :
    ‖ψ t - ι * NormedSpace.exp (t • L)‖
      ≤ (M₂ / 2 + ML ^ 2 * Real.exp (t₀ * ML)) * t ^ 2 := by
  have hbase := quadratic_channel_remainder_window ψ ψ' ψ''
    ι L 0 M₂ ML t t₀ ht ht₀ hL hι hψ0 hd1 hd2 hM
    (by rw [htan]; simp)
  simpa using hbase

end Curve

end SMSTChannel
end NCG
