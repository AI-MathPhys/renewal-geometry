/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Norm-convergent boundary-cycle channel and return pencil
  (`thm:marked-cycle-channel`, Gran-Tensor manuscript)

* `marked_cycle_channel`: under the boxed exponential
  survivor decay `‖F_n‖ ≤ C·e^{-αn}`:
  (i) the boxed partial first-return sums converge in norm
      (`Summable F`);
  (ii) the boxed marked cycle pencil `Σ zⁿ·F_n` is
      norm-convergent for every `‖z‖ < e^α` (norm
      analyticity on the disc of radius `e^α`);
  (iii) the stationary boundary state: every trace-preserving
      endomorphism of a nonempty finite matrix algebra has a
      nonzero fixed point.

The CPTP/GNS-contraction reading of the fixed point and the
moment-derivative clause are the manuscript's positivity
bookkeeping over these convergence statements.
-/

open Matrix

namespace NCG

/-- `thm:marked-cycle-channel`. -/
theorem marked_cycle_channel {V : Type*}
    [NormedAddCommGroup V] [CompleteSpace V]
    (F : ℕ → V) (Cb α : ℝ)
    (hα : 0 < α)
    (hdecay : ∀ n, ‖F n‖ ≤ Cb * Real.exp (-α * n)) :
    -- (i) the first-return sums converge in norm
    Summable F
    -- (ii) the return pencil is norm-analytic on ‖z‖ < e^α
    ∧ (∀ z : ℂ, ‖z‖ < Real.exp α →
        Summable fun n : ℕ => ‖z‖ ^ n * ‖F n‖)
    -- (iii) trace-preserving cycle maps have a stationary
    --       direction
    ∧ (∀ {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
        (Φ : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ),
        (∀ X, (Φ X).trace = X.trace) →
        ∃ ρ : Matrix d d ℂ, ρ ≠ 0 ∧ Φ ρ = ρ) := by
  have hgeom : ∀ n : ℕ, Cb * Real.exp (-α * n)
      = Cb * (Real.exp (-α)) ^ n := by
    intro n
    rw [← Real.exp_nat_mul]
    ring_nf
  have hr : Real.exp (-α) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have hg : Summable
        (fun n : ℕ => Cb * Real.exp (-α * n)) := by
      rw [show (fun n : ℕ => Cb * Real.exp (-α * n))
          = fun n : ℕ => Cb * (Real.exp (-α)) ^ n from
        funext hgeom]
      exact (summable_geometric_of_lt_one
        (Real.exp_nonneg _) hr).mul_left Cb
    exact Summable.of_norm_bounded hg hdecay
  · intro z hz
    have hb : ∀ n : ℕ, ‖z‖ ^ n * ‖F n‖
        ≤ Cb * (‖z‖ * Real.exp (-α)) ^ n := by
      intro n
      calc ‖z‖ ^ n * ‖F n‖
          ≤ ‖z‖ ^ n * (Cb * Real.exp (-α * n)) := by
            apply mul_le_mul_of_nonneg_left (hdecay n)
              (by positivity)
        _ = Cb * (‖z‖ * Real.exp (-α)) ^ n := by
            rw [hgeom n, mul_pow]
            ring
    have hs : Summable fun n : ℕ =>
        Cb * (‖z‖ * Real.exp (-α)) ^ n := by
      apply Summable.mul_left
      apply summable_geometric_of_lt_one (by positivity)
      have h1 : ‖z‖ * Real.exp (-α)
          < Real.exp α * Real.exp (-α) := by
        apply mul_lt_mul_of_pos_right hz
          (Real.exp_pos _)
      rwa [← Real.exp_add, add_neg_cancel,
        Real.exp_zero] at h1
    exact Summable.of_nonneg_of_le
      (fun n => by positivity) hb hs
  · intro d _ _ _ Φ htr
    by_contra hno
    push Not at hno
    set L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ
      := Φ - LinearMap.id with hL
    have hinj : Function.Injective L := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro ρ hρ
      rw [LinearMap.mem_ker, hL, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hρ
      by_contra hρ0
      exact hno ρ hρ0 hρ
    have hsurj := LinearMap.surjective_of_injective hinj
    obtain ⟨Y, hY⟩ := hsurj 1
    have htr0 : (L Y).trace = 0 := by
      rw [hL, LinearMap.sub_apply, LinearMap.id_apply,
        Matrix.trace_sub, htr, sub_self]
    rw [hY, Matrix.trace_one] at htr0
    have hcard : (Fintype.card d : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact hcard htr0

end NCG
