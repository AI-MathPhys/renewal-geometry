/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Bounded perturbations by Dyson expansion

A reusable Dyson-series proof of the quasi-contractive bounded-perturbation
estimate. This is the analytic engine behind the manuscript's bounded
conjugation-defect certificate.
-/

open Filter MeasureTheory Set
open scoped Interval

noncomputable section

namespace NCG
namespace BoundedPerturbationDyson

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Recursive time-ordered Dyson term. -/
def dysonTerm (P : ℝ → A) (K : A) : ℕ → ℝ → A
  | 0, t => P t
  | n + 1, t => ∫ s in (0 : ℝ)..t, P (t - s) * K * dysonTerm P K n s

/-- The nth Dyson term has its exact factorial majorant. -/
theorem norm_dysonTerm_le
    (P : ℝ → A) (K : A) (v κ : ℝ)
    (hκ : 0 ≤ κ) (hK : ‖K‖ ≤ κ)
    (hP : ∀ t, 0 ≤ t → ‖P t‖ ≤ Real.exp (v * t)) :
    ∀ n t, 0 ≤ t →
      ‖dysonTerm P K n t‖
        ≤ Real.exp (v * t) * (κ * t) ^ n / (n.factorial : ℝ) := by
  intro n
  induction n with
  | zero =>
      intro t ht
      simpa [dysonTerm] using hP t ht
  | succ n ih =>
      intro t ht
      rw [dysonTerm]
      let C : ℝ :=
        Real.exp (v * t) * κ ^ (n + 1) / (n.factorial : ℝ)
      have hC : 0 ≤ C := by
        dsimp [C]
        positivity
      have hg : IntervalIntegrable
          (fun s : ℝ => C * s ^ n) volume 0 t := by
        exact (continuous_const.mul (continuous_id.pow n)).intervalIntegrable 0 t
      have h := intervalIntegral.norm_integral_le_of_norm_le ht
        (f := fun s => P (t - s) * K * dysonTerm P K n s)
        (g := fun s : ℝ => C * s ^ n)
        (by
          filter_upwards [] with s
          intro hs
          have hs0 : 0 ≤ s := hs.1.le
          have hst : s ≤ t := hs.2
          calc
            ‖P (t - s) * K * dysonTerm P K n s‖
                ≤ ‖P (t - s)‖ * ‖K‖ * ‖dysonTerm P K n s‖ := by
              exact (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
                  (norm_nonneg _))
            _ ≤ Real.exp (v * (t - s)) * κ *
                  (Real.exp (v * s) * (κ * s) ^ n /
                    (n.factorial : ℝ)) := by
              calc
                ‖P (t - s)‖ * ‖K‖ * ‖dysonTerm P K n s‖
                    ≤ Real.exp (v * (t - s)) * ‖K‖ *
                        ‖dysonTerm P K n s‖ := by
                  gcongr
                  exact hP (t - s) (sub_nonneg.mpr hst)
                _ ≤ Real.exp (v * (t - s)) * κ *
                        ‖dysonTerm P K n s‖ := by
                  gcongr
                _ ≤ Real.exp (v * (t - s)) * κ *
                      (Real.exp (v * s) * (κ * s) ^ n /
                        (n.factorial : ℝ)) := by
                  exact mul_le_mul_of_nonneg_left (ih s hs0)
                    (mul_nonneg (Real.exp_pos _).le hκ)
            _ = C * s ^ n := by
              dsimp [C]
              calc
                Real.exp (v * (t - s)) * κ *
                      (Real.exp (v * s) * (κ * s) ^ n /
                        (n.factorial : ℝ))
                    = κ ^ (n + 1) * s ^ n / (n.factorial : ℝ) *
                        (Real.exp (v * (t - s)) * Real.exp (v * s)) := by
                      rw [mul_pow]
                      ring
                _ = κ ^ (n + 1) * s ^ n / (n.factorial : ℝ) *
                      Real.exp (v * (t - s) + v * s) := by
                      rw [Real.exp_add]
                _ = Real.exp (v * t) * κ ^ (n + 1) /
                      (n.factorial : ℝ) * s ^ n := by
                      rw [show v * (t - s) + v * s = v * t by ring]
                      ring)
        hg
      calc
        ‖∫ s in (0 : ℝ)..t, P (t - s) * K * dysonTerm P K n s‖
            ≤ ∫ s in (0 : ℝ)..t, C * s ^ n := h
        _ = C * ((t ^ (n + 1) - 0 ^ (n + 1)) / (n + 1)) := by
          rw [intervalIntegral.integral_const_mul, integral_pow]
        _ = Real.exp (v * t) * (κ * t) ^ (n + 1) /
            ((n + 1).factorial : ℝ) := by
          dsimp [C]
          rw [zero_pow (Nat.succ_ne_zero n), sub_zero, mul_pow,
            Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          field_simp

/-- The Dyson expansion of the boundedly perturbed evolution. -/
def perturbedEvolution (P : ℝ → A) (K : A) (t : ℝ) : A :=
  ∑' n : ℕ, dysonTerm P K n t

theorem summable_dysonTerm
    (P : ℝ → A) (K : A) (v κ t : ℝ)
    (ht : 0 ≤ t) (hκ : 0 ≤ κ) (hK : ‖K‖ ≤ κ)
    (hP : ∀ r, 0 ≤ r → ‖P r‖ ≤ Real.exp (v * r)) :
    Summable fun n : ℕ => dysonTerm P K n t := by
  apply Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial (κ * t)).mul_left
      (Real.exp (v * t)))
  intro n
  simpa [div_eq_mul_inv, mul_assoc] using
    norm_dysonTerm_le P K v κ hκ hK hP n t ht

theorem real_exp_eq_tsum_pow_div_factorial (x : ℝ) :
    Real.exp x = ∑' n : ℕ, x ^ n / (n.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- Bounded perturbation theorem with quasi-contractive constant one. -/
theorem norm_perturbedEvolution_le
    (P : ℝ → A) (K : A) (v κ t : ℝ)
    (ht : 0 ≤ t) (hκ : 0 ≤ κ) (hK : ‖K‖ ≤ κ)
    (hP : ∀ r, 0 ≤ r → ‖P r‖ ≤ Real.exp (v * r)) :
    ‖perturbedEvolution P K t‖ ≤ Real.exp ((v + κ) * t) := by
  let g : ℕ → ℝ := fun n =>
    Real.exp (v * t) * (κ * t) ^ n / (n.factorial : ℝ)
  have hg : Summable g :=
    by
      simpa [g, div_eq_mul_inv, mul_assoc] using
        (Real.summable_pow_div_factorial (κ * t)).mul_left
          (Real.exp (v * t))
  have hnorm : Summable fun n : ℕ => ‖dysonTerm P K n t‖ :=
    hg.of_norm_bounded fun n => by
      simpa only [norm_norm, g] using
        norm_dysonTerm_le P K v κ hκ hK hP n t ht
  calc
    ‖perturbedEvolution P K t‖
        ≤ ∑' n : ℕ, ‖dysonTerm P K n t‖ := by
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, g n := hnorm.tsum_le_tsum
      (fun n => norm_dysonTerm_le P K v κ hκ hK hP n t ht) hg
    _ = Real.exp (v * t) * Real.exp (κ * t) := by
      dsimp [g]
      calc
        (∑' n : ℕ, Real.exp (v * t) * (κ * t) ^ n /
            (n.factorial : ℝ))
            = ∑' n : ℕ, Real.exp (v * t) *
                ((κ * t) ^ n / (n.factorial : ℝ)) := by
              apply tsum_congr
              intro n
              ring
        _ = Real.exp (v * t) *
              ∑' n : ℕ, (κ * t) ^ n / (n.factorial : ℝ) := tsum_mul_left
        _ = Real.exp (v * t) * Real.exp (κ * t) := by
              rw [← real_exp_eq_tsum_pow_div_factorial]
    _ = Real.exp ((v + κ) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Exact bounded conjugation-defect certificate: once the common-domain
generator identity identifies the conjugated evolution with the canonical
Dyson bounded perturbation, its growth exponent increases by at most κ. -/
theorem bounded_conjugation_defect_certificate
    (P Q : ℝ → A) (K : A) (v₀ κ : ℝ)
    (hκ : 0 ≤ κ) (hK : ‖K‖ ≤ κ)
    (hP : ∀ t, 0 ≤ t → ‖P t‖ ≤ Real.exp (v₀ * t))
    (hQ : ∀ t, 0 ≤ t → Q t = perturbedEvolution P K t) :
    ∀ t, 0 ≤ t → ‖Q t‖ ≤ Real.exp ((v₀ + κ) * t) := by
  intro t ht
  rw [hQ t ht]
  exact norm_perturbedEvolution_le P K v₀ κ t ht hκ hK hP

end BoundedPerturbationDyson
end NCG
