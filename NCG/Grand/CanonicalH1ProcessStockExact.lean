/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical H1 process payment and replenishment

This file formalizes (NS.0a)--(NS.0c).  Once the assembled strong-solution
energy balance is supplied in integral form, the positive and negative parts
of its net loss are the unique nonduplicating payment and replenishment.
-/

open MeasureTheory intervalIntegral
open scoped RealInnerProductSpace

noncomputable section

namespace NCG.CanonicalH1ProcessStock

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A typed Hilbert-space evolution gives the strong-solution `H¹` energy
identity once the viscous and nonlinear pairings are identified with `Z₁`
and `G₁`.  Here `w=A^{1/2}u`. -/
theorem h1_energy_derivative_of_evolution
    (w wdot viscous production : ℝ → H) (Z G : ℝ → ℝ) (nu q : ℝ)
    (hw : HasDerivAt w (wdot q) q)
    (hevolution : wdot q = -(nu • viscous q) + production q)
    (hviscous : ⟪w q, viscous q⟫ = Z q)
    (hproduction : ⟪w q, production q⟫ = G q) :
    HasDerivAt (fun r => ‖w r‖ ^ 2) (2 * (G q - nu * Z q)) q := by
  refine hw.norm_sq.congr_deriv ?_
  rw [hevolution]
  simp only [inner_add_right, inner_neg_right, inner_smul_right]
  rw [hviscous, hproduction]
  ring

/-- Integral form of the exact strong-solution balance
`(1/2)Y₁' + nu Z₁ = G₁`. -/
theorem h1_energy_integral_balance_of_evolution
    (w wdot viscous production : ℝ → H) (Z G : ℝ → ℝ) (nu s t : ℝ)
    (hw : ∀ q, HasDerivAt w (wdot q) q)
    (hevolution : ∀ q, wdot q = -(nu • viscous q) + production q)
    (hviscous : ∀ q, ⟪w q, viscous q⟫ = Z q)
    (hproduction : ∀ q, ⟪w q, production q⟫ = G q)
    (hint : IntervalIntegrable (fun q => 2 * (G q - nu * Z q)) volume s t) :
    ‖w t‖ ^ 2 - ‖w s‖ ^ 2 =
      ∫ q in s..t, 2 * (G q - nu * Z q) := by
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun q hq => h1_energy_derivative_of_evolution w wdot viscous production
      Z G nu q (hw q) (hevolution q) (hviscous q) (hproduction q)) hint

/-- Net `H¹` loss rate `2 (nu Z₁ - G₁)`. -/
def netLossRate (nu : ℝ) (Z G : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * (nu * Z t - G t)

/-- **(NS.0a)**: the canonical net payment rate. -/
def paymentRate (nu : ℝ) (Z G : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * max (nu * Z t - G t) 0

/-- **(NS.0a)**: the canonical net replenishment rate. -/
def replenishmentRate (nu : ℝ) (Z G : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * max (G t - nu * Z t) 0

/-- **(NS.0c)**: turnover erased when viscosity and production are split
before their common stock row is assembled. -/
def duplicatedTurnoverRate (nu : ℝ) (Z G : ℝ → ℝ) (t : ℝ) : ℝ :=
  nu * Z t + |G t| - |nu * Z t - G t|

theorem payment_sub_replenishment
    (nu : ℝ) (Z G : ℝ → ℝ) (t : ℝ) :
    paymentRate nu Z G t - replenishmentRate nu Z G t =
      netLossRate nu Z G t := by
  by_cases h : 0 ≤ nu * Z t - G t
  · have hn : G t - nu * Z t ≤ 0 := by linarith
    simp [paymentRate, replenishmentRate, netLossRate,
      max_eq_left h, max_eq_right hn]
  · have hn : nu * Z t - G t ≤ 0 := le_of_not_ge h
    have hp : 0 ≤ G t - nu * Z t := by linarith
    simp [paymentRate, replenishmentRate, netLossRate,
      max_eq_right hn, max_eq_left hp]
    ring

theorem payment_replenishment_nonnegative_disjoint
    (nu : ℝ) (Z G : ℝ → ℝ) (t : ℝ) :
    0 ≤ paymentRate nu Z G t ∧
      0 ≤ replenishmentRate nu Z G t ∧
      paymentRate nu Z G t * replenishmentRate nu Z G t = 0 := by
  unfold paymentRate replenishmentRate
  constructor
  · positivity
  constructor
  · positivity
  · by_cases h : 0 ≤ nu * Z t - G t
    · have hn : G t - nu * Z t ≤ 0 := by linarith
      simp [max_eq_left h, max_eq_right hn]
    · have hn : nu * Z t - G t ≤ 0 := le_of_not_ge h
      simp [max_eq_right hn]

/-- The Jordan pair is pointwise unique among nonnegative, mutually singular
rates with the assembled net loss. -/
theorem payment_replenishment_unique
    (nu : ℝ) (Z G : ℝ → ℝ) (t p r : ℝ)
    (hp : 0 ≤ p) (hr : 0 ≤ r) (hpr : p * r = 0)
    (hnet : p - r = netLossRate nu Z G t) :
    p = paymentRate nu Z G t ∧ r = replenishmentRate nu Z G t := by
  rcases mul_eq_zero.mp hpr with hp0 | hr0
  · subst p
    have hrate : netLossRate nu Z G t ≤ 0 := by linarith
    have hraw : nu * Z t - G t ≤ 0 := by
      unfold netLossRate at hrate
      linarith
    have hraw' : 0 ≤ G t - nu * Z t := by linarith
    simp [paymentRate, replenishmentRate, max_eq_right hraw,
      max_eq_left hraw']
    unfold netLossRate at hnet
    linarith
  · subst r
    have hrate : 0 ≤ netLossRate nu Z G t := by linarith
    have hraw : 0 ≤ nu * Z t - G t := by
      unfold netLossRate at hrate
      linarith
    have hraw' : G t - nu * Z t ≤ 0 := by linarith
    simp [paymentRate, replenishmentRate, max_eq_left hraw,
      max_eq_right hraw']
    unfold netLossRate at hnet
    linarith

/-- **(NS.0b)**: the exact finite-stock balance on an interval. -/
theorem integrated_stock_balance
    (Y Z G : ℝ → ℝ) (nu s t : ℝ)
    (hp : IntervalIntegrable (paymentRate nu Z G) volume s t)
    (hr : IntervalIntegrable (replenishmentRate nu Z G) volume s t)
    (henergy : Y t - Y s =
      ∫ q in s..t, 2 * (G q - nu * Z q)) :
    Y t + ∫ q in s..t, paymentRate nu Z G q =
      Y s + ∫ q in s..t, replenishmentRate nu Z G q := by
  have hdiff :
      (∫ q in s..t, paymentRate nu Z G q) -
          ∫ q in s..t, replenishmentRate nu Z G q = Y s - Y t := by
    rw [← intervalIntegral.integral_sub hp hr]
    calc
      (∫ q in s..t, paymentRate nu Z G q - replenishmentRate nu Z G q) =
          ∫ q in s..t, -(2 * (G q - nu * Z q)) := by
            apply intervalIntegral.integral_congr
            intro q hq
            change paymentRate nu Z G q - replenishmentRate nu Z G q =
              -(2 * (G q - nu * Z q))
            rw [payment_sub_replenishment]
            unfold netLossRate
            ring
      _ = -(∫ q in s..t, 2 * (G q - nu * Z q)) := by
        rw [intervalIntegral.integral_neg]
      _ = Y s - Y t := by rw [← henergy]; ring
  linarith

/-- Full exact accounting package of `thm:NS-H1-process-stock`. -/
theorem canonical_h1_process_payment_and_replenishment
    (Y Z G : ℝ → ℝ) (nu s t : ℝ)
    (hp : IntervalIntegrable (paymentRate nu Z G) volume s t)
    (hr : IntervalIntegrable (replenishmentRate nu Z G) volume s t)
    (henergy : Y t - Y s =
      ∫ q in s..t, 2 * (G q - nu * Z q)) :
    (∀ q,
      0 ≤ paymentRate nu Z G q ∧
      0 ≤ replenishmentRate nu Z G q ∧
      paymentRate nu Z G q * replenishmentRate nu Z G q = 0) ∧
    Y t + ∫ q in s..t, paymentRate nu Z G q =
      Y s + ∫ q in s..t, replenishmentRate nu Z G q ∧
    (∀ q p r, 0 ≤ p → 0 ≤ r → p * r = 0 →
      p - r = netLossRate nu Z G q →
      p = paymentRate nu Z G q ∧ r = replenishmentRate nu Z G q) ∧
    (∀ q, duplicatedTurnoverRate nu Z G q =
      nu * Z q + |G q| - |nu * Z q - G q|) := by
  refine ⟨payment_replenishment_nonnegative_disjoint nu Z G,
    integrated_stock_balance Y Z G nu s t hp hr henergy, ?_, ?_⟩
  · intro q p r hp' hr' hpr hnet
    exact payment_replenishment_unique nu Z G q p r hp' hr' hpr hnet
  · intro q
    rfl

/-- The manuscript theorem with the `H¹` energy balance derived from a typed
strong evolution rather than supplied as a scalar premise. -/
theorem canonical_h1_process_stock_of_evolution
    (w wdot viscous production : ℝ → H) (Z G : ℝ → ℝ) (nu s t : ℝ)
    (hw : ∀ q, HasDerivAt w (wdot q) q)
    (hevolution : ∀ q, wdot q = -(nu • viscous q) + production q)
    (hviscous : ∀ q, ⟪w q, viscous q⟫ = Z q)
    (hproduction : ∀ q, ⟪w q, production q⟫ = G q)
    (hint : IntervalIntegrable (fun q => 2 * (G q - nu * Z q)) volume s t)
    (hp : IntervalIntegrable (paymentRate nu Z G) volume s t)
    (hr : IntervalIntegrable (replenishmentRate nu Z G) volume s t) :
    (∀ q,
      0 ≤ paymentRate nu Z G q ∧
      0 ≤ replenishmentRate nu Z G q ∧
      paymentRate nu Z G q * replenishmentRate nu Z G q = 0) ∧
    ‖w t‖ ^ 2 + ∫ q in s..t, paymentRate nu Z G q =
      ‖w s‖ ^ 2 + ∫ q in s..t, replenishmentRate nu Z G q ∧
    (∀ q p r, 0 ≤ p → 0 ≤ r → p * r = 0 →
      p - r = netLossRate nu Z G q →
      p = paymentRate nu Z G q ∧ r = replenishmentRate nu Z G q) ∧
    (∀ q, duplicatedTurnoverRate nu Z G q =
      nu * Z q + |G q| - |nu * Z q - G q|) := by
  exact canonical_h1_process_payment_and_replenishment
    (fun q => ‖w q‖ ^ 2) Z G nu s t hp hr
    (h1_energy_integral_balance_of_evolution w wdot viscous production
      Z G nu s t hw hevolution hviscous hproduction hint)

end NCG.CanonicalH1ProcessStock
