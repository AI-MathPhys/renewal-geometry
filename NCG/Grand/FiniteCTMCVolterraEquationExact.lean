/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCFirstJumpConditioningExact
import NCG.Grand.ExponentialHoldingRenewalExact

/-!
# Lebesgue Volterra equation for the actual finite-CTMC path moment

The true first-jump renewal equation is converted to a finite-interval
integral equation, with integrability of its source derived from the path
law. No time regularity of the unknown moment is assumed here.
-/

open MeasureTheory ProbabilityTheory Finset Set
open scoped BigOperators

namespace NCG.FiniteCTMCVolterraEquation

open DrivenProcess DrivenProcess.FinitePath FiniteCTMCJumpSequenceLaw
open FiniteCTMCFirstJumpConditioning FiniteCTMCFirstJumpIntegration
open FiniteCTMCFeynmanKacPathMoment ExponentialHoldingRenewal

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Diagonal occupation growth minus escape killing. -/
def killedRate (L : Matrix S S ℝ) (v : S → ℝ) (k : ℝ) (x : S) : ℝ :=
  -escapeRate L x + k * v x

/-- Weighted off-diagonal jump source for a time-dependent moment vector. -/
def jumpSource (L : Matrix S S ℝ) (g : S → S → ℝ) (k : ℝ)
    (F : ℝ → S → ℝ) (u : ℝ) (x : S) : ℝ :=
  ∑ y, escapeRate L x * destinationProbability L x y * Real.exp (k*g x y) * F u y

/-- The destination average of the first-jump contribution before density weighting. -/
def holdingJumpSource (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ)
    (k : ℝ) (F : ℝ → S → ℝ) (T t : ℝ) (x : S) : ℝ :=
  ∑ y, destinationProbability L x y * Real.exp (k * (t*v x + g x y)) * F (T-t) y

/-- Exact conversion of the exponential density times the destination sum
to the killed-flow jump source. -/
theorem density_mul_holdingJumpSource
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (F : ℝ → S → ℝ) (T t : ℝ) (x : S) :
    escapeRate L x * Real.exp (-(escapeRate L x*t)) * holdingJumpSource L v g k F T t x =
      Real.exp (killedRate L v k x*t) * jumpSource L g k F (T-t) x := by
  unfold holdingJumpSource jumpSource
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [mul_add, Real.exp_add]
  have he : Real.exp (-(escapeRate L x*t)) * Real.exp (k*(t*v x)) =
      Real.exp (killedRate L v k x*t) := by
    rw [← Real.exp_add]
    congr 1
    unfold killedRate
    ring
  calc
    _ = (Real.exp (-(escapeRate L x*t)) * Real.exp (k*(t*v x))) *
        (escapeRate L x * destinationProbability L x y * Real.exp (k*g x y) * F (T-t) y) := by ring
    _ = _ := by rw [he]

variable (L : Matrix S S ℝ) (hL : IsGenerator L)
  (hescape : ∀ x, 0 < escapeRate L x)

/-- The actual destination-averaged renewal integrand is integrable under
the exponential holding-time law. -/
theorem integrable_destinationAverage
    (x : S) (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T) :
    Integrable (fun t => ∑ y, destinationProbability L x y *
      firstJumpHoldingMoment L hL hescape x v g k T f (t,y)) (expMeasure (escapeRate L x)) := by
  have hi := integrable_firstJumpHoldingMoment L hL hescape x v g k T f hT
  unfold holdingDestinationMeasure at hi
  have houter := hi.integral_prod_left
  have heq : (fun t => ∫ y, firstJumpHoldingMoment L hL hescape x v g k T f (t,y)
      ∂destinationMeasure L x) =
      (fun t => ∑ y, destinationProbability L x y *
        firstJumpHoldingMoment L hL hescape x v g k T f (t,y)) := by
    funext t
    exact integral_discrete (destinationProbability L x)
      (destinationProbability_nonnegative L hL hescape x) _
  rwa [heq] at houter

/-- Algebraic form of the destination-averaged renewal integrand. -/
theorem destinationAverage_eq_piecewise
    (x : S) (v : S → ℝ) (g : S → S → ℝ) (k T t : ℝ) (f : S → ℝ) :
    (∑ y, destinationProbability L x y *
      firstJumpHoldingMoment L hL hescape x v g k T f (t,y)) =
      if T < t then Real.exp (k*T*v x) * f x
      else holdingJumpSource L v g k
        (fun u => conditionalPathMoment L hL hescape v g k u f) T t x := by
  by_cases ht : T < t
  · simp only [firstJumpHoldingMoment, if_pos ht, ← Finset.sum_mul,
      sum_destinationProbability L hescape x, one_mul]
  · simp only [firstJumpHoldingMoment, if_neg ht, holdingJumpSource, mul_assoc]

/-- Integrability of the true jump source on every finite physical interval. -/
theorem integrableOn_volterraSource
    (x : S) (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T) :
    IntegrableOn (fun t => Real.exp (killedRate L v k x*t) *
      jumpSource L g k (fun u => conditionalPathMoment L hL hescape v g k u f) (T-t) x)
      (Icc 0 T) := by
  have hi := integrable_destinationAverage L hL hescape x v g k T f hT
  simp_rw [destinationAverage_eq_piecewise] at hi
  have hd := integrableOn_renewal_jump_density (escapeRate L x) T
    (Real.exp (k*T*v x) * f x) (hescape x) _ hi
  simpa only [density_mul_holdingJumpSource] using hd

/-- Actual finite-CTMC path moments satisfy the Lebesgue Volterra equation. -/
theorem conditionalPathMoment_eq_volterra
    (x : S) (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T) :
    conditionalPathMoment L hL hescape v g k T f x =
      Real.exp (killedRate L v k x*T) * f x +
        ∫ t in Icc 0 T, Real.exp (killedRate L v k x*t) *
          jumpSource L g k (fun u => conditionalPathMoment L hL hescape v g k u f) (T-t) x := by
  rw [conditionalPathMoment_eq_integral_firstJumpHoldingMoment L hL hescape x v g k T f hT,
    integral_holdingDestinationMeasure L hL hescape x _
      (integrable_firstJumpHoldingMoment L hL hescape x v g k T f hT)]
  simp_rw [destinationAverage_eq_piecewise]
  have hi := integrable_destinationAverage L hL hescape x v g k T f hT
  simp_rw [destinationAverage_eq_piecewise] at hi
  rw [integral_renewal_eq_survival_add_jump (escapeRate L x) T
    (Real.exp (k*T*v x) * f x) (hescape x) hT _ hi]
  simp_rw [density_mul_holdingJumpSource]
  congr 1
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  unfold killedRate
  ring

end

end NCG.FiniteCTMCVolterraEquation
