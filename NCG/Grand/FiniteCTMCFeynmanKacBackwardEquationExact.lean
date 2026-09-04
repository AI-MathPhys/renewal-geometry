/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCVolterraEquationExact
import NCG.Grand.ExponentialVolterraRegularityExact
import NCG.Grand.NonnegativeTimeFeynmanKacExact

/-!
# Backward equation and Feynman--Kac formula for the genuine CTMC path moment

The actual point-start expectation is first proved continuous from its
integrable Volterra equation. Its finite jump source is then continuous,
so the fundamental theorem of calculus gives the backward equation. The
half-line uniqueness theorem identifies the expectation with the tilted
matrix exponential. No backward-equation or moment-integrability hypothesis
is supplied by the caller.
-/

open MeasureTheory Set Matrix
open scoped BigOperators

namespace NCG.FiniteCTMCFeynmanKacBackwardEquation

open DrivenProcess DrivenProcess.FinitePath
open FiniteCTMCFeynmanKacPathMoment FiniteCTMCFeynmanKacCompiler
open FiniteCTMCVolterraEquation ExponentialVolterraRegularity

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

variable (L : Matrix S S ℝ) (hL : IsGenerator L)
  (hescape : ∀ x, 0 < escapeRate L x)

/-- Continuity in physical time is derived from the actual renewal equation. -/
theorem continuousOn_conditionalPathMoment
    (x : S) (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) (f : S → ℝ) :
    ContinuousOn (fun t => conditionalPathMoment L hL hescape v g k t f x) (Ici 0) := by
  exact continuousOn_of_volterra (killedRate L v k x) (f x)
    (fun t => conditionalPathMoment L hL hescape v g k t f x)
    (fun t => jumpSource L g k (fun u => conditionalPathMoment L hL hescape v g k u f) t x)
    (fun T hT => integrableOn_volterraSource L hL hescape x v g k T f hT)
    (fun T hT => conditionalPathMoment_eq_volterra L hL hescape x v g k T f hT)

/-- The finite weighted jump source inherits continuity from the actual
destination-state moments. -/
theorem continuousOn_jumpSource
    (x : S) (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) (f : S → ℝ) :
    ContinuousOn (fun t => jumpSource L g k
      (fun u => conditionalPathMoment L hL hescape v g k u f) t x) (Ici 0) := by
  unfold jumpSource
  apply continuousOn_finsetSum
  intro y _
  exact continuousOn_const.mul (continuousOn_conditionalPathMoment L hL hescape y v g k f)

/-- The physical conditional moment satisfies its exact first-jump backward
equation, including the right derivative at time zero. -/
theorem hasDerivWithinAt_conditionalPathMoment
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) (f : S → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun u => conditionalPathMoment L hL hescape v g k u f)
      (firstJumpDerivative L v g k (fun u => conditionalPathMoment L hL hescape v g k u f) t)
      (Ici 0) t := by
  apply hasDerivWithinAt_pi.mpr
  intro x
  have hd := hasDerivWithinAt_of_volterra (killedRate L v k x) (f x)
    (fun t => conditionalPathMoment L hL hescape v g k t f x)
    (fun t => jumpSource L g k (fun u => conditionalPathMoment L hL hescape v g k u f) t x)
    (fun T hT => integrableOn_volterraSource L hL hescape x v g k T f hT)
    (fun T hT => conditionalPathMoment_eq_volterra L hL hescape x v g k T f hT)
    (continuousOn_jumpSource L hL hescape x v g k f) t ht
  simpa only [firstJumpDerivative, killedRate, jumpSource, diagonal_eq_neg_escapeRate hL] using hd

/-- The concrete path expectation starts at the terminal function. -/
theorem conditionalPathMoment_zero
    (v : S → ℝ) (g : S → S → ℝ) (k : ℝ) (f : S → ℝ) :
    conditionalPathMoment L hL hescape v g k 0 f = f := by
  funext x
  simpa using
    conditionalPathMoment_eq_volterra L hL hescape x v g k 0 f le_rfl

/-- Genuine point-start finite-state Feynman--Kac formula for positive
escape rates, proved from the Ionescu--Tulcea path expectation. -/
theorem conditionalPathMoment_eq_exponentialEntry_mulVec [Nonempty S]
    (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T) :
    conditionalPathMoment L hL hescape v g k T f =
      Matrix.mulVec (Matrix.exponentialEntry (T • tilt L v g k)) f := by
  exact NonnegativeTimeFeynmanKac.eq_exponentialEntry_mulVec_of_firstJumpConditioning_nonnegative
    L v g k hescape f (fun u => conditionalPathMoment L hL hescape v g k u f)
    (hasDerivWithinAt_conditionalPathMoment L hL hescape v g k f)
    (conditionalPathMoment_zero L hL hescape v g k f) T hT

end

end NCG.FiniteCTMCFeynmanKacBackwardEquation
