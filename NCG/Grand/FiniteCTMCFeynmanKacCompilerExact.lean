/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCFirstJumpGeneratorExact
import NCG.Grand.FiniteFeynmanKacBackwardEquationExact

/-!
# First-jump to Feynman--Kac compiler

This module packages the exact final deterministic step of the probabilistic
argument.  Once the conditional path expectation has the derivative supplied
by first-jump conditioning, the first-jump coefficients assemble to the
tilted generator and ODE uniqueness gives the matrix exponential formula.
-/

open Matrix

noncomputable section

namespace NCG.FiniteCTMCFeynmanKacCompiler

open NCG.DrivenProcess
open NCG.DrivenProcess.FinitePath
open NCG.FiniteCTMCJumpSequenceLaw
open NCG.FiniteCTMCFirstJumpGenerator
open NCG.FiniteFeynmanKacBackwardEquation

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Derivative obtained by conditioning on the first holding time and next
state. -/
def firstJumpDerivative
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (F : ℝ → S → ℝ) (t : ℝ) : S → ℝ :=
  fun x =>
    (L x x + k * v x) * F t x +
      ∑ y, escapeRate L x * destinationProbability L x y *
        Real.exp (k * g x y) * F t y

/-- Exact interface delivered by probabilistic first-jump conditioning. -/
structure SatisfiesFirstJumpBackwardEquation
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (f : S → ℝ) (F : ℝ → S → ℝ) : Prop where
  hasDerivAt : ∀ t, HasDerivAt F (firstJumpDerivative L v g k F t) t
  initial : F 0 = f

/-- The probabilistic first-jump derivative is exactly `B_k F`. -/
theorem firstJumpDerivative_eq_tilt_mulVec
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (hescape : ∀ x, 0 < escapeRate L x)
    (F : ℝ → S → ℝ) (t : ℝ) :
    firstJumpDerivative L v g k F t = (tilt L v g k).mulVec (F t) := by
  funext x
  exact diagonal_add_weightedDestination_eq_tilt_mulVec
    L v g k hescape (F t) x

/-- **Finite CTMC Feynman--Kac compiler.**  A conditional expectation that
satisfies the genuine first-jump backward equation is necessarily the tilted
matrix exponential applied to the terminal reward. -/
theorem eq_exponentialEntry_mulVec_of_firstJumpConditioning
    [Nonempty S]
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (hescape : ∀ x, 0 < escapeRate L x)
    (f : S → ℝ) (F : ℝ → S → ℝ)
    (hF : SatisfiesFirstJumpBackwardEquation L v g k f F) (t : ℝ) :
    F t = Matrix.mulVec
      (Matrix.exponentialEntry (t • tilt L v g k)) f := by
  apply eq_exponentialEntry_mulVec_of_backwardEquation
    (tilt L v g k) f F _ hF.initial t
  intro u
  rw [← firstJumpDerivative_eq_tilt_mulVec L v g k hescape F u]
  exact hF.hasDerivAt u

/-- Functional extensional form of the same compiler. -/
theorem firstJumpConditioning_unique
    [Nonempty S]
    (L : Matrix S S ℝ) (v : S → ℝ) (g : S → S → ℝ) (k : ℝ)
    (hescape : ∀ x, 0 < escapeRate L x)
    (f : S → ℝ) (F : ℝ → S → ℝ)
    (hF : SatisfiesFirstJumpBackwardEquation L v g k f F) :
    F = fun t => Matrix.mulVec
      (Matrix.exponentialEntry (t • tilt L v g k)) f := by
  funext t
  exact eq_exponentialEntry_mulVec_of_firstJumpConditioning
    L v g k hescape f F hF t

end NCG.FiniteCTMCFeynmanKacCompiler
