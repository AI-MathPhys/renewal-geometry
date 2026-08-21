/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BoundedOperatorNormalResolventFamily

/-!
# Injectivity of bounded normal resolvents

At a positive shift, the strong normal equation makes the canonical inverse of
`A† A + λ I` injective without any closed-range or kernel assumption on `A`.
-/

noncomputable section
open scoped InnerProduct

namespace NCG.VaryingHilbert

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The canonical positive-shift bounded normal resolvent is injective. -/
theorem boundedOperatorNormalResolventFamily_injective
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam) :
    Function.Injective (boundedOperatorNormalResolventFamily A lam) := by
  intro x y hxy
  calc
    x = (A† ∘L A) (boundedOperatorNormalResolventFamily A lam x) +
        (lam : ℂ) • boundedOperatorNormalResolventFamily A lam x :=
      (boundedOperatorNormalResolventFamily_normalEquation A lam hlam x).symm
    _ = (A† ∘L A) (boundedOperatorNormalResolventFamily A lam y) +
        (lam : ℂ) • boundedOperatorNormalResolventFamily A lam y := by rw [hxy]
    _ = y := boundedOperatorNormalResolventFamily_normalEquation A lam hlam y

end NCG.VaryingHilbert
