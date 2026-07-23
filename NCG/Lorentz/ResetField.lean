/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Reset fields and sprinkling covariance (encodings)

**Definition `def:reset-field`** (encoding): a nondegenerate reset
field over a base `X` — pointwise reset directions and strictly
positive normalised weights (`NCG.ResetField`); the smoothness and
nondegeneracy of the direction frame are stated as side conditions in
the manuscript.

**Theorem `thm:sprinkling`** (encoding): the covariance property of
Poisson sprinkling — invariance of the intensity measure under a
symmetry (`NCG.SprinklingCovariance`); that a Poisson process with
invariant intensity has invariant law is the established external
input. -/

namespace NCG

/-- **Definition `def:reset-field`** (encoding): a reset field on a
base `X` with `m` channels in `d` ambient directions — pointwise reset
directions `dir` and strictly positive weights `weight` normalised to
total mass one. -/
structure ResetField (X : Type*) (m d : ℕ) where
  /-- The reset direction of channel `a` at the point `x`. -/
  dir : X → Fin m → Fin d → ℝ
  /-- The reset weight of channel `a` at the point `x`. -/
  weight : X → Fin m → ℝ
  weight_pos : ∀ x a, 0 < weight x a
  weight_sum : ∀ x, ∑ a, weight x a = 1

/-- **Theorem `thm:sprinkling`** (encoding): sprinkling covariance —
the symmetry `T` preserves the sprinkling intensity measure `μ`.  A
Poisson point process with `T`-invariant intensity has `T`-invariant
law; that functoriality is the established external input. -/
def SprinklingCovariance {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (T : X → X) : Prop :=
  MeasureTheory.MeasurePreserving T μ μ

/-- The identity symmetry is sprinkling-covariant. -/
theorem sprinklingCovariance_id {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) : SprinklingCovariance μ id :=
  MeasureTheory.MeasurePreserving.id μ

/-- Sprinkling covariance is closed under composition — the invariance
group of the intensity is a genuine symmetry group. -/
theorem sprinklingCovariance_comp {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} {T U : X → X}
    (hT : SprinklingCovariance μ T) (hU : SprinklingCovariance μ U) :
    SprinklingCovariance μ (T ∘ U) :=
  hT.comp hU

end NCG
