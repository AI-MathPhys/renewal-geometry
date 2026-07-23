/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Drift hull versus dispersion ellipsoid (Minkowski-sum core)

**Proposition `prop:drift-dispersion`**: for constant reset data the
`N`-step displacement set is the `N`-fold Minkowski sum of the step
set; for a *convex* indicatrix this sum is exactly the dilate `N·Θ`
(`NCG.stepSum_eq_smul`) — the ballistic travel-time gauge.  Agreement
with the Lorentzian optical distance forces the indicatrix equality
`Θ = κ·M·B^d`, whose isotropic normalisation `κ = d` is the proved
rounding core.  The lattice-tolerance and metric-derivative arguments
are the noted steps.
-/

open scoped Pointwise

namespace NCG

/-- The `N`-step displacement set: the `N`-fold Minkowski sumset of
the step set `C`. -/
def stepSum {V : Type*} [AddCommGroup V] (C : Set V) : ℕ → Set V
  | 0 => {0}
  | (N + 1) => stepSum C N + C

theorem stepSum_zero {V : Type*} [AddCommGroup V] (C : Set V) :
    stepSum C 0 = {0} := rfl

theorem stepSum_succ {V : Type*} [AddCommGroup V] (C : Set V) (N : ℕ) :
    stepSum C (N + 1) = stepSum C N + C := rfl

/-- **Proposition `prop:drift-dispersion` (Minkowski-sum core)**: for
a convex step set the `N`-step displacement set is exactly the dilate
`N·C` — the drift hull grows linearly with the exact indicatrix
shape. -/
theorem stepSum_eq_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    {C : Set V} (hC : Convex ℝ C) :
    ∀ N : ℕ, stepSum C (N + 1) = (((N : ℝ) + 1)) • C := by
  intro N
  induction N with
  | zero =>
    rw [stepSum_succ, stepSum_zero]
    simp [Set.singleton_add, one_smul]
  | succ N ih =>
    rw [stepSum_succ, ih,
      show ((N + 1 : ℕ) : ℝ) + 1 = ((N : ℝ) + 1) + 1 from by push_cast; ring]
    conv_rhs => rw [hC.add_smul (by positivity) (by norm_num : (0:ℝ) ≤ 1)]
    rw [one_smul]

end NCG
