/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealBoundedOperatorNormalResolvent
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Canonical resolvent of a bounded normal operator

For a bounded operator `A` between complex Hilbert spaces, the shifted normal
operator `A† A + λ I` is bounded below at every positive real shift.  The
positive-operator invertibility criterion supplies a continuous inverse.  This
module packages that inverse and its exact normal and weak graph equations.
-/

open scoped InnerProduct NNReal

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- The positive shifted normal operator `A† A + λ I`. -/
noncomputable def shiftedBoundedNormalCLM (A : H →L[ℂ] F) (lam : ℝ) :
    H →L[ℂ] H :=
  (A† ∘L A) + (lam : ℂ) • 1

@[simp] theorem shiftedBoundedNormalCLM_apply
    (A : H →L[ℂ] F) (lam : ℝ) (x : H) :
    shiftedBoundedNormalCLM A lam x =
      (A† ∘L A) x + (lam : ℂ) • x := by
  simp [shiftedBoundedNormalCLM]

/-- The shifted normal operator has the expected exact quadratic form. -/
theorem shiftedBoundedNormalCLM_inner_re
    (A : H →L[ℂ] F) (lam : ℝ) (x : H) :
    (inner ℂ (shiftedBoundedNormalCLM A lam x) x).re =
      ‖A x‖ ^ 2 + lam * ‖x‖ ^ 2 := by
  rw [shiftedBoundedNormalCLM_apply, inner_add_left,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, inner_smul_left]
  simp
  norm_cast

/-- A positive shift makes the bounded normal operator invertible. -/
theorem shiftedBoundedNormalCLM_isUnit
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam) :
    IsUnit (shiftedBoundedNormalCLM A lam) := by
  let c : ℝ≥0 := ⟨lam, hlam.le⟩
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    (shiftedBoundedNormalCLM A lam) (c := c)
  · exact_mod_cast hlam
  · intro x
    calc
      ‖x‖ ^ 2 * (c : ℝ) = lam * ‖x‖ ^ 2 := by
        change ‖x‖ ^ 2 * lam = lam * ‖x‖ ^ 2
        ring
      _ ≤ ‖A x‖ ^ 2 + lam * ‖x‖ ^ 2 := by
        nlinarith [sq_nonneg ‖A x‖]
      _ = (inner ℂ (shiftedBoundedNormalCLM A lam x) x).re :=
        (shiftedBoundedNormalCLM_inner_re A lam x).symm
      _ ≤ ‖inner ℂ (shiftedBoundedNormalCLM A lam x) x‖ :=
        Complex.re_le_norm _

/-- The positive shifted normal operator as a continuous linear equivalence. -/
noncomputable def shiftedBoundedNormalEquiv
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam) : H ≃L[ℂ] H :=
  let hbij := ContinuousLinearMap.isUnit_iff_bijective.mp
    (shiftedBoundedNormalCLM_isUnit A lam hlam)
  ContinuousLinearEquiv.ofBijective (shiftedBoundedNormalCLM A lam)
    (LinearMap.ker_eq_bot.mpr hbij.1)
    (LinearMap.range_eq_top.mpr hbij.2)

@[simp] theorem shiftedBoundedNormalEquiv_apply
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam) (x : H) :
    shiftedBoundedNormalEquiv A lam hlam x =
      shiftedBoundedNormalCLM A lam x := by
  rfl

/-- The canonical positive-shift resolvent of the bounded normal operator. -/
noncomputable def boundedOperatorNormalResolvent
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam) : H →L[ℂ] H :=
  (shiftedBoundedNormalEquiv A lam hlam).symm.toContinuousLinearMap

/-- The canonical bounded normal resolvent solves the exact strong equation. -/
theorem boundedOperatorNormalResolvent_normalEquation
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam) (f : H) :
    (A† ∘L A) (boundedOperatorNormalResolvent A lam hlam f) +
        (lam : ℂ) • boundedOperatorNormalResolvent A lam hlam f = f := by
  rw [← shiftedBoundedNormalCLM_apply,
    ← shiftedBoundedNormalEquiv_apply]
  exact (shiftedBoundedNormalEquiv A lam hlam).apply_symm_apply f

/-- The canonical bounded normal resolvent solves the weak graph equation. -/
theorem boundedOperatorNormalResolvent_resolventEquation
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam) (f : H) :
    OperatorGraphResolventEquation (⊤ : Submodule ℂ H)
      (boundedOperatorGraphMap A) lam f
      (boundedOperatorNormalResolvent A lam hlam f) := by
  exact boundedOperatorGraph_resolventEquation_of_normalEquation
    A lam f (boundedOperatorNormalResolvent A lam hlam f)
      (boundedOperatorNormalResolvent_normalEquation A lam hlam f)

end NCG.VaryingHilbert
