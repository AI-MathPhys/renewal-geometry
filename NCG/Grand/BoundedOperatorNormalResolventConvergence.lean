/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BoundedOperatorNormalResolventFamily
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Continuity of bounded normal resolvents

The canonical positive inverse of `A†A + λ` is the Banach-algebra inverse of
the shifted normal operator.  Consequently it converges in operator norm
whenever the shifted normal operators do.  The formulation in this file is
particularly convenient when `A†A` has already been identified with an
explicit Fourier symbol.
-/

open Filter Topology
open scoped InnerProduct

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- The canonical positive normal resolvent is exactly the ring inverse of
its shifted normal operator. -/
theorem boundedOperatorNormalResolvent_eq_ringInverse
    (A : H →L[ℂ] F) (lam : ℝ) (hlam : 0 < lam) :
    boundedOperatorNormalResolvent A lam hlam =
      Ring.inverse (shiftedBoundedNormalCLM A lam) := by
  let hunit := shiftedBoundedNormalCLM_isUnit A lam hlam
  have hinverse :
      Ring.inverse (shiftedBoundedNormalCLM A lam) =
        (↑(hunit.unit⁻¹) : H →L[ℂ] H) := by
    calc
      Ring.inverse (shiftedBoundedNormalCLM A lam) =
          Ring.inverse (↑hunit.unit : H →L[ℂ] H) :=
        congrArg Ring.inverse hunit.unit_spec.symm
      _ = (↑(hunit.unit⁻¹) : H →L[ℂ] H) := Ring.inverse_unit hunit.unit
  rw [hinverse]
  apply ContinuousLinearMap.ext
  intro f
  apply (shiftedBoundedNormalEquiv A lam hlam).injective
  change
    (shiftedBoundedNormalEquiv A lam hlam)
        ((shiftedBoundedNormalEquiv A lam hlam).symm f) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change f = shiftedBoundedNormalCLM A lam ((↑(hunit.unit⁻¹) : H →L[ℂ] H) f)
  symm
  rw [← ContinuousLinearMap.mul_apply, hunit.mul_val_inv]
  rfl

/-- Operator-norm convergence of shifted normal operators implies
operator-norm convergence of their canonical positive resolvents. -/
theorem boundedOperatorNormalResolvent_tendsto_of_shifted
    {ι : Type*} {l : Filter ι} (Aι : ι → H →L[ℂ] F) (A : H →L[ℂ] F)
    (lam : ℝ) (hlam : 0 < lam)
    (hshift : Tendsto
      (fun i ↦ shiftedBoundedNormalCLM (Aι i) lam) l
      (𝓝 (shiftedBoundedNormalCLM A lam))) :
    Tendsto
      (fun i ↦ boundedOperatorNormalResolvent (Aι i) lam hlam) l
      (𝓝 (boundedOperatorNormalResolvent A lam hlam)) := by
  let hunit := shiftedBoundedNormalCLM_isUnit A lam hlam
  have hinv := (NormedRing.inverse_continuousAt hunit.unit).tendsto
  rw [hunit.unit_spec] at hinv
  simp_rw [boundedOperatorNormalResolvent_eq_ringInverse]
  change Tendsto
    (Ring.inverse ∘ fun i ↦ shiftedBoundedNormalCLM (Aι i) lam) l
    (𝓝 (Ring.inverse (shiftedBoundedNormalCLM A lam)))
  exact hinv.comp hshift

end NCG.VaryingHilbert
