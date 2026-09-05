/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CircleRieszProjectionEigenvector
import NCG.Grand.OperatorGraphResolventEigenspace

/-!
# Circle Riesz ranges for graph-operator kernels

This file joins the weak graph-resolvent equation, the resolvent eigenspace identification, and
the exact circle residue calculation.  If a contour encloses the graph-kernel eigenvalue and its
Riesz operator has the expected finite multiplicity, the Riesz range is exactly the kernel of the
partially defined graph operator.
-/

open Complex Set

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Finite multiplicity plus contour separation identifies the Riesz range of a graph resolvent
with the ambient kernel of the underlying partially defined operator. -/
theorem range_circleRieszProjection_eq_operatorGraphKernel_of_finrank_eq
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (lam : ℝ) (hlam : 0 < lam) (T : E →L[ℂ] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A lam f (T f))
    (center : ℂ) (radius : ℝ)
    (hinside : (((lam : ℝ) : ℂ)⁻¹) ∈ Metric.ball center radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T)
    [Module.Finite ℂ
      (LinearMap.range
        (NCG.ResolventStability.circleRieszProjection T center radius).toLinearMap)]
    (hrank :
      Module.finrank ℂ (LinearMap.range
        (NCG.ResolventStability.circleRieszProjection T center radius).toLinearMap) =
      Module.finrank ℂ (operatorGraphKernel D A)) :
    LinearMap.range
        (NCG.ResolventStability.circleRieszProjection T center radius).toLinearMap =
      operatorGraphKernel D A := by
  calc
    LinearMap.range
        (NCG.ResolventStability.circleRieszProjection T center radius).toLinearMap =
        Module.End.eigenspace T.toLinearMap (((lam : ℝ) : ℂ)⁻¹) := by
      apply NCG.ResolventStability.range_circleRieszProjection_eq_eigenspace_of_finrank_eq
        T center (((lam : ℝ) : ℂ)⁻¹) radius hinside hcontour
      calc
        _ = Module.finrank ℂ (operatorGraphKernel D A) := hrank
        _ = Module.finrank ℂ
            (Module.End.eigenspace T.toLinearMap (((lam : ℝ) : ℂ)⁻¹)) :=
          congrArg (fun S : Submodule ℂ E ↦ Module.finrank ℂ S)
            (operatorGraphKernel_eq_resolventEigenspace D A lam hlam T hequation)
    _ = operatorGraphKernel D A :=
      (operatorGraphKernel_eq_resolventEigenspace D A lam hlam T hequation).symm

end NCG.VaryingHilbert
