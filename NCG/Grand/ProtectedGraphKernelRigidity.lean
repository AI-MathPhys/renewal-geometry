/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CircleRieszProjectionOperatorGraphKernel

/-!
# Protected graph-kernel rigidity from Riesz multiplicity

The graph-resolvent residue theorem puts the graph kernel inside the range of every circle Riesz
operator enclosing the kernel eigenvalue.  Hence a protected subspace contained in the kernel
locks the entire kernel as soon as its dimension equals the finite Riesz multiplicity.  An
eventual version is the kernel-stabilization step in the coercive continuum Howe argument.
-/

open Filter Topology Complex Set

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- A protected subspace contained in a graph kernel equals that kernel when its dimension is the
finite multiplicity selected by a contour around the graph-resolvent kernel eigenvalue. -/
theorem range_protected_eq_operatorGraphKernel_of_riesz_finrank_eq
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] F)
    (lam : ℝ) (hlam : 0 < lam) (T P : E →L[ℂ] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A lam f (T f))
    (center : ℂ) (radius : ℝ)
    (hinside : (((lam : ℝ) : ℂ)⁻¹) ∈ Metric.ball center radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T)
    [Module.Finite ℂ
      (LinearMap.range
        (NCG.ResolventStability.circleRieszProjection T center radius).toLinearMap)]
    (hprotected : LinearMap.range P.toLinearMap ≤ operatorGraphKernel D A)
    (hrank :
      Module.finrank ℂ (LinearMap.range P.toLinearMap) =
      Module.finrank ℂ (LinearMap.range
        (NCG.ResolventStability.circleRieszProjection T center radius).toLinearMap)) :
    LinearMap.range P.toLinearMap = operatorGraphKernel D A := by
  have hkernelRiesz :
      operatorGraphKernel D A ≤
        LinearMap.range
          (NCG.ResolventStability.circleRieszProjection T center radius).toLinearMap := by
    rw [operatorGraphKernel_eq_resolventEigenspace D A lam hlam T hequation]
    exact NCG.ResolventStability.eigenspace_le_range_circleRieszProjection_of_mem_ball
      T center (((lam : ℝ) : ℂ)⁻¹) radius hinside hcontour
  have hprotectedRiesz :
      LinearMap.range P.toLinearMap =
        LinearMap.range
          (NCG.ResolventStability.circleRieszProjection T center radius).toLinearMap :=
    Submodule.eq_of_le_of_finrank_eq (hprotected.trans hkernelRiesz) hrank
  apply le_antisymm hprotected
  rw [hprotectedRiesz]
  exact hkernelRiesz

/-- Eventual kernel locking from protected inclusion and stabilized finite Riesz multiplicity. -/
theorem eventually_range_protected_eq_operatorGraphKernel_of_riesz_finrank_eq
    (D : ℕ → Submodule ℂ E) (A : ∀ n, D n →ₗ[ℂ] F)
    (lam : ℝ) (hlam : 0 < lam) (T P : ℕ → E →L[ℂ] E)
    (hequation : ∀ n f, OperatorGraphResolventEquation (D n) (A n) lam f (T n f))
    (center : ℂ) (radius : ℝ)
    (hinside : (((lam : ℝ) : ℂ)⁻¹) ∈ Metric.ball center radius)
    (hcontour : ∀ n z, z ∈ Metric.sphere center radius → z ∈ resolventSet ℂ (T n))
    (hfinite : ∀ n, Module.Finite ℂ
      (LinearMap.range
        (NCG.ResolventStability.circleRieszProjection (T n) center radius).toLinearMap))
    (hprotected : ∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap ≤ operatorGraphKernel (D n) (A n))
    (hrank : ∀ᶠ n in atTop,
      Module.finrank ℂ (LinearMap.range (P n).toLinearMap) =
      Module.finrank ℂ (LinearMap.range
        (NCG.ResolventStability.circleRieszProjection (T n) center radius).toLinearMap)) :
    ∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap = operatorGraphKernel (D n) (A n) := by
  filter_upwards [hprotected, hrank] with n hnProtected hnRank
  letI : Module.Finite ℂ
      (LinearMap.range
        (NCG.ResolventStability.circleRieszProjection (T n) center radius).toLinearMap) :=
    hfinite n
  exact range_protected_eq_operatorGraphKernel_of_riesz_finrank_eq
    (D n) (A n) lam hlam (T n) (P n) (hequation n)
      center radius hinside (fun z hz ↦ hcontour n z hz) hnProtected hnRank

end NCG.VaryingHilbert
