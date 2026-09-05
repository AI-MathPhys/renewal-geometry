/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphResolventKernel
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Graph kernels as resolvent eigenspaces

For a positive graph-resolvent shift `λ`, the kernel of the underlying partially defined
operator is the eigenspace of its bounded resolvent at the eigenvalue `λ⁻¹`.  The final theorem
packages the immediate range transfer used after a contour argument has identified the range of
a Riesz projection with that eigenspace.
-/

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F]

/-- Pointwise form of the graph-kernel/resolvent-eigenspace identification. -/
theorem mem_operatorGraphKernel_iff_resolvent_eigenvector
    (D : Submodule K E) (A : D →ₗ[K] F)
    (lam : ℝ) (hlam : 0 < lam) (T : E →L[K] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A lam f (T f))
    (x : E) :
    x ∈ operatorGraphKernel D A ↔
      T x = (((lam : ℝ) : K)⁻¹) • x := by
  rw [mem_operatorGraphKernel_iff_scaledResolvent_fixed D A lam hlam T hequation]
  have hlamK : ((lam : ℝ) : K) ≠ 0 := by
    exact_mod_cast ne_of_gt hlam
  constructor
  · intro hfixed
    have hscaled : ((lam : ℝ) : K) • T x = x := by
      simpa only [map_smul] using hfixed
    calc
      T x = (1 : K) • T x := by simp
      _ = (((lam : ℝ) : K)⁻¹ * ((lam : ℝ) : K)) • T x := by rw [inv_mul_cancel₀ hlamK]
      _ = (((lam : ℝ) : K)⁻¹) • (((lam : ℝ) : K) • T x) := by rw [smul_smul]
      _ = (((lam : ℝ) : K)⁻¹) • x := by rw [hscaled]
  · intro heigen
    rw [map_smul, heigen, smul_smul]
    simp [hlamK]

/-- The ambient kernel of a graph operator is the `λ⁻¹`-eigenspace of its bounded
resolvent at every positive shift. -/
theorem operatorGraphKernel_eq_resolventEigenspace
    (D : Submodule K E) (A : D →ₗ[K] F)
    (lam : ℝ) (hlam : 0 < lam) (T : E →L[K] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A lam f (T f)) :
    operatorGraphKernel D A =
      Module.End.eigenspace T.toLinearMap (((lam : ℝ) : K)⁻¹) := by
  ext x
  rw [mem_operatorGraphKernel_iff_resolvent_eigenvector D A lam hlam T hequation]
  exact Module.End.mem_eigenspace_iff.symm

/-- Once a contour construction identifies the range of a projection with the isolated
`λ⁻¹`-eigenspace of the resolvent, its range is exactly the graph-operator kernel. -/
theorem range_eq_operatorGraphKernel_of_range_eq_resolventEigenspace
    (D : Submodule K E) (A : D →ₗ[K] F)
    (lam : ℝ) (hlam : 0 < lam) (T P : E →L[K] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A lam f (T f))
    (hP : LinearMap.range P.toLinearMap =
      Module.End.eigenspace T.toLinearMap (((lam : ℝ) : K)⁻¹)) :
    LinearMap.range P.toLinearMap = operatorGraphKernel D A := by
  rw [hP, ← operatorGraphKernel_eq_resolventEigenspace D A lam hlam T hequation]

end NCG.VaryingHilbert
