/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealOperatorGraphResolventMinimizer

/-!
# Operator kernels as fixed spaces of graph resolvents

Weak graph-resolvent solutions are unique at every positive shift.  Consequently the ambient
kernel of the graph operator is exactly the fixed space of the scaled resolvent `λ Tλ`.  This is
the algebraic identification needed to read the zero eigenspace of an unbounded nonnegative
operator from an isolated eigenvalue of its bounded resolvent.
-/

open Set

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F]

/-- The kernel of a partially defined graph operator, viewed as a submodule of its ambient
Hilbert space. -/
def operatorGraphKernel (D : Submodule K E) (A : D →ₗ[K] F) : Submodule K E :=
  (LinearMap.ker A).map D.subtype

/-- Ambient membership in the graph-operator kernel is domain membership together with vanishing
operator value. -/
theorem mem_operatorGraphKernel_iff
    (D : Submodule K E) (A : D →ₗ[K] F) (x : E) :
    x ∈ operatorGraphKernel D A ↔
      ∃ hx : x ∈ D, A ⟨x, hx⟩ = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, LinearMap.mem_ker.mp hy⟩
  · rintro ⟨hx, hAx⟩
    refine ⟨⟨x, hx⟩, LinearMap.mem_ker.mpr hAx, rfl⟩

/-- Weak graph-resolvent solutions at a positive shift are unique. -/
theorem OperatorGraphResolventEquation.eq_of_pos
    (D : Submodule K E) (A : D →ₗ[K] F)
    (lam : ℝ) (hlam : 0 < lam) (f x y : E)
    (hx : OperatorGraphResolventEquation D A lam f x)
    (hy : OperatorGraphResolventEquation D A lam f y) :
    x = y := by
  have hgap := operatorGraph_resolventObjective_sub_eq
    D A lam f x hx y hy.mem
  have hmin := operatorGraph_resolventObjective_minimizer
    D A lam hlam.le f y hy x hx.mem
  have hdist : ‖y - x‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖A ⟨y, hy.mem⟩ - A ⟨x, hx.mem⟩‖,
      sq_nonneg ‖y - x‖]
  have hyx : y - x = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hdist)
  exact (sub_eq_zero.mp hyx).symm

/-- At a positive shift, an ambient vector lies in the graph-operator kernel exactly when it is a
fixed vector of the scaled resolvent. -/
theorem mem_operatorGraphKernel_iff_scaledResolvent_fixed
    (D : Submodule K E) (A : D →ₗ[K] F)
    (lam : ℝ) (hlam : 0 < lam) (T : E →L[K] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A lam f (T f))
    (x : E) :
    x ∈ operatorGraphKernel D A ↔
      T (((lam : ℝ) : K) • x) = x := by
  constructor
  · intro hx
    obtain ⟨hxD, hAx⟩ := (mem_operatorGraphKernel_iff D A x).mp hx
    let xD : D := ⟨x, hxD⟩
    have hxEquation : OperatorGraphResolventEquation D A lam
        (((lam : ℝ) : K) • x) x := {
      mem := hxD
      weakEuler z := by
        have hAx' : A xD = 0 := hAx
        simp only [xD] at hAx'
        rw [hAx']
        rw [inner_smul_right, RCLike.mul_re]
        simp only [RCLike.ofReal_re, RCLike.ofReal_im, inner_zero_left,
          map_zero, zero_add, zero_mul, sub_zero]
        exact congrArg (fun r : ℝ ↦ lam * r) (inner_re_symm (𝕜 := K) x z)
    }
    exact (hequation (((lam : ℝ) : K) • x)).eq_of_pos
      D A lam hlam (((lam : ℝ) : K) • x) (T (((lam : ℝ) : K) • x)) x
        hxEquation
  · intro hfixed
    have h : OperatorGraphResolventEquation D A lam
        (((lam : ℝ) : K) • x) x := by
      simpa only [hfixed] using hequation (((lam : ℝ) : K) • x)
    have hxD : x ∈ D := h.mem
    have heuler := h.weakEuler ⟨x, hxD⟩
    have hnorm : ‖A ⟨x, hxD⟩‖ ^ 2 = 0 := by
      rw [← norm_sq_eq_re_inner (𝕜 := K)] at heuler
      rw [← norm_sq_eq_re_inner (𝕜 := K) x] at heuler
      rw [inner_smul_right, RCLike.mul_re] at heuler
      simp only [RCLike.ofReal_re, RCLike.ofReal_im, zero_mul, sub_zero] at heuler
      rw [← norm_sq_eq_re_inner (𝕜 := K) x] at heuler
      nlinarith
    exact (mem_operatorGraphKernel_iff D A x).2
      ⟨hxD, norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)⟩

/-- Submodule form of the kernel/fixed-space identification. -/
theorem operatorGraphKernel_eq_scaledResolvent_fixedSpace
    (D : Submodule K E) (A : D →ₗ[K] F)
    (lam : ℝ) (hlam : 0 < lam) (T : E →L[K] E)
    (hequation : ∀ f : E, OperatorGraphResolventEquation D A lam f (T f)) :
    operatorGraphKernel D A =
      LinearMap.ker
        ((((lam : ℝ) : K) • T).toLinearMap - LinearMap.id) := by
  ext x
  rw [mem_operatorGraphKernel_iff_scaledResolvent_fixed D A lam hlam T hequation]
  simp [LinearMap.mem_ker, sub_eq_zero]

end NCG.VaryingHilbert
