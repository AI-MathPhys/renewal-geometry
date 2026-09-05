/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CircleRieszProjectionIdempotence
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Compact circle Riesz projections

When the contour disc avoids zero, the resolvent identity factors the circle Riesz operator
through the underlying operator.  It is therefore compact whenever that operator is compact.
An idempotent compact operator has finite-dimensional range, eliminating the separate
finite-range premise from compact self-adjoint spectral stability.
-/

open Complex Set

noncomputable section

namespace NCG.ResolventStability

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A circle integral commutes with multiplication by a fixed element on the right. -/
theorem circleIntegral_mul_const
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (f : ℂ → A) (a : A) (center : ℂ) (radius : ℝ)
    (hf : CircleIntegrable f center radius) :
    (∮ z in C(center, radius), f z * a) =
      (∮ z in C(center, radius), f z) * a := by
  unfold circleIntegral
  simp only [← smul_mul_assoc]
  change
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      ((ContinuousLinearMap.mul ℂ A).flip a)
        (deriv (circleMap center radius) θ • f (circleMap center radius θ))) =
      ((ContinuousLinearMap.mul ℂ A).flip a)
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          deriv (circleMap center radius) θ • f (circleMap center radius θ))
  exact ContinuousLinearMap.intervalIntegral_comp_comm
    ((ContinuousLinearMap.mul ℂ A).flip a) hf.out

/-- The bounded factor through which a zero-avoiding circle Riesz operator factors. -/
def circleRieszCompactFactor
    (T : E →L[ℂ] E) (center : ℂ) (radius : ℝ) : E →L[ℂ] E :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    ∮ z in C(center, radius), z⁻¹ • resolvent T z

/-- If zero lies outside the closed contour disc, the circle Riesz operator factors through the
underlying operator. -/
theorem circleRieszProjection_eq_compactFactor_mul
    (T : E →L[ℂ] E) (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hzero : (0 : ℂ) ∉ Metric.closedBall center radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    circleRieszProjection T center radius =
      circleRieszCompactFactor T center radius * T := by
  have hzeroBall : (0 : ℂ) ∉ Metric.ball center radius := by
    intro hz
    exact hzero (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hz).le)
  have hzeroSphere : (0 : ℂ) ∉ Metric.sphere center radius := by
    intro hz
    exact hzero (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hz).le)
  have hzNe : ∀ z ∈ Metric.sphere center radius, z ≠ 0 := by
    intro z hz hzeq
    exact hzeroSphere (hzeq ▸ hz)
  have hresContinuous :
      ContinuousOn (resolvent T) (Metric.sphere center radius) := by
    intro z hz
    exact (spectrum.hasDerivAt_resolvent_const_left
      (hcontour z hz)).continuousAt.continuousWithinAt
  have hinvContinuous :
      ContinuousOn (fun z : ℂ ↦ z⁻¹) (Metric.sphere center radius) := by
    exact continuousOn_id.inv₀ hzNe
  have hweightedContinuous :
      ContinuousOn (fun z ↦ z⁻¹ • resolvent T z) (Metric.sphere center radius) :=
    hinvContinuous.smul hresContinuous
  have hweightedMulIntegrable : CircleIntegrable
      (fun z ↦ (z⁻¹ • resolvent T z) * T) center radius :=
    (hweightedContinuous.mul continuousOn_const).circleIntegrable hR.le
  have hweightedIntegrable : CircleIntegrable
      (fun z ↦ z⁻¹ • resolvent T z) center radius :=
    hweightedContinuous.circleIntegrable hR.le
  have hscalarOneIntegrable : CircleIntegrable
      (fun z : ℂ ↦ z⁻¹ • (1 : E →L[ℂ] E)) center radius :=
    (hinvContinuous.smul continuousOn_const).circleIntegrable hR.le
  have hpoint : Set.EqOn (resolvent T)
      (fun z ↦ (z⁻¹ • resolvent T z) * T +
        z⁻¹ • (1 : E →L[ℂ] E))
      (Metric.sphere center radius) := by
    intro z hz
    have hz0 := hzNe z hz
    have hinv :
        resolvent T z * (algebraMap ℂ (E →L[ℂ] E) z - T) = 1 := by
      rw [spectrum.resolvent_eq (hcontour z hz)]
      exact (hcontour z hz).unit.inv_mul
    have hshift : z • resolvent T z - resolvent T z * T = 1 := by
      rw [← hinv]
      simp [Algebra.algebraMap_eq_smul_one, mul_sub]
    have hsum : z • resolvent T z = 1 + resolvent T z * T :=
      eq_add_of_sub_eq hshift
    calc
      resolvent T z = (1 : ℂ) • resolvent T z := by simp
      _ = (z⁻¹ * z) • resolvent T z := by rw [inv_mul_cancel₀ hz0]
      _ = z⁻¹ • (z • resolvent T z) := by rw [smul_smul]
      _ = z⁻¹ • (1 + resolvent T z * T) := by rw [hsum]
      _ = (z⁻¹ • resolvent T z) * T +
          z⁻¹ • (1 : E →L[ℂ] E) := by
        rw [smul_add, smul_mul_assoc]
        abel
  rw [circleRieszProjection, circleRieszCompactFactor]
  rw [circleIntegral.integral_congr hR.le hpoint]
  rw [circleIntegral.integral_add hweightedMulIntegrable hscalarOneIntegrable]
  rw [circleIntegral_mul_const _ _ _ _ hweightedIntegrable]
  rw [circleIntegral.integral_smul_const]
  have hscalar : (∮ z in C(center, radius), z⁻¹) = 0 := by
    simpa using circleIntegral_sub_inv_eq_zero_of_not_mem_ball
      center 0 radius hR hzeroBall hzeroSphere
  rw [hscalar]
  simp only [zero_smul, add_zero, smul_mul_assoc]

/-- A zero-avoiding circle Riesz operator of a compact operator is compact. -/
theorem circleRieszProjection_isCompactOperator
    (T : E →L[ℂ] E) (hcompact : IsCompactOperator T)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hzero : (0 : ℂ) ∉ Metric.closedBall center radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    IsCompactOperator ((circleRieszProjection T center radius : E →L[ℂ] E) : E → E) := by
  let B := circleRieszCompactFactor T center radius
  have hBT := hcompact.clm_comp B
  have heqfun :
      ((circleRieszProjection T center radius : E →L[ℂ] E) : E → E) =
        fun x ↦ B (T x) := by
    funext x
    have heq := congrArg (fun S : E →L[ℂ] E ↦ S x)
      (circleRieszProjection_eq_compactFactor_mul
        T center radius hR hzero hcontour)
    change (circleRieszProjection T center radius : E →L[ℂ] E) x = B (T x) at heq
    exact heq
  exact heqfun.symm ▸ hBT

/-- The range of a compact idempotent bounded operator is finite-dimensional. -/
theorem finiteDimensional_range_of_compact_idempotent
    (P : E →L[ℂ] E)
    (hcompact : IsCompactOperator (P : E → E))
    (hidem : IsIdempotentElem P) :
    FiniteDimensional ℂ (LinearMap.range P.toLinearMap) := by
  let R := LinearMap.range P.toLinearMap
  have hidemLinear : IsIdempotentElem P.toLinearMap :=
    ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr hidem
  have hclosed : IsClosed (R : Set E) :=
    ContinuousLinearMap.IsIdempotentElem.isClosed_range hidem
  letI : CompleteSpace R := hclosed.completeSpace_coe
  have hpres : ∀ x ∈ R, P.toLinearMap x ∈ R := by
    intro x _
    exact LinearMap.mem_range_self P.toLinearMap x
  have hcompactLinear : IsCompactOperator P.toLinearMap := hcompact
  have hrestrict :
      IsCompactOperator (P.toLinearMap.restrict hpres) :=
    hcompactLinear.restrict' hpres
  have hrestrictEq :
      P.toLinearMap.restrict hpres = LinearMap.id := by
    ext x
    change P x = (x : E)
    exact LinearMap.IsIdempotentElem.mem_range_iff hidemLinear |>.mp x.property
  have hidCompact : IsCompactOperator (id : R → R) := by
    have heqfun :
        ((P.toLinearMap.restrict hpres : R →ₗ[ℂ] R) : R → R) = id := by
      funext x
      exact DFunLike.congr_fun hrestrictEq x
    exact heqfun ▸ hrestrict
  exact FiniteDimensional.of_isCompactOperator_id hidCompact

/-- A zero-avoiding circle Riesz projection of a compact self-adjoint operator has
finite-dimensional range. -/
theorem finiteDimensional_range_circleRieszProjection_of_compact_of_isSymmetric
    (T : E →L[ℂ] E) (hcompact : IsCompactOperator (T : E → E))
    (hsymmetric : LinearMap.IsSymmetric T.toLinearMap)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hzero : (0 : ℂ) ∉ Metric.closedBall center radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    FiniteDimensional ℂ
      (LinearMap.range
        (circleRieszProjection T center radius : E →L[ℂ] E).toLinearMap) := by
  apply finiteDimensional_range_of_compact_idempotent
  · exact circleRieszProjection_isCompactOperator
      T hcompact center radius hR hzero hcontour
  · exact ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mp
      (circleRieszProjection_isIdempotentElem_of_compact_of_isSymmetric
        T hcompact hsymmetric center radius hR hcontour)

end NCG.ResolventStability
