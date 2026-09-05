/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RieszProjectionStability
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Circle Riesz projections on eigenvectors

The circle Riesz operator fixes every eigenvector whose eigenvalue is strictly inside the
contour.  The proof evaluates the resolvent on an eigenvector and then applies the elementary
circle residue formula.  This is the inside-eigenspace inclusion needed in the spectral range
identification for compact-screen limits.
-/

open Complex Set

noncomputable section

namespace NCG.ResolventStability

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Evaluation by a vector commutes with a circle integral of continuous linear maps. -/
theorem circleIntegral_apply
    (f : ℂ → E →L[ℂ] E) (c : ℂ) (R : ℝ) (x : E)
    (hf : CircleIntegrable f c R) :
    (∮ z in C(c, R), f z) x = ∮ z in C(c, R), f z x := by
  unfold circleIntegral
  rw [ContinuousLinearMap.intervalIntegral_apply hf.out]
  rfl

/-- The scalar resolvent has zero circle integral when its pole lies strictly outside the closed
contour disc. -/
theorem circleIntegral_sub_inv_eq_zero_of_not_mem_ball
    (center μ : ℂ) (radius : ℝ) (hR : 0 < radius)
    (hball : μ ∉ Metric.ball center radius)
    (hsphere : μ ∉ Metric.sphere center radius) :
    (∮ z in C(center, radius), (z - μ)⁻¹) = 0 := by
  have hout : ∀ w ∈ Metric.closedBall center radius, w ≠ μ := by
    intro w hw hwm
    rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hw) with h | h
    · exact hball (hwm ▸ Metric.mem_ball.mpr h)
    · exact hsphere (hwm ▸ Metric.mem_sphere.mpr h)
  have hdiff : DifferentiableOn ℂ
      (fun z : ℂ ↦ (z - μ)⁻¹) (Metric.closedBall center radius) := by
    apply DifferentiableOn.inv
    · exact (differentiable_id.sub (differentiable_const μ)).differentiableOn
    · intro w hw
      exact sub_ne_zero.mpr (hout w hw)
  exact DiffContOnCl.circleIntegral_eq_zero hR.le
    (hdiff.diffContOnCl_ball (le_refl (Metric.closedBall center radius)))

/-- At a resolvent point, the resolvent acts on a `μ`-eigenvector by the scalar
`(z - μ)⁻¹`. -/
theorem resolvent_apply_eigenvector
    (T : E →L[ℂ] E) (z μ : ℂ) (x : E)
    (hz : z ∈ resolventSet ℂ T) (hx : T x = μ • x) :
    resolvent T z x = (z - μ)⁻¹ • x := by
  by_cases hzero : x = 0
  · simp [hzero]
  have hzmu : z - μ ≠ 0 := by
    intro h
    have hzm : z = μ := sub_eq_zero.mp h
    have hnotunit : ¬IsUnit (algebraMap ℂ (E →L[ℂ] E) z - T) := by
      intro hu
      have hkill : (algebraMap ℂ (E →L[ℂ] E) z - T) x = 0 := by
        simp [hzm, hx]
      have hunitkill : (↑hu.unit : E →L[ℂ] E) x = 0 := by
        simpa using hkill
      apply hzero
      calc
        x = ((↑hu.unit⁻¹ : E →L[ℂ] E) * (↑hu.unit : E →L[ℂ] E)) x := by
          rw [hu.unit.inv_mul]
          rfl
        _ = (↑hu.unit⁻¹ : E →L[ℂ] E) ((↑hu.unit : E →L[ℂ] E) x) := rfl
        _ = 0 := by rw [hunitkill]; simp
    exact hnotunit hz
  let y : E := (z - μ)⁻¹ • x
  have hshift : (algebraMap ℂ (E →L[ℂ] E) z - T) y = x := by
    simp only [y, sub_apply, ContinuousLinearMap.algebraMap_apply, map_smul, hx]
    rw [← sub_smul, smul_smul, inv_mul_cancel₀ hzmu, one_smul]
  have hinv :
      resolvent T z * (algebraMap ℂ (E →L[ℂ] E) z - T) = 1 := by
    rw [spectrum.resolvent_eq hz]
    exact hz.unit.inv_mul
  calc
    resolvent T z x = resolvent T z
        ((algebraMap ℂ (E →L[ℂ] E) z - T) y) := by rw [hshift]
    _ = (resolvent T z *
        (algebraMap ℂ (E →L[ℂ] E) z - T)) y := by rfl
    _ = y := by rw [hinv]; rfl
    _ = (z - μ)⁻¹ • x := rfl

/-- A circle Riesz operator fixes every eigenvector whose eigenvalue is inside the circle. -/
theorem circleRieszProjection_apply_eigenvector_of_mem_ball
    [CompleteSpace E]
    (T : E →L[ℂ] E) (center μ : ℂ) (radius : ℝ) (x : E)
    (hμ : μ ∈ Metric.ball center radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T)
    (hx : T x = μ • x) :
    circleRieszProjection T center radius x = x := by
  have hR : 0 < radius := dist_nonneg.trans_lt hμ
  have hcontinuous :
      ContinuousOn (resolvent T) (Metric.sphere center radius) := by
    intro z hz
    exact (spectrum.hasDerivAt_resolvent_const_left
      (hcontour z hz)).continuousAt.continuousWithinAt
  have hint : CircleIntegrable (resolvent T) center radius :=
    hcontinuous.circleIntegrable hR.le
  rw [circleRieszProjection]
  change (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    ((∮ z in C(center, radius), resolvent T z) x) = x
  rw [circleIntegral_apply (resolvent T) center radius x hint]
  have hcircle :
      (∮ z in C(center, radius), resolvent T z x) =
        ∮ z in C(center, radius), (z - μ)⁻¹ • x :=
    circleIntegral.integral_congr hR.le fun z hz ↦
      resolvent_apply_eigenvector T z μ x (hcontour z hz) hx
  rw [hcircle, circleIntegral.integral_smul_const,
    circleIntegral.integral_sub_inv_of_mem_ball hμ, smul_smul]
  have hnonzero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  rw [inv_mul_cancel₀ hnonzero, one_smul]

/-- A circle Riesz operator kills every eigenvector whose eigenvalue lies strictly outside the
closed contour disc. -/
theorem circleRieszProjection_apply_eigenvector_of_not_mem_closedBall
    [CompleteSpace E]
    (T : E →L[ℂ] E) (center μ : ℂ) (radius : ℝ) (x : E)
    (hR : 0 < radius) (houtside : μ ∉ Metric.closedBall center radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T)
    (hx : T x = μ • x) :
    circleRieszProjection T center radius x = 0 := by
  have hball : μ ∉ Metric.ball center radius := by
    intro hμ
    exact houtside (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hμ).le)
  have hsphere : μ ∉ Metric.sphere center radius := by
    intro hμ
    exact houtside (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hμ).le)
  have hcontinuous :
      ContinuousOn (resolvent T) (Metric.sphere center radius) := by
    intro z hz
    exact (spectrum.hasDerivAt_resolvent_const_left
      (hcontour z hz)).continuousAt.continuousWithinAt
  have hint : CircleIntegrable (resolvent T) center radius :=
    hcontinuous.circleIntegrable hR.le
  rw [circleRieszProjection]
  change (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    ((∮ z in C(center, radius), resolvent T z) x) = 0
  rw [circleIntegral_apply (resolvent T) center radius x hint]
  have hcircle :
      (∮ z in C(center, radius), resolvent T z x) =
        ∮ z in C(center, radius), (z - μ)⁻¹ • x :=
    circleIntegral.integral_congr hR.le fun z hz ↦
      resolvent_apply_eigenvector T z μ x (hcontour z hz) hx
  rw [hcircle, circleIntegral.integral_smul_const,
    circleIntegral_sub_inv_eq_zero_of_not_mem_ball
      center μ radius hR hball hsphere, zero_smul, smul_zero]

/-- The eigenspace of every eigenvalue inside the contour is contained in the range of the
circle Riesz operator. -/
theorem eigenspace_le_range_circleRieszProjection_of_mem_ball
    [CompleteSpace E]
    (T : E →L[ℂ] E) (center μ : ℂ) (radius : ℝ)
    (hμ : μ ∈ Metric.ball center radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) :
    Module.End.eigenspace T.toLinearMap μ ≤
      LinearMap.range (circleRieszProjection T center radius).toLinearMap := by
  intro x hx
  refine ⟨x, ?_⟩
  exact circleRieszProjection_apply_eigenvector_of_mem_ball
    T center μ radius x hμ hcontour (Module.End.mem_eigenspace_iff.mp hx)


/-- If the contour operator has the expected finite multiplicity, the inside-eigenspace
inclusion already identifies its whole range.  This turns the multiplicity conclusion of a
compact-screen argument into the exact Riesz-range statement without a separate outside-contour
calculation. -/
theorem range_circleRieszProjection_eq_eigenspace_of_finrank_eq
    [CompleteSpace E]
    (T : E →L[ℂ] E) (center μ : ℂ) (radius : ℝ)
    (hμ : μ ∈ Metric.ball center radius)
    (hcontour : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T)
    [Module.Finite ℂ
      (LinearMap.range (circleRieszProjection T center radius).toLinearMap)]
    (hrank :
      Module.finrank ℂ (LinearMap.range
        (circleRieszProjection T center radius).toLinearMap) =
      Module.finrank ℂ (Module.End.eigenspace T.toLinearMap μ)) :
    LinearMap.range (circleRieszProjection T center radius).toLinearMap =
      Module.End.eigenspace T.toLinearMap μ := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
    (eigenspace_le_range_circleRieszProjection_of_mem_ball
      T center μ radius hμ hcontour)
  exact hrank.symm
end NCG.ResolventStability
