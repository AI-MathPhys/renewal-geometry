/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ContinuumHoweCoercivityFromLimitEndpoints
import NCG.Grand.CompactPositiveCircleRieszGap
import NCG.Grand.OperatorGraphResolventBound
import NCG.Grand.OperatorGraphResolventPositivity
import NCG.Grand.PositiveOperatorNormLimits

/-!
# Continuum Howe coercivity from a nonzero limiting complement

For positive-shift graph resolvents, positivity and the sharp `λ⁻¹` operator-norm bound pass
to the norm limit.  Compact positivity then makes the limiting complement gap strictly positive
as soon as the complement compression is nonzero.  This removes the numerical positive-gap
hypothesis from the endpoint Howe compiler.
-/

open Complex Filter Set Topology

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Norm-convergent compact graph resolvents have a positive limiting inverse-norm gap whenever
the Riesz complement compression is nonzero and the circle contains `λ⁻¹`. -/
theorem limit_circleRieszProjection_inverseNormGap_pos_of_graphResolvents
    (D : ℕ → Submodule ℂ E) (A : ∀ n, D n →ₗ[ℂ] F)
    (lam : ℝ) (hlam : 0 < lam) (T : ℕ → E →L[ℂ] E)
    (hequation : ∀ n f, OperatorGraphResolventEquation (D n) (A n) lam f (T n f))
    (hcompact : ∀ n, IsCompactOperator (T n))
    (Tlim : E →L[ℂ] E) (hlimSymmetric : LinearMap.IsSymmetric Tlim.toLinearMap)
    (center radius : ℝ)
    (hinside : (((lam : ℝ) : ℂ)⁻¹) ∈ Metric.ball (center : ℂ) radius)
    (hleft : ((center - radius : ℝ) : ℂ) ∈ resolventSet ℂ Tlim)
    (hright : ((center + radius : ℝ) : ℂ) ∈ resolventSet ℂ Tlim)
    (hTnorm : Tendsto T atTop (nhds Tlim))
    (hne : NCG.SpectralGap.complementCompression Tlim
      (NCG.ResolventStability.circleRieszProjection Tlim (center : ℂ) radius) ≠ 0) :
    0 < ‖NCG.SpectralGap.complementCompression Tlim
      (NCG.ResolventStability.circleRieszProjection Tlim (center : ℂ) radius)‖⁻¹ - lam := by
  have hlimCompact : IsCompactOperator Tlim :=
    isCompactOperator_of_tendsto hTnorm (Filter.Eventually.of_forall hcompact)
  have hstagePositive : ∀ᶠ n in atTop, (T n).IsPositive :=
    Filter.Eventually.of_forall fun n ↦
      operatorGraphResolvent_isPositive (D n) (A n) lam hlam.le (T n) (hequation n)
  have hlimPositive : Tlim.IsPositive :=
    NCG.OperatorLimits.isPositive_of_tendsto_of_isSymmetric
      T Tlim hTnorm hlimSymmetric hstagePositive
  have hstageNorm : ∀ᶠ n in atTop, ‖T n‖ ≤ lam⁻¹ :=
    Filter.Eventually.of_forall fun n ↦ by
      simpa [one_div] using
        operatorGraphResolvent_opNorm_le_inv (D n) (A n) (T n) lam hlam (hequation n)
  have hlimNorm : ‖Tlim‖ ≤ lam⁻¹ :=
    NCG.OperatorLimits.norm_le_of_tendsto T Tlim hTnorm lam⁻¹ hstageNorm
  have hR : 0 < radius := dist_nonneg.trans_lt hinside
  have hlimitContour : ∀ z ∈ Metric.sphere (center : ℂ) radius,
      z ∈ resolventSet ℂ Tlim :=
    NCG.ResolventStability.circle_subset_resolventSet_of_isSymmetric_of_endpoints
      Tlim hlimSymmetric center radius hleft hright
  exact NCG.SpectralGap.inverseNormGap_circleRieszProjection_pos
    Tlim hlimCompact hlimPositive (center : ℂ) radius hR hlimitContour
      lam hlam hinside hlimNorm hne

/-- Endpoint Howe compiler with an automatically derived positive limiting gap.  The caller only
asserts that the limiting Riesz complement compression is nonzero. -/
theorem continuumHowe_kernel_and_coercivity_of_limit_endpoints_of_nonzero_complement
    (D : ℕ → Submodule ℂ E) (A : ∀ n, D n →ₗ[ℂ] F)
    (lam : ℝ) (hlam : 0 < lam) (T P : ℕ → E →L[ℂ] E)
    (hequation : ∀ n f, OperatorGraphResolventEquation (D n) (A n) lam f (T n f))
    (hcompact : ∀ n, IsCompactOperator (T n))
    (hsymmetric : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap)
    (Tlim : E →L[ℂ] E) (hlimSymmetric : LinearMap.IsSymmetric Tlim.toLinearMap)
    (center radius : ℝ)
    (hzero : (0 : ℂ) ∉ Metric.closedBall (center : ℂ) radius)
    (hinside : (((lam : ℝ) : ℂ)⁻¹) ∈ Metric.ball (center : ℂ) radius)
    (hleft : ((center - radius : ℝ) : ℂ) ∈ resolventSet ℂ Tlim)
    (hright : ((center + radius : ℝ) : ℂ) ∈ resolventSet ℂ Tlim)
    (hprotected : ∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap ≤ operatorGraphKernel (D n) (A n))
    (hprotectedRank : ∀ n,
      Module.finrank ℂ (LinearMap.range (P n).toLinearMap) =
        Module.finrank ℂ (LinearMap.range
          (NCG.ResolventStability.circleRieszProjection
            Tlim (center : ℂ) radius).toLinearMap))
    (hstarP : ∀ᶠ n in atTop, IsStarProjection (P n))
    (hTnorm : Tendsto T atTop (nhds Tlim))
    (hne : NCG.SpectralGap.complementCompression Tlim
      (NCG.ResolventStability.circleRieszProjection Tlim (center : ℂ) radius) ≠ 0)
    (energy residual : ℕ → E → ℝ)
    (hresidual : ∀ n x, 0 ≤ residual n x)
    (hcoercive : ∀ n x,
      (‖NCG.SpectralGap.complementCompression (T n) (P n)‖⁻¹ - lam) * residual n x ≤
        energy n x) :
    (∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap = operatorGraphKernel (D n) (A n)) ∧
      0 < (‖NCG.SpectralGap.complementCompression Tlim
        (NCG.ResolventStability.circleRieszProjection Tlim (center : ℂ) radius)‖⁻¹ - lam) / 2 ∧
      (∀ᶠ n in atTop, ∀ x,
        (‖NCG.SpectralGap.complementCompression Tlim
          (NCG.ResolventStability.circleRieszProjection Tlim (center : ℂ) radius)‖⁻¹ - lam) /
            2 * residual n x ≤ energy n x) ∧
      ∀ xseq : ℕ → E,
        Tendsto (fun n ↦ energy n (xseq n)) atTop (nhds 0) →
          Tendsto (fun n ↦ residual n (xseq n)) atTop (nhds 0) := by
  have hgapPos := limit_circleRieszProjection_inverseNormGap_pos_of_graphResolvents
    D A lam hlam T hequation hcompact Tlim hlimSymmetric center radius
      hinside hleft hright hTnorm hne
  exact continuumHowe_kernel_and_coercivity_of_limit_endpoints
    D A lam hlam T P hequation hcompact hsymmetric Tlim hlimSymmetric center radius
      hzero hinside hleft hright hprotected hprotectedRank hstarP hTnorm
      energy residual hresidual hcoercive hgapPos

/-- Strongest endpoint Howe compiler for an infinite-dimensional limit space: injectivity of the
limit resolvent automatically makes the Riesz complement compression nonzero, so no gap or
nonvanishing premise is supplied by the caller. -/
theorem continuumHowe_kernel_and_coercivity_of_injective_limit_endpoints
    (D : ℕ → Submodule ℂ E) (A : ∀ n, D n →ₗ[ℂ] F)
    (lam : ℝ) (hlam : 0 < lam) (T P : ℕ → E →L[ℂ] E)
    (hequation : ∀ n f, OperatorGraphResolventEquation (D n) (A n) lam f (T n f))
    (hcompact : ∀ n, IsCompactOperator (T n))
    (hsymmetric : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap)
    (Tlim : E →L[ℂ] E) (hlimSymmetric : LinearMap.IsSymmetric Tlim.toLinearMap)
    (hlimInjective : Function.Injective Tlim) (hinfinite : ¬FiniteDimensional ℂ E)
    (center radius : ℝ)
    (hzero : (0 : ℂ) ∉ Metric.closedBall (center : ℂ) radius)
    (hinside : (((lam : ℝ) : ℂ)⁻¹) ∈ Metric.ball (center : ℂ) radius)
    (hleft : ((center - radius : ℝ) : ℂ) ∈ resolventSet ℂ Tlim)
    (hright : ((center + radius : ℝ) : ℂ) ∈ resolventSet ℂ Tlim)
    (hprotected : ∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap ≤ operatorGraphKernel (D n) (A n))
    (hprotectedRank : ∀ n,
      Module.finrank ℂ (LinearMap.range (P n).toLinearMap) =
        Module.finrank ℂ (LinearMap.range
          (NCG.ResolventStability.circleRieszProjection
            Tlim (center : ℂ) radius).toLinearMap))
    (hstarP : ∀ᶠ n in atTop, IsStarProjection (P n))
    (hTnorm : Tendsto T atTop (nhds Tlim))
    (energy residual : ℕ → E → ℝ)
    (hresidual : ∀ n x, 0 ≤ residual n x)
    (hcoercive : ∀ n x,
      (‖NCG.SpectralGap.complementCompression (T n) (P n)‖⁻¹ - lam) * residual n x ≤
        energy n x) :
    (∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap = operatorGraphKernel (D n) (A n)) ∧
      0 < (‖NCG.SpectralGap.complementCompression Tlim
        (NCG.ResolventStability.circleRieszProjection Tlim (center : ℂ) radius)‖⁻¹ - lam) / 2 ∧
      (∀ᶠ n in atTop, ∀ x,
        (‖NCG.SpectralGap.complementCompression Tlim
          (NCG.ResolventStability.circleRieszProjection Tlim (center : ℂ) radius)‖⁻¹ - lam) /
            2 * residual n x ≤ energy n x) ∧
      ∀ xseq : ℕ → E,
        Tendsto (fun n ↦ energy n (xseq n)) atTop (nhds 0) →
          Tendsto (fun n ↦ residual n (xseq n)) atTop (nhds 0) := by
  have hlimCompact : IsCompactOperator Tlim :=
    isCompactOperator_of_tendsto hTnorm (Filter.Eventually.of_forall hcompact)
  have hR : 0 < radius := dist_nonneg.trans_lt hinside
  have hlimitContour : ∀ z ∈ Metric.sphere (center : ℂ) radius,
      z ∈ resolventSet ℂ Tlim :=
    NCG.ResolventStability.circle_subset_resolventSet_of_isSymmetric_of_endpoints
      Tlim hlimSymmetric center radius hleft hright
  have hne : NCG.SpectralGap.complementCompression Tlim
      (NCG.ResolventStability.circleRieszProjection
        Tlim (center : ℂ) radius) ≠ 0 :=
    NCG.SpectralGap.circleRieszProjection_complementCompression_ne_zero_of_injective
      Tlim hlimCompact hlimSymmetric hlimInjective (center : ℂ) radius hR
        hzero hlimitContour hinfinite
  exact continuumHowe_kernel_and_coercivity_of_limit_endpoints_of_nonzero_complement
    D A lam hlam T P hequation hcompact hsymmetric Tlim hlimSymmetric center radius
      hzero hinside hleft hright hprotected hprotectedRank hstarP hTnorm hne
      energy residual hresidual hcoercive

end NCG.VaryingHilbert
