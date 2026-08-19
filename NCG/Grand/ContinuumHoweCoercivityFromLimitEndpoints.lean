/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ContinuumHoweCoercivityCompiler
import NCG.Grand.AutomaticCircleRieszProjectionStability

/-!
# Continuum Howe coercivity from limiting endpoint separation

This is the strongest compact-resolvent Howe compiler.  Operator-norm convergence and two
limiting real endpoint exclusions automatically provide late-cutoff contour separation, uniform
resolvent bounds, and convergence of the circle Riesz projections.  The remaining inputs are the
model's graph-resolvent equation, protected multiplicity, and positivity of the limiting
complement-compressed gap.
-/

open Complex Filter Set Topology

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Two endpoint exclusions for the limiting symmetric resolvent suffice for eventual exact
graph kernels, convergence of protected projections, uniform coercivity, and absence of soft
modes.  No cutoff contour or Riesz-convergence hypotheses are supplied by the caller. -/
theorem continuumHowe_kernel_and_derivedCompressedResolventCoercivity_of_limit_endpoints
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
    (hstarQlim : IsStarProjection
      (NCG.ResolventStability.circleRieszProjection Tlim (center : ℂ) radius))
    (hTnorm : Tendsto T atTop (𝓝 Tlim))
    (hne : ‖NCG.SpectralGap.complementCompression Tlim
      (NCG.ResolventStability.circleRieszProjection Tlim (center : ℂ) radius)‖ ≠ 0)
    (energy residual : ℕ → E → ℝ)
    (hresidual : ∀ n x, 0 ≤ residual n x)
    (hcoercive : ∀ n x,
      (‖NCG.SpectralGap.complementCompression (T n) (P n)‖⁻¹ - lam) * residual n x ≤
        energy n x)
    (hgapPos : 0 < ‖NCG.SpectralGap.complementCompression Tlim
      (NCG.ResolventStability.circleRieszProjection Tlim (center : ℂ) radius)‖⁻¹ - lam) :
    (∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap = operatorGraphKernel (D n) (A n)) ∧
      0 < (‖NCG.SpectralGap.complementCompression Tlim
        (NCG.ResolventStability.circleRieszProjection Tlim (center : ℂ) radius)‖⁻¹ - lam) / 2 ∧
      (∀ᶠ n in atTop, ∀ x,
        (‖NCG.SpectralGap.complementCompression Tlim
          (NCG.ResolventStability.circleRieszProjection Tlim (center : ℂ) radius)‖⁻¹ - lam) /
            2 * residual n x ≤ energy n x) ∧
      ∀ xseq : ℕ → E,
        Tendsto (fun n ↦ energy n (xseq n)) atTop (𝓝 0) →
          Tendsto (fun n ↦ residual n (xseq n)) atTop (𝓝 0) := by
  have hR : 0 < radius := dist_nonneg.trans_lt hinside
  have hlimitContour : ∀ z ∈ Metric.sphere (center : ℂ) radius,
      z ∈ resolventSet ℂ Tlim :=
    NCG.ResolventStability.circle_subset_resolventSet_of_isSymmetric_of_endpoints
      Tlim hlimSymmetric center radius hleft hright
  obtain ⟨M, hM, hlimitBound⟩ :=
    NCG.ResolventStability.exists_circle_resolvent_norm_bound
      Tlim (center : ℂ) radius hlimitContour
  obtain ⟨N, hN, hstage⟩ :=
    NCG.ResolventStability.eventually_circle_resolvent_bound_of_tendsto
      T Tlim hTnorm (center : ℂ) radius M hM hlimitContour hlimitBound
  have hcontour : ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere (center : ℂ) radius,
      z ∈ resolventSet ℂ (T n) := hstage.mono fun n hn z hz ↦ (hn z hz).1
  have hRieszTendsto :=
    NCG.ResolventStability.circleRieszProjection_tendsto_of_tendsto_of_circle_subset_resolventSet
      T Tlim hTnorm (center : ℂ) radius hR.le hlimitContour
  exact continuumHowe_kernel_and_derivedCompressedResolventCoercivity
    D A lam hlam T P hequation hcompact hsymmetric (center : ℂ) radius hzero hinside
      hcontour
      (NCG.ResolventStability.circleRieszProjection Tlim (center : ℂ) radius) Tlim
      hRieszTendsto hprotected hprotectedRank hstarP hstarQlim hTnorm hne
      energy residual hresidual hcoercive hgapPos

end NCG.VaryingHilbert
