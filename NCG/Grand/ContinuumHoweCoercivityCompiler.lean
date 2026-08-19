/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ProtectedGraphKernelRigidityFromCompactResolvents
import NCG.Grand.ConvergentSpectralGapCoercivity
import NCG.Grand.ComplementCompressedResolventGap
import NCG.Grand.SelfAdjointContourSeparation
import NCG.Grand.AutomaticCircleRieszProjectionStability

/-!
# Coercive continuum Howe compiler

This theorem assembles the two analytic conclusions of the continuum Howe argument.  Convergent
compact Riesz operators lock the protected spaces to the cutoff graph kernels, while
convergence of the first positive spectral value to a positive limit supplies one explicit
uniform coercivity constant.
-/

open Filter Topology Complex Set

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Riesz norm convergence, protected multiplicity, and a positive limiting gap jointly give
eventual exact kernels, uniform coercivity, and the no-soft-mode consequence. -/
theorem continuumHowe_kernel_and_uniformCoercivity
    (D : ℕ → Submodule ℂ E) (A : ∀ n, D n →ₗ[ℂ] F)
    (lam : ℝ) (hlam : 0 < lam) (T P : ℕ → E →L[ℂ] E)
    (hequation : ∀ n f, OperatorGraphResolventEquation (D n) (A n) lam f (T n f))
    (hcompact : ∀ n, IsCompactOperator (T n))
    (hsymmetric : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap)
    (center : ℂ) (radius : ℝ)
    (hzero : (0 : ℂ) ∉ Metric.closedBall center radius)
    (hinside : (((lam : ℝ) : ℂ)⁻¹) ∈ Metric.ball center radius)
    (hcontour : ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ (T n))
    (Qlim : E →L[ℂ] E)
    (hRieszTendsto : Tendsto
      (fun n ↦ NCG.ResolventStability.circleRieszProjection (T n) center radius)
      atTop (nhds Qlim))
    (hprotected : ∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap ≤ operatorGraphKernel (D n) (A n))
    (hprotectedRank : ∀ n,
      Module.finrank ℂ (LinearMap.range (P n).toLinearMap) =
        Module.finrank ℂ (LinearMap.range Qlim.toLinearMap))
    (energy residual : ℕ → E → ℝ) (gap : ℕ → ℝ) (gaplim : ℝ)
    (hresidual : ∀ n x, 0 ≤ residual n x)
    (hcoercive : ∀ n x, gap n * residual n x ≤ energy n x)
    (hgap : Tendsto gap atTop (nhds gaplim)) (hgapPos : 0 < gaplim) :
    (∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap = operatorGraphKernel (D n) (A n)) ∧
      0 < gaplim / 2 ∧
      (∀ᶠ n in atTop, ∀ x, gaplim / 2 * residual n x ≤ energy n x) ∧
      ∀ xseq : ℕ → E,
        Tendsto (fun n ↦ energy n (xseq n)) atTop (nhds 0) →
          Tendsto (fun n ↦ residual n (xseq n)) atTop (nhds 0) := by
  have hR : 0 < radius := dist_nonneg.trans_lt hinside
  refine ⟨eventually_range_protected_eq_operatorGraphKernel_of_compact_riesz_tendsto
    D A lam hlam T P hequation hcompact hsymmetric center radius hR hzero
      hinside hcontour Qlim hRieszTendsto hprotected hprotectedRank, ?_⟩
  obtain ⟨hhalf, huniform⟩ :=
    NCG.SpectralGap.eventually_uniform_coercivity_of_gap_tendsto
    energy residual gap gaplim hresidual hcoercive hgap hgapPos
  refine ⟨hhalf, huniform, ?_⟩
  intro xseq henergy
  exact NCG.SpectralGap.residual_tendsto_zero_of_gap_tendsto
    energy residual xseq gap gaplim hresidual hcoercive hgap hgapPos henergy


/-- A stronger compiler in which the cutoff gaps are not supplied independently. They are
read from the norms of the resolvents compressed to the protected complements, so norm
convergence of the resolvents and protected projections supplies gap convergence automatically. -/
theorem continuumHowe_kernel_and_compressedResolventCoercivity
    (D : ℕ → Submodule ℂ E) (A : ∀ n, D n →ₗ[ℂ] F)
    (lam : ℝ) (hlam : 0 < lam) (T P : ℕ → E →L[ℂ] E)
    (hequation : ∀ n f, OperatorGraphResolventEquation (D n) (A n) lam f (T n f))
    (hcompact : ∀ n, IsCompactOperator (T n))
    (hsymmetric : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap)
    (center : ℂ) (radius : ℝ)
    (hzero : (0 : ℂ) ∉ Metric.closedBall center radius)
    (hinside : (((lam : ℝ) : ℂ)⁻¹) ∈ Metric.ball center radius)
    (hcontour : ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ (T n))
    (Qlim Tlim Plim : E →L[ℂ] E)
    (hRieszTendsto : Tendsto
      (fun n ↦ NCG.ResolventStability.circleRieszProjection (T n) center radius)
      atTop (nhds Qlim))
    (hprotected : ∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap ≤ operatorGraphKernel (D n) (A n))
    (hprotectedRank : ∀ n,
      Module.finrank ℂ (LinearMap.range (P n).toLinearMap) =
        Module.finrank ℂ (LinearMap.range Qlim.toLinearMap))
    (hTnorm : Tendsto T atTop (nhds Tlim))
    (hPnorm : Tendsto P atTop (nhds Plim))
    (hne : ‖NCG.SpectralGap.complementCompression Tlim Plim‖ ≠ 0)
    (energy residual : ℕ → E → ℝ)
    (hresidual : ∀ n x, 0 ≤ residual n x)
    (hcoercive : ∀ n x,
      (‖NCG.SpectralGap.complementCompression (T n) (P n)‖⁻¹ - lam) * residual n x ≤
        energy n x)
    (hgapPos : 0 < ‖NCG.SpectralGap.complementCompression Tlim Plim‖⁻¹ - lam) :
    (∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap = operatorGraphKernel (D n) (A n)) ∧
      0 < (‖NCG.SpectralGap.complementCompression Tlim Plim‖⁻¹ - lam) / 2 ∧
      (∀ᶠ n in atTop, ∀ x,
        (‖NCG.SpectralGap.complementCompression Tlim Plim‖⁻¹ - lam) / 2 * residual n x ≤
          energy n x) ∧
      ∀ xseq : ℕ → E,
        Tendsto (fun n ↦ energy n (xseq n)) atTop (nhds 0) →
          Tendsto (fun n ↦ residual n (xseq n)) atTop (nhds 0) := by
  exact continuumHowe_kernel_and_uniformCoercivity
    D A lam hlam T P hequation hcompact hsymmetric center radius hzero hinside hcontour
      Qlim hRieszTendsto hprotected hprotectedRank energy residual
      (fun n ↦ ‖NCG.SpectralGap.complementCompression (T n) (P n)‖⁻¹ - lam)
      (‖NCG.SpectralGap.complementCompression Tlim Plim‖⁻¹ - lam)
      hresidual hcoercive
      (NCG.SpectralGap.inverseNormGap_tendsto T P Tlim Plim lam hTnorm hPnorm hne) hgapPos
/-- Fully derived compressed-resolvent compiler: once the cutoff protected projections and the
limiting Riesz projection are orthogonal, kernel rigidity forces the protected projections to
converge to the Riesz limit. Thus only resolvent norm convergence and positivity of the limiting
compressed gap remain as analytic inputs to the coercivity passage. -/
theorem continuumHowe_kernel_and_derivedCompressedResolventCoercivity
    (D : ℕ → Submodule ℂ E) (A : ∀ n, D n →ₗ[ℂ] F)
    (lam : ℝ) (hlam : 0 < lam) (T P : ℕ → E →L[ℂ] E)
    (hequation : ∀ n f, OperatorGraphResolventEquation (D n) (A n) lam f (T n f))
    (hcompact : ∀ n, IsCompactOperator (T n))
    (hsymmetric : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap)
    (center : ℂ) (radius : ℝ)
    (hzero : (0 : ℂ) ∉ Metric.closedBall center radius)
    (hinside : (((lam : ℝ) : ℂ)⁻¹) ∈ Metric.ball center radius)
    (hcontour : ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ (T n))
    (Qlim Tlim : E →L[ℂ] E)
    (hRieszTendsto : Tendsto
      (fun n ↦ NCG.ResolventStability.circleRieszProjection (T n) center radius)
      atTop (nhds Qlim))
    (hprotected : ∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap ≤ operatorGraphKernel (D n) (A n))
    (hprotectedRank : ∀ n,
      Module.finrank ℂ (LinearMap.range (P n).toLinearMap) =
        Module.finrank ℂ (LinearMap.range Qlim.toLinearMap))
    (hstarP : ∀ᶠ n in atTop, IsStarProjection (P n))
    (hstarQlim : IsStarProjection Qlim)
    (hTnorm : Tendsto T atTop (nhds Tlim))
    (hne : ‖NCG.SpectralGap.complementCompression Tlim Qlim‖ ≠ 0)
    (energy residual : ℕ → E → ℝ)
    (hresidual : ∀ n x, 0 ≤ residual n x)
    (hcoercive : ∀ n x,
      (‖NCG.SpectralGap.complementCompression (T n) (P n)‖⁻¹ - lam) * residual n x ≤
        energy n x)
    (hgapPos : 0 < ‖NCG.SpectralGap.complementCompression Tlim Qlim‖⁻¹ - lam) :
    (∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap = operatorGraphKernel (D n) (A n)) ∧
      0 < (‖NCG.SpectralGap.complementCompression Tlim Qlim‖⁻¹ - lam) / 2 ∧
      (∀ᶠ n in atTop, ∀ x,
        (‖NCG.SpectralGap.complementCompression Tlim Qlim‖⁻¹ - lam) / 2 * residual n x ≤
          energy n x) ∧
      ∀ xseq : ℕ → E,
        Tendsto (fun n ↦ energy n (xseq n)) atTop (nhds 0) →
          Tendsto (fun n ↦ residual n (xseq n)) atTop (nhds 0) := by
  have hR : 0 < radius := dist_nonneg.trans_lt hinside
  have hPnorm : Tendsto P atTop (nhds Qlim) :=
    protectedProjection_tendsto_of_compact_riesz_tendsto
      D A lam hlam T P hequation hcompact hsymmetric center radius hR hzero hinside
        hcontour Qlim hRieszTendsto hprotected hprotectedRank hstarP hstarQlim
  exact continuumHowe_kernel_and_compressedResolventCoercivity
    D A lam hlam T P hequation hcompact hsymmetric center radius hzero hinside hcontour
      Qlim Tlim Qlim hRieszTendsto hprotected hprotectedRank hTnorm hPnorm hne
      energy residual hresidual hcoercive hgapPos
/-- Endpoint-separated form of the strongest compiler. For symmetric resolvents and a
real-centered circle, checking the left and right real endpoints at each cutoff automatically
supplies the entire contour-resolvent hypothesis. -/
theorem continuumHowe_kernel_and_derivedCompressedResolventCoercivity_of_endpoints
    (D : ℕ → Submodule ℂ E) (A : ∀ n, D n →ₗ[ℂ] F)
    (lam : ℝ) (hlam : 0 < lam) (T P : ℕ → E →L[ℂ] E)
    (hequation : ∀ n f, OperatorGraphResolventEquation (D n) (A n) lam f (T n f))
    (hcompact : ∀ n, IsCompactOperator (T n))
    (hsymmetric : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap)
    (center radius : ℝ)
    (hzero : (0 : ℂ) ∉ Metric.closedBall (center : ℂ) radius)
    (hinside : (((lam : ℝ) : ℂ)⁻¹) ∈ Metric.ball (center : ℂ) radius)
    (hleft : ∀ n, ((center - radius : ℝ) : ℂ) ∈ resolventSet ℂ (T n))
    (hright : ∀ n, ((center + radius : ℝ) : ℂ) ∈ resolventSet ℂ (T n))
    (Qlim Tlim : E →L[ℂ] E)
    (hRieszTendsto : Tendsto
      (fun n ↦ NCG.ResolventStability.circleRieszProjection
        (T n) (center : ℂ) radius)
      atTop (nhds Qlim))
    (hprotected : ∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap ≤ operatorGraphKernel (D n) (A n))
    (hprotectedRank : ∀ n,
      Module.finrank ℂ (LinearMap.range (P n).toLinearMap) =
        Module.finrank ℂ (LinearMap.range Qlim.toLinearMap))
    (hstarP : ∀ᶠ n in atTop, IsStarProjection (P n))
    (hstarQlim : IsStarProjection Qlim)
    (hTnorm : Tendsto T atTop (nhds Tlim))
    (hne : ‖NCG.SpectralGap.complementCompression Tlim Qlim‖ ≠ 0)
    (energy residual : ℕ → E → ℝ)
    (hresidual : ∀ n x, 0 ≤ residual n x)
    (hcoercive : ∀ n x,
      (‖NCG.SpectralGap.complementCompression (T n) (P n)‖⁻¹ - lam) * residual n x ≤
        energy n x)
    (hgapPos : 0 < ‖NCG.SpectralGap.complementCompression Tlim Qlim‖⁻¹ - lam) :
    (∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap = operatorGraphKernel (D n) (A n)) ∧
      0 < (‖NCG.SpectralGap.complementCompression Tlim Qlim‖⁻¹ - lam) / 2 ∧
      (∀ᶠ n in atTop, ∀ x,
        (‖NCG.SpectralGap.complementCompression Tlim Qlim‖⁻¹ - lam) / 2 * residual n x ≤
          energy n x) ∧
      ∀ xseq : ℕ → E,
        Tendsto (fun n ↦ energy n (xseq n)) atTop (nhds 0) →
          Tendsto (fun n ↦ residual n (xseq n)) atTop (nhds 0) := by
  have hcontour : ∀ n z,
      z ∈ Metric.sphere (center : ℂ) radius → z ∈ resolventSet ℂ (T n) := by
    intro n
    exact NCG.ResolventStability.circle_subset_resolventSet_of_isSymmetric_of_endpoints
      (T n) (hsymmetric n) center radius (hleft n) (hright n)
  exact continuumHowe_kernel_and_derivedCompressedResolventCoercivity
    D A lam hlam T P hequation hcompact hsymmetric (center : ℂ) radius hzero hinside
      (Filter.Eventually.of_forall hcontour) Qlim Tlim hRieszTendsto hprotected
      hprotectedRank hstarP hstarQlim
      hTnorm hne energy residual hresidual hcoercive hgapPos
end NCG.VaryingHilbert
