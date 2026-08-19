/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ProtectedGraphKernelRigidityFromRieszConvergence
import NCG.Grand.CompactCircleRieszProjection
import NCG.Grand.IdempotentRangeOrthogonalization

/-!
# Protected graph-kernel rigidity from compact resolvents

Compact self-adjoint resolvents make all cutoff circle Riesz operators idempotent automatically.
Together with norm convergence of those contour operators and a fixed protected multiplicity,
this forces the protected range to equal the full graph kernel eventually.
-/

open Filter Topology Complex Set
open NCG.ResolventStability

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Compactness and symmetry discharge the Riesz-idempotence premise in eventual protected
graph-kernel rigidity. -/
theorem eventually_range_protected_eq_operatorGraphKernel_of_compact_riesz_tendsto
    (D : ℕ → Submodule ℂ E) (A : ∀ n, D n →ₗ[ℂ] F)
    (lam : ℝ) (hlam : 0 < lam) (T P : ℕ → E →L[ℂ] E)
    (hequation : ∀ n f, OperatorGraphResolventEquation (D n) (A n) lam f (T n f))
    (hcompact : ∀ n, IsCompactOperator (T n))
    (hsymmetric : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
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
        Module.finrank ℂ (LinearMap.range Qlim.toLinearMap)) :
    ∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap = operatorGraphKernel (D n) (A n) := by
  have hRieszCompact : ∀ᶠ n in atTop, IsCompactOperator
      ((NCG.ResolventStability.circleRieszProjection
        (T n) center radius : E →L[ℂ] E) : E → E) := by
    filter_upwards [hcontour] with n hn
    exact NCG.ResolventStability.circleRieszProjection_isCompactOperator
      (T n) (hcompact n) center radius hR hzero hn
  have hRieszIdempotentCLM : ∀ᶠ n in atTop, IsIdempotentElem
      (NCG.ResolventStability.circleRieszProjection
        (T n) center radius : E →L[ℂ] E) := by
    filter_upwards [hcontour] with n hn
    exact ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mp
      (NCG.ResolventStability.circleRieszProjection_isIdempotentElem_of_compact_of_isSymmetric
        (T n) (hcompact n) (hsymmetric n) center radius hR
          hn)
  have hRieszIdempotent : ∀ᶠ n in atTop, IsIdempotentElem
      (NCG.ResolventStability.circleRieszProjection
        (T n) center radius).toLinearMap := hRieszIdempotentCLM.mono fun n hn ↦
      ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr
        hn
  have hfinite : ∀ᶠ n in atTop, Module.Finite ℂ
      (LinearMap.range
        (NCG.ResolventStability.circleRieszProjection
          (T n) center radius).toLinearMap) := by
    filter_upwards [hcontour] with n hn
    exact finiteDimensional_range_circleRieszProjection_of_compact_of_isSymmetric
        (T n) (hcompact n) (hsymmetric n) center radius hR hzero
          hn
  have hQlimCompact : IsCompactOperator (Qlim : E → E) :=
    isCompactOperator_of_tendsto hRieszTendsto
      hRieszCompact
  have hQlimIdempotent : IsIdempotentElem Qlim :=
    NCG.isIdempotentElem_of_tendsto
      (fun n ↦ NCG.ResolventStability.circleRieszProjection
        (T n) center radius) Qlim hRieszTendsto
      hRieszIdempotentCLM
  letI : Module.Finite ℂ (LinearMap.range Qlim.toLinearMap) :=
    NCG.ResolventStability.finiteDimensional_range_of_compact_idempotent
      Qlim hQlimCompact hQlimIdempotent
  apply eventually_range_protected_eq_operatorGraphKernel_of_riesz_tendsto
    D A lam hlam T P hequation center radius hinside hcontour Qlim
      hRieszTendsto
  · exact hRieszIdempotent
  · exact hfinite
  · exact hprotected
  · exact hprotectedRank

/-- If the protected operators and the limiting Riesz operator are orthogonal projections,
compact-resolvent kernel rigidity upgrades stabilized equality of the cutoff ranges to
operator-norm convergence of the protected projections themselves. -/
theorem protectedProjection_tendsto_of_compact_riesz_tendsto
    (D : ℕ → Submodule ℂ E) (A : ∀ n, D n →ₗ[ℂ] F)
    (lam : ℝ) (hlam : 0 < lam) (T P : ℕ → E →L[ℂ] E)
    (hequation : ∀ n f, OperatorGraphResolventEquation (D n) (A n) lam f (T n f))
    (hcompact : ∀ n, IsCompactOperator (T n))
    (hsymmetric : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap)
    (center : ℂ) (radius : ℝ) (hR : 0 < radius)
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
    (hstarP : ∀ᶠ n in atTop, IsStarProjection (P n))
    (hstarQlim : IsStarProjection Qlim) :
    Tendsto P atTop (nhds Qlim) := by
  let Q : ℕ → E →L[ℂ] E :=
    fun n ↦ NCG.ResolventStability.circleRieszProjection (T n) center radius
  have hQCompact : ∀ᶠ n in atTop, IsCompactOperator (Q n : E → E) := by
    filter_upwards [hcontour] with n hn
    exact NCG.ResolventStability.circleRieszProjection_isCompactOperator
      (T n) (hcompact n) center radius hR hzero hn
  have hQIdempotent : ∀ᶠ n in atTop, IsIdempotentElem (Q n) := by
    filter_upwards [hcontour] with n hn
    exact ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mp
      (NCG.ResolventStability.circleRieszProjection_isIdempotentElem_of_compact_of_isSymmetric
        (T n) (hcompact n) (hsymmetric n) center radius hR
          hn)
  have hfiniteQ : ∀ᶠ n in atTop, Module.Finite ℂ (LinearMap.range (Q n).toLinearMap) := by
    filter_upwards [hcontour] with n hn
    exact finiteDimensional_range_circleRieszProjection_of_compact_of_isSymmetric
      (T n) (hcompact n) (hsymmetric n) center radius hR hzero
        hn
  have hQlimCompact : IsCompactOperator (Qlim : E → E) :=
    isCompactOperator_of_tendsto hRieszTendsto
      hQCompact
  have hQlimIdempotent : IsIdempotentElem Qlim :=
    NCG.isIdempotentElem_of_tendsto Q Qlim hRieszTendsto
      hQIdempotent
  letI : Module.Finite ℂ (LinearMap.range Qlim.toLinearMap) :=
    NCG.ResolventStability.finiteDimensional_range_of_compact_idempotent
      Qlim hQlimCompact hQlimIdempotent
  have hQrank : ∀ᶠ n in atTop,
      Module.finrank ℂ (LinearMap.range (Q n).toLinearMap) =
        Module.finrank ℂ (LinearMap.range Qlim.toLinearMap) :=
    NCG.ProjectionStability.eventually_finrank_range_eq_of_tendsto
      Q Qlim hRieszTendsto
      (hQIdempotent.mono fun n hn ↦ ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr hn)
      (ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr hQlimIdempotent)
      hfiniteQ
  have hPker :=
    eventually_range_protected_eq_operatorGraphKernel_of_compact_riesz_tendsto
      D A lam hlam T P hequation hcompact hsymmetric center radius hR hzero hinside
        hcontour Qlim hRieszTendsto hprotected hprotectedRank
  have hQker : ∀ᶠ n in atTop,
      LinearMap.range (Q n).toLinearMap = operatorGraphKernel (D n) (A n) := by
    filter_upwards [hPker, hQrank, hfiniteQ, hcontour] with n hPn hQn hnFinite hnContour
    letI : Module.Finite ℂ (LinearMap.range (Q n).toLinearMap) := hnFinite
    apply range_circleRieszProjection_eq_operatorGraphKernel_of_finrank_eq
      (D n) (A n) lam hlam (T n) (hequation n) center radius hinside
        hnContour
    calc
      Module.finrank ℂ (LinearMap.range (Q n).toLinearMap) =
          Module.finrank ℂ (LinearMap.range Qlim.toLinearMap) := hQn
      _ = Module.finrank ℂ (LinearMap.range (P n).toLinearMap) :=
        (hprotectedRank n).symm
      _ = Module.finrank ℂ (operatorGraphKernel (D n) (A n)) :=
        congrArg (fun S : Submodule ℂ E ↦ Module.finrank ℂ S) hPn
  have hPQrange : ∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap = LinearMap.range (Q n).toLinearMap := by
    filter_upwards [hPker, hQker] with n hPn hQn
    exact hPn.trans hQn.symm
  exact NCG.ProjectionStability.starProjection_tendsto_of_idempotent_range_eq
    P Q Qlim hstarP hQIdempotent hstarQlim
      hPQrange hRieszTendsto
end NCG.VaryingHilbert
