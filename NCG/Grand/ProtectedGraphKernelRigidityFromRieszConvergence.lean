/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ProtectedGraphKernelRigidity
import NCG.Grand.NearbyProjectionRankStability
import NCG.Grand.IdempotentNormLimit

/-!
# Protected graph-kernel rigidity from convergent Riesz projections

Norm convergence of finite-rank idempotent Riesz operators stabilizes their multiplicities.
Combining that fact with a fixed protected rank and the graph-resolvent residue inclusion forces
the protected range to equal the full graph kernel at every sufficiently late cutoff.
-/

open Filter Topology Complex Set

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Norm-convergent finite-rank Riesz operators and one fixed protected multiplicity lock the
protected range to the graph kernel eventually. -/
theorem eventually_range_protected_eq_operatorGraphKernel_of_riesz_tendsto
    (D : ℕ → Submodule ℂ E) (A : ∀ n, D n →ₗ[ℂ] F)
    (lam : ℝ) (hlam : 0 < lam) (T P : ℕ → E →L[ℂ] E)
    (hequation : ∀ n f, OperatorGraphResolventEquation (D n) (A n) lam f (T n f))
    (center : ℂ) (radius : ℝ)
    (hinside : (((lam : ℝ) : ℂ)⁻¹) ∈ Metric.ball center radius)
    (hcontour : ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ (T n))
    (Qlim : E →L[ℂ] E)
    (hRieszTendsto : Tendsto
      (fun n ↦ NCG.ResolventStability.circleRieszProjection (T n) center radius)
      atTop (nhds Qlim))
    (hRieszIdempotent : ∀ᶠ n in atTop,
      IsIdempotentElem
        (NCG.ResolventStability.circleRieszProjection
          (T n) center radius).toLinearMap)
    (hfinite : ∀ᶠ n in atTop, Module.Finite ℂ
      (LinearMap.range
        (NCG.ResolventStability.circleRieszProjection (T n) center radius).toLinearMap))
    [Module.Finite ℂ (LinearMap.range Qlim.toLinearMap)]
    (hprotected : ∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap ≤ operatorGraphKernel (D n) (A n))
    (hprotectedRank : ∀ n,
      Module.finrank ℂ (LinearMap.range (P n).toLinearMap) =
        Module.finrank ℂ (LinearMap.range Qlim.toLinearMap)) :
    ∀ᶠ n in atTop,
      LinearMap.range (P n).toLinearMap = operatorGraphKernel (D n) (A n) := by
  have hRieszIdempotentCLM : ∀ᶠ n in atTop,
      IsIdempotentElem
        (NCG.ResolventStability.circleRieszProjection (T n) center radius) :=
    hRieszIdempotent.mono fun _ hn ↦
      ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mp hn
  have hQlimIdempotent : IsIdempotentElem Qlim.toLinearMap :=
    ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr
      (NCG.isIdempotentElem_of_tendsto
        (fun n ↦ NCG.ResolventStability.circleRieszProjection (T n) center radius)
        Qlim hRieszTendsto hRieszIdempotentCLM)
  have hRieszRank : ∀ᶠ n in atTop,
      Module.finrank ℂ (LinearMap.range
        (NCG.ResolventStability.circleRieszProjection (T n) center radius).toLinearMap) =
      Module.finrank ℂ (LinearMap.range Qlim.toLinearMap) :=
    NCG.ProjectionStability.eventually_finrank_range_eq_of_tendsto
      (fun n ↦ NCG.ResolventStability.circleRieszProjection (T n) center radius)
      Qlim hRieszTendsto hRieszIdempotent hQlimIdempotent
        hfinite
  apply eventually_range_protected_eq_operatorGraphKernel_of_riesz_finrank_eq
    D A lam hlam T P hequation center radius hinside hcontour hfinite hprotected
  filter_upwards [hRieszRank] with n hn
  calc
    Module.finrank ℂ (LinearMap.range (P n).toLinearMap) =
        Module.finrank ℂ (LinearMap.range Qlim.toLinearMap) := hprotectedRank n
    _ = Module.finrank ℂ (LinearMap.range
        (NCG.ResolventStability.circleRieszProjection (T n) center radius).toLinearMap) :=
      hn.symm

end NCG.VaryingHilbert
