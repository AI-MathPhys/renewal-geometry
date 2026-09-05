/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BanachAlgebraResolventStability
import Mathlib.MeasureTheory.Integral.CircleIntegral
import NCG.Grand.CollectivelyCompactStrongToNorm

/-!
# Stability of Riesz projections

This file defines the circle-contour Riesz projection in a complex Banach algebra and proves its
norm continuity under operator-norm convergence.  The hypotheses are the standard compact-screen
ones: the contour stays in every relevant resolvent set and the resolvents are uniformly bounded
there.  `BanachAlgebraResolventStability` upgrades norm convergence to uniform convergence on the
circle; the Bochner circle-integral convergence theorem then gives convergence of the Riesz
projections themselves.
-/

open Filter Topology
open Complex

noncomputable section

namespace NCG.ResolventStability

universe u v

variable {A : Type u}
variable [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The Riesz projection obtained by integrating the resolvent counterclockwise around a circle. -/
def circleRieszProjection (a : A) (center : ℂ) (radius : ℝ) : A :=
  (2 * Real.pi * I)⁻¹ • ∮ z in C(center, radius), resolvent a z

/-- Riesz projections on a fixed circle converge in Banach-algebra norm when the underlying
operators converge in norm and their resolvents admit uniform bounds on that circle. -/
theorem circleRieszProjection_tendsto
    {J : Type v} {l : Filter J} [l.IsCountablyGenerated]
    {a : A} {aSeq : J → A} (ha : Tendsto aSeq l (𝓝 a))
    (center : ℂ) (radius : ℝ) (hradius : 0 ≤ radius) (M N : ℝ)
    (hM : 0 ≤ M)
    (hlimit_unit : ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ a)
    (hlimit_bound :
      ∀ z ∈ Metric.sphere center radius, ‖resolvent a z‖ ≤ M)
    (hstage_unit :
      ∀ᶠ j in l, ∀ z ∈ Metric.sphere center radius,
        z ∈ resolventSet ℂ (aSeq j))
    (hstage_bound :
      ∀ᶠ j in l, ∀ z ∈ Metric.sphere center radius,
        ‖resolvent (aSeq j) z‖ ≤ N) :
    Tendsto (fun j ↦ circleRieszProjection (aSeq j) center radius) l
      (𝓝 (circleRieszProjection a center radius)) := by
  have huniform := resolvent_tendstoUniformlyOn_of_uniform_bound
    ha (Metric.sphere center radius) M N hM hlimit_unit hlimit_bound
      hstage_unit hstage_bound
  have hcontinuous :
      ∀ᶠ j in l, ContinuousOn (resolvent (aSeq j)) (Metric.sphere center radius) := by
    filter_upwards [hstage_unit] with j hj
    intro z hz
    exact (spectrum.hasDerivAt_resolvent_const_left (hj z hz)).continuousAt.continuousWithinAt
  have hintegral :=
    huniform.tendsto_circleIntegral_of_continuousOn hradius hcontinuous
  simpa [circleRieszProjection] using
    hintegral.const_smul ((2 * Real.pi * I : ℂ)⁻¹)


/-- The complete compact-screen pipeline: collectively compact symmetric strong convergence
first upgrades to operator-norm convergence, and uniform contour resolvent bounds then give
operator-norm convergence of the associated Riesz projections. -/
theorem circleRieszProjection_tendsto_of_collectivelyCompact
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : ℕ → H →L[ℂ] H) (Tlim : H →L[ℂ] H)
    (hcompact :
      (NCG.VaryingHilbert.constantSystem ℂ H).CollectivelyCompact T)
    (hlim_compact : IsCompactOperator Tlim)
    (hsymm : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap)
    (hlim_symm : LinearMap.IsSymmetric Tlim.toLinearMap)
    (hstrong : ∀ y : H, Tendsto (fun n ↦ T n y) atTop (𝓝 (Tlim y)))
    (center : ℂ) (radius : ℝ) (hradius : 0 ≤ radius) (M N : ℝ)
    (hM : 0 ≤ M)
    (hlimit_unit :
      ∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ Tlim)
    (hlimit_bound :
      ∀ z ∈ Metric.sphere center radius, ‖resolvent Tlim z‖ ≤ M)
    (hstage_unit :
      ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius,
        z ∈ resolventSet ℂ (T n))
    (hstage_bound :
      ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere center radius,
        ‖resolvent (T n) z‖ ≤ N) :
    Tendsto (fun n ↦ circleRieszProjection (T n) center radius) atTop
      (𝓝 (circleRieszProjection Tlim center radius)) := by
  have hop :=
    NCG.VaryingHilbert.System.tendsto_operatorNorm_of_collectivelyCompact_of_symmetric
      T Tlim hcompact hlim_compact hsymm hlim_symm hstrong
  exact circleRieszProjection_tendsto hop center radius hradius M N hM
    hlimit_unit hlimit_bound hstage_unit hstage_bound
end NCG.ResolventStability
