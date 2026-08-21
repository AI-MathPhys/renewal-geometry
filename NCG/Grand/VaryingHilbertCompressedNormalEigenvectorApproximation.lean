/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactNormalRieszEigenspace
import NCG.Grand.VaryingHilbertCompressedNormalSpectralSubspaces

/-!
# Eigenvector approximation for compressed normal operators

An automatically isolated nonzero limit eigenspace has canonical stage approximants: apply the
stage Riesz projection to a limit eigenvector. These vectors converge to the original eigenvector,
belong to the exact sum of enclosed stage eigenspaces, and have vanishing eigen-residual.
-/

open Complex Filter Topology
open NCG.ResolventStability

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]

/-- Every vector in a nonzero limit eigenspace has canonical approximants in the exact enclosed
stage spectral subspaces. The approximants converge strongly and their residual at the target
eigenvalue tends to zero. -/
theorem compressedOperator_eigenvectorApproximation_automaticCircle_of_isStarNormal
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (center : ℂ) (hcenter : center ≠ 0)
    (y : H) (hy : y ∈ Module.End.eigenspace T.toLinearMap center) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall center radius ∧
      (∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) ∧
      LinearMap.range (circleRieszProjection T center radius).toLinearMap =
        Module.End.eigenspace T.toLinearMap center ∧
      Tendsto
        (fun n ↦ circleRieszProjection
          (J.compressedOperator Tn n) center radius y) atTop (𝓝 y) ∧
      Tendsto
        (fun n ↦
          J.compressedOperator Tn n
              (circleRieszProjection
                (J.compressedOperator Tn n) center radius y) -
            center • circleRieszProjection
              (J.compressedOperator Tn n) center radius y)
        atTop (𝓝 0) ∧
      ∀ᶠ n in atTop,
        circleRieszProjection
            (J.compressedOperator Tn n) center radius y ∈
          ⨆ μ : ℂ, ⨆ (_ : μ ∈ Metric.ball center radius),
            Module.End.eigenspace
              (J.compressedOperator Tn n).toLinearMap μ := by
  obtain ⟨hTcompact, hop⟩ :=
    J.compressedOperator_tendsto_operatorNorm_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal
  obtain ⟨radius, hR, hzero, hcontour, hrange⟩ :=
    exists_circleRieszProjection_range_eq_eigenspace_of_compact_of_isStarNormal
      T hTcompact hlimNormal center hcenter
  obtain ⟨_, _, hproj⟩ :=
    J.compressedOperator_circleRieszProjection_tendsto_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal
      center radius hR.le hcontour
  let P : H →L[ℂ] H := circleRieszProjection T center radius
  have hyRange : y ∈ LinearMap.range P.toLinearMap := by
    rw [hrange]
    exact hy
  have hPidem : IsIdempotentElem P.toLinearMap := by
    dsimp [P]
    exact circleRieszProjection_isIdempotentElem_of_compact_of_isStarNormal
      T hTcompact hlimNormal center radius hR hcontour
  have hPy : P y = y :=
    (LinearMap.IsIdempotentElem.mem_range_iff hPidem).mp hyRange
  have hvector : Tendsto
      (fun n ↦ circleRieszProjection
        (J.compressedOperator Tn n) center radius y) atTop (𝓝 y) := by
    have happ : Tendsto
        (fun n ↦ circleRieszProjection
          (J.compressedOperator Tn n) center radius y)
        atTop (𝓝 (P y)) := by
      change Tendsto
        ((fun Q : H →L[ℂ] H ↦ Q y) ∘
          fun n ↦ circleRieszProjection
            (J.compressedOperator Tn n) center radius) atTop (𝓝 (P y))
      exact ((continuous_id.clm_apply continuous_const).tendsto P).comp hproj
    simpa only [hPy] using happ
  let C : H →L[ℂ] H := algebraMap ℂ (H →L[ℂ] H) center
  have hlimitResidual : (T - C) * P = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    have hxRange : P x ∈ LinearMap.range P.toLinearMap := ⟨x, rfl⟩
    have hxEig : P x ∈ Module.End.eigenspace T.toLinearMap center := by
      rw [← hrange]
      exact hxRange
    have hxEquation : T (P x) = center • P x :=
      Module.End.mem_eigenspace_iff.mp hxEig
    change T (P x) - center • P x = 0
    rw [hxEquation, sub_self]
  have hshift : Tendsto
      (fun n ↦ J.compressedOperator Tn n - C) atTop (𝓝 (T - C)) :=
    hop.sub tendsto_const_nhds
  have hresidualOperator : Tendsto
      (fun n ↦ (J.compressedOperator Tn n - C) *
        circleRieszProjection
          (J.compressedOperator Tn n) center radius) atTop (𝓝 0) := by
    simpa [P, hlimitResidual] using hshift.mul hproj
  have hresidual : Tendsto
      (fun n ↦
        J.compressedOperator Tn n
            (circleRieszProjection
              (J.compressedOperator Tn n) center radius y) -
          center • circleRieszProjection
            (J.compressedOperator Tn n) center radius y)
      atTop (𝓝 0) := by
    have happ : Tendsto
        (fun n ↦ ((J.compressedOperator Tn n - C) *
          circleRieszProjection
            (J.compressedOperator Tn n) center radius) y)
        atTop (𝓝 ((0 : H →L[ℂ] H) y)) := by
      change Tendsto
        ((fun Q : H →L[ℂ] H ↦ Q y) ∘
          fun n ↦ (J.compressedOperator Tn n - C) *
            circleRieszProjection
              (J.compressedOperator Tn n) center radius)
        atTop (𝓝 ((0 : H →L[ℂ] H) y))
      exact ((continuous_id.clm_apply continuous_const).tendsto
        (0 : H →L[ℂ] H)).comp hresidualOperator
    simpa [C] using happ
  obtain ⟨_, hstage⟩ :=
    J.compressedOperator_circleRieszProjection_spectralSubspaces_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal
      center radius hR hzero hcontour
  have hmember : ∀ᶠ n in atTop,
      circleRieszProjection
          (J.compressedOperator Tn n) center radius y ∈
        ⨆ μ : ℂ, ⨆ (_ : μ ∈ Metric.ball center radius),
          Module.End.eigenspace
            (J.compressedOperator Tn n).toLinearMap μ := by
    filter_upwards [hstage] with n hn
    rw [← hn.1]
    exact ⟨y, rfl⟩
  exact ⟨radius, hR, hzero, hcontour, hrange,
    hvector, hresidual, hmember⟩

end NCG.VaryingHilbert.System
