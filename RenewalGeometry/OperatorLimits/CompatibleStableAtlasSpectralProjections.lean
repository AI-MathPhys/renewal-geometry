/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.OperatorLimits.CompatibleStableAtlasNormResolvent
import RenewalGeometry.OperatorLimits.SelfAdjointIntervalSpectralProjection

/-!
# Convergence of isolated bounded-energy spectral projections for compatible stable atlases

Paper `predictive_spectral_geometry`, `thm:supp-compact-spin-resolvent`, the clause
"Isolated bounded-energy spectral projections converge".

For a compatible stable atlas (`def:stable-spin-atlas`, `CompatibleStableAtlas`) the limit
operator `D̂` has compact resolvent (`isCompactOperator_limit_resolvent`).  For a bounded energy
window `(a,b)` whose endpoints are not eigenvalues of `D̂` (the window cuts out an isolated
spectral cluster; for a compact-resolvent operator the spectrum is the eigenvalue set), let
`1_{(a,b)}(D̂)` be the orthogonal projection onto the closed span of the eigenvectors with
eigenvalue in `(a,b)` (`SelfAdjointResolventData.spectralProjection`), and `1_{(a,b)}(D_h)` the
spectral projection of the Hermitian stage operator (the sum of its eigenprojections for the
eigenvalues in `(a,b)`, `stageSpectralProjection`).  Then

`‖W_h 1_{(a,b)}(D_h) W_h^* - 1_{(a,b)}(D̂)‖ → 0`  (`tendsto_embeddedSpectralProjection`).

Proof: with `z = (a+b)/2 + i(b-a)/2`, the Möbius map `λ ↦ (λ - z)⁻¹` sends `(a,b)` into a disc
whose boundary circle avoids the spectrum of `(D̂ - z)⁻¹`; the circle Riesz projection of
`(D̂ - z)⁻¹` is `1_{(a,b)}(D̂)` and that of the compressed resolvent `W_h (D_h - z)⁻¹ W_h^*` is
`W_h 1_{(a,b)}(D_h) W_h^*` (`SelfAdjointResolventData.circleRieszProjection_compressedResolvent_eq`);
norm-resolvent convergence then gives norm convergence of the Riesz projections
(`circleRieszProjection_embeddedResolvent_tendsto`).
-/

open Filter Topology

noncomputable section

namespace RenewalGeometry

namespace CompatibleStableAtlas

open SelfAdjointResolventData IntervalCircle ResolventStability

universe u v w

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {Hn : ℕ → Type w} [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)] [∀ n, FiniteDimensional ℂ (Hn n)]

variable (A : CompatibleStableAtlas H V Hn)

/-- The spectral projection `1_{(a,b)}(D_h)` of the finite self-adjoint stage operator. -/
def stageSpectralProjection (n : ℕ) (a b : ℝ) : Hn n →L[ℂ] Hn n :=
  (A.stageData n).spectralProjection a b

/-- The stage spectral projection fixes the eigenvectors of `D_h` with eigenvalue in `(a,b)`. -/
theorem stageSpectralProjection_apply_of_mem (n : ℕ) {a b μ : ℝ} (hμ : μ ∈ Set.Ioo a b)
    {v : Hn n} (hv : A.stage n v = (μ : ℂ) • v) : A.stageSpectralProjection n a b v = v := by
  apply (A.stageData n).spectralProjection_apply_of_mem hμ
  unfold stageData
  rw [ofBounded_opEigenspace, Module.End.mem_eigenspace_iff]
  exact hv

/-- The stage spectral projection kills the eigenvectors of `D_h` with eigenvalue outside
`(a,b)`. -/
theorem stageSpectralProjection_apply_of_not_mem (n : ℕ) {a b μ : ℝ} (hμ : μ ∉ Set.Ioo a b)
    {v : Hn n} (hv : A.stage n v = (μ : ℂ) • v) : A.stageSpectralProjection n a b v = 0 := by
  apply (A.stageData n).spectralProjection_apply_of_not_mem hμ
  unfold stageData
  rw [ofBounded_opEigenspace, Module.End.mem_eigenspace_iff]
  exact hv

/-- The embedded stage spectral projection `W_h 1_{(a,b)}(D_h) W_h^*`. -/
def embeddedSpectralProjection (a b : ℝ) (n : ℕ) : H →L[ℂ] H :=
  (A.embed n).toContinuousLinearMap ∘L A.stageSpectralProjection n a b ∘L
    ContinuousLinearMap.adjoint (A.embed n).toContinuousLinearMap

theorem embeddedResolvent_eq_compressedResolvent (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    A.embeddedResolvent z hz n = (A.stageData n).compressedResolvent (A.embed n) z hz := rfl

/-- **Spectral-projection clause of `thm:supp-compact-spin-resolvent`.**  For a compatible
stable atlas and a bounded energy window `(a,b)` whose endpoints are not eigenvalues of the
limit operator `D̂`, the embedded spectral projections `W_h 1_{(a,b)}(D_h) W_h^*` converge in
operator norm to the spectral projection `1_{(a,b)}(D̂)`. -/
theorem tendsto_embeddedSpectralProjection {a b : ℝ} (hab : a < b)
    (ha : A.limit.opEigenspace (a : ℂ) = ⊥) (hb : A.limit.opEigenspace (b : ℂ) = ⊥) :
    Tendsto (A.embeddedSpectralProjection a b) atTop (𝓝 (A.limit.spectralProjection a b)) := by
  have hz : (point a b).im ≠ 0 := point_im_ne_zero hab
  obtain ⟨hunit, hlim⟩ :=
    A.limit.circleRieszProjection_resolvent_eq hab (A.isCompactOperator_limit_resolvent hz) ha hb
  have hconv := A.circleRieszProjection_embeddedResolvent_tendsto hz (center a b) (radius a b)
    (radius_pos hab).le hunit
  rw [hlim] at hconv
  obtain ⟨M, hM, hbound⟩ :=
    exists_circle_resolvent_norm_bound (A.limit.resolvent (point a b) hz) (center a b)
      (radius a b) hunit
  obtain ⟨N, -, hN⟩ := eventually_circle_resolvent_bound_of_tendsto
    (A.embeddedResolvent (point a b) hz) (A.limit.resolvent (point a b) hz)
    (A.tendsto_embeddedResolvent hz) (center a b) (radius a b) M hM hunit hbound
  refine hconv.congr' ?_
  filter_upwards [hN] with n hn
  exact (A.stageData n).circleRieszProjection_compressedResolvent_eq (A.embed n) hab
    ((A.stageData n).isCompactOperator_compressedResolvent (A.embed n) _ hz)
    (fun w hw => (hn w hw).1)

/-- Norm form of `tendsto_embeddedSpectralProjection`. -/
theorem tendsto_norm_embeddedSpectralProjection_sub {a b : ℝ} (hab : a < b)
    (ha : A.limit.opEigenspace (a : ℂ) = ⊥) (hb : A.limit.opEigenspace (b : ℂ) = ⊥) :
    Tendsto (fun n => ‖A.embeddedSpectralProjection a b n - A.limit.spectralProjection a b‖)
      atTop (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.mp (A.tendsto_embeddedSpectralProjection hab ha hb)

/-- The limit `1_{(a,b)}(D̂)` is the circle Riesz projection of the limit resolvent, and the
circle lies in the resolvent set (the cluster in `(a,b)` is isolated). -/
theorem limit_spectralProjection_eq_circleRieszProjection {a b : ℝ} (hab : a < b)
    (ha : A.limit.opEigenspace (a : ℂ) = ⊥) (hb : A.limit.opEigenspace (b : ℂ) = ⊥) :
    circleRieszProjection (A.limit.resolvent (point a b) (point_im_ne_zero hab))
        (center a b) (radius a b) = A.limit.spectralProjection a b :=
  (A.limit.circleRieszProjection_resolvent_eq hab
    (A.isCompactOperator_limit_resolvent (point_im_ne_zero hab)) ha hb).2

end CompatibleStableAtlas

end RenewalGeometry
