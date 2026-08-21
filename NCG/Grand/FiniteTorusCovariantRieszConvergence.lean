/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteTorusCovariantLatticeResolver
import NCG.Grand.FiniteTorusCovariantResolverCompactness
import NCG.Grand.CompactSymmetricRieszEigenspace
import NCG.Grand.AutomaticCircleRieszProjectionStability
import NCG.Grand.CompactCircleRieszProjection
import NCG.Grand.NearbyProjectionRankStability

/-!
# Riesz spectral convergence for periodic covariant resolvers

The literal interpolated finite-lattice resolvers are compact symmetric
operators converging in norm to a compact symmetric continuum resolver.
Every nonzero continuum resolvent spectral value therefore admits an
automatically selected Riesz circle on which the spectral projections
converge in norm and their finite multiplicities eventually agree.
-/

open Complex Filter Topology
open scoped InnerProduct lp

noncomputable section

namespace NCG

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {r : Type} [Fintype r] [Nonempty r]

/-- The continuum coefficient resolver is symmetric. -/
theorem continuumCovariantCoefficientResolver_isSymmetric
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    LinearMap.IsSymmetric
      (continuumCovariantCoefficientResolver B lam hlam).toLinearMap := by
  intro f g
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  change inner ℂ
      (continuumCovariantResolverBlock B lam hlam k (f k)) (g k) =
    inner ℂ (f k)
      (continuumCovariantResolverBlock B lam hlam k (g k))
  exact VaryingHilbert.boundedOperatorNormalResolvent_isSymmetric
    (continuumCovariantFourierOperatorStack k B) lam hlam (f k) (g k)

/-- Symmetry is preserved by the finite-fibre torus Fourier
conjugation. -/
theorem conjugateByFiniteFiberTorusFourierEquiv_isSymmetric
    (T : ℓ²(d → ℤ, EuclideanSpace ℂ r) →L[ℂ]
      ℓ²(d → ℤ, EuclideanSpace ℂ r))
    (hT : LinearMap.IsSymmetric T.toLinearMap) :
    LinearMap.IsSymmetric
      (conjugateByFiniteFiberTorusFourierEquiv T).toLinearMap := by
  intro f g
  change inner ℂ
      (finiteFiberTorusFourierEquiv.symm
        (T (finiteFiberTorusFourierEquiv f))) g =
    inner ℂ f
      (finiteFiberTorusFourierEquiv.symm
        (T (finiteFiberTorusFourierEquiv g)))
  rw [← finiteFiberTorusFourierEquiv.inner_map_map
      (finiteFiberTorusFourierEquiv.symm
        (T (finiteFiberTorusFourierEquiv f))) g,
    ← finiteFiberTorusFourierEquiv.inner_map_map f
      (finiteFiberTorusFourierEquiv.symm
        (T (finiteFiberTorusFourierEquiv g))),
    LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]
  exact hT (finiteFiberTorusFourierEquiv f)
    (finiteFiberTorusFourierEquiv g)

/-- Every embedded finite-stage resolver is symmetric. -/
theorem finiteTorusCovariantInterpolatedResolver_isSymmetric
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    LinearMap.IsSymmetric
      (finiteTorusCovariantInterpolatedResolver N B lam hlam).toLinearMap := by
  rw [finiteTorusCovariantInterpolatedResolver_eq_embeddedResolver]
  exact conjugateByFiniteFiberTorusFourierEquiv_isSymmetric _
    (finiteTorusCovariantCoefficientResolver_isSymmetric N B lam hlam)

/-- The continuum torus resolver is symmetric. -/
theorem continuumTorusCovariantResolver_isSymmetric
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    LinearMap.IsSymmetric
      (continuumTorusCovariantResolver B lam hlam).toLinearMap := by
  exact conjugateByFiniteFiberTorusFourierEquiv_isSymmetric _
    (continuumCovariantCoefficientResolver_isSymmetric B lam hlam)

/-- Every literal interpolated finite-lattice resolver is compact because it
factors through the finite-dimensional lattice space. -/
theorem finiteTorusCovariantInterpolatedResolver_isCompactOperator
    (N : ℕ)
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam) :
    IsCompactOperator
      ((finiteTorusCovariantInterpolatedResolver N B lam hlam :
          FiniteFiberContinuumTorusL2 (d := d) (r := r) →L[ℂ]
            FiniteFiberContinuumTorusL2 (d := d) (r := r)) :
        FiniteFiberContinuumTorusL2 (d := d) (r := r) →
          FiniteFiberContinuumTorusL2 (d := d) (r := r)) := by
  have hAdj : IsCompactOperator
      ((finiteFiberFourierInterpolationAdjoint
          (N := N + 1) (d := d) (r := r) :
        FiniteFiberContinuumTorusL2 (d := d) (r := r) →L[ℂ]
          FiniteFiberLatticeL2 (N := N + 1) (d := d) (r := r)) :
        FiniteFiberContinuumTorusL2 (d := d) (r := r) →
          FiniteFiberLatticeL2 (N := N + 1) (d := d) (r := r)) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  exact (hAdj.clm_comp
    (finiteTorusCovariantLatticeResolver N B lam hlam)).clm_comp
      (finiteFiberFourierInterpolationCLM
        (N := N + 1) (d := d) (r := r))

/-- Complete isolated spectral-projection and multiplicity convergence for
the periodic covariant resolvents, stated at any nonzero spectral center of
the continuum resolvent. -/
theorem finiteTorusCovariantInterpolatedResolver_rieszConvergence
    (B : d → EuclideanSpace ℂ r →L[ℂ] EuclideanSpace ℂ r)
    (lam : ℝ) (hlam : 0 < lam)
    (mu : ℂ) (hmu : mu ≠ 0) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall mu radius ∧
      (∀ z ∈ Metric.sphere mu radius,
        z ∈ resolventSet ℂ (continuumTorusCovariantResolver B lam hlam)) ∧
      LinearMap.range
          (ResolventStability.circleRieszProjection
            (continuumTorusCovariantResolver B lam hlam)
            mu radius).toLinearMap =
        Module.End.eigenspace
          (continuumTorusCovariantResolver B lam hlam).toLinearMap mu ∧
      Tendsto
        (fun N ↦ ResolventStability.circleRieszProjection
          (finiteTorusCovariantInterpolatedResolver N B lam hlam)
          mu radius)
        atTop
        (𝓝 (ResolventStability.circleRieszProjection
          (continuumTorusCovariantResolver B lam hlam) mu radius)) ∧
      (∀ᶠ N in atTop,
        Module.finrank ℂ
            (LinearMap.range
              (ResolventStability.circleRieszProjection
                (finiteTorusCovariantInterpolatedResolver N B lam hlam)
                mu radius).toLinearMap) =
          Module.finrank ℂ
            (LinearMap.range
              (ResolventStability.circleRieszProjection
                (continuumTorusCovariantResolver B lam hlam)
                mu radius).toLinearMap)) := by
  let T : ℕ → FiniteFiberContinuumTorusL2 (d := d) (r := r) →L[ℂ]
      FiniteFiberContinuumTorusL2 (d := d) (r := r) :=
    fun N ↦ finiteTorusCovariantInterpolatedResolver N B lam hlam
  let Tlim : FiniteFiberContinuumTorusL2 (d := d) (r := r) →L[ℂ]
      FiniteFiberContinuumTorusL2 (d := d) (r := r) :=
    continuumTorusCovariantResolver B lam hlam
  have hconv : Tendsto T atTop (𝓝 Tlim) :=
    finiteTorusCovariantInterpolatedResolver_tendsto B lam hlam
  have hcompactLim : IsCompactOperator (Tlim :
      FiniteFiberContinuumTorusL2 (d := d) (r := r) →
        FiniteFiberContinuumTorusL2 (d := d) (r := r)) :=
    continuumTorusCovariantResolver_isCompactOperator B lam hlam
  have hsymmLim : LinearMap.IsSymmetric Tlim.toLinearMap :=
    continuumTorusCovariantResolver_isSymmetric B lam hlam
  obtain ⟨radius, hR, hzero, hcontour, hrange⟩ :=
    ResolventStability.exists_circleRieszProjection_range_eq_eigenspace_of_compact_of_isSymmetric
      Tlim hcompactLim hsymmLim mu hmu
  have hproj :
      Tendsto
        (fun N ↦ ResolventStability.circleRieszProjection
          (T N) mu radius) atTop
        (𝓝 (ResolventStability.circleRieszProjection Tlim mu radius)) :=
    ResolventStability.circleRieszProjection_tendsto_of_tendsto_of_circle_subset_resolventSet
      T Tlim hconv mu radius hR.le hcontour
  obtain ⟨M, hM, hlimitBound⟩ :=
    ResolventStability.exists_circle_resolvent_norm_bound
      Tlim mu radius hcontour
  obtain ⟨_, _, hstage⟩ :=
    ResolventStability.eventually_circle_resolvent_bound_of_tendsto
      T Tlim hconv mu radius M hM hcontour hlimitBound
  have hstageContour : ∀ᶠ N in atTop,
      ∀ z ∈ Metric.sphere mu radius, z ∈ resolventSet ℂ (T N) :=
    hstage.mono fun N hN z hz ↦ (hN z hz).1
  have hidemStage : ∀ᶠ N in atTop,
      IsIdempotentElem
        (ResolventStability.circleRieszProjection
          (T N) mu radius).toLinearMap := by
    filter_upwards [hstageContour] with N hN
    exact ResolventStability.circleRieszProjection_isIdempotentElem_of_compact_of_isSymmetric
      (T N)
      (finiteTorusCovariantInterpolatedResolver_isCompactOperator
        N B lam hlam)
      (finiteTorusCovariantInterpolatedResolver_isSymmetric N B lam hlam)
      mu radius hR hN
  have hfiniteStage : ∀ᶠ N in atTop,
      Module.Finite ℂ
        (LinearMap.range
          (ResolventStability.circleRieszProjection
            (T N) mu radius).toLinearMap) := by
    filter_upwards [hstageContour] with N hN
    exact
      ResolventStability.finiteDimensional_range_circleRieszProjection_of_compact_of_isSymmetric
        (T N)
        (finiteTorusCovariantInterpolatedResolver_isCompactOperator
          N B lam hlam)
        (finiteTorusCovariantInterpolatedResolver_isSymmetric N B lam hlam)
        mu radius hR hzero hN
  have hidemLim : IsIdempotentElem
      (ResolventStability.circleRieszProjection
        Tlim mu radius).toLinearMap :=
    ResolventStability.circleRieszProjection_isIdempotentElem_of_compact_of_isSymmetric
      Tlim hcompactLim hsymmLim mu radius hR hcontour
  letI : Module.Finite ℂ
      (LinearMap.range
        (ResolventStability.circleRieszProjection
          Tlim mu radius).toLinearMap) :=
    ResolventStability.finiteDimensional_range_circleRieszProjection_of_compact_of_isSymmetric
      Tlim hcompactLim hsymmLim mu radius hR hzero hcontour
  have hrank :=
    ProjectionStability.eventually_finrank_range_eq_of_tendsto
      (fun N ↦ ResolventStability.circleRieszProjection
        (T N) mu radius)
      (ResolventStability.circleRieszProjection Tlim mu radius)
      hproj hidemStage hidemLim hfiniteStage
  exact ⟨radius, hR, hzero, hcontour, hrange, hproj, hrank⟩

end NCG
