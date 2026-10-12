/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import MathPhys.NCG.OperatorLimits.BoundedOperatorNormalResolventInjectivity
import MathPhys.NCG.OperatorLimits.CompactPositiveCircleRieszGap
import MathPhys.NCG.OperatorAlgebras.JointCommutatorProtectedKernelRigidityFromDenseSourcesAndGraphScreens
/-!
# Joint-commutator Howe gaps from dense sources and graph screens

The protected-kernel spectral package already supplies norm convergence of the compressed
finite resolvents and their circle Riesz projections.  When the protected projections are
orthogonal, equal cutoff ranges therefore force convergence of the complement-compressed
inverse-norm gaps.  Injectivity of the canonical bounded normal resolvent and infinite
dimensionality make the limiting gap strictly positive automatically.
-/

open Complex Filter Set Topology

noncomputable section

namespace MathPhys.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- Dense-core convergence and compact graph screens automatically give eventual exact
protected kernels and convergence to a strictly positive inverse-norm Howe gap. -/
theorem jointCommutator_inverseNormGap_tendsto_of_denseSources_of_graphScreens
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun cutoff ↦ WithLp 2
        (EuclideanSpace ℂ (d cutoff × d cutoff) ×
          EuclideanSpace ℂ (Fin s × (d cutoff × d cutoff)))))
    (A : H →L[ℂ] F)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff, EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ y ∈ D, J.StronglyConverges (source y) y)
    (hcore : ∀ y ∈ D, J.StronglyConverges
      (fun cutoff ↦ MathPhys.jointCommutatorResolventFamily c lam0 cutoff
        (source y cutoff))
      (boundedOperatorNormalResolventFamily A lam0 y))
    (a : ℝ) (ha : 0 < a)
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (hcompact : ∀ cutoff, IsCompactOperator (screen cutoff))
    (htail : ∀ ε > 0, ∃ screenIndex, ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (MathPhys.jointCommutatorCLM (c cutoff)))
        (MathPhys.jointCommutatorResolventFamily c a cutoff) a ha
        (MathPhys.jointCommutatorResolventFamily_resolventEquation c a ha cutoff)),
      ‖y - screen screenIndex y‖ < ε)
    (hfst : ∀ cutoff y, J.embedding cutoff y.fst = (L.embedding cutoff y).fst)
    (b : ℝ) (hb : 0 < b)
    (P : ℕ → H →L[ℂ] H)
    (hprotected : ∀ᶠ cutoff in atTop,
      LinearMap.range (P cutoff).toLinearMap ≤
        (LinearMap.ker (MathPhys.jointCommutatorCLM (c cutoff)).toLinearMap).map
          (J.embedding cutoff).toLinearMap)
    (hprotectedRank : ∀ᶠ cutoff in atTop,
      Module.finrank ℂ (LinearMap.range (P cutoff).toLinearMap) =
        Module.finrank ℂ (LinearMap.ker A.toLinearMap))
    (hstarP : ∀ᶠ cutoff in atTop, IsStarProjection (P cutoff))
    (hinfinite : ¬FiniteDimensional ℂ H) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall (((1 / b : ℝ) : ℂ)) radius ∧
      (∀ᶠ cutoff in atTop,
        LinearMap.range (P cutoff).toLinearMap =
          (LinearMap.ker (MathPhys.jointCommutatorCLM (c cutoff)).toLinearMap).map
            (J.embedding cutoff).toLinearMap) ∧
      Tendsto
        (fun cutoff ↦
          ‖MathPhys.SpectralGap.complementCompression
            (J.compressedOperator (MathPhys.jointCommutatorResolventFamily c b) cutoff)
            (P cutoff)‖⁻¹ - b)
        atTop
        (nhds (‖MathPhys.SpectralGap.complementCompression
          (boundedOperatorNormalResolventFamily A b)
          (MathPhys.ResolventStability.circleRieszProjection
            (boundedOperatorNormalResolventFamily A b)
            (((1 / b : ℝ) : ℂ)) radius)‖⁻¹ - b)) ∧
      0 < ‖MathPhys.SpectralGap.complementCompression
        (boundedOperatorNormalResolventFamily A b)
        (MathPhys.ResolventStability.circleRieszProjection
          (boundedOperatorNormalResolventFamily A b)
          (((1 / b : ℝ) : ℂ)) radius)‖⁻¹ - b := by
  obtain ⟨radius, hR, hzero, hlimitContour, hlimitCompact, _hlimitRange,
    hTconv, hQconv, hPKernel, hPQ⟩ :=
    J.jointCommutator_protectedKernelRigidity_of_denseSources_of_graphScreens
      c L A lam0 hlam0 D hD source hsource hcore a ha screen hcompact htail hfst
        b hb P hprotected hprotectedRank
  let T : ℕ → H →L[ℂ] H :=
    J.compressedOperator (MathPhys.jointCommutatorResolventFamily c b)
  let Tlim : H →L[ℂ] H := boundedOperatorNormalResolventFamily A b
  let Q : ℕ → H →L[ℂ] H := fun cutoff ↦
    MathPhys.ResolventStability.circleRieszProjection
      (T cutoff) (((1 / b : ℝ) : ℂ)) radius
  let Qlim : H →L[ℂ] H :=
    MathPhys.ResolventStability.circleRieszProjection
      Tlim (((1 / b : ℝ) : ℂ)) radius
  obtain ⟨M, hM, hlimitBound⟩ :=
    MathPhys.ResolventStability.exists_circle_resolvent_norm_bound
      Tlim (((1 / b : ℝ) : ℂ)) radius hlimitContour
  obtain ⟨N, hN, hstageBound⟩ :=
    MathPhys.ResolventStability.eventually_circle_resolvent_bound_of_tendsto
      T Tlim hTconv (((1 / b : ℝ) : ℂ)) radius M hM
        hlimitContour hlimitBound
  have hcontour : ∀ᶠ cutoff in atTop,
      ∀ z ∈ Metric.sphere (((1 / b : ℝ) : ℂ)) radius,
        z ∈ resolventSet ℂ (T cutoff) :=
    hstageBound.mono fun _ hn z hz ↦ (hn z hz).1
  have hstageSymmetric : ∀ cutoff,
      LinearMap.IsSymmetric (T cutoff).toLinearMap := by
    intro cutoff
    apply J.compressedOperator_isSymmetric
    intro n
    exact operatorGraphResolvent_isSymmetric
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (d n × d n)))
      (boundedOperatorGraphMap (MathPhys.jointCommutatorCLM (c n))) b
      (MathPhys.jointCommutatorResolventFamily c b n)
      (MathPhys.jointCommutatorResolventFamily_resolventEquation c b hb n)
  have hstageCompact : ∀ cutoff, IsCompactOperator (T cutoff : H → H) := by
    intro cutoff
    exact J.compressedOperator_isCompactOperator_of_finiteDimensional
      (MathPhys.jointCommutatorResolventFamily c b) cutoff
  have hstarQ : ∀ᶠ cutoff in atTop, IsStarProjection (Q cutoff) := by
    filter_upwards [hcontour] with cutoff hn
    exact MathPhys.ResolventStability.circleRieszProjection_isStarProjection_of_compact_of_isSymmetric
      (T cutoff) (hstageCompact cutoff) (hstageSymmetric cutoff)
        (((1 / b : ℝ) : ℂ)) radius hR hn
  have hlimSymmetric : LinearMap.IsSymmetric Tlim.toLinearMap := by
    exact boundedOperatorNormalResolventFamily_isSymmetric A b hb
  have hstarQlim : IsStarProjection Qlim :=
    MathPhys.ResolventStability.circleRieszProjection_isStarProjection_of_compact_of_isSymmetric
      Tlim hlimitCompact hlimSymmetric (((1 / b : ℝ) : ℂ)) radius hR hlimitContour
  have hne : MathPhys.SpectralGap.complementCompression Tlim Qlim ≠ 0 :=
    MathPhys.SpectralGap.circleRieszProjection_complementCompression_ne_zero_of_injective
      Tlim hlimitCompact hlimSymmetric
        (boundedOperatorNormalResolventFamily_injective A b hb)
        (((1 / b : ℝ) : ℂ)) radius hR hzero hlimitContour hinfinite
  have hgapTendsto : Tendsto
      (fun cutoff ↦ ‖MathPhys.SpectralGap.complementCompression (T cutoff) (P cutoff)‖⁻¹ - b)
      atTop (nhds (‖MathPhys.SpectralGap.complementCompression Tlim Qlim‖⁻¹ - b)) :=
    MathPhys.SpectralGap.inverseNormGap_tendsto_of_idempotent_ranges
      T P Q Tlim Qlim b hTconv hQconv hstarP
        (hstarQ.mono fun _ h ↦ h.isIdempotentElem) hstarQlim hPQ
        (norm_ne_zero_iff.mpr hne)
  have hlimitPositive : Tlim.IsPositive :=
    boundedOperatorNormalResolventFamily_isPositive A b hb
  have hlimitNorm : ‖Tlim‖ ≤ b⁻¹ := by
    simpa [one_div] using boundedOperatorNormalResolventFamily_opNorm_le_inv A b hb
  have hinside : (((b : ℝ) : ℂ)⁻¹) ∈
      Metric.ball (((1 / b : ℝ) : ℂ)) radius := by
    simpa [one_div] using
      (Metric.mem_ball_self hR : (((1 / b : ℝ) : ℂ)) ∈
        Metric.ball (((1 / b : ℝ) : ℂ)) radius)
  have hgapPos : 0 < ‖MathPhys.SpectralGap.complementCompression Tlim Qlim‖⁻¹ - b :=
    MathPhys.SpectralGap.inverseNormGap_circleRieszProjection_pos
      Tlim hlimitCompact hlimitPositive (((1 / b : ℝ) : ℂ)) radius hR
        hlimitContour b hb hinside hlimitNorm hne
  exact ⟨radius, hR, hzero, hPKernel, hgapTendsto, hgapPos⟩

end MathPhys.VaryingHilbert.System
