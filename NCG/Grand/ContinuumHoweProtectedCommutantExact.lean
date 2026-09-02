/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.EmbeddedJointCommutatorCommutant
import NCG.Grand.JointCommutatorProtectedKernelRigidityFromDenseSourcesAndGraphScreens
import NCG.Grand.ProtectedSpectralProjectionRigidity
import NCG.Grand.CircleRieszProjectionOrthogonality

/-!
# Exact protected commutants in the continuum Howe limit

This is the algebraic half of the coercive continuum Howe theorem.  Dense
resolvent sources and a compact graph-screen profile stabilize the finite
kernel multiplicity.  Orthogonality then upgrades equality of ranges to norm
convergence of the protected commutant projections.  Finally, the transported
kernel is identified with the literal simultaneous commutant of the screened
matrix generators.
-/

open Complex Filter Set Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- The protected cutoff projections eventually project onto exactly the
screened matrix commutants, and converge in operator norm to the limiting
commutant projection. -/
theorem jointCommutator_protectedCommutant_tendsto_of_denseSources_of_graphScreens
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : NCG.VaryingHilbert.System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (L : NCG.VaryingHilbert.System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun cutoff ↦ WithLp 2
        (EuclideanSpace ℂ (d cutoff × d cutoff) ×
          EuclideanSpace ℂ (Fin s × (d cutoff × d cutoff)))))
    (A : H →L[ℂ] F)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff, EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ y ∈ D, J.StronglyConverges (source y) y)
    (hcore : ∀ y ∈ D, J.StronglyConverges
      (fun cutoff ↦ NCG.jointCommutatorResolventFamily c lam0 cutoff
        (source y cutoff))
      (boundedOperatorNormalResolventFamily A lam0 y))
    (a : ℝ) (ha : 0 < a)
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (hcompact : ∀ cutoff, IsCompactOperator (screen cutoff))
    (htail : ∀ ε > 0, ∃ screenIndex, ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
        (NCG.jointCommutatorResolventFamily c a cutoff) a ha
        (NCG.jointCommutatorResolventFamily_resolventEquation c a ha cutoff)),
      ‖y - screen screenIndex y‖ < ε)
    (hfst : ∀ cutoff y, J.embedding cutoff y.fst = (L.embedding cutoff y).fst)
    (b : ℝ) (hb : 0 < b)
    (P : ℕ → H →L[ℂ] H)
    (hprotected : ∀ᶠ cutoff in atTop,
      LinearMap.range (P cutoff).toLinearMap ≤
        (LinearMap.ker (NCG.jointCommutatorCLM (c cutoff)).toLinearMap).map
          (J.embedding cutoff).toLinearMap)
    (hprotectedRank : ∀ᶠ cutoff in atTop,
      Module.finrank ℂ (LinearMap.range (P cutoff).toLinearMap) =
        Module.finrank ℂ (LinearMap.ker A.toLinearMap))
    (hstarP : ∀ᶠ cutoff in atTop, IsStarProjection (P cutoff)) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall (((1 / b : ℝ) : ℂ)) radius ∧
      Tendsto P atTop
        (nhds (NCG.ResolventStability.circleRieszProjection
          (boundedOperatorNormalResolventFamily A b)
          (((1 / b : ℝ) : ℂ)) radius)) ∧
      (∀ᶠ cutoff in atTop,
        LinearMap.range (P cutoff).toLinearMap =
          (LinearMap.ker (NCG.jointCommutatorCLM (c cutoff)).toLinearMap).map
            (J.embedding cutoff).toLinearMap) ∧
      (∀ᶠ cutoff in atTop,
        ∀ X : Matrix (d cutoff) (d cutoff) ℂ,
          J.embedding cutoff (NCG.matrixL2 X) ∈
              LinearMap.range (P cutoff).toLinearMap ↔
            ∀ j, c cutoff j * X = X * c cutoff j) := by
  obtain ⟨radius, hR, hzero, hlimitContour, hlimitCompact, _hlimitRange,
    hTconv, hQconv, hPKernel, hPQ⟩ :=
    J.jointCommutator_protectedKernelRigidity_of_denseSources_of_graphScreens
      c L A lam0 hlam0 D hD source hsource hcore a ha screen hcompact htail hfst
        b hb P hprotected hprotectedRank
  let T : ℕ → H →L[ℂ] H :=
    J.compressedOperator (NCG.jointCommutatorResolventFamily c b)
  let Tlim : H →L[ℂ] H := boundedOperatorNormalResolventFamily A b
  let Q : ℕ → H →L[ℂ] H := fun cutoff ↦
    NCG.ResolventStability.circleRieszProjection
      (T cutoff) (((1 / b : ℝ) : ℂ)) radius
  let Qlim : H →L[ℂ] H :=
    NCG.ResolventStability.circleRieszProjection
      Tlim (((1 / b : ℝ) : ℂ)) radius
  obtain ⟨M, hM, hlimitBound⟩ :=
    NCG.ResolventStability.exists_circle_resolvent_norm_bound
      Tlim (((1 / b : ℝ) : ℂ)) radius hlimitContour
  obtain ⟨_N, _hN, hstageBound⟩ :=
    NCG.ResolventStability.eventually_circle_resolvent_bound_of_tendsto
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
      (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c n))) b
      (NCG.jointCommutatorResolventFamily c b n)
      (NCG.jointCommutatorResolventFamily_resolventEquation c b hb n)
  have hstageCompact : ∀ cutoff, IsCompactOperator (T cutoff : H → H) := by
    intro cutoff
    exact J.compressedOperator_isCompactOperator_of_finiteDimensional
      (NCG.jointCommutatorResolventFamily c b) cutoff
  have hstarQ : ∀ᶠ cutoff in atTop, IsStarProjection (Q cutoff) := by
    filter_upwards [hcontour] with cutoff hn
    exact NCG.ResolventStability.circleRieszProjection_isStarProjection_of_compact_of_isSymmetric
      (T cutoff) (hstageCompact cutoff) (hstageSymmetric cutoff)
        (((1 / b : ℝ) : ℂ)) radius hR hn
  have hPconv : Tendsto P atTop (nhds Qlim) :=
    NCG.ProjectionStability.protectedProjection_tendsto_of_eventually_range_eq
      P Q Qlim hstarP hstarQ hPQ hQconv
  have hcommutant :=
    eventually_embeddedMatrix_mem_protectedRange_iff_commutes c J P hPKernel
  exact ⟨radius, hR, hzero, hPconv, hPKernel, hcommutant⟩

end NCG.VaryingHilbert.System
