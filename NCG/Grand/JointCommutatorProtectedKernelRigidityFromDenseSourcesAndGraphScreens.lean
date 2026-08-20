/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactCircleRieszProjection
import NCG.Grand.ContourResolventBounds
import NCG.Grand.JointCommutatorBoundedKernelSpectralConsequencesFromDenseSourcesAndGraphScreens
import NCG.Grand.JointCommutatorCompressedResolventKernel

/-!
# Protected finite commutant kernels from dense sources and graph screens

Dense-core convergence to the canonical continuum normal resolvent and compact graph
screens stabilize the Riesz multiplicity.  A protected cutoff subspace contained in
the embedded finite commutant kernel, with the limiting commutant dimension, therefore
equals the entire embedded cutoff kernel eventually.  The proof also identifies that
kernel with the cutoff circle-Riesz range.
-/

open Complex Filter Set Topology

open NCG.ResolventStability
noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- Protected cutoff kernels of the limiting dimension exhaust the full finite
joint-commutator kernels eventually. -/
theorem jointCommutator_protectedKernelRigidity_of_denseSources_of_graphScreens
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
        (NCG.jointCommutatorResolventFamily_resolventEquation
          c a ha cutoff)),
      ‖y - screen screenIndex y‖ < ε)
    (hfst : ∀ cutoff y, J.embedding cutoff y.fst =
      (L.embedding cutoff y).fst)
    (b : ℝ) (hb : 0 < b)
    (P : ℕ → H →L[ℂ] H)
    (hprotected : ∀ᶠ cutoff in atTop,
      LinearMap.range (P cutoff).toLinearMap ≤
        (LinearMap.ker
          (NCG.jointCommutatorCLM (c cutoff)).toLinearMap).map
            (J.embedding cutoff).toLinearMap)
    (hprotectedRank : ∀ᶠ cutoff in atTop,
      Module.finrank ℂ (LinearMap.range (P cutoff).toLinearMap) =
        Module.finrank ℂ (LinearMap.ker A.toLinearMap)) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall (((1 / b : ℝ) : ℂ)) radius ∧
      (∀ z ∈ Metric.sphere (((1 / b : ℝ) : ℂ)) radius,
        z ∈ resolventSet ℂ (boundedOperatorNormalResolventFamily A b)) ∧
      IsCompactOperator (boundedOperatorNormalResolventFamily A b) ∧
      LinearMap.range
          (NCG.ResolventStability.circleRieszProjection
            (boundedOperatorNormalResolventFamily A b)
            (((1 / b : ℝ) : ℂ)) radius).toLinearMap =
        LinearMap.ker A.toLinearMap ∧
      Tendsto
        (J.compressedOperator (NCG.jointCommutatorResolventFamily c b))
        atTop (nhds (boundedOperatorNormalResolventFamily A b)) ∧
      Tendsto
        (fun cutoff ↦ NCG.ResolventStability.circleRieszProjection
          (J.compressedOperator
            (NCG.jointCommutatorResolventFamily c b) cutoff)
          (((1 / b : ℝ) : ℂ)) radius) atTop
        (nhds (NCG.ResolventStability.circleRieszProjection
          (boundedOperatorNormalResolventFamily A b)
          (((1 / b : ℝ) : ℂ)) radius)) ∧
      (∀ᶠ cutoff in atTop,
        LinearMap.range (P cutoff).toLinearMap =
          (LinearMap.ker
            (NCG.jointCommutatorCLM (c cutoff)).toLinearMap).map
              (J.embedding cutoff).toLinearMap) ∧
      (∀ᶠ cutoff in atTop,
        LinearMap.range (P cutoff).toLinearMap =
          LinearMap.range
            (NCG.ResolventStability.circleRieszProjection
              (J.compressedOperator
                (NCG.jointCommutatorResolventFamily c b) cutoff)
              (((1 / b : ℝ) : ℂ)) radius).toLinearMap) := by
  have hresult :=
    J.jointCommutator_boundedKernelSpectralConsequences_of_denseSources_of_graphScreens
      (iota := Fin 0) c L A lam0 hlam0 D hD source hsource hcore
      a ha screen hcompact htail hfst b hb
      (fun _ i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
      (by intro i; exact Fin.elim0 i)
  obtain ⟨radius, hR, hzero, hlimitContour, hlimitCompact,
    hlimitRange, hTconv, hQconv, hQrank, _⟩ := hresult
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
  obtain ⟨N, hN, hstageBound⟩ :=
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
  have hfinite : ∀ᶠ cutoff in atTop,
      Module.Finite ℂ (LinearMap.range (Q cutoff).toLinearMap) := by
    filter_upwards [hcontour] with cutoff hn
    exact finiteDimensional_range_circleRieszProjection_of_compact_of_isSymmetric
      (T cutoff) (hstageCompact cutoff) (hstageSymmetric cutoff)
      (((1 / b : ℝ) : ℂ)) radius hR hzero hn
  have hkernelRiesz : ∀ᶠ cutoff in atTop,
      (LinearMap.ker
        (NCG.jointCommutatorCLM (c cutoff)).toLinearMap).map
          (J.embedding cutoff).toLinearMap ≤
        LinearMap.range (Q cutoff).toLinearMap := by
    filter_upwards [hcontour] with cutoff hn
    rw [← J.eigenspace_compressed_jointCommutatorResolventFamily c b hb cutoff]
    exact NCG.ResolventStability.eigenspace_le_range_circleRieszProjection_of_mem_ball
      (T cutoff) (((1 / b : ℝ) : ℂ)) (((b : ℝ) : ℂ)⁻¹) radius
      (by
        have hcenter : (((1 / b : ℝ) : ℂ)) ∈
            Metric.ball (((1 / b : ℝ) : ℂ)) radius :=
          Metric.mem_ball_self hR
        simpa [one_div] using hcenter) hn
  have hPQrank : ∀ᶠ cutoff in atTop,
      Module.finrank ℂ (LinearMap.range (P cutoff).toLinearMap) =
        Module.finrank ℂ (LinearMap.range (Q cutoff).toLinearMap) := by
    filter_upwards [hQrank, hprotectedRank] with cutoff hn hnProtectedRank
    calc
      Module.finrank ℂ (LinearMap.range (P cutoff).toLinearMap) =
          Module.finrank ℂ (LinearMap.ker A.toLinearMap) :=
        hnProtectedRank
      _ = Module.finrank ℂ (LinearMap.range Qlim.toLinearMap) :=
        congrArg (fun S : Submodule ℂ H ↦ Module.finrank ℂ S) hlimitRange.symm
      _ = Module.finrank ℂ (LinearMap.range (Q cutoff).toLinearMap) := hn.symm
  have hPQ : ∀ᶠ cutoff in atTop,
      LinearMap.range (P cutoff).toLinearMap =
        LinearMap.range (Q cutoff).toLinearMap := by
    filter_upwards [hfinite, hprotected, hkernelRiesz, hPQrank]
      with cutoff hnFinite hnProtected hnKernel hnRank
    letI : Module.Finite ℂ (LinearMap.range (Q cutoff).toLinearMap) := hnFinite
    exact Submodule.eq_of_le_of_finrank_eq (hnProtected.trans hnKernel) hnRank
  have hPKernel : ∀ᶠ cutoff in atTop,
      LinearMap.range (P cutoff).toLinearMap =
        (LinearMap.ker
          (NCG.jointCommutatorCLM (c cutoff)).toLinearMap).map
            (J.embedding cutoff).toLinearMap := by
    filter_upwards [hprotected, hkernelRiesz, hPQ]
      with cutoff hnProtected hnKernel hnPQ
    apply le_antisymm hnProtected
    rw [hnPQ]
    exact hnKernel
  exact ⟨radius, hR, hzero, hlimitContour, hlimitCompact,
    hlimitRange, hTconv, hQconv, hPKernel, hPQ⟩

end NCG.VaryingHilbert.System
