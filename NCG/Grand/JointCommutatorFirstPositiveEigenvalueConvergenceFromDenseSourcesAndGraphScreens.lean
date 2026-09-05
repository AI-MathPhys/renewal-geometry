/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorFirstPositiveEigenvalue
import NCG.Grand.JointCommutatorHoweGapFromDenseSourcesAndGraphScreens
import NCG.Grand.VaryingHilbertFiniteStageNorm

/-!
# Convergence of cutoff first positive joint-commutator eigenvalues

This is the numerical endpoint of the graph-screen compiler.  The protected common-carrier
projection is eventually the transport of the canonical finite kernel projection.  Thus the
convergent inverse-norm gaps are exactly the attained least positive eigenvalues of the literal
cutoff commutant Laplacians.
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

/-- Dense-source graph-screen convergence forces the numerical first positive cutoff
joint-commutator eigenvalues to converge to a strictly positive continuum gap. -/
theorem jointCommutator_firstPositiveEigenvalue_tendsto_of_denseSources_of_graphScreens
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
    (hstarP : ∀ᶠ cutoff in atTop, IsStarProjection (P cutoff))
    (hinfinite : ¬FiniteDimensional ℂ H) :
    ∃ (radius μlim : ℝ), 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall (((1 / b : ℝ) : ℂ)) radius ∧
      0 < μlim ∧
      (∀ᶠ cutoff in atTop,
        LinearMap.range (P cutoff).toLinearMap =
          (LinearMap.ker (NCG.jointCommutatorCLM (c cutoff)).toLinearMap).map
            (J.embedding cutoff).toLinearMap) ∧
      Tendsto
        (fun cutoff ↦
          ‖NCG.SpectralGap.complementCompression
            (J.compressedOperator (NCG.jointCommutatorResolventFamily c b) cutoff)
            (P cutoff)‖⁻¹ - b)
        atTop (nhds μlim) ∧
      (∀ᶠ cutoff in atTop,
        let μ := ‖NCG.SpectralGap.complementCompression
          (J.compressedOperator (NCG.jointCommutatorResolventFamily c b) cutoff)
          (P cutoff)‖⁻¹ - b
        0 < μ ∧
          Module.End.HasEigenvalue
            (NCG.commutantLaplacianCLM (c cutoff)).toLinearMap (μ : ℂ) ∧
          ∀ ν : ℝ, 0 < ν →
            Module.End.HasEigenvalue
              (NCG.commutantLaplacianCLM (c cutoff)).toLinearMap (ν : ℂ) → μ ≤ ν) := by
  obtain ⟨radius, hR, hzero, hPKernel, hgap, hgapPos⟩ :=
    J.jointCommutator_inverseNormGap_tendsto_of_denseSources_of_graphScreens
      c L A lam0 hlam0 D hD source hsource hcore a ha screen hcompact htail hfst
        b hb P hprotected hprotectedRank hstarP hinfinite
  let μlim : ℝ := ‖NCG.SpectralGap.complementCompression
    (boundedOperatorNormalResolventFamily A b)
    (NCG.ResolventStability.circleRieszProjection
      (boundedOperatorNormalResolventFamily A b)
      (((1 / b : ℝ) : ℂ)) radius)‖⁻¹ - b
  let R : ∀ cutoff, EuclideanSpace ℂ (d cutoff × d cutoff) →L[ℂ]
      EuclideanSpace ℂ (d cutoff × d cutoff) :=
    fun cutoff ↦ NCG.jointCommutatorKernelProjection (c cutoff)
  have hstarR : ∀ cutoff, IsStarProjection (R cutoff) := by
    intro cutoff
    exact NCG.jointCommutatorKernelProjection_isStarProjection (c cutoff)
  have htransportStar : ∀ cutoff,
      IsStarProjection (J.compressedOperator R cutoff) := by
    intro cutoff
    exact J.compressedOperator_isStarProjection R cutoff (hstarR cutoff)
  have htransportRange : ∀ cutoff,
      LinearMap.range (J.compressedOperator R cutoff).toLinearMap =
        (LinearMap.ker (NCG.jointCommutatorCLM (c cutoff)).toLinearMap).map
          (J.embedding cutoff).toLinearMap := by
    intro cutoff
    rw [J.range_compressedOperator, NCG.range_jointCommutatorKernelProjection]
  have hPeq : ∀ᶠ cutoff in atTop, P cutoff = J.compressedOperator R cutoff := by
    filter_upwards [hPKernel, hstarP] with cutoff hrange hPstar
    exact ContinuousLinearMap.IsStarProjection.ext hPstar (htransportStar cutoff)
      (hrange.trans (htransportRange cutoff).symm)
  have hgapEq : ∀ᶠ cutoff in atTop,
      ‖NCG.SpectralGap.complementCompression
        (J.compressedOperator (NCG.jointCommutatorResolventFamily c b) cutoff)
        (P cutoff)‖⁻¹ - b =
      ‖NCG.SpectralGap.complementCompression
        (NCG.jointCommutatorResolvent (c cutoff) b hb) (R cutoff)‖⁻¹ - b := by
    filter_upwards [hPeq] with cutoff heq
    rw [heq, J.norm_complementCompression_compressedOperator]
    simp [NCG.jointCommutatorResolventFamily,
      NCG.jointCommutatorResolventAllShifts, dif_pos hb, R]
  have hstagePos : ∀ᶠ cutoff in atTop,
      0 < ‖NCG.SpectralGap.complementCompression
        (J.compressedOperator (NCG.jointCommutatorResolventFamily c b) cutoff)
        (P cutoff)‖⁻¹ - b :=
    hgap.eventually (Ioi_mem_nhds (by simpa [μlim] using hgapPos))
  have hnumeric : ∀ᶠ cutoff in atTop,
      let μ := ‖NCG.SpectralGap.complementCompression
        (J.compressedOperator (NCG.jointCommutatorResolventFamily c b) cutoff)
        (P cutoff)‖⁻¹ - b
      0 < μ ∧
        Module.End.HasEigenvalue
          (NCG.commutantLaplacianCLM (c cutoff)).toLinearMap (μ : ℂ) ∧
        ∀ ν : ℝ, 0 < ν →
          Module.End.HasEigenvalue
            (NCG.commutantLaplacianCLM (c cutoff)).toLinearMap (ν : ℂ) → μ ≤ ν := by
    filter_upwards [hgapEq, hstagePos] with cutoff heq hpos
    have hne : NCG.SpectralGap.complementCompression
        (NCG.jointCommutatorResolvent (c cutoff) b hb) (R cutoff) ≠ 0 := by
      intro hzeroNative
      rw [hzeroNative, norm_zero, inv_zero] at heq
      linarith
    have hleast := NCG.jointCommutator_inverseNormGap_is_leastPositiveEigenvalue
      (c cutoff) b hb (by simpa [R] using hne)
    rw [heq]
    simpa [R] using hleast
  refine ⟨radius, μlim, hR, hzero, ?_, hPKernel, ?_, hnumeric⟩
  · simpa [μlim] using hgapPos
  · simpa [μlim] using hgap

end NCG.VaryingHilbert.System
