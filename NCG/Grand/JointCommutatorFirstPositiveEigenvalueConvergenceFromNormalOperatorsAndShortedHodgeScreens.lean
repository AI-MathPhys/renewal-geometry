/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorFirstPositiveEigenvalueConvergenceFromNormalOperatorsAndGraphScreens
import NCG.Grand.JointCommutatorShortedHodgeGraphScreenTail

/-!
# Howe eigenvalue convergence from normal operators and shorted-Hodge screens

This is the numerical continuum-Howe compiler with the compact graph-screen tail discharged by
a shorted-Hodge Sobolev estimate on the literal embedded joint-commutator graph unit balls.
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

/-- Strong convergence of the literal cutoff commutant Laplacians and a shorted-Hodge spectral
screen prove convergence of the attained first positive eigenvalues to a positive continuum
Howe gap. -/
theorem jointCommutator_firstPositiveEigenvalue_tendsto_of_normalOperatorConvergence_of_shortedHodgeScreens
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {q : ℕ}
    (c : ∀ cutoff, Fin q → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun cutoff ↦ WithLp 2
        (EuclideanSpace ℂ (d cutoff × d cutoff) ×
          EuclideanSpace ℂ (Fin q × (d cutoff × d cutoff)))))
    (A : H →L[ℂ] F)
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ cutoff, EuclideanSpace ℂ (d cutoff × d cutoff))
    (hsource : ∀ y ∈ D, J.StronglyConverges (source y) y)
    (hnormal : J.StrongOperatorConverges J
      (fun cutoff ↦ NCG.commutantLaplacianCLM (c cutoff))
      ((ContinuousLinearMap.adjoint A).comp A))
    (a : ℝ) (ha : 0 < a)
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (hcompact : ∀ cutoff, IsCompactOperator (screen cutoff))
    {i : Type*} [Fintype i]
    (ell : i → ℝ)
    (coeff : WithLp 2 (H × F) → i → ℂ)
    (action : WithLp 2 (H × F) → ℝ)
    (sSob cSob C0 E B : ℝ)
    (hell : ∀ j, 0 ≤ ell j) (hsSob : 0 < sSob) (hcSob : 0 < cSob)
    (hC0 : 0 ≤ C0)
    (haction : ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
        (NCG.jointCommutatorResolventFamily c a cutoff) a ha
        (NCG.jointCommutatorResolventFamily_resolventEquation c a ha cutoff)),
      action y ≤ E)
    (hcoeff : ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
        (NCG.jointCommutatorResolventFamily c a cutoff) a ha
        (NCG.jointCommutatorResolventFamily_resolventEquation c a ha cutoff)),
      ∑ j, Complex.normSq (coeff y j) ≤ B)
    (hcoercive : ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
        (NCG.jointCommutatorResolventFamily c a cutoff) a ha
        (NCG.jointCommutatorResolventFamily_resolventEquation c a ha cutoff)),
      cSob * NCG.RenewalShortedHodgeAndCompactScreen.spectralSobolevEnergy
          ell sSob (coeff y) -
        C0 * (∑ j, Complex.normSq (coeff y j)) ≤ action y)
    (hscreen : ∀ R y, y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
        (NCG.jointCommutatorResolventFamily c a cutoff) a ha
        (NCG.jointCommutatorResolventFamily_resolventEquation c a ha cutoff)) →
      ‖y - screen R y‖ ^ 2 =
        NCG.RenewalShortedHodgeAndCompactScreen.spectralTailNormSq
          ell (R : ℝ) (coeff y))
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
  have htail : ∀ ε > 0, ∃ screenIndex, ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphResolventHilbertGraph
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
        (NCG.jointCommutatorResolventFamily c a cutoff) a ha
        (NCG.jointCommutatorResolventFamily_resolventEquation c a ha cutoff)),
      ‖y - screen screenIndex y‖ < ε :=
    jointCommutator_graphScreenTail_of_shortedHodgeSobolevBound
      c L a ha ell screen coeff action sSob cSob C0 E B hell hsSob hcSob hC0
        haction hcoeff hcoercive hscreen
  exact J.jointCommutator_firstPositiveEigenvalue_tendsto_of_normalOperatorConvergence_of_graphScreens
    c L A lam0 hlam0 D hD source hsource hnormal a ha screen hcompact htail hfst
      b hb P hprotected hprotectedRank hstarP hinfinite

end NCG.VaryingHilbert.System
