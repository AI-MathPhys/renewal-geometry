/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorGraphNormShortedHodgeCompactScreen
import NCG.Grand.OperatorGraphResolventDenseRange
import NCG.Grand.VaryingHilbertCompressedSpectralConsequences

/-!
# Joint-commutator spectral convergence from full graph-energy screens

Full graph-energy shorted-Hodge control of the finite joint commutators is
compiled into the automatic-circle spectral package on the common physical
carrier.
-/

open Complex Filter Set Topology
open NCG.ResolventStability

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w x y

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Shorted-Hodge coercivity and spectral-tail identification on the full
joint-commutator graph-energy balls imply the complete automatic-circle
spectral approximation package. -/
theorem jointCommutatorResolvent_fullSpectralConsequences_of_graphNorm_shortedHodge
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {q : ℕ}
    (c : ∀ cutoff, Fin q → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun cutoff ↦ WithLp 2
        (EuclideanSpace ℂ (d cutoff × d cutoff) ×
          EuclideanSpace ℂ (Fin q × (d cutoff × d cutoff)))))
    (a : ℝ) (ha : 0 < a)
    {ι : Type x} [Fintype ι]
    (ell : ι → ℝ)
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (coeff : WithLp 2 (H × F) →L[ℂ] EuclideanSpace ℂ ι)
    (action : WithLp 2 (H × F) →L[ℂ] E)
    (sSob cSob C0 : ℝ)
    (hell : ∀ j, 0 ≤ ell j) (hsSob : 0 < sSob) (hcSob : 0 < cSob)
    (hC0 : 0 ≤ C0)
    (hcoercive : ∀ y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphNormInclusion
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))),
      cSob * NCG.RenewalShortedHodgeAndCompactScreen.spectralSobolevEnergy
          ell sSob (coeff y) -
        C0 * (∑ j, Complex.normSq (coeff y j)) ≤ ‖action y‖ ^ 2)
    (hscreen : ∀ radius y, y ∈ L.embeddedUnitBallOutputs
      (fun cutoff ↦ operatorGraphNormInclusion
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))) →
      ‖y - screen radius y‖ ^ 2 =
        NCG.RenewalShortedHodgeAndCompactScreen.spectralTailNormSq
          ell (radius : ℝ) (coeff y))
    (hcompact : ∀ radius, IsCompactOperator (screen radius))
    (hfst : ∀ cutoff y,
      J.embedding cutoff y.fst = (L.embedding cutoff y).fst)
    (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J
      (NCG.jointCommutatorResolventFamily c a) T)
    (hlimSymm : LinearMap.IsSymmetric T.toLinearMap)
    (center : ℂ) (hcenter : center ≠ 0)
    {κ : Type y} (source : ℕ → κ → H) (sourceLim : κ → H)
    (hsource : ∀ i, Tendsto (fun n ↦ source n i) atTop (𝓝 (sourceLim i))) :
    ∃ radius : ℝ, 0 < radius ∧
      (0 : ℂ) ∉ Metric.closedBall center radius ∧
      (∀ z ∈ Metric.sphere center radius, z ∈ resolventSet ℂ T) ∧
      IsCompactOperator T ∧
      LinearMap.range (circleRieszProjection T center radius).toLinearMap =
        Module.End.eigenspace T.toLinearMap center ∧
      Tendsto
        (J.compressedOperator (NCG.jointCommutatorResolventFamily c a))
        atTop (𝓝 T) ∧
      Tendsto
        (fun n ↦ circleRieszProjection
          (J.compressedOperator
            (NCG.jointCommutatorResolventFamily c a) n) center radius)
        atTop (𝓝 (circleRieszProjection T center radius)) ∧
      (∀ᶠ n in atTop,
        Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection
                (J.compressedOperator
                  (NCG.jointCommutatorResolventFamily c a) n)
                center radius).toLinearMap) =
          Module.finrank ℂ
            (LinearMap.range
              (circleRieszProjection T center radius).toLinearMap)) ∧
      Tendsto
        (fun n ↦ NCG.SpectralApproximation.sourceGram
          (circleRieszProjection
            (J.compressedOperator
              (NCG.jointCommutatorResolventFamily c a) n)
            center radius) (source n)) atTop
        (𝓝 (NCG.SpectralApproximation.sourceGram
          (circleRieszProjection T center radius) sourceLim)) := by
  have hcollective : J.CollectivelyCompact
      (NCG.jointCommutatorResolventFamily c a) :=
    J.jointCommutatorResolvent_collectivelyCompact_of_graphNorm_shortedHodge
      c L a ha ell screen coeff action sSob cSob C0
      hell hsSob hcSob hC0 hcoercive hscreen hcompact hfst
  exact J.compressedOperator_spectralConsequences_of_collectivelyCompact_automaticCircle
    (NCG.jointCommutatorResolventFamily c a) T hdense hstrong hcollective
      (fun cutoff ↦ operatorGraphResolvent_isSymmetric
        (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
        (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
        a (NCG.jointCommutatorResolventFamily c a cutoff)
        (NCG.jointCommutatorResolventFamily_resolventEquation c a ha cutoff))
      hlimSymm center hcenter source sourceLim hsource

end NCG.VaryingHilbert.System
