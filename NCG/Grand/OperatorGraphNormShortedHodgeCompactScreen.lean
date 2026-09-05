/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphNormCompactScreenCollectiveCompactness
import NCG.Grand.LinearMapShortedHodgeGraphScreenTail

/-!
# Compact resolvents from shorted-Hodge control of graph-energy balls

This module connects the shorted-Hodge Sobolev screen estimate to the exact
operator graph-norm carrier.  Coercivity and a spectral-tail identity on the
union of embedded graph-energy unit balls give a uniform screen tail, hence
collective compactness of the physical weak resolvents.
-/

open Filter Set Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w z z' e x

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
variable {F : Type z} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]
variable {Fn : ℕ → Type z'}
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace ℂ (Fn n)]
variable {E : Type e} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A shorted-Hodge Sobolev estimate on the full graph-energy unit balls
implies collective compactness of the physical resolvents. -/
theorem operatorGraphResolvent_collectivelyCompact_of_graphNorm_shortedHodge
    {ι : Type x} [Fintype ι]
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (L : System (K := ℂ) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Dn : ∀ n, Submodule ℂ (Hn n))
    (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (Rn : ∀ n, Hn n →L[ℂ] Hn n)
    (lam : ℝ) (hlam : 0 < lam)
    (hEquation : ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Rn n f))
    (ell : ι → ℝ)
    (screen : ℕ → WithLp 2 (H × F) →L[ℂ] WithLp 2 (H × F))
    (coeff : WithLp 2 (H × F) →L[ℂ] EuclideanSpace ℂ ι)
    (action : WithLp 2 (H × F) →L[ℂ] E)
    (s c C0 : ℝ)
    (hell : ∀ j, 0 ≤ ell j) (hs : 0 < s) (hc : 0 < c)
    (hC0 : 0 ≤ C0)
    (hcoercive : ∀ y ∈
      L.embeddedUnitBallOutputs
        (fun n ↦ operatorGraphNormInclusion (Dn n) (An n)),
      c * NCG.RenewalShortedHodgeAndCompactScreen.spectralSobolevEnergy
          ell s (coeff y) -
        C0 * (∑ j, Complex.normSq (coeff y j)) ≤ ‖action y‖ ^ 2)
    (hscreen : ∀ radius y, y ∈
      L.embeddedUnitBallOutputs
        (fun n ↦ operatorGraphNormInclusion (Dn n) (An n)) →
      ‖y - screen radius y‖ ^ 2 =
        NCG.RenewalShortedHodgeAndCompactScreen.spectralTailNormSq
          ell (radius : ℝ) (coeff y))
    (hcompact : ∀ radius, IsCompactOperator (screen radius))
    (hfst : ∀ n y, J.embedding n y.fst = (L.embedding n y).fst) :
    J.CollectivelyCompact Rn := by
  let S : Set (WithLp 2 (H × F)) :=
    L.embeddedUnitBallOutputs
      (fun n ↦ operatorGraphNormInclusion (Dn n) (An n))
  have hbounded : S ⊆ Metric.closedBall 0 1 := by
    simpa only [S] using
      embeddedUnitBallOutputs_operatorGraphNormInclusion_subset_closedBall
        L Dn An
  have htail : ∀ ε > 0, ∃ radius, ∀ y ∈ S,
      ‖y - screen radius y‖ < ε := by
    apply NCG.VaryingHilbert.graphScreenTail_of_linearMap_shortedHodgeSobolevBound
      ell screen S coeff action s c C0 1
      hell hs hc hC0 (by positivity) hbounded
    · simpa only [S] using hcoercive
    · simpa only [S] using hscreen
  apply J.operatorGraphResolvent_collectivelyCompact_of_graphNormScreenTails
    L Dn An Rn lam hlam hEquation screen hcompact
  · simpa only [S] using htail
  · exact hfst

end NCG.VaryingHilbert.System
