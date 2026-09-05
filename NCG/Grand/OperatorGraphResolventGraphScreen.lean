/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphResolventGraphMap
import NCG.Grand.CollectivelyCompactTransport

/-!
# Compact graph screens for weak graph resolvents

This module connects the literal graph-output operator supplied by a weak
resolvent equation to the varying-Hilbert compact-screen machinery.  A compact
screen for the pairs `(R f, A (R f))` therefore gives collective compactness of
the physical resolvents without requiring a separately postulated compactness
hypothesis.
-/

open Set

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w z z'

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable {F : Type z} [NormedAddCommGroup F] [InnerProductSpace K F]
  [CompleteSpace F]
variable {Fn : ℕ → Type z'}
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace K (Fn n)]
omit [CompleteSpace H] [CompleteSpace F] in
/-- The embedded unit-ball outputs of every canonical weak-resolvent graph map lie in one
explicit common-carrier ball. -/
theorem embeddedUnitBallOutputs_operatorGraphResolventHilbertGraph_subset_closedBall
    (L : System (K := K) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Dn : ∀ n, Submodule K (Hn n))
    (An : ∀ n, Dn n →ₗ[K] Fn n)
    (Rn : ∀ n, Hn n →L[K] Hn n)
    (lam : ℝ) (hlam : 0 < lam)
    (hEquation : ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Rn n f)) :
    L.embeddedUnitBallOutputs
      (fun n ↦ operatorGraphResolventHilbertGraph
        (Dn n) (An n) (Rn n) lam hlam (hEquation n)) ⊆
      Metric.closedBall 0 (2 * (1 + 1 / lam)) := by
  let graphRn : ∀ n, Hn n →L[K] WithLp 2 (Hn n × Fn n) :=
    fun n ↦ operatorGraphResolventHilbertGraph
      (Dn n) (An n) (Rn n) lam hlam (hEquation n)
  intro y hy
  rw [embeddedUnitBallOutputs] at hy
  obtain ⟨n, x, hx, rfl⟩ := Set.mem_iUnion.mp hy
  have hxnorm : ‖x‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  rw [Metric.mem_closedBall, dist_zero_right, embeddedOperator_apply,
    (L.embedding n).norm_map]
  calc
    ‖graphRn n x‖ ≤ (2 * (1 + 1 / lam)) * ‖x‖ := by
      simpa only [graphRn] using
        norm_operatorGraphResolventHilbertGraph_le
          (Dn n) (An n) (Rn n) lam hlam (hEquation n) x
    _ ≤ (2 * (1 + 1 / lam)) * 1 :=
      mul_le_mul_of_nonneg_left hxnorm (by positivity)
    _ = 2 * (1 + 1 / lam) := by ring


/-- Compact screens for the canonical weak-resolvent graph outputs imply
collective compactness of the physical resolvent family. -/
theorem operatorGraphResolvent_collectivelyCompact_of_graphScreens
    (J : System (K := K) (H := H) (Hn := Hn))
    (L : System (K := K) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Dn : ∀ n, Submodule K (Hn n))
    (An : ∀ n, Dn n →ₗ[K] Fn n)
    (Rn : ∀ n, Hn n →L[K] Hn n)
    (lam : ℝ) (hlam : 0 < lam)
    (hEquation : ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Rn n f))
    (screen : ℕ → WithLp 2 (H × F) →L[K] WithLp 2 (H × F)) (B : ℝ)
    (hbounded : L.embeddedUnitBallOutputs
      (fun n ↦ operatorGraphResolventHilbertGraph
        (Dn n) (An n) (Rn n) lam hlam (hEquation n)) ⊆
        Metric.closedBall 0 B)
    (hcompact : ∀ R, IsCompactOperator (screen R))
    (htail : ∀ ε > 0, ∃ R, ∀ y ∈ L.embeddedUnitBallOutputs
      (fun n ↦ operatorGraphResolventHilbertGraph
        (Dn n) (An n) (Rn n) lam hlam (hEquation n)),
      ‖y - screen R y‖ < ε)
    (hfst : ∀ n y, J.embedding n y.fst = (L.embedding n y).fst) :
    J.CollectivelyCompact Rn := by
  let graphRn : ∀ n, Hn n →L[K] WithLp 2 (Hn n × Fn n) :=
    fun n ↦ operatorGraphResolventHilbertGraph
      (Dn n) (An n) (Rn n) lam hlam (hEquation n)
  have hprojected :=
    L.collectivelyCompact_postcomp_of_compactOperator_screens J
      graphRn screen B
      (fun n ↦ WithLp.fstL 2 K (Hn n) (Fn n))
      (WithLp.fstL 2 K H F)
      (by simpa only [graphRn] using hbounded)
      hcompact
      (by simpa only [graphRn] using htail)
      (by
        intro n y
        exact hfst n y)
  simpa only [graphRn, fstL_comp_operatorGraphResolventHilbertGraph] using hprojected

/-- For canonical weak-resolvent graph maps the uniform boundedness premise is
automatic, so a uniformly vanishing compact-screen tail alone gives collective
compactness of the physical resolvents. -/
theorem operatorGraphResolvent_collectivelyCompact_of_graphScreenTails
    (J : System (K := K) (H := H) (Hn := Hn))
    (L : System (K := K) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Dn : ∀ n, Submodule K (Hn n))
    (An : ∀ n, Dn n →ₗ[K] Fn n)
    (Rn : ∀ n, Hn n →L[K] Hn n)
    (lam : ℝ) (hlam : 0 < lam)
    (hEquation : ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Rn n f))
    (screen : ℕ → WithLp 2 (H × F) →L[K] WithLp 2 (H × F))
    (hcompact : ∀ cutoff, IsCompactOperator (screen cutoff))
    (htail : ∀ ε > 0, ∃ cutoff, ∀ y ∈ L.embeddedUnitBallOutputs
      (fun n ↦ operatorGraphResolventHilbertGraph
        (Dn n) (An n) (Rn n) lam hlam (hEquation n)),
      ‖y - screen cutoff y‖ < ε)
    (hfst : ∀ n y, J.embedding n y.fst = (L.embedding n y).fst) :
    J.CollectivelyCompact Rn := by
  let graphRn : ∀ n, Hn n →L[K] WithLp 2 (Hn n × Fn n) :=
    fun n ↦ operatorGraphResolventHilbertGraph
      (Dn n) (An n) (Rn n) lam hlam (hEquation n)
  have hbounded : L.embeddedUnitBallOutputs graphRn ⊆
      Metric.closedBall 0 (2 * (1 + 1 / lam)) := by
    simpa only [graphRn] using
      embeddedUnitBallOutputs_operatorGraphResolventHilbertGraph_subset_closedBall
        L Dn An Rn lam hlam hEquation
  apply J.operatorGraphResolvent_collectivelyCompact_of_graphScreens
    L Dn An Rn lam hlam hEquation screen (2 * (1 + 1 / lam))
  · simpa only [graphRn] using hbounded
  · exact hcompact
  · exact htail
  · exact hfst

end NCG.VaryingHilbert.System
