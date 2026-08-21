/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CollectivelyCompactEventualScreenTransport
import NCG.Grand.GraphScreenMassEscape
import NCG.Grand.OperatorGraphResolventGraphScreen
import NCG.Grand.CompressedOperatorNormConvergence

/-!
# Compact-screen or mass-escape alternative for operator graph resolvents

This is the asymptotic screen formulation used in the Gran-Tensor manuscript. Uniform graph-tail
tightness only needs to hold eventually in the cutoff: finitely many early stage graph maps are
absorbed using stagewise compactness. If tightness fails, the same data produce cofinal screen
radii, cofinal cutoffs, unit-bounded sources, and a fixed positive escaped graph-tail norm.
-/

open Filter Set Topology

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

/-- Eventual compact-screen tails for the canonical weak-resolvent graph maps imply collective
compactness of the physical resolvents. -/
theorem operatorGraphResolvent_collectivelyCompact_of_eventual_graphScreenTails
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
    (hstage : ∀ n, IsCompactOperator
      (L.embeddedOperator
        (fun m ↦ operatorGraphResolventHilbertGraph
          (Dn m) (An m) (Rn m) lam hlam (hEquation m)) n))
    (hcompact : ∀ cutoff, IsCompactOperator (screen cutoff))
    (htail : ∀ ε > 0, ∃ cutoff,
      ∀ᶠ n in atTop, ∀ y ∈
        L.embeddedOperator
          (fun m ↦ operatorGraphResolventHilbertGraph
            (Dn m) (An m) (Rn m) lam hlam (hEquation m)) n ''
            Metric.closedBall 0 1,
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
  have hprojected :=
    L.collectivelyCompact_postcomp_of_eventually_compactOperator_screens J
      graphRn screen (2 * (1 + 1 / lam))
      (fun n ↦ WithLp.fstL 2 K (Hn n) (Fn n))
      (WithLp.fstL 2 K H F)
      hbounded
      (by simpa only [graphRn] using hstage)
      hcompact
      (by simpa only [graphRn] using htail)
      hfst
  simpa only [graphRn, fstL_comp_operatorGraphResolventHilbertGraph] using hprojected

/-- The manuscript's monotone eventual graph-screen tightness condition implies collective
compactness. -/
theorem operatorGraphResolvent_collectivelyCompact_of_uniformGraphScreenTight
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
    (hstage : ∀ n, IsCompactOperator
      (L.embeddedOperator
        (fun m ↦ operatorGraphResolventHilbertGraph
          (Dn m) (An m) (Rn m) lam hlam (hEquation m)) n))
    (hcompact : ∀ cutoff, IsCompactOperator (screen cutoff))
    (htight : NCG.VaryingHilbert.UniformGraphScreenTight
      (fun n f ↦ L.embedding n
        (operatorGraphResolventHilbertGraph
          (Dn n) (An n) (Rn n) lam hlam (hEquation n) f))
      (fun cutoff y ↦ y - screen cutoff y)
      (fun _ f ↦ ‖f‖ ≤ 1))
    (hfst : ∀ n y, J.embedding n y.fst = (L.embedding n y).fst) :
    J.CollectivelyCompact Rn := by
  apply J.operatorGraphResolvent_collectivelyCompact_of_eventual_graphScreenTails
    L Dn An Rn lam hlam hEquation screen hstage hcompact
  · intro ε hε
    obtain ⟨cutoff, hcutoff⟩ := htight ε hε
    refine ⟨cutoff, ?_⟩
    filter_upwards [hcutoff cutoff le_rfl] with n hn
    intro y hy
    obtain ⟨f, hf, rfl⟩ := hy
    apply hn f
    simpa only [Metric.mem_closedBall, dist_zero_right] using hf
  · exact hfst

/-- Exact positive-or-negative compact-screen alternative. In the positive branch the physical
resolvents are collectively compact. In the negative branch, graph mass escapes by one fixed
positive amount along cofinal screen radii and cofinal cutoff indices. -/
theorem operatorGraphResolvent_collectivelyCompact_or_massEscape
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
    (hstage : ∀ n, IsCompactOperator
      (L.embeddedOperator
        (fun m ↦ operatorGraphResolventHilbertGraph
          (Dn m) (An m) (Rn m) lam hlam (hEquation m)) n))
    (hcompact : ∀ cutoff, IsCompactOperator (screen cutoff))
    (hfst : ∀ n y, J.embedding n y.fst = (L.embedding n y).fst) :
    J.CollectivelyCompact Rn ∨
      ∃ ε > 0, ∃ radius cutoff : ℕ → ℕ,
        ∃ f : ∀ j, Hn (cutoff j),
          Tendsto radius atTop atTop ∧ Tendsto cutoff atTop atTop ∧
          ∀ j, ‖f j‖ ≤ 1 ∧
            ε ≤ ‖L.embedding (cutoff j)
                (operatorGraphResolventHilbertGraph
                  (Dn (cutoff j)) (An (cutoff j)) (Rn (cutoff j))
                  lam hlam (hEquation (cutoff j)) (f j)) -
              screen (radius j)
                (L.embedding (cutoff j)
                  (operatorGraphResolventHilbertGraph
                    (Dn (cutoff j)) (An (cutoff j)) (Rn (cutoff j))
                    lam hlam (hEquation (cutoff j)) (f j)))‖ := by
  let graph : ∀ n, Hn n → WithLp 2 (H × F) := fun n f ↦
    L.embedding n
      (operatorGraphResolventHilbertGraph
        (Dn n) (An n) (Rn n) lam hlam (hEquation n) f)
  let tail : ℕ → WithLp 2 (H × F) → WithLp 2 (H × F) :=
    fun cutoff y ↦ y - screen cutoff y
  let admissible : ∀ n, Hn n → Prop := fun _ f ↦ ‖f‖ ≤ 1
  by_cases htight : NCG.VaryingHilbert.UniformGraphScreenTight
      graph tail admissible
  · left
    apply J.operatorGraphResolvent_collectivelyCompact_of_uniformGraphScreenTight
      L Dn An Rn lam hlam hEquation screen hstage hcompact
    · simpa only [graph, tail, admissible] using htight
    · exact hfst
  · right
    simpa only [graph, tail, admissible] using
      NCG.VaryingHilbert.massEscape_of_not_uniformGraphScreenTight
        graph tail admissible htight

end NCG.VaryingHilbert.System
