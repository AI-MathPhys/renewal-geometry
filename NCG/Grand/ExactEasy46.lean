/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.LocalityModulus

/-!
# Exact EASY 46: incomplete-panel locality modulus

This file instantiates the abstract support sandwich with the manuscript's
actual objects: positive semidefinite matrix completions satisfying measured
linear constraints, connected-support functionals, their two-section graphs,
and the induced extended graph distances.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

variable {I V M : Type*} [Fintype I] [DecidableEq I]

/-- Positive connected-panel completions satisfying every measured linear
constraint. -/
def connectedPanelCompletions
    (measure : M -> (Matrix I I Complex →ₗ[Complex] Complex))
    (observed : M -> Complex) : Set (Matrix I I Complex) :=
  {K | K.PosSemidef ∧ ∀ m, measure m K = observed m}

/-- The operational two-section graph of one completed connected panel.
An edge is present when some connected support containing both endpoints has
nonzero coefficient. -/
def completedPanelGraph
    (coeff : Finset V -> (Matrix I I Complex →ₗ[Complex] Complex))
    (K : Matrix I I Complex) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ A : Finset V,
    u ∈ A ∧ v ∈ A ∧ coeff A K ≠ 0
  symm := ⟨by
    intro u v h
    exact ⟨Ne.symm h.1, by
      obtain ⟨A, hu, hv, hnz⟩ := h.2
      exact ⟨A, hv, hu, hnz⟩⟩⟩
  loopless := ⟨by
    intro u h
    exact h.1 rfl⟩

/-- The forced two-section graph: a support coefficient must be nonzero in
every feasible positive completion. -/
def forcedPanelGraph
    (comp : Set (Matrix I I Complex))
    (coeff : Finset V -> (Matrix I I Complex →ₗ[Complex] Complex)) :
    SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ A : Finset V,
    u ∈ A ∧ v ∈ A ∧ ∀ K ∈ comp, coeff A K ≠ 0
  symm := ⟨by
    intro u v h
    exact ⟨Ne.symm h.1, by
      obtain ⟨A, hu, hv, hnz⟩ := h.2
      exact ⟨A, hv, hu, hnz⟩⟩⟩
  loopless := ⟨by
    intro u h
    exact h.1 rfl⟩

/-- The possible two-section graph: a support coefficient is nonzero in at
least one feasible positive completion. -/
def possiblePanelGraph
    (comp : Set (Matrix I I Complex))
    (coeff : Finset V -> (Matrix I I Complex →ₗ[Complex] Complex)) :
    SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ A : Finset V,
    u ∈ A ∧ v ∈ A ∧ ∃ K ∈ comp, coeff A K ≠ 0
  symm := ⟨by
    intro u v h
    exact ⟨Ne.symm h.1, by
      obtain ⟨A, hu, hv, hnz⟩ := h.2
      exact ⟨A, hv, hu, hnz⟩⟩⟩
  loopless := ⟨by
    intro u h
    exact h.1 rfl⟩

/-- The exact graph sandwich, identification criterion, and lower/upper
extended graph-distance functions of `thm:locality-modulus`. -/
theorem locality_modulus_exact
    (measure : M -> (Matrix I I Complex →ₗ[Complex] Complex))
    (observed : M -> Complex)
    (coeff : Finset V -> (Matrix I I Complex →ₗ[Complex] Complex))
    (hcompact : IsCompact (connectedPanelCompletions measure observed)) :
    (∀ K ∈ connectedPanelCompletions measure observed,
      forcedPanelGraph (connectedPanelCompletions measure observed) coeff
        ≤ completedPanelGraph coeff K)
    ∧ (∀ K ∈ connectedPanelCompletions measure observed,
        completedPanelGraph coeff K
          ≤ possiblePanelGraph (connectedPanelCompletions measure observed)
            coeff)
    ∧ (forcedPanelGraph (connectedPanelCompletions measure observed) coeff
          = possiblePanelGraph (connectedPanelCompletions measure observed)
            coeff ->
        ∀ K ∈ connectedPanelCompletions measure observed,
          completedPanelGraph coeff K
            = forcedPanelGraph
              (connectedPanelCompletions measure observed) coeff)
    ∧ (∀ K ∈ connectedPanelCompletions measure observed, ∀ u v,
        (possiblePanelGraph
            (connectedPanelCompletions measure observed) coeff).edist u v
          ≤ (completedPanelGraph coeff K).edist u v
        ∧ (completedPanelGraph coeff K).edist u v
          ≤ (forcedPanelGraph
            (connectedPanelCompletions measure observed) coeff).edist u v) := by
  let comp := connectedPanelCompletions measure observed
  have hforced : ∀ K ∈ comp,
      forcedPanelGraph comp coeff ≤ completedPanelGraph coeff K := by
    intro K hK u v huv
    change u ≠ v ∧ ∃ A : Finset V,
      u ∈ A ∧ v ∈ A ∧ ∀ K ∈ comp, coeff A K ≠ 0 at huv
    change u ≠ v ∧ ∃ A : Finset V,
      u ∈ A ∧ v ∈ A ∧ coeff A K ≠ 0
    exact ⟨huv.1, by
      obtain ⟨A, hu, hv, hall⟩ := huv.2
      exact ⟨A, hu, hv, hall K hK⟩⟩
  have hpossible : ∀ K ∈ comp,
      completedPanelGraph coeff K ≤ possiblePanelGraph comp coeff := by
    intro K hK u v huv
    change u ≠ v ∧ ∃ A : Finset V,
      u ∈ A ∧ v ∈ A ∧ coeff A K ≠ 0 at huv
    change u ≠ v ∧ ∃ A : Finset V,
      u ∈ A ∧ v ∈ A ∧ ∃ K ∈ comp, coeff A K ≠ 0
    exact ⟨huv.1, by
      obtain ⟨A, hu, hv, hnz⟩ := huv.2
      exact ⟨A, hu, hv, K, hK, hnz⟩⟩
  refine ⟨hforced, hpossible, ?_, ?_⟩
  · intro heq K hK
    apply le_antisymm
    · rw [heq]
      exact hpossible K hK
    · exact hforced K hK
  · intro K hK u v
    exact ⟨SimpleGraph.edist_anti (hpossible K hK),
      SimpleGraph.edist_anti (hforced K hK)⟩

end NCG
