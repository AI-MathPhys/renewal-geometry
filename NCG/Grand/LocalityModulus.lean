/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Incomplete-panel locality modulus
  (`thm:locality-modulus`, Gran-Tensor manuscript)

* `locality_modulus`: for the set of positive connected-panel
  completions compatible with the measured constraints, with
  `nz c A` the predicate "support `A` is nonzero in completion
  `c`":
  (i) the forced hypergraph (nonzero in every completion) is
      contained in every admissible interaction hypergraph;
  (ii) every admissible hypergraph is contained in the
      possible hypergraph (nonzero in at least one
      completion);
  (iii) if forced and possible coincide, the interaction
      hypergraph is identified: all completions have the same
      support set.

The graph-distance modulus reading and the compactness of the
completion set are the manuscript's packaging of this
sandwich.
-/

namespace NCG

/-- `thm:locality-modulus`. -/
theorem locality_modulus {C S : Type*} (comp : Set C)
    (nz : C → S → Prop) :
    -- (i) forced ⊆ every admissible support set
    (∀ c ∈ comp,
      {A | ∀ c' ∈ comp, nz c' A} ⊆ {A | nz c A})
    -- (ii) every admissible support set ⊆ possible
    ∧ (∀ c ∈ comp,
        {A | nz c A} ⊆ {A | ∃ c' ∈ comp, nz c' A})
    -- (iii) forced = possible identifies the hypergraph
    ∧ ({A | ∀ c' ∈ comp, nz c' A}
          = {A | ∃ c' ∈ comp, nz c' A} →
        ∀ c ∈ comp, ∀ c' ∈ comp,
          {A | nz c A} = {A | nz c' A}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc A hA
    exact hA c hc
  · intro c hc A hA
    exact ⟨c, hc, hA⟩
  · intro heq c hc c' hc'
    ext A
    constructor
    · intro hA
      have hposs : A ∈ {A | ∃ c'' ∈ comp, nz c'' A} :=
        ⟨c, hc, hA⟩
      have hforced : A ∈ {A | ∀ c'' ∈ comp, nz c'' A} := by
        rw [heq]
        exact hposs
      exact hforced c' hc'
    · intro hA
      have hposs : A ∈ {A | ∃ c'' ∈ comp, nz c'' A} :=
        ⟨c', hc', hA⟩
      have hforced : A ∈ {A | ∀ c'' ∈ comp, nz c'' A} := by
        rw [heq]
        exact hposs
      exact hforced c hc

end NCG
