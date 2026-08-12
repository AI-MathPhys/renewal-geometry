/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Compact projective alternative and finite separator
  (`thm:projective-state-alternative`,
  Gran-Tensor manuscript)

* `projective_state_alternative`: for the finite-stage
  state sequence in the compact projective state space:
  (i) the cluster set `𝔖_∞` is nonempty;
  (ii) it is closed, hence (iii) compact;
  (iv) if it is a singleton, every scalar coordinate
      converges (the sequence converges to the unique
      cluster state);
  (v) two distinct cluster states are realized by two
      cofinal subsequences with the two subsequential
      limits — the finite-stage separator.

The exact finite-dimensional C-star state-space realization, Tychonoff
product, closed inverse-limit compatibility equations, coordinatewise
singleton criterion, and self-adjoint finite-stage separator are completed in
`NCG.Grand.FiniteProjectiveStateAlternative`.
-/

open Filter

namespace NCG

/-- `thm:projective-state-alternative`. -/
theorem projective_state_alternative {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (ω : ℕ → X) :
    -- (i) the cluster (limit-state) set is nonempty
    (∃ x, MapClusterPt x atTop ω)
    -- (ii) it is closed
    ∧ IsClosed {x | MapClusterPt x atTop ω}
    -- (iii) hence compact
    ∧ IsCompact {x | MapClusterPt x atTop ω}
    -- (iv) a singleton cluster set forces convergence
    ∧ (∀ {Y : Type} [MetricSpace Y] [CompactSpace Y]
        (u : ℕ → Y) (y : Y),
        {z | MapClusterPt z atTop u} = {y} →
        Tendsto u atTop (nhds y))
    -- (v) two cluster states give two subsequential limits
    ∧ (∀ {Y : Type} [MetricSpace Y] (u : ℕ → Y)
        (y₁ y₂ : Y),
        MapClusterPt y₁ atTop u →
        MapClusterPt y₂ atTop u →
        ∃ φ₁ φ₂ : ℕ → ℕ, StrictMono φ₁ ∧ StrictMono φ₂
          ∧ Tendsto (u ∘ φ₁) atTop (nhds y₁)
          ∧ Tendsto (u ∘ φ₂) atTop (nhds y₂)) := by
  have hclosed : IsClosed {x | MapClusterPt x atTop ω} :=
    isClosed_setOf_clusterPt
      (f := Filter.map ω atTop)
  refine ⟨?_, hclosed, hclosed.isCompact, ?_, ?_⟩
  · obtain ⟨x, _, hx⟩ :=
      isCompact_univ.exists_clusterPt
        (f := Filter.map ω atTop) (by simp)
    exact ⟨x, hx⟩
  · intro Y _ _ u y hset
    by_contra hnot
    rw [Metric.tendsto_atTop] at hnot
    push Not at hnot
    obtain ⟨ε, hε, hfreq⟩ := hnot
    have hfreq' : ∃ᶠ n in atTop, ε ≤ dist (u n) y := by
      rw [Filter.frequently_atTop]
      intro N
      obtain ⟨n, hn1, hn2⟩ := hfreq N
      exact ⟨n, hn1, hn2⟩
    obtain ⟨φ, hφ, hP⟩ :=
      Filter.extraction_of_frequently_atTop hfreq'
    obtain ⟨z, _, ψ, hψ, hz⟩ :=
      isCompact_univ.tendsto_subseq
        (x := u ∘ φ) (fun n => Set.mem_univ _)
    have hzc : MapClusterPt z atTop u := by
      refine MapClusterPt.of_comp
        (φ := φ ∘ ψ) ((hφ.comp hψ).tendsto_atTop) ?_
      exact (Tendsto.mapClusterPt (by
        simpa [Function.comp_assoc] using hz))
    have hzy : z = y := by
      have hmem : z ∈ {z | MapClusterPt z atTop u} := hzc
      rw [hset] at hmem
      exact hmem
    have hd : ε ≤ dist z y := by
      have hlim : Tendsto
          (fun n => dist ((u ∘ φ ∘ ψ) n) y) atTop
          (nhds (dist z y)) := by
        have h := hz.dist
          (tendsto_const_nhds (x := y) (f := atTop))
        simpa [Function.comp_assoc] using h
      refine le_of_tendsto_of_tendsto
        tendsto_const_nhds hlim
        (Eventually.of_forall fun n => ?_)
      exact hP (ψ n)
    rw [hzy] at hd
    simp only [dist_self] at hd
    linarith
  · intro Y _ u y₁ y₂ h1 h2
    obtain ⟨φ₁, hφ₁, hl₁⟩ := h1.tendsto_subseq
    obtain ⟨φ₂, hφ₂, hl₂⟩ := h2.tendsto_subseq
    exact ⟨φ₁, φ₂, hφ₁, hφ₂, hl₁, hl₂⟩

end NCG
