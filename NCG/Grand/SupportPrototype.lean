/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GramHelpers

/-!
# `S₄` prototype reduction, the intrinsic interaction
  hypergraph, and the four-cell orbit audit
  (`thm:S4-support-prototype`,
  `thm:intrinsic-interaction-hypergraph`, and
  `cor:four-cell-support-orbit-audit`,
  Gran-Tensor manuscript)

* `s4_support_prototype`: for a unitary covariance
  `C(g•A) = ρ_g ᴴ C(A) ρ_g` (the boxed display):
  (i) the covariance itself; (ii) vanishing of a panel is
  orbit-constant; (iii) under a transitive action one
  prototype panel decides every panel.

* `intrinsic_interaction_hypergraph`:
  (i) every retained support extends to a maximal retained
      support (the edge-minimal hypergraph `ℋ^min` exists
      and covers every retained response);
  (ii) maximality is invariant under every nonzero-preserving
      relabelling (support-minimal coordinate changes and
      unread refinements).

* `four_cell_support_orbit_audit`:
  (i)–(ii) `S₄` is transitive on pair and on triple supports
      (one prototype decides each level);
  (iii) under `S₄`-covariant zero-transport, the pairwise-`K₄`
      branch criterion: one nonzero pair prototype forces all
      six pairs; one zero triple prototype kills all four
      triples.
-/

open Matrix

namespace NCG

/-- `thm:S4-support-prototype`. -/
theorem s4_support_prototype {G I k : Type*} [Group G]
    [MulAction G I] [Fintype k] [DecidableEq k]
    (ρ : G → Matrix k k ℂ) (C : I → Matrix k k ℂ)
    (hρ : ∀ g, ρ g * (ρ g)ᴴ = 1 ∧ (ρ g)ᴴ * ρ g = 1)
    (hcov : ∀ (g : G) (A : I),
      C (g • A) = (ρ g)ᴴ * C A * ρ g) :
    -- (i) the boxed conjugation display
    (∀ (g : G) (A : I), C (g • A) = (ρ g)ᴴ * C A * ρ g)
    -- (ii) vanishing is orbit-constant
    ∧ (∀ (g : G) (A : I), (C (g • A) = 0 ↔ C A = 0))
    -- (iii) one prototype decides every panel
    ∧ ((∀ A B : I, ∃ g : G, g • A = B) →
        ∀ A B : I, (C A = 0 ↔ C B = 0)) := by
  have hiff : ∀ (g : G) (A : I),
      (C (g • A) = 0 ↔ C A = 0) := by
    intro g A
    constructor
    · intro h
      have h2 : (ρ g)ᴴ * C A * ρ g = 0 := by
        rw [← hcov g A]
        exact h
      have h3 := congrArg
        (fun X => ρ g * X * (ρ g)ᴴ) h2
      simp only [Matrix.mul_zero, Matrix.zero_mul] at h3
      rw [show ρ g * ((ρ g)ᴴ * C A * ρ g) * (ρ g)ᴴ
          = C A from by
        simp only [Matrix.mul_assoc, cancel_left (hρ g).1,
          (hρ g).1, Matrix.mul_one]] at h3
      exact h3
    · intro h
      rw [hcov g A, h, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨hcov, hiff, ?_⟩
  intro htrans A B
  obtain ⟨g, hg⟩ := htrans A B
  rw [← hg]
  exact (hiff g A).symm

/-- `thm:intrinsic-interaction-hypergraph`. -/
theorem intrinsic_interaction_hypergraph {α k : Type*}
    [Finite α] [DecidableEq α]
    (C : Finset α → Matrix k k ℂ) :
    -- (i) every retained support has a maximal extension
    (∀ A : Finset α, C A ≠ 0 →
      ∃ B : Finset α, C B ≠ 0 ∧ A ⊆ B
        ∧ ∀ B' : Finset α, C B' ≠ 0 → B ⊆ B' → B' = B)
    -- (ii) maximality transports along nonzero-preserving
    --      relabellings
    ∧ (∀ σ : α ≃ α,
        (∀ A : Finset α, (C (A.image σ) = 0 ↔ C A = 0)) →
        ∀ B : Finset α,
          (C B ≠ 0 ∧ ∀ B', C B' ≠ 0 → B ⊆ B' → B' = B) →
          (C (B.image σ) ≠ 0
            ∧ ∀ B', C B' ≠ 0 → B.image σ ⊆ B'
              → B' = B.image σ)) := by
  classical
  have _ := Fintype.ofFinite α
  constructor
  · intro A hA
    have hne : (Finset.univ.filter
        (fun B : Finset α => C B ≠ 0 ∧ A ⊆ B)).Nonempty :=
      ⟨A, by simp [hA]⟩
    obtain ⟨B, hBP, hBmax⟩ := Finset.exists_maximal hne
    rw [Finset.mem_filter] at hBP
    refine ⟨B, hBP.2.1, hBP.2.2, ?_⟩
    intro B' hB' hBB'
    have hB'mem : B' ∈ Finset.univ.filter
        (fun B : Finset α => C B ≠ 0 ∧ A ⊆ B) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hB', hBP.2.2.trans hBB'⟩
    exact le_antisymm (hBmax hB'mem hBB') hBB'
  · intro σ hσ B hB
    have hBσ : C (B.image σ) ≠ 0 := by
      intro h0
      exact hB.1 ((hσ B).mp h0)
    refine ⟨hBσ, ?_⟩
    intro B' hB' hsub
    have hB'' : C (B'.image σ.symm) ≠ 0 := by
      intro h0
      apply hB'
      have := (hσ (B'.image σ.symm)).mpr h0
      rwa [Finset.image_image,
        show (⇑σ ∘ ⇑σ.symm) = id from funext
          (fun x => σ.apply_symm_apply x),
        Finset.image_id] at this
    have hsub' : B ⊆ B'.image σ.symm := by
      intro x hx
      have : σ x ∈ B' := hsub
        (Finset.mem_image_of_mem σ hx)
      have h2 : σ.symm (σ x) ∈ B'.image σ.symm :=
        Finset.mem_image_of_mem _ this
      rwa [σ.symm_apply_apply] at h2
    have heq := hB.2 _ hB'' hsub'
    have := congrArg (fun s => Finset.image σ s) heq
    simpa [Finset.image_image,
      show (⇑σ ∘ ⇑σ.symm) = id from funext
        (fun x => σ.apply_symm_apply x)] using this

/-- `cor:four-cell-support-orbit-audit`. -/
theorem four_cell_support_orbit_audit {k : Type*}
    (C : Finset (Fin 4) → Matrix k k ℂ)
    (hzero : ∀ (σ : Equiv.Perm (Fin 4)) (A : Finset (Fin 4)),
      (C (A.image σ) = 0 ↔ C A = 0)) :
    -- (i) `S₄` is transitive on pair supports
    (∀ A B : Finset (Fin 4), A.card = 2 → B.card = 2 →
      ∃ σ : Equiv.Perm (Fin 4), A.image σ = B)
    -- (ii) and on triple supports
    ∧ (∀ A B : Finset (Fin 4), A.card = 3 → B.card = 3 →
        ∃ σ : Equiv.Perm (Fin 4), A.image σ = B)
    -- (iii) the pairwise-`K₄` branch criterion
    ∧ (C {0, 1} ≠ 0 →
        ∀ A : Finset (Fin 4), A.card = 2 → C A ≠ 0)
    ∧ (C {0, 1, 2} = 0 →
        ∀ A : Finset (Fin 4), A.card = 3 → C A = 0) := by
  have htrans2 : ∀ A B : Finset (Fin 4),
      A.card = 2 → B.card = 2 →
      ∃ σ : Equiv.Perm (Fin 4), A.image σ = B := by decide
  have htrans3 : ∀ A B : Finset (Fin 4),
      A.card = 3 → B.card = 3 →
      ∃ σ : Equiv.Perm (Fin 4), A.image σ = B := by decide
  refine ⟨htrans2, htrans3, ?_, ?_⟩
  · intro hproto A hA h0
    obtain ⟨σ, hσ⟩ := htrans2 A {0, 1} hA (by decide)
    apply hproto
    rw [← hσ]
    exact (hzero σ A).mpr h0
  · intro hproto A hA
    obtain ⟨σ, hσ⟩ := htrans3 {0, 1, 2} A (by decide) hA
    rw [← hσ]
    exact (hzero σ _).mpr hproto

end NCG
