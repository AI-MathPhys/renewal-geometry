/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PredictiveAlternative
import NCG.Grand.HankelMinimality
import Mathlib.Data.ENat.Lattice

/-!
# The finite/infinite Hankel-rank alternative

This module defines the rank of an exhaustive infinite Hankel table as the
supremum of its finite panel ranks.  It proves stabilization in the finite
case, exclusion of every fixed finite predictor in the infinite case, and an
explicit family showing that an observed finite panel cannot rule out later
independent innovations.
-/

open Matrix Set

namespace NCG

/-- Extended-natural rank of an exhaustive family of finite Hankel panels. -/
noncomputable def totalPanelRank (d : ℕ → ℕ) : ℕ∞ :=
  ⨆ n, (d n : ℕ∞)

theorem panelRank_le_total (d : ℕ → ℕ) (n : ℕ) :
    (d n : ℕ∞) ≤ totalPanelRank d :=
  le_iSup (fun k => (d k : ℕ∞)) n

/-- The infinite Hankel rank is infinite exactly when the finite panel ranks
are unbounded. -/
theorem totalPanelRank_eq_top_iff (d : ℕ → ℕ) :
    totalPanelRank d = ⊤ ↔ ¬ BddAbove (Set.range d) := by
  exact ENat.iSup_coe_eq_top

/-- If the total rank is the finite integer `D`, monotone panel ranks
eventually stabilize at `D`. -/
theorem finite_totalPanelRank_stabilizes
    (d : ℕ → ℕ) (D : ℕ) (hmono : Monotone d)
    (htotal : totalPanelRank d = (D : ℕ∞)) :
    ∃ N, ∀ n, N ≤ n → d n = d N := by
  have hbound : ∀ n, d n ≤ D := by
    intro n
    exact_mod_cast (panelRank_le_total d n).trans_eq htotal
  exact (predictive_alternative.2.1 d D hmono hbound)

/-- Infinite total rank contradicts the rank bound supplied by every fixed
finite-dimensional factorization. -/
theorem infinite_totalPanelRank_excludes_finite_predictor
    (d : ℕ → ℕ) (htop : totalPanelRank d = ⊤) :
    ∀ D : ℕ, ¬ (∀ n, d n ≤ D) := by
  intro D hD
  have hbdd : BddAbove (Set.range d) := by
    refine ⟨D, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hD n
  exact (totalPanelRank_eq_top_iff d).mp htop hbdd

/-- Canonical embedding of an observed `N`-panel into a later `N + k` panel. -/
def initialPanelEmbedding (N k : ℕ) : Fin N → Fin (N + k) :=
  Fin.castLE (Nat.le_add_right N k)

/-- The initial identity Hankel panel is literally unchanged inside every
larger identity panel. -/
theorem enlargedIdentity_initialPanel (N k : ℕ) :
    (1 : Matrix (Fin (N + k)) (Fin (N + k)) ℝ).submatrix
        (initialPanelEmbedding N k) (initialPanelEmbedding N k)
      = (1 : Matrix (Fin N) (Fin N) ℝ) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.one_apply,
    initialPanelEmbedding, Fin.castLE_inj]

/-- No finite panel can certify absence of later innovations: for every
observed size `N` and every requested extra rank `k`, a later panel has the
same observed corner and rank exactly `N + k`. -/
theorem finitePanel_does_not_certify_globalRank (N k : ℕ) :
    ∃ (A : Matrix (Fin (N + k)) (Fin (N + k)) ℝ),
      A.submatrix (initialPanelEmbedding N k) (initialPanelEmbedding N k)
          = (1 : Matrix (Fin N) (Fin N) ℝ)
      ∧ A.rank = N + k := by
  refine ⟨1, enlargedIdentity_initialPanel N k, ?_⟩
  simp

/-- Exact finite/infinite rank dichotomy for exhaustive monotone panels. -/
theorem infiniteHankelRankAlternative (d : ℕ → ℕ) (hmono : Monotone d) :
    ((∃ D : ℕ, totalPanelRank d = (D : ℕ∞)) →
      ∃ N, ∀ n, N ≤ n → d n = d N)
    ∧ (totalPanelRank d = ⊤ →
      ∀ D : ℕ, ¬ (∀ n, d n ≤ D))
    ∧ (∀ N k : ℕ, ∃ (A : Matrix (Fin (N + k)) (Fin (N + k)) ℝ),
      A.submatrix (initialPanelEmbedding N k) (initialPanelEmbedding N k)
          = (1 : Matrix (Fin N) (Fin N) ℝ)
      ∧ A.rank = N + k) := by
  refine ⟨?_, infinite_totalPanelRank_excludes_finite_predictor d, ?_⟩
  · rintro ⟨D, hD⟩
    exact finite_totalPanelRank_stabilizes d D hmono hD
  · exact finitePanel_does_not_certify_globalRank

end NCG
