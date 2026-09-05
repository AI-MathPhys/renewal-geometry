/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Analysis.ApproximationSingularValues
import NCG.Grand.RobustHankelGap

/-!
# Singular-gap certification of predictive rank

This file supplies the missing operator-norm Weyl input in the robust Hankel
gap theorem.  Singular values are represented by their equivalent best
low-rank approximation characterization; the sharp perturbation estimate is
therefore the one-Lipschitz estimate for distance to the rank-`k` locus.
-/

open Matrix

namespace NCG

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Exact robust Hankel-gap theorem, with one-indexed `σ_d` represented by
the zero-indexed approximation singular value at `d - 1`. -/
theorem singular_gap_predictive_rank
    (H Htilde : EuclideanOperator m n) (d : ℕ) (γ ε τ : ℝ)
    (hrank : euclideanOperatorRank H = d) (hd : 0 < d)
    (hγ : γ ≤ approximationSingularValue H (d - 1))
    (hγpos : 0 < γ) (hclose : ‖Htilde - H‖ ≤ ε)
    (heps : ε < γ / 2) (hετ : ε < τ) (hτγ : τ < γ - ε) :
    approximationSingularValue Htilde (d - 1) ≥ γ - ε
      ∧ approximationSingularValue Htilde d ≤ ε
      ∧ (Finset.univ.filter fun j : Fin (Fintype.card n) =>
          τ < approximationSingularValue Htilde j).card = d
      ∧ ((∀ k : ℕ, (Matrix.diagonal
            (fun _ : Fin 1 => (1 : ℝ) / (k + 1))).rank = 1)
          ∧ (0 : Matrix (Fin 1) (Fin 1) ℝ).rank = 0
          ∧ Filter.Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1))
              Filter.atTop (nhds 0)) := by
  have hW : ∀ j : ℕ,
      |approximationSingularValue Htilde j -
        approximationSingularValue H j| ≤ ε := by
    intro j
    exact (approximationSingularValue_weyl Htilde H j).trans hclose
  have hlower : γ - ε ≤ approximationSingularValue Htilde (d - 1) := by
    have habs := abs_le.mp (hW (d - 1))
    linarith [habs.1]
  have hHzero : approximationSingularValue H d = 0 :=
    approximationSingularValue_eq_zero_of_rank_le H d (by rw [hrank])
  have hupper : approximationSingularValue Htilde d ≤ ε := by
    have habs := abs_le.mp (hW d)
    linarith [habs.2]
  have hdN : d ≤ Fintype.card n := by
    calc
      d = Module.finrank ℂ H.range := hrank.symm
      _ ≤ Module.finrank ℂ (EuclideanSpace ℂ n) := H.toLinearMap.finrank_range_le
      _ = Fintype.card n := by simp
  have hbig : ∀ j : Fin (Fintype.card n), (j : ℕ) < d →
      γ - ε ≤ approximationSingularValue Htilde j := by
    intro j hj
    have hjle : (j : ℕ) ≤ d - 1 := Nat.le_sub_one_of_lt hj
    have hmono : approximationSingularValue H (d - 1) ≤
        approximationSingularValue H j :=
      approximationSingularValue_antitone H hjle
    have habs := abs_le.mp (hW j)
    linarith [hγ, hmono, habs.1]
  have hsmall : ∀ j : Fin (Fintype.card n), d ≤ (j : ℕ) →
      approximationSingularValue Htilde j ≤ ε := by
    intro j hj
    have hzero : approximationSingularValue H j = 0 :=
      approximationSingularValue_eq_zero_of_rank_le H j (by
        rw [hrank]
        exact hj)
    have habs := abs_le.mp (hW j)
    linarith [habs.2]
  have hcount := robust_hankel_gap.2.2.1
    (Fintype.card n) d
    (fun j : Fin (Fintype.card n) => approximationSingularValue Htilde j)
    γ ε τ hdN hετ hτγ hbig hsmall
  exact ⟨hlower, hupper, hcount, robust_hankel_gap.2.2.2⟩

end NCG
