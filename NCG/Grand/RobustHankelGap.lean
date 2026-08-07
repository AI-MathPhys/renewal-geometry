/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Singular-gap certification of predictive rank
  (`thm:robust-hankel-gap`, Gran-Tensor manuscript)

* `robust_hankel_gap`:
  (1) the boxed perturbed-gap transfer: from the Weyl
      singular-value stability `|σ_j(H̃) − σ_j(H)| ≤ ε` with
      `σ_d(H) ≥ γ` and `σ_{d+1}(H) = 0`, exactly
      `σ_d(H̃) ≥ γ − ε` and `σ_{d+1}(H̃) ≤ ε`;
  (2) threshold certification: an ordered singular family with
      the two-sided gap (`σ_j ≥ γ−ε` below `d`, `σ_j ≤ ε` from
      `d` on) recovers the exact rank `d` by counting values
      above any threshold in `(ε, γ−ε)`;
  (3) non-robustness without a gap: an explicit family of
      rank-one matrices with least singular value `1/(k+1) → 0`
      while the limit matrix has rank zero.

Rendering disclosed: the Weyl singular-value perturbation
inequality itself is the classical variational input, declared
as the stability hypothesis of clause (1) (Mathlib has no
singular-value calculus); the identification of predictive
rank/flat depth with the Hankel rank is the proved Kalman
layer of the earlier Hankel records.
-/

open Matrix

namespace NCG

/-- `thm:robust-hankel-gap`. -/
theorem robust_hankel_gap :
    -- (1) the boxed gap transfer from Weyl stability
    (∀ σH σH' γ ε : ℝ, |σH' - σH| ≤ ε → γ ≤ σH →
      γ - ε ≤ σH')
    ∧ (∀ σH σH' ε : ℝ, |σH' - σH| ≤ ε → σH = 0 →
        σH' ≤ ε)
    -- (2) threshold certification of the exact rank
    ∧ (∀ (N d : ℕ) (σ : Fin N → ℝ) (γ ε τ : ℝ),
        d ≤ N → ε < τ → τ < γ - ε →
        (∀ j : Fin N, (j : ℕ) < d → γ - ε ≤ σ j) →
        (∀ j : Fin N, d ≤ (j : ℕ) → σ j ≤ ε) →
        (Finset.univ.filter fun j : Fin N => τ < σ j).card
          = d)
    -- (3) rank is not robust without a positive least
    --     singular value
    ∧ ((∀ k : ℕ, (Matrix.diagonal
          (fun _ : Fin 1 => (1 : ℝ) / (k + 1))).rank = 1)
        ∧ (0 : Matrix (Fin 1) (Fin 1) ℝ).rank = 0
        ∧ Filter.Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1))
            Filter.atTop (nhds 0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σH σH' γ ε hW hγ
    have := abs_le.mp hW
    linarith [this.1]
  · intro σH σH' ε hW h0
    have := abs_le.mp hW
    linarith [this.2]
  · intro N d σ γ ε τ hdN hετ hτγ hbig hsmall
    have hset : (Finset.univ.filter fun j : Fin N => τ < σ j)
        = Finset.univ.filter fun j : Fin N => (j : ℕ) < d := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hτσ
        by_contra hd
        have hle := hsmall j (le_of_not_gt hd)
        linarith
      · intro hjd
        have hge := hbig j hjd
        linarith
    rw [hset]
    have hequiv : {j : Fin N // (j : ℕ) < d} ≃ Fin d :=
      { toFun := fun j => ⟨(j : ℕ), j.2⟩
        invFun := fun i =>
          ⟨⟨(i : ℕ), lt_of_lt_of_le i.2 hdN⟩, i.2⟩
        left_inv := fun j => by
          ext
          rfl
        right_inv := fun i => by
          ext
          rfl }
    calc (Finset.univ.filter
          fun j : Fin N => (j : ℕ) < d).card
        = Fintype.card {j : Fin N // (j : ℕ) < d} :=
          (Fintype.card_subtype _).symm
      _ = Fintype.card (Fin d) := Fintype.card_congr hequiv
      _ = d := Fintype.card_fin d
  · intro k
    classical
    rw [Matrix.rank_diagonal]
    rw [show Fintype.card
        {i : Fin 1 // (1 : ℝ) / (k + 1) ≠ 0} = 1 from ?_]
    have hne : (1 : ℝ) / (k + 1) ≠ 0 := by positivity
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨0, hne⟩, fun j =>
      Subtype.ext (Subsingleton.elim (α := Fin 1) j.1 _)⟩
  · exact Matrix.rank_zero
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

end NCG
