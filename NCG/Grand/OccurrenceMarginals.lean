/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Typed and colour marginals do not select occurrence, and the
  occurrence environment rank
  (`cth:SM-occurrence-marginal-nonselection` and
  `cor:SM-occurrence-environment-rank`, Gran-Tensor manuscript)

* `occurrence_marginal_nonselection`: the interior scalar
  effect `(c/Tr G)·I` meets the conductance constraint; adding
  any conductance-null perturbation preserves it (so the
  feasible spectrahedron is not a point); one nonzero affine
  functional on the ten-dimensional real commutant cuts the
  dimension to exactly nine; and (contrast) the full joint
  state *does* separate effects when the source is faithful
  (invertible `G` cancels).
* `occurrence_environment_rank`: for a projection effect
  (0/1 diagonal `K`), `rank K + rank(I−K) = n`, so the
  environment rank `r_env = rank K + 15·rank(I−K)` is
  determined by the occurrence effect alone
  (`= rank K + 15(n − rank K)`).

Rendering disclosed: compactness of the spectrahedron and the
`1⊕15` conjugation decomposition are the manuscript's context;
the dimension-nine count is proved as the rank–nullity fact for
one nonzero affine functional on the ten-dimensional real
commutant, and the environment-rank formula is proved on the
spectral (0/1 diagonal) representation of the effect.
-/

open Matrix

namespace NCG

/-- `cth:SM-occurrence-marginal-nonselection`. -/
theorem occurrence_marginal_nonselection :
    -- (1) the interior scalar effect meets the conductance
    (∀ {n : Type} [Fintype n] [DecidableEq n]
      (G : Matrix n n ℂ) (c : ℂ), G.trace ≠ 0 →
      (G * ((c / G.trace) • 1)).trace = c)
    -- (2) conductance-null perturbations stay feasible
    ∧ (∀ {n : Type} [Fintype n] [DecidableEq n]
        (G Δ : Matrix n n ℂ) (c : ℂ), G.trace ≠ 0 →
        (G * Δ).trace = 0 →
        (G * ((c / G.trace) • 1 + Δ)).trace = c)
    -- (3) one nonzero affine functional: dimension ten → nine
    ∧ (∀ (V : Type) [AddCommGroup V] [Module ℝ V]
        [FiniteDimensional ℝ V] (φ : V →ₗ[ℝ] ℝ),
        Module.finrank ℝ V = 10 → φ ≠ 0 →
        Module.finrank ℝ (LinearMap.ker φ) = 9)
    -- (4) contrast: the faithful joint state separates effects
    ∧ (∀ {n : Type} [Fintype n] [DecidableEq n]
        (G K K' : Matrix n n ℂ) [Invertible G],
        K * G = K' * G → K = K') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n _ _ G c htr
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
      smul_eq_mul, div_mul_cancel₀ c htr]
  · intro n _ _ G Δ c htr hΔ
    rw [Matrix.mul_add, Matrix.trace_add, hΔ, add_zero,
      Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
      smul_eq_mul, div_mul_cancel₀ c htr]
  · intro V _ _ _ φ h10 hφ
    have hrn := LinearMap.finrank_range_add_finrank_ker φ
    have hle : Module.finrank ℝ (LinearMap.range φ)
        ≤ Module.finrank ℝ ℝ := (LinearMap.range φ).finrank_le
    rw [Module.finrank_self] at hle
    have hne : Module.finrank ℝ (LinearMap.range φ) ≠ 0 := by
      intro h0
      exact hφ (LinearMap.range_eq_bot.mp
        (Submodule.finrank_eq_zero.mp h0))
    rw [h10] at hrn
    omega
  · intro n _ _ G K K' _ h
    calc K = K * G * ⅟G := (mul_invOf_cancel_right K G).symm
      _ = K' * G * ⅟G := by rw [h]
      _ = K' := mul_invOf_cancel_right K' G

/-- `cor:SM-occurrence-environment-rank`. -/
theorem occurrence_environment_rank {n : Type*} [Fintype n]
    [DecidableEq n] (d : n → ℂ)
    (hd : ∀ i, d i = 0 ∨ d i = 1) :
    (Matrix.diagonal d).rank
        + (Matrix.diagonal fun i => 1 - d i).rank
      = Fintype.card n
    ∧ (Matrix.diagonal d).rank
          + 15 * (Matrix.diagonal fun i => 1 - d i).rank
        = (Matrix.diagonal d).rank
          + 15 * (Fintype.card n - (Matrix.diagonal d).rank) := by
  classical
  have hiff : ∀ i, ((1 : ℂ) - d i ≠ 0) ↔ ¬(d i ≠ 0) := by
    intro i
    rcases hd i with h | h <;> simp [h]
  have h1 : (Matrix.diagonal fun i => 1 - d i).rank
      = Fintype.card n - (Matrix.diagonal d).rank := by
    rw [Matrix.rank_diagonal, Matrix.rank_diagonal,
      Fintype.card_congr (Equiv.subtypeEquivRight hiff),
      Fintype.card_subtype_compl]
  have hle : (Matrix.diagonal d).rank ≤ Fintype.card n := by
    rw [Matrix.rank_diagonal]
    exact Fintype.card_subtype_le _
  constructor
  · rw [h1]
    omega
  · rw [h1]

end NCG
