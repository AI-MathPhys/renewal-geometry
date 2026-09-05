/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Common predictor plus fresh positive innovation
  (`thm:common-predictor-innovation`, Gran-Tensor manuscript)

* `common_predictor_innovation`: strict causality (nilpotency of
  the causal block `P`) makes `I - P` invertible; the two
  covariances obey the boxed formulas with difference
  `L·D_B·L*` positive, so `Cov(Y) ⪯ Cov(X)`; and conversely the
  congruence `Δ ↦ LΔL*` preserves positivity in both directions
  for invertible `L`, which is the exact realizability
  criterion.

Rendering disclosed: Gaussian path laws are rendered by their
covariances (the manuscript's proof is covariance algebra);
strict causality of a block-triangular operator with zero
diagonal is rendered by nilpotency; the independent-innovation
cross-covariance removal is the additivity `D_G + D_B` in the
displayed formula.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:common-predictor-innovation`. -/
theorem common_predictor_innovation {n : Type*} [Fintype n]
    [DecidableEq n] (P : Matrix n n ℂ) (hP : IsNilpotent P)
    (DB : Matrix n n ℂ) (hDB : DB.PosSemidef) :
    IsUnit (1 - P)
    ∧ (∀ L DG : Matrix n n ℂ,
        L * (DG + DB) * Lᴴ - L * DG * Lᴴ = L * DB * Lᴴ)
    ∧ (∀ L : Matrix n n ℂ, (L * DB * Lᴴ).PosSemidef)
    ∧ (∀ L : Matrix n n ℂ, IsUnit L → ∀ Δ : Matrix n n ℂ,
        ((L * Δ * Lᴴ).PosSemidef ↔ Δ.PosSemidef)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hP.isUnit_one_sub
  · intro L DG
    noncomm_ring
  · intro L
    exact hDB.mul_mul_conjTranspose_same L
  · intro L hL Δ
    rw [← Matrix.star_eq_conjTranspose]
    exact hL.posSemidef_star_right_conjugate_iff

end NCG
