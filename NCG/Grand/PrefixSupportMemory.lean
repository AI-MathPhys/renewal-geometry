/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Prefix purification support is not recurrent memory
  (`cth:prefix-support-memory`, Gran-Tensor manuscript)

* `prefix_support_memory`: for iid fair bits, the word table is
  the rank-one outer product `H(p,f) = (2^{-|p|})(2^{-|f|})`
  (one-state predictor); every fixed-horizon Hankel panel has
  rank at most one; yet the `N`-output cylinder density
  `2^{-N}·I` is invertible of full rank `2^N`, and every
  purification matrix `M` with `MMᴴ = 2^{-N}·I` needs
  environment dimension at least `2^N`.

Rendering disclosed: the Schmidt-rank argument is the proved
chain `2^N = rank(MMᴴ) ≤ rank M ≤ dim E`; the CP/classical
one-state realization clause is the rank-one factorization
itself.
-/

open Matrix

namespace NCG

/-- `cth:prefix-support-memory`. -/
theorem prefix_support_memory (N : ℕ) :
    -- (1) the word table is a rank-one outer product
    ((fun (p f : List Bool) =>
        ((2 : ℝ)⁻¹) ^ (p.length + f.length))
      = fun p f =>
          Matrix.vecMulVec
            (fun p : List Bool => ((2 : ℝ)⁻¹) ^ p.length)
            (fun f : List Bool => ((2 : ℝ)⁻¹) ^ f.length) p f)
    -- (2) any fixed-horizon panel has rank at most one
    ∧ (∀ (P F : Type) [Fintype P] [Fintype F]
        (u : P → ℝ) (v : F → ℝ),
        (Matrix.vecMulVec u v).rank ≤ 1)
    -- (3) the cylinder density is invertible (full rank 2^N)
    ∧ IsUnit (((2 : ℂ) ^ N)⁻¹
        • (1 : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ))
    -- (4) purification environments have dimension ≥ 2^N
    ∧ (∀ (E : Type) [Fintype E]
        (M : Matrix (Fin (2 ^ N)) E ℂ),
        M * Mᴴ = ((2 : ℂ) ^ N)⁻¹ • 1 →
        2 ^ N ≤ Fintype.card E) := by
  have hc : ((2 : ℂ) ^ N)⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero N two_ne_zero)
  have hunit : IsUnit (((2 : ℂ) ^ N)⁻¹
      • (1 : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul,
      Matrix.det_one, mul_one]
    exact (isUnit_iff_ne_zero.mpr hc).pow _
  refine ⟨?_, ?_, hunit, ?_⟩
  · funext p f
    rw [Matrix.vecMulVec_apply, pow_add]
  · intro P F _ _ u v
    exact Matrix.rank_vecMulVec_le u v
  · intro E _ M hM
    have hrank : (((2 : ℂ) ^ N)⁻¹
        • (1 : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ)).rank
        = 2 ^ N := by
      rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]
    calc 2 ^ N = (((2 : ℂ) ^ N)⁻¹
          • (1 : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ)).rank :=
          hrank.symm
      _ = (M * Mᴴ).rank := by rw [hM]
      _ ≤ M.rank := Matrix.rank_mul_le_left M Mᴴ
      _ ≤ Fintype.card E := Matrix.rank_le_card_width M

end NCG
