/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Approximate Schur locality at a renewal cut
  (`thm:approximate-cut-locality-master`,
   `cor:approximate-cut-product-master`, flagship manuscript)

* `average_within_defect`: the group-averaging step — the
  average `W̄` of the conjugates `U_g*WU_g`, each within the
  naturality defect `ε` of `W`, stays within `ε` of `W`;
* `unitary_defect_bound`: the unitarity transfer —
  `‖A*A - 1‖ = ‖W̄*W̄ - W*W‖ ≤ 2ε` for elements at distance
  `≤ ε` from the unitary `W`;
* `eta_bounds`: the boxed remainder arithmetic — for
  `0 ≤ ε ≤ 1/2`,
  `2ε ≤ η_nat(ε) = ε + 1 - √(1-2ε) ≤ 3ε`,
  the quantitative form of `η_nat(ε) = 2ε + O(ε²)`;
* `approximate_cut_locality`: the boxed conclusion — the triangle
  through the averaged element gives `‖W - I⊗V‖ ≤ η_nat(ε)`,
  with the polar step `‖W̄ - I⊗V‖ ≤ 1 - √(1-2ε)` displayed;
* `approximate_cut_product`: the product corollary — the same
  bound transfers to every normalized source pair through the
  displayed structure identification.

Rendering disclosed: Schur's lemma identifying the average with
`I⊗A` (irreducibility of the past representation) and the polar
bound `‖A - V‖ ≤ 1 - √(1-2ε)` (smallest singular value
`≥ √(1-2ε)` from `‖A*A - 1‖ ≤ 2ε`, then the polar unitary) are
the manuscript's representation/functional-calculus steps — no
polar-decomposition norm calculus exists in Mathlib, so they
enter as the displayed hypothesis `hpolar`.
-/

namespace NCG

/-- Group averaging keeps the naturality defect: the average of
conjugates each within `ε` of `W` is within `ε` of `W`. -/
theorem average_within_defect {G A : Type*} [Fintype G]
    [Nonempty G] [NormedAddCommGroup A] [NormedSpace ℝ A]
    (W : A) (f : G → A) (ε : ℝ) (hf : ∀ g, ‖W - f g‖ ≤ ε) :
    ‖W - (Fintype.card G : ℝ)⁻¹ • ∑ g, f g‖ ≤ ε := by
  have hcard : (0:ℝ) < (Fintype.card G : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hW : W = (Fintype.card G : ℝ)⁻¹ • ∑ _g : G, W := by
    rw [Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ hcard.ne', one_smul]
  calc ‖W - (Fintype.card G : ℝ)⁻¹ • ∑ g, f g‖
      = ‖(Fintype.card G : ℝ)⁻¹ • ∑ g, (W - f g)‖ := by
        rw [Finset.sum_sub_distrib, smul_sub, ← hW]
    _ = (Fintype.card G : ℝ)⁻¹ * ‖∑ g, (W - f g)‖ := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g, ‖W - f g‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact norm_sum_le _ _
    _ ≤ (Fintype.card G : ℝ)⁻¹ * (Fintype.card G * ε) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∑ g, ‖W - f g‖ ≤ ∑ _g : G, ε :=
            Finset.sum_le_sum fun g _ => hf g
          _ = Fintype.card G * ε := by
            rw [Finset.sum_const, Finset.card_univ,
              nsmul_eq_mul]
    _ = ε := by field_simp

/-- Unitarity transfer: an element within `ε` of the unitary `W`
(`W*W = 1`, `‖W‖ ≤ 1`) has unitarity defect `≤ 2ε`. -/
theorem unitary_defect_bound {𝔸 : Type*} [NormedRing 𝔸]
    [StarRing 𝔸] [NormedStarGroup 𝔸] (W A : 𝔸)
    (hWu : star W * W = 1) (hWn : ‖W‖ ≤ 1) (hA : ‖A‖ ≤ 1)
    (ε : ℝ) (h : ‖W - A‖ ≤ ε) :
    ‖star A * A - 1‖ ≤ 2 * ε := by
  have hsplit : star A * A - 1
      = star A * (A - W) + (star A - star W) * W := by
    rw [← hWu]
    noncomm_ring
  rw [hsplit]
  have h1 : ‖star A * (A - W)‖ ≤ ε := by
    calc ‖star A * (A - W)‖ ≤ ‖star A‖ * ‖A - W‖ :=
        norm_mul_le _ _
      _ ≤ 1 * ε := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _)
            zero_le_one
          · rw [norm_star]
            exact hA
          · rw [norm_sub_rev]
            exact h
      _ = ε := one_mul ε
  have h2 : ‖(star A - star W) * W‖ ≤ ε := by
    calc ‖(star A - star W) * W‖
        ≤ ‖star A - star W‖ * ‖W‖ := norm_mul_le _ _
      _ = ‖A - W‖ * ‖W‖ := by
          rw [← star_sub, norm_star]
      _ ≤ ε * 1 := by
          refine mul_le_mul ?_ hWn (norm_nonneg _)
            (le_trans (norm_nonneg _) h)
          rw [norm_sub_rev]
          exact h
      _ = ε := mul_one ε
  calc ‖star A * (A - W) + (star A - star W) * W‖
      ≤ ‖star A * (A - W)‖ + ‖(star A - star W) * W‖ :=
        norm_add_le _ _
    _ ≤ ε + ε := add_le_add h1 h2
    _ = 2 * ε := by ring

/-- Boxed remainder arithmetic:
`2ε ≤ η_nat(ε) = ε + 1 - √(1-2ε) ≤ 3ε` for `0 ≤ ε ≤ 1/2`. -/
theorem eta_bounds (ε : ℝ) (h0 : 0 ≤ ε) (h2 : ε ≤ 1 / 2) :
    2 * ε ≤ ε + (1 - Real.sqrt (1 - 2 * ε))
    ∧ ε + (1 - Real.sqrt (1 - 2 * ε)) ≤ 3 * ε := by
  have h12 : (0:ℝ) ≤ 1 - 2 * ε := by linarith
  have hs := Real.sq_sqrt h12
  have hsn := Real.sqrt_nonneg (1 - 2 * ε)
  constructor
  · have hle : Real.sqrt (1 - 2 * ε) ≤ 1 - ε := by
      have h1e : (0:ℝ) ≤ 1 - ε := by linarith
      have hcmp : Real.sqrt (1 - 2 * ε)
          ≤ Real.sqrt ((1 - ε) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq h1e] at hcmp
    linarith
  · have hone : Real.sqrt (1 - 2 * ε) ≤ 1 :=
      Real.sqrt_le_one.mpr (by linarith)
    have hge : 1 - 2 * ε ≤ Real.sqrt (1 - 2 * ε) := by
      nlinarith [hs, hsn, hone]
    linarith

/-- `thm:approximate-cut-locality-master`, boxed conclusion: the
triangle through the averaged element gives
`‖W - I⊗V‖ ≤ η_nat(ε)` (polar step displayed). -/
theorem approximate_cut_locality {A : Type*}
    [NormedAddCommGroup A] (W Wbar IV : A) (ε : ℝ)
    (havg : ‖W - Wbar‖ ≤ ε)
    (hpolar : ‖Wbar - IV‖ ≤ 1 - Real.sqrt (1 - 2 * ε)) :
    ‖W - IV‖ ≤ ε + (1 - Real.sqrt (1 - 2 * ε)) := by
  calc ‖W - IV‖ = ‖(W - Wbar) + (Wbar - IV)‖ := by abel_nf
    _ ≤ ‖W - Wbar‖ + ‖Wbar - IV‖ := norm_add_le _ _
    _ ≤ ε + (1 - Real.sqrt (1 - 2 * ε)) :=
        add_le_add havg hpolar

/-- `cor:approximate-cut-product-master`: the locality bound
transfers to every normalized source pair through the displayed
structure identification `hstruct`. -/
theorem approximate_cut_product {A B : Type*}
    [NormedAddCommGroup A] [NormedAddCommGroup B]
    (Ξ Ξt : B) (W Wbar IV : A) (ε : ℝ)
    (hstruct : ‖Ξ - Ξt‖ ≤ ‖W - IV‖)
    (havg : ‖W - Wbar‖ ≤ ε)
    (hpolar : ‖Wbar - IV‖ ≤ 1 - Real.sqrt (1 - 2 * ε)) :
    ‖Ξ - Ξt‖ ≤ ε + (1 - Real.sqrt (1 - 2 * ε)) :=
  le_trans hstruct
    (approximate_cut_locality W Wbar IV ε havg hpolar)

end NCG
