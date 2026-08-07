/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Weighted source-influence criterion
  (`thm:weighted-source-influence`, Gran-Tensor manuscript)

* `weighted_schur_profile`: the per-index weighted Schur test —
  for a symmetric nonnegative block-bound matrix `c` and
  positive weights `w` with `Σ_j c_ij w_j ≤ κ_i w_i`, every
  nonnegative profile obeys `Σ_ij c_ij ξ_i ξ_j ≤ Σ_i κ_i ξ_i²`.
* `weighted_source_influence`: the uniform norm clause
  (`κ_i = κ_w`) and the dual diagonal-dominance clause
  (`κ_i = d_i` with vanishing diagonal), giving `R ⪰ 0` in
  profile form.

Rendering disclosed: `‖H‖ ≤ κ_w` and `R ⪰ 0` follow by applying
the proved profile inequalities to `ξ_i = ‖x_i‖` after
Cauchy–Schwarz on each block (the operator packaging);
`κ_w = sup_i (1/w_i)Σ_j c_ij w_j` is rendered by the per-index
bound hypothesis; the off-diagonal dominance sums are rendered
with vanishing diagonal bounds.
-/

namespace NCG

/-- The per-index weighted Schur test on nonnegative
profiles. -/
theorem weighted_schur_profile {I : Type*} [Fintype I]
    (c : I → I → ℝ) (w : I → ℝ) (κ : I → ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (hsymm : ∀ i j, c i j = c j i)
    (hw : ∀ i, 0 < w i)
    (hk : ∀ i, ∑ j, c i j * w j ≤ κ i * w i)
    (ξ : I → ℝ) (_hξ : ∀ i, 0 ≤ ξ i) :
    ∑ i, ∑ j, c i j * ξ i * ξ j ≤ ∑ i, κ i * ξ i ^ 2 := by
  have hterm : ∀ i j,
      c i j * ξ i * ξ j
        ≤ c i j * ((w j / w i) * ξ i ^ 2) / 2
          + c i j * ((w i / w j) * ξ j ^ 2) / 2 := by
    intro i j
    have hcore : 2 * (ξ i * ξ j)
        ≤ (w j / w i) * ξ i ^ 2 + (w i / w j) * ξ j ^ 2 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
        div_add_div _ _ (ne_of_gt (hw i)) (ne_of_gt (hw j)),
        le_div_iff₀ (mul_pos (hw i) (hw j))]
      nlinarith [sq_nonneg (w j * ξ i - w i * ξ j),
        (hw i).le, (hw j).le]
    nlinarith [mul_le_mul_of_nonneg_left hcore (hc i j)]
  have hhalf : ∑ i, ∑ j, c i j * ((w i / w j) * ξ j ^ 2)
      = ∑ i, ∑ j, c i j * ((w j / w i) * ξ i ^ 2) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    rw [hsymm j i]
  have hdistrib : ∑ i, ∑ j,
      (c i j * ((w j / w i) * ξ i ^ 2) / 2
        + c i j * ((w i / w j) * ξ j ^ 2) / 2)
      = ∑ i, ∑ j, c i j * ((w j / w i) * ξ i ^ 2) := by
    simp only [Finset.sum_add_distrib]
    rw [show (∑ i, ∑ j, c i j * ((w i / w j) * ξ j ^ 2) / 2)
        = (∑ i, ∑ j, c i j * ((w i / w j) * ξ j ^ 2)) / 2 from by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Finset.sum_div]]
    rw [show (∑ i, ∑ j, c i j * ((w j / w i) * ξ i ^ 2) / 2)
        = (∑ i, ∑ j, c i j * ((w j / w i) * ξ i ^ 2)) / 2 from by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Finset.sum_div]]
    rw [hhalf]
    ring
  calc ∑ i, ∑ j, c i j * ξ i * ξ j
      ≤ ∑ i, ∑ j, (c i j * ((w j / w i) * ξ i ^ 2) / 2
          + c i j * ((w i / w j) * ξ j ^ 2) / 2) :=
        Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => hterm i j
    _ = ∑ i, ∑ j, c i j * ((w j / w i) * ξ i ^ 2) := hdistrib
    _ = ∑ i, (ξ i ^ 2 / w i) * ∑ j, c i j * w j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        field_simp [(hw i).ne']
    _ ≤ ∑ i, (ξ i ^ 2 / w i) * (κ i * w i) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hk i)
            (div_nonneg (sq_nonneg _) (hw i).le)
    _ = ∑ i, κ i * ξ i ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp [(hw i).ne']

/-- `thm:weighted-source-influence`: uniform norm clause and
dual diagonal dominance. -/
theorem weighted_source_influence {I : Type*} [Fintype I]
    (c : I → I → ℝ) (w : I → ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (hsymm : ∀ i j, c i j = c j i)
    (hw : ∀ i, 0 < w i) :
    (∀ κ : ℝ, (∀ i, ∑ j, c i j * w j ≤ κ * w i) →
      ∀ ξ : I → ℝ, (∀ i, 0 ≤ ξ i) →
        ∑ i, ∑ j, c i j * ξ i * ξ j ≤ κ * ∑ i, ξ i ^ 2)
    ∧ (∀ dfl : I → ℝ, (∀ i, c i i = 0) →
        (∀ i, ∑ j, c i j * w j ≤ dfl i * w i) →
        ∀ ξ : I → ℝ, (∀ i, 0 ≤ ξ i) →
          0 ≤ ∑ i, dfl i * ξ i ^ 2
            - ∑ i, ∑ j, c i j * ξ i * ξ j) := by
  constructor
  · intro κ hk ξ hξ
    have h := weighted_schur_profile c w (fun _ => κ) hc hsymm
      hw hk ξ hξ
    calc ∑ i, ∑ j, c i j * ξ i * ξ j
        ≤ ∑ i, κ * ξ i ^ 2 := h
      _ = κ * ∑ i, ξ i ^ 2 := by rw [Finset.mul_sum]
  · intro dfl _ hdom ξ hξ
    have h := weighted_schur_profile c w dfl hc hsymm hw hdom
      ξ hξ
    linarith

end NCG
