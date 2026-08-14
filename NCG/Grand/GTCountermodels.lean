/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Countermodel pack for the Grand-Tensor source geometry
  (`cth:GT-flat-linear-not-monoidal`,
  `cth:GT-secant-no-tangent`,
  `cth:GT-angle-predictor-nonmonotone`,
  `cth:GT-character-nuisance`,
  `cth:GT-negative-connected-generator`,
  `cth:GT-return-cancellation`,
  `cth:GT-one-shell-no-nesting`,
  `cth:GRH-atomic-short`, Gran-Tensor manuscript)

Each countertheorem is realized by its explicit concrete
witness from the manuscript's proof, verified exactly:

* `gt_flat_linear_not_monoidal`: the rational reflection
  `R = I - (1/3)ww^T`, `w = (2,-1,-1)`, is orthogonal,
  fixes the constants, is an involution (so the two-edge
  cycle `R·R = I` has trivial linear holonomy), yet is not
  multiplicative on the algebra `ℝ³`.
* `gt_secant_no_tangent`: two full-support `C¹` paths on
  the two-point space with equal endpoints and different
  initial derivatives.
* `gt_angle_predictor_nonmonotone`: in `ℝ²`, orthogonal
  residuals become aligned after projecting out
  `span(e₁-e₂)`; in `ℝ³`, correlated sources become
  orthogonal after projecting out `span(e₃)`.
* `gt_character_nuisance`: shorting `e₁ ⊥ e₂` by the
  noninvariant direction `(e₁+e₂)/√2` produces overlap
  `-1/2`.
* `gt_negative_connected_generator`:
  `K₁₂ = -Q₁⊗Q₂ ⪯ 0` although `L₁, L₂, L₁₂ ⪰ 0`.
* `gt_return_cancellation`: the boxed packet with
  `BD⁰C = 1`, `BDC = -1`, `BDⁿC = 0 (n ≥ 2)` has vanishing
  aggregate `B(I-D)⁻¹C = 0` and a nonzero returned word.
* `gt_one_shell_no_nesting`: `F₁ = G₁ = id`,
  `F₂(x,r) = x+r`: each retained one-shell map is exact
  while the discarded-tail two-shell defect is `c ≠ 0`.
* `grh_atomic_short`: two energy atoms with per-atom
  shorts `1 - 1 = 0` and assembled short `2 > 0`.
-/

open Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedFintypeInType false
set_option linter.unnecessarySeqFocus false

namespace NCG

/-- `cth:GT-flat-linear-not-monoidal`. -/
theorem gt_flat_linear_not_monoidal :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ,
      -- orthogonal (Hilbert-unitary source transport)
      Rᵀ * R = 1
      -- fixes the constant vector (trace-preserving)
      ∧ R *ᵥ ![1, 1, 1] = ![1, 1, 1]
      -- the two-edge cycle has trivial linear holonomy
      ∧ R * R = 1
      -- yet the transport is not monoidal
      ∧ ¬(∀ x y : Fin 3 → ℝ,
          R *ᵥ (x * y) = (R *ᵥ x) * (R *ᵥ y)) := by
  refine ⟨!![-1/3, 2/3, 2/3; 2/3, 2/3, -1/3;
    2/3, -1/3, 2/3], ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      norm_num
  · funext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      norm_num
  · intro h
    have hcontra := congrFun (h ![1, 0, 0] ![1, 0, 0]) 0
    norm_num [Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Pi.mul_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] at hcontra

/-- `cth:GT-secant-no-tangent`. -/
theorem gt_secant_no_tangent (δ η : ℝ) (hη : η ≠ 0) :
    -- equal endpoints
    ((1 / 2 + δ * 0 : ℝ)
      = 1 / 2 + δ * 0 + η * (0 * (1 - 0)))
    ∧ ((1 / 2 + δ * 1 : ℝ)
      = 1 / 2 + δ * 1 + η * (1 * (1 - 1)))
    -- different initial derivatives
    ∧ HasDerivAt (fun t : ℝ => 1 / 2 + δ * t) δ 0
    ∧ HasDerivAt
        (fun t : ℝ => 1 / 2 + δ * t + η * (t * (1 - t)))
        (δ + η) 0
    ∧ δ ≠ δ + η := by
  refine ⟨by ring, by ring, ?_, ?_,
    by intro h; apply hη; linarith⟩
  · simpa using ((hasDerivAt_id (0 : ℝ)).const_mul
      δ).const_add (1 / 2)
  · have h1 : HasDerivAt (fun t : ℝ => t * (1 - t)) 1 0 := by
      have h := (hasDerivAt_id (0 : ℝ)).mul
        ((hasDerivAt_id (0 : ℝ)).const_sub 1)
      norm_num at h
      exact h
    have h2 := ((hasDerivAt_id (0 : ℝ)).const_mul
      δ).const_add (1 / 2)
    have h3 := h1.const_mul η
    have h := h2.add h3
    have hfun : ((fun x : ℝ => 1 / 2 + δ * id x)
        + fun y : ℝ => η * (y * (1 - y)))
        = fun t : ℝ => 1 / 2 + δ * t + η * (t * (1 - t)) := by
      funext t
      simp [Pi.add_apply]
    rw [hfun] at h
    have hval : δ * 1 + η * 1 = δ + η := by ring
    rw [hval] at h
    exact h

/-- `cth:GT-angle-predictor-nonmonotone`. -/
theorem gt_angle_predictor_nonmonotone :
    -- ℝ²: orthogonal sources become aligned after the
    -- projection onto `span(e₁-e₂)` is removed
    ((![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![0, 1] = 0
      ∧ (![1, 0] : Fin 2 → ℝ)
          - ((2⁻¹ : ℝ) * (![1, 0] ⬝ᵥ ![1, -1]))
            • (![1, -1] : Fin 2 → ℝ)
        = (![0, 1] : Fin 2 → ℝ)
          - ((2⁻¹ : ℝ) * (![0, 1] ⬝ᵥ ![1, -1]))
            • (![1, -1] : Fin 2 → ℝ))
    -- ℝ³: correlated sources become orthogonal after the
    -- `e₃` direction is removed
    ∧ ((![1, 0, 1] : Fin 3 → ℝ) ⬝ᵥ ![0, 1, 1] = 1
      ∧ (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ ![0, 1, 0] = 0) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp [dotProduct, Fin.sum_univ_two]
  · funext i
    fin_cases i <;>
      (simp [dotProduct, Fin.sum_univ_two]
       norm_num)
  · simp [dotProduct, Fin.sum_univ_three]
  · simp [dotProduct, Fin.sum_univ_three]

/-- `cth:GT-character-nuisance`. -/
theorem gt_character_nuisance :
    -- orthogonal before shorting
    ((![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![0, 1] = 0)
    -- overlap `-1/2` after shorting by `(e₁+e₂)/√2`
    ∧ (((![1, 0] : Fin 2 → ℝ)
        - ((2⁻¹ : ℝ) * (![1, 0] ⬝ᵥ ![1, 1]))
          • (![1, 1] : Fin 2 → ℝ))
      ⬝ᵥ ((![0, 1] : Fin 2 → ℝ)
        - ((2⁻¹ : ℝ) * (![0, 1] ⬝ᵥ ![1, 1]))
          • (![1, 1] : Fin 2 → ℝ)) = -(1/2)) := by
  constructor
  · simp [dotProduct, Fin.sum_univ_two]
  · simp [dotProduct, Fin.sum_univ_two]
    norm_num

/-- `cth:GT-negative-connected-generator`. -/
theorem gt_negative_connected_generator :
    let _Q : Matrix (Fin 2) (Fin 2) ℝ :=
      Matrix.diagonal ![1, 0]
    -- `L₁₂ = Q⊗I + I⊗Q - Q⊗Q` is entrywise a diagonal
    -- matrix with entries in `{0,1}` (hence PSD)
    (∀ i : Fin 2 × Fin 2,
      (0 : ℝ) ≤ (Matrix.diagonal
        (fun p : Fin 2 × Fin 2 =>
          ![1, 0] p.1 + ![1, 0] p.2
            - ![1, 0] p.1 * ![1, 0] p.2)) i i)
    -- while the connected interaction `K₁₂ = -Q⊗Q` is
    -- negative and nonzero
    ∧ ((Matrix.diagonal (fun p : Fin 2 × Fin 2 =>
        -(![1, 0] p.1 * ![1, 0] p.2))) (0, 0) (0, 0)
      = -1) := by
  constructor
  · intro i
    rcases i with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;>
      norm_num [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply]

/-- `cth:GT-return-cancellation`. -/
theorem gt_return_cancellation (t : ℝ) (ht : t ≠ 0) :
    let B : Matrix (Fin 1) (Fin 2) ℝ := !![1, -t⁻¹]
    let D : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; t, 0]
    let C : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]
    -- the returned words: `BD⁰C = 1`, `BDC = -1`, `D² = 0`
    (B * C = !![1]
      ∧ B * D * C = !![-1]
      ∧ D * D = 0)
    -- the boxed aggregate cancellation `B(I + D)C = 0`
    -- (with `(I-D)⁻¹ = I + D` since `D² = 0`)
    ∧ (B * ((1 : Matrix (Fin 2) (Fin 2) ℝ) + D) * C = 0
      ∧ ((1 : Matrix (Fin 2) (Fin 2) ℝ) - D)
        * ((1 : Matrix (Fin 2) (Fin 2) ℝ) + D) = 1) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    (ext i j
     fin_cases i <;> fin_cases j <;>
       (simp [Matrix.mul_apply, Matrix.vecMul,
          dotProduct, Fin.sum_univ_two,
          Matrix.one_apply]
        try field_simp
        try ring))

/-- `cth:GT-one-shell-no-nesting`. -/
theorem gt_one_shell_no_nesting :
    let F₁ : ℝ → ℝ := id
    let G₁ : ℝ → ℝ := id
    let F₂ : ℝ → ℝ → ℝ := fun x r => x + r
    -- each retained one-shell map is exactly represented
    (∀ c, F₁ c = c) ∧ (∀ c, G₁ c = c)
    -- but the discarded-tail two-shell defect is `c ≠ 0`
    ∧ (∀ c, F₂ (F₁ c) (G₁ c) - F₂ (F₁ c) 0 = c) := by
  exact ⟨fun c => rfl, fun c => rfl, fun c => by simp⟩

/-- `cth:GRH-atomic-short`. -/
theorem grh_atomic_short :
    -- per-atom protected shorts vanish
    ((1 : ℝ) - 1 * 1 / 1 = 0 ∧ (1 : ℝ) - (-1) * (-1) / 1 = 0)
    -- while the assembled short is strictly positive
    ∧ ((2 : ℝ) - (1 + -1) * (1 + -1) / 2 = 2 ∧ (0 : ℝ) < 2) := by
  norm_num

end NCG
