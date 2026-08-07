/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The completed-private mark is the first predictive reset
  (`thm:completed-boundary-decoupling` and
  `cor:resolved-phase-selection`, Gran-Tensor manuscript)

* `completed_boundary_decoupling`: for the concrete renewal
  packet `Q₀ = [[1/5,4/5],[0,1/3]]`, `r₀ = (0,2/3)ᵀ`,
  `α = (1,0)`:
  (i) each completion branch `R_h = ½·r₀α` is a nonzero
      atomic (rank-one, `ℓ(x)ω`-form) reset;
  (ii) `R₀ + R₁ = r₀α = M₀ - Q₀` (the completed endpoint is a
      fresh fair mark: both branches are the same `R/2`);
  (iii) every pure survivor `Q₀ⁿ` has rank two (the survivor
      never erases the active phase);
  (iv) every first-completion word `Q₀ⁿ·R_h` is nonzero and
      rank one with the same output direction (its private
      column mass is exactly `(1/3)ⁿ·(1/3)`).

* `resolved_phase_selection`: within the positive two-state
  quotient family, the concrete resolved renewal selects
  `a = 1/5` with `c(1/5) = 0`, `d(1/5) = 1/3`,
  `r_P(1/5) = 2/3`, recovering exactly `Q₀` and `r₀`; the
  seriality separation of the two scalar orientations is
  `1/3 - 1/5 = 2/15`.
-/

open Matrix

namespace NCG

private lemma mul_vecMulVec {n m p : Type*} [Fintype n]
    (A : Matrix p n ℚ) (v : n → ℚ) (w : m → ℚ) :
    A * Matrix.vecMulVec v w
      = Matrix.vecMulVec (A *ᵥ v) w := by
  ext i j
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

/-- `thm:completed-boundary-decoupling`. -/
theorem completed_boundary_decoupling :
    -- (i) the completion branch is a nonzero atomic reset
    ((2 : ℚ)⁻¹ • Matrix.vecMulVec (![0, 2/3] : Fin 2 → ℚ) (![1, 0] : Fin 2 → ℚ) ≠ 0)
    -- (ii) the two branches sum to the completed transition
    ∧ (2 : ℚ) • ((2 : ℚ)⁻¹
          • Matrix.vecMulVec (![0, 2/3] : Fin 2 → ℚ) (![1, 0] : Fin 2 → ℚ))
        = !![1/5, 4/5; 2/3, 1/3]
          - !![1/5, 4/5; 0, 1/3]
    -- (iii) every pure survivor has rank two
    ∧ (∀ n : ℕ,
        ((!![1/5, 4/5; 0, 1/3] : Matrix (Fin 2) (Fin 2) ℚ)
          ^ n).rank = 2)
    -- (iv) first-completion words are rank-one and nonzero
    ∧ (∀ n : ℕ,
        (!![1/5, 4/5; 0, 1/3] : Matrix (Fin 2) (Fin 2) ℚ)
            ^ n
          * ((2 : ℚ)⁻¹ • Matrix.vecMulVec (![0, 2/3] : Fin 2 → ℚ) (![1, 0] : Fin 2 → ℚ))
        = Matrix.vecMulVec
            ((!![1/5, 4/5; 0, 1/3]
                : Matrix (Fin 2) (Fin 2) ℚ) ^ n
              *ᵥ (![0, 1/3] : Fin 2 → ℚ)) ![1, 0]
        ∧ ((!![1/5, 4/5; 0, 1/3]
              : Matrix (Fin 2) (Fin 2) ℚ) ^ n
            *ᵥ (![0, 1/3] : Fin 2 → ℚ)) 1 = (1/3 : ℚ) ^ n * (1/3)) := by
  have hcol : ∀ n : ℕ,
      ((!![1/5, 4/5; 0, 1/3] : Matrix (Fin 2) (Fin 2) ℚ) ^ n
        *ᵥ (![0, 1/3] : Fin 2 → ℚ)) 1 = (1/3 : ℚ) ^ n * (1/3) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        rw [pow_succ']
        rw [← Matrix.mulVec_mulVec]
        have h1 : ∀ x : Fin 2 → ℚ,
            ((!![1/5, 4/5; 0, 1/3]
              : Matrix (Fin 2) (Fin 2) ℚ) *ᵥ x) 1
              = (1/3 : ℚ) * x 1 := by
          intro x
          simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        rw [h1, ih]
        ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    have h := congrFun (congrFun h0 1) 0
    norm_num [Matrix.vecMulVec_apply, Matrix.smul_apply] at h
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.vecMulVec_apply, Matrix.smul_apply]
  · intro n
    have hdet : ((!![1/5, 4/5; 0, 1/3]
        : Matrix (Fin 2) (Fin 2) ℚ) ^ n).det
        = (1/15 : ℚ) ^ n := by
      rw [Matrix.det_pow, Matrix.det_fin_two_of]
      norm_num
    have hunit : IsUnit ((!![1/5, 4/5; 0, 1/3]
        : Matrix (Fin 2) (Fin 2) ℚ) ^ n) := by
      rw [Matrix.isUnit_iff_isUnit_det, hdet]
      exact (isUnit_iff_ne_zero.mpr (by norm_num)).pow n
    rw [Matrix.rank_of_isUnit _ hunit]
    simp
  · intro n
    constructor
    · rw [show ((2 : ℚ)⁻¹
          • Matrix.vecMulVec (![0, 2/3] : Fin 2 → ℚ) (![1, 0] : Fin 2 → ℚ))
          = Matrix.vecMulVec (![0, 1/3] : Fin 2 → ℚ) (![1, 0] : Fin 2 → ℚ) from by
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [Matrix.vecMulVec_apply,
            Matrix.smul_apply]]
      exact mul_vecMulVec _ _ _
    · exact hcol n

/-- `cor:resolved-phase-selection`. -/
theorem resolved_phase_selection :
    -- the family formulas at the selected point `a = 1/5`
    ((8 : ℚ)/15 - 1/5 = 1/3)
    ∧ ((5 * (1/5 : ℚ) - 1) * (1 - 3 * (1/5))
        / (15 * (1 - 1/5)) = 0)
    ∧ ((8 : ℚ) / (15 * (1 - 1/5)) = 2/3)
    -- the recovered transfer and completion vector
    ∧ (!![1/5, 1 - 1/5;
          (5 * (1/5 : ℚ) - 1) * (1 - 3 * (1/5))
            / (15 * (1 - 1/5)),
          8/15 - 1/5] = !![1/5, 4/5; 0, 1/3])
    ∧ (![0, 1 - ((5 * (1/5 : ℚ) - 1) * (1 - 3 * (1/5))
          / (15 * (1 - 1/5))) - (8/15 - 1/5)] = ![0, 2/3])
    -- the seriality separation margin
    ∧ ((1 : ℚ)/3 - 1/5 = 2/15) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_,
    by norm_num⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  · funext i
    fin_cases i <;> norm_num

end NCG
