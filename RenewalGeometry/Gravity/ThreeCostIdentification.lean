/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Three-cost identification and rank defect
  (`prop:supp-three-costs`, `eq:main-measured-quadratic-cost`,
  `eq:main-rank-defect`, `eq:supp-cost-completion`;
  emergent-spacetime manuscript)

The measured quadratic cost of the finite positive class is
`E_s(x,y) = A (y-x)^2 / s + B s ((x+y)/2)^2 + C (y^2 - x^2)`.

* `measuredQuadraticCost`: the cost `E_s(x,y)`.
* `rankDefect`: the directly measurable rank defect `𝔇 = AB - C^2`
  (`eq:main-rank-defect`), which is the determinant of the coefficient
  matrix `[[A, C], [C, B]]` (`rankDefect_eq_det`) and is nonnegative when
  that matrix is positive semidefinite (`rankDefect_nonneg_of_posSemidef`).
* `measuredQuadraticCost_identify_B/C/A`: the three measured costs
  `E_s(u,u)`, `E_s(u,v)`, `E_s(v,u)` (distinct `u, v > 0`, `s > 0`)
  identify `B`, `C`, `A` by the boxed formulas
  `eq:supp-three-cost-identification`.
* `measuredQuadraticCost_completion`: the completed square
  `eq:supp-cost-completion`, `E_s = (A/s)[y - x - c s (x+y)/2]^2
  + ν s ((x+y)/2)^2` with `c = -C/A`, `ν = 𝔇/A`.
* `rankDefect_eq_zero_iff_rankOne`: `𝔇 = 0` is exactly the rank-one
  compatibility condition, i.e. the coefficient form
  `A x^2 + 2 C x y + B y^2` is the perfect square `A (x + (C/A) y)^2`.
-/

namespace RenewalGeometry

/-- The measured quadratic cost `E_s(x,y)` of
`eq:main-measured-quadratic-cost`. -/
noncomputable def measuredQuadraticCost (A B C s x y : ℝ) : ℝ :=
  A * (y - x) ^ 2 / s + B * s * ((x + y) / 2) ^ 2 + C * (y ^ 2 - x ^ 2)

/-- The rank defect `𝔇 = AB - C^2` of `eq:main-rank-defect`. -/
def rankDefect (A B C : ℝ) : ℝ := A * B - C ^ 2

/-- The rank defect is the determinant of the coefficient matrix
`[[A, C], [C, B]]` of `eq:main-measured-quadratic-cost`. -/
theorem rankDefect_eq_det (A B C : ℝ) :
    rankDefect A B C = Matrix.det !![A, C; C, B] := by
  rw [Matrix.det_fin_two_of]; unfold rankDefect; ring

/-- On the declared class (`[[A, C], [C, B]] ⪰ 0`) the rank defect is
nonnegative, `eq:main-rank-defect`. -/
theorem rankDefect_nonneg_of_posSemidef (A B C : ℝ)
    (h : Matrix.PosSemidef !![A, C; C, B]) : 0 ≤ rankDefect A B C := by
  rw [rankDefect_eq_det]
  exact h.det_nonneg

/-- The diagonal measurement determines `B`
(`eq:supp-three-cost-identification`, first line). -/
theorem measuredQuadraticCost_identify_B (A B C s u : ℝ) (hs : s ≠ 0)
    (hu : u ≠ 0) :
    B = measuredQuadraticCost A B C s u u / (s * u ^ 2) := by
  unfold measuredQuadraticCost
  field_simp
  ring

/-- Reversal determines `C`
(`eq:supp-three-cost-identification`, second line). -/
theorem measuredQuadraticCost_identify_C (A B C s u v : ℝ) (hs : s ≠ 0)
    (huv : v ^ 2 ≠ u ^ 2) :
    C = (measuredQuadraticCost A B C s u v - measuredQuadraticCost A B C s v u) /
      (2 * (v ^ 2 - u ^ 2)) := by
  have h : v ^ 2 - u ^ 2 ≠ 0 := sub_ne_zero.mpr huv
  unfold measuredQuadraticCost
  field_simp
  ring

/-- The reversal sum determines `A`
(`eq:supp-three-cost-identification`, third line). -/
theorem measuredQuadraticCost_identify_A (A B C s u v : ℝ) (hs : s ≠ 0)
    (huv : u ≠ v) :
    A = s / (2 * (v - u) ^ 2) *
      (measuredQuadraticCost A B C s u v + measuredQuadraticCost A B C s v u -
        2 * B * s * ((u + v) / 2) ^ 2) := by
  have h : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  unfold measuredQuadraticCost
  field_simp
  ring

/-- Distinct positive `u, v` have distinct squares (the `v^2 ≠ u^2`
hypothesis of the `C` identification in the paper's setting `u, v > 0`,
`u ≠ v`). -/
theorem sq_ne_sq_of_pos_of_ne {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (huv : u ≠ v) : v ^ 2 ≠ u ^ 2 := by
  intro h
  have := (pow_left_inj₀ hv.le hu.le (by norm_num : (2 : ℕ) ≠ 0)).mp h
  exact huv this.symm

/-- The three-cost identification of `prop:supp-three-costs` in the paper's
scope: `s > 0`, distinct `u, v > 0`. -/
theorem measuredQuadraticCost_three_cost_identification
    (A B C s u v : ℝ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v) :
    B = measuredQuadraticCost A B C s u u / (s * u ^ 2) ∧
    C = (measuredQuadraticCost A B C s u v - measuredQuadraticCost A B C s v u) /
      (2 * (v ^ 2 - u ^ 2)) ∧
    A = s / (2 * (v - u) ^ 2) *
      (measuredQuadraticCost A B C s u v + measuredQuadraticCost A B C s v u -
        2 * B * s * ((u + v) / 2) ^ 2) :=
  ⟨measuredQuadraticCost_identify_B A B C s u hs.ne' hu.ne',
   measuredQuadraticCost_identify_C A B C s u v hs.ne'
     (sq_ne_sq_of_pos_of_ne hu hv huv),
   measuredQuadraticCost_identify_A A B C s u v hs.ne' huv⟩

/-- The completed square `eq:supp-cost-completion` with `c = -C/A` and
`ν = 𝔇/A`. -/
theorem measuredQuadraticCost_completion (A B C s x y : ℝ) (hA : A ≠ 0)
    (hs : s ≠ 0) :
    measuredQuadraticCost A B C s x y =
      A / s * (y - x - (-C / A) * s * ((x + y) / 2)) ^ 2 +
        rankDefect A B C / A * s * ((x + y) / 2) ^ 2 := by
  unfold measuredQuadraticCost rankDefect
  field_simp
  ring

/-- `𝔇 = 0` is exactly the rank-one compatibility condition: for `A ≠ 0`
the coefficient quadratic form `A x^2 + 2 C x y + B y^2` of the matrix
`[[A, C], [C, B]]` is the perfect square `A (x + (C/A) y)^2` if and only if
`𝔇 = 0`. -/
theorem rankDefect_eq_zero_iff_rankOne (A B C : ℝ) (hA : A ≠ 0) :
    rankDefect A B C = 0 ↔
      ∀ x y : ℝ, A * x ^ 2 + 2 * C * x * y + B * y ^ 2 =
        A * (x + C / A * y) ^ 2 := by
  unfold rankDefect
  constructor
  · intro h x y
    have hB : B = C ^ 2 / A := by
      field_simp
      linarith
    subst hB
    field_simp
    ring
  · intro h
    have := h 0 1
    field_simp at this
    linarith

/-- The second term of the completed square vanishes identically exactly
when the rank defect vanishes (`A ≠ 0`, `s ≠ 0`). -/
theorem completion_second_term_eq_zero_iff (A B C s : ℝ) (hA : A ≠ 0)
    (hs : s ≠ 0) :
    (∀ x y : ℝ, rankDefect A B C / A * s * ((x + y) / 2) ^ 2 = 0) ↔
      rankDefect A B C = 0 := by
  constructor
  · intro h
    have := h 1 1
    norm_num at this
    rcases this with h1 | h1
    · rcases h1 with h2 | h2
      · exact h2
      · exact absurd h2 hA
    · exact absurd h1 hs
  · intro h x y
    rw [h]; ring

end RenewalGeometry
