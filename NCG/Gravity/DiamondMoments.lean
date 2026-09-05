/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Causal-diamond moment tomography (GR_emergence, Phase 2)

* `diamondMoment`, `canonical_diamond_moments` —
  `lem:canonical-diamond-moments`: the even mixed moments of the
  canonical diamond profile `(m,n) = (0,0)` in `d = 3`, via the
  factorized Beta formula displayed in
  `def:diamond-quartic-response`:
  `⟨η^{2a}|z|^{2b}⟩ = B(2a+1, 2b+4)/B(1,4) · B(b+3/2,1)/B(3/2,1)`,
  which for integer `a, b` is the rational value
  `4·(2a)!·(2b+3)!/(2a+2b+4)! · 3/(2b+3)`.  The five displayed
  values `1/15, 2/5, 3/14, 2/15, 1/210` follow, including the
  genuine longitudinal–transverse correlation
  `⟨η²|z|⁴⟩ ≠ ⟨η²⟩⟨|z|⁴⟩`;
* `diamond_linear_response` — `thm:diamond-linear-response`: the
  induced diamond response coefficients
  `α_u = -(1/6)(⟨η²|z|⁴⟩-⟨η²⟩⟨|z|⁴⟩)/⟨|z|⁴⟩`,
  `α_⊥ = -(1/6)(⟨|z|⁶⟩-⟨|z|²⟩⟨|z|⁴⟩)/⟨|z|⁴⟩` evaluate to
  `α_R = α_⊥ = -1/27` and `α_{R_uu} = α_u + α_⊥ = -4/135`;
* `explicit_tomography_matrix` — the displayed two-profile moment
  matrix of `prop:explicit-tomography`: its determinant is
  `-1/583200` and its inverse is `[[-900,1620],[1710,-2430]]`.
-/

namespace NCG

/-- The even mixed moment `⟨η^{2a}|z|^{2b}⟩` of the canonical
`(m,n) = (0,0)` diamond profile in `d = 3`, via the factorized Beta
formula of `def:diamond-quartic-response`. -/
def diamondMoment (a b : ℕ) : ℚ :=
  4 * (Nat.factorial (2 * a)) * (Nat.factorial (2 * b + 3))
    / (Nat.factorial (2 * a + 2 * b + 4)) * (3 / (2 * b + 3))

/-- `lem:canonical-diamond-moments`: the five canonical moments, and
the nonvanishing longitudinal–transverse correlation
`⟨η²|z|⁴⟩ ≠ ⟨η²⟩·⟨|z|⁴⟩` (the shrinking transverse radius
correlates the coordinates — absent for a product cylinder). -/
theorem canonical_diamond_moments :
    diamondMoment 1 0 = 1/15 ∧
    diamondMoment 0 1 = 2/5 ∧
    diamondMoment 0 2 = 3/14 ∧
    diamondMoment 0 3 = 2/15 ∧
    diamondMoment 1 2 = 1/210 ∧
    diamondMoment 1 2 ≠ diamondMoment 1 0 * diamondMoment 0 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [diamondMoment, Nat.factorial]

/-- `thm:diamond-linear-response`: the diamond response coefficients
of the isotropic quartic cumulant evaluate to
`α_R = α_⊥ = -1/27` and `α_{R_uu} = α_u + α_⊥ = -4/135` on the
canonical profile. -/
theorem diamond_linear_response :
    let alpha_u := -(1/6 : ℚ)
      * (diamondMoment 1 2 - diamondMoment 1 0 * diamondMoment 0 2)
      / diamondMoment 0 2
    let alpha_perp := -(1/6 : ℚ)
      * (diamondMoment 0 3 - diamondMoment 0 1 * diamondMoment 0 2)
      / diamondMoment 0 2
    alpha_perp = -(1/27) ∧ alpha_u + alpha_perp = -(4/135) := by
  norm_num [diamondMoment, Nat.factorial]

/-- `prop:explicit-tomography` (inversion arithmetic): the displayed
two-profile moment matrix for `(m,n) = (0,0)` vs `(0,2)` in `d = 3`
has determinant `-1/583200` and the displayed inverse — the
two-profile Ricci reconstruction is well posed. -/
theorem explicit_tomography_matrix :
    let M : Matrix (Fin 2) (Fin 2) ℚ := !![1/240, 1/360; 19/6480, 1/648]
    M.det = -(1/583200) ∧
    M * !![-900, 1620; 1710, -2430] = 1 ∧
    !![-900, 1620; 1710, -2430] * M = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two]
    norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      norm_num

/-- `prop:diamond-covariant-linear` (arithmetic): with the isotropic
direction average `⟨u^μu^ν⟩ = g^{μν}/n` at `n = 4`, the u-averaged
diamond response is the pure Einstein-coefficient renormalization
`α_R + (1/4)·α_{R_uu} = -2/45` — a shift of `1/(16πG_ren)`, not a
higher-curvature invariant. -/
theorem diamond_covariant_linear :
    -(1/27 : ℚ) + (1/4) * (-(4/135)) = -(2/45) := by norm_num

end NCG
