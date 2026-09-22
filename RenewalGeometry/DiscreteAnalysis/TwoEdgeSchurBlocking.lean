/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Two-edge Schur identity (`lem:supp-two-edge-schur`, emergent spacetime)

For the positive edge quadratics
`E_i(x,y) = p_i x² - 2 q_i x y + r_i y²` (`p_i, q_i, r_i > 0`,
`d_i = p_i r_i - q_i² ≥ 0`), blocking the two-edge series
`z ↦ E₁(x,z) + E₂(z,y)` over the interior vertex `z` gives:

* `twoEdgeSchur_completed_square` — the exact completed square
  `E₁(x,z) + E₂(z,y) = E'(x,y) + (r₁ + p₂)(z - z_*)²` with
  `z_* = (q₁ x + q₂ y)/(r₁ + p₂)` and the blocked coefficients
  `p' = p₁ - q₁²/(r₁+p₂)`, `q' = q₁q₂/(r₁+p₂)`,
  `r' = r₂ - q₂²/(r₁+p₂)` (`eq:supp-schur-coefficients`);
* `twoEdgeSchur_minimizer_pos` — the minimizer is positive on
  positive endpoints;
* `twoEdgeSchur_blocked_le` / `twoEdgeSchur_eq_iff` — the blocked
  quadratic is the minimum in `z`, attained exactly at `z_*`;
* `twoEdgeSchur_determinant` — the boxed identity
  `p' r' - q'² = (r₂ d₁ + p₁ d₂)/(r₁ + p₂)`
  (`eq:supp-schur-determinant`);
* `two_edge_schur` — the packaged lemma.
-/

namespace RenewalGeometry

/-- The edge quadratic `E(x,y) = p x² - 2 q x y + r y²` of
`lem:supp-two-edge-schur`. -/
def edgeQuadratic (p q r x y : ℝ) : ℝ :=
  p * x ^ 2 - 2 * q * x * y + r * y ^ 2

/-- The blocked coefficient `p' = p₁ - q₁²/(r₁ + p₂)`
(`eq:supp-schur-coefficients`). -/
noncomputable def schurBlockedP (p₁ q₁ r₁ p₂ : ℝ) : ℝ :=
  p₁ - q₁ ^ 2 / (r₁ + p₂)

/-- The blocked coefficient `q' = q₁ q₂/(r₁ + p₂)`
(`eq:supp-schur-coefficients`). -/
noncomputable def schurBlockedQ (q₁ r₁ p₂ q₂ : ℝ) : ℝ :=
  q₁ * q₂ / (r₁ + p₂)

/-- The blocked coefficient `r' = r₂ - q₂²/(r₁ + p₂)`
(`eq:supp-schur-coefficients`). -/
noncomputable def schurBlockedR (r₁ p₂ q₂ r₂ : ℝ) : ℝ :=
  r₂ - q₂ ^ 2 / (r₁ + p₂)

/-- The interior minimizer `z_* = (q₁ x + q₂ y)/(r₁ + p₂)` of
`lem:supp-two-edge-schur`. -/
noncomputable def schurMinimizer (q₁ r₁ p₂ q₂ x y : ℝ) : ℝ :=
  (q₁ * x + q₂ * y) / (r₁ + p₂)

/-- `lem:supp-two-edge-schur` (completed square): for every `z`,
`E₁(x,z) + E₂(z,y) = E'(x,y) + (r₁ + p₂) (z - z_*)²`, where `E'`
carries the blocked coefficients `p', q', r'`.  Only `r₁ + p₂ ≠ 0`
is used. -/
theorem twoEdgeSchur_completed_square
    (p₁ q₁ r₁ p₂ q₂ r₂ : ℝ) (hs : r₁ + p₂ ≠ 0) (x y z : ℝ) :
    edgeQuadratic p₁ q₁ r₁ x z + edgeQuadratic p₂ q₂ r₂ z y
      = edgeQuadratic (schurBlockedP p₁ q₁ r₁ p₂)
          (schurBlockedQ q₁ r₁ p₂ q₂) (schurBlockedR r₁ p₂ q₂ r₂) x y
        + (r₁ + p₂) * (z - schurMinimizer q₁ r₁ p₂ q₂ x y) ^ 2 := by
  unfold edgeQuadratic schurBlockedP schurBlockedQ schurBlockedR
    schurMinimizer
  field_simp
  ring

/-- `lem:supp-two-edge-schur`: the minimizer `z_*` is positive on
positive endpoints `x, y > 0`. -/
theorem twoEdgeSchur_minimizer_pos
    (q₁ r₁ p₂ q₂ : ℝ) (hq₁ : 0 < q₁) (hr₁ : 0 < r₁) (hp₂ : 0 < p₂)
    (hq₂ : 0 < q₂) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 < schurMinimizer q₁ r₁ p₂ q₂ x y := by
  unfold schurMinimizer
  positivity

/-- `lem:supp-two-edge-schur`: the blocked quadratic is a lower bound
for the two-edge series at every interior value `z`. -/
theorem twoEdgeSchur_blocked_le
    (p₁ q₁ r₁ p₂ q₂ r₂ : ℝ) (hr₁ : 0 < r₁) (hp₂ : 0 < p₂) (x y z : ℝ) :
    edgeQuadratic (schurBlockedP p₁ q₁ r₁ p₂)
        (schurBlockedQ q₁ r₁ p₂ q₂) (schurBlockedR r₁ p₂ q₂ r₂) x y
      ≤ edgeQuadratic p₁ q₁ r₁ x z + edgeQuadratic p₂ q₂ r₂ z y := by
  rw [twoEdgeSchur_completed_square p₁ q₁ r₁ p₂ q₂ r₂ (by positivity)]
  have : 0 ≤ (r₁ + p₂) * (z - schurMinimizer q₁ r₁ p₂ q₂ x y) ^ 2 := by
    positivity
  linarith

/-- `lem:supp-two-edge-schur`: the two-edge series equals the blocked
quadratic exactly at the minimizer `z = z_*` (uniqueness of the
minimizer). -/
theorem twoEdgeSchur_eq_iff
    (p₁ q₁ r₁ p₂ q₂ r₂ : ℝ) (hr₁ : 0 < r₁) (hp₂ : 0 < p₂) (x y z : ℝ) :
    edgeQuadratic p₁ q₁ r₁ x z + edgeQuadratic p₂ q₂ r₂ z y
        = edgeQuadratic (schurBlockedP p₁ q₁ r₁ p₂)
            (schurBlockedQ q₁ r₁ p₂ q₂) (schurBlockedR r₁ p₂ q₂ r₂) x y
      ↔ z = schurMinimizer q₁ r₁ p₂ q₂ x y := by
  rw [twoEdgeSchur_completed_square p₁ q₁ r₁ p₂ q₂ r₂ (by positivity)]
  have hs : 0 < r₁ + p₂ := by positivity
  constructor
  · intro h
    have h0 : (r₁ + p₂) * (z - schurMinimizer q₁ r₁ p₂ q₂ x y) ^ 2 = 0 := by
      linarith
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 hs.ne'
    · exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1)
  · intro h
    rw [h, sub_self]
    ring

/-- `lem:supp-two-edge-schur` (`eq:supp-schur-determinant`): the boxed
determinant identity `p' r' - q'² = (r₂ d₁ + p₁ d₂)/(r₁ + p₂)` with
`d_i = p_i r_i - q_i²`. -/
theorem twoEdgeSchur_determinant
    (p₁ q₁ r₁ p₂ q₂ r₂ : ℝ) (hs : r₁ + p₂ ≠ 0) :
    schurBlockedP p₁ q₁ r₁ p₂ * schurBlockedR r₁ p₂ q₂ r₂
        - (schurBlockedQ q₁ r₁ p₂ q₂) ^ 2
      = (r₂ * (p₁ * r₁ - q₁ ^ 2) + p₁ * (p₂ * r₂ - q₂ ^ 2)) / (r₁ + p₂) := by
  unfold schurBlockedP schurBlockedQ schurBlockedR
  field_simp
  ring

/-- `lem:supp-two-edge-schur` (packaged): for positive coefficients
`p_i, q_i, r_i > 0` with `d_i = p_i r_i - q_i² ≥ 0`,
(i) the minimizer `z_*` of `z ↦ E₁(x,z) + E₂(z,y)` is positive on
positive endpoints; (ii) the blocked quadratic with coefficients
`p', q', r'` of `eq:supp-schur-coefficients` is the minimum over `z`,
attained exactly at `z_*`; (iii) the boxed determinant identity
`eq:supp-schur-determinant` holds.  (The nonnegativity `d_i ≥ 0` is
not needed for the identities; it is carried for faithfulness and
yields `p' r' - q'² ≥ 0` as a byproduct.) -/
theorem two_edge_schur
    (p₁ q₁ r₁ p₂ q₂ r₂ : ℝ)
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hr₁ : 0 < r₁)
    (hp₂ : 0 < p₂) (hq₂ : 0 < q₂) (hr₂ : 0 < r₂)
    (hd₁ : 0 ≤ p₁ * r₁ - q₁ ^ 2) (hd₂ : 0 ≤ p₂ * r₂ - q₂ ^ 2) :
    -- (i) positive minimizer on positive endpoints
    (∀ x y : ℝ, 0 < x → 0 < y → 0 < schurMinimizer q₁ r₁ p₂ q₂ x y)
    -- (ii) the blocked quadratic is the minimum in `z`, attained at `z_*`
    ∧ (∀ x y z : ℝ,
        edgeQuadratic (schurBlockedP p₁ q₁ r₁ p₂)
            (schurBlockedQ q₁ r₁ p₂ q₂) (schurBlockedR r₁ p₂ q₂ r₂) x y
          ≤ edgeQuadratic p₁ q₁ r₁ x z + edgeQuadratic p₂ q₂ r₂ z y)
    ∧ (∀ x y : ℝ,
        edgeQuadratic p₁ q₁ r₁ x (schurMinimizer q₁ r₁ p₂ q₂ x y)
            + edgeQuadratic p₂ q₂ r₂ (schurMinimizer q₁ r₁ p₂ q₂ x y) y
          = edgeQuadratic (schurBlockedP p₁ q₁ r₁ p₂)
              (schurBlockedQ q₁ r₁ p₂ q₂) (schurBlockedR r₁ p₂ q₂ r₂) x y)
    -- (iii) the boxed determinant identity, and its nonnegativity
    ∧ schurBlockedP p₁ q₁ r₁ p₂ * schurBlockedR r₁ p₂ q₂ r₂
          - (schurBlockedQ q₁ r₁ p₂ q₂) ^ 2
        = (r₂ * (p₁ * r₁ - q₁ ^ 2) + p₁ * (p₂ * r₂ - q₂ ^ 2)) / (r₁ + p₂)
    ∧ 0 ≤ schurBlockedP p₁ q₁ r₁ p₂ * schurBlockedR r₁ p₂ q₂ r₂
          - (schurBlockedQ q₁ r₁ p₂ q₂) ^ 2 := by
  have hs : r₁ + p₂ ≠ 0 := by positivity
  refine ⟨fun x y hx hy =>
      twoEdgeSchur_minimizer_pos q₁ r₁ p₂ q₂ hq₁ hr₁ hp₂ hq₂ x y hx hy,
    fun x y z => twoEdgeSchur_blocked_le p₁ q₁ r₁ p₂ q₂ r₂ hr₁ hp₂ x y z,
    fun x y => (twoEdgeSchur_eq_iff p₁ q₁ r₁ p₂ q₂ r₂ hr₁ hp₂ x y _).2 rfl,
    twoEdgeSchur_determinant p₁ q₁ r₁ p₂ q₂ r₂ hs, ?_⟩
  rw [twoEdgeSchur_determinant p₁ q₁ r₁ p₂ q₂ r₂ hs]
  positivity

end RenewalGeometry
