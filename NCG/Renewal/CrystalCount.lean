/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Renewal.DimensionTransfer

/-!
# The spacetime-crystal counting function and `q_alg = 1 + b_eff`

**Theorem `thm:dimension-coincidence` (algebraic link)**: under the
topological-crystal assumption the predictive classes of the regular
phase are (clock value, lattice displacement) pairs — the counting
function is the crystal count

`N(R) = (R+1)·(2R+1)^{b_eff}`

(clock shells × ℤ^{b_eff}-lattice balls, counted *exactly*:
`NCG.latticeBallCard_eq`, `NCG.crystalCount_card`), and its log–log
dimension is **exactly** `1 + b_eff` as an actual limit
(`NCG.crystal_log_dimension`) — the link `q_alg = 1 + b_eff` of the
dimension-coincidence chain, at the level of the defined limsup
dimension.  The identification of a concrete memory's predictive
quotient with the crystal is the topological-crystal assumption
(`ass:topological-crystal`) that the manuscript theorem itself takes
as hypothesis.
-/

namespace NCG

open Filter

/-- **Exact lattice-ball count**: the `ℤ^r`-ball of `ℓ∞` radius `R`
has exactly `(2R+1)^r` points. -/
theorem latticeBallCard_eq (r R : ℕ) :
    Nat.card {n : Fin r → ℤ // ∀ i, |n i| ≤ (R : ℤ)}
      = (2 * R + 1) ^ r := by
  rw [Nat.card_congr
    (Equiv.subtypePiEquivPi (p := fun (_ : Fin r) (a : ℤ) => |a| ≤ (R:ℤ)))]
  rw [Nat.card_pi]
  have hcard : Nat.card {a : ℤ // |a| ≤ (R:ℤ)} = 2 * R + 1 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun a : ℤ => by
      rw [abs_le, ← Finset.mem_Icc]))]
    rw [Nat.card_eq_finsetCard, Int.card_Icc]
    omega
  simp [hcard]

/-- The **crystal counting function**: clock shells times lattice
balls, `N(R) = (R+1)·(2R+1)^b`. -/
def crystalCount (b R : ℕ) : ℕ := (R + 1) * (2 * R + 1) ^ b

/-- The crystal count is the exact cardinality of the (clock,
displacement) class space at radius `R`. -/
theorem crystalCount_card (b R : ℕ) :
    Nat.card ({k : ℕ // k ≤ R}
        × {n : Fin b → ℤ // ∀ i, |n i| ≤ (R : ℤ)})
      = crystalCount b R := by
  rw [Nat.card_prod, latticeBallCard_eq]
  congr 1
  rw [Nat.card_congr ((Equiv.subtypeEquivRight
      (fun k : ℕ => Nat.lt_succ_iff.symm)).trans
    (Fin.equivSubtype (n := R + 1)).symm)]
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **`q_alg = 1 + b_eff` (Theorem `thm:dimension-coincidence`,
algebraic link)**: the crystal counting function has log–log dimension
*exactly* `1 + b` — an actual limit, hence the defined limsup
dimension of the regular spacetime-crystal phase equals `1 + b_eff`. -/
theorem crystal_log_dimension (b : ℕ) :
    Tendsto (fun R : ℕ => Real.log (crystalCount b R) / Real.log R)
      atTop (nhds (1 + b)) := by
  apply log_ratio_tendsto_of_poly_bounds ((1:ℝ) + b) 1 (2 * 3 ^ b)
    one_pos (by positivity)
  · -- lower: R^{1+b} ≤ (R+1)·(2R+1)^b
    intro R hR
    have hR0 : (0:ℝ) ≤ (R:ℝ) := by positivity
    have hrpow : (R:ℝ) ^ ((1:ℝ) + b) = (R:ℝ) ^ (1 + b) := by
      rw [show ((1:ℝ) + b) = ((1 + b : ℕ) : ℝ) from by push_cast; ring,
        Real.rpow_natCast]
    have hsplit : (R:ℝ) ^ (1 + b) = (R:ℝ) * (R:ℝ) ^ b := by
      rw [pow_add, pow_one]
    have hcast : (crystalCount b R : ℝ)
        = ((R:ℝ) + 1) * (2 * (R:ℝ) + 1) ^ b := by
      rw [crystalCount]
      push_cast
      ring
    rw [hrpow, one_mul, hsplit, hcast]
    have h1 : (R:ℝ) ≤ (R:ℝ) + 1 := by linarith
    have h2 : (R:ℝ) ^ b ≤ (2 * (R:ℝ) + 1) ^ b :=
      pow_le_pow_left₀ hR0 (by linarith) b
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  · -- upper: (R+1)·(2R+1)^b ≤ 2·3^b·R^{1+b} for R ≥ 2
    intro R hR
    have hR2 : (2:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    have hR0 : (0:ℝ) < (R:ℝ) := by linarith
    have hrpow : (R:ℝ) ^ ((1:ℝ) + b) = (R:ℝ) ^ (1 + b) := by
      rw [show ((1:ℝ) + b) = ((1 + b : ℕ) : ℝ) from by push_cast; ring,
        Real.rpow_natCast]
    have hcast : (crystalCount b R : ℝ)
        = ((R:ℝ) + 1) * (2 * (R:ℝ) + 1) ^ b := by
      rw [crystalCount]
      push_cast
      ring
    have hfinal : (2 * (R:ℝ)) * (3 * (R:ℝ)) ^ b
        = 2 * 3 ^ b * (R:ℝ) ^ (1 + b) := by
      rw [mul_pow, pow_add, pow_one]
      ring
    rw [hrpow, hcast]
    have h1 : (R:ℝ) + 1 ≤ 2 * (R:ℝ) := by linarith
    have h2 : (2 * (R:ℝ) + 1) ^ b ≤ (3 * (R:ℝ)) ^ b :=
      pow_le_pow_left₀ (by positivity) (by linarith) b
    calc ((R:ℝ) + 1) * (2 * (R:ℝ) + 1) ^ b
        ≤ (2 * (R:ℝ)) * (3 * (R:ℝ)) ^ b :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 * 3 ^ b * (R:ℝ) ^ (1 + b) := hfinal

end NCG
