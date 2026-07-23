/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The renewal measured causal set and 2d Minkowski emergence

The order-theoretic continuum ladder of the manuscript, in the regular
commuting regime `𝒲_CP ≅ ℕ^c` with product predictive order:

* **Proposition `prop:measured-causet`** (renewal measured causal set):
  with calibrated generator lengths `ℓᵢ > 0`, the rank
  `Λ(x) = Σᵢ ℓᵢ xᵢ` is strictly increasing along strict divisibility, order
  intervals are the finite boxes `[x, y] = ∏ᵢ {xᵢ, …, yᵢ}` with
  `|[x,y]| = ∏ᵢ (yᵢ − xᵢ + 1)`, and rank level sets are antichains;
* **Proposition `prop:commuting-order`** (commuting order and interval
  growth): the exact interval count `∏ᵢ (yᵢ − xᵢ + 1)` — for balanced
  intervals of rank separation `τ` this is the `≍ τ^c` growth identifying
  the interval-growth dimension with `q_alg = c`;
* **Theorem `thm:minkowski-2d`** (two-dimensional Minkowski emergence): in
  null coordinates `u, v` with `t = (u+v)/2`, `ξ = (v−u)/2`, the product
  order is exactly the Minkowski causal order `Δt ≥ |Δξ|`, and the
  order/volume time separation satisfies `Δu·Δv = Δt² − Δξ²` — the flat
  proper time.  (For `c ≥ 3` the deterministic product cone is polyhedral,
  Theorem `thm:obstruction`; the rounding is the Clifford layer.)
-/

namespace NCG

/-! ### The measured causal set `ℕ^c` -/

variable {c : ℕ}

/-- The calibrated **rank** (quotient length) of the free commuting model:
`Λ(x) = Σᵢ ℓᵢ xᵢ` for generator lengths `ℓ`. -/
def productRank (ℓ : Fin c → ℕ) (x : Fin c → ℕ) : ℕ :=
  ∑ i, ℓ i * x i

/-- **Rank is strictly increasing along strict divisibility**
(Proposition `prop:measured-causet`): the calibrated length is a time
function for the product predictive order. -/
theorem productRank_strict_mono (ℓ : Fin c → ℕ) (hℓ : ∀ i, 0 < ℓ i)
    {x y : Fin c → ℕ} (hxy : x ≤ y) (hne : x ≠ y) :
    productRank ℓ x < productRank ℓ y := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
  · exact Nat.mul_le_mul_left _ (hxy i)
  · exact mul_lt_mul_of_pos_left (lt_of_le_of_ne (hxy j) hj) (hℓ j)

/-- **Rank level sets are antichains**
(Proposition `prop:measured-causet`): comparable classes of equal rank
coincide. -/
theorem eq_of_productRank_eq (ℓ : Fin c → ℕ) (hℓ : ∀ i, 0 < ℓ i)
    {x y : Fin c → ℕ} (hxy : x ≤ y)
    (hrank : productRank ℓ x = productRank ℓ y) : x = y := by
  by_contra hne
  exact absurd hrank (ne_of_lt (productRank_strict_mono ℓ hℓ hxy hne))

/-- **Exact interval counting** (Propositions `prop:measured-causet` and
`prop:commuting-order`): the order interval of the product order is the
finite box with `|[x, y]| = ∏ᵢ (yᵢ + 1 − xᵢ)`.  Along balanced intervals
`yᵢ − xᵢ ≃ τ/c` this is the `≍ τ^c` interval growth identifying the
interval-growth dimension of the predictive order with `q_alg = c`. -/
theorem card_interval (x y : Fin c → ℕ) :
    (Finset.Icc x y).card = ∏ i, (y i + 1 - x i) := by
  rw [Pi.card_Icc]
  simp [Nat.card_Icc]

/-- Local finiteness of the renewal causal order: intervals of the product
order are finite (Proposition `prop:measured-causet`). -/
theorem interval_finite (x y : Fin c → ℕ) :
    ∃ s : Finset (Fin c → ℕ), ∀ z, z ∈ s ↔ x ≤ z ∧ z ≤ y :=
  ⟨Finset.Icc x y, fun _z => Finset.mem_Icc⟩

/-! ### Two-dimensional Minkowski emergence -/

/-- **The flat proper time in null coordinates**
(Theorem `thm:minkowski-2d`): with `Δt = (Δu + Δv)/2` and
`Δξ = (Δv − Δu)/2`,

`Δu · Δv = Δt² − Δξ²`,

so the order/volume time separation `τ = √(Δu Δv)` of the `c = 2` product
model is the Minkowski proper time. -/
theorem minkowski_proper_time (du dv : ℝ) :
    du * dv = ((du + dv) / 2) ^ 2 - ((dv - du) / 2) ^ 2 := by
  ring

/-- **The product order is the Minkowski causal order**
(Theorem `thm:minkowski-2d`): both null increments are nonnegative iff
`|Δξ| ≤ Δt`, the future light-cone condition of the flat metric
`−dt² + dξ²`. -/
theorem minkowski_causal_order (du dv : ℝ) :
    (0 ≤ du ∧ 0 ≤ dv) ↔ |(dv - du) / 2| ≤ (du + dv) / 2 := by
  rw [abs_le]
  constructor
  · intro h
    constructor <;> linarith [h.1, h.2]
  · intro h
    constructor <;> linarith [h.1, h.2]

/-- The proper time vanishes exactly on the null faces: for causal
increments, `Δu Δv = 0` iff one of the null coordinates is constant
(Theorem `thm:minkowski-2d`, null boundary of the cone). -/
theorem proper_time_eq_zero_iff (du dv : ℝ) (_hdu : 0 ≤ du) (_hdv : 0 ≤ dv) :
    du * dv = 0 ↔ du = 0 ∨ dv = 0 :=
  mul_eq_zero

end NCG
