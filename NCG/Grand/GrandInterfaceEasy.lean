/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Pair-carry identity and interface coercivity
  (`thm:ar-pair-carry`, `thm:interface-coercivity`,
   Gran-Tensor manuscript)

* `pair_carry`: the exact base-`q` identity — for
  `U = aq + r`, `V = bq + s` with `r, s < q`,
  `⌊UV/q⌋ = qab + as + br + ⌊rs/q⌋` and `UV ≡ rs (mod q)`; all
  irreducible floor nonlinearity lies in the carry `⌊rs/q⌋`;
* `interface_coercivity`: the boxed lower bound — if
  `‖Ax‖ ≥ δ_A‖x‖`, `‖Hu‖ ≥ δ_I‖u‖` (with `H` invertible), and
  `‖K·‖, ‖Kᴴ·‖ ≤ κ‖·‖`, then the Schur response
  `Λ = A - KH⁻¹Kᴴ` obeys
  `‖Λx‖ ≥ (δ_A - κ²/δ_I)‖x‖`.

Rendering disclosed: the second display of the interface record
(the resolvent bound for the full block matrix) is the
Feshbach-expansion bookkeeping over the same estimates.
-/

open Matrix

namespace NCG

/-- `thm:ar-pair-carry`: the exact base-`q` pair-carry
identity. -/
theorem pair_carry (q a b r s : ℕ) (hq : 0 < q) (_hr : r < q)
    (_hs : s < q) :
    ((a * q + r) * (b * q + s)) / q
      = q * (a * b) + a * s + b * r + (r * s) / q
    ∧ ((a * q + r) * (b * q + s)) % q = (r * s) % q := by
  have hexp : (a * q + r) * (b * q + s)
      = (q * (a * b) + a * s + b * r) * q + r * s := by
    ring
  constructor
  · rw [hexp, add_comm ((q * (a * b) + a * s + b * r) * q)
      (r * s), Nat.add_mul_div_right _ _ hq]
    exact Nat.add_comm _ _
  · rw [hexp, add_comm ((q * (a * b) + a * s + b * r) * q)
      (r * s), Nat.add_mul_mod_self_right]

/-- `thm:interface-coercivity`: the boxed Schur-response lower
bound `s_min(Λ) ≥ δ_A - κ²/δ_I`. -/
theorem interface_coercivity {e i : Type*} [Fintype e]
    [Fintype i] [DecidableEq i]
    (A : Matrix e e ℂ) (K : Matrix e i ℂ) (H : Matrix i i ℂ)
    (δA δI κ : ℝ) (hδI : 0 < δI)
    (hH : IsUnit H.det)
    (hA : ∀ x : e → ℂ, δA * ‖x‖ ≤ ‖A *ᵥ x‖)
    (hHl : ∀ u : i → ℂ, δI * ‖u‖ ≤ ‖H *ᵥ u‖)
    (hK : ∀ u : i → ℂ, ‖K *ᵥ u‖ ≤ κ * ‖u‖)
    (hKH : ∀ x : e → ℂ, ‖Kᴴ *ᵥ x‖ ≤ κ * ‖x‖)
    (hκ : 0 ≤ κ) (x : e → ℂ) :
    (δA - κ ^ 2 / δI) * ‖x‖
      ≤ ‖(A - K * H⁻¹ * Kᴴ) *ᵥ x‖ := by
  have hinv : ∀ y : i → ℂ, ‖H⁻¹ *ᵥ y‖ ≤ δI⁻¹ * ‖y‖ := by
    intro y
    have h := hHl (H⁻¹ *ᵥ y)
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH,
      Matrix.one_mulVec] at h
    rw [inv_mul_eq_div, le_div_iff₀ hδI, mul_comm]
    exact h
  have hchain : ‖(K * H⁻¹ * Kᴴ) *ᵥ x‖ ≤ κ ^ 2 / δI * ‖x‖ := by
    calc ‖(K * H⁻¹ * Kᴴ) *ᵥ x‖
        = ‖K *ᵥ (H⁻¹ *ᵥ (Kᴴ *ᵥ x))‖ := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ ≤ κ * ‖H⁻¹ *ᵥ (Kᴴ *ᵥ x)‖ := hK _
      _ ≤ κ * (δI⁻¹ * ‖Kᴴ *ᵥ x‖) := by
          exact mul_le_mul_of_nonneg_left (hinv _) hκ
      _ ≤ κ * (δI⁻¹ * (κ * ‖x‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ hκ
          exact mul_le_mul_of_nonneg_left (hKH x)
            (inv_nonneg.mpr hδI.le)
      _ = κ ^ 2 / δI * ‖x‖ := by
          field_simp
  calc (δA - κ ^ 2 / δI) * ‖x‖
      = δA * ‖x‖ - κ ^ 2 / δI * ‖x‖ := by ring
    _ ≤ ‖A *ᵥ x‖ - ‖(K * H⁻¹ * Kᴴ) *ᵥ x‖ :=
        sub_le_sub (hA x) hchain
    _ ≤ ‖A *ᵥ x - (K * H⁻¹ * Kᴴ) *ᵥ x‖ :=
        norm_sub_norm_le _ _
    _ = ‖(A - K * H⁻¹ * Kᴴ) *ᵥ x‖ := by
        rw [Matrix.sub_mulVec]

end NCG
