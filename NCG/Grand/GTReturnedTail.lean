/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Source-minimal retained-tail derivative
  (`cor:GT-returned-tail-derivative`,
  Gran-Tensor manuscript)

* `gt_returned_tail_derivative`: the boxed RT.1 — for a
  retained-plus-tail linearization with `‖D‖ < 1` (ℓ²
  operator norm), the Neumann resolvent is the tail
  aggregate: `(1-D)⁻¹ = ∑ₙ Dⁿ` (proved as a two-sided
  inverse), the returned-word series converges with
  `HasSum (BDⁿC) (B(1-D)⁻¹C)`, and the exact reduced
  derivative satisfies
  `A + B(1-D)⁻¹C = A + ∑ₙ BDⁿC`.

The identification of the reachable–observable returned
quotient (`thm:universal-feedback-memory`) and the
stabilized Hankel rank of `[BD^{i+j}C]` as the minimum
tail dimension are the manuscript's realization layer
(cf. the repo's Kalman/minimal-realization records).
-/

open scoped Matrix.Norms.L2Operator

namespace NCG

/-- `cor:GT-returned-tail-derivative` (RT.1). -/
theorem gt_returned_tail_derivative {n : Type}
    [Fintype n] [DecidableEq n]
    (A B C D : Matrix n n ℂ) (hD : ‖D‖ < 1) :
    -- the Neumann resolvent is the aggregate
    ((1 - D)⁻¹ = ∑' k : ℕ, D ^ k)
    -- the returned-word series converges to the reduced
    -- coupling
    ∧ HasSum (fun k : ℕ => B * D ^ k * C)
        (B * (1 - D)⁻¹ * C)
    -- the boxed RT.1
    ∧ A + B * (1 - D)⁻¹ * C
        = A + ∑' k : ℕ, B * D ^ k * C := by
  haveI : CompleteSpace (Matrix n n ℂ) :=
    FiniteDimensional.complete ℂ _
  have hsummable : Summable fun k : ℕ => D ^ k :=
    summable_geometric_of_norm_lt_one hD
  have h1 : (1 - D) * (∑' k : ℕ, D ^ k) = 1 :=
    mul_neg_geom_series _ hD
  have hinv : (1 - D)⁻¹ = ∑' k : ℕ, D ^ k :=
    Matrix.inv_eq_right_inv h1
  have hsum : HasSum (fun k : ℕ => B * D ^ k * C)
      (B * (∑' k : ℕ, D ^ k) * C) :=
    (hsummable.hasSum.mul_left B).mul_right C
  refine ⟨hinv, ?_, ?_⟩
  · rw [hinv]
    exact hsum
  · rw [hinv, hsum.tsum_eq]

end NCG
