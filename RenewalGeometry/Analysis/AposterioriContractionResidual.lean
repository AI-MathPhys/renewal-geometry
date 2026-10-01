/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# A posteriori error bounds for approximate fixed points of contractions

* `aposteriori_fixed_point_bound`: if `T` is `q`-Lipschitz (`q < 1`) on a set `B` containing
  the fixed point `e_*` and an approximate fixed point `ẽ = T ẽ + δ`, then
  `‖ẽ - e_*‖ ≤ ‖δ‖ / (1 - q)`.
* `aposteriori_green_bound`: the boundary-value form.  For `T e = G (f + N e)` with `G` additive,
  an approximate solution `ẽ = b + G (f + N ẽ + r)` (boundary data `b`, residual `r`) satisfies
  `‖ẽ - e_*‖ ≤ (‖b‖ + Γ ‖r‖) / (1 - q)` whenever `‖G r‖ ≤ Γ ‖r‖`.  With `‖b‖ ≤ M_D(|d₋| + |d₊|)`
  (the dichotomy bounds of the boundary terms) and `Γ = C_G(1 + S)` this is the shape of
  `eq:supp-exact-residual-bound` (emergent-spacetime manuscript, `prop:supp-exact-boundary-residual`).
-/

namespace RenewalGeometry

namespace AposterioriContraction

variable {X : Type*} [NormedAddCommGroup X]

/-- **A posteriori bound for an approximate fixed point.** -/
theorem aposteriori_fixed_point_bound (T : X → X) {q : ℝ} (hq : q < 1) (B : Set X)
    (hLip : ∀ x ∈ B, ∀ y ∈ B, ‖T x - T y‖ ≤ q * ‖x - y‖) {e eT δ : X} (he : e ∈ B)
    (heT : eT ∈ B) (hfix : T e = e) (happrox : eT = T eT + δ) :
    ‖eT - e‖ ≤ ‖δ‖ / (1 - q) := by
  have h1 : ‖eT - e‖ ≤ q * ‖eT - e‖ + ‖δ‖ := by
    calc ‖eT - e‖ = ‖(T eT - T e) + δ‖ := by
          congr 1; rw [hfix]; nth_rewrite 1 [happrox]; abel
      _ ≤ ‖T eT - T e‖ + ‖δ‖ := norm_add_le _ _
      _ ≤ q * ‖eT - e‖ + ‖δ‖ := by gcongr; exact hLip _ heT _ he
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- **A posteriori boundary-residual bound** (Green-operator form). -/
theorem aposteriori_green_bound {Y : Type*} [NormedAddCommGroup Y] (G : Y →+ X) (N : X → Y)
    (f : Y) {q Γ : ℝ} (hq : q < 1) (B : Set X)
    (hLip : ∀ x ∈ B, ∀ y ∈ B, ‖G (f + N x) - G (f + N y)‖ ≤ q * ‖x - y‖)
    (hG : ∀ r, ‖G r‖ ≤ Γ * ‖r‖) {e eT b : X} {r : Y} (he : e ∈ B) (heT : eT ∈ B)
    (hfix : G (f + N e) = e) (happrox : eT = b + G (f + N eT + r)) :
    ‖eT - e‖ ≤ (‖b‖ + Γ * ‖r‖) / (1 - q) := by
  have h := aposteriori_fixed_point_bound (fun x => G (f + N x)) hq B hLip he heT hfix
    (δ := b + G r) (by
      show eT = G (f + N eT) + (b + G r)
      conv_lhs => rw [happrox]
      rw [map_add]; abel)
  calc ‖eT - e‖ ≤ ‖b + G r‖ / (1 - q) := h
    _ ≤ (‖b‖ + Γ * ‖r‖) / (1 - q) :=
      div_le_div_of_nonneg_right ((norm_add_le _ _).trans (by gcongr; exact hG r))
        (by linarith)

end AposterioriContraction

end RenewalGeometry
