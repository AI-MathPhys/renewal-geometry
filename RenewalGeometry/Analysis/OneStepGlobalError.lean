/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Global error of a perturbed one-step scheme (discrete Gronwall)

Let `Φₙ` be one-step maps that are `(1 + Lh)`-Lipschitz on a set `S` (a chart, kept by a
bootstrap or an enforced envelope).  If a numerical sequence satisfies
`X_{n+1} = Φₙ(Xₙ) + rₙ` (residuals) and a reference sequence (e.g. the grid sampling of a smooth
solution) satisfies `Y_{n+1} = Φₙ(Yₙ) + τₙ` (consistency errors), both staying in `S`, then
(`one_step_global_error`, via Mathlib's `discrete_gronwall`)

`‖Xₙ - Yₙ‖ ≤ (‖X₀ - Y₀‖ + ∑_{k<n} (‖r_k‖ + ‖τ_k‖)) e^{n L h}`,

and the residual sum is controlled by the residual energy through Cauchy–Schwarz
(`sum_norm_le_sqrt_mul_sqrt_sum_sq`): `∑_{k<n} ‖r_k‖ ≤ √n · (∑_{k<n} ‖r_k‖²)^{1/2}`.

This is the discrete-Gronwall layer of `prop:supp-gowdy-residual-control`
(emergent-spacetime manuscript): with `τ_k = O(h³)`, `n h ≤ T` it gives the global bound
`C(ε₀ + h² + ∑‖r_k‖)`.
-/

open Finset Real

namespace RenewalGeometry

namespace OneStepGlobalError

variable {E : Type*} [NormedAddCommGroup E]

/-- **Global error of a perturbed one-step scheme.** -/
theorem one_step_global_error (Φ : ℕ → E → E) (S : Set E) {L h : ℝ} (hLh : 0 ≤ L * h)
    (hLip : ∀ n, ∀ x ∈ S, ∀ y ∈ S, ‖Φ n x - Φ n y‖ ≤ (1 + L * h) * ‖x - y‖)
    (X Y r τ : ℕ → E) (hX : ∀ n, X (n + 1) = Φ n (X n) + r n)
    (hY : ∀ n, Y (n + 1) = Φ n (Y n) + τ n) (hXS : ∀ n, X n ∈ S) (hYS : ∀ n, Y n ∈ S) (n : ℕ) :
    ‖X n - Y n‖ ≤
      (‖X 0 - Y 0‖ + ∑ k ∈ range n, (‖r k‖ + ‖τ k‖)) * Real.exp (n * (L * h)) := by
  have hstep : ∀ m ≥ 0, ‖X (m + 1) - Y (m + 1)‖ ≤
      (1 + L * h) * ‖X m - Y m‖ + (‖r m‖ + ‖τ m‖) := by
    intro m _
    rw [hX, hY]
    calc ‖Φ m (X m) + r m - (Φ m (Y m) + τ m)‖
        = ‖(Φ m (X m) - Φ m (Y m)) + (r m - τ m)‖ := by congr 1; abel
      _ ≤ ‖Φ m (X m) - Φ m (Y m)‖ + ‖r m - τ m‖ := norm_add_le _ _
      _ ≤ (1 + L * h) * ‖X m - Y m‖ + (‖r m‖ + ‖τ m‖) := by
          gcongr
          · exact hLip m _ (hXS m) _ (hYS m)
          · exact norm_sub_le _ _
  have := discrete_gronwall (u := fun m => ‖X m - Y m‖) (c := fun _ => L * h)
    (b := fun m => ‖r m‖ + ‖τ m‖) (n₀ := 0) (norm_nonneg _) hstep (fun _ _ => hLh)
    (fun _ _ => by positivity) (Nat.zero_le n)
  rw [← Finset.range_eq_Ico, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  exact this

/-- **Cauchy–Schwarz for the residual sum**: `∑_{k<n} ‖r_k‖ ≤ √n · √(∑_{k<n} ‖r_k‖²)`. -/
theorem sum_norm_le_sqrt_mul_sqrt_sum_sq (r : ℕ → E) (n : ℕ) :
    ∑ k ∈ range n, ‖r k‖ ≤ Real.sqrt n * Real.sqrt (∑ k ∈ range n, ‖r k‖ ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (range n) (fun _ => (1 : ℝ)) (fun k => ‖r k‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one] at hcs
  rw [← Real.sqrt_mul (Nat.cast_nonneg n)]
  apply Real.le_sqrt_of_sq_le
  exact hcs

end OneStepGlobalError

end RenewalGeometry
