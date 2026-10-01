/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# One-dimensional periodic grid norms, inverse estimates and residual budgets
(infrastructure for `prop:supp-gowdy-residual-control`, `eq:supp-gowdy-state-error`,
`eq:supp-gowdy-residual-energy`; emergent-spacetime manuscript)

On the periodic grid `ℤ/N` with spacing `ℓ > 0` and values in a normed space `E` (the local
state space of a scheme):

* `fwdDiff ℓ v j = (v(j+1) − v(j))/ℓ` (`D₊`), the sup norm `‖v‖` (Pi norm), the grid `L²` norm
  `l2Norm ℓ v = (ℓ ∑ⱼ ‖v j‖²)^{1/2}` (`‖·‖_{2,ℓ}`) and the `C^r_ℓ` norm
  `crNorm r ℓ v = max_{k ≤ r} ‖D₊ᵏ v‖` (`‖·‖_{r,∞,ℓ}`).
* Inverse estimates: `‖D₊ v‖ ≤ (2/ℓ)‖v‖`, `‖D₊ᵏ v‖ ≤ (2/ℓ)ᵏ‖v‖`, `‖v‖ ≤ ℓ^{-1/2}‖v‖_{2,ℓ}`, and
  for `ℓ ≤ 2`, `‖v‖_{r,∞,ℓ} ≤ (2/ℓ)^r ℓ^{-1/2} ‖v‖_{2,ℓ}`; `crNorm` is a seminorm (triangle
  inequality `crNorm_add_le`).
* `sum_crNorm_le_sqrt_residualFlux` (**residual budget**): for residuals `r_j` with
  `𝓔_h = ∑_{j<n} ‖r_j‖²_{2,ℓ}/(2h)`, `𝓕_h = ℓ^{-(2r+1)} 𝓔_h` and `h = ℓ ≤ 2`,
  `∑_{j<n} ‖r_j‖_{r,∞,ℓ} ≤ 2^r √(2 n h) √𝓕_h` — the inverse-estimate/Cauchy–Schwarz step of the
  proof of `eq:supp-gowdy-state-error`.
* `global_error_crNorm`: discrete Grönwall in the `C^r_ℓ` norm: if the one-step maps are
  `(1 + Lh)`-Lipschitz in `‖·‖_{r,∞,ℓ}` on a set containing both the numerical and the sampled
  reference histories, with consistency errors `τ_k`, then
  `‖X_n − Y_n‖_{r,∞,ℓ} ≤ (‖X₀ − Y₀‖_{r,∞,ℓ} + ∑ ‖τ_k‖_{r,∞,ℓ} + 2^r √(2nh) √𝓕_h) e^{nLh}`.
  This is `eq:supp-gowdy-state-error` modulo the Lipschitz and consistency inputs of the concrete
  Gowdy split map.
-/

open Finset

namespace RenewalGeometry.PeriodicGridResidual

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ} [NeZero N]

/-- Forward difference `D₊ v (j) = (v(j+1) − v(j))/ℓ` on the periodic grid `ℤ/N`. -/
noncomputable def fwdDiff (ℓ : ℝ) (v : ZMod N → E) : ZMod N → E :=
  fun j => ℓ⁻¹ • (v (j + 1) - v j)

/-- Grid `L²` norm `‖v‖_{2,ℓ} = (ℓ ∑ⱼ ‖v j‖²)^{1/2}`. -/
noncomputable def l2Norm (ℓ : ℝ) (v : ZMod N → E) : ℝ := Real.sqrt (ℓ * ∑ j, ‖v j‖ ^ 2)

/-- `C^r_ℓ` norm `‖v‖_{r,∞,ℓ} = max_{k ≤ r} ‖D₊ᵏ v‖_∞`. -/
noncomputable def crNorm (r : ℕ) (ℓ : ℝ) (v : ZMod N → E) : ℝ :=
  (range (r + 1)).sup' nonempty_range_add_one fun k => ‖(fwdDiff ℓ)^[k] v‖

theorem fwdDiff_add (ℓ : ℝ) (v w : ZMod N → E) :
    fwdDiff ℓ (v + w) = fwdDiff ℓ v + fwdDiff ℓ w := by
  funext j; simp only [fwdDiff, Pi.add_apply]; rw [← smul_add]; congr 1; abel

theorem iterate_fwdDiff_add (ℓ : ℝ) (k : ℕ) (v w : ZMod N → E) :
    (fwdDiff ℓ)^[k] (v + w) = (fwdDiff ℓ)^[k] v + (fwdDiff ℓ)^[k] w := by
  induction k generalizing v w with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      fwdDiff_add, ih]

theorem iterate_fwdDiff_sub (ℓ : ℝ) (k : ℕ) (v w : ZMod N → E) :
    (fwdDiff ℓ)^[k] (v - w) = (fwdDiff ℓ)^[k] v - (fwdDiff ℓ)^[k] w := by
  have := iterate_fwdDiff_add ℓ k (v - w) w
  rw [sub_add_cancel] at this
  rw [this]; abel

/-- First inverse estimate `‖D₊ v‖ ≤ (2/ℓ) ‖v‖`. -/
theorem norm_fwdDiff_le {ℓ : ℝ} (hℓ : 0 < ℓ) (v : ZMod N → E) :
    ‖fwdDiff ℓ v‖ ≤ 2 / ℓ * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  simp only [fwdDiff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓ]
  have h1 := norm_le_pi_norm v (j + 1)
  have h2 := norm_le_pi_norm v j
  calc ℓ⁻¹ * ‖v (j + 1) - v j‖ ≤ ℓ⁻¹ * (‖v‖ + ‖v‖) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2)) (by positivity)
    _ = 2 / ℓ * ‖v‖ := by field_simp; ring

/-- Iterated inverse estimate `‖D₊ᵏ v‖ ≤ (2/ℓ)ᵏ ‖v‖`. -/
theorem norm_iterate_fwdDiff_le {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) (v : ZMod N → E) :
    ‖(fwdDiff ℓ)^[k] v‖ ≤ (2 / ℓ) ^ k * ‖v‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    calc ‖fwdDiff ℓ ((fwdDiff ℓ)^[k] v)‖ ≤ 2 / ℓ * ‖(fwdDiff ℓ)^[k] v‖ := norm_fwdDiff_le hℓ _
      _ ≤ 2 / ℓ * ((2 / ℓ) ^ k * ‖v‖) := by gcongr
      _ = (2 / ℓ) ^ (k + 1) * ‖v‖ := by ring

/-- `L² → L^∞` inverse estimate `‖v‖_∞ ≤ ℓ^{-1/2} ‖v‖_{2,ℓ}`. -/
theorem norm_le_l2Norm {ℓ : ℝ} (hℓ : 0 < ℓ) (v : ZMod N → E) :
    ‖v‖ ≤ l2Norm ℓ v / Real.sqrt ℓ := by
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ
  refine (pi_norm_le_iff_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hs.le)).2 fun j => ?_
  rw [le_div_iff₀ hs]
  calc ‖v j‖ * Real.sqrt ℓ = Real.sqrt (ℓ * ‖v j‖ ^ 2) := by
        rw [Real.sqrt_mul hℓ.le, Real.sqrt_sq (norm_nonneg _), mul_comm]
    _ ≤ Real.sqrt (ℓ * ∑ i, ‖v i‖ ^ 2) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun i _ => sq_nonneg _) (mem_univ j))
        hℓ.le)
    _ = l2Norm ℓ v := rfl

theorem crNorm_nonneg (r : ℕ) (ℓ : ℝ) (v : ZMod N → E) : 0 ≤ crNorm r ℓ v :=
  (norm_nonneg _).trans (Finset.le_sup' (fun k => ‖(fwdDiff ℓ)^[k] v‖) (mem_range.2 r.succ_pos))

theorem crNorm_add_le (r : ℕ) (ℓ : ℝ) (v w : ZMod N → E) :
    crNorm r ℓ (v + w) ≤ crNorm r ℓ v + crNorm r ℓ w := by
  refine Finset.sup'_le _ _ fun k hk => ?_
  rw [iterate_fwdDiff_add]
  exact (norm_add_le _ _).trans (add_le_add (Finset.le_sup' (fun k => ‖(fwdDiff ℓ)^[k] v‖) hk)
    (Finset.le_sup' (fun k => ‖(fwdDiff ℓ)^[k] w‖) hk))

/-- `‖v‖_{r,∞,ℓ} ≤ (2/ℓ)^r ‖v‖_∞` for `0 < ℓ ≤ 2`. -/
theorem crNorm_le_sup {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ2 : ℓ ≤ 2) (r : ℕ) (v : ZMod N → E) :
    crNorm r ℓ v ≤ (2 / ℓ) ^ r * ‖v‖ := by
  refine Finset.sup'_le _ _ fun k hk => ?_
  have h1 : 1 ≤ 2 / ℓ := by rw [le_div_iff₀ hℓ]; linarith
  refine (norm_iterate_fwdDiff_le hℓ k v).trans ?_
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 (Nat.lt_succ_iff.1 (mem_range.1 hk)))
    (norm_nonneg _)

/-- **`C^r_ℓ`–`L²` inverse estimate** `‖v‖_{r,∞,ℓ} ≤ (2/ℓ)^r ℓ^{-1/2} ‖v‖_{2,ℓ}`. -/
theorem crNorm_le_l2Norm {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ2 : ℓ ≤ 2) (r : ℕ) (v : ZMod N → E) :
    crNorm r ℓ v ≤ (2 / ℓ) ^ r * (l2Norm ℓ v / Real.sqrt ℓ) :=
  (crNorm_le_sup hℓ hℓ2 r v).trans (by gcongr; exact norm_le_l2Norm hℓ v)

/-- Residual energy `𝓔_h = ∑_{j<n} ‖r_j‖²_{2,ℓ}/(2h)` (`eq:supp-gowdy-residual-energy`). -/
noncomputable def residualEnergy (ℓ h : ℝ) (res : ℕ → ZMod N → E) (n : ℕ) : ℝ :=
  ∑ j ∈ range n, l2Norm ℓ (res j) ^ 2 / (2 * h)

/-- Normalized residual flux `𝓕_h = ℓ^{-(2r+1)} 𝓔_h`. -/
noncomputable def residualFlux (r : ℕ) (ℓ h : ℝ) (res : ℕ → ZMod N → E) (n : ℕ) : ℝ :=
  residualEnergy ℓ h res n / ℓ ^ (2 * r + 1)

/-- **Residual budget**: with `h = ℓ ∈ (0, 2]`,
`∑_{j<n} ‖r_j‖_{r,∞,ℓ} ≤ 2^r √(2 n h) √𝓕_h`. -/
theorem sum_crNorm_le_sqrt_residualFlux {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ2 : ℓ ≤ 2) (r : ℕ)
    (res : ℕ → ZMod N → E) (n : ℕ) :
    ∑ j ∈ range n, crNorm r ℓ (res j)
      ≤ 2 ^ r * Real.sqrt (2 * n * ℓ) * Real.sqrt (residualFlux r ℓ ℓ res n) := by
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ
  have hl2 : ∀ j, 0 ≤ l2Norm ℓ (res j) := fun j => Real.sqrt_nonneg _
  -- inverse estimate termwise
  have h1 : ∑ j ∈ range n, crNorm r ℓ (res j)
      ≤ (2 / ℓ) ^ r / Real.sqrt ℓ * ∑ j ∈ range n, l2Norm ℓ (res j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => (crNorm_le_l2Norm hℓ hℓ2 r (res j)).trans (le_of_eq ?_)
    ring
  -- Cauchy–Schwarz
  have hcs : ∑ j ∈ range n, l2Norm ℓ (res j)
      ≤ Real.sqrt n * Real.sqrt (∑ j ∈ range n, l2Norm ℓ (res j) ^ 2) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (range n) (fun _ => (1 : ℝ)) fun j => l2Norm ℓ (res j)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at this
    rw [← Real.sqrt_mul (Nat.cast_nonneg n)]
    exact Real.le_sqrt_of_sq_le this
  have hsum : ∑ j ∈ range n, l2Norm ℓ (res j) ^ 2
      = 2 * ℓ * ℓ ^ (2 * r + 1) * residualFlux r ℓ ℓ res n := by
    simp only [residualFlux, residualEnergy, ← Finset.sum_div]
    field_simp
  have hF0 : 0 ≤ residualFlux r ℓ ℓ res n := by
    unfold residualFlux residualEnergy
    exact div_nonneg (Finset.sum_nonneg fun j _ => by positivity) (by positivity)
  have hsq : Real.sqrt (∑ j ∈ range n, l2Norm ℓ (res j) ^ 2)
      = Real.sqrt (2 * ℓ) * (ℓ ^ r * Real.sqrt ℓ) * Real.sqrt (residualFlux r ℓ ℓ res n) := by
    rw [hsum, show 2 * ℓ * ℓ ^ (2 * r + 1) = (2 * ℓ) * (ℓ ^ r * Real.sqrt ℓ) ^ 2 by
      rw [mul_pow, Real.sq_sqrt hℓ.le, ← pow_mul]; ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  calc ∑ j ∈ range n, crNorm r ℓ (res j)
      ≤ (2 / ℓ) ^ r / Real.sqrt ℓ * (Real.sqrt n * Real.sqrt (∑ j ∈ range n,
          l2Norm ℓ (res j) ^ 2)) := h1.trans (by gcongr)
    _ = 2 ^ r * Real.sqrt (2 * n * ℓ) * Real.sqrt (residualFlux r ℓ ℓ res n) := by
        rw [hsq, show (2 : ℝ) * n * ℓ = n * (2 * ℓ) by ring,
          Real.sqrt_mul (Nat.cast_nonneg n), div_pow]
        field_simp

/-- **Discrete Grönwall in the `C^r_ℓ` norm** (abstract form of `eq:supp-gowdy-state-error`):
if the one-step maps `Φ_k` are `(1 + Lh)`-Lipschitz in `‖·‖_{r,∞,ℓ}` on a set `S` containing the
numerical history `X_{k+1} = Φ_k(X_k) + r_k` and the reference history
`Y_{k+1} = Φ_k(Y_k) + τ_k`, then with `h = ℓ ∈ (0,2]`
`‖X_n − Y_n‖_{r,∞,ℓ} ≤ (‖X₀ − Y₀‖_{r,∞,ℓ} + ∑_{k<n} ‖τ_k‖_{r,∞,ℓ} + 2^r √(2nh) √𝓕_h) e^{nLh}`. -/
theorem global_error_crNorm (r : ℕ) {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓ2 : ℓ ≤ 2) (hL : 0 ≤ L)
    (Φ : ℕ → (ZMod N → E) → (ZMod N → E)) (S : Set (ZMod N → E))
    (hLip : ∀ k, ∀ x ∈ S, ∀ y ∈ S, crNorm r ℓ (Φ k x - Φ k y) ≤ (1 + L * ℓ) * crNorm r ℓ (x - y))
    (X Y res τ : ℕ → ZMod N → E) (hX : ∀ k, X (k + 1) = Φ k (X k) + res k)
    (hY : ∀ k, Y (k + 1) = Φ k (Y k) + τ k) (hXS : ∀ k, X k ∈ S) (hYS : ∀ k, Y k ∈ S)
    (n : ℕ) :
    crNorm r ℓ (X n - Y n) ≤
      (crNorm r ℓ (X 0 - Y 0) + ∑ k ∈ range n, crNorm r ℓ (τ k)
        + 2 ^ r * Real.sqrt (2 * n * ℓ) * Real.sqrt (residualFlux r ℓ ℓ res n))
        * Real.exp (n * (L * ℓ)) := by
  have hneg : ∀ v : ZMod N → E, crNorm r ℓ (-v) = crNorm r ℓ v := by
    intro v
    unfold crNorm
    congr 1; funext k
    have hz : ∀ m : ℕ, (fwdDiff ℓ)^[m] (0 : ZMod N → E) = 0 := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [Function.iterate_succ_apply', ih]; funext j; simp [fwdDiff]
    have : (fwdDiff ℓ)^[k] (-v) = -(fwdDiff ℓ)^[k] v := by
      have h0 := iterate_fwdDiff_sub ℓ k (0 : ZMod N → E) v
      rw [zero_sub, hz, zero_sub] at h0
      exact h0
    rw [this, norm_neg]
  have hstep : ∀ m ≥ 0, crNorm r ℓ (X (m + 1) - Y (m + 1)) ≤
      (1 + L * ℓ) * crNorm r ℓ (X m - Y m) + (crNorm r ℓ (res m) + crNorm r ℓ (τ m)) := by
    intro m _
    rw [hX, hY]
    have e : Φ m (X m) + res m - (Φ m (Y m) + τ m) = (Φ m (X m) - Φ m (Y m)) + (res m + -τ m) := by
      abel
    rw [e]
    refine (crNorm_add_le _ _ _ _).trans (add_le_add (hLip m _ (hXS m) _ (hYS m)) ?_)
    exact (crNorm_add_le _ _ _ _).trans (by rw [hneg])
  have hLh : 0 ≤ L * ℓ := mul_nonneg hL hℓ.le
  have := discrete_gronwall (u := fun m => crNorm r ℓ (X m - Y m)) (c := fun _ => L * ℓ)
    (b := fun m => crNorm r ℓ (res m) + crNorm r ℓ (τ m)) (n₀ := 0) (crNorm_nonneg _ _ _) hstep
    (fun _ _ => hLh) (fun _ _ => add_nonneg (crNorm_nonneg _ _ _) (crNorm_nonneg _ _ _))
    (Nat.zero_le n)
  rw [← Finset.range_eq_Ico, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  refine this.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  rw [Finset.sum_add_distrib]
  have := sum_crNorm_le_sqrt_residualFlux hℓ hℓ2 r res n
  linarith


/-- Non-vacuity: the identity scheme is `1`-Lipschitz in every `C^r_ℓ` norm, so
`global_error_crNorm` applies (with `L = 0`) to any pair of histories. -/
example (r : ℕ) (ℓ : ℝ) :
    ∀ k : ℕ, ∀ x ∈ (Set.univ : Set (ZMod 5 → ℝ)), ∀ y ∈ (Set.univ : Set (ZMod 5 → ℝ)),
      crNorm r ℓ ((fun _ v => v : ℕ → (ZMod 5 → ℝ) → (ZMod 5 → ℝ)) k x
        - (fun _ v => v : ℕ → (ZMod 5 → ℝ) → (ZMod 5 → ℝ)) k y)
        ≤ (1 + 0 * ℓ) * crNorm r ℓ (x - y) := by
  intro k x _ y _; simp

end RenewalGeometry.PeriodicGridResidual
