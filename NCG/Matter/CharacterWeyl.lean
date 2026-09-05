/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Character-resolved scalar Weyl functions
  (`thm:character-weyl`, SM_emergence)

On a one-dimensional character line the marked renewal kernel acts
by the scalar `λ_d·φ_d(s)`, so the renewal series sums to the
self-energy `Σ_d = λφ/(1-λφ)`:

* `eventCountWaiting` — the critical event-count waiting law
  `q_d(n) = (1/n)·C(nd,n-1)·(1/d)^{n-1}·(1-1/d)^{nd-n+1}`;
* `event_count_waiting_one` / `event_count_waiting_two` — its first
  two weights `q_d(1) = (1-1/d)^d` and `q_d(2) = (1-1/d)^{2d-1}`;
* `renewal_self_energy_sum` — the scalar geometric summation
  `Σ_{n≥1} (λφ)ⁿ = λφ/(1-λφ)` for `|λφ| < 1`;
* `renewal_self_energy_dyson` — the formal fixed-point equation
  `S = x + x·S` for `S = x·(1-x)⁻¹` in `ℝ⟦X⟧`;
* `self_energy_coeff` — the leading dressed coefficients
  `S₁ = λq(1)`, `S₂ = λq(2) + λ²q(1)²`;
* `character_weyl_nonproportional` — with `(λ₅,λ₃) = (-1/5,-1/3)`
  and the degree-five/degree-three waiting laws, the two dressed
  self-energies are not proportional.

The `-1/5` and `-1/3` type-walk eigenvalues are the declared
representation-theoretic inputs, and the common square-root
threshold exponent (an asymptotic side remark) is not formalized.
-/

namespace NCG

/-- The critical event-count waiting law of
`thm:event-count-kernel`:
`q_d(n) = (1/n)·C(nd,n-1)·(1/d)^{n-1}·(1-1/d)^{nd-n+1}`. -/
noncomputable def eventCountWaiting (d n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * (Nat.choose (n * d) (n - 1) : ℝ)
    * (1 / (d : ℝ)) ^ (n - 1) * (1 - 1 / (d : ℝ)) ^ (n * d - n + 1)

/-- First waiting weight: `q_d(1) = (1-1/d)^d`. -/
theorem event_count_waiting_one (d : ℕ) (hd : 1 ≤ d) :
    eventCountWaiting d 1 = (1 - 1 / (d : ℝ)) ^ d := by
  have h1 : d - 1 + 1 = d := by omega
  simp [eventCountWaiting, h1]

/-- Second waiting weight: `q_d(2) = (1-1/d)^{2d-1}`. -/
theorem event_count_waiting_two (d : ℕ) (hd : 1 ≤ d) :
    eventCountWaiting d 2 = (1 - 1 / (d : ℝ)) ^ (2 * d - 1) := by
  have h1 : 2 * d - 2 + 1 = 2 * d - 1 := by omega
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hexp : (2 - 1 : ℕ) = 1 := rfl
  simp only [eventCountWaiting, h1, hexp, Nat.choose_one_right]
  rw [pow_one]
  push_cast
  have ha : (1 : ℝ) / 2 * (2 * (d : ℝ)) * (1 / (d : ℝ)) = 1 := by
    field_simp
  linear_combination (1 - 1 / (d : ℝ)) ^ (2 * d - 1) * ha

/-- Scalar renewal summation: for `|x| < 1` the renewal series of a
one-dimensional character line sums to `x/(1-x)`. -/
theorem renewal_self_energy_sum {x : ℝ} (hx : |x| < 1) :
    ∑' n : ℕ, x ^ (n + 1) = x / (1 - x) := by
  have hgeom := tsum_geometric_of_abs_lt_one hx
  calc ∑' n : ℕ, x ^ (n + 1) = ∑' n : ℕ, x * x ^ n := by
        apply tsum_congr
        intro n
        rw [pow_succ']
  _ = x * ∑' n : ℕ, x ^ n := by rw [tsum_mul_left]
  _ = x / (1 - x) := by rw [hgeom, div_eq_mul_inv]

/-- Formal renewal fixed point: `S = x·(1-x)⁻¹` satisfies the Dyson
equation `S = x + x·S` in `ℝ⟦X⟧` when `x` has no constant term. -/
theorem renewal_self_energy_dyson (x : PowerSeries ℝ)
    (hx : PowerSeries.constantCoeff x = 0) :
    x * (1 - x)⁻¹ = x + x * (x * (1 - x)⁻¹) := by
  have hunit : PowerSeries.constantCoeff (1 - x) ≠ 0 := by
    simp [hx]
  have hinv : (1 - x) * (1 - x)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ hunit
  have hone : (1 : PowerSeries ℝ) + x * (1 - x)⁻¹ = (1 - x)⁻¹ := by
    calc (1 : PowerSeries ℝ) + x * (1 - x)⁻¹
        = (1 - x) * (1 - x)⁻¹ + x * (1 - x)⁻¹ := by rw [hinv]
    _ = (1 - x)⁻¹ := by ring
  calc x * (1 - x)⁻¹ = x * (1 + x * (1 - x)⁻¹) := by rw [hone]
  _ = x + x * (x * (1 - x)⁻¹) := by ring

private theorem coeff_mul_one_zeros (A B : PowerSeries ℝ)
    (hA : PowerSeries.constantCoeff A = 0)
    (hB : PowerSeries.constantCoeff B = 0) :
    PowerSeries.coeff 1 (A * B) = 0 := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hA, hB]

private theorem coeff_mul_two_zeros (A B : PowerSeries ℝ)
    (hA : PowerSeries.constantCoeff A = 0)
    (hB : PowerSeries.constantCoeff B = 0) :
    PowerSeries.coeff 2 (A * B)
      = PowerSeries.coeff 1 A * PowerSeries.coeff 1 B := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hA, hB]

/-- Leading coefficients of the dressed self-energy
`S = (λ·φ)(1-λ·φ)⁻¹`: `S₁ = λ·q(1)` and `S₂ = λ·q(2) + λ²·q(1)²`. -/
theorem self_energy_coeff (φ : PowerSeries ℝ) (lam : ℝ)
    (h0 : PowerSeries.constantCoeff φ = 0) :
    PowerSeries.coeff 1 ((lam • φ) * (1 - lam • φ)⁻¹)
        = lam * PowerSeries.coeff 1 φ
      ∧ PowerSeries.coeff 2 ((lam • φ) * (1 - lam • φ)⁻¹)
        = lam * PowerSeries.coeff 2 φ
          + lam ^ 2 * (PowerSeries.coeff 1 φ) ^ 2 := by
  set x : PowerSeries ℝ := lam • φ with hxdef
  have h0' : PowerSeries.coeff 0 φ = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h0
  have hx0 : PowerSeries.constantCoeff x = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hxdef,
      PowerSeries.coeff_smul, h0', smul_zero]
  set S : PowerSeries ℝ := x * (1 - x)⁻¹ with hSdef
  have hS0 : PowerSeries.constantCoeff S = 0 := by
    rw [hSdef, map_mul, hx0, zero_mul]
  have hdy : S = x + x * S := renewal_self_energy_dyson x hx0
  have hc1x : PowerSeries.coeff 1 x = lam * PowerSeries.coeff 1 φ := by
    rw [hxdef, PowerSeries.coeff_smul, smul_eq_mul]
  have hc2x : PowerSeries.coeff 2 x = lam * PowerSeries.coeff 2 φ := by
    rw [hxdef, PowerSeries.coeff_smul, smul_eq_mul]
  have hc1 : PowerSeries.coeff 1 S = lam * PowerSeries.coeff 1 φ := by
    have h1 := congrArg (fun ψ : PowerSeries ℝ =>
      PowerSeries.coeff 1 ψ) hdy
    simp only [map_add] at h1
    rw [coeff_mul_one_zeros x S hx0 hS0, add_zero, hc1x] at h1
    exact h1
  refine ⟨hc1, ?_⟩
  have h2 := congrArg (fun ψ : PowerSeries ℝ =>
    PowerSeries.coeff 2 ψ) hdy
  simp only [map_add] at h2
  rw [coeff_mul_two_zeros x S hx0 hS0, hc1x, hc2x, hc1] at h2
  rw [h2]
  ring

/-- `thm:character-weyl` (non-proportionality): with the type-walk
eigenvalues `(λ₅,λ₃) = (-1/5,-1/3)` and the degree-five and
degree-three event-count waiting laws, the two dressed character
self-energies `Σ_d = λ_dφ_d(1-λ_dφ_d)⁻¹` are not proportional. -/
theorem character_weyl_nonproportional (φ5 φ3 : PowerSeries ℝ)
    (h05 : PowerSeries.constantCoeff φ5 = 0)
    (h03 : PowerSeries.constantCoeff φ3 = 0)
    (h15 : PowerSeries.coeff 1 φ5 = eventCountWaiting 5 1)
    (h25 : PowerSeries.coeff 2 φ5 = eventCountWaiting 5 2)
    (h13 : PowerSeries.coeff 1 φ3 = eventCountWaiting 3 1)
    (h23 : PowerSeries.coeff 2 φ3 = eventCountWaiting 3 2) :
    ¬ ∃ c : ℝ,
      ((-(1 / 5) : ℝ) • φ5) * (1 - (-(1 / 5) : ℝ) • φ5)⁻¹
        = c • (((-(1 / 3) : ℝ) • φ3)
          * (1 - (-(1 / 3) : ℝ) • φ3)⁻¹) := by
  rintro ⟨c, hc⟩
  obtain ⟨hA1, hA2⟩ := self_energy_coeff φ5 (-(1 / 5)) h05
  obtain ⟨hB1, hB2⟩ := self_energy_coeff φ3 (-(1 / 3)) h03
  have q51 : eventCountWaiting 5 1 = (4 / 5 : ℝ) ^ 5 := by
    rw [event_count_waiting_one 5 (by norm_num)]
    norm_num
  have q52 : eventCountWaiting 5 2 = (4 / 5 : ℝ) ^ 9 := by
    rw [event_count_waiting_two 5 (by norm_num)]
    norm_num
  have q31 : eventCountWaiting 3 1 = (2 / 3 : ℝ) ^ 3 := by
    rw [event_count_waiting_one 3 (by norm_num)]
    norm_num
  have q32 : eventCountWaiting 3 2 = (2 / 3 : ℝ) ^ 5 := by
    rw [event_count_waiting_two 3 (by norm_num)]
    norm_num
  have e1 := congrArg (fun ψ : PowerSeries ℝ =>
    PowerSeries.coeff 1 ψ) hc
  have e2 := congrArg (fun ψ : PowerSeries ℝ =>
    PowerSeries.coeff 2 ψ) hc
  simp only [PowerSeries.coeff_smul, smul_eq_mul] at e1 e2
  rw [hA1, hB1, h15, h13, q51, q31] at e1
  rw [hA2, hB2, h25, h23, h15, h13, q52, q32, q51, q31] at e2
  norm_num at e1 e2
  linarith [e1, e2]

end NCG
