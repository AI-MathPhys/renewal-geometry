/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Stability of the rounded Lorentzian endpoint (perturbation cores)

**Theorem `thm:stability` / Corollary `cor:curved-stability`**: the
Lorentzian Dirac endpoint is stable under bounded perturbations of the
reset data.  The two mechanisms proved here:

* **squared-symbol shift** (`NCG.perturbation_sq_bound`):
  `‖(σ+V)² − σ²‖ ≤ ‖σ‖‖V‖ + ‖V‖‖σ‖ + ‖V‖²` — a small perturbation of
  the symbol moves the metric quadratic form by `O(‖V‖)`;
* **resolvent identity** (`NCG.resolvent_identity`):
  `u⁻¹ − v⁻¹ = u⁻¹(v − u)v⁻¹` — resolvents depend Lipschitz-ly on the
  operator, converting symbol closeness into resolvent closeness.

The Kato–Rellich self-adjointness of the perturbed endpoint and the
Sobolev-domain packaging are the noted analytic steps.
-/

namespace NCG

/-- **Resolvent identity**: `u⁻¹ − v⁻¹ = u⁻¹(v − u)v⁻¹` — the
Lipschitz dependence of resolvents on the operator. -/
theorem resolvent_identity {A : Type*} [Ring A] (u v : Aˣ) :
    (↑u⁻¹ : A) - ↑v⁻¹ = ↑u⁻¹ * ((v : A) - ↑u) * ↑v⁻¹ := by
  rw [mul_sub, Units.inv_mul, sub_mul, one_mul, mul_assoc,
    Units.mul_inv, mul_one]

/-- **Theorem `thm:stability` (squared-symbol shift)**: a bounded
perturbation `V` of the symbol moves the squared symbol — the metric
quadratic form — by at most `‖σ‖‖V‖ + ‖V‖‖σ‖ + ‖V‖²`. -/
theorem perturbation_sq_bound {A : Type*} [NormedRing A] (σ V : A) :
    ‖(σ + V) ^ 2 - σ ^ 2‖ ≤ ‖σ‖ * ‖V‖ + ‖V‖ * ‖σ‖ + ‖V‖ ^ 2 := by
  have hexp : (σ + V) ^ 2 - σ ^ 2 = σ * V + V * σ + V * V := by
    noncomm_ring
  rw [hexp]
  have h1 := norm_mul_le σ V
  have h2 := norm_mul_le V σ
  have h3 := norm_mul_le V V
  calc ‖σ * V + V * σ + V * V‖
      ≤ ‖σ * V + V * σ‖ + ‖V * V‖ := norm_add_le _ _
    _ ≤ ‖σ * V‖ + ‖V * σ‖ + ‖V * V‖ := by
        have := norm_add_le (σ * V) (V * σ)
        linarith
    _ ≤ ‖σ‖ * ‖V‖ + ‖V‖ * ‖σ‖ + ‖V‖ ^ 2 := by
        rw [pow_two]
        linarith

/-- **Theorem `thm:curved-limit` (quantitative resolvent
mechanism)**: the resolvent difference is controlled by the operator
difference — `‖u⁻¹ − v⁻¹‖ ≤ ‖u⁻¹‖·‖v − u‖·‖v⁻¹‖`, so consistency of
the operators on a core forces convergence of the resolvents. -/
theorem resolvent_diff_bound {A : Type*} [NormedRing A] (u v : Aˣ) :
    ‖(↑u⁻¹ : A) - ↑v⁻¹‖
      ≤ ‖(↑u⁻¹ : A)‖ * ‖(v : A) - ↑u‖ * ‖(↑v⁻¹ : A)‖ := by
  rw [resolvent_identity]
  calc ‖(↑u⁻¹ : A) * ((v : A) - ↑u) * ↑v⁻¹‖
      ≤ ‖(↑u⁻¹ : A) * ((v : A) - ↑u)‖ * ‖(↑v⁻¹ : A)‖ := norm_mul_le _ _
    _ ≤ ‖(↑u⁻¹ : A)‖ * ‖(v : A) - ↑u‖ * ‖(↑v⁻¹ : A)‖ := by
        have h := norm_mul_le (↑u⁻¹ : A) ((v : A) - ↑u)
        nlinarith [norm_nonneg ((↑v⁻¹ : A))]

/-- Difference of squares without commutativity:
`v² − u² = v(v − u) + (v − u)u` — the manuscript's expansion in
Lemma `lem:optical-distance-stability`. -/
theorem sq_sub_sq_noncomm {A : Type*} [Ring A] (u v : A) :
    v ^ 2 - u ^ 2 = v * (v - u) + (v - u) * u := by
  noncomm_ring

/-- **Lemma `lem:optical-distance-stability` (the displayed bound)**:
for invertible elements with `‖u⁻¹‖, ‖v⁻¹‖ ≤ c` and `‖u‖, ‖v‖ ≤ 1`,

`‖u⁻² − v⁻²‖ ≤ 2·c⁴·‖v − u‖`.

Instantiated with symmetric matrix fields `m₀I ⪯ M, M̃ ⪯ I` (where the
spectral bound gives `‖M⁻¹‖ ≤ m₀⁻¹ = c`), this is exactly the
manuscript's `‖M⁻² − M̃⁻²‖ ≤ 2m₀⁻⁴‖M − M̃‖`, proved via the
noncommutative identity `u⁻² − v⁻² = u⁻²(v² − u²)v⁻²` and the
difference-of-squares expansion.  The spectral input
`m₀I ⪯ M ⟹ ‖M⁻¹‖ ≤ m₀⁻¹` and the induced local-uniform convergence of
optical distances are the noted steps. -/
theorem inv_sq_diff_bound {A : Type*} [NormedRing A] (u v : Aˣ)
    (c : ℝ) (hu : ‖(↑u⁻¹ : A)‖ ≤ c) (hv : ‖(↑v⁻¹ : A)‖ ≤ c)
    (hun : ‖(u : A)‖ ≤ 1) (hvn : ‖(v : A)‖ ≤ 1) :
    ‖(↑(u ^ 2)⁻¹ : A) - ↑(v ^ 2)⁻¹‖ ≤ 2 * c ^ 4 * ‖(v : A) - ↑u‖ := by
  have hc0 : 0 ≤ c := le_trans (norm_nonneg _) hu
  have husq : ‖(↑(u ^ 2)⁻¹ : A)‖ ≤ c ^ 2 := by
    have : ((u ^ 2)⁻¹ : Aˣ) = u⁻¹ ^ 2 := by rw [inv_pow]
    rw [this]
    calc ‖((u⁻¹ ^ 2 : Aˣ) : A)‖ = ‖(↑u⁻¹ : A) * ↑u⁻¹‖ := by
          rw [show ((u⁻¹ ^ 2 : Aˣ) : A) = (↑u⁻¹ : A) * ↑u⁻¹ from by
            rw [pow_two, Units.val_mul]]
      _ ≤ ‖(↑u⁻¹ : A)‖ * ‖(↑u⁻¹ : A)‖ := norm_mul_le _ _
      _ ≤ c * c := mul_le_mul hu hu (norm_nonneg _) hc0
      _ = c ^ 2 := (pow_two c).symm
  have hvsq : ‖(↑(v ^ 2)⁻¹ : A)‖ ≤ c ^ 2 := by
    have : ((v ^ 2)⁻¹ : Aˣ) = v⁻¹ ^ 2 := by rw [inv_pow]
    rw [this]
    calc ‖((v⁻¹ ^ 2 : Aˣ) : A)‖ = ‖(↑v⁻¹ : A) * ↑v⁻¹‖ := by
          rw [show ((v⁻¹ ^ 2 : Aˣ) : A) = (↑v⁻¹ : A) * ↑v⁻¹ from by
            rw [pow_two, Units.val_mul]]
      _ ≤ ‖(↑v⁻¹ : A)‖ * ‖(↑v⁻¹ : A)‖ := norm_mul_le _ _
      _ ≤ c * c := mul_le_mul hv hv (norm_nonneg _) hc0
      _ = c ^ 2 := (pow_two c).symm
  have hdiff : ‖((v ^ 2 : Aˣ) : A) - ↑(u ^ 2)‖ ≤ 2 * ‖(v : A) - ↑u‖ := by
    have hexp : ((v ^ 2 : Aˣ) : A) - ↑(u ^ 2)
        = (v : A) * ((v : A) - ↑u) + ((v : A) - ↑u) * ↑u := by
      rw [show ((v ^ 2 : Aˣ) : A) = (v : A) ^ 2 from Units.val_pow_eq_pow_val v 2,
        show ((u ^ 2 : Aˣ) : A) = (u : A) ^ 2 from Units.val_pow_eq_pow_val u 2]
      exact sq_sub_sq_noncomm _ _
    rw [hexp]
    calc ‖(v : A) * ((v : A) - ↑u) + ((v : A) - ↑u) * ↑u‖
        ≤ ‖(v : A) * ((v : A) - ↑u)‖ + ‖((v : A) - ↑u) * ↑u‖ :=
          norm_add_le _ _
      _ ≤ ‖(v : A)‖ * ‖(v : A) - ↑u‖ + ‖(v : A) - ↑u‖ * ‖(u : A)‖ := by
          have h1 := norm_mul_le (v : A) ((v : A) - ↑u)
          have h2 := norm_mul_le ((v : A) - ↑u) (↑u : A)
          linarith
      _ ≤ 2 * ‖(v : A) - ↑u‖ := by
          have h3 : ‖(v : A)‖ * ‖(v : A) - ↑u‖ ≤ ‖(v : A) - ↑u‖ := by
            calc ‖(v : A)‖ * ‖(v : A) - ↑u‖
                ≤ 1 * ‖(v : A) - ↑u‖ :=
                  mul_le_mul_of_nonneg_right hvn (norm_nonneg _)
              _ = ‖(v : A) - ↑u‖ := one_mul _
          have h4 : ‖(v : A) - ↑u‖ * ‖(u : A)‖ ≤ ‖(v : A) - ↑u‖ := by
            calc ‖(v : A) - ↑u‖ * ‖(u : A)‖
                ≤ ‖(v : A) - ↑u‖ * 1 :=
                  mul_le_mul_of_nonneg_left hun (norm_nonneg _)
              _ = ‖(v : A) - ↑u‖ := mul_one _
          linarith
  calc ‖(↑(u ^ 2)⁻¹ : A) - ↑(v ^ 2)⁻¹‖
      ≤ ‖(↑(u ^ 2)⁻¹ : A)‖ * ‖((v ^ 2 : Aˣ) : A) - ↑(u ^ 2)‖
          * ‖(↑(v ^ 2)⁻¹ : A)‖ := resolvent_diff_bound (u ^ 2) (v ^ 2)
    _ ≤ c ^ 2 * (2 * ‖(v : A) - ↑u‖) * c ^ 2 := by
        have hstep1 : ‖(↑(u ^ 2)⁻¹ : A)‖
              * ‖((v ^ 2 : Aˣ) : A) - ↑(u ^ 2)‖
            ≤ c ^ 2 * (2 * ‖(v : A) - ↑u‖) :=
          mul_le_mul husq hdiff (norm_nonneg _) (by positivity)
        exact mul_le_mul hstep1 hvsq (norm_nonneg _) (by positivity)
    _ = 2 * c ^ 4 * ‖(v : A) - ↑u‖ := by ring

end NCG
