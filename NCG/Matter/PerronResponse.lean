/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The universal Perron tilt of the six-port frame
  (`thm:perron-response`, SM_emergence)

For `P_η = (1-η)I₆ + (η/6)J₆` and `ℒ_η(z) = P_η·diag(e^z)`, the
local Perron data at `z = 0` in exact jet form:

* `perron_response_zero` — `ρ(0) = 1` with left vector `𝟙ᵀ/6` and
  right vector `𝟙`;
* `perron_response_first` — the first-order left-eigenvector jet
  equation is satisfied exactly by `ℓ₁ = z₀/(6η)` with the
  centering normalization `Σℓ₁ = 0`;
* `perron_response_hessian` — the second-order coefficient of
  `log ρ` equals `((2-η)/(6η))·‖z₀‖²`, i.e. the boxed Hessian
  `∇²log ρ(0) = ((2-η)/(6η))(I₆ - Π₆)`.

The identification of these jets with the analytic derivatives of
the simple Perron root is the standard finite-dimensional
perturbation dictionary (declared).
-/

namespace NCG

open Matrix

noncomputable section

/-- The tilt kernel `P_η = (1-η)I + (η/6)J`. -/
def perronP (η : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun i j => (if i = j then 1 - η else 0) + η / 6

/-- Row action: `(P_η·v)_i = (1-η)v_i + (η/6)Σv`. -/
lemma perronP_mulVec (η : ℝ) (v : Fin 6 → ℝ) (i : Fin 6) :
    (perronP η *ᵥ v) i = (1 - η) * v i + η / 6 * ∑ k, v k := by
  simp only [Matrix.mulVec, dotProduct, perronP, Matrix.of_apply]
  rw [Finset.sum_congr rfl
    (fun k _ => add_mul (if i = k then 1 - η else 0) (η / 6) (v k)),
    Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg (fun h => hk h.symm), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [← Finset.mul_sum]

/-- Column action: `(vᵀP_η)_j = (1-η)v_j + (η/6)Σv`. -/
lemma perronP_vecMul (η : ℝ) (v : Fin 6 → ℝ) (j : Fin 6) :
    (v ᵥ* perronP η) j = (1 - η) * v j + η / 6 * ∑ k, v k := by
  simp only [Matrix.vecMul, dotProduct, perronP, Matrix.of_apply]
  rw [Finset.sum_congr rfl
    (fun k _ => mul_add (v k) (if k = j then 1 - η else 0) (η / 6)),
    Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single j]
    · rw [if_pos rfl, mul_comm]
    · intro k _ hk
      rw [if_neg hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · rw [← Finset.sum_mul, mul_comm]

/-- The centered-sum identity `Σ(z_k - z̄) = 0`. -/
lemma centered_sum (z : Fin 6 → ℝ) :
    ∑ k, (z k - (∑ l, z l) / 6) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
  simp
  ring

/-- The centered quadratic identities. -/
lemma centered_sq (z : Fin 6 → ℝ) :
    (∑ k, (z k - (∑ l, z l) / 6) * z k
        = ∑ k, (z k - (∑ l, z l) / 6) ^ 2) := by
  have h1 : ∑ k, (z k - (∑ l, z l) / 6) ^ 2
      = ∑ k, ((z k - (∑ l, z l) / 6) * z k
          - (z k - (∑ l, z l) / 6) * ((∑ l, z l) / 6)) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h1, Finset.sum_sub_distrib, ← Finset.sum_mul,
    centered_sum, zero_mul, sub_zero]

/-- Zeroth order: `𝟙ᵀ/6` and `𝟙` are the left and right Perron
vectors of `P_η` at eigenvalue `1`. -/
theorem perron_response_zero (η : ℝ) :
    ((fun _ => (1 / 6 : ℝ)) ᵥ* perronP η = fun _ => (1 / 6 : ℝ))
    ∧ (perronP η *ᵥ (fun _ => (1 : ℝ)) = fun _ => (1 : ℝ)) := by
  constructor
  · funext j
    rw [perronP_vecMul, Finset.sum_const, Finset.card_univ]
    simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  · funext i
    rw [perronP_mulVec, Finset.sum_const, Finset.card_univ]
    simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    ring

/-- First order: `ℓ₁ = z₀/(6η)` satisfies the first-order left
Perron jet equation `ℓ₁ᵀP_η + ℓ₀ᵀP_η·diag z = ρ₁ℓ₀ᵀ + ℓ₁ᵀ` with
`ρ₁ = z̄`, and is centered. -/
theorem perron_response_first (η : ℝ) (hη : η ≠ 0)
    (z : Fin 6 → ℝ) :
    ((fun i => (z i - (∑ k, z k) / 6) / (6 * η)) ᵥ* perronP η
        + (fun _ => (1 / 6 : ℝ)) ᵥ* (perronP η * Matrix.diagonal z)
      = (((∑ k, z k) / 6) • (fun _ => (1 / 6 : ℝ)) : Fin 6 → ℝ)
        + fun i => (z i - (∑ k, z k) / 6) / (6 * η))
    ∧ (∑ i, (z i - (∑ k, z k) / 6) / (6 * η)) = 0 := by
  have hcent : ∑ k, (z k - (∑ l, z l) / 6) / (6 * η) = 0 := by
    rw [← Finset.sum_div, centered_sum, zero_div]
  refine ⟨?_, hcent⟩
  funext j
  rw [Pi.add_apply, ← Matrix.vecMul_vecMul, Matrix.vecMul_diagonal,
    perronP_vecMul, perronP_vecMul, hcent, Pi.add_apply,
    Pi.smul_apply]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [smul_eq_mul, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat]
  field_simp
  ring

/-- Second order: the `t²`-coefficient of `log ρ` along the tilt
direction `z` equals `((2-η)/(6η))·‖z₀‖²` — the boxed Hessian
`∇²log ρ(0) = ((2-η)/(6η))(I₆-Π₆)`. -/
theorem perron_response_hessian (η : ℝ) (hη : η ≠ 0)
    (z : Fin 6 → ℝ) :
    2 * (((fun i => (z i - (∑ k, z k) / 6) / (6 * η)) ᵥ*
          (perronP η * Matrix.diagonal z)) ⬝ᵥ (fun _ => (1 : ℝ)))
      + (((fun _ => (1 / 6 : ℝ)) ᵥ*
          (perronP η * Matrix.diagonal (fun i => z i ^ 2)))
            ⬝ᵥ (fun _ => (1 : ℝ)))
      - ((∑ k, z k) / 6) ^ 2
    = ((2 - η) / (6 * η))
        * ∑ i, (z i - (∑ k, z k) / 6) ^ 2 := by
  have hcent : ∑ k, (z k - (∑ l, z l) / 6) / (6 * η) = 0 := by
    rw [← Finset.sum_div, centered_sum, zero_div]
  have hdot : ∀ (u w : Fin 6 → ℝ),
      ((u ᵥ* (perronP η * Matrix.diagonal w))
          ⬝ᵥ (fun _ => (1 : ℝ)))
        = (1 - η) * (∑ k, u k * w k)
          + η / 6 * (∑ k, u k) * (∑ k, w k) := by
    intro u w
    simp only [dotProduct, ← Matrix.vecMul_vecMul,
      Matrix.vecMul_diagonal, mul_one]
    rw [Finset.sum_congr rfl (fun k _ => by
      rw [perronP_vecMul η u k])]
    rw [show (∑ k, ((1 - η) * u k + η / 6 * ∑ l, u l) * w k)
        = ∑ k, ((1 - η) * (u k * w k)
            + (η / 6 * ∑ l, u l) * w k) from
      Finset.sum_congr rfl fun k _ => by ring]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hdot, hdot, hcent]
  have h6η : (6 : ℝ) * η ≠ 0 := mul_ne_zero (by norm_num) hη
  have hl1z : ∑ k, (z k - (∑ l, z l) / 6) / (6 * η) * z k
      = (∑ k, (z k - (∑ l, z l) / 6) ^ 2) / (6 * η) := by
    rw [← centered_sq, eq_div_iff h6η, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    field_simp
  have hl0 : ∑ _k : Fin 6, (1 / 6 : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ]
    simp
  have hl0z2 : ∑ k, (1 / 6 : ℝ) * z k ^ 2
      = (∑ k, z k ^ 2) / 6 := by
    rw [← Finset.mul_sum]
    ring
  have hsq : ∑ k, (z k - (∑ l, z l) / 6) ^ 2
      = ∑ k, z k ^ 2 - (∑ k, z k) ^ 2 / 6 := by
    have h1 : ∀ k : Fin 6, (z k - (∑ l, z l) / 6) ^ 2
        = z k ^ 2 - 2 * ((∑ l, z l) / 6) * z k
          + ((∑ l, z l) / 6) ^ 2 := fun k => by ring
    rw [Finset.sum_congr rfl (fun k _ => h1 k)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ]
    simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [hl1z, hl0, hl0z2, hsq]
  field_simp
  ring

end

end NCG
