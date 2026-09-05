/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# two missing countertheorems
-/

open Matrix

namespace NCG

/-! ## Unsigned provenance does not determine the short -/

def unsignedProvP1 : Matrix (Fin 2) (Fin 1) ℂ :=
  Matrix.vecMulVec ![1, 0] ![1]

def unsignedProvP2 : Matrix (Fin 2) (Fin 1) ℂ :=
  Matrix.vecMulVec ![0, 1] ![1]

def unsignedProvF : Matrix (Fin 2) (Fin 1) ℂ := unsignedProvP1

/-- `cth:unsigned-provenance-no-short`: two provenance
syntheses have the same marginal Gram but produce different
provenance-aware connected Grams. -/
theorem unsigned_provenance_no_short :
    unsignedProvP1ᴴ * unsignedProvP1 =
      unsignedProvP2ᴴ * unsignedProvP2
    ∧ unsignedProvP1ᴴ * unsignedProvP1 = 1
    ∧ unsignedProvFᴴ * (1 - unsignedProvP1 * unsignedProvP1ᴴ)
        * unsignedProvF = 0
    ∧ unsignedProvFᴴ * (1 - unsignedProvP2 * unsignedProvP2ᴴ)
        * unsignedProvF = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [unsignedProvP1, unsignedProvP2, unsignedProvF,
      Matrix.mul_apply, Matrix.vecMulVec, Fin.sum_univ_two]

/-! ## Accepted bit does not determine a field kernel -/

/-- Reset every input row to the same terminal law. -/
def fullResetKernel {d : Type*} (ρ : d → ℝ) : Matrix d d ℝ :=
  fun _ j => ρ j

theorem fullResetKernel_idempotent {d : Type*} [Fintype d]
    (ρ : d → ℝ) (hρ : ∑ j, ρ j = 1) :
    fullResetKernel ρ * fullResetKernel ρ = fullResetKernel ρ := by
  ext i j
  simp only [Matrix.mul_apply, fullResetKernel]
  rw [show (∑ x, ρ x * ρ j) = (∑ x, ρ x) * ρ j by
    rw [Finset.sum_mul]]
  rw [hρ, one_mul]

/-- A concrete full-support reset law. -/
noncomputable def acceptedResetLaw : Fin 2 → ℝ := ![1/2, 1/2]

/-- `cth:accepted-bit-no-field-kernel`: identity and reset are
distinct idempotent stochastic kernels and therefore can be
placed behind the same state-independent accepted mark while
having different terminal field actions. -/
theorem accepted_bit_no_field_kernel :
    let K₀ : Matrix (Fin 2) (Fin 2) ℝ := 1
    let K₁ := fullResetKernel acceptedResetLaw
    K₀ * K₀ = K₀
      ∧ K₁ * K₁ = K₁
      ∧ (∀ i, ∑ j, K₀ i j = 1)
      ∧ (∀ i, ∑ j, K₁ i j = 1)
      ∧ (∀ j, 0 < acceptedResetLaw j)
      ∧ K₀ ≠ K₁
      ∧ K₀ *ᵥ ![1, 0] ≠ K₁ *ᵥ ![1, 0] := by
  dsimp
  refine ⟨Matrix.one_mul (1 : Matrix (Fin 2) (Fin 2) ℝ),
    fullResetKernel_idempotent _ ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [acceptedResetLaw, Fin.sum_univ_two]
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_two, Matrix.one_apply]
  · intro i
    fin_cases i <;> norm_num [fullResetKernel, acceptedResetLaw,
      Fin.sum_univ_two]
  · intro j
    fin_cases j <;> norm_num [acceptedResetLaw]
  · intro h
    have hentry := congrFun (congrFun h 0) 0
    norm_num [fullResetKernel, acceptedResetLaw] at hentry
  · intro h
    have hentry := congrFun h 0
    norm_num [fullResetKernel, acceptedResetLaw, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] at hentry

end NCG
