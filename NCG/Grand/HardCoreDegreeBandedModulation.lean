/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.InterchangeActualAudit
import Mathlib.Data.Finset.Card

/-!
# Degree-banded Walsh modulation

The one-site factor in the explicit modulated interchange generator is split
into its constant and centered Boolean parts.  Multiplication by the centered
part toggles exactly one Walsh support, hence changes Walsh degree by at most
one.
-/

namespace NCG.HardCoreWalsh

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Toggle one Walsh generator in a finite support. -/
def toggle (x : V) (A : Finset V) : Finset V :=
  if x ∈ A then A.erase x else insert x A

theorem toggle_card_band (x : V) (A : Finset V) :
    (toggle x A).card ≤ A.card + 1 ∧
      A.card ≤ (toggle x A).card + 1 := by
  by_cases hx : x ∈ A
  · have hcard := Finset.card_erase_add_one hx
    simp [toggle, hx]
    omega
  · rw [toggle, if_neg hx, Finset.card_insert_of_notMem hx]
    omega

theorem toggle_card_exact (x : V) (A : Finset V) :
    ((toggle x A).card = A.card + 1) ∨
      ((toggle x A).card + 1 = A.card) := by
  by_cases hx : x ∈ A
  · right
    simpa [toggle, hx] using Finset.card_erase_add_one hx
  · left
    simp [toggle, hx]

/-- A matrix block supported on one-site Walsh multiplication. -/
def OneSiteDegreeBlock (x : V) (weight : Finset V → ℝ) :
    Matrix (Finset V) (Finset V) ℝ :=
  fun B A => if B = toggle x A then weight A else 0

theorem oneSiteDegreeBlock_degree_banded
    (x : V) (weight : Finset V → ℝ) {B A : Finset V}
    (hBA : OneSiteDegreeBlock x weight B A ≠ 0) :
    B.card ≤ A.card + 1 ∧ A.card ≤ B.card + 1 := by
  have hEq : B = toggle x A := by
    by_contra h
    simp [OneSiteDegreeBlock, h] at hBA
  subst B
  exact toggle_card_band x A

/-- Even coefficient of a real Boolean one-site modulation. -/
noncomputable def booleanEven (φ : Bool → ℝ) : ℝ :=
  (φ true + φ false) / 2

/-- Centered Walsh coefficient of a real Boolean one-site modulation. -/
noncomputable def booleanOdd (φ : Bool → ℝ) : ℝ :=
  (φ true - φ false) / 2

/-- The normalized one-site Boolean Walsh character. -/
def booleanWalsh (b : Bool) : ℝ := if b then 1 else -1

theorem boolean_walsh_decomposition (φ : Bool → ℝ) (b : Bool) :
    φ b = booleanEven φ + booleanOdd φ * booleanWalsh b := by
  cases b <;> simp [booleanEven, booleanOdd, booleanWalsh] <;> ring

/-- Consequently the manuscript modulation factor is a diagonal Walsh block
plus a single toggle block; no coefficient can connect degrees farther than
one. -/
theorem modulation_factor_even_odd
    (θ : ℝ) (φ : Bool → ℝ) (b : Bool) :
    1 + θ * φ b =
      (1 + θ * booleanEven φ) +
        (θ * booleanOdd φ) * booleanWalsh b := by
  rw [boolean_walsh_decomposition φ b]
  ring

/-- Walsh monomial carried by a finite support. -/
def walshMonomial (A : Finset V) (η : V → Bool) : ℝ :=
  ∏ x ∈ A, booleanWalsh (η x)

@[simp] theorem booleanWalsh_sq (b : Bool) :
    booleanWalsh b * booleanWalsh b = 1 := by
  cases b <;> norm_num [booleanWalsh]

/-- Multiplication by one centered Boolean coordinate toggles that coordinate
in the Walsh support. -/
theorem booleanWalsh_mul_walshMonomial
    (x : V) (A : Finset V) (η : V → Bool) :
    booleanWalsh (η x) * walshMonomial A η =
      walshMonomial (toggle x A) η := by
  by_cases hx : x ∈ A
  · rw [toggle, if_pos hx]
    simp only [walshMonomial]
    rw [← Finset.mul_prod_erase A (fun y => booleanWalsh (η y)) hx]
    rw [← mul_assoc, booleanWalsh_sq, one_mul]
  · rw [toggle, if_neg hx]
    simp [walshMonomial, Finset.prod_insert, hx]

/-- Exact Walsh action of the explicit one-site modulation factor: a diagonal
coefficient plus one degree-toggle coefficient. -/
theorem modulation_factor_mul_walshMonomial
    (θ : ℝ) (φ : Bool → ℝ) (x : V)
    (A : Finset V) (η : V → Bool) :
    (1 + θ * φ (η x)) * walshMonomial A η =
      (1 + θ * booleanEven φ) * walshMonomial A η +
        (θ * booleanOdd φ) * walshMonomial (toggle x A) η := by
  rw [modulation_factor_even_odd]
  rw [add_mul, mul_assoc, booleanWalsh_mul_walshMonomial]

end NCG.HardCoreWalsh

