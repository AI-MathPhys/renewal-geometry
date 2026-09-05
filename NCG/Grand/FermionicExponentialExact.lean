/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Powers of sums of commuting square-zero elements

The engine behind the fermionic exponential: for pairwise-commuting square-zero elements
`x i` of a (noncommutative) ring — such as the Grassmann bilinear pairs `ψ̄ᵢ ∧ χᵢ` —

`(∑ i ∈ s, x i) ^ p = p! • ∑_{T ⊆ s, |T| = p} ∏_{i ∈ T} x i`  (`sum_pow_eq`),

so the power series of `exp(∑ x i)` truncates: powers beyond `|s|` vanish
(`sum_pow_eq_zero_of_card_lt`) and the top power saturates to the factorial times the full
product (`sum_pow_card`).  This is the exact statement that a fermionic Gaussian exponential
contributes precisely its top Grassmann monomial with unit normalization.
-/

namespace NCG
namespace Fermionic

variable {A : Type*} [Ring A] {ι : Type*}

/-- Squares-zero propagates to all higher powers. -/
theorem pow_eq_zero_of_sq {x : A} (hx : x * x = 0) {m : ℕ} (hm : 2 ≤ m) : x ^ m = 0 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add, pow_two, hx, zero_mul]

/-- **Sum-power expansion for commuting square-zero elements**:
`(∑ i ∈ s, x i)^p = p! • ∑_{T ∈ powersetCard p s} ∏_{i ∈ T} x i`. -/
theorem sum_pow_eq (x : ι → A) (hcomm : ∀ i j, Commute (x i) (x j))
    (hsq : ∀ i, x i * x i = 0) (s : Finset ι) :
    ∀ p : ℕ, (∑ i ∈ s, x i) ^ p
      = p.factorial • ∑ T ∈ s.powersetCard p,
          T.noncommProd x fun a _ b _ _ => hcomm a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro p
    rcases p with _ | q
    · rw [pow_zero, Finset.powersetCard_zero, Finset.sum_singleton,
        Nat.factorial_zero, one_smul]
      exact (Finset.noncommProd_empty _ _).symm
    · rw [Finset.sum_empty, zero_pow (Nat.succ_ne_zero q),
        Finset.powersetCard_eq_empty.mpr (by simp), Finset.sum_empty, smul_zero]
  | insert a s ha IH =>
    intro p
    have hS : Commute (x a) (∑ i ∈ s, x i) :=
      Commute.sum_right _ _ _ fun i _ => hcomm a i
    rw [Finset.sum_insert ha]
    rcases p with _ | q
    · rw [pow_zero, Finset.powersetCard_zero, Finset.sum_singleton,
        Nat.factorial_zero, one_smul]
      exact (Finset.noncommProd_empty _ _).symm
    -- binomial for the commuting pair, with all powers ≥ 2 of `x a` vanishing
    rw [hS.add_pow (q + 1)]
    have hzero : ∀ m ∈ Finset.range q,
        x a ^ (m + 2) * (∑ i ∈ s, x i) ^ (q + 1 - (m + 2)) * ((q + 1).choose (m + 2) : A)
          = 0 := by
      intro m _
      rw [pow_eq_zero_of_sq (hsq a) (by omega), zero_mul, zero_mul]
    have hsplit : (∑ m ∈ Finset.range (q + 2),
        x a ^ m * (∑ i ∈ s, x i) ^ (q + 1 - m) * ((q + 1).choose m : A))
        = (∑ i ∈ s, x i) ^ (q + 1)
          + (q + 1) • (x a * (∑ i ∈ s, x i) ^ q) := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      rw [Finset.sum_eq_zero fun m hm => hzero m hm]
      simp only [zero_add, pow_zero, pow_one, one_mul, Nat.sub_zero,
        Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.choose_one_right]
      rw [show q + 1 - 1 = q from rfl, add_comm]
      congr 1
      rw [nsmul_eq_mul, ← (Nat.cast_commute (q + 1) _).eq]
    rw [hsplit, IH (q + 1), IH q]
    -- assemble the right-hand side over `powersetCard (q+1) (insert a s)`
    rw [Finset.powersetCard_succ_insert ha, Finset.sum_union, Finset.sum_image]
    · have hins : ∀ T ∈ s.powersetCard q,
          Finset.noncommProd (insert a T) x
              (fun c _ d _ _ => hcomm c d)
            = x a * T.noncommProd x fun c _ d _ _ => hcomm c d := by
        intro T hT
        have haT : a ∉ T := fun haT =>
          ha ((Finset.mem_powersetCard.mp hT).1 haT)
        exact Finset.noncommProd_insert_of_notMem T a x _ haT
      rw [Finset.sum_congr rfl hins, smul_add]
      congr 1
      rw [mul_smul_comm, smul_smul, ← Nat.factorial_succ, Finset.mul_sum]
    · intro T₁ h₁ T₂ h₂ he
      have h₁' : a ∉ T₁ := fun hmem => ha ((Finset.mem_powersetCard.mp h₁).1 hmem)
      have h₂' : a ∉ T₂ := fun hmem => ha ((Finset.mem_powersetCard.mp h₂).1 hmem)
      have := congrArg (fun U => U.erase a) he
      simpa [Finset.erase_insert h₁', Finset.erase_insert h₂'] using this
    · rw [Finset.disjoint_right]
      rintro T hT hT'
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hT
      exact ha ((Finset.mem_powersetCard.mp hT').1 (Finset.mem_insert_self a U))

/-- **Nilpotence**: powers beyond the number of terms vanish — the fermionic exponential is
a polynomial. -/
theorem sum_pow_eq_zero_of_card_lt (x : ι → A) (hcomm : ∀ i j, Commute (x i) (x j))
    (hsq : ∀ i, x i * x i = 0) (s : Finset ι) {p : ℕ} (hp : s.card < p) :
    (∑ i ∈ s, x i) ^ p = 0 := by
  classical
  rw [sum_pow_eq x hcomm hsq s p, Finset.powersetCard_eq_empty.mpr hp,
    Finset.sum_empty, smul_zero]

/-- **Factorial saturation**: the top power is `|s|!` times the full ordered product — the
fermionic exponential contributes exactly its top Grassmann monomial with the inverse
factorial normalization. -/
theorem sum_pow_card (x : ι → A) (hcomm : ∀ i j, Commute (x i) (x j))
    (hsq : ∀ i, x i * x i = 0) (s : Finset ι) :
    (∑ i ∈ s, x i) ^ s.card
      = s.card.factorial • s.noncommProd x fun a _ b _ _ => hcomm a b := by
  classical
  rw [sum_pow_eq x hcomm hsq s s.card, Finset.powersetCard_self, Finset.sum_singleton]

end Fermionic
end NCG
