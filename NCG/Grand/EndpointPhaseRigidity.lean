/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# endpoint phase rigidity
-/

open scoped ArithmeticFunction.Moebius ArithmeticFunction

namespace NCG

private theorem cardFactors_finset_prod
    {r : Type*} [Fintype r] [DecidableEq r]
    (x : r → ℕ) (hx0 : ∀ j, x j ≠ 0) :
    ArithmeticFunction.cardFactors (∏ j, x j)
      = ∑ j, ArithmeticFunction.cardFactors (x j) := by
  classical
  let s : Finset r := Finset.univ
  change ArithmeticFunction.cardFactors (∏ j ∈ s, x j)
      = ∑ j ∈ s, ArithmeticFunction.cardFactors (x j)
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        ArithmeticFunction.cardFactors_mul (hx0 a)]
      · rw [ih]
      · exact Finset.prod_ne_zero_iff.mpr fun j _ => hx0 j

/-- The boxed Liouville-phase identity in
`thm:ar-phase-rigidity`.  Repeated primes in different slots are
correctly counted by the completely additive `cardFactors = Ω`. -/
theorem endpoint_moebius_phase
    {r : Type*} [Fintype r] [DecidableEq r]
    (x : r → ℕ) (hsq : ∀ j, Squarefree (x j))
    (hx0 : ∀ j, x j ≠ 0) :
    ∏ j, ArithmeticFunction.moebius (x j)
      = (-1 : ℤ) ^ ArithmeticFunction.cardFactors (∏ j, x j) := by
  calc
    ∏ j, ArithmeticFunction.moebius (x j)
        = ∏ j, (-1 : ℤ) ^ ArithmeticFunction.cardFactors (x j) := by
            apply Finset.prod_congr rfl
            intro j _
            exact ArithmeticFunction.moebius_apply_of_squarefree (hsq j)
    _ = (-1 : ℤ) ^ ∑ j, ArithmeticFunction.cardFactors (x j) := by
          exact Finset.prod_pow_eq_pow_sum Finset.univ
            (fun j => ArithmeticFunction.cardFactors (x j)) (-1)
    _ = (-1 : ℤ) ^ ArithmeticFunction.cardFactors (∏ j, x j) := by
          rw [cardFactors_finset_prod x hx0]

/-- Full endpoint-fibre phase statement: every ordered squarefree
slot allocation with endpoint `u` has the same Möbius--character
phase, and arbitrary amplitudes therefore add coherently. -/
theorem endpoint_phase_rigidity_exact
    {r H : Type*} [Fintype r] [DecidableEq r]
    [Fintype H] [DecidableEq H]
    (slots : H → r → ℕ) (u : ℕ)
    (hsq : ∀ h j, Squarefree (slots h j))
    (hpos : ∀ h j, slots h j ≠ 0)
    (hend : ∀ h, ∏ j, slots h j = u)
    (χ : ℕ →* ℂ) (a : H → ℂ) :
    (∀ h, (((∏ j, ArithmeticFunction.moebius (slots h j) : ℤ) : ℂ)
        * χ u)
      = ((((-1 : ℤ) ^ ArithmeticFunction.cardFactors u : ℤ) : ℂ)
          * χ u))
    ∧ (∑ h, a h *
        ((((∏ j, ArithmeticFunction.moebius (slots h j) : ℤ) : ℂ)
          * χ u))
      = (∑ h, a h) *
        ((((-1 : ℤ) ^ ArithmeticFunction.cardFactors u : ℤ) : ℂ)
          * χ u)) := by
  have hphase : ∀ h,
      (((∏ j, ArithmeticFunction.moebius (slots h j) : ℤ) : ℂ) * χ u)
        = ((((-1 : ℤ) ^ ArithmeticFunction.cardFactors u : ℤ) : ℂ)
          * χ u) := by
    intro h
    have hm := endpoint_moebius_phase (slots h) (hsq h) (hpos h)
    rw [hend h] at hm
    rw [hm]
  refine ⟨hphase, ?_⟩
  simp_rw [hphase]
  rw [Finset.sum_mul]

end NCG
