/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Derived common-source freshness diamond
  (`cor:derived-fresh-diamond-master`, flagship manuscript)

Two regenerated external legs conditioned on the complete source
label `z` have the boxed diamond kernel
`K_◇((z,a,b),(z',a',b')) = P(z,z')·R_{z'}(a')·R_{z'}(b')`
(`diamondKernel`, the composition of the source transition with
the two identical fresh Read laws — the independence supplied by
the proved complete-cut factorization, disclosed).  We prove:

* the product law `π(z)R_z(a)R_z(b)` is stationary for the
  diamond kernel (`diamond_stationary`);
* the stationary law is exchange invariant
  (`diamond_exchange_invariant`);
* every exchange-odd observable has zero stationary mean
  (`diamond_odd_mean_zero`, by the `(a,b) ↦ (b,a)` pairing).

The corollary's own firewall — no metric-compatibility or torsion
conclusion — is prose.
-/

open Finset

namespace NCG

variable {Z A : Type*} [Fintype Z] [Fintype A]

/-- The boxed diamond kernel: source transition times two
identical fresh Read laws. -/
def diamondKernel (P : Z → Z → ℝ) (R : Z → A → ℝ) :
    Z × A × A → Z × A × A → ℝ :=
  fun w w' => P w.1 w'.1 * R w'.1 w'.2.1 * R w'.1 w'.2.2

/-- The stationary product law `π(z)R_z(a)R_z(b)`. -/
def diamondLaw (π : Z → ℝ) (R : Z → A → ℝ) : Z × A × A → ℝ :=
  fun w => π w.1 * R w.1 w.2.1 * R w.1 w.2.2

/-- The product law is stationary for the diamond kernel. -/
theorem diamond_stationary (P : Z → Z → ℝ) (R : Z → A → ℝ)
    (π : Z → ℝ) (hπ : ∀ z', ∑ z, π z * P z z' = π z')
    (hR : ∀ z, ∑ a, R z a = 1) (w' : Z × A × A) :
    ∑ w : Z × A × A,
        diamondLaw π R w * diamondKernel P R w w'
      = diamondLaw π R w' := by
  obtain ⟨z', a', b'⟩ := w'
  calc ∑ w : Z × A × A, diamondLaw π R w
        * diamondKernel P R w (z', a', b')
      = ∑ z, ∑ a, ∑ b, π z * R z a * R z b
          * (P z z' * R z' a' * R z' b') := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [diamondLaw, diamondKernel]
    _ = ∑ z, π z * P z z' * ((∑ a, R z a) * (∑ b, R z b))
          * (R z' a' * R z' b') := by
        refine Finset.sum_congr rfl fun z _ => ?_
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
    _ = (∑ z, π z * P z z') * (R z' a' * R z' b') := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun z _ => ?_
        simp only [hR]
        ring
    _ = diamondLaw π R (z', a', b') := by
        rw [hπ z']
        simp only [diamondLaw]
        ring

omit [Fintype Z] [Fintype A] in
/-- The stationary law is exchange invariant. -/
theorem diamond_exchange_invariant (π : Z → ℝ) (R : Z → A → ℝ)
    (z : Z) (a b : A) :
    diamondLaw π R (z, a, b) = diamondLaw π R (z, b, a) := by
  simp only [diamondLaw]
  ring

/-- Every bounded exchange-odd observable has zero stationary
mean. -/
theorem diamond_odd_mean_zero (π : Z → ℝ) (R : Z → A → ℝ)
    (f : Z × A × A → ℝ)
    (hodd : ∀ z a b, f (z, a, b) = -f (z, b, a)) :
    ∑ w : Z × A × A, diamondLaw π R w * f w = 0 := by
  have hswap : ∑ w : Z × A × A, diamondLaw π R w * f w
      = ∑ w : Z × A × A, diamondLaw π R w * -f w := by
    rw [← (Equiv.prodCongr (Equiv.refl Z)
      (Equiv.prodComm A A)).sum_comp
      (fun w => diamondLaw π R w * f w)]
    refine Finset.sum_congr rfl fun ⟨z, a, b⟩ _ => ?_
    have h1 : (Equiv.prodCongr (Equiv.refl Z)
        (Equiv.prodComm A A)) (z, a, b) = (z, b, a) := rfl
    rw [h1, diamond_exchange_invariant π R z b a, hodd z b a]
  have h2 : ∑ w : Z × A × A, diamondLaw π R w * f w
      = -∑ w : Z × A × A, diamondLaw π R w * f w := by
    rw [← Finset.sum_neg_distrib]
    simpa [mul_neg] using hswap
  linarith

end NCG
