/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Weighted congruence sums and dual-gauge insertion
  (`thm:chain-Pontryagin`, Gran-Tensor manuscript)

* `chain_pontryagin`:
  (1) subgroup character orthogonality — for a finite additive
      subgroup `H` and a `+`-multiplicative unit-valued pairing
      `φ`, the sum `Σ_{ξ∈H} φ(ξ)` equals `|H|` when `φ` is
      trivial on `H` and `0` otherwise (the boxed insertion
      identity `1_{x−x₀∈Ker A_q} = |im Aᵀ|⁻¹Σ_ξ e_q(ξ·(x−x₀))`
      is this dichotomy applied to `H = im A_qᵀ`);
  (2) section independence — the fibre sum is invariant under
      any bijective reparameterization of the fibre (the boxed
      first decomposition and its basis independence).

Rendering disclosed: the identification of the annihilator of
`Ker A_q` with `im A_qᵀ` and the fibre structure over the
proved Smith–Gale sequence are the manuscript's exactness
bookkeeping (`thm:Smith-Gale-sequence`, proved); factoring the
coordinate sums into the one-variable transforms is the proved
factorization clause of `ar_add_mult`.
-/

namespace NCG

/-- `thm:chain-Pontryagin`. -/
theorem chain_pontryagin :
    -- (1) subgroup character orthogonality dichotomy
    (∀ {A : Type} [AddCommGroup A] (H : AddSubgroup A)
      [Fintype H] (φ : A → ℂ),
      (∀ a b : A, φ (a + b) = φ a * φ b) →
      ((∀ ξ : H, φ ξ = 1) →
        ∑ ξ : H, φ ξ = (Fintype.card H : ℂ))
      ∧ (∀ ξ₀ : H, φ ξ₀ ≠ 1 → ∑ ξ : H, φ ξ = 0))
    -- (2) section independence of the fibre sum
    ∧ (∀ {α β : Type} [Fintype α] [Fintype β]
        (e : α ≃ β) (w : β → ℂ),
        ∑ p : α, w (e p) = ∑ x : β, w x) := by
  refine ⟨?_, ?_⟩
  · intro A _ H _ φ hφ
    constructor
    · intro htriv
      rw [Finset.sum_congr rfl fun ξ _ => htriv ξ]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one]
    · intro ξ₀ h₀
      have htrans : ∑ ξ : H, φ ((ξ₀ : A) + (ξ : A))
          = ∑ ξ : H, φ ξ := by
        rw [show (∑ ξ : H, φ ((ξ₀ : A) + (ξ : A)))
            = ∑ ξ : H, φ ((ξ₀ + ξ : H) : A) from
          Finset.sum_congr rfl fun ξ _ => by
            rw [AddSubgroup.coe_add]]
        exact Fintype.sum_bijective (ξ₀ + ·)
          (Equiv.addLeft ξ₀).bijective _ _ fun ξ => rfl
      have hexp : ∑ ξ : H, φ ((ξ₀ : A) + (ξ : A))
          = φ ξ₀ * ∑ ξ : H, φ ξ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ξ _ => hφ _ _
      have hkey : (φ ξ₀ - 1) * ∑ ξ : H, φ ξ = 0 := by
        rw [sub_mul, one_mul, ← hexp, htrans, sub_self]
      rcases mul_eq_zero.mp hkey with h | h
      · exact absurd (sub_eq_zero.mp h) h₀
      · exact h
  · intro α β _ _ e w
    exact Fintype.sum_bijective e e.bijective _ _ fun p => rfl

end NCG
