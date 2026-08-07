/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The endpoint record bimodule
  (`thm:SM-record-bimodule`, Gran-Tensor manuscript)

* `sm_record_bimodule`: on the canonical link-mode space
  `HS(M_R, M_L)`, the boxed representation
  `π(a ⊗ b^op)F = aFb` of the endpoint record algebra
  `𝔯_L ⊗ 𝔯_R^op` obeys the opposite-order composition law
  `π(a₁,b₁)∘π(a₂,b₂) = π(a₁a₂, b₂b₁)`, is unital, and is
  faithful on simple tensors (if `aFb = 0` for every link mode
  `F`, then `a = 0` or `b = 0`).

Rendering disclosed: the unique factorization `Y_e = D_e ⊗ F_e`
of a carrier-equivariant edge is the proved
`multiplicity_factorization`; the flat-depth reconstruction of
the carrier line and multiplicity spaces is the manuscript's
central/commutant bookkeeping.
-/

open Matrix

namespace NCG

/-- `thm:SM-record-bimodule`: composition law, unitality, and
faithfulness of the endpoint record representation. -/
theorem sm_record_bimodule {L R : Type*} [Fintype L]
    [Fintype R] [DecidableEq L] [DecidableEq R] :
    (∀ (a₁ a₂ : Matrix L L ℂ) (b₁ b₂ : Matrix R R ℂ)
        (F : Matrix L R ℂ),
      a₁ * (a₂ * F * b₂) * b₁ = (a₁ * a₂) * F * (b₂ * b₁))
    ∧ (∀ F : Matrix L R ℂ,
        (1 : Matrix L L ℂ) * F * (1 : Matrix R R ℂ) = F)
    ∧ (∀ (a : Matrix L L ℂ) (b : Matrix R R ℂ),
        (∀ F : Matrix L R ℂ, a * F * b = 0) →
        a = 0 ∨ b = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a₁ a₂ b₁ b₂ F
    simp only [Matrix.mul_assoc]
  · intro F
    rw [Matrix.one_mul, Matrix.mul_one]
  · intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    · refine Or.inr ?_
      have hex : ∃ i k, a i k ≠ 0 := by
        by_contra hall
        apply ha
        ext i k
        rw [Matrix.zero_apply]
        by_contra hik
        exact hall ⟨i, k, hik⟩
      obtain ⟨i, k, hik⟩ := hex
      ext l j
      rw [Matrix.zero_apply]
      have h := congrFun (congrFun
        (hab (Matrix.single k l 1)) i) j
      rw [Matrix.zero_apply] at h
      have hent : (a * Matrix.single k l (1 : ℂ) * b) i j
          = a i k * b l j := by
        rw [Matrix.mul_apply]
        rw [Finset.sum_eq_single l
          (fun m _ hm => by
            rw [show (a * Matrix.single k l (1 : ℂ)) i m = 0
                from by
              rw [Matrix.mul_apply]
              refine Finset.sum_eq_zero fun p _ => ?_
              rw [Matrix.single_apply,
                if_neg (fun hand => hm hand.2.symm),
                mul_zero],
              zero_mul])
          (fun habs => absurd (Finset.mem_univ _) habs)]
        rw [show (a * Matrix.single k l (1 : ℂ)) i l
            = a i k from by
          rw [Matrix.mul_apply]
          rw [Finset.sum_eq_single k
            (fun p _ hp => by
              rw [Matrix.single_apply,
                if_neg (fun hand => hp hand.1.symm),
                mul_zero])
            (fun habs => absurd (Finset.mem_univ _) habs)]
          rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩, mul_one]]
      rw [hent] at h
      rcases mul_eq_zero.mp h with h1 | h2
      · exact absurd h1 hik
      · exact h2

end NCG
