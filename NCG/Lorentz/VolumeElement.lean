/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Dimension.GradedGram

/-!
# The oriented volume element

**Proposition `prop:renewal-volume-element`**: the Clifford volume
element `Vol = Γ(e₁)⋯Γ(e_d)` of the marked endpoint satisfies

* the **square identity** `Vol² = (−1)^{d(d−1)/2}·1`
  (`NCG.volume_element_sq`), by the generator-exchange calculus of
  `NCG/Dimension/GradedGram.lean`;
* the temporal generator **anticommutes** with `Vol` for odd `d`
  (`NCG.temporal_anticomm_volume` via `NCG.gen0_mul_prod`), so `Vol` is
  not central in the full spacetime Clifford algebra and need not act
  as one scalar on the full spinor module.

The `SO`-basis-independence and the spatial centrality claims rest on
the determinant/top-exterior-power argument and are not formalised. -/

namespace NCG

variable {A : Type*} [Ring A] {ι : Type*} [DecidableEq ι]

/-- **Proposition `prop:renewal-volume-element`, square identity**: a
product of `n` distinct anticommuting square-one generators satisfies
`(γ₁⋯γₙ)² = (−1)^{n(n−1)/2}·1`. -/
theorem volume_element_sq (γ : ι → A)
    (hanti : ∀ i j, i ≠ j → γ i * γ j = -(γ j * γ i))
    (hsq : ∀ i, γ i * γ i = 1) :
    ∀ (l : List ι), l.Nodup →
      (l.map γ).prod * (l.map γ).prod
        = ((-1 : ℤ) ^ (l.length * (l.length - 1) / 2)) • (1 : A)
  | [], _ => by simp
  | j :: l, hnodup => by
      have hj : j ∉ l := (List.nodup_cons.mp hnodup).1
      have hl : l.Nodup := (List.nodup_cons.mp hnodup).2
      have ih := volume_element_sq γ hanti hsq l hl
      have hmove := gen_mul_prod γ hanti j l hj
      have hmove' : (l.map γ).prod * γ j
          = ((-1 : ℤ) ^ l.length) • (γ j * (l.map γ).prod) := by
        rw [hmove, smul_smul, ← pow_add,
          Even.neg_one_pow ⟨l.length, rfl⟩, one_smul]
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      calc γ j * (l.map γ).prod * (γ j * (l.map γ).prod)
          = γ j * (((l.map γ).prod * γ j) * (l.map γ).prod) := by
            rw [mul_assoc, ← mul_assoc ((l.map γ).prod) (γ j)]
        _ = γ j * ((((-1 : ℤ) ^ l.length)
              • (γ j * (l.map γ).prod)) * (l.map γ).prod) := by
            rw [hmove']
        _ = ((-1 : ℤ) ^ l.length)
              • (γ j * (γ j * ((l.map γ).prod * (l.map γ).prod))) := by
            rw [smul_mul_assoc, mul_smul_comm]
            congr 1
            rw [mul_assoc]
        _ = ((-1 : ℤ) ^ l.length)
              • (((-1 : ℤ) ^ (l.length * (l.length - 1) / 2))
                • (1 : A)) := by
            rw [← mul_assoc, hsq, one_mul, ih]
        _ = ((-1 : ℤ) ^ ((l.length + 1) * (l.length + 1 - 1) / 2))
              • (1 : A) := by
            rw [smul_smul, ← pow_add]
            congr 2
            have hexp : (l.length + 1) * (l.length + 1 - 1)
                = l.length * (l.length - 1) + l.length * 2 := by
              cases l.length with
              | zero => rfl
              | succ m =>
                  show (m + 2) * (m + 1) = (m + 1) * m + (m + 1) * 2
                  ring
            rw [hexp, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]
            omega

/-- Moving an element that anticommutes with **all** members of a family
through their product costs `(−1)^{length}` — the temporal-move lemma
(no distinctness needed). -/
theorem gen0_mul_prod (γ : ι → A) (γ0 : A)
    (hanti0 : ∀ i, γ0 * γ i = -(γ i * γ0)) :
    ∀ l : List ι,
      γ0 * (l.map γ).prod
        = ((-1 : ℤ) ^ l.length) • ((l.map γ).prod * γ0)
  | [] => by simp
  | i :: l => by
      have ih := gen0_mul_prod γ γ0 hanti0 l
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      calc γ0 * (γ i * (l.map γ).prod)
          = (γ0 * γ i) * (l.map γ).prod := by rw [mul_assoc]
        _ = -(γ i * (γ0 * (l.map γ).prod)) := by
            rw [hanti0 i, neg_mul, mul_assoc]
        _ = -(γ i * (((-1 : ℤ) ^ l.length)
              • ((l.map γ).prod * γ0))) := by rw [ih]
        _ = (-((-1 : ℤ) ^ l.length))
              • (γ i * ((l.map γ).prod * γ0)) := by
            rw [mul_smul_comm, neg_smul]
        _ = ((-1 : ℤ) ^ (l.length + 1))
              • ((γ i * (l.map γ).prod) * γ0) := by
            rw [mul_assoc]
            congr 1
            rw [pow_succ]
            ring

/-- **Proposition `prop:renewal-volume-element`, odd rank**: the
temporal generator anticommutes with the volume element, so `Vol` is not
central in the full spacetime Clifford algebra. -/
theorem temporal_anticomm_volume (γ : ι → A) (γ0 : A)
    (hanti0 : ∀ i, γ0 * γ i = -(γ i * γ0)) (l : List ι)
    (hodd : Odd l.length) :
    γ0 * (l.map γ).prod = -((l.map γ).prod * γ0) := by
  rw [gen0_mul_prod γ γ0 hanti0 l, Odd.neg_one_pow hodd]
  rw [neg_smul, one_smul]

end NCG
