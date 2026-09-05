/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite inserted-panel certificate
  (`thm:inserted-panel-certificate`, Gran-Tensor manuscript)

* `conj_panel_zero`: a matrix whose full inserted panel through
  a surjective synthesis vanishes is zero.
* `inserted_panel_certificate`: if the observability syntheses
  are unitarily identified (`U W₁ = W₂`) and the inserted panels
  agree — `W₁ᴴT₁W₁ = W₂ᴴT₂W₂` for a linear transfer and
  `W₁ᴴR₁(g)W₁ = W₂ᴴR₂(φ(g))W₂` for actions related by a map
  `φ` — then the reconstructed unitary intertwines:
  `UT₁ = T₂U` and `UR₁(g) = R₂(φ(g))U`.

Rendering disclosed: the hypotheses of
`thm:flat-monoidal-reconstruction` enter through the unitary
`U` with `UW₁ = W₂` (its reconstructed unitary) and the
source-generation of the realizations through the surjectivity
of the synthesis `W₁`; the group clause is the pointwise
instance of the same panel-cancellation argument, quantified
over the relating isomorphism `φ`.
-/

open Matrix

namespace NCG

/-- A matrix with vanishing full inserted panel through a
surjective synthesis vanishes. -/
lemma conj_panel_zero {h w : Type*} [Fintype h] [Fintype w]
    (W : Matrix h w ℂ) (M : Matrix h h ℂ)
    (hsurj : Function.Surjective W.mulVec)
    (h0 : Wᴴ * M * W = 0) : M = 0 := by
  classical
  have key : ∀ a b : w → ℂ,
      star (W *ᵥ a) ⬝ᵥ (M *ᵥ (W *ᵥ b)) = 0 := by
    intro a b
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      Matrix.vecMul_vecMul, ← Matrix.mul_assoc, h0,
      Matrix.vecMul_zero, zero_dotProduct]
  ext i j
  rw [Matrix.zero_apply]
  obtain ⟨a, ha⟩ := hsurj (Pi.single i 1)
  obtain ⟨b, hb⟩ := hsurj (Pi.single j 1)
  have hval : star (Pi.single i (1 : ℂ) : h → ℂ)
      ⬝ᵥ (M *ᵥ (Pi.single j (1 : ℂ) : h → ℂ)) = M i j := by
    have hstar : star (Pi.single i (1 : ℂ) : h → ℂ)
        = Pi.single i (1 : ℂ) := by
      funext k
      rw [Pi.star_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [hstar]
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        rw [if_neg hk, mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ _) hk
    · intro k _ hk
      rw [if_neg hk, zero_mul]
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  rw [← hval, ← ha, ← hb]
  exact key a b

/-- `thm:inserted-panel-certificate`: agreement of the inserted
transfer and symmetry panels transports to exact intertwining by
the reconstructed unitary. -/
theorem inserted_panel_certificate {h w : Type*} [Fintype h]
    [Fintype w] [DecidableEq h]
    (W1 W2 : Matrix h w ℂ) (U : Matrix h h ℂ)
    (_hUl : Uᴴ * U = 1) (hUr : U * Uᴴ = 1)
    (hW : U * W1 = W2)
    (hsurj : Function.Surjective W1.mulVec) :
    (∀ T1 T2 : Matrix h h ℂ,
      W1ᴴ * T1 * W1 = W2ᴴ * T2 * W2 → U * T1 = T2 * U)
    ∧ (∀ {G1 G2 : Type} (φ : G1 → G2)
        (R1 : G1 → Matrix h h ℂ) (R2 : G2 → Matrix h h ℂ),
        (∀ g, W1ᴴ * R1 g * W1 = W2ᴴ * R2 (φ g) * W2) →
        ∀ g, U * R1 g = R2 (φ g) * U) := by
  have core : ∀ T1 T2 : Matrix h h ℂ,
      W1ᴴ * T1 * W1 = W2ᴴ * T2 * W2 → U * T1 = T2 * U := by
    intro T1 T2 hT
    have hpanel : W1ᴴ * T1 * W1
        = W1ᴴ * (Uᴴ * T2 * U) * W1 := by
      calc W1ᴴ * T1 * W1 = W2ᴴ * T2 * W2 := hT
        _ = W1ᴴ * (Uᴴ * T2 * U) * W1 := by
            rw [← hW, Matrix.conjTranspose_mul]
            simp only [Matrix.mul_assoc]
    have hM : W1ᴴ * (T1 - Uᴴ * T2 * U) * W1 = 0 := by
      have hsub := sub_eq_zero.mpr hpanel
      calc W1ᴴ * (T1 - Uᴴ * T2 * U) * W1
          = W1ᴴ * T1 * W1 - W1ᴴ * (Uᴴ * T2 * U) * W1 := by
            rw [Matrix.mul_sub, Matrix.sub_mul]
        _ = 0 := hsub
    have hTeq : T1 = Uᴴ * T2 * U :=
      sub_eq_zero.mp (conj_panel_zero W1 _ hsurj hM)
    rw [hTeq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUr,
      Matrix.one_mul]
  refine ⟨core, ?_⟩
  intro G1 G2 φ R1 R2 hR g
  exact core (R1 g) (R2 (φ g)) (hR g)

end NCG
