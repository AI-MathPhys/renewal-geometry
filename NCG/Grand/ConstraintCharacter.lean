/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite constraint–character partition duality
  (`thm:constraint-character`, Gran-Tensor manuscript)

* `constraint_character`: the boxed duality
  `Z_A(b; w) = |G|⁻ᵐ ∑_η η(-b) ∏ⱼ ŵⱼ((A^∨η)ⱼ)` —
  the constrained partition sum over `Ax = b` with arbitrary
  slot weights equals the character-dual sum, where
  `(A^∨η)ⱼ(g) = η(A(gδⱼ))` is the pulled-back character and
  `ŵⱼ(χ) = ∑_g wⱼ(g)χ(g)` the weight transform.
* `dual_sum_indicator` / `dual_card`: finite abelian character
  orthogonality — the full dual sum at `h` is `|H|·[h = 1]` and
  the dual has the same cardinality as the group (via Mathlib's
  roots-of-unity duality for `ℂ`).

Rendering disclosed: the finite abelian constraint group is
written multiplicatively (`CommGroup`), the constraint `A` is an
arbitrary homomorphism `Gⁿ → Gᵐ` (subsuming the manuscript's
integer matrix action), and `η(-b)` is `η(b⁻¹)`.
-/

namespace NCG

/-- The character dual of a finite commutative group into `ℂˣ`
is finite. -/
noncomputable instance dualFintype (H : Type*) [CommGroup H]
    [Finite H] : Fintype (H →* ℂˣ) := by
  have h := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity H ℂ
  haveI : Nonempty (H →* ℂˣ) := ⟨1⟩
  have hpos : 0 < Nat.card (H →* ℂˣ) := by
    rw [h]
    exact Nat.card_pos
  haveI : Finite (H →* ℂˣ) := (Nat.card_pos_iff.mp hpos).2
  exact Fintype.ofFinite _

/-- The character dual of a finite commutative group has the
same cardinality as the group. -/
lemma dual_card (H : Type*) [CommGroup H] [Finite H] :
    Nat.card (H →* ℂˣ) = Nat.card H :=
  CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity H ℂ

/-- Character orthogonality, vanishing half: the full dual sum
at `h ≠ 1` vanishes. -/
lemma dual_sum_eq_zero {H : Type*} [CommGroup H] [Finite H]
    {h : H} (hne : h ≠ 1) :
    ∑ η : H →* ℂˣ, ((η h : ℂˣ) : ℂ) = 0 := by
  obtain ⟨φ, hφ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity H ℂ hne
  have hre : ∑ η : H →* ℂˣ, (((φ * η) h : ℂˣ) : ℂ)
      = ∑ η : H →* ℂˣ, ((η h : ℂˣ) : ℂ) :=
    Fintype.sum_bijective (fun η => φ * η)
      (Group.mulLeft_bijective φ) _ _ (fun η => rfl)
  have hfac : ∑ η : H →* ℂˣ, (((φ * η) h : ℂˣ) : ℂ)
      = ((φ h : ℂˣ) : ℂ)
        * ∑ η : H →* ℂˣ, ((η h : ℂˣ) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [MonoidHom.mul_apply, Units.val_mul]
  have hkey : (((φ h : ℂˣ) : ℂ) - 1)
      * ∑ η : H →* ℂˣ, ((η h : ℂˣ) : ℂ) = 0 := by
    rw [sub_mul, one_mul, ← hfac, hre, sub_self]
  rcases mul_eq_zero.mp hkey with h0 | h0
  · exfalso
    apply hφ
    apply Units.ext
    rw [Units.val_one]
    exact sub_eq_zero.mp h0
  · exact h0

/-- Character orthogonality: the full dual sum at `h` is
`|H| · [h = 1]`. -/
lemma dual_sum_indicator {H : Type*} [CommGroup H] [Finite H]
    (h : H) [Decidable (h = 1)] :
    ∑ η : H →* ℂˣ, ((η h : ℂˣ) : ℂ)
      = if h = 1 then (Nat.card H : ℂ) else 0 := by
  by_cases hh : h = 1
  · subst hh
    rw [if_pos rfl]
    simp only [map_one, Units.val_one]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_univ, ← Nat.card_eq_fintype_card, dual_card]
  · rw [if_neg hh]
    exact dual_sum_eq_zero hh

/-- `thm:constraint-character`: the finite constraint–character
partition duality
`Z_A(b; w) = |G|⁻ᵐ ∑_η η(b⁻¹) ∏ⱼ ŵⱼ((A^∨η)ⱼ)`. -/
theorem constraint_character {G : Type*} [CommGroup G]
    [Fintype G] [DecidableEq G] {n m : ℕ}
    (A : (Fin n → G) →* (Fin m → G)) (w : Fin n → G → ℂ)
    (b : Fin m → G) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin n → G => A x = b),
        ∏ j, w j (x j)
      = ((Fintype.card G : ℂ) ^ m)⁻¹
        * ∑ η : (Fin m → G) →* ℂˣ,
            ((η (b⁻¹) : ℂˣ) : ℂ)
              * ∏ j, ∑ g, w j g
                  * ((η (A (Pi.mulSingle j g)) : ℂˣ) : ℂ) := by
  have hG0 : ((Fintype.card G : ℂ)) ^ m ≠ 0 :=
    pow_ne_zero m (by exact_mod_cast Fintype.card_ne_zero)
  have hcardH : (Nat.card (Fin m → G) : ℂ)
      = (Fintype.card G : ℂ) ^ m := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun,
      Fintype.card_fin]
    push_cast
    ring
  have hswap : ∀ η : (Fin m → G) →* ℂˣ,
      ∏ j, ∑ g, w j g * ((η (A (Pi.mulSingle j g)) : ℂˣ) : ℂ)
        = ∑ x : Fin n → G,
            (∏ j, w j (x j)) * ((η (A x) : ℂˣ) : ℂ) := by
    intro η
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.prod_mul_distrib]
    congr 1
    calc ∏ j, ((η (A (Pi.mulSingle j (x j))) : ℂˣ) : ℂ)
        = (((∏ j, η (A (Pi.mulSingle j (x j)))) : ℂˣ) : ℂ) :=
          (map_prod (Units.coeHom ℂ) _ Finset.univ).symm
      _ = ((η (∏ j, A (Pi.mulSingle j (x j))) : ℂˣ) : ℂ) := by
          rw [← map_prod η]
      _ = ((η (A (∏ j, Pi.mulSingle j (x j))) : ℂˣ) : ℂ) := by
          rw [← map_prod A]
      _ = ((η (A x) : ℂˣ) : ℂ) := by
          rw [Finset.univ_prod_mulSingle]
  have hmain :
      ∑ η : (Fin m → G) →* ℂˣ,
          ((η (b⁻¹) : ℂˣ) : ℂ)
            * ∏ j, ∑ g, w j g
                * ((η (A (Pi.mulSingle j g)) : ℂˣ) : ℂ)
        = ∑ x : Fin n → G,
            if A x = b
            then (∏ j, w j (x j)) * (Fintype.card G : ℂ) ^ m
            else 0 := by
    calc ∑ η : (Fin m → G) →* ℂˣ,
            ((η (b⁻¹) : ℂˣ) : ℂ)
              * ∏ j, ∑ g, w j g
                  * ((η (A (Pi.mulSingle j g)) : ℂˣ) : ℂ)
        = ∑ η : (Fin m → G) →* ℂˣ, ∑ x : Fin n → G,
            (∏ j, w j (x j))
              * ((η (A x * b⁻¹) : ℂˣ) : ℂ) := by
          refine Finset.sum_congr rfl fun η _ => ?_
          rw [hswap η, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [map_mul, Units.val_mul]
          ring
      _ = ∑ x : Fin n → G, ∑ η : (Fin m → G) →* ℂˣ,
            (∏ j, w j (x j))
              * ((η (A x * b⁻¹) : ℂˣ) : ℂ) := Finset.sum_comm
      _ = ∑ x : Fin n → G,
            (∏ j, w j (x j))
              * ∑ η : (Fin m → G) →* ℂˣ,
                  ((η (A x * b⁻¹) : ℂˣ) : ℂ) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ x : Fin n → G,
            if A x = b
            then (∏ j, w j (x j)) * (Fintype.card G : ℂ) ^ m
            else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [dual_sum_indicator (A x * b⁻¹), mul_ite, mul_zero,
            hcardH]
          exact if_congr mul_inv_eq_one rfl rfl
  rw [Finset.sum_filter, hmain, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_ite, mul_zero]
  by_cases hx : A x = b
  · rw [if_pos hx, if_pos hx]
    field_simp
  · rw [if_neg hx, if_neg hx]

end NCG
