/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Character–residue Parseval identity
  (`thm:residue-parseval`, arithmetic monograph)

For packets `v : (ZMod n)ˣ → H` in a complex inner-product space,
with residue mean `v̄ = φ(n)⁻¹ Σ_a v_a` and character packets
`G_χ = Σ_a χ(a) v_a`,

  `Σ_a ‖v_a − v̄‖² = φ(n)⁻¹ Σ_{χ ≠ χ₀} ‖G_χ‖²`.

* `charPacket` — the character packet `G_χ`;
* `residue_parseval` — the identity for a general modulus (with
  `φ(n)` in place of `q − 1`);
* `residue_parseval_prime` — the manuscript display for a prime
  modulus `q`, where `φ(q) = q − 1`.

The proof is the finite Plancherel identity for the character
group of `(ZMod n)ˣ` (`DirichletCharacter.sum_char_inv_mul_char_eq`)
with the principal channel subtracted.
-/

open Finset

namespace NCG

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

/-- The character packet `G_χ = Σ_a χ(a) v_a`. -/
noncomputable def charPacket {n : ℕ} [NeZero n] (v : (ZMod n)ˣ → H)
    (χ : DirichletCharacter ℂ n) : H :=
  ∑ a : (ZMod n)ˣ, χ (a : ZMod n) • v a

/-- `thm:residue-parseval` (general modulus): the residue variance
equals `φ(n)⁻¹` times the nonprincipal character energy. -/
theorem residue_parseval {n : ℕ} [NeZero n] (v : (ZMod n)ˣ → H) :
    (∑ a : (ZMod n)ˣ,
        ‖v a - (n.totient : ℂ)⁻¹ • ∑ b : (ZMod n)ˣ, v b‖ ^ 2)
      = (n.totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
          ‖charPacket v χ‖ ^ 2 := by
  classical
  set N : ℕ := n.totient with hNdef
  set S : H := ∑ b : (ZMod n)ˣ, v b with hSdef
  have hcard : Fintype.card (ZMod n)ˣ = N := ZMod.card_units_eq_totient n
  have hN0 : 0 < N := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hNC : ((N : ℂ)) ≠ 0 := by exact_mod_cast hN0.ne'
  -- conjugate character values are values at the inverse
  have hconj : ∀ (χ : DirichletCharacter ℂ n) (u : (ZMod n)ˣ),
      (starRingEnd ℂ) (χ (u : ZMod n)) = χ ((u : ZMod n)⁻¹) := by
    intro χ u
    have h1 : χ (u : ZMod n) * χ ((u : ZMod n)⁻¹) = 1 := by
      rw [← map_mul, ZMod.mul_inv_of_unit _ u.isUnit, map_one]
    rw [← RCLike.inv_eq_conj (χ.unit_norm_eq_one u)]
    exact (eq_inv_of_mul_eq_one_right h1).symm
  -- orthogonality delta
  have hδ : ∀ a b : (ZMod n)ˣ,
      (∑ χ : DirichletCharacter ℂ n,
          χ ((a : ZMod n)⁻¹) * χ (b : ZMod n))
        = if a = b then (N : ℂ) else 0 := by
    intro a b
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit (b : ZMod n)]
    by_cases hab : a = b
    · simp [hab, hNdef]
    · have hne : (a : ZMod n) ≠ (b : ZMod n) := fun h => hab (Units.ext h)
      simp [hab, hne]
  -- Plancherel over the full character group
  have hpars : (∑ χ : DirichletCharacter ℂ n,
        ⟪charPacket v χ, charPacket v χ⟫)
      = (N : ℂ) * ∑ a : (ZMod n)ˣ, ⟪v a, v a⟫ := by
    have hexp : ∀ χ : DirichletCharacter ℂ n,
        ⟪charPacket v χ, charPacket v χ⟫
          = ∑ a : (ZMod n)ˣ, ∑ b : (ZMod n)ˣ,
              χ ((a : ZMod n)⁻¹) * χ (b : ZMod n) * ⟪v a, v b⟫ := by
      intro χ
      rw [charPacket, sum_inner]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [inner_smul_left, inner_smul_right, hconj χ a]
      ring
    rw [Finset.sum_congr rfl fun χ _ => hexp χ, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
    have hstep : ∀ a : (ZMod n)ˣ,
        (∑ b : (ZMod n)ˣ, ∑ χ : DirichletCharacter ℂ n,
            χ ((a : ZMod n)⁻¹) * χ (b : ZMod n) * ⟪v a, v b⟫)
          = (N : ℂ) * ⟪v a, v a⟫ := by
      intro a
      have hfac : ∀ b : (ZMod n)ˣ,
          (∑ χ : DirichletCharacter ℂ n,
              χ ((a : ZMod n)⁻¹) * χ (b : ZMod n) * ⟪v a, v b⟫)
            = (if a = b then (N : ℂ) else 0) * ⟪v a, v b⟫ := by
        intro b
        rw [← Finset.sum_mul, hδ a b]
      rw [Finset.sum_congr rfl fun b _ => hfac b]
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp
    rw [Finset.sum_congr rfl fun a _ => hstep a, ← Finset.mul_sum]
  -- the principal packet is the plain residue sum
  have hG1 : charPacket v (1 : DirichletCharacter ℂ n) = S := by
    rw [charPacket, hSdef]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [MulChar.one_apply_coe, one_smul]
  -- nonprincipal energy from the full Plancherel identity
  have hsplit : (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
        ⟪charPacket v χ, charPacket v χ⟫)
      = (N : ℂ) * (∑ a : (ZMod n)ˣ, ⟪v a, v a⟫) - ⟪S, S⟫ := by
    have h := Finset.sum_erase_add Finset.univ
      (fun χ : DirichletCharacter ℂ n =>
        ⟪charPacket v χ, charPacket v χ⟫)
      (Finset.mem_univ (1 : DirichletCharacter ℂ n))
    rw [hpars, hG1] at h
    linear_combination h
  -- conjugation of the real scalar
  have hconjN : (starRingEnd ℂ) ((N : ℂ)⁻¹) = (N : ℂ)⁻¹ := by
    rw [map_inv₀, map_natCast]
  -- the centred variance in inner-product form
  have hLHS : (∑ a : (ZMod n)ˣ,
        ⟪v a - (N : ℂ)⁻¹ • S, v a - (N : ℂ)⁻¹ • S⟫)
      = (∑ a : (ZMod n)ˣ, ⟪v a, v a⟫) - (N : ℂ)⁻¹ * ⟪S, S⟫ := by
    simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right,
      hconjN]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← sum_inner, ← inner_sum, ← hSdef, Finset.sum_const,
      Finset.card_univ, hcard, nsmul_eq_mul]
    field_simp
    ring
  -- assemble, and descend from `ℂ` to the real norms
  have hns : ∀ x : H, ((‖x‖ : ℂ)) ^ 2 = ⟪x, x⟫ := fun x => by
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_eq_complex_ofReal]
  refine Complex.ofReal_injective ?_
  push_cast
  simp only [hns]
  rw [hLHS, hsplit]
  field_simp

/-- `thm:residue-parseval` (manuscript display, prime modulus `q`):
`Σ_a ‖v_a − v̄‖² = (q−1)⁻¹ Σ_{χ ≠ χ₀} ‖G_χ‖²`. -/
theorem residue_parseval_prime {q : ℕ} [Fact q.Prime]
    (v : (ZMod q)ˣ → H) :
    (∑ a : (ZMod q)ˣ,
        ‖v a - ((q : ℂ) - 1)⁻¹ • ∑ b : (ZMod q)ˣ, v b‖ ^ 2)
      = ((q : ℝ) - 1)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖charPacket v χ‖ ^ 2 := by
  have hq : q.Prime := Fact.out
  have h1 : (q.totient : ℂ) = (q : ℂ) - 1 := by
    rw [Nat.totient_prime hq, Nat.cast_sub (Nat.Prime.one_lt hq).le,
      Nat.cast_one]
  have h1r : (q.totient : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.totient_prime hq, Nat.cast_sub (Nat.Prime.one_lt hq).le,
      Nat.cast_one]
  rw [← h1, ← h1r]
  exact residue_parseval v

end NCG
