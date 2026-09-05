/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Assembly before shorting and router dispersion
  (`thm:GT-assembly-before-short`, Gran-Tensor manuscript)

* `gt_assembly_before_short`: the boxed router-dispersion
  identity — for packets `Gᵢ = [[Aᵢ, Bᵢ], [Bᵢ*, Dᵢ]]` with
  routers `Kᵢ = Aᵢ⁻¹Bᵢ` and pooled router `K = A⁻¹B`,
  `∑ᵢ Bᵢ*Aᵢ⁻¹Bᵢ - B*A⁻¹B = ∑ᵢ (Kᵢ-K)*Aᵢ(Kᵢ-K)`,
  and the dispersion is positive semidefinite whenever the
  local heads `Aᵢ` are.  Adding `∑ᵢ Dᵢ` to both sides gives
  the boxed Schur form
  `S = ∑ᵢ Sᵢ + ∑ᵢ (Kᵢ-K)*Aᵢ(Kᵢ-K)`: shorting after
  coherent assembly retains a positive router-dispersion
  coordinate lost by separately shorting the local packets.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

set_option linter.unusedFintypeInType false in
/-- `thm:GT-assembly-before-short`. -/
theorem gt_assembly_before_short {ι n p : Type}
    [Fintype ι] [Fintype n] [Fintype p] [DecidableEq n]
    (A : ι → Matrix n n ℂ) (B : ι → Matrix n p ℂ)
    [∀ i, Invertible (A i)] [Invertible (∑ i, A i)]
    (hAH : ∀ i, (A i)ᴴ = A i) :
    -- the boxed router-dispersion identity
    ((∑ i, (B i)ᴴ * ((A i)⁻¹ * B i))
      - (∑ i, B i)ᴴ * ((∑ i, A i)⁻¹ * ∑ i, B i)
      = ∑ i, ((A i)⁻¹ * B i
            - (∑ i, A i)⁻¹ * ∑ i, B i)ᴴ
          * A i
          * ((A i)⁻¹ * B i
              - (∑ i, A i)⁻¹ * ∑ i, B i))
    -- positivity of the dispersion
    ∧ ((∀ i, (A i).PosSemidef) →
        (∑ i, ((A i)⁻¹ * B i
              - (∑ i, A i)⁻¹ * ∑ i, B i)ᴴ
            * A i
            * ((A i)⁻¹ * B i
                - (∑ i, A i)⁻¹ * ∑ i,
                    B i)).PosSemidef) := by
  set Ab := ∑ i, A i with hAb
  set Bb := ∑ i, B i with hBb
  set Kb := Ab⁻¹ * Bb with hKb
  have hAbH : Abᴴ = Ab := by
    rw [hAb, Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun i _ => hAH i
  have hAinvH : ∀ i, ((A i)⁻¹)ᴴ = (A i)⁻¹ := fun i => by
    rw [Matrix.conjTranspose_nonsing_inv, hAH i]
  have hAbinvH : (Ab⁻¹)ᴴ = Ab⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hAbH]
  constructor
  · have hterm : ∀ i,
        ((A i)⁻¹ * B i - Kb)ᴴ * A i
            * ((A i)⁻¹ * B i - Kb)
        = (B i)ᴴ * ((A i)⁻¹ * B i) - (B i)ᴴ * Kb
          - Kbᴴ * B i + Kbᴴ * (A i * Kb) := by
      intro i
      have h1 : ((A i)⁻¹ * B i)ᴴ * A i = (B i)ᴴ := by
        rw [Matrix.conjTranspose_mul, hAinvH i,
          Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
          Matrix.mul_one]
      have h2 : A i * ((A i)⁻¹ * B i) = B i :=
        Matrix.mul_inv_cancel_left_of_invertible _ _
      rw [Matrix.conjTranspose_sub, Matrix.sub_mul,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
        h1, Matrix.mul_assoc Kbᴴ (A i)
          ((A i)⁻¹ * B i), h2,
        Matrix.mul_assoc Kbᴴ (A i) Kb]
      abel
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
    have hs2 : ∑ i, (B i)ᴴ * Kb = Bbᴴ * Kb := by
      rw [← Matrix.sum_mul, hBb,
        ← Matrix.conjTranspose_sum]
    have hs3 : ∑ i, Kbᴴ * B i = Kbᴴ * Bb := by
      rw [← Matrix.mul_sum, hBb]
    have hs4 : ∑ i, Kbᴴ * (A i * Kb) = Kbᴴ * (Ab * Kb) := by
      rw [← Matrix.mul_sum, ← Matrix.sum_mul, hAb]
    rw [hs2, hs3, hs4]
    have hAbKb : Ab * Kb = Bb :=
      Matrix.mul_inv_cancel_left_of_invertible _ _
    have hKbBb : Kbᴴ * Bb = Bbᴴ * Kb := by
      rw [hKb, Matrix.conjTranspose_mul, hAbinvH,
        Matrix.mul_assoc]
    rw [hAbKb, hKbBb]
    abel
  · intro hpsd
    exact Finset.sum_induction _
      (fun M : Matrix p p ℂ => M.PosSemidef)
      (fun a b ha hb => ha.add hb)
      Matrix.PosSemidef.zero
      (fun i _ => (hpsd i).conjTranspose_mul_mul_same _)

end NCG
