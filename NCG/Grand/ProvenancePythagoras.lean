/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Orthogonal same-history provenance decomposition
  (`thm:SMST-provenance-Pythagoras` and
  `cor:SMST-record-native-provenance`,
  Gran-Tensor manuscript)

* `smst_provenance_pythagoras`:
  (i) the boxed three-panel Gram identity: for any
      resolution of the identity into hermitian idempotents
      `Q₁ + Q₂ + Q₃ = I`,
      `X*X = (Q₁X)*(Q₁X) + (Q₂X)*(Q₂X) + (Q₃X)*(Q₃X)` —
      applied to `X = B_H - B_rev` this is the split into
      pair-span leakage, reversal-even leakage, and
      normalization/orientation failure;
  (ii) mutual orthogonality of the three panel ranges;
  (iii) the retained-reversal construction: from a
      hermitian involution `Θ` and a hermitian idempotent
      `P` commuting with it, the triple
      `(I - P, P_ev P, P_odd P)` with
      `P_ev = (I+Θ)/2`, `P_odd = (I-Θ)/2` is exactly such a
      resolution.

* `smst_record_native_provenance`: the boxed closure
  `B_H = B_rev ⟺ ℙ_{H|±} = 0` — the complete provenance
  residual vanishes exactly when all three positive panels
  vanish.

The identification of `P_pair` with the Moore–Penrose
projection `ℬ(ℬ*ℬ)†ℬ*` onto the joint source range (so
every panel is reconstructed from the joint source Gram) is
the manuscript's least-squares layer.
-/

open Matrix
open scoped ComplexOrder

set_option linter.unusedSimpArgs false

namespace NCG

/-- `thm:SMST-provenance-Pythagoras`. -/
theorem smst_provenance_pythagoras {Y E : Type*}
    [Fintype Y] [DecidableEq Y] :
    -- (i) the boxed three-panel Gram identity
    (∀ (Q₁ Q₂ Q₃ : Matrix Y Y ℂ),
      Q₁ᴴ = Q₁ → Q₂ᴴ = Q₂ → Q₃ᴴ = Q₃ →
      Q₁ * Q₁ = Q₁ → Q₂ * Q₂ = Q₂ → Q₃ * Q₃ = Q₃ →
      Q₁ + Q₂ + Q₃ = 1 →
      ∀ X : Matrix Y E ℂ,
        Xᴴ * X = (Q₁ * X)ᴴ * (Q₁ * X)
          + (Q₂ * X)ᴴ * (Q₂ * X)
          + (Q₃ * X)ᴴ * (Q₃ * X))
    -- (ii) mutual orthogonality of the panel ranges
    ∧ (∀ (Q R : Matrix Y Y ℂ), Qᴴ = Q → Q * R = 0 →
        ∀ X : Matrix Y E ℂ, (Q * X)ᴴ * (R * X) = 0)
    -- (iii) the retained-reversal resolution
    ∧ (∀ Θ P : Matrix Y Y ℂ, Θᴴ = Θ → Θ * Θ = 1 →
        Pᴴ = P → P * P = P → Θ * P = P * Θ →
        ((1 - P) + ((2 : ℂ)⁻¹ • (1 + Θ)) * P
            + ((2 : ℂ)⁻¹ • (1 - Θ)) * P = 1)
          ∧ (((2 : ℂ)⁻¹ • (1 + Θ)) * P)ᴴ
              = ((2 : ℂ)⁻¹ • (1 + Θ)) * P
          ∧ ((((2 : ℂ)⁻¹ • (1 + Θ)) * P)
              * (((2 : ℂ)⁻¹ • (1 + Θ)) * P)
              = ((2 : ℂ)⁻¹ • (1 + Θ)) * P)
          ∧ ((((2 : ℂ)⁻¹ • (1 + Θ)) * P)
              * (((2 : ℂ)⁻¹ • (1 - Θ)) * P) = 0)) := by
  have hpanel : ∀ (Q : Matrix Y Y ℂ), Qᴴ = Q →
      Q * Q = Q → ∀ X : Matrix Y E ℂ,
      (Q * X)ᴴ * (Q * X) = Xᴴ * (Q * X) := by
    intro Q hH hI X
    rw [Matrix.conjTranspose_mul, hH, Matrix.mul_assoc,
      ← Matrix.mul_assoc Q Q X, hI]
  refine ⟨?_, ?_, ?_⟩
  · intro Q₁ Q₂ Q₃ h1H h2H h3H h1I h2I h3I hsum X
    rw [hpanel Q₁ h1H h1I, hpanel Q₂ h2H h2I,
      hpanel Q₃ h3H h3I]
    calc Xᴴ * X = Xᴴ * ((Q₁ + Q₂ + Q₃) * X) := by
          rw [hsum, Matrix.one_mul]
      _ = Xᴴ * (Q₁ * X) + Xᴴ * (Q₂ * X)
          + Xᴴ * (Q₃ * X) := by
          simp only [Matrix.add_mul, Matrix.mul_add]
  · intro Q R hH hQR X
    rw [Matrix.conjTranspose_mul, hH, Matrix.mul_assoc,
      ← Matrix.mul_assoc Q R X, hQR, Matrix.zero_mul,
      Matrix.mul_zero]
  · intro Θ P hΘH hΘ2 hPH hP2 hcomm
    -- the reversal-even and reversal-odd projectors
    have hevH : ((2 : ℂ)⁻¹ • ((1 : Matrix Y Y ℂ) + Θ))ᴴ
        = (2 : ℂ)⁻¹ • (1 + Θ) := by
      rw [Matrix.conjTranspose_smul,
        Matrix.conjTranspose_add,
        Matrix.conjTranspose_one, hΘH]
      congr 1
      norm_num
    have hevI : ((2 : ℂ)⁻¹ • ((1 : Matrix Y Y ℂ) + Θ))
        * ((2 : ℂ)⁻¹ • (1 + Θ))
        = (2 : ℂ)⁻¹ • (1 + Θ) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, Matrix.add_mul, Matrix.mul_add,
        Matrix.one_mul, Matrix.mul_one, hΘ2]
      module
    have hoddI : ((2 : ℂ)⁻¹ • ((1 : Matrix Y Y ℂ) - Θ))
        * ((2 : ℂ)⁻¹ • (1 - Θ))
        = (2 : ℂ)⁻¹ • (1 - Θ) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.one_mul, Matrix.mul_one, hΘ2]
      module
    have hevodd : ((2 : ℂ)⁻¹ • ((1 : Matrix Y Y ℂ) + Θ))
        * ((2 : ℂ)⁻¹ • (1 - Θ)) = 0 := by
      simp only [Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, Matrix.add_mul, Matrix.mul_sub,
        Matrix.one_mul, Matrix.mul_one, hΘ2]
      module
    have hevcomm : ((2 : ℂ)⁻¹ • ((1 : Matrix Y Y ℂ) + Θ))
        * P = P * ((2 : ℂ)⁻¹ • (1 + Θ)) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul,
        Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
        Matrix.mul_one, hcomm]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hsum : ((2 : ℂ)⁻¹ • ((1 : Matrix Y Y ℂ) + Θ))
          + ((2 : ℂ)⁻¹ • (1 - Θ)) = 1 := by module
      rw [add_assoc, ← Matrix.add_mul, hsum,
        Matrix.one_mul]
      abel
    · rw [Matrix.conjTranspose_mul, hPH, hevH, ← hevcomm]
    · calc (((2 : ℂ)⁻¹ • ((1 : Matrix Y Y ℂ) + Θ)) * P)
            * (((2 : ℂ)⁻¹ • (1 + Θ)) * P)
          = ((2 : ℂ)⁻¹ • (1 + Θ))
            * ((P * ((2 : ℂ)⁻¹ • (1 + Θ))) * P) := by
            simp only [Matrix.mul_assoc]
        _ = (((2 : ℂ)⁻¹ • (1 + Θ))
            * ((2 : ℂ)⁻¹ • (1 + Θ))) * (P * P) := by
            rw [← hevcomm]
            simp only [Matrix.mul_assoc]
        _ = ((2 : ℂ)⁻¹ • (1 + Θ)) * P := by
            rw [hevI, hP2]
    · calc (((2 : ℂ)⁻¹ • ((1 : Matrix Y Y ℂ) + Θ)) * P)
            * (((2 : ℂ)⁻¹ • (1 - Θ)) * P)
          = ((2 : ℂ)⁻¹ • (1 + Θ))
            * ((P * ((2 : ℂ)⁻¹ • (1 - Θ))) * P) := by
            simp only [Matrix.mul_assoc]
        _ = (((2 : ℂ)⁻¹ • (1 + Θ))
            * ((2 : ℂ)⁻¹ • (1 - Θ))) * (P * P) := by
            have hoddcomm :
                ((2 : ℂ)⁻¹ • ((1 : Matrix Y Y ℂ) - Θ)) * P
                = P * ((2 : ℂ)⁻¹ • (1 - Θ)) := by
              simp only [Matrix.smul_mul, Matrix.mul_smul,
                Matrix.sub_mul, Matrix.mul_sub,
                Matrix.one_mul, Matrix.mul_one, hcomm]
            rw [← hoddcomm]
            simp only [Matrix.mul_assoc]
        _ = 0 := by
            rw [hevodd, Matrix.zero_mul]

/-- `cor:SMST-record-native-provenance`. -/
theorem smst_record_native_provenance {Y E : Type*}
    [Fintype Y] [Finite E]
    (X L Em N : Matrix Y E ℂ)
    (hsplit : Xᴴ * X = Lᴴ * L + Emᴴ * Em + Nᴴ * N) :
    (X = 0 ↔ (Lᴴ * L = 0 ∧ Emᴴ * Em = 0 ∧ Nᴴ * N = 0)) := by
  haveI := Fintype.ofFinite E
  constructor
  · intro hX
    have h0 : Xᴴ * X = 0 := by
      rw [hX, Matrix.mul_zero]
    rw [h0] at hsplit
    have hL := Matrix.posSemidef_conjTranspose_mul_self L
    have hE := Matrix.posSemidef_conjTranspose_mul_self Em
    have hN := Matrix.posSemidef_conjTranspose_mul_self N
    -- a vanishing sum of positive panels kills each panel
    have hsum : (Lᴴ * L).trace + (Emᴴ * Em).trace
        + (Nᴴ * N).trace = 0 := by
      have := congrArg Matrix.trace hsplit.symm
      rw [Matrix.trace_add, Matrix.trace_add,
        Matrix.trace_zero] at this
      exact this
    have htriple : ∀ x y z : ℂ, 0 ≤ x → 0 ≤ y → 0 ≤ z →
        x + y + z = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
      intro x y z hx hy hz hxyz
      refine ⟨le_antisymm ?_ hx, le_antisymm ?_ hy,
        le_antisymm ?_ hz⟩
      · calc x ≤ x + (y + z) :=
              le_add_of_nonneg_right (add_nonneg hy hz)
          _ = 0 := by rw [← hxyz]; ring
      · calc y ≤ y + (x + z) :=
              le_add_of_nonneg_right (add_nonneg hx hz)
          _ = 0 := by rw [← hxyz]; ring
      · calc z ≤ z + (x + y) :=
              le_add_of_nonneg_right (add_nonneg hx hy)
          _ = 0 := by rw [← hxyz]; ring
    obtain ⟨hL0, hE0, hN0⟩ := htriple _ _ _
      hL.trace_nonneg hE.trace_nonneg hN.trace_nonneg hsum
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
        hL0, Matrix.conjTranspose_zero, Matrix.mul_zero]
    · rw [Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
        hE0, Matrix.conjTranspose_zero, Matrix.mul_zero]
    · rw [Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
        hN0, Matrix.conjTranspose_zero, Matrix.mul_zero]
  · rintro ⟨hL, hE, hN⟩
    rw [hL, hE, hN, add_zero, add_zero] at hsplit
    exact Matrix.conjTranspose_mul_self_eq_zero.mp hsplit

end NCG
