/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteProjectionAndReturnIdentities

/-!
# Exact full-to-colour Pythagoras and first memory row

This derives CY.4 from the actual full slab, colour isometry, and proposed
colour slab, then invokes the orthogonal Gram theorem for CY.5--CY.6.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:SMYM-colour-law-Pythagoras`, equations CY.4--CY.6. -/
theorem colour_slab_memory_pythagoras_exact
    {sm c : Type*} [Fintype sm] [Fintype c] [DecidableEq sm] [DecidableEq c]
    (P : Matrix sm sm ℂ) (hP : Pᴴ = P)
    (J : Matrix sm c ℂ) (hJ : Jᴴ * J = 1)
    (Q : Matrix c c ℂ) :
    let M1 := Jᴴ * P * J
    let M2 := Jᴴ * (P * P) * J
    let C := M1 - Q
    let L := (1 - J * Jᴴ) * P * J
    let V := Lᴴ * L
    V = M2 - M1 * M1
      ∧ V.PosSemidef
      ∧ P * J - J * Q = L + J * C
      ∧ (P * J - J * Q)ᴴ * (P * J - J * Q) = V + Cᴴ * C
      ∧ (P * J = J * Q ↔ C = 0 ∧ V = 0) := by
  dsimp only
  let M1 : Matrix c c ℂ := Jᴴ * P * J
  let M2 : Matrix c c ℂ := Jᴴ * (P * P) * J
  let C : Matrix c c ℂ := M1 - Q
  let L : Matrix sm c ℂ := (1 - J * Jᴴ) * P * J
  let V : Matrix c c ℂ := Lᴴ * L
  have hM1H : M1ᴴ = M1 := by
    dsimp [M1]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hP]
    simp only [Matrix.mul_assoc]
  have hcan (X : Matrix c c ℂ) : Jᴴ * (J * X) = X := by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have hJcompl : Jᴴ * (1 - J * Jᴴ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hJ,
      Matrix.one_mul, sub_self]
  have hJL : Jᴴ * L = 0 := by
    dsimp [L]
    calc
      Jᴴ * ((1 - J * Jᴴ) * P * J) =
          (Jᴴ * (1 - J * Jᴴ)) * P * J := by
            simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hJcompl, Matrix.zero_mul, Matrix.zero_mul]
  have hM1apply : Jᴴ * (P * J) = M1 := by
    simp [M1, Matrix.mul_assoc]
  have hM2apply : Jᴴ * (P * (P * J)) = M2 := by
    simp [M2, Matrix.mul_assoc]

  have hLalt : L = P * J - J * M1 := by
    dsimp [L]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    rw [hM1apply]
  have hsplit : P * J - J * Q = L + J * C := by
    rw [hLalt]
    dsimp [C]
    rw [Matrix.mul_sub]
    abel

  have hPM1 : Jᴴ * (P * (J * M1)) = M1 * M1 := by
    calc
      Jᴴ * (P * (J * M1)) = (Jᴴ * (P * J)) * M1 := by
        simp only [Matrix.mul_assoc]
      _ = M1 * M1 := by rw [hM1apply]
  have hV : V = M2 - M1 * M1 := by
    dsimp [V]
    rw [hLalt, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hP, hM1H,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    simp only [Matrix.mul_assoc, hM1apply, hM2apply]
    rw [hPM1, hcan M1]
    abel
  have hpyth := FiniteProjectionAndReturnIdentities.colour_law_pythagoras
    P J Q L C hJ hJL hsplit
  refine ⟨hV, Matrix.posSemidef_conjTranspose_mul_self L,
    hsplit, ?_, ?_⟩
  · exact hpyth.1
  · rw [hpyth.2]
    constructor
    · rintro ⟨hL, hC⟩
      refine ⟨hC, ?_⟩
      change Lᴴ * L = 0
      rw [hL, Matrix.conjTranspose_zero, Matrix.zero_mul]
    · rintro ⟨hC, hVzero⟩
      refine ⟨?_, hC⟩
      have hgram : Lᴴ * L = 0 := by
        change Lᴴ * L = 0 at hVzero
        exact hVzero
      exact Matrix.conjTranspose_mul_self_eq_zero.mp hgram

end NCG
