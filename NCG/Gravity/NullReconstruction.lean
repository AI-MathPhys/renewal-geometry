/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Null reconstruction (GR_emergence, Phase 1)

`lem:null-reconstruction`: in a Lorentzian vector space, if a
symmetric bilinear form `A` satisfies `A(k,k) = 0` for every
`g`-null vector `k`, then `A = f·g`.  Concretely, over Minkowski
space `ℝ^{1+d}` with `η = diag(-1, 1, …, 1)`, every symmetric matrix
whose quadratic form vanishes on the null cone is the multiple
`-(A₀₀)·η`.  This is the linear-algebra input of the local-wedge
Einstein assembly: the Clausius balance only constrains
`R_{μν}k^μk^ν` on null `k`, and null reconstruction upgrades that to
a tensor equation up to a trace term.
-/

namespace NCG

open Matrix

section NullReconstruction

variable {d : ℕ}

/-- The Minkowski matrix `η = diag(-1, 1, …, 1)` on `Fin (d+1)`. -/
def minkMatrix (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.diagonal fun a => if a = 0 then -1 else 1

/-- Bilinear pairing of basis vectors through a matrix. -/
theorem single_bilin (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (a b : Fin (d + 1)) :
    Pi.single a (1:ℝ) ⬝ᵥ M.mulVec (Pi.single b 1) = M a b := by
  rw [Matrix.mulVec_single]
  simp [dotProduct, Pi.single_apply]

/-- Quadratic form of a two-term combination
`c₁·e_a + c₂·e_b`. -/
theorem quad_two (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (a b : Fin (d + 1)) (c1 c2 : ℝ) :
    (c1 • Pi.single a (1:ℝ) + c2 • Pi.single b 1) ⬝ᵥ
        M.mulVec (c1 • Pi.single a 1 + c2 • Pi.single b 1)
      = c1 ^ 2 * M a a + c1 * c2 * (M a b + M b a)
        + c2 ^ 2 * M b b := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, single_bilin,
    smul_eq_mul]
  ring

/-- Quadratic form of a three-term combination
`c₁·e_a + c₂·e_b + c₃·e_c`. -/
theorem quad_three (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (a b c : Fin (d + 1)) (c1 c2 c3 : ℝ) :
    (c1 • Pi.single a (1:ℝ) + c2 • Pi.single b 1 + c3 • Pi.single c 1) ⬝ᵥ
        M.mulVec (c1 • Pi.single a 1 + c2 • Pi.single b 1
          + c3 • Pi.single c 1)
      = c1 ^ 2 * M a a + c2 ^ 2 * M b b + c3 ^ 2 * M c c
        + c1 * c2 * (M a b + M b a) + c1 * c3 * (M a c + M c a)
        + c2 * c3 * (M b c + M c b) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, single_bilin,
    smul_eq_mul]
  ring

/-- The Minkowski entries. -/
theorem minkMatrix_apply (a b : Fin (d + 1)) :
    minkMatrix d a b
      = if a = b then (if a = 0 then (-1:ℝ) else 1) else 0 := by
  unfold minkMatrix
  by_cases h : a = b
  · subst h
    rw [Matrix.diagonal_apply_eq]
    simp
  · rw [Matrix.diagonal_apply_ne _ h]
    simp [h]

/-- `lem:null-reconstruction`: a symmetric matrix whose quadratic
form vanishes on the whole Minkowski null cone is proportional to
the metric, `A = (-A₀₀)·η`. -/
theorem null_reconstruction (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hsymm : ∀ a b, A a b = A b a)
    (hnull : ∀ v : Fin (d + 1) → ℝ,
      v ⬝ᵥ (minkMatrix d).mulVec v = 0 → v ⬝ᵥ A.mulVec v = 0) :
    A = (-(A 0 0)) • minkMatrix d := by
  -- Null tests along e₀ ± eᵢ give the mixed and diagonal entries.
  have hmix : ∀ i : Fin (d + 1), i ≠ 0 →
      A 0 i = 0 ∧ A i i = -(A 0 0) := by
    intro i hi
    have hη : ∀ ε : ℝ, ε ^ 2 = 1 →
        ((1:ℝ) • Pi.single (0 : Fin (d + 1)) (1:ℝ) + ε • Pi.single i 1) ⬝ᵥ
          (minkMatrix d).mulVec
            ((1:ℝ) • Pi.single 0 1 + ε • Pi.single i 1) = 0 := by
      intro ε hε
      rw [quad_two]
      rw [minkMatrix_apply, minkMatrix_apply, minkMatrix_apply,
        minkMatrix_apply]
      simp [hi, Ne.symm hi]
      nlinarith [hε]
    have hp := hnull _ (hη 1 (by norm_num))
    have hm := hnull _ (hη (-1) (by norm_num))
    rw [quad_two] at hp hm
    have hs := hsymm 0 i
    constructor
    · nlinarith [hp, hm, hs]
    · nlinarith [hp, hm]
  -- Null tests along √2·e₀ + eᵢ + eⱼ give the spatial off-diagonals.
  have hoff : ∀ i j : Fin (d + 1), i ≠ 0 → j ≠ 0 → i ≠ j →
      A i j = 0 := by
    intro i j hi hj hij
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hη : (Real.sqrt 2 • Pi.single (0 : Fin (d + 1)) (1:ℝ)
          + (1:ℝ) • Pi.single i 1 + (1:ℝ) • Pi.single j 1) ⬝ᵥ
        (minkMatrix d).mulVec
          (Real.sqrt 2 • Pi.single 0 1 + (1:ℝ) • Pi.single i 1
            + (1:ℝ) • Pi.single j 1) = 0 := by
      rw [quad_three]
      rw [minkMatrix_apply, minkMatrix_apply, minkMatrix_apply,
        minkMatrix_apply, minkMatrix_apply, minkMatrix_apply,
        minkMatrix_apply, minkMatrix_apply, minkMatrix_apply]
      simp [hi, hj, hij, Ne.symm hi, Ne.symm hj, Ne.symm hij]
      nlinarith [hsq]
    have hq := hnull _ hη
    rw [quad_three] at hq
    have h0i := (hmix i hi).1
    have h0j := (hmix j hj).1
    have hii := (hmix i hi).2
    have hjj := (hmix j hj).2
    have hAi0 : A i 0 = 0 := by rw [← hsymm 0 i]; exact h0i
    have hAj0 : A j 0 = 0 := by rw [← hsymm 0 j]; exact h0j
    have hsij := hsymm i j
    rw [h0i, h0j, hAi0, hAj0, hii, hjj, hsq, ← hsij] at hq
    linarith
  -- Assemble the tensor equation entrywise.
  ext a b
  rw [Matrix.smul_apply, minkMatrix_apply]
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · subst ha; subst hb
      simp
    · subst ha
      rw [if_neg (fun h => hb h.symm)]
      rw [(hmix b hb).1]
      simp
  · by_cases hb : b = 0
    · subst hb
      rw [if_neg (fun h => ha h)]
      rw [hsymm a 0, (hmix a ha).1]
      simp
    · by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, if_neg ha, (hmix a ha).2]
        simp
      · rw [if_neg hab, hoff a b ha hb hab]
        simp

end NullReconstruction

end NCG
