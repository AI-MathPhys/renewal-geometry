/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.GrandInterface2

/-!
# five-parameter pointed tetrahedral Gram

This file supplies the positivity block missing from `tetrahedral_gram`.
The four-label permutation block is diagonalized by the normalized Walsh
basis: its average line couples to the fixed anchor, while the three
augmentation directions all have eigenvalue `c - d`.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

set_option maxHeartbeats 800000

/-- The Hermitian five-parameter pointed tetrahedral Gram. -/
def pointedTetrahedralGram (a c d : ℝ) (b : ℂ) :
    Matrix (Fin 5) (Fin 5) ℂ :=
  !![(a : ℂ), b, b, b, b;
     star b, (c : ℂ), (d : ℂ), (d : ℂ), (d : ℂ);
     star b, (d : ℂ), (c : ℂ), (d : ℂ), (d : ℂ);
     star b, (d : ℂ), (d : ℂ), (c : ℂ), (d : ℂ);
     star b, (d : ℂ), (d : ℂ), (d : ℂ), (c : ℂ)]

/-- The anchor/normalized-average block. -/
def pointedTetrahedralTrivialBlock (a c d : ℝ) (b : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ), 2 * b; 2 * star b, ((c + 3 * d : ℝ) : ℂ)]

/-- The real normalized Walsh change of basis on the four labels, with the
anchor left fixed. -/
noncomputable def pointedTetrahedralWalsh : Matrix (Fin 5) (Fin 5) ℂ :=
  !![1, 0, 0, 0, 0;
     0, 1 / 2, 1 / 2, 1 / 2, 1 / 2;
     0, 1 / 2, 1 / 2, -1 / 2, -1 / 2;
     0, 1 / 2, -1 / 2, 1 / 2, -1 / 2;
     0, 1 / 2, -1 / 2, -1 / 2, 1 / 2]

/-- The isotypic block form: a two-dimensional trivial block and three
copies of the augmentation eigenvalue. -/
def pointedTetrahedralDiagonalized (a c d : ℝ) (b : ℂ) :
    Matrix (Fin 5) (Fin 5) ℂ :=
  !![(a : ℂ), 2 * b, 0, 0, 0;
     2 * star b, ((c + 3 * d : ℝ) : ℂ), 0, 0, 0;
     0, 0, ((c - d : ℝ) : ℂ), 0, 0;
     0, 0, 0, ((c - d : ℝ) : ℂ), 0;
     0, 0, 0, 0, ((c - d : ℝ) : ℂ)]

lemma pointedTetrahedralWalsh_self_adjoint :
    pointedTetrahedralWalshᴴ = pointedTetrahedralWalsh := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pointedTetrahedralWalsh, Matrix.conjTranspose_apply]

lemma pointedTetrahedralWalsh_sq :
    pointedTetrahedralWalsh * pointedTetrahedralWalsh = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pointedTetrahedralWalsh, Matrix.mul_apply, Fin.sum_univ_succ]
    <;> norm_num

lemma pointedTetrahedral_diagonalization (a c d : ℝ) (b : ℂ) :
    pointedTetrahedralWalshᴴ * pointedTetrahedralGram a c d b
        * pointedTetrahedralWalsh
      = pointedTetrahedralDiagonalized a c d b := by
  rw [pointedTetrahedralWalsh_self_adjoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pointedTetrahedralWalsh, pointedTetrahedralGram,
      pointedTetrahedralDiagonalized, Matrix.mul_apply, Fin.sum_univ_succ]
    <;> ring

lemma pointedTetrahedral_reconstruction (a c d : ℝ) (b : ℂ) :
    pointedTetrahedralWalsh * pointedTetrahedralDiagonalized a c d b
        * pointedTetrahedralWalshᴴ
      = pointedTetrahedralGram a c d b := by
  rw [pointedTetrahedralWalsh_self_adjoint]
  have hdiag :
      pointedTetrahedralWalsh * pointedTetrahedralGram a c d b
          * pointedTetrahedralWalsh
        = pointedTetrahedralDiagonalized a c d b := by
    simpa [pointedTetrahedralWalsh_self_adjoint] using
      pointedTetrahedral_diagonalization a c d b
  calc
    pointedTetrahedralWalsh * pointedTetrahedralDiagonalized a c d b
          * pointedTetrahedralWalsh
        = pointedTetrahedralWalsh *
            (pointedTetrahedralWalsh * pointedTetrahedralGram a c d b
              * pointedTetrahedralWalsh) * pointedTetrahedralWalsh := by
              rw [hdiag]
    _ = (pointedTetrahedralWalsh * pointedTetrahedralWalsh)
          * pointedTetrahedralGram a c d b
          * (pointedTetrahedralWalsh * pointedTetrahedralWalsh) := by
            noncomm_ring
    _ = pointedTetrahedralGram a c d b := by
          rw [pointedTetrahedralWalsh_sq]
          simp

lemma pointedTetrahedralDiagonalized_psd_iff (a c d : ℝ) (b : ℂ) :
    (pointedTetrahedralDiagonalized a c d b).PosSemidef ↔
      (pointedTetrahedralTrivialBlock a c d b).PosSemidef ∧ 0 ≤ c - d := by
  constructor
  · intro h
    constructor
    · have hs := h.submatrix (fun i : Fin 2 => Fin.castLE (by omega) i)
      convert hs using 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pointedTetrahedralDiagonalized,
          pointedTetrahedralTrivialBlock]
    · have hz := h.dotProduct_mulVec_nonneg
          (fun i : Fin 5 => if i = 2 then 1 else 0)
      simpa [pointedTetrahedralDiagonalized, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ] using hz
  · rintro ⟨hQ, hcd⟩
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pointedTetrahedralDiagonalized,
          pointedTetrahedralTrivialBlock, Matrix.IsHermitian,
          Matrix.conjTranspose_apply]
    · intro x
      have hq := hQ.dotProduct_mulVec_nonneg
        (fun i : Fin 2 => x (Fin.castLE (by omega) i))
      have hr : (0 : ℂ) ≤ ((c - d : ℝ) : ℂ) :=
        Complex.zero_le_real.mpr hcd
      have h2 : (0 : ℂ) ≤ (c - d : ℝ) * star (x 2) * x 2 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          star_left_conjugate_nonneg hr (x 2)
      have h3 : (0 : ℂ) ≤ (c - d : ℝ) * star (x 3) * x 3 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          star_left_conjugate_nonneg hr (x 3)
      have h4 : (0 : ℂ) ≤ (c - d : ℝ) * star (x 4) * x 4 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          star_left_conjugate_nonneg hr (x 4)
      have hsum := add_nonneg (add_nonneg (add_nonneg hq h2) h3) h4
      simp [pointedTetrahedralDiagonalized,
        pointedTetrahedralTrivialBlock, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] at hsum ⊢
      convert hsum using 1 <;> ring

/-- Exact positivity criterion for the five-parameter tetrahedral Gram. -/
theorem pointedTetrahedralGram_psd_iff (a c d : ℝ) (b : ℂ) :
    (pointedTetrahedralGram a c d b).PosSemidef ↔
      0 ≤ c - d ∧ (pointedTetrahedralTrivialBlock a c d b).PosSemidef := by
  rw [and_comm, ← pointedTetrahedralDiagonalized_psd_iff]
  constructor
  · intro h
    simpa [pointedTetrahedral_diagonalization] using
      h.conjTranspose_mul_mul_same pointedTetrahedralWalsh
  · intro h
    rw [← pointedTetrahedral_reconstruction]
    exact h.mul_mul_conjTranspose_same pointedTetrahedralWalsh

/-- A pointed family, written on the anchor followed by its four labels. -/
def pointedTetrahedralFamily {V : Type*} (ξt : V) (ξ : Fin 4 → V) :
    Fin 5 → V :=
  ![ξt, ξ 0, ξ 1, ξ 2, ξ 3]

/-- The complete Gram of a pointed family for a Hermitian pairing. -/
def pointedTetrahedralFamilyGram {V : Type*} (P : V → V → ℂ)
    (ξt : V) (ξ : Fin 4 → V) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => P (pointedTetrahedralFamily ξt ξ i)
    (pointedTetrahedralFamily ξt ξ j)

/-- Full exact manuscript statement: tetrahedral invariance and Hermiticity
force the displayed five-real-parameter matrix, and that matrix is positive
exactly on the augmentation half-line and the stated `2 × 2` trivial block. -/
theorem five_parameter_pointed_tetrahedral_gram
    {V : Type*} (P : V → V → ℂ) (ξt : V) (ξ : Fin 4 → V)
    (hherm : ∀ x y, star (P y x) = P x y)
    (hactP : ∀ g : Equiv.Perm (Fin 4), ∀ i j,
      P (ξ i) (ξ j) = P (ξ (g i)) (ξ (g j)))
    (hactT : ∀ g : Equiv.Perm (Fin 4), ∀ i,
      P ξt (ξ i) = P ξt (ξ (g i))) :
    ∃ a c d : ℝ, ∃ b : ℂ,
      pointedTetrahedralFamilyGram P ξt ξ
          = pointedTetrahedralGram a c d b
      ∧ ((pointedTetrahedralGram a c d b).PosSemidef ↔
          0 ≤ c - d ∧
            (pointedTetrahedralTrivialBlock a c d b).PosSemidef) := by
  have ht := tetrahedral_gram P ξt ξ hactP hactT
  let a : ℝ := (P ξt ξt).re
  let c : ℝ := (P (ξ 0) (ξ 0)).re
  let d : ℝ := (P (ξ 0) (ξ 1)).re
  let b : ℂ := P ξt (ξ 0)
  have haSelf := hherm ξt ξt
  rw [Complex.star_def] at haSelf
  have hcSelf := hherm (ξ 0) (ξ 0)
  rw [Complex.star_def] at hcSelf
  have hoffSwap : P (ξ 0) (ξ 1) = P (ξ 1) (ξ 0) :=
    ht.2.2 0 1 1 0 (by decide) (by decide)
  have hdStar : star (P (ξ 0) (ξ 1)) = P (ξ 0) (ξ 1) := by
    calc
      star (P (ξ 0) (ξ 1)) = P (ξ 1) (ξ 0) := hherm (ξ 1) (ξ 0)
      _ = P (ξ 0) (ξ 1) := hoffSwap.symm
  have hdSelf := hdStar
  rw [Complex.star_def] at hdSelf
  have ha : P ξt ξt = (a : ℂ) :=
    (Complex.conj_eq_iff_re.mp haSelf).symm
  have hc : P (ξ 0) (ξ 0) = (c : ℂ) :=
    (Complex.conj_eq_iff_re.mp hcSelf).symm
  have hd : P (ξ 0) (ξ 1) = (d : ℂ) :=
    (Complex.conj_eq_iff_re.mp hdSelf).symm
  have hanchor : ∀ i, P ξt (ξ i) = b := by
    intro i
    exact ht.1 i 0
  have hanchorStar : ∀ i, P (ξ i) ξt = star b := by
    intro i
    calc
      P (ξ i) ξt = star (P ξt (ξ i)) := (hherm (ξ i) ξt).symm
      _ = star b := congrArg star (hanchor i)
  have hdiag : ∀ i, P (ξ i) (ξ i) = (c : ℂ) := by
    intro i
    exact (ht.2.1 i 0).trans hc
  have hoff : ∀ i j, i ≠ j → P (ξ i) (ξ j) = (d : ℂ) := by
    intro i j hij
    exact (ht.2.2 i j 0 1 hij (by decide)).trans hd
  refine ⟨a, c, d, b, ?_, pointedTetrahedralGram_psd_iff a c d b⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pointedTetrahedralFamilyGram, pointedTetrahedralFamily,
      pointedTetrahedralGram, ha, hanchor, hanchorStar, hdiag, hoff]

end NCG
