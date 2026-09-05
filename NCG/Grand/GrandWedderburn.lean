/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandMultSaturation

/-!
# Block commutant, bicommutant, and the edge commutant
  (`thm:commutant-decomposition`, `thm:SMST-trinity`,
   `thm:SMST-edge-commutant`, Gran-Tensor manuscript)

On the decomposed carrier `(I₁×J₁) ⊕ (I₂×J₂)` with the sector
algebra acting block-diagonally as `(g⊗1) ⊕ (h⊗1)`:

* `commutant_decomposition`: the commutant is exactly the
  block-diagonal multiplicity algebra
  `{(1⊗B₁) ⊕ (1⊗B₂)}` — off-diagonal blocks vanish against the
  sector projections and each diagonal block is a marked
  Kronecker commutant;
* `block_bicommutant`: the commutant of the multiplicity
  algebra is the sector algebra back — `𝒞'' = 𝒞`, the
  finite bicommutant identification;
* `smst_edge_commutant`: adjoining one nondegenerate edge
  `Y = [[0, D⊗F],[0,0]]` with invertible `F` cuts the
  commutant to a single copy
  `{(1⊗B) ⊕ (1⊗F⁻¹BF)}` — the typed multiplicity algebra with
  one common dimension, transported along the edge.

Rendering disclosed: the reduction of an abstract
finite-dimensional C*-algebra to this decomposed frame is the
Artin–Wedderburn classification (`NCG.Matter.FiniteAlgebra`);
the general connected-incidence statement iterates the
single-edge transport along a spanning tree.
-/

open Matrix Kronecker

namespace NCG

variable {I1 J1 I2 J2 : Type*}
  [Fintype I1] [Fintype J1] [Fintype I2] [Fintype J2]
  [DecidableEq I1] [DecidableEq J1] [DecidableEq I2]
  [DecidableEq J2]

/-- `thm:commutant-decomposition`: the commutant of the
block-diagonal sector algebra is the block-diagonal
multiplicity algebra. -/
theorem commutant_decomposition [Nonempty I1] [Nonempty I2]
    (X : Matrix ((I1 × J1) ⊕ (I2 × J2))
      ((I1 × J1) ⊕ (I2 × J2)) ℂ)
    (hcomm : ∀ (g : Matrix I1 I1 ℂ) (h : Matrix I2 I2 ℂ),
      Matrix.fromBlocks (g ⊗ₖ (1 : Matrix J1 J1 ℂ)) 0 0
          (h ⊗ₖ (1 : Matrix J2 J2 ℂ)) * X
        = X * Matrix.fromBlocks (g ⊗ₖ 1) 0 0 (h ⊗ₖ 1)) :
    ∃ (B1 : Matrix J1 J1 ℂ) (B2 : Matrix J2 J2 ℂ),
      X = Matrix.fromBlocks
        ((1 : Matrix I1 I1 ℂ) ⊗ₖ B1) 0 0
        ((1 : Matrix I2 I2 ℂ) ⊗ₖ B2) := by
  obtain ⟨A, B, C, D, rfl⟩ :
      ∃ A B C D, X = Matrix.fromBlocks A B C D :=
    ⟨X.toBlocks₁₁, X.toBlocks₁₂, X.toBlocks₂₁, X.toBlocks₂₂,
      (Matrix.fromBlocks_toBlocks X).symm⟩
  have hP := hcomm 1 0
  rw [Matrix.one_kronecker_one, Matrix.zero_kronecker,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    at hP
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero] at hP
  have hB : B = 0 := by
    have h12 := congrArg Matrix.toBlocks₁₂ hP
    simp only [Matrix.toBlocks_fromBlocks₁₂] at h12
    exact h12
  have hC : C = 0 := by
    have h21 := congrArg Matrix.toBlocks₂₁ hP
    simp only [Matrix.toBlocks_fromBlocks₂₁] at h21
    exact h21.symm
  subst hB
  subst hC
  have h11 : ∀ g : Matrix I1 I1 ℂ,
      (g ⊗ₖ (1 : Matrix J1 J1 ℂ)) * A = A * (g ⊗ₖ 1) := by
    intro g
    have h := hcomm g 0
    rw [Matrix.zero_kronecker, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply] at h
    have h1 := congrArg Matrix.toBlocks₁₁ h
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.zero_mul,
      Matrix.mul_zero, add_zero] at h1
    exact h1
  have h22 : ∀ h : Matrix I2 I2 ℂ,
      (h ⊗ₖ (1 : Matrix J2 J2 ℂ)) * D = D * (h ⊗ₖ 1) := by
    intro hM
    have h := hcomm 0 hM
    rw [Matrix.zero_kronecker, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply] at h
    have h2 := congrArg Matrix.toBlocks₂₂ h
    simp only [Matrix.toBlocks_fromBlocks₂₂, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add] at h2
    exact h2
  obtain ⟨B1, hB1⟩ := CommonOrigin.left_factor_commutant A h11
  obtain ⟨B2, hB2⟩ := CommonOrigin.left_factor_commutant D h22
  exact ⟨B1, B2, by rw [hB1, hB2]⟩

/-- `thm:SMST-trinity`, bicommutant clause: the commutant of
the multiplicity algebra is the sector algebra back —
`𝒞'' = 𝒞`. -/
theorem block_bicommutant [Nonempty J1] [Nonempty J2]
    (X : Matrix ((I1 × J1) ⊕ (I2 × J2))
      ((I1 × J1) ⊕ (I2 × J2)) ℂ)
    (hcomm : ∀ (B1 : Matrix J1 J1 ℂ) (B2 : Matrix J2 J2 ℂ),
      Matrix.fromBlocks ((1 : Matrix I1 I1 ℂ) ⊗ₖ B1) 0 0
          ((1 : Matrix I2 I2 ℂ) ⊗ₖ B2) * X
        = X * Matrix.fromBlocks ((1 : Matrix I1 I1 ℂ) ⊗ₖ B1)
            0 0 ((1 : Matrix I2 I2 ℂ) ⊗ₖ B2)) :
    ∃ (A1 : Matrix I1 I1 ℂ) (A2 : Matrix I2 I2 ℂ),
      X = Matrix.fromBlocks
        (A1 ⊗ₖ (1 : Matrix J1 J1 ℂ)) 0 0
        (A2 ⊗ₖ (1 : Matrix J2 J2 ℂ)) := by
  obtain ⟨A, B, C, D, rfl⟩ :
      ∃ A B C D, X = Matrix.fromBlocks A B C D :=
    ⟨X.toBlocks₁₁, X.toBlocks₁₂, X.toBlocks₂₁, X.toBlocks₂₂,
      (Matrix.fromBlocks_toBlocks X).symm⟩
  have hP := hcomm 1 0
  rw [Matrix.one_kronecker_one, Matrix.kronecker_zero,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    at hP
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero] at hP
  have hB : B = 0 := by
    have h12 := congrArg Matrix.toBlocks₁₂ hP
    simp only [Matrix.toBlocks_fromBlocks₁₂] at h12
    exact h12
  have hC : C = 0 := by
    have h21 := congrArg Matrix.toBlocks₂₁ hP
    simp only [Matrix.toBlocks_fromBlocks₂₁] at h21
    exact h21.symm
  subst hB
  subst hC
  have h11 : ∀ B1 : Matrix J1 J1 ℂ,
      ((1 : Matrix I1 I1 ℂ) ⊗ₖ B1) * A
        = A * ((1 : Matrix I1 I1 ℂ) ⊗ₖ B1) := by
    intro B1
    have h := hcomm B1 0
    rw [Matrix.kronecker_zero, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply] at h
    have h1 := congrArg Matrix.toBlocks₁₁ h
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.zero_mul,
      Matrix.mul_zero, add_zero] at h1
    exact h1
  have h22 : ∀ B2 : Matrix J2 J2 ℂ,
      ((1 : Matrix I2 I2 ℂ) ⊗ₖ B2) * D
        = D * ((1 : Matrix I2 I2 ℂ) ⊗ₖ B2) := by
    intro B2
    have h := hcomm 0 B2
    rw [Matrix.kronecker_zero, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply] at h
    have h2 := congrArg Matrix.toBlocks₂₂ h
    simp only [Matrix.toBlocks_fromBlocks₂₂, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add] at h2
    exact h2
  obtain ⟨A1, hA1⟩ := right_factor_commutant A h11
  obtain ⟨A2, hA2⟩ := right_factor_commutant D h22
  exact ⟨A1, A2, by rw [hA1, hA2]⟩

/-- `thm:SMST-edge-commutant`: one nondegenerate edge with an
invertible link cuts the commutant to a single transported
multiplicity copy. -/
theorem smst_edge_commutant {L R g : Type*}
    [Fintype L] [Fintype R] [Fintype g]
    [DecidableEq L] [DecidableEq R] [DecidableEq g]
    [Nonempty L] [Nonempty R]
    (Dm : Matrix L R ℂ) (hD : Dm ≠ 0) (F : Matrix g g ℂ)
    [Invertible F]
    (X : Matrix ((L × g) ⊕ (R × g)) ((L × g) ⊕ (R × g)) ℂ)
    (hdiag : ∀ (a : Matrix L L ℂ) (b : Matrix R R ℂ),
      Matrix.fromBlocks (a ⊗ₖ (1 : Matrix g g ℂ)) 0 0
          (b ⊗ₖ (1 : Matrix g g ℂ)) * X
        = X * Matrix.fromBlocks (a ⊗ₖ 1) 0 0 (b ⊗ₖ 1))
    (hedge : Matrix.fromBlocks 0 (Dm ⊗ₖ F) 0
        (0 : Matrix (R × g) (R × g) ℂ) * X
      = X * Matrix.fromBlocks 0 (Dm ⊗ₖ F) 0 0) :
    ∃ B : Matrix g g ℂ,
      X = Matrix.fromBlocks ((1 : Matrix L L ℂ) ⊗ₖ B) 0 0
        ((1 : Matrix R R ℂ) ⊗ₖ (F⁻¹ * B * F)) := by
  obtain ⟨B1, B2, rfl⟩ := commutant_decomposition X hdiag
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    at hedge
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero,
    zero_add] at hedge
  have h12 := congrArg Matrix.toBlocks₁₂ hedge
  simp only [Matrix.toBlocks_fromBlocks₁₂] at h12
  -- h12 : (Dm ⊗ₖ F) * (1 ⊗ₖ B2) = (1 ⊗ₖ B1) * (Dm ⊗ₖ F)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul] at h12
  -- h12 : Dm ⊗ₖ (F * B2) = Dm ⊗ₖ (B1 * F)
  have hex : ∃ i j, Dm i j ≠ 0 := by
    by_contra hall
    apply hD
    ext i j
    rw [Matrix.zero_apply]
    by_contra hij
    exact hall ⟨i, j, hij⟩
  obtain ⟨i0, j0, hij⟩ := hex
  have hFB : F * B2 = B1 * F := by
    ext a b
    have h := congrFun (congrFun h12 (i0, a)) (j0, b)
    simp only [Matrix.kroneckerMap_apply] at h
    exact mul_left_cancel₀ hij h
  have hB2 : B2 = F⁻¹ * B1 * F := by
    calc B2 = F⁻¹ * (F * B2) := by
          rw [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
            Matrix.one_mul]
      _ = F⁻¹ * (B1 * F) := by rw [hFB]
      _ = F⁻¹ * B1 * F := by rw [Matrix.mul_assoc]
  exact ⟨B1, by rw [hB2]⟩

end NCG
