/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Two-dimensional twisted carrier (`thm:twisted-carrier`, SM manuscript)

For a nontrivial sign local system `L_n` on `K₄` with twisted
incidence `B_n : C¹ → C⁰` (edge order `01,02,03,12,13,23`, edge
column `-1` at the tail and `ε_e` at the head), the two twist
orbits are represented by the edge twist (`ε = -1` on edge `01`)
and the triangle twist (`ε = -1` on `01, 02, 12`).  For both:

* `dim_ℂ H¹(K₄;L_n) = dim ker B_n = 2` (`finrank_edgeTwist_ker`,
  `finrank_triTwist_ker`) with explicit kernel bases and a complete
  parametrization of the kernel;
* the vertex-Hodge Laplacian `B_nB_n†` has the boxed spectra
  `{2, 4, 3-√5, 3+√5}` (edge twist: four exhibited eigenvectors
  with pairwise distinct eigenvalues, hence a complete
  eigenbasis) and `{2, 2, 2, 6}` (triangle twist: three
  independent `λ = 2` eigenvectors and one `λ = 6` eigenvector);
* the boxed harmonic projector `P_n = I₆ - B_n†(B_nB_n†)⁻¹B_n` is
  computed explicitly: with the certified inverse `W = (B_nB_n†)⁻¹`
  the explicit matrix `P_n` equals `I - B†WB`, is a Hermitian
  idempotent annihilated by `B_n`, and fixes the kernel basis —
  the orthogonal projection onto `ker B_n = H¹(K₄;L_n)`.

Spectra are rendered as eigenvector certificates (the manuscript's
"direct diagonalization"); all matrices are over `ℂ` with real
entries.
-/

open Matrix

namespace NCG

/-! ### The edge twist -/

/-- Twisted incidence for the edge twist (`ε₀₁ = -1`). -/
noncomputable def edgeTwistB : Matrix (Fin 4) (Fin 6) ℂ :=
  !![-1, -1, -1, 0, 0, 0;
     -1, 0, 0, -1, -1, 0;
     0, 1, 0, 1, 0, -1;
     0, 0, 1, 0, 1, 1]

/-- Vertex-Hodge Laplacian of the edge twist. -/
noncomputable def edgeTwistL : Matrix (Fin 4) (Fin 4) ℂ :=
  !![3, 1, -1, -1;
     1, 3, -1, -1;
     -1, -1, 3, -1;
     -1, -1, -1, 3]

/-- Certified inverse of the edge-twist Laplacian. -/
noncomputable def edgeTwistW : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1/2, 0, 1/4, 1/4;
     0, 1/2, 1/4, 1/4;
     1/4, 1/4, 5/8, 3/8;
     1/4, 1/4, 3/8, 5/8]

/-- First kernel vector of the edge twist. -/
noncomputable def edgeTwistK1 : Fin 6 → ℂ := ![0, 1, -1, -1, 1, 0]

/-- Second kernel vector of the edge twist. -/
noncomputable def edgeTwistK2 : Fin 6 → ℂ := ![0, 1, -1, 0, 0, 1]

/-- The explicit harmonic projector of the edge twist. -/
noncomputable def edgeTwistP : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 0, 0, 0, 0, 0;
     0, 3/8, -3/8, -1/8, 1/8, 2/8;
     0, -3/8, 3/8, 1/8, -1/8, -2/8;
     0, -1/8, 1/8, 3/8, -3/8, 2/8;
     0, 1/8, -1/8, -3/8, 3/8, -2/8;
     0, 2/8, -2/8, 2/8, -2/8, 4/8]

/-- The Laplacian is `B B†`. -/
lemma edgeTwistL_eq : edgeTwistB * edgeTwistBᴴ = edgeTwistL := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [edgeTwistB, edgeTwistL, Matrix.mul_apply,
      Fin.sum_univ_six, Matrix.conjTranspose_apply] <;> norm_num

/-- `W` inverts the Laplacian. -/
lemma edgeTwistW_inv : edgeTwistL * edgeTwistW = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [edgeTwistL, edgeTwistW, Matrix.mul_apply,
      Fin.sum_univ_four] <;> norm_num

/-- The kernel vectors are twisted cocycles. -/
lemma edgeTwistK_ker :
    edgeTwistB *ᵥ edgeTwistK1 = 0 ∧ edgeTwistB *ᵥ edgeTwistK2 = 0 := by
  constructor <;> funext v <;>
    fin_cases v <;>
      simp [edgeTwistB, edgeTwistK1, edgeTwistK2, Matrix.mulVec,
        dotProduct, Fin.sum_univ_six]

set_option linter.flexible false in
/-- Complete kernel parametrization: every twisted cocycle is the
displayed combination of the two basis vectors. -/
lemma edgeTwist_ker_complete (x : Fin 6 → ℂ)
    (hx : edgeTwistB *ᵥ x = 0) :
    x = x 4 • edgeTwistK1 + x 5 • edgeTwistK2 := by
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  have h2 := congrFun hx 2
  have h3 := congrFun hx 3
  simp [edgeTwistB, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
    at h0 h1 h2 h3
  have hx0 : x 0 = 0 := by
    linear_combination (-1/2 : ℂ) * h0 - (1/2 : ℂ) * h1
      - (1/2 : ℂ) * h2 - (1/2 : ℂ) * h3
  funext e
  fin_cases e
  · simpa [edgeTwistK1, edgeTwistK2] using hx0
  · simp [edgeTwistK1, edgeTwistK2]
    linear_combination h2 + h1 + hx0
  · simp [edgeTwistK1, edgeTwistK2]
    linear_combination h3
  · simp [edgeTwistK1, edgeTwistK2]
    linear_combination -h1 - hx0
  · simp [edgeTwistK1, edgeTwistK2]
  · simp [edgeTwistK1, edgeTwistK2]

/-- `dim H¹(K₄;L_n) = 2` for the edge twist. -/
noncomputable def edgeTwistKerEquiv :
    LinearMap.ker (Matrix.mulVecLin edgeTwistB) ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun x := ![x.1 4, x.1 5]
  map_add' _ _ := by
    funext i
    fin_cases i <;> simp
  map_smul' _ _ := by
    funext i
    fin_cases i <;> simp
  invFun c := ⟨c 0 • edgeTwistK1 + c 1 • edgeTwistK2, by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, edgeTwistK_ker.1,
      edgeTwistK_ker.2, smul_zero, smul_zero, add_zero]⟩
  left_inv := fun x => Subtype.ext (by
    have hker : edgeTwistB *ᵥ x.1 = 0 := by
      have h2 := x.2
      rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
    have h := edgeTwist_ker_complete x.1 hker
    simpa using h.symm)
  right_inv c := by
    funext i
    fin_cases i <;> simp [edgeTwistK1, edgeTwistK2]

lemma finrank_edgeTwist_ker :
    Module.finrank ℂ
      (LinearMap.ker (Matrix.mulVecLin edgeTwistB)) = 2 := by
  rw [edgeTwistKerEquiv.finrank_eq]
  exact Module.finrank_fin_fun ℂ

set_option linter.flexible false in
/-- Eigenvector certificates for the boxed edge-twist spectrum
`{2, 4, 3-√5, 3+√5}`. -/
lemma edgeTwist_spectrum :
    (edgeTwistL *ᵥ ![1, -1, 0, 0] = (2 : ℂ) • ![1, -1, 0, 0])
    ∧ (edgeTwistL *ᵥ ![0, 0, 1, -1] = (4 : ℂ) • ![0, 0, 1, -1])
    ∧ (edgeTwistL *ᵥ ![1, 1, (1 + (Real.sqrt 5 : ℂ)) / 2,
          (1 + (Real.sqrt 5 : ℂ)) / 2]
        = (3 - (Real.sqrt 5 : ℂ)) • ![1, 1, (1 + (Real.sqrt 5 : ℂ)) / 2,
          (1 + (Real.sqrt 5 : ℂ)) / 2])
    ∧ (edgeTwistL *ᵥ ![1, 1, (1 - (Real.sqrt 5 : ℂ)) / 2,
          (1 - (Real.sqrt 5 : ℂ)) / 2]
        = (3 + (Real.sqrt 5 : ℂ)) • ![1, 1, (1 - (Real.sqrt 5 : ℂ)) / 2,
          (1 - (Real.sqrt 5 : ℂ)) / 2]) := by
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 :=
    Real.mul_self_sqrt (by norm_num)
  have c5 : (Real.sqrt 5 : ℂ) * (Real.sqrt 5 : ℂ) = 5 := by
    exact_mod_cast congrArg Complex.ofReal h5
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext v <;>
    fin_cases v <;>
      simp [edgeTwistL, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four] <;>
      first
        | linear_combination c5 / 2
        | linear_combination -c5 / 2
        | ring

/-- The four edge-twist eigenvalues are pairwise distinct: the
exhibited eigenvectors form a complete eigenbasis. -/
lemma edgeTwist_eigen_distinct :
    ((2 : ℂ) ≠ 4) ∧ ((2 : ℂ) ≠ 3 - (Real.sqrt 5 : ℂ))
    ∧ ((2 : ℂ) ≠ 3 + (Real.sqrt 5 : ℂ))
    ∧ ((4 : ℂ) ≠ 3 - (Real.sqrt 5 : ℂ))
    ∧ ((4 : ℂ) ≠ 3 + (Real.sqrt 5 : ℂ))
    ∧ (3 - (Real.sqrt 5 : ℂ) ≠ 3 + (Real.sqrt 5 : ℂ)) := by
  have h5a : (2 : ℝ) < Real.sqrt 5 := by
    have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
    nlinarith [Real.sqrt_nonneg 5]
  have h5b : Real.sqrt 5 < 3 := by
    have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
    nlinarith [Real.sqrt_nonneg 5]
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h' : (2 : ℝ) = 3 - Real.sqrt 5 := by exact_mod_cast h
    linarith
  · intro h
    have h' : (2 : ℝ) = 3 + Real.sqrt 5 := by exact_mod_cast h
    linarith
  · intro h
    have h' : (4 : ℝ) = 3 - Real.sqrt 5 := by exact_mod_cast h
    linarith
  · intro h
    have h' : (4 : ℝ) = 3 + Real.sqrt 5 := by exact_mod_cast h
    linarith
  · intro h
    have h' : (3 : ℝ) - Real.sqrt 5 = 3 + Real.sqrt 5 := by
      exact_mod_cast h
    linarith

/-- The explicit projector realizes the boxed formula
`P_n = I - B†(BB†)⁻¹B`. -/
lemma edgeTwistP_eq :
    edgeTwistP = 1 - edgeTwistBᴴ * edgeTwistW * edgeTwistB := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [edgeTwistP, edgeTwistB, edgeTwistW, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.conjTranspose_apply] <;> norm_num

/-- The harmonic projector is a Hermitian idempotent annihilated
by the twisted incidence and fixing the kernel basis. -/
lemma edgeTwistP_projector :
    (edgeTwistP * edgeTwistP = edgeTwistP)
    ∧ (edgeTwistPᴴ = edgeTwistP)
    ∧ (edgeTwistB * edgeTwistP = 0)
    ∧ (edgeTwistP *ᵥ edgeTwistK1 = edgeTwistK1)
    ∧ (edgeTwistP *ᵥ edgeTwistK2 = edgeTwistK2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [edgeTwistP, Matrix.mul_apply, Fin.sum_univ_six] <;>
        norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [edgeTwistP, Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [edgeTwistP, edgeTwistB, Matrix.mul_apply,
        Fin.sum_univ_six] <;> norm_num
  · funext e
    fin_cases e <;>
      simp [edgeTwistP, edgeTwistK1, Matrix.mulVec, dotProduct,
        Fin.sum_univ_six] <;> norm_num
  · funext e
    fin_cases e <;>
      simp [edgeTwistP, edgeTwistK2, Matrix.mulVec, dotProduct,
        Fin.sum_univ_six] <;> norm_num

/-! ### The triangle twist -/

/-- Twisted incidence for the triangle twist
(`ε = -1` on `01, 02, 12`). -/
noncomputable def triTwistB : Matrix (Fin 4) (Fin 6) ℂ :=
  !![-1, -1, -1, 0, 0, 0;
     -1, 0, 0, -1, -1, 0;
     0, -1, 0, -1, 0, -1;
     0, 0, 1, 0, 1, 1]

/-- Vertex-Hodge Laplacian of the triangle twist. -/
noncomputable def triTwistL : Matrix (Fin 4) (Fin 4) ℂ :=
  !![3, 1, 1, -1;
     1, 3, 1, -1;
     1, 1, 3, -1;
     -1, -1, -1, 3]

/-- Certified inverse of the triangle-twist Laplacian. -/
noncomputable def triTwistW : Matrix (Fin 4) (Fin 4) ℂ :=
  !![5/12, -1/12, -1/12, 1/12;
     -1/12, 5/12, -1/12, 1/12;
     -1/12, -1/12, 5/12, 1/12;
     1/12, 1/12, 1/12, 5/12]

/-- First kernel vector of the triangle twist. -/
noncomputable def triTwistK1 : Fin 6 → ℂ := ![0, 1, -1, -1, 1, 0]

/-- Second kernel vector of the triangle twist. -/
noncomputable def triTwistK2 : Fin 6 → ℂ := ![1, 0, -1, -1, 0, 1]

/-- The explicit harmonic projector of the triangle twist. -/
noncomputable def triTwistP : Matrix (Fin 6) (Fin 6) ℂ :=
  !![2/6, -1/6, -1/6, -1/6, -1/6, 2/6;
     -1/6, 2/6, -1/6, -1/6, 2/6, -1/6;
     -1/6, -1/6, 2/6, 2/6, -1/6, -1/6;
     -1/6, -1/6, 2/6, 2/6, -1/6, -1/6;
     -1/6, 2/6, -1/6, -1/6, 2/6, -1/6;
     2/6, -1/6, -1/6, -1/6, -1/6, 2/6]

/-- The Laplacian is `B B†`. -/
lemma triTwistL_eq : triTwistB * triTwistBᴴ = triTwistL := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triTwistB, triTwistL, Matrix.mul_apply,
      Fin.sum_univ_six, Matrix.conjTranspose_apply] <;> norm_num

/-- `W` inverts the Laplacian. -/
lemma triTwistW_inv : triTwistL * triTwistW = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triTwistL, triTwistW, Matrix.mul_apply,
      Fin.sum_univ_four] <;> norm_num

/-- The kernel vectors are twisted cocycles. -/
lemma triTwistK_ker :
    triTwistB *ᵥ triTwistK1 = 0 ∧ triTwistB *ᵥ triTwistK2 = 0 := by
  constructor <;> funext v <;>
    fin_cases v <;>
      simp [triTwistB, triTwistK1, triTwistK2, Matrix.mulVec,
        dotProduct, Fin.sum_univ_six]

set_option linter.flexible false in
/-- Complete kernel parametrization for the triangle twist. -/
lemma triTwist_ker_complete (x : Fin 6 → ℂ)
    (hx : triTwistB *ᵥ x = 0) :
    x = x 4 • triTwistK1 + x 5 • triTwistK2 := by
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  have h2 := congrFun hx 2
  have h3 := congrFun hx 3
  simp [triTwistB, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
    at h0 h1 h2 h3
  have hx0 : x 0 = x 5 := by
    linear_combination (-1/2 : ℂ) * h0 - (1/2 : ℂ) * h1
      + (1/2 : ℂ) * h2 - (1/2 : ℂ) * h3
  have hx1 : x 1 = x 4 := by
    linear_combination (-1/2 : ℂ) * h0 + (1/2 : ℂ) * h1
      - (1/2 : ℂ) * h2 - (1/2 : ℂ) * h3
  funext e
  fin_cases e
  · simpa [triTwistK1, triTwistK2] using hx0
  · simpa [triTwistK1, triTwistK2] using hx1
  · simp [triTwistK1, triTwistK2]
    linear_combination h3
  · simp [triTwistK1, triTwistK2]
    linear_combination -h1 - hx0
  · simp [triTwistK1, triTwistK2]
  · simp [triTwistK1, triTwistK2]

/-- `dim H¹(K₄;L_τ) = 2` for the triangle twist. -/
noncomputable def triTwistKerEquiv :
    LinearMap.ker (Matrix.mulVecLin triTwistB) ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun x := ![x.1 4, x.1 5]
  map_add' _ _ := by
    funext i
    fin_cases i <;> simp
  map_smul' _ _ := by
    funext i
    fin_cases i <;> simp
  invFun c := ⟨c 0 • triTwistK1 + c 1 • triTwistK2, by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, triTwistK_ker.1,
      triTwistK_ker.2, smul_zero, smul_zero, add_zero]⟩
  left_inv := fun x => Subtype.ext (by
    have hker : triTwistB *ᵥ x.1 = 0 := by
      have h2 := x.2
      rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
    have h := triTwist_ker_complete x.1 hker
    simpa using h.symm)
  right_inv c := by
    funext i
    fin_cases i <;> simp [triTwistK1, triTwistK2]

lemma finrank_triTwist_ker :
    Module.finrank ℂ
      (LinearMap.ker (Matrix.mulVecLin triTwistB)) = 2 := by
  rw [triTwistKerEquiv.finrank_eq]
  exact Module.finrank_fin_fun ℂ

/-- Eigenvector certificates for the boxed triangle-twist spectrum
`{2, 2, 2, 6}`: three `λ = 2` eigenvectors and one `λ = 6`. -/
lemma triTwist_spectrum :
    (triTwistL *ᵥ ![1, -1, 0, 0] = (2 : ℂ) • ![1, -1, 0, 0])
    ∧ (triTwistL *ᵥ ![0, 1, -1, 0] = (2 : ℂ) • ![0, 1, -1, 0])
    ∧ (triTwistL *ᵥ ![1, 0, 0, 1] = (2 : ℂ) • ![1, 0, 0, 1])
    ∧ (triTwistL *ᵥ ![1, 1, 1, -1] = (6 : ℂ) • ![1, 1, 1, -1]) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext v <;>
    fin_cases v <;>
      simp [triTwistL, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four] <;> norm_num

set_option linter.flexible false in
/-- The three `λ = 2` eigenvectors are linearly independent. -/
lemma triTwist_eigen_independent (a b c : ℂ)
    (h : a • (![1, -1, 0, 0] : Fin 4 → ℂ) + b • ![0, 1, -1, 0]
      + c • ![1, 0, 0, 1] = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp at h0 h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · linear_combination h0 - h3
  · linear_combination h2
  · linear_combination h3

/-- The explicit projector realizes the boxed formula
`P_τ = I - B†(BB†)⁻¹B`. -/
lemma triTwistP_eq :
    triTwistP = 1 - triTwistBᴴ * triTwistW * triTwistB := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triTwistP, triTwistB, triTwistW, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.conjTranspose_apply] <;> norm_num

/-- The harmonic projector is a Hermitian idempotent annihilated
by the twisted incidence and fixing the kernel basis. -/
lemma triTwistP_projector :
    (triTwistP * triTwistP = triTwistP)
    ∧ (triTwistPᴴ = triTwistP)
    ∧ (triTwistB * triTwistP = 0)
    ∧ (triTwistP *ᵥ triTwistK1 = triTwistK1)
    ∧ (triTwistP *ᵥ triTwistK2 = triTwistK2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [triTwistP, Matrix.mul_apply, Fin.sum_univ_six] <;>
        norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [triTwistP, Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [triTwistP, triTwistB, Matrix.mul_apply,
        Fin.sum_univ_six] <;> norm_num
  · funext e
    fin_cases e <;>
      simp [triTwistP, triTwistK1, Matrix.mulVec, dotProduct,
        Fin.sum_univ_six] <;> norm_num
  · funext e
    fin_cases e <;>
      simp [triTwistP, triTwistK2, Matrix.mulVec, dotProduct,
        Fin.sum_univ_six] <;> norm_num

/-- `thm:twisted-carrier`: for both twist orbits the twisted
carrier is two-dimensional, with the boxed spectra certified by
eigenvectors and the boxed harmonic projector realized by the
explicit matrices. -/
theorem twisted_carrier :
    (Module.finrank ℂ
        (LinearMap.ker (Matrix.mulVecLin edgeTwistB)) = 2)
    ∧ (Module.finrank ℂ
        (LinearMap.ker (Matrix.mulVecLin triTwistB)) = 2)
    ∧ (edgeTwistP = 1 - edgeTwistBᴴ * edgeTwistW * edgeTwistB)
    ∧ (triTwistP = 1 - triTwistBᴴ * triTwistW * triTwistB)
    ∧ (edgeTwistL * edgeTwistW = 1) ∧ (triTwistL * triTwistW = 1) :=
  ⟨finrank_edgeTwist_ker, finrank_triTwist_ker, edgeTwistP_eq,
    triTwistP_eq, edgeTwistW_inv, triTwistW_inv⟩

end NCG
