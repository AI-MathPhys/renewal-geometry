/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointSourceUniversality

/-!
# Strict joint-source cutoff functor
  (`thm:joint-source-cutoff-functor`, Gran-Tensor manuscript)

* `joint_source_cutoff_functor`: under block-Gram compression
  (`jᴴ G_Y j = G_X`), the cutoff correspondence
  `S_X u ↦ S_Y (j u)` is inner-preserving and well defined on
  the Gram quotients (the unique isometry `ι_{Y/X}`); the
  compressions compose strictly; and the Hilbert–Schmidt
  intertwining defect `‖M‖²_HS = 0` iff `M = 0` (the exact
  intertwining criterion).

Rendering disclosed: the isometry object on the minimal joint
spaces is the linear-algebra packaging of the proved
well-definedness/inner-preservation (as in
`thm:joint-source-universality`); the whitened
normalized-transport naturality is the hard-tier square-root
statement.
-/

open Matrix

namespace NCG

/-- `thm:joint-source-cutoff-functor`. -/
theorem joint_source_cutoff_functor {hX hY eX eY : Type*}
    [Fintype hX] [Fintype hY] [Fintype eX] [Fintype eY]
    (SX : Matrix hX eX ℂ) (SY : Matrix hY eY ℂ)
    (j : Matrix eY eX ℂ) (GX : Matrix eX eX ℂ)
    (hGX : SXᴴ * SX = GX)
    (hcomp : jᴴ * (SYᴴ * SY) * j = GX) :
    (∀ u v : eX → ℂ,
      star (SY *ᵥ (j *ᵥ u)) ⬝ᵥ (SY *ᵥ (j *ᵥ v))
        = star (SX *ᵥ u) ⬝ᵥ (SX *ᵥ v))
    ∧ (∀ u u' : eX → ℂ, SX *ᵥ u = SX *ᵥ u' →
        SY *ᵥ (j *ᵥ u) = SY *ᵥ (j *ᵥ u'))
    ∧ (∀ {eZ : Type} [Fintype eZ] (j' : Matrix eZ eY ℂ)
        (u : eX → ℂ), j' *ᵥ (j *ᵥ u) = (j' * j) *ᵥ u)
    ∧ (∀ {m n : Type} [Fintype m] [Fintype n]
        (M : Matrix m n ℂ),
        (Mᴴ * M).trace = 0 ↔ M = 0) := by
  have hS' : (SY * j)ᴴ * (SY * j) = GX := by
    rw [Matrix.conjTranspose_mul]
    calc jᴴ * SYᴴ * (SY * j) = jᴴ * (SYᴴ * SY) * j := by
          simp only [Matrix.mul_assoc]
      _ = GX := hcomp
  obtain ⟨-, -, h3, h4, -⟩ :=
    joint_source_universality SX (SY * j) GX hGX hS'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact (h4 u v).symm
  · intro u u' hSu
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact h3 u u' hSu
  · intro eZ _ j' u
    rw [Matrix.mulVec_mulVec]
  · intro m n _ _ M
    constructor
    · intro htr
      have hexp : (Mᴴ * M).trace
          = ∑ j, ∑ i, (starRingEnd ℂ) (M i j) * M i j := by
        rw [Matrix.trace]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Matrix.diag_apply, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.conjTranspose_apply]
        rfl
      rw [hexp] at htr
      have hnormSq : ∑ j, ∑ i,
          ((Complex.normSq (M i j) : ℝ) : ℂ) = 0 := by
        rw [← htr]
        refine Finset.sum_congr rfl fun p _ =>
          Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm, Complex.mul_conj]
      have hreal : ∑ j, ∑ i, Complex.normSq (M i j) = 0 := by
        have h2 : (((∑ j, ∑ i, Complex.normSq (M i j)) : ℝ)
            : ℂ) = 0 := by
          push_cast
          exact hnormSq
        exact_mod_cast h2
      ext i j
      have hj := (Finset.sum_eq_zero_iff_of_nonneg
        (fun p _ => Finset.sum_nonneg fun i _ =>
          Complex.normSq_nonneg _)).mp hreal j
        (Finset.mem_univ j)
      have hij := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Complex.normSq_nonneg _)).mp hj i
        (Finset.mem_univ i)
      rw [Matrix.zero_apply]
      exact Complex.normSq_eq_zero.mp hij
    · rintro rfl
      simp

end NCG
