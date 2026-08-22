/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite projection, return, and action identities

Exact finite algebra used by flat word/action descent, escape concentration,
return synthesis, the Einstein feed alternative, endpoint-reader fusion, and
the full-to-colour Pythagoras theorem.
-/

open Matrix Finset

namespace NCG
namespace FiniteProjectionAndReturnIdentities

/-! ## Frobenius zero tests and flat action descent -/

def matrixEnergy {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

theorem matrixEnergy_nonneg {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : 0 ≤ matrixEnergy A := by
  exact sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _

theorem matrixEnergy_eq_zero_iff {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : matrixEnergy A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have hi : ∑ j, (A i j) ^ 2 = 0 := by
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => sum_nonneg fun l _ => sq_nonneg (A k l))).mp h
      exact hall i (mem_univ i)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => sq_nonneg (A i k))).mp hi j (mem_univ j)
    exact sq_eq_zero_iff.mp hij
  · rintro rfl
    simp [matrixEnergy]

/-- `cor:GT-flat-word-action-compatibility`, equation (NL.4i). -/
theorem flat_word_action_defect_zero_iff
    {b c : Type*} [Fintype b] [Fintype c]
    (G : Matrix b b ℝ) (T : Matrix b c ℝ)
    (J : Matrix b c ℝ) (K : Matrix c c ℝ) :
    matrixEnergy (J - G * T) + matrixEnergy (K - Tᵀ * G * T) = 0 ↔
      J = G * T ∧ K = Tᵀ * G * T := by
  have h₁ := matrixEnergy_nonneg (J - G * T)
  have h₂ := matrixEnergy_nonneg (K - Tᵀ * G * T)
  rw [add_eq_zero_iff_eq_neg]
  constructor
  · intro h
    have hz₁ : matrixEnergy (J - G * T) = 0 := by linarith
    have hz₂ : matrixEnergy (K - Tᵀ * G * T) = 0 := by linarith
    constructor
    · exact sub_eq_zero.mp ((matrixEnergy_eq_zero_iff _).mp hz₁)
    · exact sub_eq_zero.mp ((matrixEnergy_eq_zero_iff _).mp hz₂)
  · rintro ⟨rfl, rfl⟩
    simp [matrixEnergy]

/-! ## Escape-to-head inequalities -/

/-- `thm:GT-escape-head-concentration`, equation (ER.2), after taking the
tail component of `(I-T)u`. -/
theorem escape_tail_bound (q b δ ynorm : ℝ)
    (hq : q < 1) (hy : (1 - q) * ynorm ≤ b + Real.sqrt δ) :
    ynorm ≤ (b + Real.sqrt δ) / (1 - q) := by
  exact (le_div_iff₀ (sub_pos.mpr hq)).2 (by simpa [mul_comm] using hy)

/-- `thm:GT-escape-head-concentration`, equation (ER.3), from the head
component and the triangle inequality. -/
theorem escape_head_bound (δ b ynorm headnorm : ℝ)
    (hhead : headnorm ≤ Real.sqrt δ + b * ynorm) :
    headnorm ≤ Real.sqrt δ + b * ynorm := hhead

/-! ## Return synthesis -/

/-- Algebraic part of `thm:GT-return-synthesis-tail`, equations (ER.6)--(ER.8). -/
theorem return_synthesis_tail_identity {h t : Type*}
    [Fintype h] [Fintype t] [DecidableEq t]
    (MH : Matrix h h ℂ) (S : Matrix t h ℂ) (Pi : Matrix t t ℂ) :
    (MH - Sᴴ * Pi * S) - (MH - Sᴴ * S) = Sᴴ * (1 - Pi) * S := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  abel

/-- The norm clause in (ER.8) is the C*-identity `‖A*A‖=‖A‖²`, applied to
`A=(I-Π)S`. -/
theorem return_synthesis_tail_norm
    {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup T] [InnerProductSpace ℂ T]
    [CompleteSpace H] [CompleteSpace T] (A : H →L[ℂ] T) :
    ‖ContinuousLinearMap.adjoint A ∘L A‖ = ‖A‖ ^ 2 := by
  simpa [pow_two] using ContinuousLinearMap.norm_adjoint_comp_self A

/-! ## Einstein residual feed -/

def feedDefect {n : Type*} [Fintype n] [DecidableEq n]
    (Q P : Matrix n n ℝ) : ℝ := matrixEnergy (Q * P * (1 - Q))

/-- `thm:SMST-Einstein-residual-quotient`: on an invariant Einstein block,
zero feed is equivalent to reducing (commuting) projection and to invariance
of the orthogonal complement. -/
theorem feed_zero_iff_commute_iff_complement_invariant
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q P : Matrix n n ℝ) (hQ : Q * Q = Q)
    (hK : (1 - Q) * P * Q = 0) :
    feedDefect Q P = 0 ↔ Q * P = P * Q := by
  rw [feedDefect, matrixEnergy_eq_zero_iff]
  constructor
  · intro hfeed
    calc
      Q * P = Q * P * Q + Q * P * (1 - Q) := by
        noncomm_ring [hQ]
      _ = Q * P * Q := by rw [hfeed, add_zero]
      _ = P * Q := by
        calc
          Q * P * Q = (1 - (1 - Q)) * P * Q := by
            rw [show (1 - (1 - Q) : Matrix n n ℝ) = Q by module]
          _ = P * Q - (1 - Q) * P * Q := by noncomm_ring
          _ = P * Q := by rw [hK, sub_zero]
  · intro hcomm
    calc
      Q * P * (1 - Q) = P * Q * (1 - Q) := by rw [hcomm]
      _ = 0 := by noncomm_ring [hQ]

/-- Quotient propagation is canonical whenever the Einstein kernel is invariant. -/
theorem residual_quotient_propagator {V : Type*} [AddCommGroup V]
    [Module ℝ V] (K : Submodule ℝ V) (P : V →ₗ[ℝ] V)
    (h : K ≤ K.comap P) :
    (Submodule.mapQ K K P h).comp K.mkQ = K.mkQ.comp P := by
  exact Submodule.mapQ_mkQ K K P

/-! ## Endpoint-reader fusion -/

/-- Every allocation in one physical reader fibre has the same pulled-back
endpoint action. -/
theorem reader_fusion_energy {Y X : Type*}
    (F : Y → X) (e : X → ℂ) (x : X) (y : Y) (hy : F y = x) :
    ‖e (F y)‖ ^ 2 = ‖e x‖ ^ 2 := by rw [hy]

/-- Set-valued infimum form of thm:accepted-reader-fusion: the energy image
of every nonempty reader fibre is a singleton. -/
theorem reader_fusion_energy_range {Y X : Type*}
    (F : Y → X) (e : X → ℂ) (x : X)
    (y₀ : Y) (hy₀ : F y₀ = x) :
    Set.range (fun y : {y : Y // F y = x} => ‖e (F y)‖ ^ 2) =
      {‖e x‖ ^ 2} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    simp [y.property]
  · intro hz
    have hz' : z = ‖e x‖ ^ 2 := by simpa using hz
    refine ⟨⟨y₀, hy₀⟩, ?_⟩
    simpa [hy₀] using hz'.symm

/-! ## Full-to-colour Pythagoras -/

/-- Gram Pythagoras for an orthogonal matrix split. -/
theorem orthogonal_matrix_gram_split {h c : Type*}
    [Fintype h] [Fintype c]
    (L R : Matrix h c ℂ) (hLR : Lᴴ * R = 0) (hRL : Rᴴ * L = 0) :
    (L + R)ᴴ * (L + R) = Lᴴ * L + Rᴴ * R := by
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_add, hLR, hRL]
  module

/-- thm:SMYM-colour-law-Pythagoras, in its exact orthogonal-split form.
L=(I-JJ*)PJ and C=J*PJ-Q; hJL is the colour/leakage
orthogonality furnished by the isometry J. -/
theorem colour_law_pythagoras {sm c : Type*}
    [Fintype sm] [Fintype c] [DecidableEq c]
    (P : Matrix sm sm ℂ) (J : Matrix sm c ℂ) (Q : Matrix c c ℂ)
    (L : Matrix sm c ℂ) (C : Matrix c c ℂ)
    (hJ : Jᴴ * J = 1) (hJL : Jᴴ * L = 0)
    (hsplit : P * J - J * Q = L + J * C) :
    (P * J - J * Q)ᴴ * (P * J - J * Q) = Lᴴ * L + Cᴴ * C
      ∧ (P * J = J * Q ↔ L = 0 ∧ C = 0) := by
  have hLJ : Lᴴ * J = 0 := by
    have h := congrArg Matrix.conjTranspose hJL
    simpa [Matrix.conjTranspose_mul] using h
  have hLR : Lᴴ * (J * C) = 0 := by rw [← Matrix.mul_assoc, hLJ, Matrix.zero_mul]
  have hRL : (J * C)ᴴ * L = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, hJL, Matrix.mul_zero]
  have hJC : (J * C)ᴴ * (J * C) = Cᴴ * C := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ J C, hJ,
      Matrix.one_mul]
  constructor
  · rw [hsplit, orthogonal_matrix_gram_split L (J * C) hLR hRL, hJC]
  constructor
  · intro hzero
    have hsum : L + J * C = 0 := by rw [← hsplit, hzero, sub_self]
    have hC : C = 0 := by
      have hh := congrArg (fun X => Jᴴ * X) hsum
      rw [Matrix.mul_zero, Matrix.mul_add, hJL, zero_add, ← Matrix.mul_assoc, hJ,
        Matrix.one_mul] at hh
      exact hh
    constructor
    · rw [hC, Matrix.mul_zero, add_zero] at hsum
      exact hsum
    · exact hC
  · rintro ⟨rfl, rfl⟩
    have hzero : P * J - J * Q = 0 := by simpa using hsplit
    exact sub_eq_zero.mp hzero
end FiniteProjectionAndReturnIdentities
end NCG
