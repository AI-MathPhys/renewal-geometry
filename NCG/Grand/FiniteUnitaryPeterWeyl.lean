/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FinitePeterWeylDecomposition

import Mathlib.Analysis.InnerProductSpace.Defs
/-!
# Unitary normalization of finite Peter--Weyl blocks

Every finite-dimensional representation of a finite group is unitarizable:
averaging the standard squared norm over the group produces a positive
definite invariant norm.  This file proves that statement directly for the
Artin--Wedderburn blocks used by the finite spin-network construction.
-/

namespace NCG.FinitePeterWeyl

variable {G : Type*} [Group G] [Fintype G]

/-- The group-averaged squared norm on one irreducible block. -/
noncomputable def blockAveragedNormSq (D : MatrixBlockDecomposition G)
    (i : Fin D.count) (v : Fin (D.dimension i) → ℂ) : ℝ :=
  ∑ g : G, ∑ a : Fin (D.dimension i),
    Complex.normSq ((blockMatrix D i g).mulVec v a)

theorem blockAveragedNormSq_nonneg (D : MatrixBlockDecomposition G)
    (i : Fin D.count) (v : Fin (D.dimension i) → ℂ) :
    0 ≤ blockAveragedNormSq D i v := by
  exact Finset.sum_nonneg fun g _ =>
    Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _

/-- The averaged norm is definite, since its identity-group summand is the
standard coordinate squared norm. -/
theorem blockAveragedNormSq_eq_zero_iff
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (v : Fin (D.dimension i) → ℂ) :
    blockAveragedNormSq D i v = 0 ↔ v = 0 := by
  classical
  constructor
  · intro hzero
    have hterm : (∑ a : Fin (D.dimension i), Complex.normSq (v a)) ≤
        blockAveragedNormSq D i v := by
      rw [blockAveragedNormSq]
      have hnonneg : ∀ g : G,
          0 ≤ ∑ a : Fin (D.dimension i),
            Complex.normSq ((blockMatrix D i g).mulVec v a) :=
        fun g => Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _
      have hle := Finset.single_le_sum
        (s := (Finset.univ : Finset G))
        (f := fun g : G => ∑ a : Fin (D.dimension i),
          Complex.normSq ((blockMatrix D i g).mulVec v a))
        (fun g _ => hnonneg g)
        (Finset.mem_univ (1 : G))
      simpa [blockMatrix_one] using hle
    have hsumzero : ∑ a : Fin (D.dimension i), Complex.normSq (v a) = 0 := by
      apply le_antisymm
      · simpa [hzero] using hterm
      · exact Finset.sum_nonneg fun a _ => Complex.normSq_nonneg (v a)
    funext a
    have ha : Complex.normSq (v a) = 0 := by
      apply le_antisymm
      · have hle := Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin (D.dimension i))))
          (f := fun b => Complex.normSq (v b))
          (fun b _ => Complex.normSq_nonneg (v b))
          (Finset.mem_univ a)
        simpa [hsumzero] using hle
      · exact Complex.normSq_nonneg (v a)
    exact Complex.normSq_eq_zero.mp ha
  · rintro rfl
    simp [blockAveragedNormSq]

/-- Averaging makes every block matrix an isometry. -/
theorem blockAveragedNormSq_invariant
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (h : G) (v : Fin (D.dimension i) → ℂ) :
    blockAveragedNormSq D i ((blockMatrix D i h).mulVec v) =
      blockAveragedNormSq D i v := by
  classical
  unfold blockAveragedNormSq
  have hpoint : ∀ g : G,
      (∑ a : Fin (D.dimension i),
        Complex.normSq
          ((blockMatrix D i g).mulVec ((blockMatrix D i h).mulVec v) a)) =
      ∑ a : Fin (D.dimension i),
        Complex.normSq ((blockMatrix D i (g * h)).mulVec v a) := by
    intro g
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.mulVec_mulVec, ← blockMatrix_mul]
  simp_rw [hpoint]
  exact Fintype.sum_bijective (· * h) (Group.mulRight_bijective h)
    (fun g => ∑ a : Fin (D.dimension i),
      Complex.normSq ((blockMatrix D i (g * h)).mulVec v a))
    (fun g => ∑ a : Fin (D.dimension i),
      Complex.normSq ((blockMatrix D i g).mulVec v a))
    (fun g => rfl)

/-- The polarized group-averaged Hermitian form on one block. -/
noncomputable def blockAveragedInner (D : MatrixBlockDecomposition G)
    (i : Fin D.count) (v w : Fin (D.dimension i) → ℂ) : ℂ :=
  ∑ g : G, ∑ a : Fin (D.dimension i),
    star ((blockMatrix D i g).mulVec v a) *
      ((blockMatrix D i g).mulVec w a)

theorem blockAveragedInner_conj_symm
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (v w : Fin (D.dimension i) → ℂ) :
    blockAveragedInner D i v w = star (blockAveragedInner D i w v) := by
  classical
  simp [blockAveragedInner, mul_comm]

theorem blockAveragedInner_add_right
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (u v w : Fin (D.dimension i) → ℂ) :
    blockAveragedInner D i u (v + w) =
      blockAveragedInner D i u v + blockAveragedInner D i u w := by
  classical
  simp [blockAveragedInner, Matrix.mulVec, dotProduct, mul_add,
    Finset.sum_add_distrib]

theorem blockAveragedInner_smul_right
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (c : ℂ) (v w : Fin (D.dimension i) → ℂ) :
    blockAveragedInner D i v (c • w) =
      c * blockAveragedInner D i v w := by
  classical
  simp [blockAveragedInner, Matrix.mulVec, dotProduct, Finset.mul_sum,
    mul_left_comm]

theorem blockAveragedInner_self (D : MatrixBlockDecomposition G)
    (i : Fin D.count) (v : Fin (D.dimension i) → ℂ) :
    blockAveragedInner D i v v = blockAveragedNormSq D i v := by
  classical
  simp only [blockAveragedInner, blockAveragedNormSq]
  push_cast
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro a _
  exact Complex.normSq_eq_conj_mul_self.symm

/-- The averaged Hermitian form is invariant under every group element. -/
theorem blockAveragedInner_invariant
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (h : G) (v w : Fin (D.dimension i) → ℂ) :
    blockAveragedInner D i ((blockMatrix D i h).mulVec v)
        ((blockMatrix D i h).mulVec w) =
      blockAveragedInner D i v w := by
  classical
  unfold blockAveragedInner
  have hpoint : ∀ g : G,
      (∑ a : Fin (D.dimension i),
        star ((blockMatrix D i g).mulVec
          ((blockMatrix D i h).mulVec v) a) *
        ((blockMatrix D i g).mulVec
          ((blockMatrix D i h).mulVec w) a)) =
      ∑ a : Fin (D.dimension i),
        star ((blockMatrix D i (g * h)).mulVec v a) *
          ((blockMatrix D i (g * h)).mulVec w a) := by
    intro g
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← blockMatrix_mul]
  simp_rw [hpoint]
  exact Fintype.sum_bijective (· * h) (Group.mulRight_bijective h)
    (fun g => ∑ a : Fin (D.dimension i),
      star ((blockMatrix D i (g * h)).mulVec v a) *
        ((blockMatrix D i (g * h)).mulVec w a))
    (fun g => ∑ a : Fin (D.dimension i),
      star ((blockMatrix D i g).mulVec v a) *
        ((blockMatrix D i g).mulVec w a))
    (fun g => rfl)

/-- Positivity is strict: the averaged Hermitian square vanishes only at
the zero vector. -/
theorem blockAveragedInner_self_eq_zero_iff
    (D : MatrixBlockDecomposition G) (i : Fin D.count)
    (v : Fin (D.dimension i) → ℂ) :
    blockAveragedInner D i v v = 0 ↔ v = 0 := by
  rw [blockAveragedInner_self]
  norm_cast
  exact blockAveragedNormSq_eq_zero_iff D i v

/-- The averaged form packaged as Mathlib's positive-definite inner-product
core.  It is kept as explicit data, so it does not conflict with the standard
coordinate norm on the underlying function type. -/
@[instance_reducible] noncomputable def blockInnerProductCore
    (D : MatrixBlockDecomposition G) (i : Fin D.count) :
    InnerProductSpace.Core ℂ (Fin (D.dimension i) → ℂ) where
  inner := blockAveragedInner D i
  conj_inner_symm x y := (blockAveragedInner_conj_symm D i x y).symm
  re_inner_nonneg x := by
    rw [blockAveragedInner_self]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    exact blockAveragedNormSq_nonneg D i x
  add_left x y z := by
    calc
      blockAveragedInner D i (x + y) z =
          star (blockAveragedInner D i z (x + y)) :=
        blockAveragedInner_conj_symm D i (x + y) z
      _ = star (blockAveragedInner D i z x +
          blockAveragedInner D i z y) := by
        rw [blockAveragedInner_add_right]
      _ = star (blockAveragedInner D i z x) +
          star (blockAveragedInner D i z y) := by simp
      _ = blockAveragedInner D i x z +
          blockAveragedInner D i y z := by
        rw [← blockAveragedInner_conj_symm D i x z,
          ← blockAveragedInner_conj_symm D i y z]
  smul_left x y c := by
    calc
      blockAveragedInner D i (c • x) y =
          star (blockAveragedInner D i y (c • x)) :=
        blockAveragedInner_conj_symm D i (c • x) y
      _ = star (c * blockAveragedInner D i y x) := by
        rw [blockAveragedInner_smul_right]
      _ = star c * star (blockAveragedInner D i y x) := by simp
      _ = star c * blockAveragedInner D i x y := by
        rw [← blockAveragedInner_conj_symm D i x y]
  definite x hx := (blockAveragedInner_self_eq_zero_iff D i x).mp hx

/-- Complete unitary certificate for the algebraic block: the displayed form is
Hermitian, additive and complex-linear in its second argument, positive
definite, and preserved by the group action. -/
theorem block_is_unitary_for_averagedInner
    (D : MatrixBlockDecomposition G) (i : Fin D.count) :
    (∀ v w, blockAveragedInner D i v w =
      star (blockAveragedInner D i w v)) ∧
    (∀ u v w, blockAveragedInner D i u (v + w) =
      blockAveragedInner D i u v + blockAveragedInner D i u w) ∧
    (∀ c v w, blockAveragedInner D i v (c • w) =
      c * blockAveragedInner D i v w) ∧
    (∀ v, blockAveragedInner D i v v = 0 ↔ v = 0) ∧
    (∀ h v w,
      blockAveragedInner D i ((blockMatrix D i h).mulVec v)
          ((blockMatrix D i h).mulVec w) =
        blockAveragedInner D i v w) :=
  ⟨blockAveragedInner_conj_symm D i,
    blockAveragedInner_add_right D i,
    blockAveragedInner_smul_right D i,
    blockAveragedInner_self_eq_zero_iff D i,
    blockAveragedInner_invariant D i⟩

/-- Each Artin--Wedderburn block is a unitarizable irreducible finite-group
representation: it carries an explicit positive-definite invariant norm. -/
theorem block_is_unitarizable (D : MatrixBlockDecomposition G)
    (i : Fin D.count) :
    (∀ v, 0 ≤ blockAveragedNormSq D i v) ∧
    (∀ v, blockAveragedNormSq D i v = 0 ↔ v = 0) ∧
    (∀ h v, blockAveragedNormSq D i ((blockMatrix D i h).mulVec v) =
      blockAveragedNormSq D i v) :=
  ⟨blockAveragedNormSq_nonneg D i,
    blockAveragedNormSq_eq_zero_iff D i,
    blockAveragedNormSq_invariant D i⟩

end NCG.FinitePeterWeyl
