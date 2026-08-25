/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The linear span of the permutation matrices

Machinery for `thm:SM-active-residual-algebra`: the linear span of the permutation
matrices over `ℂ` is exactly the space of matrices whose row sums and column sums
all agree (`span_permMatrix`).  Since the permutation matrices form a monoid under
multiplication, this span is simultaneously the generated algebra — the external
Burnside algebra of the permutation representation.

The proof is fully explicit:

* `zero_sum_decomposition`: a matrix with vanishing row and column sums is the
  explicit combination `∑ Y i j • D i j i₀ j₀` of elementary difference patterns;
* `dmat_mem`: each pattern `E_ij - E_ij₀ - E_i₀j + E_i₀j₀` is the difference of two
  explicit permutation matrices;
* subtracting a scaled identity permutation matrix reduces any equal-sum matrix to
  the zero-sum case.
-/

open Finset Matrix

namespace NCG
namespace PermSpan

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The submodule of matrices whose row sums and column sums all agree. -/
def equalSum (n : Type*) [Fintype n] [DecidableEq n] : Submodule ℂ (Matrix n n ℂ) where
  carrier := {X | ∀ i j, ∑ k, X i k = ∑ k, X k j}
  zero_mem' := fun i j => by simp
  add_mem' := fun {X Y} hX hY i j => by
    simp only [Matrix.add_apply, Finset.sum_add_distrib]
    rw [hX i j, hY i j]
  smul_mem' := fun c {X} hX i j => by
    simp only [Matrix.smul_apply, ← Finset.smul_sum]
    rw [hX i j]

theorem mem_equalSum {X : Matrix n n ℂ} :
    X ∈ equalSum n ↔ ∀ i j, ∑ k, X i k = ∑ k, X k j := Iff.rfl

omit [Fintype n] in
/-- Entry formula for the permutation matrix. -/
theorem permMatrix_entry (σ : Equiv.Perm n) (a b : n) :
    σ.permMatrix ℂ a b = if σ a = b then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, PEquiv.toMatrix_apply,
    Option.mem_def, eq_comm]

theorem rowSum_permMatrix (σ : Equiv.Perm n) (i : n) :
    ∑ k, σ.permMatrix ℂ i k = 1 := by
  rw [Finset.sum_congr rfl fun k _ => permMatrix_entry σ i k,
    Finset.sum_ite_eq Finset.univ (σ i) fun _ => (1 : ℂ),
    if_pos (Finset.mem_univ _)]

theorem colSum_permMatrix (σ : Equiv.Perm n) (j : n) :
    ∑ k, σ.permMatrix ℂ k j = 1 := by
  have hc : ∀ k : n, σ.permMatrix ℂ k j = if k = σ.symm j then 1 else 0 := by
    intro k
    rw [permMatrix_entry]
    exact if_congr (Equiv.apply_eq_iff_eq_symm_apply σ) rfl rfl
  rw [Finset.sum_congr rfl fun k _ => hc k,
    Finset.sum_ite_eq' Finset.univ (σ.symm j) fun _ => (1 : ℂ),
    if_pos (Finset.mem_univ _)]

theorem permMatrix_mem_equalSum (σ : Equiv.Perm n) : σ.permMatrix ℂ ∈ equalSum n := by
  intro i j
  rw [rowSum_permMatrix, colSum_permMatrix]

/-- The elementary difference pattern `E_ij - E_ij₀ - E_i₀j + E_i₀j₀`. -/
def dmat (i j i₀ j₀ : n) : Matrix n n ℂ :=
  Matrix.single i j 1 - Matrix.single i j₀ 1 - Matrix.single i₀ j 1
    + Matrix.single i₀ j₀ 1

/-- A matrix with vanishing row and column sums is the explicit combination of its
entries against the difference patterns anchored at `(i₀, j₀)`. -/
theorem zero_sum_decomposition (i₀ j₀ : n) (Y : Matrix n n ℂ)
    (hrow : ∀ i, ∑ k, Y i k = 0) (hcol : ∀ j, ∑ k, Y k j = 0) :
    Y = ∑ i ∈ Finset.univ.erase i₀, ∑ j ∈ Finset.univ.erase j₀,
      Y i j • dmat i j i₀ j₀ := by
  have hrowE : ∀ i, ∑ j ∈ Finset.univ.erase j₀, Y i j = -Y i j₀ := by
    intro i
    have h := Finset.sum_erase_add Finset.univ (Y i) (Finset.mem_univ j₀)
    rw [hrow i] at h
    linear_combination h
  have hcolE : ∀ j, ∑ i ∈ Finset.univ.erase i₀, Y i j = -Y i₀ j := by
    intro j
    have h := Finset.sum_erase_add Finset.univ (fun k => Y k j) (Finset.mem_univ i₀)
    rw [hcol j] at h
    linear_combination h
  ext a b
  rw [Matrix.sum_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, dmat, Matrix.add_apply,
    Matrix.sub_apply, Matrix.single_apply, smul_eq_mul]
  by_cases ha : a = i₀
  · by_cases hb : b = j₀
    · subst ha
      subst hb
      have hsummand : ∀ i ∈ Finset.univ.erase a, ∀ j ∈ Finset.univ.erase b,
          Y i j * ((if i = a ∧ j = b then (1 : ℂ) else 0)
            - (if i = a ∧ b = b then 1 else 0)
            - (if a = a ∧ j = b then 1 else 0)
            + if a = a ∧ b = b then 1 else 0) = Y i j := by
        intro i hi j hj
        rw [if_neg (fun h => (Finset.mem_erase.mp hi).1 h.1),
          if_neg (fun h => (Finset.mem_erase.mp hi).1 h.1),
          if_neg (fun h => (Finset.mem_erase.mp hj).1 h.2),
          if_pos ⟨rfl, rfl⟩]
        ring
      rw [Finset.sum_congr rfl fun i hi =>
        Finset.sum_congr rfl fun j hj => hsummand i hi j hj]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ.erase a) => hrowE i]
      rw [Finset.sum_neg_distrib, hcolE b, neg_neg]
    · subst ha
      have hsummand : ∀ i ∈ Finset.univ.erase a, ∀ j ∈ Finset.univ.erase j₀,
          Y i j * ((if i = a ∧ j = b then (1 : ℂ) else 0)
            - (if i = a ∧ j₀ = b then 1 else 0)
            - (if a = a ∧ j = b then 1 else 0)
            + if a = a ∧ j₀ = b then 1 else 0)
          = if j = b then -Y i j else 0 := by
        intro i hi j hj
        rw [if_neg (show ¬(i = a ∧ j = b) from fun h => (Finset.mem_erase.mp hi).1 h.1),
          if_neg (show ¬(i = a ∧ j₀ = b) from fun h => hb h.2.symm),
          if_neg (show ¬(a = a ∧ j₀ = b) from fun h => hb h.2.symm)]
        by_cases hjb : j = b
        · rw [if_pos (show a = a ∧ j = b from ⟨rfl, hjb⟩), if_pos hjb]
          ring
        · rw [if_neg (show ¬(a = a ∧ j = b) from fun h => hjb h.2), if_neg hjb]
          ring
      rw [Finset.sum_congr rfl fun i hi =>
        Finset.sum_congr rfl fun j hj => hsummand i hi j hj]
      have hin : ∀ i ∈ Finset.univ.erase a,
          ∑ j ∈ Finset.univ.erase j₀, (if j = b then -Y i j else 0) = -Y i b := by
        intro i _
        rw [Finset.sum_ite_eq' (Finset.univ.erase j₀) b fun j => -Y i j,
          if_pos (Finset.mem_erase.mpr ⟨fun h => hb h, Finset.mem_univ b⟩)]
      rw [Finset.sum_congr rfl hin, Finset.sum_neg_distrib, hcolE b, neg_neg]
  · by_cases hb : b = j₀
    · subst hb
      have hsummand : ∀ i ∈ Finset.univ.erase i₀, ∀ j ∈ Finset.univ.erase b,
          Y i j * ((if i = a ∧ j = b then (1 : ℂ) else 0)
            - (if i = a ∧ b = b then 1 else 0)
            - (if i₀ = a ∧ j = b then 1 else 0)
            + if i₀ = a ∧ b = b then 1 else 0)
          = if i = a then -Y i j else 0 := by
        intro i hi j hj
        rw [if_neg (show ¬(i = a ∧ j = b) from fun h => (Finset.mem_erase.mp hj).1 h.2),
          if_neg (show ¬(i₀ = a ∧ j = b) from fun h => ha h.1.symm),
          if_neg (show ¬(i₀ = a ∧ b = b) from fun h => ha h.1.symm)]
        by_cases hia : i = a
        · rw [if_pos (show i = a ∧ b = b from ⟨hia, rfl⟩), if_pos hia]
          ring
        · rw [if_neg (show ¬(i = a ∧ b = b) from fun h => hia h.1), if_neg hia]
          ring
      rw [Finset.sum_congr rfl fun i hi =>
        Finset.sum_congr rfl fun j hj => hsummand i hi j hj]
      have hin : ∀ i ∈ Finset.univ.erase i₀,
          ∑ j ∈ Finset.univ.erase b, (if i = a then -Y i j else 0)
            = if i = a then Y i b else 0 := by
        intro i _
        by_cases hia : i = a
        · rw [if_pos hia, Finset.sum_congr rfl fun j _ => if_pos hia,
            Finset.sum_neg_distrib, hrowE i, neg_neg]
        · rw [if_neg hia]
          exact Finset.sum_eq_zero fun j _ => if_neg hia
      rw [Finset.sum_congr rfl hin,
        Finset.sum_ite_eq' (Finset.univ.erase i₀) a fun i => Y i b,
        if_pos (Finset.mem_erase.mpr ⟨fun h => ha h, Finset.mem_univ a⟩)]
    · have hsummand : ∀ i ∈ Finset.univ.erase i₀, ∀ j ∈ Finset.univ.erase j₀,
          Y i j * ((if i = a ∧ j = b then (1 : ℂ) else 0)
            - (if i = a ∧ j₀ = b then 1 else 0)
            - (if i₀ = a ∧ j = b then 1 else 0)
            + if i₀ = a ∧ j₀ = b then 1 else 0)
          = if i = a ∧ j = b then Y a b else 0 := by
        intro i hi j hj
        rw [if_neg (show ¬(i = a ∧ j₀ = b) from fun h => hb h.2.symm),
          if_neg (show ¬(i₀ = a ∧ j = b) from fun h => ha h.1.symm),
          if_neg (show ¬(i₀ = a ∧ j₀ = b) from fun h => ha h.1.symm)]
        by_cases hij : i = a ∧ j = b
        · rw [if_pos hij, if_pos hij, hij.1, hij.2]
          ring
        · rw [if_neg hij, if_neg hij]
          ring
      rw [Finset.sum_congr rfl fun i hi =>
        Finset.sum_congr rfl fun j hj => hsummand i hi j hj]
      have hin : ∀ i ∈ Finset.univ.erase i₀,
          ∑ j ∈ Finset.univ.erase j₀, (if i = a ∧ j = b then Y a b else 0)
            = if i = a then Y a b else 0 := by
        intro i _
        by_cases hia : i = a
        · rw [if_pos hia]
          rw [Finset.sum_congr rfl fun j _ =>
            if_congr (show (i = a ∧ j = b) ↔ (j = b) from
              ⟨fun h => h.2, fun h => ⟨hia, h⟩⟩) rfl rfl]
          rw [Finset.sum_ite_eq' (Finset.univ.erase j₀) b fun _ => Y a b,
            if_pos (Finset.mem_erase.mpr ⟨fun h => hb h, Finset.mem_univ b⟩)]
        · rw [if_neg hia]
          exact Finset.sum_eq_zero fun j _ => if_neg (fun h => hia h.1)
      rw [Finset.sum_congr rfl hin,
        Finset.sum_ite_eq' (Finset.univ.erase i₀) a fun _ => Y a b,
        if_pos (Finset.mem_erase.mpr ⟨fun h => ha h, Finset.mem_univ a⟩)]

omit [Fintype n] in
/-- Each difference pattern is the difference of two explicit permutation
matrices. -/
theorem dmat_mem (i j i₀ j₀ : n) (hi : i ≠ i₀) (hj : j ≠ j₀) :
    dmat i j i₀ j₀ ∈
      Submodule.span ℂ (Set.range fun σ : Equiv.Perm n => σ.permMatrix ℂ) := by
  set τ : Equiv.Perm n := Equiv.swap i₀ j₀ with hτ
  have hτi₀ : τ i₀ = j₀ := Equiv.swap_apply_left i₀ j₀
  have hτine : τ i ≠ j₀ := by
    intro hcon
    exact hi (τ.injective (hcon.trans hτi₀.symm))
  set σ : Equiv.Perm n := τ.trans (Equiv.swap (τ i) j) with hσ
  have hσi : σ i = j := by
    rw [hσ, Equiv.trans_apply, Equiv.swap_apply_left]
  have hσi₀ : σ i₀ = j₀ := by
    rw [hσ, Equiv.trans_apply, hτi₀,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hτine) (Ne.symm hj)]
  set β : Equiv.Perm n := (Equiv.swap i i₀).trans σ with hβ
  have hβi : β i = j₀ := by
    rw [hβ, Equiv.trans_apply, Equiv.swap_apply_left, hσi₀]
  have hβi₀ : β i₀ = j := by
    rw [hβ, Equiv.trans_apply, Equiv.swap_apply_right, hσi]
  have hβagree : ∀ a, a ≠ i → a ≠ i₀ → β a = σ a := by
    intro a hai hai₀
    rw [hβ, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hai hai₀]
  have hD : dmat i j i₀ j₀ = σ.permMatrix ℂ - β.permMatrix ℂ := by
    ext a b
    rw [Matrix.sub_apply, permMatrix_entry, permMatrix_entry, dmat,
      Matrix.add_apply, Matrix.sub_apply, Matrix.sub_apply,
      Matrix.single_apply, Matrix.single_apply, Matrix.single_apply,
      Matrix.single_apply]
    by_cases hai : a = i
    · subst hai
      rw [hσi, hβi]
      simp [Ne.symm hi]
    · by_cases hai₀ : a = i₀
      · subst hai₀
        rw [hσi₀, hβi₀,
          if_neg (show ¬(i = a ∧ j = b) from fun h => hi h.1),
          if_neg (show ¬(i = a ∧ j₀ = b) from fun h => hi h.1)]
        simp only [true_and]
        ring
      · rw [hβagree a hai hai₀]
        simp [Ne.symm hai, Ne.symm hai₀]
  rw [hD]
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨σ, rfl⟩)
    (Submodule.subset_span ⟨β, rfl⟩)

/-- **The permutation-span theorem**: the linear span of the permutation matrices
is exactly the equal-row/column-sum space. -/
theorem span_permMatrix :
    Submodule.span ℂ (Set.range fun σ : Equiv.Perm n => σ.permMatrix ℂ)
      = equalSum n := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨σ, rfl⟩
    exact permMatrix_mem_equalSum σ
  · intro X hX
    rcases isEmpty_or_nonempty n with hn | hn
    · have hX0 : X = 0 := by
        ext a b
        exact (IsEmpty.false a).elim
      rw [hX0]
      exact Submodule.zero_mem _
    · obtain ⟨i₀⟩ := hn
      set s : ℂ := ∑ k, X i₀ k with hs
      have hrowX : ∀ i, ∑ k, X i k = s := by
        intro i
        rw [hs, hX i i₀, ← hX i₀ i₀]
      have hcolX : ∀ j, ∑ k, X k j = s := by
        intro j
        rw [hs, ← hX i₀ j]
      set Y := X - s • (1 : Equiv.Perm n).permMatrix ℂ with hY
      have hYrow : ∀ i, ∑ k, Y i k = 0 := by
        intro i
        rw [hY]
        simp only [Matrix.sub_apply, Matrix.smul_apply, Finset.sum_sub_distrib,
          ← Finset.smul_sum]
        rw [hrowX i, rowSum_permMatrix, smul_eq_mul, mul_one, sub_self]
      have hYcol : ∀ j, ∑ k, Y k j = 0 := by
        intro j
        rw [hY]
        simp only [Matrix.sub_apply, Matrix.smul_apply, Finset.sum_sub_distrib,
          ← Finset.smul_sum]
        rw [hcolX j, colSum_permMatrix, smul_eq_mul, mul_one, sub_self]
      have hXsplit : X = s • (1 : Equiv.Perm n).permMatrix ℂ + Y := by
        rw [hY]
        abel
      rw [hXsplit]
      refine Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)) ?_
      rw [zero_sum_decomposition i₀ i₀ Y hYrow hYcol]
      refine Submodule.sum_mem _ fun i hi => Submodule.sum_mem _ fun j hj => ?_
      exact Submodule.smul_mem _ _
        (dmat_mem i j i₀ i₀ (Finset.mem_erase.mp hi).1 (Finset.mem_erase.mp hj).1)

end PermSpan
end NCG
