/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Perron–Frobenius existence for positive matrices

Mathlib has no Perron–Frobenius theorem; this file proves the
**existence half** for entrywise positive matrices, by the
Collatz–Wielandt variational argument — no fixed-point theorem is
used:

* `cwSet` — the compact set of pairs `(λ, x)` with `x` in the
  probability simplex and `λ x ≤ A x` entrywise
  (`cwSet_isCompact`), containing a pair with strictly positive `λ`
  (`cwSet_witness`);
* `perron_exists` — a strictly positive eigenvector with a strictly
  positive eigenvalue: the pair maximizing `λ` over `cwSet` must
  satisfy `A x = λ x` exactly, since otherwise applying the strictly
  positive matrix once more strictly improves `λ`;
* `perron_exists_left` — the left (row) eigenvector, by transposing;
* `perron_left_right_eq` — a left and a right eigenvalue with
  positive eigenvectors always agree (pair the eigenvectors).

This supplies the Doob data of `constr:pressure-law`
(`manuscripts/renewal_emergence/renewal_emergence.tex`).
-/

namespace NCG

open Matrix Set

variable {n : ℕ} [NeZero n]

/-- The Collatz–Wielandt set of a matrix: pairs `(λ, x)` with `x`
in the probability simplex and `λ x ≤ A x` entrywise. -/
def cwSet (A : Matrix (Fin n) (Fin n) ℝ) : Set (ℝ × (Fin n → ℝ)) :=
  {p | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ (∑ i, p.2 i = 1)
    ∧ ∀ i, p.1 * p.2 i ≤ A.mulVec p.2 i}

theorem cwSet_witness {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 < A i j) :
    ∃ lam₀ x₀, (lam₀, x₀) ∈ cwSet A ∧ 0 < lam₀ := by
  classical
  set m : ℝ := Finset.univ.inf' Finset.univ_nonempty
    (fun p : Fin n × Fin n => A p.1 p.2) with hm
  have hmpos : 0 < m := by
    rw [hm, Finset.lt_inf'_iff]
    intro p _
    exact hA p.1 p.2
  have hmle : ∀ i j, m ≤ A i j := by
    intro i j
    rw [hm]
    exact Finset.inf'_le _ (Finset.mem_univ (i, j))
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne n
  have hn1 : (1 : ℝ) ≤ n := by
    have h0 := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    exact_mod_cast h0
  refine ⟨m, fun _ => (n : ℝ)⁻¹, ⟨hmpos.le, ?_, ?_, ?_⟩, hmpos⟩
  · intro i
    positivity
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  · intro i
    have h5 : m * (n : ℝ)⁻¹ ≤ m := by
      have h6 : (n : ℝ)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        right
        exact hn1
      calc m * (n : ℝ)⁻¹ ≤ m * 1 :=
          mul_le_mul_of_nonneg_left h6 hmpos.le
        _ = m := mul_one m
    have h7 : m ≤ A.mulVec (fun _ => (n : ℝ)⁻¹) i := by
      rw [Matrix.mulVec, dotProduct]
      have h8 : m = ∑ _j : Fin n, m * (n : ℝ)⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        field_simp
      rw [h8]
      refine Finset.sum_le_sum fun j _ => ?_
      exact mul_le_mul_of_nonneg_right (hmle i j) (by positivity)
    linarith

theorem cwSet_isClosed (A : Matrix (Fin n) (Fin n) ℝ) :
    IsClosed (cwSet A) := by
  have hcoord : ∀ i : Fin n,
      Continuous fun p : ℝ × (Fin n → ℝ) => p.2 i :=
    fun i => (continuous_apply i).comp continuous_snd
  have hmv : ∀ i : Fin n,
      Continuous fun p : ℝ × (Fin n → ℝ) => A.mulVec p.2 i := by
    intro i
    have h2 : (fun p : ℝ × (Fin n → ℝ) => A.mulVec p.2 i)
        = fun p : ℝ × (Fin n → ℝ) => ∑ j, A i j * p.2 j := by
      funext p
      rw [Matrix.mulVec, dotProduct]
    rw [h2]
    exact continuous_finset_sum _ fun j _ =>
      continuous_const.mul (hcoord j)
  have h1 : cwSet A = {p : ℝ × (Fin n → ℝ) | 0 ≤ p.1}
      ∩ ((⋂ i, {p : ℝ × (Fin n → ℝ) | 0 ≤ p.2 i})
        ∩ ({p : ℝ × (Fin n → ℝ) | ∑ i, p.2 i = 1}
          ∩ ⋂ i, {p : ℝ × (Fin n → ℝ)
            | p.1 * p.2 i ≤ A.mulVec p.2 i})) := by
    ext p
    simp only [cwSet, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_iInter]
  rw [h1]
  refine IsClosed.inter (isClosed_le continuous_const
    continuous_fst) (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
  · exact isClosed_iInter fun i =>
      isClosed_le continuous_const (hcoord i)
  · exact isClosed_eq (continuous_finset_sum _ fun i _ => hcoord i)
      continuous_const
  · exact isClosed_iInter fun i =>
      isClosed_le (continuous_fst.mul (hcoord i)) (hmv i)

theorem cwSet_subset_box {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 < A i j) :
    cwSet A ⊆ Set.Icc ((0 : ℝ), fun _ => (0 : ℝ))
      ((∑ i, ∑ j, A i j), fun _ => (1 : ℝ)) := by
  rintro ⟨lam, x⟩ ⟨hlam, hx, hsum, hle⟩
  have hx1 : ∀ i, x i ≤ 1 := by
    intro i
    calc x i ≤ ∑ j, x j :=
        Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      _ = 1 := hsum
  refine ⟨⟨hlam, fun i => hx i⟩, ⟨?_, fun i => hx1 i⟩⟩
  have h1 : lam = ∑ i, lam * x i := by
    rw [← Finset.mul_sum, hsum, mul_one]
  have h2 : ∑ i, lam * x i ≤ ∑ i, A.mulVec x i :=
    Finset.sum_le_sum fun i _ => hle i
  have h3 : ∑ i, A.mulVec x i ≤ ∑ i, ∑ j, A i j := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Matrix.mulVec, dotProduct]
    refine Finset.sum_le_sum fun j _ => ?_
    calc A i j * x j ≤ A i j * 1 :=
        mul_le_mul_of_nonneg_left (hx1 j) (hA i j).le
      _ = A i j := mul_one _
  linarith

theorem cwSet_isCompact {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 < A i j) : IsCompact (cwSet A) :=
  IsCompact.of_isClosed_subset isCompact_Icc (cwSet_isClosed A)
    (cwSet_subset_box hA)

/-- Strictly positive matrices send nonzero nonnegative vectors to
strictly positive vectors. -/
theorem mulVec_pos {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 < A i j) {v : Fin n → ℝ} (hv : ∀ j, 0 ≤ v j)
    (hvne : ∃ j, 0 < v j) (i : Fin n) : 0 < A.mulVec v i := by
  obtain ⟨j₀, hj₀⟩ := hvne
  rw [Matrix.mulVec, dotProduct]
  exact Finset.sum_pos' (fun j _ =>
    mul_nonneg (hA i j).le (hv j)) ⟨j₀, Finset.mem_univ j₀,
    mul_pos (hA i j₀) hj₀⟩

/-- **Perron–Frobenius existence for positive matrices**
(Collatz–Wielandt, no fixed-point theorem): a strictly positive
eigenvector with a strictly positive eigenvalue. -/
theorem perron_exists {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 < A i j) :
    ∃ (r : ℝ) (x : Fin n → ℝ), 0 < r ∧ (∀ i, 0 < x i)
      ∧ A.mulVec x = r • x := by
  classical
  obtain ⟨lam₀, x₀, hmem₀, hlam₀⟩ := cwSet_witness hA
  obtain ⟨⟨r, x⟩, hmem, hmax⟩ :=
    (cwSet_isCompact hA).exists_isMaxOn ⟨_, hmem₀⟩
      continuous_fst.continuousOn
  obtain ⟨hr0, hx0, hsum, hle⟩ := hmem
  have hrpos : 0 < r := lt_of_lt_of_le hlam₀ (hmax hmem₀)
  have hxne : ∃ j, 0 < x j := by
    by_contra hcon
    push_neg at hcon
    have h4 : ∑ i, x i ≤ 0 :=
      Finset.sum_nonpos fun i _ => hcon i
    rw [hsum] at h4
    linarith
  have heq : A.mulVec x = r • x := by
    by_contra hne
    have hstrict : ∃ j, r * x j < A.mulVec x j := by
      by_contra hcon
      push_neg at hcon
      refine hne (funext fun i => ?_)
      have h5 := le_antisymm (hcon i) (hle i)
      rw [Pi.smul_apply, smul_eq_mul]
      exact h5
    obtain ⟨j₀, hj₀⟩ := hstrict
    set y := A.mulVec x with hy
    have hypos : ∀ i, 0 < y i := fun i => mulVec_pos hA hx0 hxne i
    set d : Fin n → ℝ := fun i => y i - r * x i with hd
    have hd0 : ∀ i, 0 ≤ d i := fun i => sub_nonneg.mpr (hle i)
    have hdne : ∃ i, 0 < d i := ⟨j₀, sub_pos.mpr hj₀⟩
    have hAd : ∀ i, 0 < A.mulVec d i :=
      fun i => mulVec_pos hA hd0 hdne i
    set ε := Finset.univ.inf' Finset.univ_nonempty
      (fun i => A.mulVec d i) with hε
    have hεpos : 0 < ε := by
      rw [hε, Finset.lt_inf'_iff]
      intro i _
      exact hAd i
    have hεle : ∀ i, ε ≤ A.mulVec d i := by
      intro i
      rw [hε]
      exact Finset.inf'_le _ (Finset.mem_univ i)
    set Y := Finset.univ.sup' Finset.univ_nonempty y with hY
    have hyY : ∀ i, y i ≤ Y := by
      intro i
      rw [hY]
      exact Finset.le_sup' _ (Finset.mem_univ i)
    have hYpos : 0 < Y :=
      lt_of_lt_of_le
        (hypos ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩)
        (hyY _)
    have hkey : ∀ i, (r + ε / Y) * y i ≤ A.mulVec y i := by
      intro i
      have h5 : A.mulVec y i = r * A.mulVec x i + A.mulVec d i
          := by
        have h6 : y = fun k => r * x k + d k := by
          funext k
          rw [hd]
          ring
        calc A.mulVec y i
            = A.mulVec (fun k => r * x k + d k) i := by
              rw [← h6]
          _ = r * A.mulVec x i + A.mulVec d i := by
              rw [Matrix.mulVec, Matrix.mulVec, Matrix.mulVec,
                dotProduct, dotProduct, dotProduct,
                Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun k _ => ?_
              ring
      have h7 : ε / Y * y i ≤ A.mulVec d i := by
        have h8 : ε / Y * y i ≤ ε / Y * Y :=
          mul_le_mul_of_nonneg_left (hyY i) (by positivity)
        have h9 : ε / Y * Y = ε := by
          field_simp
        linarith [hεle i]
      have h10 : (r + ε / Y) * y i
          = r * y i + ε / Y * y i := by
        ring
      rw [h10, h5, ← hy]
      linarith
    set s := ∑ i, y i with hs
    have hspos : 0 < s := by
      rw [hs]
      exact Finset.sum_pos (fun i _ => hypos i)
        Finset.univ_nonempty
    have hmem' : (r + ε / Y, fun i => y i / s) ∈ cwSet A := by
      refine ⟨add_nonneg hr0 (div_nonneg hεpos.le hYpos.le),
        fun i => div_nonneg (hypos i).le hspos.le, ?_, ?_⟩
      · rw [← Finset.sum_div, ← hs]
        field_simp
      · intro i
        have h11 : A.mulVec (fun k => y k / s) i
            = A.mulVec y i / s := by
          rw [Matrix.mulVec, Matrix.mulVec, dotProduct,
            dotProduct, Finset.sum_div]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
        rw [h11]
        have h13 : (r + ε / Y) * (y i / s)
            = ((r + ε / Y) * y i) / s := by
          ring
        rw [h13]
        gcongr
        exact hkey i
    have h14 := hmax hmem'
    have h15 : 0 < ε / Y := by positivity
    have h16 : r + ε / Y ≤ r := h14
    linarith
  have hxpos : ∀ i, 0 < x i := by
    intro i
    have h16 : 0 < A.mulVec x i := mulVec_pos hA hx0 hxne i
    rw [heq, Pi.smul_apply, smul_eq_mul] at h16
    by_contra hcon
    push_neg at hcon
    have h17 : x i = 0 := le_antisymm hcon (hx0 i)
    rw [h17, mul_zero] at h16
    linarith
  exact ⟨r, x, hrpos, hxpos, heq⟩

/-- **Left Perron eigenvector**, by transposing. -/
theorem perron_exists_left {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 < A i j) :
    ∃ (r : ℝ) (ν : Fin n → ℝ), 0 < r ∧ (∀ i, 0 < ν i)
      ∧ A.vecMul ν = r • ν := by
  obtain ⟨r, ν, hr, hν, heq⟩ :=
    perron_exists (A := Aᵀ) (fun i j => hA j i)
  refine ⟨r, ν, hr, hν, ?_⟩
  rw [← Matrix.mulVec_transpose]
  exact heq

/-- A left and a right eigenvalue with positive eigenvectors
agree: pair the eigenvectors. -/
theorem perron_left_right_eq {A : Matrix (Fin n) (Fin n) ℝ}
    {r s : ℝ} {h ν : Fin n → ℝ}
    (hh : ∀ i, 0 < h i) (hν : ∀ i, 0 < ν i)
    (hr : A.mulVec h = r • h) (hs : A.vecMul ν = s • ν) :
    r = s := by
  have h1 : ν ⬝ᵥ A.mulVec h = r * (ν ⬝ᵥ h) := by
    rw [hr]
    rw [dotProduct_smul, smul_eq_mul]
  have h2 : ν ⬝ᵥ A.mulVec h = s * (ν ⬝ᵥ h) := by
    rw [Matrix.dotProduct_mulVec, hs]
    rw [smul_dotProduct, smul_eq_mul]
  have h3 : 0 < ν ⬝ᵥ h := by
    rw [dotProduct]
    exact Finset.sum_pos
      (fun i _ => mul_pos (hν i) (hh i)) Finset.univ_nonempty
  have h4 : r * (ν ⬝ᵥ h) = s * (ν ⬝ᵥ h) := by
    rw [← h1, h2]
  exact mul_right_cancel₀ h3.ne' h4

end NCG
