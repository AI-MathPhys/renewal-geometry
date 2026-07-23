/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Perron–Frobenius theorem: existence of a positive eigenvector

This file proves the existence half of the **Perron–Frobenius theorem**
for irreducible nonnegative real matrices (`Matrix.IsIrreducible`), by
the Collatz–Wielandt variational argument — no fixed-point theorem is
used.  It is stated over an arbitrary finite index type, in the `Matrix`
namespace, building on `Matrix.IsIrreducible` / `Matrix.IsPrimitive`
from `Mathlib.LinearAlgebra.Matrix.Irreducible.Defs`.

## Main definitions

* `Matrix.collatzWielandtSet A`: the set of pairs `(r, x)` with `r ≥ 0`,
  `x` in the probability simplex, and `r * x i ≤ (A *ᵥ x) i` for every
  `i`; it is compact when `A` is entrywise nonnegative
  (`Matrix.isCompact_collatzWielandtSet`).

## Main results

* `Matrix.IsIrreducible.isPrimitive_one_add`: for an irreducible matrix
  `A`, the shifted matrix `1 + A` is primitive — some power of it is
  entrywise positive.
* `Matrix.IsIrreducible.exists_pos_eigenvector`: **Perron–Frobenius
  existence** — an irreducible nonnegative matrix has a strictly
  positive eigenvalue with an entrywise strictly positive right
  eigenvector.  The pair maximizing `r` over the Collatz–Wielandt set
  is an exact eigenpair: otherwise applying the entrywise positive
  power of `1 + A` strictly improves `r`.
* `Matrix.IsIrreducible.exists_pos_left_eigenvector`: the left (row)
  eigenvector, by transposing.
* `Matrix.left_right_eigenvalue_eq`: eigenvalues with entrywise
  positive left and right eigenvectors agree (pair the eigenvectors);
  with `Matrix.IsIrreducible.eigenvalue_eq_of_pos_eigenvectors` this
  makes the Perron eigenvalue the unique eigenvalue admitting a
  positive eigenvector.
* `Matrix.exists_pos_eigenvector_of_pos`,
  `Matrix.exists_pos_left_eigenvector_of_pos`: the classical statements
  for entrywise positive matrices, via `Matrix.isIrreducible_of_pos`.

## References

* [E. Seneta, *Non-negative Matrices and Markov Chains*][seneta2006],
  Chapter 1.

## Tags

Perron-Frobenius, Collatz-Wielandt, irreducible, primitive,
nonnegative matrix, eigenvector
-/

namespace Matrix

variable {n : Type*} [Fintype n]

/-! ### Entrywise positivity and matrix–vector products -/

/-- An entrywise positive matrix sends a nonzero nonnegative vector to
an entrywise positive vector. -/
theorem mulVec_pos {A : Matrix n n ℝ} (hA : ∀ i j, 0 < A i j)
    {v : n → ℝ} (hv : ∀ j, 0 ≤ v j) (hvne : ∃ j, 0 < v j) (i : n) :
    0 < A.mulVec v i := by
  obtain ⟨j₀, hj₀⟩ := hvne
  rw [mulVec, dotProduct]
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hA i j).le (hv j))
    ⟨j₀, Finset.mem_univ j₀, mul_pos (hA i j₀) hj₀⟩

/-- Entrywise ordering of nonnegative matrices is preserved by powers. -/
theorem pow_apply_le_pow_apply [DecidableEq n] {A B : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hAB : ∀ i j, A i j ≤ B i j) (k : ℕ)
    (i j : n) : (A ^ k) i j ≤ (B ^ k) i j := by
  induction k generalizing i j with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, mul_apply, mul_apply]
    refine Finset.sum_le_sum fun l _ => ?_
    exact mul_le_mul (ih i l) (hAB l j) (hA l j)
      ((pow_apply_nonneg hA m i l).trans (ih i l))

/-- Powers of a nonnegative matrix have positive diagonal entries
wherever the matrix itself does. -/
theorem pow_apply_diag_pos [DecidableEq n] {B : Matrix n n ℝ}
    (hB : ∀ i j, 0 ≤ B i j) {i : n} (hd : 0 < B i i) (m : ℕ) :
    0 < (B ^ m) i i := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_apply]
    exact Finset.sum_pos'
      (fun l _ => mul_nonneg (pow_apply_nonneg hB k i l) (hB l i))
      ⟨i, Finset.mem_univ i, mul_pos ih hd⟩

/-- A single diagonal-times-entry product lower-bounds the entry of the
summed power of a nonnegative matrix. -/
theorem le_pow_add_apply [DecidableEq n] {B : Matrix n n ℝ}
    (hB : ∀ i j, 0 ≤ B i j) (a b : ℕ) (i j : n) :
    (B ^ a) i i * (B ^ b) i j ≤ (B ^ (a + b)) i j := by
  rw [pow_add, mul_apply]
  exact Finset.single_le_sum
    (f := fun l => (B ^ a) i l * (B ^ b) l j)
    (fun l _ => mul_nonneg (pow_apply_nonneg hB a i l)
      (pow_apply_nonneg hB b l j))
    (Finset.mem_univ i)

/-- Iterating a matrix on an eigenvector iterates the eigenvalue. -/
theorem pow_mulVec_eq_smul_pow [DecidableEq n] {B : Matrix n n ℝ}
    {c : ℝ} {x : n → ℝ} (h : B.mulVec x = c • x) (m : ℕ) :
    (B ^ m).mulVec x = c ^ m • x := by
  induction m with
  | zero => simp [one_mulVec]
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul,
      ← pow_succ']

/-! ### Irreducible matrices: rows, and primitivity of `1 + A` -/

omit [Fintype n] in
/-- Every row of an irreducible matrix contains a positive entry (unlike
`Matrix.IsIrreducible.exists_pos`, this needs neither a `Nontrivial`
nor a finiteness hypothesis: a positive-length cycle through `i`
starts with an edge out of `i`). -/
theorem IsIrreducible.exists_pos_entry
    {A : Matrix n n ℝ} (hA : A.IsIrreducible) (i : n) :
    ∃ j, 0 < A i j := by
  letI : Quiver n := toQuiver A
  obtain ⟨p, hp_pos⟩ := hA.connected i i
  obtain ⟨v, p₁, p₂, _, hp₁⟩ :=
    p.exists_eq_comp_of_le_length (n := 1) (Nat.succ_le_of_lt hp_pos)
  obtain ⟨c, p', e, rfl⟩ :=
    (Quiver.Path.length_ne_zero_iff_eq_cons (p := p₁)).1 (by omega)
  obtain rfl : i = c := Quiver.Path.eq_of_length_zero p' (by
    simpa using hp₁)
  exact ⟨v, e.down⟩

/-- For an irreducible matrix `A`, the shifted matrix `1 + A` is
**primitive**: some power of it is entrywise strictly positive.  The
positive diagonal of `1 + A` pads a positive-entry power of `A` up to
a uniform exponent. -/
theorem IsIrreducible.isPrimitive_one_add [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsIrreducible) :
    (1 + A).IsPrimitive := by
  classical
  have hBnn : ∀ i j, 0 ≤ (1 + A) i j := by
    intro i j
    have h1 := hA.nonneg i j
    rw [add_apply, one_apply]
    split_ifs <;> linarith
  have hAB : ∀ i j, A i j ≤ (1 + A) i j := by
    intro i j
    rw [add_apply, one_apply]
    split_ifs <;> linarith
  have hBd : ∀ i, 0 < (1 + A) i i := by
    intro i
    have h1 := hA.nonneg i i
    rw [add_apply, one_apply_eq]
    linarith
  have hex : ∀ p : n × n, ∃ k, 0 < k ∧ 0 < ((1 + A) ^ k) p.1 p.2 := by
    rintro ⟨i, j⟩
    obtain ⟨k, hk, hpos⟩ :=
      ((isIrreducible_iff_exists_pow_pos hA.nonneg).1 hA) i j
    exact ⟨k, hk, lt_of_lt_of_le hpos
      (pow_apply_le_pow_apply hA.nonneg hAB k i j)⟩
  choose k hk hkpos using hex
  refine ⟨hBnn, Finset.univ.sup k + 1, Nat.succ_pos _, fun i j => ?_⟩
  have hle : k (i, j) ≤ Finset.univ.sup k + 1 :=
    (Finset.le_sup (Finset.mem_univ _)).trans (Nat.le_succ _)
  obtain ⟨m, hm⟩ : ∃ m, Finset.univ.sup k + 1 = m + k (i, j) :=
    ⟨Finset.univ.sup k + 1 - k (i, j), (Nat.sub_add_cancel hle).symm⟩
  rw [hm]
  calc (0 : ℝ)
      < ((1 + A) ^ m) i i * ((1 + A) ^ k (i, j)) i j :=
        mul_pos (pow_apply_diag_pos hBnn (hBd i) m) (hkpos (i, j))
    _ ≤ ((1 + A) ^ (m + k (i, j))) i j :=
        le_pow_add_apply hBnn m (k (i, j)) i j

omit [Fintype n] in
/-- An entrywise positive matrix is irreducible: every pair of indices
is joined by an edge of the positivity quiver. -/
theorem isIrreducible_of_pos {A : Matrix n n ℝ}
    (hA : ∀ i j, 0 < A i j) : A.IsIrreducible := by
  refine ⟨fun i j => (hA i j).le, fun i j => ?_⟩
  letI : Quiver n := toQuiver A
  exact ⟨Quiver.Hom.toPath (PLift.up (hA i j)), by simp⟩

/-! ### The Collatz–Wielandt set -/

/-- The Collatz–Wielandt set of a square real matrix: pairs `(r, x)`
with `r ≥ 0`, `x` in the probability simplex, and `r * x i ≤ (A *ᵥ x) i`
for every `i`.  Maximizing `r` over this compact set produces the
Perron eigenvalue. -/
def collatzWielandtSet (A : Matrix n n ℝ) : Set (ℝ × (n → ℝ)) :=
  {p | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ (∑ i, p.2 i = 1)
    ∧ ∀ i, p.1 * p.2 i ≤ A.mulVec p.2 i}

theorem isClosed_collatzWielandtSet (A : Matrix n n ℝ) :
    IsClosed (collatzWielandtSet A) := by
  have hcoord : ∀ i : n,
      Continuous fun p : ℝ × (n → ℝ) => p.2 i :=
    fun i => (continuous_apply i).comp continuous_snd
  have hmv : ∀ i : n,
      Continuous fun p : ℝ × (n → ℝ) => A.mulVec p.2 i := by
    intro i
    have h2 : (fun p : ℝ × (n → ℝ) => A.mulVec p.2 i)
        = fun p : ℝ × (n → ℝ) => ∑ j, A i j * p.2 j := by
      funext p
      rw [mulVec, dotProduct]
    rw [h2]
    exact continuous_finsetSum _ fun j _ =>
      continuous_const.mul (hcoord j)
  have h1 : collatzWielandtSet A = {p : ℝ × (n → ℝ) | 0 ≤ p.1}
      ∩ ((⋂ i, {p : ℝ × (n → ℝ) | 0 ≤ p.2 i})
        ∩ ({p : ℝ × (n → ℝ) | ∑ i, p.2 i = 1}
          ∩ ⋂ i, {p : ℝ × (n → ℝ)
            | p.1 * p.2 i ≤ A.mulVec p.2 i})) := by
    ext p
    simp only [collatzWielandtSet, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_iInter]
  rw [h1]
  refine IsClosed.inter (isClosed_le continuous_const
    continuous_fst) (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
  · exact isClosed_iInter fun i =>
      isClosed_le continuous_const (hcoord i)
  · exact isClosed_eq (continuous_finsetSum _ fun i _ => hcoord i)
      continuous_const
  · exact isClosed_iInter fun i =>
      isClosed_le (continuous_fst.mul (hcoord i)) (hmv i)

theorem collatzWielandtSet_subset_Icc {A : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) :
    collatzWielandtSet A ⊆ Set.Icc ((0 : ℝ), fun _ => (0 : ℝ))
      ((∑ i, ∑ j, A i j), fun _ => (1 : ℝ)) := by
  rintro ⟨r, x⟩ ⟨hr, hx, hsum, hle⟩
  have hx1 : ∀ i, x i ≤ 1 := by
    intro i
    calc x i ≤ ∑ j, x j :=
        Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      _ = 1 := hsum
  refine ⟨⟨hr, fun i => hx i⟩, ⟨?_, fun i => hx1 i⟩⟩
  have h1 : r = ∑ i, r * x i := by
    rw [← Finset.mul_sum, hsum, mul_one]
  have h2 : ∑ i, r * x i ≤ ∑ i, A.mulVec x i :=
    Finset.sum_le_sum fun i _ => hle i
  have h3 : ∑ i, A.mulVec x i ≤ ∑ i, ∑ j, A i j := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mulVec, dotProduct]
    refine Finset.sum_le_sum fun j _ => ?_
    calc A i j * x j ≤ A i j * 1 :=
        mul_le_mul_of_nonneg_left (hx1 j) (hA i j)
      _ = A i j := mul_one _
  linarith

/-- For a nonnegative matrix the Collatz–Wielandt set is compact. -/
theorem isCompact_collatzWielandtSet {A : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) : IsCompact (collatzWielandtSet A) :=
  IsCompact.of_isClosed_subset isCompact_Icc
    (isClosed_collatzWielandtSet A) (collatzWielandtSet_subset_Icc hA)

/-- The Collatz–Wielandt set of an irreducible matrix contains a pair
with strictly positive `r` (the uniform vector works). -/
theorem IsIrreducible.exists_pos_mem_collatzWielandtSet
    [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsIrreducible) :
    ∃ r x, (r, x) ∈ collatzWielandtSet A ∧ 0 < r := by
  classical
  have hN : (0 : ℝ) < Fintype.card n := by
    exact_mod_cast Fintype.card_pos
  set x₀ : n → ℝ := fun _ => (Fintype.card n : ℝ)⁻¹ with hx₀
  have hrow : ∀ i, 0 < A.mulVec x₀ i := by
    intro i
    obtain ⟨j₀, hj₀⟩ := hA.exists_pos_entry i
    rw [mulVec, dotProduct]
    refine Finset.sum_pos'
      (fun j _ => mul_nonneg (hA.nonneg i j) (by simp [hx₀]))
      ⟨j₀, Finset.mem_univ j₀, mul_pos hj₀ (by simp only [hx₀]; positivity)⟩
  set r₀ : ℝ :=
    Finset.univ.inf' Finset.univ_nonempty (fun i => A.mulVec x₀ i)
    with hr₀def
  have hr₀ : 0 < r₀ := by
    rw [hr₀def, Finset.lt_inf'_iff]
    exact fun i _ => hrow i
  have hr₀le : ∀ i, r₀ ≤ A.mulVec x₀ i := by
    intro i
    rw [hr₀def]
    exact Finset.inf'_le _ (Finset.mem_univ i)
  refine ⟨r₀, x₀, ⟨hr₀.le, fun i => by simp [hx₀], ?_, ?_⟩,
    hr₀⟩
  · simp only [hx₀]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ hN.ne']
  · intro i
    have h1 : x₀ i ≤ 1 := by
      simp only [hx₀]
      rw [inv_le_one_iff₀]
      right
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
    calc r₀ * x₀ i ≤ r₀ * 1 :=
        mul_le_mul_of_nonneg_left h1 hr₀.le
      _ = r₀ := mul_one _
      _ ≤ A.mulVec x₀ i := hr₀le i

/-! ### The Perron–Frobenius theorem, existence half -/

/-- **The Perron–Frobenius theorem, existence half**: an irreducible
nonnegative real matrix has a strictly positive eigenvalue with an
entrywise strictly positive right eigenvector (Collatz–Wielandt, no
fixed-point theorem).  The pair maximizing `r` over the compact set
`collatzWielandtSet A` satisfies `A *ᵥ x = r • x` exactly, since
otherwise applying the entrywise positive matrix `(1 + A) ^ K` of
`Matrix.IsIrreducible.isPrimitive_one_add` strictly improves `r`. -/
theorem IsIrreducible.exists_pos_eigenvector
    [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsIrreducible) :
    ∃ (r : ℝ) (x : n → ℝ), 0 < r ∧ (∀ i, 0 < x i)
      ∧ A.mulVec x = r • x := by
  classical
  obtain ⟨r₀, x₀, hmem₀, hr₀⟩ := hA.exists_pos_mem_collatzWielandtSet
  obtain ⟨⟨r, x⟩, hmem, hmax⟩ :=
    (isCompact_collatzWielandtSet hA.nonneg).exists_isMaxOn ⟨_, hmem₀⟩
      continuous_fst.continuousOn
  obtain ⟨hr0, hx0, hsum, hle⟩ := hmem
  have hrpos : 0 < r := lt_of_lt_of_le hr₀ (hmax hmem₀)
  have hxne : ∃ j, 0 < x j := by
    by_contra hcon
    push Not at hcon
    have h4 : ∑ i, x i ≤ 0 :=
      Finset.sum_nonpos fun i _ => hcon i
    rw [hsum] at h4
    linarith
  obtain ⟨hPnn, K, hK, hPpos⟩ := hA.isPrimitive_one_add
  set P : Matrix n n ℝ := (1 + A) ^ K with hPdef
  have hcomm : A * P = P * A := by
    rw [hPdef]
    exact (((Commute.one_right A).add_right (Commute.refl A)).pow_right
      K).eq
  have hcommv : ∀ v : n → ℝ,
      A.mulVec (P.mulVec v) = P.mulVec (A.mulVec v) := by
    intro v
    rw [mulVec_mulVec, mulVec_mulVec, hcomm]
  have heq : A.mulVec x = r • x := by
    by_contra hne
    have hstrict : ∃ j, r * x j < A.mulVec x j := by
      by_contra hcon
      push Not at hcon
      refine hne (funext fun i => ?_)
      have h5 := le_antisymm (hcon i) (hle i)
      rw [Pi.smul_apply, smul_eq_mul]
      exact h5
    obtain ⟨j₀, hj₀⟩ := hstrict
    set d : n → ℝ := fun i => A.mulVec x i - r * x i with hd
    have hd0 : ∀ i, 0 ≤ d i := fun i => sub_nonneg.mpr (hle i)
    have hdne : ∃ i, 0 < d i := ⟨j₀, sub_pos.mpr hj₀⟩
    set y : n → ℝ := P.mulVec x with hy
    have hypos : ∀ i, 0 < y i := fun i => mulVec_pos hPpos hx0 hxne i
    have hPd : ∀ i, 0 < P.mulVec d i :=
      fun i => mulVec_pos hPpos hd0 hdne i
    have hAy : ∀ i, A.mulVec y i = r * y i + P.mulVec d i := by
      intro i
      have h6 : A.mulVec x = r • x + d := by
        funext k
        simp only [hd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have h7 : A.mulVec y = P.mulVec (A.mulVec x) := by
        rw [hy, hcommv]
      rw [h7, h6, mulVec_add, mulVec_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hy]
    set ε : ℝ := Finset.univ.inf' Finset.univ_nonempty
      (fun i => P.mulVec d i) with hε
    have hεpos : 0 < ε := by
      rw [hε, Finset.lt_inf'_iff]
      exact fun i _ => hPd i
    have hεle : ∀ i, ε ≤ P.mulVec d i := by
      intro i
      rw [hε]
      exact Finset.inf'_le _ (Finset.mem_univ i)
    set Y : ℝ := Finset.univ.sup' Finset.univ_nonempty y with hY
    have hyY : ∀ i, y i ≤ Y := by
      intro i
      rw [hY]
      exact Finset.le_sup' _ (Finset.mem_univ i)
    have hYpos : 0 < Y :=
      lt_of_lt_of_le (hypos (Classical.arbitrary n)) (hyY _)
    have hkey : ∀ i, (r + ε / Y) * y i ≤ A.mulVec y i := by
      intro i
      have h8 : ε / Y * y i ≤ ε := by
        have h9 : ε / Y * y i ≤ ε / Y * Y :=
          mul_le_mul_of_nonneg_left (hyY i) (by positivity)
        have h10 : ε / Y * Y = ε := by
          field_simp
        linarith
      calc (r + ε / Y) * y i = r * y i + ε / Y * y i := by ring
        _ ≤ r * y i + P.mulVec d i := by linarith [hεle i]
        _ = A.mulVec y i := (hAy i).symm
    set s : ℝ := ∑ i, y i with hs
    have hspos : 0 < s := by
      rw [hs]
      exact Finset.sum_pos (fun i _ => hypos i) Finset.univ_nonempty
    have hmem' : (r + ε / Y, fun i => y i / s)
        ∈ collatzWielandtSet A := by
      refine ⟨add_nonneg hr0 (div_nonneg hεpos.le hYpos.le),
        fun i => div_nonneg (hypos i).le hspos.le, ?_, ?_⟩
      · rw [← Finset.sum_div, ← hs, div_self hspos.ne']
      · intro i
        have h11 : A.mulVec (fun k => y k / s) i
            = A.mulVec y i / s := by
          rw [mulVec, mulVec, dotProduct, dotProduct, Finset.sum_div]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
        rw [h11, show (r + ε / Y) * (y i / s)
            = ((r + ε / Y) * y i) / s by ring]
        gcongr
        exact hkey i
    have h14 := hmax hmem'
    have h15 : 0 < ε / Y := by positivity
    have h16 : r + ε / Y ≤ r := h14
    linarith
  have hPx : ∀ i, 0 < P.mulVec x i :=
    fun i => mulVec_pos hPpos hx0 hxne i
  have hBx : (1 + A).mulVec x = (1 + r) • x := by
    rw [add_mulVec, one_mulVec, heq]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hPxeq : P.mulVec x = (1 + r) ^ K • x := by
    rw [hPdef]
    exact pow_mulVec_eq_smul_pow hBx K
  have hxpos : ∀ i, 0 < x i := by
    intro i
    have h17 := hPx i
    rw [hPxeq, Pi.smul_apply, smul_eq_mul] at h17
    have h18 : 0 < (1 + r) ^ K := pow_pos (by linarith) K
    by_contra hcon
    push Not at hcon
    nlinarith
  exact ⟨r, x, hrpos, hxpos, heq⟩

/-- **Left Perron eigenvector** for an irreducible matrix, by
transposing. -/
theorem IsIrreducible.exists_pos_left_eigenvector
    [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsIrreducible) :
    ∃ (r : ℝ) (ν : n → ℝ), 0 < r ∧ (∀ i, 0 < ν i)
      ∧ A.vecMul ν = r • ν := by
  classical
  obtain ⟨r, ν, hr, hν, heq⟩ := hA.transpose.exists_pos_eigenvector
  refine ⟨r, ν, hr, hν, ?_⟩
  rw [← mulVec_transpose]
  exact heq

/-- Eigenvalues with entrywise positive left and right eigenvectors
agree: pair the eigenvectors. -/
theorem left_right_eigenvalue_eq [Nonempty n] {A : Matrix n n ℝ}
    {r s : ℝ} {h ν : n → ℝ}
    (hh : ∀ i, 0 < h i) (hν : ∀ i, 0 < ν i)
    (hr : A.mulVec h = r • h) (hs : A.vecMul ν = s • ν) :
    r = s := by
  have h1 : ν ⬝ᵥ A.mulVec h = r * (ν ⬝ᵥ h) := by
    rw [hr, dotProduct_smul, smul_eq_mul]
  have h2 : ν ⬝ᵥ A.mulVec h = s * (ν ⬝ᵥ h) := by
    rw [dotProduct_mulVec, hs, smul_dotProduct, smul_eq_mul]
  have h3 : 0 < ν ⬝ᵥ h := by
    rw [dotProduct]
    exact Finset.sum_pos
      (fun i _ => mul_pos (hν i) (hh i)) Finset.univ_nonempty
  have h4 : r * (ν ⬝ᵥ h) = s * (ν ⬝ᵥ h) := by
    rw [← h1, h2]
  exact mul_right_cancel₀ h3.ne' h4

/-- The Perron eigenvalue of an irreducible matrix is the unique
eigenvalue admitting an entrywise positive eigenvector. -/
theorem IsIrreducible.eigenvalue_eq_of_pos_eigenvectors
    [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsIrreducible)
    {r r' : ℝ} {x x' : n → ℝ} (hx : ∀ i, 0 < x i) (hx' : ∀ i, 0 < x' i)
    (h : A.mulVec x = r • x) (h' : A.mulVec x' = r' • x') : r = r' := by
  classical
  obtain ⟨t, ν, _, hν, ht⟩ := hA.exists_pos_left_eigenvector
  rw [left_right_eigenvalue_eq hx hν h ht,
    left_right_eigenvalue_eq hx' hν h' ht]

/-- **Simplicity of the Perron eigenvalue**: every eigenvector of an
irreducible matrix for an eigenvalue admitting an entrywise positive
eigenvector is a scalar multiple of that eigenvector — the Perron
eigenspace is one-dimensional.  Subtracting the extremal multiple of
the positive eigenvector leaves a nonnegative eigenvector with a zero
coordinate, which the entrywise positive power of `1 + A` forbids
unless it vanishes. -/
theorem IsIrreducible.exists_eq_smul_of_mulVec_eq_smul [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsIrreducible) {r : ℝ} {x y : n → ℝ}
    (hx : ∀ i, 0 < x i) (hAx : A.mulVec x = r • x)
    (hAy : A.mulVec y = r • y) : ∃ c : ℝ, y = c • x := by
  classical
  set t : ℝ := Finset.univ.inf' Finset.univ_nonempty
    (fun i => y i / x i) with ht
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => y i / x i)
  set z : n → ℝ := y - t • x with hz
  have hz0 : ∀ i, 0 ≤ z i := by
    intro i
    have h1 : t ≤ y i / x i := by
      rw [ht]
      exact Finset.inf'_le _ (Finset.mem_univ i)
    have h2 := (le_div_iff₀ (hx i)).1 h1
    simp only [hz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hzi₀ : z i₀ = 0 := by
    simp only [hz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [ht, hi₀, div_mul_cancel₀ _ (hx i₀).ne', sub_self]
  have hAz : A.mulVec z = r • z := by
    rw [hz, mulVec_sub, mulVec_smul, hAx, hAy, smul_sub, smul_smul,
      smul_smul, mul_comm t r]
  refine ⟨t, funext fun i => ?_⟩
  by_contra hne
  have hzine : z i ≠ 0 := by
    simp only [hz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    intro h3
    exact hne (by rw [Pi.smul_apply, smul_eq_mul]; linarith)
  have hzipos : 0 < z i := (hz0 i).lt_of_ne (Ne.symm hzine)
  obtain ⟨hPnn, K, hK, hPpos⟩ := hA.isPrimitive_one_add
  have hBz : (1 + A).mulVec z = (1 + r) • z := by
    rw [add_mulVec, one_mulVec, hAz]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hPz : ((1 + A) ^ K).mulVec z = (1 + r) ^ K • z :=
    pow_mulVec_eq_smul_pow hBz K
  have h4 : 0 < ((1 + A) ^ K).mulVec z i₀ :=
    mulVec_pos hPpos hz0 ⟨i, hzipos⟩ i₀
  rw [hPz, Pi.smul_apply, smul_eq_mul, hzi₀, mul_zero] at h4
  exact lt_irrefl 0 h4

/-! ### Entrywise positive matrices -/

/-- **Perron–Frobenius existence for entrywise positive matrices**: a
strictly positive eigenvalue with an entrywise strictly positive right
eigenvector. -/
theorem exists_pos_eigenvector_of_pos [Nonempty n] {A : Matrix n n ℝ}
    (hA : ∀ i j, 0 < A i j) :
    ∃ (r : ℝ) (x : n → ℝ), 0 < r ∧ (∀ i, 0 < x i)
      ∧ A.mulVec x = r • x := by
  classical
  exact (isIrreducible_of_pos hA).exists_pos_eigenvector

/-- **Left Perron eigenvector** for an entrywise positive matrix. -/
theorem exists_pos_left_eigenvector_of_pos [Nonempty n]
    {A : Matrix n n ℝ} (hA : ∀ i j, 0 < A i j) :
    ∃ (r : ℝ) (ν : n → ℝ), 0 < r ∧ (∀ i, 0 < ν i)
      ∧ A.vecMul ν = r • ν := by
  classical
  exact (isIrreducible_of_pos hA).exists_pos_left_eigenvector

end Matrix
