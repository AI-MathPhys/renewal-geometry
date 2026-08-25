/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Irreducibility of the traceless block under unitary conjugation

Machinery for `thm:SM-colour-orbit`: any subspace of `Matrix n n ℂ` invariant under
all unitary conjugations `A ↦ U A U*` that contains a non-scalar element contains
every traceless matrix (`traceless_le_of_nonscalar`).

The proof is a fully explicit finite reduction:

* `single_entry_mem`: phase-diagonal conjugations (with `-1` and `i` phases) isolate
  any single off-diagonal entry of a member;
* `swap_conj_single` / `single_transport`: swap-matrix conjugations move an isolated
  off-diagonal unit to every off-diagonal position;
* `had_conj_single` / `had_conj_diag`: the Hadamard-type plane rotation converts
  between off-diagonal units and diagonal differences `E_kk - E_ll`;
* `traceless_le_of_nonscalar`: zero-diagonal matrices and traceless diagonals are
  spanned by the extracted family.
-/

open Finset Matrix

namespace NCG
namespace ConjIrreducible

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Invariance under every unitary conjugation. -/
def ConjInvariant (W : Submodule ℂ (Matrix n n ℂ)) : Prop :=
  ∀ U ∈ Matrix.unitaryGroup n ℂ, ∀ A ∈ W, U * A * star U ∈ W

/-- Phase diagonal `diag(1, …, c, …, 1)` with `c` in slot `i`. -/
def phase (i : n) (c : ℂ) : Matrix n n ℂ :=
  Matrix.diagonal fun k => if k = i then c else 1

theorem phase_mem (i : n) {c : ℂ} (hc : star c * c = 1) :
    phase i c ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [phase, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext k
  simp only [Pi.star_apply]
  by_cases h : k = i
  · rw [if_pos h]
    exact hc
  · rw [if_neg h, star_one, one_mul]

theorem phase_conj_apply (i : n) (c : ℂ) (A : Matrix n n ℂ) (k l : n) :
    (phase i c * A * star (phase i c)) k l
      = (if k = i then c else 1) * A k l * star (if l = i then c else 1) := by
  rw [phase, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Pi.star_apply]

/-- Conjugation of a single-entry matrix by an arbitrary matrix, entrywise. -/
theorem conj_single_apply (U : Matrix n n ℂ) (a b : n) (c : ℂ) (k l : n) :
    (U * Matrix.single a b c * star U) k l = U k a * c * star (U l b) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.mul_apply]
  rw [Finset.sum_eq_single b
    (fun m _ hm => by rw [Matrix.mul_single_apply_of_ne (hbj := hm), zero_mul])
    (fun hb => absurd (Finset.mem_univ b) hb)]
  rw [Matrix.mul_single_apply_same, Matrix.conjTranspose_apply]

/-- **Entry isolation**: a conjugation-invariant subspace containing `A` contains the
single-entry matrix carrying any chosen off-diagonal entry of `A`. -/
theorem single_entry_mem {W : Submodule ℂ (Matrix n n ℂ)} (hW : ConjInvariant W)
    {A : Matrix n n ℂ} (hA : A ∈ W) {i j : n} (hij : i ≠ j) :
    Matrix.single i j (A i j) ∈ W := by
  have hc1 : star (-1 : ℂ) * (-1) = 1 := by simp
  have hcI : star Complex.I * Complex.I = 1 := by
    rw [Complex.star_def, Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg]
  set A₁ := (2⁻¹ : ℂ) • (A - phase i (-1) * A * star (phase i (-1))) with hA₁def
  have hA₁mem : A₁ ∈ W :=
    W.smul_mem _ (W.sub_mem hA (hW _ (phase_mem i hc1) A hA))
  have hA₁app : ∀ k l, A₁ k l
      = 2⁻¹ * (1 - (if k = i then (-1 : ℂ) else 1) * star (if l = i then (-1 : ℂ) else 1))
        * A k l := by
    intro k l
    rw [hA₁def, Matrix.smul_apply, Matrix.sub_apply, phase_conj_apply]
    ring
  set A₂ := (2⁻¹ : ℂ) • (A₁ - Complex.I • (phase i Complex.I * A₁ * star (phase i Complex.I)))
    with hA₂def
  have hA₂mem : A₂ ∈ W :=
    W.smul_mem _ (W.sub_mem hA₁mem (W.smul_mem _ (hW _ (phase_mem i hcI) A₁ hA₁mem)))
  have hA₂app : ∀ k l, A₂ k l
      = 2⁻¹ * (1 - Complex.I * ((if k = i then Complex.I else 1)
          * star (if l = i then Complex.I else 1))) * A₁ k l := by
    intro k l
    rw [hA₂def, Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply, phase_conj_apply]
    ring
  set A₃ := (2⁻¹ : ℂ) • (A₂ - phase j (-1) * A₂ * star (phase j (-1))) with hA₃def
  have hA₃mem : A₃ ∈ W :=
    W.smul_mem _ (W.sub_mem hA₂mem (hW _ (phase_mem j hc1) A₂ hA₂mem))
  have hA₃app : ∀ k l, A₃ k l
      = 2⁻¹ * (1 - (if k = j then (-1 : ℂ) else 1) * star (if l = j then (-1 : ℂ) else 1))
        * A₂ k l := by
    intro k l
    rw [hA₃def, Matrix.smul_apply, Matrix.sub_apply, phase_conj_apply]
    ring
  have hfinal : A₃ = Matrix.single i j (A i j) := by
    ext k l
    rw [hA₃app k l, hA₂app k l, hA₁app k l, Matrix.single_apply]
    by_cases hk : k = i
    · by_cases hl : l = i
      · simp [hk, hl, hij, Ne.symm hij, star_neg, star_one]
      · by_cases hlj : l = j
        · simp [hk, hlj, hij, Ne.symm hij, star_neg, star_one]
          ring
        · simp [hk, hl, hlj, Ne.symm hlj, hij, star_one]
    · by_cases hl : l = i
      · simp [hk, Ne.symm (show k ≠ i from hk), hl,
          Complex.conj_I ]
      · simp [hk, Ne.symm (show k ≠ i from hk), hl, star_one]
  rw [← hfinal]
  exact hA₃mem

/-! ### Swap transport -/

theorem swap_mem (p q : n) : Matrix.swap ℂ p q ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff,
    (Matrix.star_eq_conjTranspose _).trans (Matrix.conjTranspose_swap p q)]
  exact Matrix.swap_mul_self p q

theorem swap_conj_apply (p q : n) (M : Matrix n n ℂ) (k l : n) :
    (Matrix.swap ℂ p q * M * Matrix.swap ℂ p q) k l
      = M (Equiv.swap p q k) (Equiv.swap p q l) := by
  have hrow : ∀ (N : Matrix n n ℂ) (k l : n),
      (Matrix.swap ℂ p q * N) k l = N (Equiv.swap p q k) l := by
    intro N k l
    rcases eq_or_ne k p with hk | hk
    · subst hk
      rw [Matrix.swap_mul_apply_left, Equiv.swap_apply_left]
    · rcases eq_or_ne k q with hk2 | hk2
      · subst hk2
        rw [Matrix.swap_mul_apply_right, Equiv.swap_apply_right]
      · rw [Matrix.swap_mul_of_ne hk hk2, Equiv.swap_apply_of_ne_of_ne hk hk2]
  have hcol : ∀ (N : Matrix n n ℂ) (k l : n),
      (N * Matrix.swap ℂ p q) k l = N k (Equiv.swap p q l) := by
    intro N k l
    rcases eq_or_ne l p with hl | hl
    · subst hl
      rw [Matrix.mul_swap_apply_left, Equiv.swap_apply_left]
    · rcases eq_or_ne l q with hl2 | hl2
      · subst hl2
        rw [Matrix.mul_swap_apply_right, Equiv.swap_apply_right]
      · rw [Matrix.mul_swap_of_ne hl hl2, Equiv.swap_apply_of_ne_of_ne hl hl2]
  rw [hcol (Matrix.swap ℂ p q * M) k l, hrow M _ _]

theorem swap_conj_single (p q a b : n) (c : ℂ) :
    Matrix.swap ℂ p q * Matrix.single a b c * star (Matrix.swap ℂ p q)
      = Matrix.single (Equiv.swap p q a) (Equiv.swap p q b) c := by
  rw [(Matrix.star_eq_conjTranspose _).trans (Matrix.conjTranspose_swap p q)]
  ext k l
  rw [swap_conj_apply, Matrix.single_apply, Matrix.single_apply]
  have key : ∀ x y : n, (x = Equiv.swap p q y) ↔ (Equiv.swap p q x = y) := by
    intro x y
    constructor
    · intro h
      rw [h, Equiv.swap_apply_self]
    · intro h
      rw [← h, Equiv.swap_apply_self]
  rw [if_congr (and_congr (key a k) (key b l)) rfl rfl]

/-- Transport of an isolated off-diagonal unit to any off-diagonal position. -/
theorem single_transport {W : Submodule ℂ (Matrix n n ℂ)} (hW : ConjInvariant W)
    {i j : n} (hij : i ≠ j) {c : ℂ} (h : Matrix.single i j c ∈ W)
    {k l : n} (hkl : k ≠ l) : Matrix.single k l c ∈ W := by
  have h1 : Matrix.single (Equiv.swap i k i) (Equiv.swap i k j) c ∈ W := by
    have := hW _ (swap_mem i k) _ h
    rwa [swap_conj_single] at this
  rw [Equiv.swap_apply_left] at h1
  set j' := Equiv.swap i k j with hj'
  have hj'k : j' ≠ k := by
    rw [hj']
    intro hcon
    exact hij ((Equiv.swap i k).injective
      (hcon.trans (Equiv.swap_apply_left i k).symm)).symm
  have h2 : Matrix.single (Equiv.swap j' l k) (Equiv.swap j' l j') c ∈ W := by
    have := hW _ (swap_mem j' l) _ h1
    rwa [swap_conj_single] at this
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hj'k) hkl] at h2
  exact h2

/-! ### The Hadamard plane rotation -/

/-- The Hadamard-type plane rotation acting in the `(i, j)` coordinate plane. -/
noncomputable def had (i j : n) : Matrix n n ℂ :=
  fun k l =>
    if k = i then
      (if l = i then ((Real.sqrt 2 : ℂ))⁻¹ else if l = j then ((Real.sqrt 2 : ℂ))⁻¹ else 0)
    else if k = j then
      (if l = i then -((Real.sqrt 2 : ℂ))⁻¹ else if l = j then ((Real.sqrt 2 : ℂ))⁻¹ else 0)
    else (if k = l then 1 else 0)

theorem sqrt_two_inv_mul_self : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 2⁻¹ := by
  rw [← mul_inv]
  rw [show ((Real.sqrt 2 : ℂ)) * ((Real.sqrt 2 : ℂ)) = (2 : ℂ) by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)]

theorem star_sqrt_two_inv : star ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 : ℂ))⁻¹ := by
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]

theorem had_mem (i j : n) (hij : i ≠ j) : had i j ∈ Matrix.unitaryGroup n ℂ := by
  have hpair : ∀ f : n → ℂ, (∀ m, m ≠ i → m ≠ j → f m = 0) → ∑ m, f m = f i + f j := by
    intro f hf
    have h1 : ∑ m ∈ ({i, j} : Finset n), f m = ∑ m, f m := by
      refine Finset.sum_subset (Finset.subset_univ _) fun m _ hm => ?_
      rw [Finset.mem_insert, Finset.mem_singleton] at hm
      exact hf m (fun h => hm (Or.inl h)) (fun h => hm (Or.inr h))
    rw [← h1, Finset.sum_pair hij]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext k l
  have hterm : ((had i j) * (had i j)ᴴ) k l
      = ∑ m, had i j k m * star (had i j l m) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun m _ => by rw [Matrix.conjTranspose_apply]
  rw [hterm]
  by_cases hk : k = i
  · rw [hpair _ (fun m hmi hmj => by simp [had, hk, hmi, hmj])]
    by_cases hl : l = i
    · simp [had, hk, hl, sqrt_two_inv_mul_self,
        Matrix.one_apply]
      norm_num
    · by_cases hlj : l = j
      · simp [had, hk, hlj, hij, Ne.symm hij,
          sqrt_two_inv_mul_self, Complex.conj_ofReal ]
      · simp [had, hk, hl, hlj, Ne.symm hl  ]
  · by_cases hk2 : k = j
    · rw [hpair _ (fun m hmi hmj => by simp [had, hk2, hmi, hmj])]
      by_cases hl : l = i
      · simp [had, hk2, Ne.symm hij, hl,
          sqrt_two_inv_mul_self, Complex.conj_ofReal ]
      · by_cases hlj : l = j
        · simp [had, hk2, hlj, Ne.symm hij,
            sqrt_two_inv_mul_self, Matrix.one_apply, Complex.conj_ofReal ]
          norm_num
        · simp [had, hk2, hl, hlj, Ne.symm hlj, Ne.symm hij  ]
    · rw [show (∑ m, had i j k m * star (had i j l m))
          = had i j k k * star (had i j l k) from
        Finset.sum_eq_single k
          (fun m _ hm => by simp [had, hk, hk2, Ne.symm hm])
          (fun hb => absurd (Finset.mem_univ k) hb)]
      by_cases hl : l = i
      · simp [had, hk, hk2, hl ]
      · by_cases hlj : l = j
        · simp [had, hk, hk2, hlj ]
        · by_cases hlk : l = k
          · simp [had, hk, hk2, hlk, Matrix.one_apply]
          · simp [had, hk, hk2, hl, hlj, Ne.symm hlk, hlk ]

theorem had_conj_single (i j : n) (hij : i ≠ j) :
    had i j * Matrix.single i j 1 * star (had i j)
      = (2⁻¹ : ℂ) • (Matrix.single i i 1 + Matrix.single i j 1
          - Matrix.single j i 1 - Matrix.single j j 1) := by
  ext k l
  rw [conj_single_apply]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply]
  by_cases hk : k = i
  · by_cases hl : l = i
    · simp [had, hk, hl, Ne.symm hij, sqrt_two_inv_mul_self]
    · by_cases hlj : l = j
      · simp [had, hk, hlj, hij, Ne.symm hij,
          sqrt_two_inv_mul_self ]
      · simp [had, hk, hl, hlj, Ne.symm hl, Ne.symm hlj]
  · by_cases hk2 : k = j
    · by_cases hl : l = i
      · simp [had, hk2, hij, Ne.symm hij, hl,
          sqrt_two_inv_mul_self]
      · by_cases hlj : l = j
        · simp [had, hk2, hlj, hij, Ne.symm hij,
            sqrt_two_inv_mul_self]
        · simp [had, hij, hk2, hl, hlj, Ne.symm hl, Ne.symm hlj]
    · simp [had, hk, hk2, Ne.symm hk, Ne.symm hk2]

theorem had_conj_diag (i j : n) (hij : i ≠ j) :
    had i j * (Matrix.single i i 1 - Matrix.single j j 1) * star (had i j)
      = -(Matrix.single i j 1 + Matrix.single j i 1) := by
  have hd : had i j * (Matrix.single i i 1 - Matrix.single j j 1) * star (had i j)
      = had i j * Matrix.single i i 1 * star (had i j)
        - had i j * Matrix.single j j 1 * star (had i j) := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [hd]
  ext k l
  rw [Matrix.sub_apply, conj_single_apply, conj_single_apply]
  simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.single_apply]
  by_cases hk : k = i
  · by_cases hl : l = i
    · simp [had, hk, hl, Ne.symm hij, sqrt_two_inv_mul_self]
    · by_cases hlj : l = j
      · simp [had, hk, hlj, hij, Ne.symm hij,
          sqrt_two_inv_mul_self ]
        ring
      · simp [had, hk, hl, hlj, Ne.symm hl, Ne.symm hlj]
  · by_cases hk2 : k = j
    · by_cases hl : l = i
      · simp [had, hk2, hij, Ne.symm hij, hl,
          sqrt_two_inv_mul_self]
        ring
      · by_cases hlj : l = j
        · simp [had, hk2, hlj, hij, Ne.symm hij,
            sqrt_two_inv_mul_self]
        · simp [had, hij, hk2, hl, hlj, Ne.symm hl, Ne.symm hlj]
    · simp [had, hk, hk2, Ne.symm hk, Ne.symm hk2]

/-! ### Classification -/

/-- From one off-diagonal unit, every off-diagonal unit and every diagonal
difference is a member. -/
theorem members_of_offdiag_unit {W : Submodule ℂ (Matrix n n ℂ)} (hW : ConjInvariant W)
    {i j : n} (hij : i ≠ j) (h : Matrix.single i j (1 : ℂ) ∈ W) :
    (∀ k l : n, k ≠ l → ∀ c : ℂ, Matrix.single k l c ∈ W) ∧
    (∀ k l : n, k ≠ l →
      Matrix.single k k (1 : ℂ) - Matrix.single l l 1 ∈ W) := by
  have hoff : ∀ k l : n, k ≠ l → ∀ c : ℂ, Matrix.single k l c ∈ W := by
    intro k l hkl c
    have h1 : Matrix.single k l (1 : ℂ) ∈ W := single_transport hW hij h hkl
    have h2 := W.smul_mem c h1
    rwa [Matrix.smul_single, smul_eq_mul, mul_one] at h2
  refine ⟨hoff, fun k l hkl => ?_⟩
  have hM : had k l * Matrix.single k l 1 * star (had k l) ∈ W :=
    hW _ (had_mem k l hkl) _ (hoff k l hkl 1)
  rw [had_conj_single k l hkl] at hM
  have h2 := W.smul_mem (2 : ℂ) hM
  rw [smul_smul, mul_inv_cancel₀ (two_ne_zero), one_smul] at h2
  -- h2 : E_kk + E_kl - E_lk - E_ll ∈ W
  have h3 := W.sub_mem h2 (hoff k l hkl 1)
  have h4 := W.add_mem h3 (hoff l k hkl.symm 1)
  have he : Matrix.single k k (1 : ℂ) + Matrix.single k l 1 - Matrix.single l k 1
        - Matrix.single l l 1 - Matrix.single k l 1 + Matrix.single l k 1
      = Matrix.single k k 1 - Matrix.single l l 1 := by
    abel
  rwa [he] at h4

/-- **Main classification**: a conjugation-invariant subspace containing a non-scalar
element contains every traceless matrix. -/
theorem traceless_le_of_nonscalar {W : Submodule ℂ (Matrix n n ℂ)} (hW : ConjInvariant W)
    {A : Matrix n n ℂ} (hA : A ∈ W)
    (hns : ∃ k l, k ≠ l ∧ (A k l ≠ 0 ∨ A k k ≠ A l l)) :
    ∀ B : Matrix n n ℂ, Matrix.trace B = 0 → B ∈ W := by
  obtain ⟨k₀, l₀, hkl₀, hcase⟩ := hns
  -- Stage 1: obtain one off-diagonal unit.
  have hunit : ∃ i j : n, i ≠ j ∧ Matrix.single i j (1 : ℂ) ∈ W := by
    by_cases hoffA : ∃ i j, i ≠ j ∧ A i j ≠ 0
    · obtain ⟨i, j, hij, hne⟩ := hoffA
      refine ⟨i, j, hij, ?_⟩
      have h1 := single_entry_mem hW hA hij
      have h2 := W.smul_mem (A i j)⁻¹ h1
      rwa [Matrix.smul_single, smul_eq_mul, inv_mul_cancel₀ hne] at h2
    · -- A is diagonal; a diagonal difference is available.
      have hdiagA : ∀ i j, i ≠ j → A i j = 0 := by
        intro i j hij
        by_contra hne
        exact hoffA ⟨i, j, hij, hne⟩
      have hdd : A k₀ k₀ ≠ A l₀ l₀ := by
        rcases hcase with h | h
        · exact absurd (hdiagA k₀ l₀ hkl₀) h
        · exact h
      -- D = A - swap-conjugate of A is a scaled diagonal difference.
      have hswap : Matrix.swap ℂ k₀ l₀ * A * star (Matrix.swap ℂ k₀ l₀) ∈ W :=
        hW _ (swap_mem k₀ l₀) _ hA
      have hD : A - Matrix.swap ℂ k₀ l₀ * A * star (Matrix.swap ℂ k₀ l₀) ∈ W :=
        W.sub_mem hA hswap
      have hDeq : A - Matrix.swap ℂ k₀ l₀ * A * star (Matrix.swap ℂ k₀ l₀)
          = (A k₀ k₀ - A l₀ l₀) •
            (Matrix.single k₀ k₀ 1 - Matrix.single l₀ l₀ 1) := by
        rw [(Matrix.star_eq_conjTranspose _).trans (Matrix.conjTranspose_swap k₀ l₀)]
        ext k l
        rw [Matrix.sub_apply, swap_conj_apply, Matrix.smul_apply, Matrix.sub_apply,
          Matrix.single_apply, Matrix.single_apply]
        by_cases hk : k = l
        · subst hk
          by_cases h1 : k = k₀
          · subst h1
            rw [Equiv.swap_apply_left]
            simp [Ne.symm hkl₀ ]
          · by_cases h2 : k = l₀
            · subst h2
              rw [Equiv.swap_apply_right]
              simp [ hkl₀ ]
            · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
              simp [ Ne.symm h1, Ne.symm h2]
        · have hzero1 : A k l = 0 := hdiagA k l hk
          have hzero2 : A (Equiv.swap k₀ l₀ k) (Equiv.swap k₀ l₀ l) = 0 :=
            hdiagA _ _ fun hcon => hk ((Equiv.swap k₀ l₀).injective hcon)
          rw [hzero1, hzero2,
            if_neg (show ¬(k₀ = k ∧ k₀ = l) from fun h => hk (h.1.symm.trans h.2)),
            if_neg (show ¬(l₀ = k ∧ l₀ = l) from fun h => hk (h.1.symm.trans h.2))]
          ring
      rw [hDeq] at hD
      have hdiff : Matrix.single k₀ k₀ (1 : ℂ) - Matrix.single l₀ l₀ 1 ∈ W := by
        have h2 := W.smul_mem (A k₀ k₀ - A l₀ l₀)⁻¹ hD
        rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hdd), one_smul] at h2
      -- Hadamard converts the diagonal difference into off-diagonal units.
      have hN : had k₀ l₀ * (Matrix.single k₀ k₀ 1 - Matrix.single l₀ l₀ 1)
          * star (had k₀ l₀) ∈ W := hW _ (had_mem k₀ l₀ hkl₀) _ hdiff
      rw [had_conj_diag k₀ l₀ hkl₀] at hN
      have hsum : Matrix.single k₀ l₀ (1 : ℂ) + Matrix.single l₀ k₀ 1 ∈ W := by
        have := W.smul_mem (-1 : ℂ) hN
        rwa [neg_smul, one_smul, neg_neg] at this
      refine ⟨k₀, l₀, hkl₀, ?_⟩
      have hiso := single_entry_mem hW hsum hkl₀
      have hval : (Matrix.single k₀ l₀ (1 : ℂ) + Matrix.single l₀ k₀ 1
          : Matrix n n ℂ) k₀ l₀ = 1 := by
        rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
        simp [hkl₀, Ne.symm hkl₀]
      exact hval ▸ hiso
  obtain ⟨i, j, hij, hunit⟩ := hunit
  obtain ⟨hoff, hdiag⟩ := members_of_offdiag_unit hW hij hunit
  -- Stage 2: span.
  intro B htr
  have hzeroDiagMem : ∀ C : Matrix n n ℂ, (∀ k, C k k = 0) → C ∈ W := by
    intro C hC
    rw [Matrix.matrix_eq_sum_single C]
    refine W.sum_mem fun k _ => W.sum_mem fun l _ => ?_
    by_cases hkl : k = l
    · subst hkl
      rw [hC k, Matrix.single_zero]
      exact W.zero_mem
    · exact hoff k l hkl _
  have hdiagMem : ∀ d : n → ℂ, ∑ m, d m = 0 → Matrix.diagonal d ∈ W := by
    intro d hd
    have hrepr : Matrix.diagonal d
        = ∑ m, d m • (Matrix.single m m (1 : ℂ) - Matrix.single i i 1) := by
      have h1 : ∑ m, d m • (Matrix.single m m (1 : ℂ) - Matrix.single i i 1)
          = (∑ m, d m • Matrix.single m m (1 : ℂ))
            - (∑ m, d m) • Matrix.single i i (1 : ℂ) := by
        rw [Finset.sum_smul]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun m _ => by rw [smul_sub]
      rw [h1, hd, zero_smul, sub_zero]
      rw [← Matrix.sum_single_eq_diagonal]
      exact Finset.sum_congr rfl fun m _ => by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hrepr]
    refine W.sum_mem fun m _ => W.smul_mem _ ?_
    by_cases hmi : m = i
    · subst hmi
      rw [sub_self]
      exact W.zero_mem
    · exact hdiag m i hmi
  have hsplit : B = (B - Matrix.diagonal fun k => B k k)
      + Matrix.diagonal (fun k => B k k) := by
    rw [sub_add_cancel]
  rw [hsplit]
  refine W.add_mem (hzeroDiagMem _ fun k => ?_) (hdiagMem _ ?_)
  · rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, sub_self]
  · rw [← htr]
    rfl

end ConjIrreducible
end NCG
