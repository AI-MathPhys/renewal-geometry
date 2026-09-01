/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Twisted exterior-square coefficients of the standard permutation module

An equivariant map `Λ²W → W ⊗ sgn` can be written, in ambient permutation
coordinates, as a three-index coefficient tensor.  The output and both inputs
are centred, the last two indices are alternating, and simultaneous index
permutation multiplies the tensor by the sign character.

The key stable-range observation is elementary: when there are at least five
coordinates, two coordinates lie outside any prescribed triple.  Swapping
those two fixes all three tensor indices but changes the sign, so every
coefficient vanishes.  This gives the entire `N ≥ 5` half of the all-dimension
vanishing clause in `thm:dimension-K4-selector` without Specht modules.
-/

open scoped BigOperators

namespace NCG

/-- Ambient coefficient presentation of a map `Λ²W → W ⊗ sgn`, where `W` is
the centred standard permutation representation. -/
structure StandardTwistedExteriorTensor (ι : Type*) [Fintype ι]
    [DecidableEq ι] where
  coeff : ι → ι → ι → ℂ
  alternate : ∀ k i j, coeff k i j = -coeff k j i
  input_centered : ∀ k j, ∑ i, coeff k i j = 0
  output_centered : ∀ i j, ∑ k, coeff k i j = 0
  equivariant : ∀ (p : Equiv.Perm ι) k i j,
    coeff (p k) (p i) (p j) =
      ((Equiv.Perm.sign p : ℤ) : ℂ) * coeff k i j

/-- In a finite type of cardinality at least five, two distinct coordinates
can be chosen outside any prescribed triple. -/
theorem exists_pair_outside_triple {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 5 ≤ Fintype.card ι) (k i j : ι) :
    ∃ a b : ι,
      a ≠ b ∧ a ≠ k ∧ a ≠ i ∧ a ≠ j ∧
        b ≠ k ∧ b ≠ i ∧ b ≠ j := by
  let s : Finset ι := Finset.univ \ {k, i, j}
  have htriple : ({k, i, j} : Finset ι).card ≤ 3 :=
    Finset.card_le_three
  have hs : 2 ≤ s.card := by
    rw [show s = Finset.univ \ {k, i, j} from rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    rw [Finset.card_univ]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (lt_of_lt_of_le (by omega) hs)
  have ha' : a ≠ k ∧ a ≠ i ∧ a ≠ j := by
    simpa [s] using ha
  have hb' : b ≠ k ∧ b ≠ i ∧ b ≠ j := by
    simpa [s] using hb
  exact ⟨a, b, hab, ha'.1, ha'.2.1, ha'.2.2,
    hb'.1, hb'.2.1, hb'.2.2⟩

/-- A sign-covariant three-index tensor vanishes in the stable range.  Notice
that alternation and centring are not needed for this part of the argument. -/
theorem signCovariantThreeTensor_zero_of_five_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 5 ≤ Fintype.card ι) (T : ι → ι → ι → ℂ)
    (hequiv : ∀ (p : Equiv.Perm ι) k i j,
      T (p k) (p i) (p j) =
        ((Equiv.Perm.sign p : ℤ) : ℂ) * T k i j) :
    T = 0 := by
  funext k i j
  change T k i j = 0
  obtain ⟨a, b, hab, hak, hai, haj, hbk, hbi, hbj⟩ :=
    exists_pair_outside_triple hcard k i j
  have h := hequiv (Equiv.swap a b) k i j
  rw [Equiv.swap_apply_of_ne_of_ne hak.symm hbk.symm,
    Equiv.swap_apply_of_ne_of_ne hai.symm hbi.symm,
    Equiv.swap_apply_of_ne_of_ne haj.symm hbj.symm] at h
  rw [Equiv.Perm.sign_swap hab] at h
  norm_num at h
  linear_combination (1 / 2) * h

/-- Consequently every centred alternating coefficient presentation of
`Λ²W → W ⊗ sgn` is zero for `card ι ≥ 5`. -/
theorem standardTwistedExteriorTensor_zero_of_five_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 5 ≤ Fintype.card ι)
    (T : StandardTwistedExteriorTensor ι) :
    T.coeff = 0 :=
  signCovariantThreeTensor_zero_of_five_le hcard T.coeff T.equivariant

/-- Alternation over characteristic zero kills every diagonal coefficient. -/
theorem StandardTwistedExteriorTensor.diagonal_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : StandardTwistedExteriorTensor ι) (k i : ι) :
    T.coeff k i i = 0 := by
  have h := T.alternate k i i
  linear_combination (1 / 2) * h

/-- The exterior square is trivial when the centred standard carrier has
dimension zero (`N = 1`). -/
theorem standardTwistedExteriorTensor_fin_one_zero
    (T : StandardTwistedExteriorTensor (Fin 1)) :
    T.coeff = 0 := by
  funext k i j
  change T.coeff k i j = 0
  fin_cases i
  fin_cases j
  exact T.diagonal_zero k 0

/-- The exterior square is trivial when the centred standard carrier has
dimension one (`N = 2`). -/
theorem standardTwistedExteriorTensor_fin_two_zero
    (T : StandardTwistedExteriorTensor (Fin 2)) :
    T.coeff = 0 := by
  funext k i j
  change T.coeff k i j = 0
  fin_cases i <;> fin_cases j
  · exact T.diagonal_zero k 0
  · have h := T.input_centered k 1
    rw [Fin.sum_univ_two] at h
    rw [T.diagonal_zero k 1] at h
    simpa using h
  · have h := T.input_centered k 0
    rw [Fin.sum_univ_two] at h
    rw [T.diagonal_zero k 0] at h
    simpa using h
  · exact T.diagonal_zero k 1

/-- The sign-twisted exterior-square coefficient space is also zero at
`N = 3`.  The transpositions `(01)` and `(02)`, together with input/output
centring, force the base coefficient triple to vanish; equivariance transports
that conclusion to the other two unordered input pairs. -/
theorem standardTwistedExteriorTensor_fin_three_zero
    (T : StandardTwistedExteriorTensor (Fin 3)) :
    T.coeff = 0 := by
  have h10 : T.coeff 1 0 1 = T.coeff 0 0 1 := by
    have he := T.equivariant (Equiv.swap (0 : Fin 3) 1) 0 0 1
    have ha := T.alternate 1 1 0
    simp [Equiv.Perm.sign_swap', Equiv.swap_apply_of_ne_of_ne] at he
    linear_combination ha - he
  have h20 : T.coeff 2 0 1 = T.coeff 0 0 1 := by
    have he := T.equivariant (Equiv.swap (0 : Fin 3) 2) 2 2 1
    have hc := T.input_centered 2 1
    rw [Fin.sum_univ_three, T.diagonal_zero 2 1] at hc
    simp [Equiv.Perm.sign_swap', Equiv.swap_apply_of_ne_of_ne] at he
    linear_combination -he + hc
  have hz0 : T.coeff 0 0 1 = 0 := by
    have hc := T.output_centered 0 1
    rw [Fin.sum_univ_three, h10, h20] at hc
    linear_combination (1 / 3) * hc
  have hbase : ∀ k : Fin 3, T.coeff k 0 1 = 0 := by
    intro k
    fin_cases k
    · exact hz0
    · simpa [h10] using hz0
    · simpa [h20] using hz0
  have h02 : ∀ k : Fin 3, T.coeff k 0 2 = 0 := by
    intro k
    have he := T.equivariant (Equiv.swap (1 : Fin 3) 2)
      ((Equiv.swap (1 : Fin 3) 2) k) 0 1
    simpa [Equiv.Perm.sign_swap', Equiv.swap_apply_of_ne_of_ne, hbase] using he
  have h12 : ∀ k : Fin 3, T.coeff k 1 2 = 0 := by
    intro k
    have he := T.equivariant (Equiv.swap (0 : Fin 3) 1)
      ((Equiv.swap (0 : Fin 3) 1) k) 0 2
    simpa [Equiv.Perm.sign_swap', Equiv.swap_apply_of_ne_of_ne, h02] using he
  funext k i j
  change T.coeff k i j = 0
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk]
  · exact T.diagonal_zero k 0
  · exact hbase k
  · exact h02 k
  · rw [T.alternate k 1 0, hbase k, neg_zero]
  · exact T.diagonal_zero k 1
  · exact h12 k
  · rw [T.alternate k 2 0, h02 k, neg_zero]
  · rw [T.alternate k 2 1, h12 k, neg_zero]
  · exact T.diagonal_zero k 2

/-- The empty coordinate type has no coefficients. -/
theorem standardTwistedExteriorTensor_fin_zero_zero
    (T : StandardTwistedExteriorTensor (Fin 0)) :
    T.coeff = 0 := by
  funext k
  exact Fin.elim0 k

/-- **All nonexceptional dimensions.**  In the centred coefficient model of
`Hom_{S_N}(Λ²W_N, W_N ⊗ sgn)`, every tensor vanishes unless `N = 4`. -/
theorem standardTwistedExteriorTensor_zero_of_ne_four
    {N : ℕ} (hN : N ≠ 4)
    (T : StandardTwistedExteriorTensor (Fin N)) :
    T.coeff = 0 := by
  by_cases h5 : 5 ≤ N
  · exact standardTwistedExteriorTensor_zero_of_five_le
      (by simpa using h5) T
  · have hcases : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 := by omega
    rcases hcases with h | h | h | h
    · subst N
      exact standardTwistedExteriorTensor_fin_zero_zero T
    · subst N
      exact standardTwistedExteriorTensor_fin_one_zero T
    · subst N
      exact standardTwistedExteriorTensor_fin_two_zero T
    · subst N
      exact standardTwistedExteriorTensor_fin_three_zero T

end NCG
