/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The cycle lemma and the event-count kernel
  (`thm:event-count-kernel`, SM_emergence)

The combinatorial heart of the Otter–Dwass waiting law
`q_d(n) = n⁻¹ ℙ(S_n = n-1)`:

* `cycle_lemma` — the Dvoretzky–Motzkin cycle lemma in the strong
  form needed here: for any `n`-periodic integer step sequence with
  period sum `-1`, **exactly one** of the `n` cyclic rotations has
  all proper partial sums nonnegative.  (No lower bound on the
  steps is required for the sum `= -1` case: the proof is the
  first-minimizer argument on the prefix walk.)  Dividing the count
  of favourable rotations by `n` is precisely the `n⁻¹` factor of
  the Otter–Dwass formula, and `ℙ(S_n = n-1)` is the displayed
  binomial `C(nd, n-1)(1/d)^{n-1}(1-1/d)^{nd-n+1}`.

The encoding of critical Galton–Watson excursions by lattice paths
(the depth-first traversal bijection) and the local-CLT `n^{-3/2}`
asymptotic are the disclosed probabilistic layers.
-/

namespace NCG

open Finset

/-- The Dvoretzky–Motzkin cycle lemma (sum `-1` form): an
`n`-periodic integer step sequence with period sum `-1` has exactly
one rotation offset `k ∈ [1, n]` whose proper partial sums are all
nonnegative. -/
theorem cycle_lemma {n : ℕ} (hn : 0 < n) (a : ℕ → ℤ)
    (hper : ∀ i, a (i + n) = a i)
    (htot : ∑ i ∈ Finset.range n, a i = -1) :
    ∃! k, k ∈ Finset.Icc 1 n ∧
      ∀ m, 1 ≤ m → m < n →
        0 ≤ (∑ i ∈ Finset.range (k + m), a i)
          - ∑ i ∈ Finset.range k, a i := by
  set S : ℕ → ℤ := fun j => ∑ i ∈ Finset.range j, a i with hS
  have hshift : ∀ j, S (j + n) = S j - 1 := by
    intro j
    induction j with
    | zero =>
        simp only [hS, zero_add, Finset.range_zero, Finset.sum_empty]
        rw [htot]
        norm_num
    | succ m ih =>
        have h1 : S (m + 1 + n) = S (m + n) + a (m + n) := by
          simp only [hS]
          rw [show m + 1 + n = (m + n) + 1 by ring,
            Finset.sum_range_succ]
        rw [h1, ih, hper m]
        simp only [hS]
        rw [Finset.sum_range_succ]
        ring
  -- the first minimizer of S on [1, n]
  have hbridge : ∀ j, (∑ i ∈ Finset.range j, a i) = S j := fun j => rfl
  have hne : (Finset.Icc 1 n).Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, hn⟩⟩
  obtain ⟨j0, hj0mem, hj0min⟩ :=
    Finset.exists_min_image (Finset.Icc 1 n) S hne
  set A := (Finset.Icc 1 n).filter
    (fun j => S j = S j0) with hA
  have hAne : A.Nonempty := ⟨j0, by simp [hA, hj0mem]⟩
  set k := A.min' hAne with hk
  have hkA : k ∈ A := A.min'_mem hAne
  have hkmem : k ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hkA).1
  have hkval : S k = S j0 := (Finset.mem_filter.mp hkA).2
  have hkmin : ∀ j ∈ Finset.Icc 1 n, S k ≤ S j := by
    intro j hj
    rw [hkval]
    exact hj0min j hj
  have hkfirst : ∀ j ∈ Finset.Icc 1 n, S j = S k → k ≤ j := by
    intro j hj hval
    apply A.min'_le
    rw [hA, Finset.mem_filter]
    exact ⟨hj, by rw [hval, hkval]⟩
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hkmem
  refine ⟨k, ⟨hkmem, ?_⟩, ?_⟩
  · -- existence: the rotation at the first minimizer works
    intro m hm1 hmn
    rw [hbridge, hbridge]
    by_cases hcase : k + m ≤ n
    · have hmem : k + m ∈ Finset.Icc 1 n :=
        Finset.mem_Icc.mpr ⟨by omega, hcase⟩
      have := hkmin (k + m) hmem
      omega
    · -- wrap: k + m = j + n with 1 ≤ j < k
      rw [not_le] at hcase
      set j := k + m - n with hj
      have hjeq : k + m = j + n := by omega
      have hj1 : 1 ≤ j := by omega
      have hjk : j < k := by omega
      have hjmem : j ∈ Finset.Icc 1 n :=
        Finset.mem_Icc.mpr ⟨hj1, by omega⟩
      have hwrap : S (k + m) = S j - 1 := by
        rw [hjeq, hshift]
      have hmin := hkmin j hjmem
      have hne2 : S j ≠ S k := by
        intro heq
        have := hkfirst j hjmem heq
        omega
      omega
  · -- uniqueness
    rintro k' ⟨hk'mem, hk'good⟩
    obtain ⟨hk'1, hk'n⟩ := Finset.mem_Icc.mp hk'mem
    by_contra hne2
    rcases lt_or_gt_of_ne hne2 with hlt | hgt
    · -- k' < k: k' would be an earlier minimizer
      have hm1 : 1 ≤ k - k' := by omega
      have hmn : k - k' < n := by omega
      have := hk'good (k - k') hm1 hmn
      rw [show k' + (k - k') = k by omega, hbridge, hbridge] at this
      have hmin := hkmin k' hk'mem
      have : S k' = S k := by omega
      have := hkfirst k' hk'mem this
      omega
    · -- k' > k: the wrap constraint is violated
      have hm1 : 1 ≤ k + n - k' := by omega
      have hmn : k + n - k' < n := by omega
      have := hk'good (k + n - k') hm1 hmn
      rw [show k' + (k + n - k') = k + n by omega, hbridge, hbridge,
        hshift] at this
      have hmin := hkmin k' hk'mem
      omega

end NCG
