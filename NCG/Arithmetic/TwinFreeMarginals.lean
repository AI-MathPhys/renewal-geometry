/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Twin-free realization of all sub-half marginals
  (`thm:v003-twinfree-marginals`, arithmetic monograph)

For an admissible tuple `h : Fin k → ℤ`, the twin graph `G₂(ℋ)`
joins `i` and `j` when `|h_i − h_j| = 2`; it is bipartite under the
`mod 4` colouring (`{0,1}` versus `{2,3}`).  Given any marginals
`0 ≤ π_i ≤ 1/2`, `twinfree_marginals` produces an explicit
probability distribution `μ` on subsets of coordinates that is
supported on independent sets of `G₂(ℋ)` and has vertex marginals
exactly `π_i` — the manuscript's construction: pick a side of the
bipartition with probability `1/2`, then include each vertex of
that side independently with probability `2π_i`.

The concluding sentence — that no statistic depending linearly on
one-coordinate marginals can certify a twin edge — is interpretive
prose about this construction.
-/

open Finset

namespace NCG

variable {k : ℕ}

/-- Bernoulli normalization: the side weights sum to one. -/
private lemma bern_total (s : Finset (Fin k)) (f g : Fin k → ℝ)
    (hfg : ∀ i, f i + g i = 1) :
    (∑ S ∈ s.powerset, (∏ i ∈ S, f i) * ∏ i ∈ s \ S, g i) = 1 := by
  rw [← Finset.prod_add,
    show (∏ i ∈ s, (f i + g i)) = ∏ _i ∈ s, (1 : ℝ) from
      Finset.prod_congr rfl fun i _ => hfg i,
    Finset.prod_const_one]

/-- Bernoulli marginal: the total weight of subsets containing a
fixed element `i` of the side is `f i`. -/
private lemma bern_marginal (s : Finset (Fin k)) (f g : Fin k → ℝ)
    (hfg : ∀ i, f i + g i = 1) {i : Fin k} (hi : i ∈ s) :
    (∑ S ∈ s.powerset,
        if i ∈ S then (∏ j ∈ S, f j) * ∏ j ∈ s \ S, g j else 0)
      = f i := by
  classical
  set e : Finset (Fin k) := s.erase i with he
  have hi' : i ∉ e := Finset.notMem_erase i s
  have hs : s = insert i e := (Finset.insert_erase hi).symm
  rw [hs, Finset.sum_powerset_insert hi']
  have hzero : (∑ S ∈ e.powerset,
      if i ∈ S then (∏ j ∈ S, f j) * ∏ j ∈ insert i e \ S, g j
      else 0) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    exact if_neg fun hit => hi' (Finset.mem_powerset.mp ht hit)
  rw [hzero, zero_add]
  have hterm : ∀ t ∈ e.powerset,
      (if i ∈ insert i t then
          (∏ j ∈ insert i t, f j) * ∏ j ∈ insert i e \ insert i t, g j
        else 0)
        = f i * ((∏ j ∈ t, f j) * ∏ j ∈ e \ t, g j) := by
    intro t ht
    have hit : i ∉ t := fun hmem =>
      hi' (Finset.mem_powerset.mp ht hmem)
    have hsd : insert i e \ insert i t = e \ t := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨hx1 | hx1, hx2⟩
        · exact absurd (Or.inl hx1) hx2
        · exact ⟨hx1, fun hxt => hx2 (Or.inr hxt)⟩
      · rintro ⟨hx1, hx2⟩
        refine ⟨Or.inr hx1, ?_⟩
        rintro (rfl | hxt)
        · exact hi' hx1
        · exact hx2 hxt
    rw [if_pos (Finset.mem_insert_self i t),
      Finset.prod_insert hit, hsd, mul_assoc]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    bern_total e f g hfg, mul_one]

/-- The `mod 4` colouring flips across every twin edge. -/
private lemma twin_edge_flip (h : Fin k → ℤ) {i j : Fin k}
    (hij : |h i - h j| = 2) :
    (h i % 4 = 0 ∨ h i % 4 = 1) ↔ ¬(h j % 4 = 0 ∨ h j % 4 = 1) := by
  have habs : h i - h j = 2 ∨ h i - h j = -2 :=
    (abs_eq (by norm_num)).mp hij
  omega

/-- `thm:v003-twinfree-marginals`: every family of marginals
`0 ≤ π_i ≤ 1/2` is realized by a probability distribution supported
on independent sets of the twin graph `G₂(ℋ)`. -/
theorem twinfree_marginals (h : Fin k → ℤ) (π : Fin k → ℝ)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ2 : ∀ i, π i ≤ 1 / 2) :
    ∃ μ : Finset (Fin k) → ℝ,
      (∀ S, 0 ≤ μ S) ∧
      (∑ S : Finset (Fin k), μ S) = 1 ∧
      (∀ S, μ S ≠ 0 → ∀ i ∈ S, ∀ j ∈ S, |h i - h j| ≠ 2) ∧
      (∀ i, (∑ S : Finset (Fin k), if i ∈ S then μ S else 0)
        = π i) := by
  classical
  set A : Finset (Fin k) :=
    Finset.univ.filter fun i => h i % 4 = 0 ∨ h i % 4 = 1 with hA
  set B : Finset (Fin k) :=
    Finset.univ.filter fun i => ¬(h i % 4 = 0 ∨ h i % 4 = 1) with hB
  set f : Fin k → ℝ := fun i => 2 * π i with hf
  set g : Fin k → ℝ := fun i => 1 - 2 * π i with hg
  have hfg : ∀ i, f i + g i = 1 := fun i => by rw [hf, hg]; ring
  have hf0 : ∀ i, 0 ≤ f i := fun i => by
    rw [hf]; linarith [hπ0 i]
  have hg0 : ∀ i, 0 ≤ g i := fun i => by
    rw [hg]; linarith [hπ2 i]
  set w : Finset (Fin k) → Finset (Fin k) → ℝ := fun s S =>
    if S ⊆ s then (∏ j ∈ S, f j) * ∏ j ∈ s \ S, g j else 0 with hw
  -- conversion between the full subset sum and the powerset sum
  have hpows : ∀ s : Finset (Fin k),
      Finset.univ.filter (fun S : Finset (Fin k) => S ⊆ s)
        = s.powerset := by
    intro s
    ext S
    simp [Finset.mem_powerset]
  have hside_total : ∀ s : Finset (Fin k),
      (∑ S : Finset (Fin k), w s S) = 1 := by
    intro s
    have hconv : (∑ S : Finset (Fin k), w s S)
        = ∑ S ∈ s.powerset, (∏ j ∈ S, f j) * ∏ j ∈ s \ S, g j := by
      rw [← hpows s, Finset.sum_filter]
    rw [hconv]
    exact bern_total s f g hfg
  have hside_marg : ∀ s : Finset (Fin k), ∀ i ∈ s,
      (∑ S : Finset (Fin k), if i ∈ S then w s S else 0) = f i := by
    intro s i hi
    have hswap : ∀ S : Finset (Fin k),
        (if i ∈ S then w s S else 0)
          = if S ⊆ s then (if i ∈ S then
              (∏ j ∈ S, f j) * ∏ j ∈ s \ S, g j else 0) else 0 := by
      intro S
      simp only [hw]
      split_ifs <;> rfl
    rw [Finset.sum_congr rfl fun S _ => hswap S, ← Finset.sum_filter,
      hpows s]
    exact bern_marginal s f g hfg hi
  have hside_marg0 : ∀ s : Finset (Fin k), ∀ i, i ∉ s →
      (∑ S : Finset (Fin k), if i ∈ S then w s S else 0) = 0 := by
    intro s i hi
    refine Finset.sum_eq_zero fun S _ => ?_
    by_cases hiS : i ∈ S
    · rw [if_pos hiS, hw]
      by_cases hSs : S ⊆ s
      · exact absurd (hSs hiS) hi
      · exact if_neg hSs
    · exact if_neg hiS
  have hwnn : ∀ s S, 0 ≤ w s S := by
    intro s S
    simp only [hw]
    split_ifs
    · exact mul_nonneg (Finset.prod_nonneg fun j _ => hf0 j)
        (Finset.prod_nonneg fun j _ => hg0 j)
    · exact le_refl 0
  refine ⟨fun S => (w A S + w B S) / 2, ?_, ?_, ?_, ?_⟩
  · -- nonnegativity
    intro S
    simp only []
    have h1 := hwnn A S
    have h2 := hwnn B S
    have h3 : (0 : ℝ) ≤ w A S + w B S := add_nonneg h1 h2
    linarith
  · -- total mass one
    simp only []
    have hsum : (∑ S : Finset (Fin k), (w A S + w B S) / 2)
        = ((∑ S : Finset (Fin k), w A S)
            + ∑ S : Finset (Fin k), w B S) / 2 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_div]
    rw [hsum, hside_total A, hside_total B]
    norm_num
  · -- support on independent sets of the twin graph
    intro S hS i hiS j hjS habs2
    have hsub : S ⊆ A ∨ S ⊆ B := by
      by_contra hcon
      obtain ⟨h1, h2⟩ := not_or.mp hcon
      apply hS
      have hwA : w A S = 0 := by simp only [hw]; exact if_neg h1
      have hwB : w B S = 0 := by simp only [hw]; exact if_neg h2
      simp only []
      rw [hwA, hwB]
      norm_num
    have hflip := twin_edge_flip h habs2
    rcases hsub with hsub | hsub
    · have hiA := (Finset.mem_filter.mp (hA ▸ hsub hiS)).2
      have hjA := (Finset.mem_filter.mp (hA ▸ hsub hjS)).2
      exact (hflip.mp hiA) hjA
    · have hiB := (Finset.mem_filter.mp (hB ▸ hsub hiS)).2
      have hjB := (Finset.mem_filter.mp (hB ▸ hsub hjS)).2
      tauto
  · -- exact marginals
    intro i
    simp only []
    have hsplit : ∀ S : Finset (Fin k),
        (if i ∈ S then (w A S + w B S) / 2 else 0)
          = ((if i ∈ S then w A S else 0)
              + (if i ∈ S then w B S else 0)) / 2 := by
      intro S
      split_ifs <;> norm_num
    rw [Finset.sum_congr rfl fun S _ => hsplit S, ← Finset.sum_div,
      Finset.sum_add_distrib]
    by_cases hiA : h i % 4 = 0 ∨ h i % 4 = 1
    · have hiA' : i ∈ A := by
        rw [hA]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiA⟩
      have hiB' : i ∉ B := by
        rw [hB]
        intro hmem
        exact (Finset.mem_filter.mp hmem).2 hiA
      rw [hside_marg A i hiA', hside_marg0 B i hiB', hf]
      ring
    · have hiA' : i ∉ A := by
        rw [hA]
        intro hmem
        exact hiA (Finset.mem_filter.mp hmem).2
      have hiB' : i ∈ B := by
        rw [hB]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiA⟩
      rw [hside_marg0 A i hiA', hside_marg B i hiB', hf]
      ring

end NCG
