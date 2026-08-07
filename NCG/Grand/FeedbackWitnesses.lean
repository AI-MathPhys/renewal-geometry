/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Temporal-tail and rank-growth witnesses
  (`thm:feedback-witnesses`, Gran-Tensor manuscript)

* `feedback_witnesses`: for escaping delay windows carrying
  mass at least `ε`:
  (T1)/(T2) after passing to the window maxima `M j`,
  either an atomic delayed route survives (`M j ≥ η`
  frequently) or the escape is diffuse (`M j → 0`), and in
  the diffuse case the window cardinalities blow up
  (`|I_j| → ∞`);
  (iii) in finite input dimension one normalized input
  direction detects the fraction `ε/d` of every packet
  (pigeonhole);
  (iv) the boxed Hankel witness: a memory of dimension `M`
  factors every finite Hankel block through `ℂ^M`, so its
  rank is at most `M` — a block of larger rank
  (equivalently `σ_{M+1} > 0`) excludes every
  `M`-dimensional recurrent memory.

The extraction of the escaping intervals from the failure
of uniform `ℓ¹` tightness is the negation bookkeeping of
`NCG.feedback_l1_limit` (ii); the singular-vector form of
the witness is the Eckart–Young reading of (iv).
-/

open Filter

namespace NCG

/-- `thm:feedback-witnesses`. -/
theorem feedback_witnesses
    (a : ℕ → ℕ → ℝ) (s : ℕ → Finset ℕ) (ε : ℝ)
    (hε : 0 < ε) (hnn : ∀ j k, 0 ≤ a j k)
    (hne : ∀ j, (s j).Nonempty)
    (hmass : ∀ j, ε ≤ ∑ k ∈ s j, a j k) :
    -- (T1)/(T2) dichotomy for the window maxima
    (Tendsto (fun j => (s j).sup' (hne j) (a j)) atTop
        (nhds 0)
      ∨ ∃ η > 0, ∀ J, ∃ j ≥ J,
          η ≤ (s j).sup' (hne j) (a j))
    -- diffuse escape blows up the window cardinality
    ∧ (Tendsto (fun j => (s j).sup' (hne j) (a j)) atTop
        (nhds 0) →
        Tendsto (fun j => ((s j).card : ℝ)) atTop atTop)
    -- pigeonhole input direction
    ∧ (∀ {d : ℕ} (f : Fin d → ℝ), (∀ i, 0 ≤ f i) →
        ε ≤ ∑ i, f i → ∃ i, ε / d ≤ f i)
    -- the boxed Hankel rank witness
    ∧ (∀ {p q r : Type} [Fintype p] [Fintype q] [Fintype r]
        [DecidableEq r] (Hm : Matrix p q ℂ)
        (O : Matrix p r ℂ) (Cc : Matrix r q ℂ),
        Hm = O * Cc → Hm.rank ≤ Fintype.card r) := by
  have hM0 : ∀ j, 0 < (s j).sup' (hne j) (a j) ∨
      0 ≤ (s j).sup' (hne j) (a j) := by
    intro j
    right
    obtain ⟨k, hk⟩ := hne j
    exact le_trans (hnn j k) (Finset.le_sup' (a j) hk)
  have hMnn : ∀ j, 0 ≤ (s j).sup' (hne j) (a j) := by
    intro j
    obtain ⟨k, hk⟩ := hne j
    exact le_trans (hnn j k) (Finset.le_sup' (a j) hk)
  have hcardM : ∀ j, ε ≤ ((s j).card : ℝ)
      * (s j).sup' (hne j) (a j) := by
    intro j
    calc ε ≤ ∑ k ∈ s j, a j k := hmass j
      _ ≤ (s j).card • (s j).sup' (hne j) (a j) :=
        Finset.sum_le_card_nsmul _ _ _
          (fun k hk => Finset.le_sup' (a j) hk)
      _ = ((s j).card : ℝ)
          * (s j).sup' (hne j) (a j) := by
        rw [nsmul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases h : Tendsto
        (fun j => (s j).sup' (hne j) (a j)) atTop (nhds 0)
    · exact Or.inl h
    · right
      rw [Metric.tendsto_atTop] at h
      push Not at h
      obtain ⟨η, hη, hfreq⟩ := h
      refine ⟨η, hη, fun J => ?_⟩
      obtain ⟨j, hjJ, hdist⟩ := hfreq J
      refine ⟨j, hjJ, ?_⟩
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (hMnn j)] at hdist
      exact hdist
  · intro hdif
    rw [tendsto_atTop]
    intro C
    have hδ : (0 : ℝ) < ε / (max C 1) := by
      have : (0 : ℝ) < max C 1 :=
        lt_of_lt_of_le one_pos (le_max_right C 1)
      positivity
    obtain ⟨J, hJ⟩ :=
      Metric.tendsto_atTop.mp hdif (ε / max C 1) hδ
    refine Eventually.mono
      (eventually_ge_atTop J) fun j hj => ?_
    have hMj := hJ j hj
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (hMnn j)] at hMj
    have hMpos : 0 < (s j).sup' (hne j) (a j) := by
      by_contra hle
      push Not at hle
      have := hcardM j
      nlinarith [Nat.cast_nonneg (α := ℝ) (s j).card]
    have hmax1 : (0 : ℝ) < max C 1 :=
      lt_of_lt_of_le one_pos (le_max_right C 1)
    have hcd := hcardM j
    -- card ≥ ε / M > max C 1 ≥ C
    have h1 : ε / (s j).sup' (hne j) (a j)
        ≤ ((s j).card : ℝ) :=
      (div_le_iff₀ hMpos).mpr hcd
    have h2 : max C 1 < ε / (s j).sup' (hne j) (a j) := by
      rw [lt_div_iff₀ hMpos]
      have h3 : (s j).sup' (hne j) (a j)
          < ε / max C 1 := hMj
      calc max C 1 * (s j).sup' (hne j) (a j)
          < max C 1 * (ε / max C 1) := by
            exact mul_lt_mul_of_pos_left h3 hmax1
        _ = ε := by field_simp
    calc C ≤ max C 1 := le_max_left C 1
      _ ≤ ((s j).card : ℝ) := by linarith
  · intro d f hf hsum
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      simp only [Finset.univ_eq_empty,
        Finset.sum_empty] at hsum
      linarith
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    by_contra hno
    push Not at hno
    have hlt : ∑ i, f i < ∑ _i : Fin d, ε / d := by
      refine Finset.sum_lt_sum_of_nonempty ?_
        fun i _ => hno i
      exact Finset.univ_nonempty
    rw [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hlt
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have : (d : ℝ) * (ε / d) = ε := by field_simp
    linarith
  · intro p q r _ _ _ _ Hm O Cc hfac
    rw [hfac]
    calc (O * Cc).rank ≤ O.rank :=
        Matrix.rank_mul_le_left O Cc
      _ ≤ Fintype.card r := Matrix.rank_le_card_width O

end NCG
