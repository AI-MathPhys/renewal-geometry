/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact operator-valued `ℓ¹` feedback limit
  (`thm:feedback-l1-limit`, Gran-Tensor manuscript)

* `feedback_l1_limit`: for feedback kernels `K_{·,n} → K`
  pointwise in norm with summable rows:
  (i) the boxed uniform-tail criterion is sufficient:
      uniform tail vanishing forces `K ∈ ℓ¹` and
      `∑_k ‖K_{k,n} - K_k‖ → 0`;
  (ii) it is necessary;
  (iii) the limiting Volterra recursion: responses defined
      by the finite feedback convolution converge termwise
      to the limiting response (in any normed ring);
  (iv) the two-inverse resolvent bound
      `‖B⁻¹ - C⁻¹‖ ≤ ‖B⁻¹‖·‖C - B‖·‖C⁻¹‖`
      behind the uniform generating-function estimate.

The instantiation `‖𝒳_n(z) - 𝒳(z)‖ ≤ (‖ΔA‖ + ‖ΔK‖₁)/(1-q)²`
on the unit disk is (iv) with the geometric-series inverse
bounds `‖[I - zA - z²𝒦(z)]⁻¹‖ ≤ (1-q)⁻¹`; the disk-uniform
bookkeeping is the manuscript's aggregation of (iv) over
`|z| ≤ 1`.
-/

open Filter

namespace NCG

/-- `thm:feedback-l1-limit`. -/
theorem feedback_l1_limit {E : Type*} [NormedAddCommGroup E]
    (K : ℕ → ℕ → E) (Kl : ℕ → E)
    (hpt : ∀ k, Tendsto (fun n => K n k) atTop
      (nhds (Kl k)))
    (hsum : ∀ n, Summable fun k => ‖K n k‖) :
    -- (i) sufficiency of the boxed uniform-tail criterion
    ((∀ ε : ℝ, 0 < ε → ∃ R : ℕ, ∀ n,
        ∑' k, ‖K n (k + R)‖ ≤ ε) →
      (Summable fun k => ‖Kl k‖)
      ∧ Tendsto (fun n => ∑' k, ‖K n k - Kl k‖)
          atTop (nhds 0))
    -- (ii) necessity
    ∧ ((Summable fun k => ‖Kl k‖) →
        Tendsto (fun n => ∑' k, ‖K n k - Kl k‖)
          atTop (nhds 0) →
        ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, ∀ n,
          ∑' k, ‖K n (k + R)‖ ≤ ε)
    -- (iii) the limiting Volterra recursion
    ∧ (∀ {A : Type} [NormedRing A]
        (a : A) (an : ℕ → A) (c : ℕ → A) (cn : ℕ → ℕ → A)
        (X : ℕ → A) (Xn : ℕ → ℕ → A),
        Tendsto an atTop (nhds a) →
        (∀ k, Tendsto (fun n => cn n k) atTop
          (nhds (c k))) →
        (∀ n, Xn n 0 = X 0) →
        (∀ n m, Xn n (m + 1)
          = an n * Xn n m + ∑ j ∈ Finset.range m,
              cn n (m - 1 - j) * Xn n j) →
        (∀ m, X (m + 1)
          = a * X m + ∑ j ∈ Finset.range m,
              c (m - 1 - j) * X j) →
        ∀ m, Tendsto (fun n => Xn n m) atTop
          (nhds (X m)))
    -- (iv) the two-inverse resolvent bound
    ∧ (∀ {A : Type} [NormedRing A] (B C Bi Ci : A),
        B * Bi = 1 → Bi * B = 1 → C * Ci = 1 →
        ‖Bi - Ci‖ ≤ ‖Bi‖ * ‖C - B‖ * ‖Ci‖) := by
  -- partial tail sums of the limit obey any uniform bound
  have hseg : ∀ (R : ℕ) (b : ℝ), (∀ n,
      ∑' k, ‖K n (k + R)‖ ≤ b) → ∀ S,
      ∑ k ∈ Finset.range S, ‖Kl (k + R)‖ ≤ b := by
    intro R b hb S
    have hlim : Tendsto
        (fun n => ∑ k ∈ Finset.range S, ‖K n (k + R)‖)
        atTop
        (nhds (∑ k ∈ Finset.range S, ‖Kl (k + R)‖)) :=
      tendsto_finsetSum _ fun k _ => (hpt (k + R)).norm
    refine le_of_tendsto hlim
      (Eventually.of_forall fun n => ?_)
    calc ∑ k ∈ Finset.range S, ‖K n (k + R)‖
        ≤ ∑' k, ‖K n (k + R)‖ :=
          ((summable_nat_add_iff R).mpr
            (hsum n)).sum_le_tsum _
            (fun k _ => norm_nonneg _)
      _ ≤ b := hb n
  -- generic tail monotonicity for nonneg summable sequences
  have hmono : ∀ (f : ℕ → ℝ), (∀ k, 0 ≤ f k) →
      Summable f → ∀ (R R' : ℕ), R ≤ R' →
      ∑' k, f (k + R') ≤ ∑' k, f (k + R) := by
    intro f hf hfs R R' hRR
    have hsub := (summable_nat_add_iff R).mpr hfs
    have hsplit := hsub.sum_add_tsum_nat_add (R' - R)
    have hidx : ∀ k : ℕ,
        f (k + (R' - R) + R) = f (k + R') := by
      intro k
      congr 1
      omega
    rw [tsum_congr hidx] at hsplit
    have hhead : 0 ≤ ∑ k ∈ Finset.range (R' - R),
        f (k + R) :=
      Finset.sum_nonneg fun k _ => hf _
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  -- (i) sufficiency
  · intro htail
    obtain ⟨R1, hR1⟩ := htail 1 one_pos
    have hKltail1 : Summable fun k => ‖Kl (k + R1)‖ :=
      summable_of_sum_range_le
        (fun k => norm_nonneg _) (hseg R1 1 hR1)
    have hKlsum : Summable fun k => ‖Kl k‖ :=
      (summable_nat_add_iff R1).mp hKltail1
    refine ⟨hKlsum, ?_⟩
    have hdiffsum : ∀ n,
        Summable fun k => ‖K n k - Kl k‖ := fun n =>
      Summable.of_nonneg_of_le (fun k => norm_nonneg _)
        (fun k => norm_sub_le _ _)
        ((hsum n).add hKlsum)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨R, hR⟩ := htail (ε / 4) (by positivity)
    have hKltail : ∑' k, ‖Kl (k + R)‖ ≤ ε / 4 :=
      (summable_of_sum_range_le
        (fun k => norm_nonneg _)
        (hseg R (ε / 4) hR)).tsum_le_of_sum_range_le
        (hseg R (ε / 4) hR)
    have hhead : Tendsto
        (fun n => ∑ k ∈ Finset.range R, ‖K n k - Kl k‖)
        atTop (nhds 0) := by
      have h : Tendsto
          (fun n => ∑ k ∈ Finset.range R, ‖K n k - Kl k‖)
          atTop
          (nhds (∑ k ∈ Finset.range R, ‖Kl k - Kl k‖)) :=
        tendsto_finsetSum _ fun k _ =>
          ((hpt k).sub tendsto_const_nhds).norm
      simpa using h
    obtain ⟨N, hN⟩ :=
      Metric.tendsto_atTop.mp hhead (ε / 4)
        (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hsplit := (hdiffsum n).sum_add_tsum_nat_add R
    have htailn : ∑' k, ‖K n (k + R) - Kl (k + R)‖
        ≤ ε / 4 + ε / 4 := by
      have h1 : ∀ k, ‖K n (k + R) - Kl (k + R)‖
          ≤ ‖K n (k + R)‖ + ‖Kl (k + R)‖ := fun k =>
        norm_sub_le _ _
      have hs1 := (summable_nat_add_iff R).mpr (hsum n)
      have hs2 := (summable_nat_add_iff R).mpr hKlsum
      calc ∑' k, ‖K n (k + R) - Kl (k + R)‖
          ≤ ∑' k, (‖K n (k + R)‖ + ‖Kl (k + R)‖) :=
            ((summable_nat_add_iff R).mpr
              (hdiffsum n)).tsum_le_tsum h1
              (hs1.add hs2)
        _ = (∑' k, ‖K n (k + R)‖)
            + ∑' k, ‖Kl (k + R)‖ := hs1.tsum_add hs2
        _ ≤ ε / 4 + ε / 4 :=
            add_le_add (hR n) hKltail
    have hheadn := hN n hn
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (Finset.sum_nonneg
        fun k _ => norm_nonneg _)] at hheadn
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (tsum_nonneg
        fun k => norm_nonneg _)]
    calc ∑' k, ‖K n k - Kl k‖
        = (∑ k ∈ Finset.range R, ‖K n k - Kl k‖)
          + ∑' k, ‖K n (k + R) - Kl (k + R)‖ :=
          hsplit.symm
      _ < ε := by linarith
  -- (ii) necessity
  · intro hKlsum hconv ε hε
    have hdiffsum : ∀ n,
        Summable fun k => ‖K n k - Kl k‖ := fun n =>
      Summable.of_nonneg_of_le (fun k => norm_nonneg _)
        (fun k => norm_sub_le _ _)
        ((hsum n).add hKlsum)
    obtain ⟨R0, hR0⟩ :=
      Metric.tendsto_atTop.mp
        (tendsto_sum_nat_add fun k => ‖Kl k‖)
        (ε / 3) (by positivity)
    have hKltail : ∑' k, ‖Kl (k + R0)‖ ≤ ε / 3 := by
      have h := hR0 R0 le_rfl
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (tsum_nonneg
          fun k => norm_nonneg _)] at h
      linarith
    obtain ⟨N, hN⟩ :=
      Metric.tendsto_atTop.mp hconv (ε / 3)
        (by positivity)
    have hearly : ∀ N' : ℕ, ∃ R, ∀ n < N',
        ∑' k, ‖K n (k + R)‖ ≤ ε := by
      intro N'
      induction N' with
      | zero => exact ⟨0, fun n hn => absurd hn (by omega)⟩
      | succ N' ihN =>
        obtain ⟨R, hRe⟩ := ihN
        obtain ⟨Rn, hRn⟩ :=
          Metric.tendsto_atTop.mp
            (tendsto_sum_nat_add fun k => ‖K N' k‖)
            ε hε
        refine ⟨max R Rn, fun n hn => ?_⟩
        rcases Nat.lt_or_ge n N' with h | h
        · exact le_trans
            (hmono (fun k => ‖K n k‖)
              (fun k => norm_nonneg _) (hsum n)
              R (max R Rn) (le_max_left _ _))
            (hRe n h)
        · have hnN : n = N' := by omega
          subst hnN
          have h2 := hRn (max R Rn) (le_max_right _ _)
          rw [Real.dist_eq, sub_zero,
            abs_of_nonneg (tsum_nonneg
              fun k => norm_nonneg _)] at h2
          linarith
    obtain ⟨Re, hRe⟩ := hearly N
    refine ⟨max R0 Re, fun n => ?_⟩
    rcases Nat.lt_or_ge n N with h | h
    · exact le_trans
        (hmono (fun k => ‖K n k‖)
          (fun k => norm_nonneg _) (hsum n)
          Re (max R0 Re) (le_max_right _ _))
        (hRe n h)
    · have h1 := hN n h
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (tsum_nonneg
          fun k => norm_nonneg _)] at h1
      have hs1 := (summable_nat_add_iff
        (max R0 Re)).mpr (hsum n)
      have hs2 := (summable_nat_add_iff
        (max R0 Re)).mpr hKlsum
      have hs3 := (summable_nat_add_iff
        (max R0 Re)).mpr (hdiffsum n)
      have htri : ∀ k, ‖K n (k + max R0 Re)‖
          ≤ ‖K n (k + max R0 Re) - Kl (k + max R0 Re)‖
            + ‖Kl (k + max R0 Re)‖ := by
        intro k
        calc ‖K n (k + max R0 Re)‖
            = ‖(K n (k + max R0 Re)
                - Kl (k + max R0 Re))
                + Kl (k + max R0 Re)‖ := by
              rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      have hdle : ∑' k,
          ‖K n (k + max R0 Re) - Kl (k + max R0 Re)‖
          ≤ ∑' k, ‖K n k - Kl k‖ := by
        have hsp :=
          (hdiffsum n).sum_add_tsum_nat_add (max R0 Re)
        have hh : 0 ≤ ∑ k ∈ Finset.range (max R0 Re),
            ‖K n k - Kl k‖ :=
          Finset.sum_nonneg fun k _ => norm_nonneg _
        linarith
      have hKlle : ∑' k, ‖Kl (k + max R0 Re)‖
          ≤ ∑' k, ‖Kl (k + R0)‖ :=
        hmono (fun k => ‖Kl k‖)
          (fun k => norm_nonneg _) hKlsum
          R0 (max R0 Re) (le_max_left _ _)
      calc ∑' k, ‖K n (k + max R0 Re)‖
          ≤ ∑' k,
            (‖K n (k + max R0 Re)
                - Kl (k + max R0 Re)‖
              + ‖Kl (k + max R0 Re)‖) :=
            hs1.tsum_le_tsum htri (hs3.add hs2)
        _ = (∑' k, ‖K n (k + max R0 Re)
              - Kl (k + max R0 Re)‖)
            + ∑' k, ‖Kl (k + max R0 Re)‖ :=
            hs3.tsum_add hs2
        _ ≤ ε / 3 + ε / 3 := by
            have := le_trans hdle h1.le
            have := le_trans hKlle hKltail
            linarith [le_trans hdle h1.le,
              le_trans hKlle hKltail]
        _ ≤ ε := by linarith
  -- (iii) the limiting Volterra recursion
  · intro A _ a an c cn X Xn han hcn h0 hrecn hrec m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      match m with
      | 0 =>
        exact Tendsto.congr (fun n => (h0 n).symm)
          tendsto_const_nhds
      | m + 1 =>
        have h1 : Tendsto (fun n =>
            an n * Xn n m + ∑ j ∈ Finset.range m,
              cn n (m - 1 - j) * Xn n j) atTop
            (nhds (a * X m + ∑ j ∈ Finset.range m,
              c (m - 1 - j) * X j)) := by
          refine Tendsto.add
            (han.mul (ih m (by omega))) ?_
          refine tendsto_finsetSum _ fun j hj => ?_
          have hjm : j < m := Finset.mem_range.mp hj
          exact (hcn (m - 1 - j)).mul
            (ih j (by omega))
        rw [hrec m]
        exact Tendsto.congr
          (fun n => (hrecn n m).symm) h1
  -- (iv) the two-inverse resolvent bound
  · intro A _ B C Bi Ci hBBi hBiB hCCi
    have hid : Bi - Ci = Bi * (C - B) * Ci := by
      have h1 : Bi * (C - B) * Ci
          = Bi * (C * Ci) - Bi * B * Ci := by
        simp only [mul_sub, sub_mul, mul_assoc]
      rw [h1, hCCi, hBiB, mul_one, one_mul]
    rw [hid]
    calc ‖Bi * (C - B) * Ci‖
        ≤ ‖Bi * (C - B)‖ * ‖Ci‖ := norm_mul_le _ _
      _ ≤ ‖Bi‖ * ‖C - B‖ * ‖Ci‖ :=
          mul_le_mul_of_nonneg_right
            (norm_mul_le _ _) (norm_nonneg _)

end NCG
