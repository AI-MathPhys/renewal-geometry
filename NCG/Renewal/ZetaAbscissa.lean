/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Renewal.Dimensions

/-!
# The zeta abscissa of the predictive length spectrum

Closes conclusion (b) of `thm:triple` (with the corresponding riders
of `cor:sharp-existence` and `cor:automatic-triples`): the abscissa
of convergence of the predictive zeta function
`ζ_CP(s) = Σ_{[w]} Λ_min([w])^{−s}` is exactly the algebraic
predictive dimension — the polynomial growth exponent of the channel
count `N_CP(R)`.

The two-sided characterization is proved for an abstract `ℕ`-valued
length function with finite shells:

* `zetaSum` — the Dirichlet sum in `ℝ≥0∞` (always defined);
* `zetaSum_lt_top_of_growth` — **convergence above the growth
  exponent**: if `N(R) ≤ C·R^a` then `ζ(s) < ∞` for every `s > a`,
  by the dyadic-block estimate
  `Σ_{2^k ≤ n < 2^{k+1}} c_n n^{−s} ≤ N(2^{k+1})·2^{−ks}` and the
  geometric series;
* `zetaSum_eq_top_of_growth_lower` — **divergence below the growth
  exponent**: if `R^a ≤ N(R)` for arbitrarily large `R`, then
  `ζ(s) = ∞` for every `0 ≤ s < a`, since the shell partial sum
  already exceeds `N(R)·R^{−s} ≥ R^{a−s}`.

Together: `abscissa(ζ_CP) = q_alg`, the exponent in
`def:qalg` / `algebraicDimension`.  The renewal instantiation
(`RenewalMemory.zeta`, `zeta_lt_top_of_channelCount_growth`,
`zeta_eq_top_of_channelCount_lower`) runs over the nonunit classes
(the length-zero classes are the kernel modes of `D_CP`, excluded
from the Dirichlet spectrum as usual) against the channel count
`N_CP` via `channelCount_split`.
-/

namespace NCG

open scoped ENNReal NNReal

section Abstract

variable {ι : Type*} (Λ : ι → ℕ)

/-- The Dirichlet sum of the length spectrum, valued in `ℝ≥0∞`. -/
noncomputable def zetaSum (s : ℝ) : ℝ≥0∞ :=
  ∑' i, ((Λ i : ℝ≥0∞)) ^ (-s)

variable (hΛ1 : ∀ i, 1 ≤ Λ i)
variable (hfin : ∀ n : ℕ, {i | Λ i ≤ n}.Finite)

/-- The exact-length fibre count `c_n`. -/
noncomputable def lengthCount (n : ℕ) : ℕ := {i | Λ i = n}.ncard

/-- The cumulative count `N(R)`. -/
noncomputable def lengthShellCount (R : ℕ) : ℕ := {i | Λ i ≤ R}.ncard

include hfin in
theorem lengthFibre_finite (n : ℕ) : {i | Λ i = n}.Finite :=
  (hfin n).subset fun _ h => le_of_eq h

include hfin in
/-- `N(R)` is the sum of the fibre counts. -/
theorem lengthShellCount_eq_sum (R : ℕ) :
    lengthShellCount Λ R
      = ∑ n ∈ Finset.range (R + 1), lengthCount Λ n := by
  induction R with
  | zero =>
      rw [Finset.sum_range_one]
      unfold lengthShellCount lengthCount
      congr 1
      ext i
      simp []
  | succ R ih =>
      have hsplit : {i | Λ i ≤ R + 1}
          = {i | Λ i ≤ R} ∪ {i | Λ i = R + 1} := by
        ext i
        simp only [Set.mem_setOf_eq, Set.mem_union]
        omega
      have hdisj : Disjoint {i | Λ i ≤ R} {i | Λ i = R + 1} := by
        rw [Set.disjoint_iff_inter_eq_empty]
        ext i
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq,
          Set.mem_empty_iff_false, iff_false]
        omega
      unfold lengthShellCount
      rw [hsplit, Set.ncard_union_eq hdisj (hfin R)
        (lengthFibre_finite Λ hfin (R + 1)),
        Finset.sum_range_succ, ← ih]
      rfl

include hΛ1 in
theorem lengthCount_zero : lengthCount Λ 0 = 0 := by
  unfold lengthCount
  convert Set.ncard_empty ι
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  have := hΛ1 i
  omega

include hfin in
/-- Fibre decomposition of the Dirichlet sum:
`ζ(s) = Σ_n c_n · n^{−s}`. -/
theorem zetaSum_eq_sum_lengthCount (s : ℝ) :
    zetaSum Λ s
      = ∑' n : ℕ, (lengthCount Λ n : ℝ≥0∞) * ((n : ℝ≥0∞)) ^ (-s)
    := by
  unfold zetaSum
  rw [← ENNReal.tsum_fiberwise (fun i => ((Λ i : ℝ≥0∞)) ^ (-s)) Λ]
  refine tsum_congr fun n => ?_
  have hconst : ∀ i : (Λ ⁻¹' {n} : Set ι),
      ((Λ i.1 : ℝ≥0∞)) ^ (-s) = ((n : ℝ≥0∞)) ^ (-s) := by
    rintro ⟨i, hi⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hi
    rw [hi]
  have hfibre : (Λ ⁻¹' {n} : Set ι).Finite := lengthFibre_finite Λ hfin n
  haveI := hfibre.fintype
  have hc : (Finset.univ : Finset (Λ ⁻¹' {n} : Set ι)).card
      = lengthCount Λ n := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    rfl
  rw [tsum_congr hconst, tsum_fintype, Finset.sum_const, nsmul_eq_mul,
    hc]

end Abstract

section Convergence

variable {ι : Type*} (Λ : ι → ℕ)
variable (hΛ1 : ∀ i, 1 ≤ Λ i)
variable (hfin : ∀ n : ℕ, {i | Λ i ≤ n}.Finite)

include hΛ1 hfin in
/-- **Convergence above the growth exponent** (`thm:triple` (b),
upper half): a polynomial channel-count bound `N(R) ≤ C·R^a` makes
the predictive zeta finite for every `s > a` — the dyadic-block
estimate against the geometric series. -/
theorem zetaSum_lt_top_of_growth (C : ℝ≥0) {a s : ℝ} (ha : 0 ≤ a)
    (hN : ∀ R : ℕ, 1 ≤ R →
      (lengthShellCount Λ R : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (R : ℝ≥0∞) ^ a)
    (hs : a < s) :
    zetaSum Λ s < ⊤ := by
  set f : ℕ → ℝ≥0∞ :=
    fun n => (lengthCount Λ n : ℝ≥0∞) * ((n : ℝ≥0∞)) ^ (-s) with hf
  rw [zetaSum_eq_sum_lengthCount Λ hfin s]
  -- the dyadic block bound
  set r : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (a - s) with hr
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  have h2zero : (2 : ℝ≥0∞) ≠ 0 := by simp
  have hrlt : r < 1 := by
    rw [hr]
    exact ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (by linarith)
  have hblock : ∀ k : ℕ,
      ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), f n
        ≤ (C : ℝ≥0∞) * (2 : ℝ≥0∞) ^ a * r ^ k := by
    intro k
    have hpow_ne : ((2 : ℕ) ^ k : ℝ≥0∞) ≠ 0 := by
      simp []
    have hstep1 : ∀ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        f n ≤ (lengthCount Λ n : ℝ≥0∞)
          * (((2 : ℕ) ^ k : ℝ≥0∞)) ^ (-s) := by
      intro n hn
      obtain ⟨hn1, _⟩ := Finset.mem_Ico.mp hn
      refine mul_le_mul' le_rfl ?_
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      refine ENNReal.inv_le_inv.mpr ?_
      exact ENNReal.rpow_le_rpow (by exact_mod_cast hn1)
        (le_of_lt (lt_of_le_of_lt ha hs))
    calc ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), f n
        ≤ ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
            (lengthCount Λ n : ℝ≥0∞)
              * (((2 : ℕ) ^ k : ℝ≥0∞)) ^ (-s) :=
          Finset.sum_le_sum hstep1
      _ = (∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
            (lengthCount Λ n : ℝ≥0∞))
              * (((2 : ℕ) ^ k : ℝ≥0∞)) ^ (-s) := by
          rw [Finset.sum_mul]
      _ ≤ (lengthShellCount Λ (2 ^ (k + 1)) : ℝ≥0∞)
              * (((2 : ℕ) ^ k : ℝ≥0∞)) ^ (-s) := by
          refine mul_le_mul' ?_ le_rfl
          rw [lengthShellCount_eq_sum Λ hfin]
          rw [show ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
              (lengthCount Λ n : ℝ≥0∞)
            = ((∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
                lengthCount Λ n : ℕ) : ℝ≥0∞) from by push_cast; rfl]
          refine Nat.cast_le.mpr ?_
          refine Finset.sum_le_sum_of_subset ?_
          intro n hn
          obtain ⟨_, hn2⟩ := Finset.mem_Ico.mp hn
          exact Finset.mem_range.mpr (by omega)
      _ ≤ ((C : ℝ≥0∞) * ((2 : ℕ) ^ (k + 1) : ℝ≥0∞) ^ a)
              * (((2 : ℕ) ^ k : ℝ≥0∞)) ^ (-s) := by
          refine mul_le_mul' ?_ le_rfl
          have h := hN (2 ^ (k + 1)) (Nat.one_le_two_pow)
          rwa [show (((2 ^ (k + 1) : ℕ) : ℝ≥0∞))
              = ((2 : ℕ) : ℝ≥0∞) ^ (k + 1) from by push_cast; rfl] at h
      _ ≤ (C : ℝ≥0∞) * (2 : ℝ≥0∞) ^ a * r ^ k := by
          rw [hr]
          have h1 : ((2 : ℕ) ^ (k + 1) : ℝ≥0∞) ^ a
              = (2 : ℝ≥0∞) ^ a * ((2 : ℝ≥0∞) ^ (a * k)) := by
            push_cast
            rw [← ENNReal.rpow_natCast (2 : ℝ≥0∞) (k + 1),
              ← ENNReal.rpow_mul]
            rw [← ENNReal.rpow_add _ _ h2zero h2top]
            congr 1
            push_cast
            ring
          have h2 : (((2 : ℕ) ^ k : ℝ≥0∞)) ^ (-s)
              = (2 : ℝ≥0∞) ^ ((-s) * k) := by
            push_cast
            rw [← ENNReal.rpow_natCast (2 : ℝ≥0∞) k,
              ← ENNReal.rpow_mul]
            congr 1
            ring
          have h3 : ((2 : ℝ≥0∞) ^ (a - s)) ^ k
              = (2 : ℝ≥0∞) ^ ((a - s) * k) := by
            rw [← ENNReal.rpow_natCast ((2 : ℝ≥0∞) ^ (a - s)) k,
              ← ENNReal.rpow_mul]
          rw [h1, h2, h3]
          rw [show ((C : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ a * (2 : ℝ≥0∞) ^ (a * k)))
                * (2 : ℝ≥0∞) ^ ((-s) * k)
              = (C : ℝ≥0∞) * (2 : ℝ≥0∞) ^ a
                * ((2 : ℝ≥0∞) ^ (a * k) * (2 : ℝ≥0∞) ^ ((-s) * k)) from by
            ring]
          rw [← ENNReal.rpow_add _ _ h2zero h2top]
          refine le_of_eq ?_
          congr 1
          congr 1
          ring
  -- partial sums up to a dyadic height
  have hpartial : ∀ K : ℕ,
      ∑ n ∈ Finset.range (2 ^ K), f n
        ≤ ∑ k ∈ Finset.range K, (C : ℝ≥0∞) * (2 : ℝ≥0∞) ^ a * r ^ k
      := by
    intro K
    induction K with
    | zero =>
        rw [pow_zero, Finset.sum_range_one, Finset.sum_range_zero]
        change (lengthCount Λ 0 : ℝ≥0∞) * (((0 : ℕ) : ℝ≥0∞)) ^ (-s) ≤ 0
        rw [lengthCount_zero Λ hΛ1]
        simp
    | succ K ih =>
        have hsplit : ∑ n ∈ Finset.range (2 ^ (K + 1)), f n
            = ∑ n ∈ Finset.range (2 ^ K), f n
              + ∑ n ∈ Finset.Ico (2 ^ K) (2 ^ (K + 1)), f n := by
          rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
          rw [Finset.sum_Ico_consecutive _ (Nat.zero_le _)
            (Nat.pow_le_pow_right (by norm_num) (by omega))]
        rw [hsplit, Finset.sum_range_succ]
        exact add_le_add ih (hblock K)
  -- pass to the tsum
  have htsum : (∑' n : ℕ, f n)
      ≤ (C : ℝ≥0∞) * (2 : ℝ≥0∞) ^ a * (1 - r)⁻¹ := by
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N => ?_
    have hsub : Finset.range N ⊆ Finset.range (2 ^ N) := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      have h2N := Nat.lt_two_pow_self (n := N)
      omega
    calc ∑ n ∈ Finset.range N, f n
        ≤ ∑ n ∈ Finset.range (2 ^ N), f n :=
          Finset.sum_le_sum_of_subset hsub
      _ ≤ ∑ k ∈ Finset.range N, (C : ℝ≥0∞) * (2 : ℝ≥0∞) ^ a * r ^ k
          := hpartial N
      _ ≤ ∑' k : ℕ, (C : ℝ≥0∞) * (2 : ℝ≥0∞) ^ a * r ^ k :=
          ENNReal.sum_le_tsum _
      _ = (C : ℝ≥0∞) * (2 : ℝ≥0∞) ^ a * ∑' k : ℕ, r ^ k := by
          rw [ENNReal.tsum_mul_left]
      _ = (C : ℝ≥0∞) * (2 : ℝ≥0∞) ^ a * (1 - r)⁻¹ := by
          rw [ENNReal.tsum_geometric]
  refine lt_of_le_of_lt htsum ?_
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ ?_) ?_
  · exact ENNReal.coe_lt_top
  · exact ENNReal.rpow_lt_top_of_nonneg ha h2top
  · rw [ENNReal.inv_lt_top]
    exact tsub_pos_of_lt hrlt

end Convergence

section Divergence

variable {ι : Type*} (Λ : ι → ℕ)
variable (hfin : ∀ n : ℕ, {i | Λ i ≤ n}.Finite)

include hfin in
/-- **Divergence below the growth exponent** (`thm:triple` (b),
lower half): if the channel count reaches `R^a` for arbitrarily
large `R`, the predictive zeta diverges for every `0 ≤ s < a` — the
shell partial sum already exceeds `N(R)·R^{−s} ≥ R^{a−s}`. -/
theorem zetaSum_eq_top_of_growth_lower {a s : ℝ}
    (hlow : ∀ j : ℕ, ∃ R : ℕ, j ≤ R ∧ 1 ≤ R ∧
      ((R : ℝ≥0∞)) ^ a ≤ (lengthShellCount Λ R : ℝ≥0∞))
    (hs0 : 0 ≤ s) (hsa : s < a) :
    zetaSum Λ s = ⊤ := by
  by_contra hne
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hne
  -- choose the dyadic exponent needed to beat m
  set t : ℝ := a - s with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  set K : ℕ := ⌈1 / t⌉₊ with hK
  obtain ⟨R, hjR, hR1, hRN⟩ := hlow ((m + 2) ^ K)
  -- the shell partial sum bound
  have hshell : ((R : ℝ≥0∞)) ^ t ≤ zetaSum Λ s := by
    have hsum : ∑ i ∈ (hfin R).toFinset, ((Λ i : ℝ≥0∞)) ^ (-s)
        ≤ zetaSum Λ s := ENNReal.sum_le_tsum _
    refine le_trans ?_ hsum
    have hterm : ∀ i ∈ (hfin R).toFinset,
        ((R : ℝ≥0∞)) ^ (-s) ≤ ((Λ i : ℝ≥0∞)) ^ (-s) := by
      intro i hi
      have hiR : Λ i ≤ R := ((hfin R).mem_toFinset).mp hi
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr
        (ENNReal.rpow_le_rpow (by exact_mod_cast hiR) hs0)
    have hRne0 : ((R : ℝ≥0∞)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by omega)
    calc ((R : ℝ≥0∞)) ^ t
        = ((R : ℝ≥0∞)) ^ a * ((R : ℝ≥0∞)) ^ (-s) := by
          rw [show t = a + (-s) from by rw [ht]; ring,
            ENNReal.rpow_add a (-s) hRne0 (ENNReal.natCast_ne_top R)]
      _ ≤ (lengthShellCount Λ R : ℝ≥0∞) * ((R : ℝ≥0∞)) ^ (-s) :=
          mul_le_mul' hRN le_rfl
      _ = ∑ _i ∈ (hfin R).toFinset, ((R : ℝ≥0∞)) ^ (-s) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          congr 1
          rw [lengthShellCount, Set.ncard_eq_toFinset_card _ (hfin R)]
      _ ≤ ∑ i ∈ (hfin R).toFinset, ((Λ i : ℝ≥0∞)) ^ (-s) :=
          Finset.sum_le_sum hterm
  -- the chosen R beats m
  have hbig : ((m : ℝ≥0∞)) < ((R : ℝ≥0∞)) ^ t := by
    have hKt : (1 : ℝ) ≤ (K : ℝ) * t := by
      have h0 : (1 / t : ℝ) ≤ (K : ℝ) := Nat.le_ceil (1 / t)
      have h1 : (1 / t) * t ≤ (K : ℝ) * t :=
        mul_le_mul_of_nonneg_right h0 ht0.le
      rw [one_div, inv_mul_cancel₀ ht0.ne'] at h1
      exact h1
    have hbase : (1 : ℝ≥0∞) ≤ ((m + 2 : ℕ) : ℝ≥0∞) := by
      exact_mod_cast (by omega : 1 ≤ m + 2)
    have hchain : ((m : ℝ≥0∞))
        < (((m + 2 : ℕ) : ℝ≥0∞)) ^ ((K : ℝ) * t) := by
      calc ((m : ℝ≥0∞)) < ((m + 2 : ℕ) : ℝ≥0∞) := by
            exact_mod_cast (by omega : m < m + 2)
        _ = (((m + 2 : ℕ) : ℝ≥0∞)) ^ (1 : ℝ) := by
            rw [ENNReal.rpow_one]
        _ ≤ (((m + 2 : ℕ) : ℝ≥0∞)) ^ ((K : ℝ) * t) :=
            ENNReal.rpow_le_rpow_of_exponent_le hbase hKt
    have heq : (((m + 2 : ℕ) : ℝ≥0∞)) ^ ((K : ℝ) * t)
        = ((((m + 2) ^ K : ℕ) : ℝ≥0∞)) ^ t := by
      push_cast
      rw [ENNReal.rpow_mul, ENNReal.rpow_natCast]
    refine lt_of_lt_of_le hchain ?_
    rw [heq]
    exact ENNReal.rpow_le_rpow (by exact_mod_cast hjR) ht0.le
  exact absurd (lt_of_lt_of_le hbig hshell) (not_lt.mpr hm.le)

end Divergence

section Theta

variable {ι : Type*} (Λ : ι → ℕ)
variable (hΛ1 : ∀ i, 1 ≤ Λ i)
variable (hfin : ∀ n : ℕ, {i | Λ i ≤ n}.Finite)

include hfin in
/-- General fibre decomposition for any weight `f` of the length. -/
theorem tsum_length_comp (f : ℕ → ℝ≥0∞) :
    (∑' i, f (Λ i)) = ∑' n : ℕ, (lengthCount Λ n : ℝ≥0∞) * f n := by
  rw [← ENNReal.tsum_fiberwise (fun i => f (Λ i)) Λ]
  refine tsum_congr fun n => ?_
  have hconst : ∀ i : (Λ ⁻¹' {n} : Set ι), f (Λ i.1) = f n := by
    rintro ⟨i, hi⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hi
    rw [hi]
  have hfibre : (Λ ⁻¹' {n} : Set ι).Finite := lengthFibre_finite Λ hfin n
  haveI := hfibre.fintype
  have hc : (Finset.univ : Finset (Λ ⁻¹' {n} : Set ι)).card
      = lengthCount Λ n := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    rfl
  rw [tsum_congr hconst, tsum_fintype, Finset.sum_const, nsmul_eq_mul,
    hc]

-- The elaboration of this proof is large; a higher heartbeat limit is required.
set_option maxHeartbeats 1000000 in
-- The exponential-series elaboration in this proof is large.
include hfin in
/-- **θ-summability** (the summability rider of `thm:fibre-dichotomy`
(1) and `cor:sharp-existence`): under a geometric channel-count bound
`N(n) ≤ B^n` (supplied for a finite alphabet by the word count), the
Gaussian heat trace `Σ_x e^{−t·Λ(x)²}` is finite for **every**
`t > 0` — the predictive length Dirac is θ-summable. -/
theorem theta_summable (B : ℝ≥0) (hB : 1 ≤ B)
    (hcount : ∀ n : ℕ,
      (lengthShellCount Λ n : ℝ≥0∞) ≤ ((B : ℝ≥0∞)) ^ n)
    {t : ℝ} (ht : 0 < t) :
    (∑' i, ENNReal.ofReal (Real.exp (-t * (Λ i : ℝ) ^ 2))) < ⊤ := by
  rw [show (∑' i, ENNReal.ofReal (Real.exp (-t * (Λ i : ℝ) ^ 2)))
      = ∑' n : ℕ, (lengthCount Λ n : ℝ≥0∞)
          * ENNReal.ofReal (Real.exp (-t * (n : ℝ) ^ 2)) from
    tsum_length_comp Λ hfin
      (fun n => ENNReal.ofReal (Real.exp (-t * (n : ℝ) ^ 2)))]
  set g : ℕ → ℝ≥0∞ := fun n =>
    (lengthCount Λ n : ℝ≥0∞)
      * ENNReal.ofReal (Real.exp (-t * (n : ℝ) ^ 2)) with hg
  set q : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-1)) with hq
  have hq1 : q < 1 := by
    rw [hq]
    calc ENNReal.ofReal (Real.exp (-1)) < ENNReal.ofReal 1 := by
          refine (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr ?_
          calc Real.exp (-1) < Real.exp 0 :=
                Real.exp_lt_exp.mpr (by norm_num)
            _ = 1 := Real.exp_zero
      _ = 1 := ENNReal.ofReal_one
  -- the threshold beyond which the Gaussian beats the geometric count
  set n₀ : ℕ := ⌈(Real.log B + 1) / t⌉₊ with hn₀
  have htail : ∀ n : ℕ, n₀ ≤ n → g n ≤ q ^ n := by
    intro n hn
    have hcn : (lengthCount Λ n : ℝ≥0∞) ≤ ((B : ℝ≥0∞)) ^ n := by
      refine le_trans ?_ (hcount n)
      refine Nat.cast_le.mpr ?_
      unfold lengthCount lengthShellCount
      exact Set.ncard_le_ncard (fun i h => le_of_eq h) (hfin n)
    have hstep : ((B : ℝ≥0∞)) ^ n
        * ENNReal.ofReal (Real.exp (-t * (n : ℝ) ^ 2)) ≤ q ^ n := by
      have hB0 : (0 : ℝ) < (B : ℝ) := lt_of_lt_of_le one_pos hB
      have hkey : (B : ℝ) * Real.exp (-t * n) ≤ Real.exp (-1) := by
        have hlog : Real.log B + 1 ≤ t * n := by
          have h1 : (Real.log B + 1) / t ≤ (n₀ : ℝ) :=
            Nat.le_ceil _
          have h2 : ((n₀ : ℝ)) ≤ (n : ℝ) := Nat.cast_le.mpr hn
          have h3 : (Real.log B + 1) / t ≤ (n : ℝ) := le_trans h1 h2
          calc Real.log B + 1 = ((Real.log B + 1) / t) * t := by
                field_simp
            _ ≤ (n : ℝ) * t :=
                mul_le_mul_of_nonneg_right h3 ht.le
            _ = t * n := by ring
        have h4 : (B : ℝ) ≤ Real.exp (t * n - 1) := by
          rw [← Real.exp_log hB0]
          exact Real.exp_le_exp.mpr (by linarith)
        calc (B : ℝ) * Real.exp (-t * n)
            ≤ Real.exp (t * n - 1) * Real.exp (-t * n) :=
              mul_le_mul_of_nonneg_right h4 (Real.exp_nonneg _)
          _ = Real.exp (-1) := by
              rw [← Real.exp_add]
              congr 1
              ring
      have hpow : ((B : ℝ) * Real.exp (-t * n)) ^ n
          ≤ Real.exp (-1) ^ n :=
        pow_le_pow_left₀ (by positivity) hkey n
      have hexpand : ((B : ℝ) * Real.exp (-t * n)) ^ n
          = (B : ℝ) ^ n * Real.exp (-t * (n : ℝ) ^ 2) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
      calc ((B : ℝ≥0∞)) ^ n
            * ENNReal.ofReal (Real.exp (-t * (n : ℝ) ^ 2))
          = ENNReal.ofReal
              ((B : ℝ) ^ n * Real.exp (-t * (n : ℝ) ^ 2)) := by
            rw [ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [show ((B : ℝ) ^ n) = (((B ^ n : ℝ≥0)) : ℝ) from by
                push_cast; rfl,
              ENNReal.ofReal_coe_nnreal, ← ENNReal.coe_pow]
        _ = ENNReal.ofReal (((B : ℝ) * Real.exp (-t * n)) ^ n) := by
            rw [hexpand]
        _ ≤ ENNReal.ofReal (Real.exp (-1) ^ n) :=
            ENNReal.ofReal_le_ofReal hpow
        _ = q ^ n := by
            rw [hq, ← ENNReal.ofReal_pow (Real.exp_nonneg _)]
    exact le_trans (mul_le_mul' hcn le_rfl) hstep
  -- bound every finite partial sum by the head plus the geometric tail
  rw [ENNReal.tsum_eq_iSup_sum]
  have hbound : ∀ s : Finset ℕ,
      (∑ n ∈ s, g n)
        ≤ ∑ n ∈ Finset.range n₀, g n + (1 - q)⁻¹ := by
    intro s
    calc ∑ n ∈ s, g n
        = ∑ n ∈ s.filter (fun n => n < n₀), g n
          + ∑ n ∈ s.filter (fun n => ¬ n < n₀), g n :=
          (Finset.sum_filter_add_sum_filter_not s _ g).symm
      _ ≤ ∑ n ∈ Finset.range n₀, g n + ∑' n : ℕ, q ^ n := by
          refine add_le_add ?_ ?_
          · refine Finset.sum_le_sum_of_subset ?_
            intro n hn
            obtain ⟨_, h2⟩ := Finset.mem_filter.mp hn
            exact Finset.mem_range.mpr h2
          · refine le_trans (Finset.sum_le_sum fun n hn => htail n ?_)
              (ENNReal.sum_le_tsum _)
            obtain ⟨_, h2⟩ := Finset.mem_filter.mp hn
            omega
      _ = ∑ n ∈ Finset.range n₀, g n + (1 - q)⁻¹ := by
          rw [ENNReal.tsum_geometric]
  refine lt_of_le_of_lt (iSup_le hbound) ?_
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · refine ENNReal.sum_lt_top.mpr fun n _ => ?_
    rw [hg]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _)
      ENNReal.ofReal_lt_top
  · rw [ENNReal.inv_lt_top]
    exact tsub_pos_of_lt hq1

end Theta

/-! ## The renewal instantiation (`thm:triple` (b)) -/

namespace RenewalMemory

variable {E M : Type*} [Monoid M] (R : RenewalMemory E M) [Finite E]

/-- **`thm:triple` (b), the predictive zeta**: the Dirichlet sum of
the positive length spectrum (the length-zero classes are the kernel
modes of `D_CP`, excluded from the spectral sum as usual). -/
noncomputable def zeta (s : ℝ) : ℝ≥0∞ :=
  zetaSum (fun x : {x : R.PredictiveQuotient // 1 ≤ R.quotLength x}
    => R.quotLength x.1) s

theorem subtype_shell_finite (n : ℕ) :
    {x : {x : R.PredictiveQuotient // 1 ≤ R.quotLength x} |
      R.quotLength x.1 ≤ n}.Finite :=
  (R.shell_finite n).preimage
    (Set.injOn_of_injective Subtype.val_injective)

theorem subtype_shellCount_le (n : ℕ) :
    lengthShellCount (fun x : {x : R.PredictiveQuotient //
        1 ≤ R.quotLength x} => R.quotLength x.1) n
      ≤ R.channelCount n := by
  unfold lengthShellCount channelCount
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  refine Set.ncard_le_ncard ?_ (R.shell_finite n)
  rintro x ⟨⟨y, hy⟩, hmem, rfl⟩
  exact hmem

/-- The channel count splits into the kernel modes and the positive
length spectrum. -/
theorem channelCount_split (n : ℕ) :
    R.channelCount n
      = {x : R.PredictiveQuotient | R.quotLength x = 0}.ncard
        + lengthShellCount (fun x : {x : R.PredictiveQuotient //
            1 ≤ R.quotLength x} => R.quotLength x.1) n := by
  have himg : lengthShellCount (fun x : {x : R.PredictiveQuotient //
        1 ≤ R.quotLength x} => R.quotLength x.1) n
      = {x : R.PredictiveQuotient |
          1 ≤ R.quotLength x ∧ R.quotLength x ≤ n}.ncard := by
    unfold lengthShellCount
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
    congr 1
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, hmem, rfl⟩
      exact ⟨hy, hmem⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h1⟩, h2, rfl⟩
  rw [himg]
  unfold channelCount
  have hsplit : R.shell n
      = {x : R.PredictiveQuotient | R.quotLength x = 0}
        ∪ {x : R.PredictiveQuotient |
            1 ≤ R.quotLength x ∧ R.quotLength x ≤ n} := by
    ext x
    simp only [shell, Set.mem_setOf_eq, Set.mem_union]
    omega
  have hdisj : Disjoint
      {x : R.PredictiveQuotient | R.quotLength x = 0}
      {x : R.PredictiveQuotient |
        1 ≤ R.quotLength x ∧ R.quotLength x ≤ n} := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false]
    omega
  rw [hsplit, Set.ncard_union_eq hdisj
    ((R.shell_finite n).subset (by
      intro x hx
      change R.quotLength x ≤ n
      simp only [Set.mem_setOf_eq] at hx
      omega))
    ((R.shell_finite n).subset (by
      intro x hx
      exact hx.2))]

/-- **`thm:triple` (b), convergence half**: polynomial channel-count
growth `N_CP(n) ≤ C·n^a` makes `ζ_CP(s)` finite for every `s > a` —
the abscissa of convergence is at most the algebraic predictive
dimension. -/
theorem zeta_lt_top_of_channelCount_growth (C : ℝ≥0) {a s : ℝ}
    (ha : 0 ≤ a)
    (hN : ∀ n : ℕ, 1 ≤ n →
      (R.channelCount n : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (n : ℝ≥0∞) ^ a)
    (hs : a < s) : R.zeta s < ⊤ :=
  zetaSum_lt_top_of_growth _ (fun i => i.2)
    (R.subtype_shell_finite) C ha
    (fun n hn => le_trans
      (Nat.cast_le.mpr (R.subtype_shellCount_le n)) (hN n hn)) hs

/-- **`thm:triple` (b), divergence half**: if the channel count
reaches `n^a` (beyond the kernel modes) for arbitrarily large `n`,
then `ζ_CP(s)` diverges for every `0 ≤ s < a` — the abscissa of
convergence is at least the algebraic predictive dimension. -/
theorem zeta_eq_top_of_channelCount_lower {a s : ℝ}
    (hlow : ∀ j : ℕ, ∃ n : ℕ, j ≤ n ∧ 1 ≤ n ∧
      ((n : ℝ≥0∞)) ^ a
          + ({x : R.PredictiveQuotient |
              R.quotLength x = 0}.ncard : ℝ≥0∞)
        ≤ (R.channelCount n : ℝ≥0∞))
    (hs0 : 0 ≤ s) (hsa : s < a) : R.zeta s = ⊤ := by
  refine zetaSum_eq_top_of_growth_lower _ (R.subtype_shell_finite)
    (fun j => ?_) hs0 hsa
  obtain ⟨n, h1, h2, h3⟩ := hlow j
  refine ⟨n, h1, h2, ?_⟩
  have hsplit := R.channelCount_split n
  rw [hsplit] at h3
  push_cast at h3
  rw [add_comm ((n : ℝ≥0∞) ^ a)] at h3
  exact (ENNReal.add_le_add_iff_left
    (ENNReal.natCast_ne_top _)).mp h3

end RenewalMemory

end NCG
