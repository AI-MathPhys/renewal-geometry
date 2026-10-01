/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Rellich compactness in Fourier-coefficient form

Infrastructure for `prop:supp-initial-cofinal-preparation` (emergent-spacetime manuscript:
"trigonometric interpolation and Rellich compactness give subsequential convergence in
`𝒫^{s+1}`").  On the torus `𝕋³` a field is identified with its Fourier coefficients
`c : ℤ³ → ℂ` and `‖u‖²_{H^a} = Σ_k (1 + |k|²)^a |c_k|²`; compactness of the embedding
`H^{a} ⊂ H^{b}`, `b < a`, is the following statement about weighted `ℓ²` spaces.

* `rellich_coefficients`: let `W > 0`, `V ≥ 0` be weights on a countable index set such that
  `{k | W k < R V k}` is finite for every `R` (i.e. `V / W → 0`).  Every sequence of coefficient
  families with `Σ_k W(k) |c_n(k)|² ≤ B` has a subsequence converging coefficientwise to a
  limit `c` with `Σ_k W(k) |c(k)|² ≤ B`, and **strongly in the `V`-weighted norm**:
  `Σ_k V(k) |c_{φ n}(k) - c(k)|² → 0`.
* `rellich_torus`: the instance `ι = ℤ³`, `W = (1 + |k|²)^a`, `V = (1 + |k|²)^b`, `b < a`:
  bounded sequences in `H^a(𝕋³)` (coefficient form) have subsequences converging in `H^b`.
-/

open Filter Topology Set Finset

namespace RenewalGeometry
namespace FourierRellich

theorem norm_sub_sq_le (x y : ℂ) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_sub_le x y
  have h0 := norm_nonneg (x - y)
  nlinarith [norm_nonneg x, norm_nonneg y, sq_nonneg (‖x‖ - ‖y‖)]

open scoped Classical in
/-- **Rellich compactness, coefficient form.**  Weights `W > 0`, `V ≥ 0` on a countable index
set with `{k | W k < R V k}` finite for every `R`.  A sequence `c_n` with
`Σ_k W(k) |c_n(k)|² ≤ B` has a subsequence `c_{φ n}` converging coefficientwise to some `c`
with `Σ_k W(k) |c(k)|² ≤ B` and `Σ_k V(k) |c_{φ n}(k) - c(k)|² → 0`. -/
theorem rellich_coefficients {ι : Type*} [Countable ι] (W V : ι → ℝ) (hW : ∀ k, 0 < W k)
    (hV : ∀ k, 0 ≤ V k) (hfin : ∀ R : ℝ, {k | W k < R * V k}.Finite) {B : ℝ}
    (c : ℕ → ι → ℂ) (hsum : ∀ n, Summable fun k => W k * ‖c n k‖ ^ 2)
    (hB : ∀ n, ∑' k, W k * ‖c n k‖ ^ 2 ≤ B) :
    ∃ (φ : ℕ → ℕ) (cl : ι → ℂ), StrictMono φ ∧
      (∀ k, Tendsto (fun n => c (φ n) k) atTop (𝓝 (cl k))) ∧
      Summable (fun k => W k * ‖cl k‖ ^ 2) ∧ ∑' k, W k * ‖cl k‖ ^ 2 ≤ B ∧
      (∀ n, Summable fun k => V k * ‖c (φ n) k - cl k‖ ^ 2) ∧
      Tendsto (fun n => ∑' k, V k * ‖c (φ n) k - cl k‖ ^ 2) atTop (𝓝 0) := by
  have hnn : ∀ n k, 0 ≤ W k * ‖c n k‖ ^ 2 := fun n k => mul_nonneg (hW k).le (sq_nonneg _)
  have hB0 : 0 ≤ B := (tsum_nonneg (hnn 0)).trans (hB 0)
  have hfinsum : ∀ n (T : Finset ι), ∑ k ∈ T, W k * ‖c n k‖ ^ 2 ≤ B := fun n T =>
    ((hsum n).sum_le_tsum T (fun k _ => hnn n k)).trans (hB n)
  have hterm : ∀ n k, W k * ‖c n k‖ ^ 2 ≤ B := fun n k => by
    simpa using hfinsum n {k}
  -- coefficientwise bounds and diagonal extraction
  set s : Set (ι → ℂ) := Set.pi univ (fun k => Metric.closedBall 0 (Real.sqrt (B / W k)))
  have hs : IsCompact s := isCompact_univ_pi fun k => isCompact_closedBall _ _
  have hx : ∀ n, c n ∈ s := by
    intro n k _
    rw [mem_closedBall_zero_iff]
    have h1 : ‖c n k‖ ^ 2 ≤ B / W k := by
      rw [le_div_iff₀ (hW k)]; linarith [hterm n k]
    simpa using Real.abs_le_sqrt h1
  obtain ⟨cl, -, φ, hφ, hlim⟩ := hs.tendsto_subseq hx
  have hcoord : ∀ k, Tendsto (fun n => c (φ n) k) atTop (𝓝 (cl k)) := fun k =>
    tendsto_pi_nhds.mp hlim k
  -- the limit is bounded in the strong weight
  have hcl_fin : ∀ T : Finset ι, ∑ k ∈ T, W k * ‖cl k‖ ^ 2 ≤ B := by
    intro T
    have ht : Tendsto (fun n => ∑ k ∈ T, W k * ‖c (φ n) k‖ ^ 2) atTop
        (𝓝 (∑ k ∈ T, W k * ‖cl k‖ ^ 2)) :=
      tendsto_finset_sum _ fun k _ => ((hcoord k).norm.pow 2).const_mul (W k)
    exact le_of_tendsto' ht fun n => hfinsum (φ n) T
  have hclnn : 0 ≤ fun k => W k * ‖cl k‖ ^ 2 := fun k => mul_nonneg (hW k).le (sq_nonneg _)
  have hcl_sum : Summable (fun k => W k * ‖cl k‖ ^ 2) := summable_of_sum_le hclnn hcl_fin
  have hcl_B : ∑' k, W k * ‖cl k‖ ^ 2 ≤ B := tsum_le_of_sum_le' hB0 hcl_fin
  -- the differences are bounded by `4B` in the strong weight
  set d : ℕ → ι → ℝ := fun n k => ‖c (φ n) k - cl k‖ ^ 2 with hd
  have hdnn : ∀ n k, 0 ≤ d n k := fun n k => sq_nonneg _
  have hdW : ∀ n (T : Finset ι), ∑ k ∈ T, W k * d n k ≤ 4 * B := by
    intro n T
    calc ∑ k ∈ T, W k * d n k
        ≤ ∑ k ∈ T, (2 * (W k * ‖c (φ n) k‖ ^ 2) + 2 * (W k * ‖cl k‖ ^ 2)) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have := mul_le_mul_of_nonneg_left (norm_sub_sq_le (c (φ n) k) (cl k)) (hW k).le
          simp only [hd]; linarith
      _ = 2 * ∑ k ∈ T, W k * ‖c (φ n) k‖ ^ 2 + 2 * ∑ k ∈ T, W k * ‖cl k‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * B + 2 * B := by
          gcongr
          · exact hfinsum (φ n) T
          · exact hcl_fin T
      _ = 4 * B := by ring
  -- splitting off the finitely many modes where `V` is not small compared to `W`
  have hsplit : ∀ (R : ℝ), 0 < R → ∀ n (T : Finset ι),
      ∑ k ∈ T, V k * d n k ≤ ∑ k ∈ (hfin R).toFinset, V k * d n k + 4 * B / R := by
    intro R hR n T
    rw [← Finset.sum_filter_add_sum_filter_not T (fun k => k ∈ {k | W k < R * V k})]
    refine add_le_add ?_ ?_
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => mul_nonneg (hV k) (hdnn n k)
      intro k hk
      rw [Finset.mem_filter] at hk
      exact (hfin R).mem_toFinset.mpr hk.2
    · have hle : ∀ k ∈ T.filter (fun k => k ∉ {k | W k < R * V k}),
          V k * d n k ≤ (W k * d n k) / R := by
        intro k hk
        rw [Finset.mem_filter, Set.mem_setOf_eq, not_lt] at hk
        rw [le_div_iff₀ hR]
        have := mul_le_mul_of_nonneg_right hk.2 (hdnn n k)
        linarith
      calc ∑ k ∈ T.filter (fun k => k ∉ {k | W k < R * V k}), V k * d n k
          ≤ ∑ k ∈ T.filter (fun k => k ∉ {k | W k < R * V k}), (W k * d n k) / R :=
            Finset.sum_le_sum hle
        _ = (∑ k ∈ T.filter (fun k => k ∉ {k | W k < R * V k}), W k * d n k) / R := by
            rw [Finset.sum_div]
        _ ≤ (4 * B) / R := by
            gcongr
            exact hdW n _
  have hVnn : ∀ n, 0 ≤ fun k => V k * d n k := fun n k => mul_nonneg (hV k) (hdnn n k)
  have hVsum : ∀ n, Summable fun k => V k * d n k := fun n =>
    summable_of_sum_le (hVnn n) (hsplit 1 one_pos n)
  refine ⟨φ, cl, hφ, hcoord, hcl_sum, hcl_B, hVsum, ?_⟩
  -- convergence
  have hfinite_lim : ∀ R : ℝ, Tendsto (fun n => ∑ k ∈ (hfin R).toFinset, V k * d n k) atTop
      (𝓝 0) := by
    intro R
    have : Tendsto (fun n => ∑ k ∈ (hfin R).toFinset, V k * d n k) atTop
        (𝓝 (∑ k ∈ (hfin R).toFinset, V k * ‖cl k - cl k‖ ^ 2)) :=
      tendsto_finset_sum _ fun k _ => (((hcoord k).sub tendsto_const_nhds).norm.pow 2).const_mul _
    simpa using this
  rw [Metric.tendsto_atTop]
  intro ε hε
  set R : ℝ := (8 * B + 1) / ε with hR
  have hRpos : 0 < R := by positivity
  have htail : 4 * B / R < ε / 2 := by
    rw [hR, div_div_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hfinite_lim R) (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq, sub_zero] at h1
  have h2 : ∑' k, V k * d n k ≤ ∑ k ∈ (hfin R).toFinset, V k * d n k + 4 * B / R :=
    tsum_le_of_sum_le' (add_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (hV k) (hdnn n k))
      (by positivity)) (hsplit R hRpos n)
  have h3 : 0 ≤ ∑' k, V k * d n k := tsum_nonneg (hVnn n)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h3]
  have h4 := le_abs_self (∑ k ∈ (hfin R).toFinset, V k * d n k)
  linarith

/-- The Sobolev weight `1 + |k|²` on `ℤ³`. -/
noncomputable def sobWeight (k : Fin 3 → ℤ) : ℝ := 1 + ∑ i, ((k i : ℝ)) ^ 2

theorem one_le_sobWeight (k : Fin 3 → ℤ) : 1 ≤ sobWeight k := by
  unfold sobWeight
  have := Finset.sum_nonneg fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    sq_nonneg ((k i : ℝ))
  linarith

theorem finite_sobWeight_lt (R : ℝ) : {k : Fin 3 → ℤ | sobWeight k < R}.Finite := by
  obtain ⟨M, hM⟩ := exists_nat_gt R
  refine (Set.Finite.pi (t := fun _ : Fin 3 => Set.Icc (-(M : ℤ)) M)
    fun _ => Set.finite_Icc _ _).subset ?_
  intro k hk
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_true_left]
  intro i
  have hk' : sobWeight k < M := lt_trans hk hM
  have hi : ((k i : ℝ)) ^ 2 ≤ ∑ j, ((k j : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun j => ((k j : ℝ)) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hsq : ((k i : ℝ)) ^ 2 < (M : ℝ) := by unfold sobWeight at hk'; linarith
  have hsqZ : (k i) ^ 2 < (M : ℤ) := by exact_mod_cast hsq
  have habs : |k i| ≤ (M : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact (Int.natAbs_le_self_sq _).trans hsqZ.le
  exact abs_le.mp habs

/-- **Rellich on `𝕋³`** (coefficient form): a sequence bounded in `H^a`,
`Σ_k (1+|k|²)^a |c_n(k)|² ≤ B`, has a subsequence converging in `H^b` for every `b < a`. -/
theorem rellich_torus {a b : ℕ} (hab : b < a) {B : ℝ} (c : ℕ → (Fin 3 → ℤ) → ℂ)
    (hsum : ∀ n, Summable fun k => sobWeight k ^ a * ‖c n k‖ ^ 2)
    (hB : ∀ n, ∑' k, sobWeight k ^ a * ‖c n k‖ ^ 2 ≤ B) :
    ∃ (φ : ℕ → ℕ) (cl : (Fin 3 → ℤ) → ℂ), StrictMono φ ∧
      (∀ k, Tendsto (fun n => c (φ n) k) atTop (𝓝 (cl k))) ∧
      Summable (fun k => sobWeight k ^ a * ‖cl k‖ ^ 2) ∧
      ∑' k, sobWeight k ^ a * ‖cl k‖ ^ 2 ≤ B ∧
      (∀ n, Summable fun k => sobWeight k ^ b * ‖c (φ n) k - cl k‖ ^ 2) ∧
      Tendsto (fun n => ∑' k, sobWeight k ^ b * ‖c (φ n) k - cl k‖ ^ 2) atTop (𝓝 0) := by
  have hw1 := one_le_sobWeight
  refine rellich_coefficients (fun k => sobWeight k ^ a) (fun k => sobWeight k ^ b)
    (fun k => pow_pos (lt_of_lt_of_le one_pos (hw1 k)) a)
    (fun k => pow_nonneg (le_trans zero_le_one (hw1 k)) b) (fun R => ?_) c hsum hB
  refine (finite_sobWeight_lt R).subset ?_
  intro k hk
  simp only [Set.mem_setOf_eq] at hk ⊢
  have hw : 1 ≤ sobWeight k := hw1 k
  have hwb : 0 < sobWeight k ^ b := pow_pos (lt_of_lt_of_le one_pos hw) b
  have hsplit : sobWeight k ^ a = sobWeight k ^ (a - b) * sobWeight k ^ b := by
    rw [← pow_add, Nat.sub_add_cancel hab.le]
  have hle : sobWeight k ≤ sobWeight k ^ (a - b) :=
    le_self_pow₀ hw (by omega)
  rw [hsplit] at hk
  have : sobWeight k ^ (a - b) < R := lt_of_mul_lt_mul_right hk hwb.le
  linarith

end FourierRellich
end RenewalGeometry
