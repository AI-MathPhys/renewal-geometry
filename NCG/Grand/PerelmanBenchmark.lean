/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Perelman benchmark interface
  (`prop:Poincare-benchmark`, Gran-Tensor manuscript)

* `poincare_benchmark_interface`: the typed scale-flow
  package the proposition asserts encodable, with its
  actual closure bookkeeping proved:
  (i) **surgery budget**: an entropy profile monotone off
      surgeries with jump allowance `J` obeys
      `W N ≤ W 0 + Σ J` at every scale (the summable
      surgery budget controls the flow);
  (ii) **closure**: if additionally the profile is
      bounded below and the surgery allowance is
      summable, the flow closes — `W` converges (the
      compensated profile `W n + tail n` is antitone and
      bounded below, and the summable tail vanishes);
  (iii) **non-transport**: the encoded package alone does
      not determine the closure value — two admissible
      profiles with identical typed boundary data (same
      initial entropy, zero surgery budget, monotone)
      converge to different limits. Encoding is
      architecture compatibility, not a proof in another
      sector.

Perelman's geometric inputs (monotonicity of the actual
Ricci-flow entropy, canonical neighbourhoods,
no-collapse, surgery-budget summability for the actual
flow) are the manuscript's cited geometric layer: they
instantiate `W`, `J` and the bounds; the proposition's
own content is the interface bookkeeping proved here.
-/

open Filter

namespace NCG

/-- `prop:Poincare-benchmark` (surgery budget, closure,
and non-transport of the scale-flow interface). -/
theorem poincare_benchmark_interface :
    -- (i) the surgery budget bounds every scale
    (∀ (W J : ℕ → ℝ) (B : ℝ),
      (∀ n, W (n + 1) ≤ W n + J n) →
      (∀ n, 0 ≤ J n) →
      (∀ N, ∑ n ∈ Finset.range N, J n ≤ B) →
      ∀ N, W N ≤ W 0 + B)
    -- (ii) bounded flows with summable surgery close
    ∧ (∀ (W J : ℕ → ℝ) (m : ℝ),
        (∀ n, W (n + 1) ≤ W n + J n) →
        (∀ n, 0 ≤ J n) →
        (∀ n, m ≤ W n) →
        Summable J →
        ∃ L, Tendsto W atTop (nhds L))
    -- (iii) the encoding does not transport the closure
    ∧ (∃ W₁ W₂ : ℕ → ℝ, W₁ 0 = W₂ 0
        ∧ (∀ n, W₁ (n + 1) ≤ W₁ n)
        ∧ (∀ n, W₂ (n + 1) ≤ W₂ n)
        ∧ ∃ L₁ L₂, L₁ ≠ L₂
          ∧ Tendsto W₁ atTop (nhds L₁)
          ∧ Tendsto W₂ atTop (nhds L₂)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (i) induction with the running budget
    intro W J B hstep hJ0 hbudget N
    have key : ∀ N, W N ≤ W 0
        + ∑ n ∈ Finset.range N, J n := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        calc W (N + 1) ≤ W N + J N := hstep N
          _ ≤ W 0 + ∑ n ∈ Finset.range N, J n + J N := by
              linarith
          _ = W 0 + ∑ n ∈ Finset.range (N + 1), J n := by
              rw [Finset.sum_range_succ]
              ring
    calc W N ≤ W 0 + ∑ n ∈ Finset.range N, J n := key N
      _ ≤ W 0 + B := by linarith [hbudget N]
  · -- (ii) compensated-profile convergence
    intro W J m hstep hJ0 hlb hsum
    set T : ℕ → ℝ := fun n => ∑' k, J (k + n) with hT
    have hT0 : ∀ n, 0 ≤ T n := by
      intro n
      rw [hT]
      exact tsum_nonneg fun k => hJ0 _
    have hTsplit : ∀ n, T n = J n + T (n + 1) := by
      intro n
      simp only [hT]
      have h1 := ((summable_nat_add_iff n).mpr
        hsum).tsum_eq_zero_add
      rw [h1, zero_add]
      congr 1
      apply tsum_congr
      intro k
      congr 1
      omega
    set V : ℕ → ℝ := fun n => W n + T n with hV
    have hVanti : Antitone V := by
      apply antitone_nat_of_succ_le
      intro n
      rw [hV]
      simp only
      have := hstep n
      have := hTsplit n
      linarith
    have hVlb : BddBelow (Set.range V) := by
      refine ⟨m, ?_⟩
      rintro x ⟨n, rfl⟩
      rw [hV]
      simp only
      have := hlb n
      have := hT0 n
      linarith
    have hVconv : Tendsto V atTop
        (nhds (⨅ n, V n)) :=
      tendsto_atTop_ciInf hVanti hVlb
    -- the summable tail vanishes
    have hTzero : Tendsto T atTop (nhds 0) := by
      have htot : ∀ n, (∑ k ∈ Finset.range n, J k) + T n
          = ∑' k, J k := by
        intro n
        rw [hT]
        exact hsum.sum_add_tsum_nat_add n
      have hpartial : Tendsto
          (fun n => ∑ k ∈ Finset.range n, J k) atTop
          (nhds (∑' k, J k)) :=
        hsum.hasSum.tendsto_sum_nat
      have : T = fun n => (∑' k, J k)
          - ∑ k ∈ Finset.range n, J k := by
        funext n
        have := htot n
        linarith
      rw [this]
      have := (tendsto_const_nhds (x := ∑' k, J k)
        (f := atTop (α := ℕ))).sub hpartial
      simpa using this
    -- `W = V - T` converges
    refine ⟨⨅ n, V n, ?_⟩
    have hWVT : W = fun n => V n - T n := by
      funext n
      rw [hV]
      ring
    rw [hWVT]
    have := hVconv.sub hTzero
    simpa using this
  · -- (iii) same boundary data, different closures
    refine ⟨fun n => 1 / (n + 1),
      fun n => if n = 0 then 1 else 1/2,
      by norm_num, ?_, ?_, 0, 1/2, by norm_num,
      ?_, ?_⟩
    · intro n
      apply div_le_div_of_nonneg_left (by norm_num)
        (by positivity)
      push_cast
      linarith
    · intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · norm_num
      · simp only
        rw [if_neg (by omega : ¬ n + 1 = 0),
          if_neg (by omega : ¬ n = 0)]
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · apply Tendsto.congr'
        (f₁ := fun _ : ℕ => (1 : ℝ)/2)
      · filter_upwards [Filter.eventually_gt_atTop 0]
          with n hn
        rw [if_neg (by omega)]
      · exact tendsto_const_nhds

end NCG
