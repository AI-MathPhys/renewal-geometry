/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.ResponseThreadCompletionExact
import NCG.Grand.UniversalLimitAlternativeExact

/-!
# Structure-preserving response passage

Record-local machinery for `cor:GT-structure-preserving-response`: the finite
solutions of a regulator family with (S1) an energy barrier, (S2) a uniform
negative-norm time bound, (S3) compact target writers and (S4) vanishing
Fortin/Galerkin defects contain a coherent response thread whose completed
trace satisfies the full countable continuum weak core.

The hypotheses enter as their analytic outputs: (S1)+(S2) supply the common
modulus of continuity for the finite responses (the discrete Aubin--Lions
step), (S3) supplies compactness of the target space, and (S4) supplies the
vanishing of every fixed continuum-test residual along the family.

* `structure_preserving_response`: a subsequence of the finite responses is a
  coherent thread; its completed trace is continuous, keeps the modulus, and
  annihilates every member of the countable weak core;
* `full_sequence_of_cauchy`: the manuscript's final clause — the limit is
  subsequential unless a Cauchy estimate is supplied, in which case the full
  sequence converges to the same trace.
-/

open Filter Topology

namespace NCG
namespace StructureResponse

/-- **Structure-preserving response passage** (S1)–(S4): the finite responses
contain a coherent thread whose completed trace satisfies the full countable
weak core.  The limit is subsequential. -/
theorem structure_preserving_response {K : Type*} [MetricSpace K]
    [CompactSpace K] [CompleteSpace K]
    (T : ℝ) (q : ℕ → ℝ) (y : ℕ → ℝ → K) (ω : ℝ → ℝ)
    (hq_mem : ∀ jq, q jq ∈ Set.Icc 0 T)
    (hdense : ∀ t ∈ Set.Icc 0 T, ∀ ε > 0, ∃ jq, |q jq - t| < ε)
    (hω_cont : Continuous ω) (hω_zero : ω 0 = 0)
    (hmod : ∀ N, ∀ t ∈ Set.Icc 0 T, ∀ s ∈ Set.Icc 0 T,
      dist (y N t) (y N s) ≤ ω |t - s|)
    {k : ℕ → ℕ} (𝔡 : ∀ j, (Fin (k j) → K) → ℝ)
    (h𝔡 : ∀ j, Continuous (𝔡 j)) (qs : ∀ j, Fin (k j) → ℝ)
    (hqs : ∀ j i, ∃ jq, qs j i = q jq)
    (hres : ∀ j, Tendsto (fun N => 𝔡 j (fun i => y N (qs j i))) atTop (𝓝 0)) :
    ∃ (z : ℝ → K) (φ' : ℕ → ℕ), StrictMono φ' ∧
      ContinuousOn z (Set.Icc 0 T) ∧
      (∀ t ∈ Set.Icc 0 T, ∀ s ∈ Set.Icc 0 T, dist (z t) (z s) ≤ ω |t - s|) ∧
      (∀ j, 𝔡 j (fun i => z (qs j i)) = 0) ∧
      (∀ jq, Tendsto (fun m => y (φ' m) (q jq)) atTop (𝓝 (z (q jq)))) := by
  classical
  -- (S3): compactness extraction over the countable query family
  obtain ⟨φ, lim, hφ, hconv⟩ :=
    NCG.UniversalLimit.exists_common_profile_subsequence
      (X := fun _ : ℕ => K) (fun N => fun j => y N (q j))
  -- projective-Cauchy speed-up
  have hN : ∀ m : ℕ, ∃ Nm : ℕ, ∀ n, Nm ≤ n → ∀ j, j ≤ m →
      dist (y (φ n) (q j)) (lim j) < (1 / 2 : ℝ) ^ (m + 1) := by
    intro m
    have hchoice : ∀ j : ℕ, ∃ Nj : ℕ, ∀ n ≥ Nj,
        dist (y (φ n) (q j)) (lim j) < (1 / 2 : ℝ) ^ (m + 1) :=
      fun j => Metric.tendsto_atTop.mp (hconv j) _ (by positivity)
    choose Nf hNf using hchoice
    refine ⟨(Finset.range (m + 1)).sup Nf, fun n hn j hj => ?_⟩
    exact hNf j n (le_trans
      (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))) hn)
  choose N hNspec using hN
  let ψ : ℕ → ℕ := fun m =>
    Nat.rec (N 0) (fun kk ih => max (N (kk + 1)) (ih + 1)) m
  have hψ_succ : ∀ m, ψ (m + 1) = max (N (m + 1)) (ψ m + 1) := fun m => rfl
  have hψ_mono : StrictMono ψ := strictMono_nat_of_lt_succ fun m => by
    rw [hψ_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  have hψ_ge : ∀ m, N m ≤ ψ m := by
    intro m
    cases m with
    | zero => exact le_refl _
    | succ kk =>
        rw [hψ_succ]
        exact le_max_left _ _
  -- the coherent thread
  let Y : ResponseThreadCompletion.Thread K :=
    { T := T
      D := fun m => {s | ∃ jq, jq ≤ m ∧ q jq = s}
      y := fun m => y (φ (ψ m))
      ω := ω
      η := fun m => (1 / 2 : ℝ) ^ m
      D_subset := by
        rintro m s ⟨jq, -, rfl⟩
        exact hq_mem jq
      D_mono := by
        intro a b hab s hs
        obtain ⟨jq, hjq, rfl⟩ := hs
        exact ⟨jq, hjq.trans hab, rfl⟩
      D_dense := by
        intro t ht ε hε
        obtain ⟨jq, hjq⟩ := hdense t ht ε hε
        exact ⟨jq, q jq, ⟨jq, le_refl _, rfl⟩, hjq⟩
      ω_cont := hω_cont
      ω_zero := hω_zero
      modulus := by
        rintro m t ⟨jt, -, rfl⟩ s ⟨js, -, rfl⟩
        exact hmod _ _ (hq_mem jt) _ (hq_mem js)
      defect := by
        rintro m n hmn t ⟨jq, hjq, rfl⟩
        have h1 := hNspec m (ψ n)
          (le_trans (hψ_ge m) (hψ_mono.monotone hmn)) jq hjq
        have h2 := hNspec m (ψ m) (hψ_ge m) jq hjq
        calc dist (y (φ (ψ n)) (q jq)) (y (φ (ψ m)) (q jq))
            ≤ dist (y (φ (ψ n)) (q jq)) (lim jq) +
              dist (lim jq) (y (φ (ψ m)) (q jq)) := dist_triangle _ _ _
          _ ≤ (1 / 2 : ℝ) ^ (m + 1) + (1 / 2 : ℝ) ^ (m + 1) :=
              add_le_add h1.le (by rw [dist_comm]; exact h2.le)
          _ = (1 / 2 : ℝ) ^ m := by
              rw [pow_succ]
              ring
      η_nonneg := fun m => by positivity
      η_tendsto :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num) }
  refine ⟨ResponseThreadCompletion.limitTrace Y, fun m => φ (ψ m),
    hφ.comp hψ_mono,
    ResponseThreadCompletion.limitTrace_continuousOn Y,
    fun t ht s hs => ResponseThreadCompletion.limitTrace_modulus Y ht hs,
    ?_, ?_⟩
  · -- the countable weak core is annihilated
    intro j
    choose idx hidx using hqs j
    refine ResponseThreadCompletion.cylinder_limit Y (𝔡 j) (h𝔡 j) (qs j)
      (Finset.univ.sup idx) (fun i => ?_) ?_
    · rw [hidx i]
      exact ⟨idx i, Finset.le_sup (Finset.mem_univ i), rfl⟩
    · have hcomp := (hres j).comp ((hφ.comp hψ_mono).tendsto_atTop)
      rw [Function.comp_def] at hcomp
      exact hcomp
  · -- subsequential query convergence
    intro jq
    have hmem : q jq ∈ Y.D jq := ⟨jq, le_refl _, rfl⟩
    have h1 := ResponseThreadCompletion.tendsto_queryLimit Y hmem
    rw [← ResponseThreadCompletion.limitTrace_eq_queryLimit Y
      ((ResponseThreadCompletion.mem_queries Y).mpr ⟨jq, hmem⟩)] at h1
    exact h1

/-- **The full-sequence upgrade**: the limit is subsequential unless a Cauchy
estimate is supplied — a Cauchy finite-response family converges along the
whole sequence to the same completed trace. -/
theorem full_sequence_of_cauchy {K : Type*} [MetricSpace K] [CompleteSpace K]
    (w : ℕ → K) (hw : CauchySeq w) (z : K) (φ' : ℕ → ℕ) (hφ' : StrictMono φ')
    (hsub : Tendsto (fun m => w (φ' m)) atTop (𝓝 z)) :
    Tendsto w atTop (𝓝 z) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hw
  have h2 : Tendsto (fun m => w (φ' m)) atTop (𝓝 L) := by
    have := hL.comp hφ'.tendsto_atTop
    rw [Function.comp_def] at this
    exact this
  rw [tendsto_nhds_unique hsub h2]
  exact hL

end StructureResponse
end NCG
