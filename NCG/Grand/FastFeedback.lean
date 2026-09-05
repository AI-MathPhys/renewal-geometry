/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Fast loaded feedback collapses to a local generator
  (`thm:fast-feedback-collapse`, Gran-Tensor manuscript)

* `power_comparison_bound`: the discrete-Duhamel core of the
  boxed sup-convergence — for two step maps bounded by `M`,
  `‖Aⁿ⁺¹ - Eⁿ⁺¹‖ ≤ (n+1)·Mⁿ·‖A - E‖`, so an `O(h²)` per-step
  defect stays `O(h)` uniformly on `0 ≤ nh ≤ T`;
* `geometric_feedback_resummation`: the boxed factored branch
  `R = B(I - D₀)⁻¹C` — for `‖D₀‖ < 1` the resummed feedback
  `∑ₖ B·D₀ᵏ·C` equals `B·(∑ₖ D₀ᵏ)·C` with
  `(1 - D₀)·(∑ₖ D₀ᵏ) = 1`, exhibiting the geometric sum as the
  exact Neumann inverse;
* `feedback_tail_summable`: the loading hypothesis
  `∑ₖ (k+1)‖Rₖ‖ < ∞` holds automatically on the factored branch
  `‖D₀ᵏ‖ ≤ M·rᵏ` with `r < 1`.

Rendering disclosed: the full telescoping of the delayed
recursion `X_{n+1,h} = A_h X_{n,h} + Σ K_{k,h} X_{n-1-k,h}`
against the exponential `e^{nh(G+R)}` (the discrete Duhamel sum
with the two vanishing-rate hypotheses) and the `o(h)`
disappearing branch are the manuscript's limit bookkeeping; the
uniform power comparison, the exact Neumann resummation, and the
tail summability are proved here.
-/

open Matrix

namespace NCG

section PowerComparison

variable {A : Type*} [NormedRing A]

/-- Discrete-Duhamel power comparison: step maps bounded by `M`
satisfy `‖Aⁿ⁺¹ - Eⁿ⁺¹‖ ≤ (n+1)·Mⁿ·‖A - E‖`. -/
theorem power_comparison_bound (X E : A) (M : ℝ)
    (hX : ‖X‖ ≤ M) (hE : ‖E‖ ≤ M) :
    ∀ n : ℕ, ‖X ^ (n + 1) - E ^ (n + 1)‖
      ≤ (n + 1 : ℝ) * M ^ n * ‖X - E‖ := by
  have hM : 0 ≤ M := le_trans (norm_nonneg X) hX
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : X ^ (n + 2) - E ^ (n + 2)
        = X * (X ^ (n + 1) - E ^ (n + 1))
          + (X - E) * E ^ (n + 1) := by
      rw [mul_sub, sub_mul, pow_succ' X (n + 1),
        pow_succ' E (n + 1)]
      abel
    have hEpow : ‖E ^ (n + 1)‖ ≤ M ^ (n + 1) := by
      calc ‖E ^ (n + 1)‖ ≤ ‖E‖ ^ (n + 1) :=
            norm_pow_le' E n.succ_pos
        _ ≤ M ^ (n + 1) := pow_le_pow_left₀ (norm_nonneg E) hE _
    calc ‖X ^ (n + 2) - E ^ (n + 2)‖
        ≤ ‖X * (X ^ (n + 1) - E ^ (n + 1))‖
          + ‖(X - E) * E ^ (n + 1)‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ ‖X‖ * ‖X ^ (n + 1) - E ^ (n + 1)‖
          + ‖X - E‖ * ‖E ^ (n + 1)‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ M * ((n + 1 : ℝ) * M ^ n * ‖X - E‖)
          + ‖X - E‖ * M ^ (n + 1) := by
          refine add_le_add (mul_le_mul hX ih (norm_nonneg _)
            hM) ?_
          exact mul_le_mul_of_nonneg_left hEpow (norm_nonneg _)
      _ = ((n + 1 : ℕ) + 1 : ℝ) * M ^ (n + 1) * ‖X - E‖ := by
          push_cast
          ring

end PowerComparison

section Resummation

variable {A : Type*} [NormedRing A] [CompleteSpace A]

/-- Boxed factored branch: for `‖D‖ < 1` the resummed feedback
is the exact Neumann composite — `∑ₖ B·Dᵏ·C = B·(∑ₖ Dᵏ)·C` and
`(1 - D)·(∑ₖ Dᵏ) = 1`, i.e. `R = B(I - D)⁻¹C`. -/
theorem geometric_feedback_resummation (B D C : A)
    (hD : ‖D‖ < 1) :
    (1 - D) * (∑' k : ℕ, D ^ k) = 1
      ∧ (∑' k : ℕ, B * D ^ k * C)
        = B * (∑' k : ℕ, D ^ k) * C := by
  have hsum : Summable fun k : ℕ => D ^ k :=
    summable_geometric_of_norm_lt_one hD
  refine ⟨mul_neg_geom_series D hD, ?_⟩
  have hsumC : Summable fun k : ℕ => D ^ k * C := hsum.mul_right C
  calc (∑' k : ℕ, B * D ^ k * C)
      = ∑' k : ℕ, B * (D ^ k * C) := by
        refine tsum_congr fun k => ?_
        rw [mul_assoc]
    _ = B * ∑' k : ℕ, D ^ k * C := hsumC.tsum_mul_left B
    _ = B * ((∑' k : ℕ, D ^ k) * C) := by
        rw [hsum.tsum_mul_right C]
    _ = B * (∑' k : ℕ, D ^ k) * C := by rw [mul_assoc]

end Resummation

/-- Loading summability on the factored branch: the weighted
tail `∑ₖ (k+1)·M·rᵏ` converges for `r < 1`. -/
theorem feedback_tail_summable (M r : ℝ) (hr : |r| < 1) :
    Summable fun k : ℕ => (k + 1 : ℝ) * M * r ^ k := by
  have h1 : Summable fun k : ℕ => (k : ℝ) * r ^ k := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (r := r) (by simpa using hr)
  have h2 : Summable fun k : ℕ => r ^ k :=
    summable_geometric_of_abs_lt_one hr
  have hsum : Summable fun k : ℕ => ((k : ℝ) + 1) * r ^ k := by
    have := h1.add h2
    refine this.congr fun k => ?_
    ring
  have := hsum.mul_right M
  refine this.congr fun k => ?_
  ring

section PerturbedEuler

variable {A : Type*} [NormedRing A] [NormOneClass A]

/-- Discrete Duhamel/Gronwall estimate for a perturbed left-Euler recursion.
This is the missing uniform-in-time core of the fast-feedback theorem. -/
theorem perturbed_euler_gronwall
    (E Y : A) (X error : ℕ → A) (M δ σ : ℝ)
    (hM : 1 ≤ M) (hE : ‖E‖ ≤ M) (hY : ‖Y‖ ≤ M)
    (hδ : ∀ n, ‖error n‖ ≤ δ) (hσ : ‖E - Y‖ ≤ σ)
    (hX0 : X 0 = 1)
    (hrec : ∀ n, X (n + 1) = E * X n + error n) :
    ∀ n : ℕ, ‖X n - Y ^ n‖ ≤ (n : ℝ) * M ^ n * (σ + δ) := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hσ0 : 0 ≤ σ := le_trans (norm_nonneg (E - Y)) hσ
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg (error 0)) (hδ 0)
  have hsd : 0 ≤ σ + δ := add_nonneg hσ0 hδ0
  intro n
  induction n with
  | zero => simp [hX0]
  | succ n ih =>
      have hsplit : X (n + 1) - Y ^ (n + 1)
          = E * (X n - Y ^ n) + (E - Y) * Y ^ n + error n := by
        rw [hrec, pow_succ']
        noncomm_ring
      have hpow : ‖Y ^ n‖ ≤ M ^ n := by
        cases n with
        | zero => simp
        | succ n =>
            calc
              ‖Y ^ (n + 1)‖ ≤ ‖Y‖ ^ (n + 1) :=
                norm_pow_le' Y (Nat.zero_lt_succ n)
              _ ≤ M ^ (n + 1) :=
                pow_le_pow_left₀ (norm_nonneg Y) hY (n + 1)
      rw [hsplit]
      calc
        ‖E * (X n - Y ^ n) + (E - Y) * Y ^ n + error n‖
            ≤ ‖E‖ * ‖X n - Y ^ n‖
              + ‖E - Y‖ * ‖Y ^ n‖ + ‖error n‖ := by
                calc
                  _ ≤ ‖E * (X n - Y ^ n)‖ + ‖(E - Y) * Y ^ n‖
                      + ‖error n‖ := by
                        exact (norm_add_le _ _).trans
                          (add_le_add (norm_add_le _ _) le_rfl)
                  _ ≤ _ := by gcongr <;> apply norm_mul_le
        _ ≤ M * ((n : ℝ) * M ^ n * (σ + δ))
              + σ * M ^ n + δ := by
                exact add_le_add
                  (add_le_add
                    (mul_le_mul hE ih (norm_nonneg _) hM0)
                    (mul_le_mul hσ hpow (norm_nonneg _) hσ0))
                  (hδ n)
        _ ≤ ((n + 1 : ℕ) : ℝ) * M ^ (n + 1)
              * (σ + δ) := by
                have hpowmono : M ^ n ≤ M ^ (n + 1) := by
                  rw [pow_succ]
                  exact le_mul_of_one_le_right (pow_nonneg hM0 n) hM
                have honepow : 1 ≤ M ^ (n + 1) := one_le_pow₀ hM
                have hsig : σ * M ^ n ≤ σ * M ^ (n + 1) :=
                  mul_le_mul_of_nonneg_left hpowmono hσ0
                have hdel : δ ≤ δ * M ^ (n + 1) := by
                  calc δ = δ * 1 := (mul_one δ).symm
                    _ ≤ δ * M ^ (n + 1) :=
                      mul_le_mul_of_nonneg_left honepow hδ0
                have hmain : M * ((n : ℝ) * M ^ n * (σ + δ))
                    ≤ (n : ℝ) * M ^ (n + 1) * (σ + δ) := by
                  have heq : M * ((n : ℝ) * M ^ n * (σ + δ))
                      = (n : ℝ) * M ^ (n + 1) * (σ + δ) := by
                    rw [pow_succ]
                    ring
                  exact heq.le
                calc
                  M * ((n : ℝ) * M ^ n * (σ + δ))
                        + σ * M ^ n + δ
                      ≤ (n : ℝ) * M ^ (n + 1) * (σ + δ)
                        + σ * M ^ (n + 1) + δ * M ^ (n + 1) := by
                          exact add_le_add (add_le_add hmain hsig) hdel
                  _ = ((n + 1 : ℕ) : ℝ) * M ^ (n + 1)
                        * (σ + δ) := by
                    push_cast
                    ring

variable [CompleteSpace A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]

/-- The exact exponential comparison for the perturbed Euler recursion. -/
theorem perturbed_euler_exponential_bound
    (L : A) (h : ℝ) (X error : ℕ → A) (M δ : ℝ)
    (hM : 1 ≤ M)
    (hE : ‖1 + h • L‖ ≤ M)
    (hY : ‖NormedSpace.exp (h • L)‖ ≤ M)
    (hδ : ∀ n, ‖error n‖ ≤ δ)
    (hX0 : X 0 = 1)
    (hrec : ∀ n, X (n + 1) = (1 + h • L) * X n + error n) :
    ∀ n : ℕ,
      ‖X n - NormedSpace.exp (((n : ℝ) * h) • L)‖
        ≤ (n : ℝ) * M ^ n
          * (‖1 + h • L - NormedSpace.exp (h • L)‖ + δ) := by
  intro n
  have hpow : (NormedSpace.exp (h • L)) ^ n
      = NormedSpace.exp (((n : ℝ) * h) • L) := by
    rw [← NormedSpace.exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [← hpow]
  exact perturbed_euler_gronwall
    (1 + h • L) (NormedSpace.exp (h • L)) X error M δ
    ‖1 + h • L - NormedSpace.exp (h • L)‖ hM hE hY hδ le_rfl hX0 hrec n

/-- A vanishing `o(h)` feedback mass disappears at generator scale. -/
theorem disappearing_feedback_generator_scale
    (kernelMass h ε : ℝ) (hh : 0 < h)
    (hsmall : kernelMass ≤ h * ε) :
    kernelMass / h ≤ ε := by
  exact (div_le_iff₀ hh).2 (by simpa [mul_comm] using hsmall)

/-- One delayed feedback summand splits into a kernel-approximation defect
and a time-translation defect.  The latter is precisely where the weighted
factor `(k+1)` in the manuscript hypothesis enters. -/
theorem delayed_feedback_term_bound
    (K R Xpast Xnow : A) (h B L w : ℝ)
    (hh : 0 ≤ h) (hB : 0 ≤ B) (hL : 0 ≤ L) (hw : 0 ≤ w)
    (hX : ‖Xpast‖ ≤ B)
    (hinc : ‖Xpast - Xnow‖ ≤ h * L * w) :
    ‖K * Xpast - h • (R * Xnow)‖
      ≤ ‖K - h • R‖ * B + h ^ 2 * L * (w * ‖R‖) := by
  have hsplit : K * Xpast - h • (R * Xnow)
      = (K - h • R) * Xpast + h • (R * (Xpast - Xnow)) := by
    rw [sub_mul, mul_sub, smul_sub, smul_mul_assoc]
    abel
  rw [hsplit]
  calc
    ‖(K - h • R) * Xpast + h • (R * (Xpast - Xnow))‖
        ≤ ‖(K - h • R) * Xpast‖
          + ‖h • (R * (Xpast - Xnow))‖ := norm_add_le _ _
    _ ≤ ‖K - h • R‖ * ‖Xpast‖
          + h * (‖R‖ * ‖Xpast - Xnow‖) := by
            gcongr
            · exact norm_mul_le _ _
            · calc
                ‖h • (R * (Xpast - Xnow))‖
                    = h * ‖R * (Xpast - Xnow)‖ := by
                        rw [norm_smul, Real.norm_eq_abs,
                          abs_of_nonneg hh]
                _ ≤ h * (‖R‖ * ‖Xpast - Xnow‖) := by
                      gcongr
                      exact norm_mul_le _ _
    _ ≤ ‖K - h • R‖ * B + h * (‖R‖ * (h * L * w)) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hX (norm_nonneg _))
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hinc (norm_nonneg R)) hh)
    _ = ‖K - h • R‖ * B + h ^ 2 * L * (w * ‖R‖) := by ring

/-- Finite delayed-memory estimate obtained by summing the preceding exact
termwise decomposition. -/
theorem delayed_feedback_sum_bound
    (n : ℕ) (K R : ℕ → A) (X : ℕ → A) (h B L : ℝ)
    (hh : 0 ≤ h) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hX : ∀ j, ‖X j‖ ≤ B)
    (hinc : ∀ k < n,
      ‖X (n - 1 - k) - X n‖ ≤ h * L * (k + 1 : ℝ)) :
    ‖∑ k ∈ Finset.range n,
        (K k * X (n - 1 - k) - h • (R k * X n))‖
      ≤ B * (∑ k ∈ Finset.range n, ‖K k - h • R k‖)
        + h ^ 2 * L *
          (∑ k ∈ Finset.range n, (k + 1 : ℝ) * ‖R k‖) := by
  calc
    ‖∑ k ∈ Finset.range n,
        (K k * X (n - 1 - k) - h • (R k * X n))‖
        ≤ ∑ k ∈ Finset.range n,
          ‖K k * X (n - 1 - k) - h • (R k * X n)‖ :=
            norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n,
          (‖K k - h • R k‖ * B
            + h ^ 2 * L * ((k + 1 : ℝ) * ‖R k‖)) := by
          gcongr with k hk
          exact delayed_feedback_term_bound
            (K k) (R k) (X (n - 1 - k)) (X n)
            h B L (k + 1 : ℝ) hh hB hL (by positivity)
            (hX _) (hinc k (Finset.mem_range.1 hk))
    _ = B * (∑ k ∈ Finset.range n, ‖K k - h • R k‖)
        + h ^ 2 * L *
          (∑ k ∈ Finset.range n, (k + 1 : ℝ) * ‖R k‖) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
          · rw [Finset.mul_sum]

/-- Uniform physical-time conversion: if `M ≤ exp(C h)` and `nh ≤ T`,
then the discrete Duhamel factor `n M^n ε` is bounded by
`T exp(C T) ε/h`. -/
theorem euler_error_uniform_on_time_window
    (n : ℕ) (M C h T ε : ℝ)
    (hM0 : 0 ≤ M) (hC : 0 ≤ C) (hh : 0 < h)
    (hM : M ≤ Real.exp (C * h))
    (hwindow : (n : ℝ) * h ≤ T) (hε : 0 ≤ ε) :
    (n : ℝ) * M ^ n * ε
      ≤ T * Real.exp (C * T) * (ε / h) := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hT : 0 ≤ T := le_trans (mul_nonneg hn0 hh.le) hwindow
  have hpow : M ^ n ≤ Real.exp (C * T) := by
    calc
      M ^ n ≤ (Real.exp (C * h)) ^ n :=
        pow_le_pow_left₀ hM0 hM n
      _ = Real.exp (C * ((n : ℝ) * h)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ Real.exp (C * T) := by
        exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hwindow hC)
  have hnT : (n : ℝ) ≤ T / h := (le_div_iff₀ hh).2 hwindow
  calc
    (n : ℝ) * M ^ n * ε
        ≤ (T / h) * Real.exp (C * T) * ε := by
          gcongr
    _ = T * Real.exp (C * T) * (ε / h) := by ring

/-- Sequence form of the boxed fast-feedback conclusion.  A compiled
perturbed Euler bound plus a per-step defect `ε_h=o(h)` yields convergence
uniformly over every fixed physical-time window. -/
theorem fast_feedback_uniform_collapse
    (h ε : ℕ → ℝ) (C T : ℝ)
    (hh : ∀ m, 0 < h m) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hε0 : ∀ m, 0 ≤ ε m)
    (hsmall : Filter.Tendsto (fun m => ε m / h m)
      Filter.atTop (nhds 0))
    (err : ℕ → ℕ → ℝ)
    (herr : ∀ m (n : ℕ), (n : ℝ) * h m ≤ T →
      err m n ≤ (n : ℝ) * (Real.exp (C * h m)) ^ n * ε m) :
    ∀ δ > 0, ∃ m0, ∀ m ≥ m0, ∀ (n : ℕ),
      (n : ℝ) * h m ≤ T → err m n < δ := by
  intro δ hδ
  have hconst : 0 ≤ T * Real.exp (C * T) := by
    positivity
  by_cases hzero : T * Real.exp (C * T) = 0
  · refine ⟨0, fun m _ n hn => ?_⟩
    have hu := euler_error_uniform_on_time_window n
      (Real.exp (C * h m)) C (h m) T (ε m)
      (Real.exp_nonneg _) hC (hh m) le_rfl hn (hε0 m)
    rw [hzero, zero_mul] at hu
    have he := herr m n hn
    linarith
  · have hcpos : 0 < T * Real.exp (C * T) := lt_of_le_of_ne hconst
        (Ne.symm hzero)
    have ht := (Metric.tendsto_atTop.1 hsmall)
      (δ / (T * Real.exp (C * T))) (by positivity)
    obtain ⟨m0, hm0⟩ := ht
    refine ⟨m0, fun m hm n hn => ?_⟩
    have he := herr m n hn
    have hu := euler_error_uniform_on_time_window n
      (Real.exp (C * h m)) C (h m) T (ε m)
      (Real.exp_nonneg _) hC (hh m) le_rfl hn (hε0 m)
    have hs := hm0 m hm
    rw [Real.dist_eq, sub_zero] at hs
    have hratio : ε m / h m < δ / (T * Real.exp (C * T)) := by
      have hr0 : 0 ≤ ε m / h m := div_nonneg (hε0 m) (hh m).le
      simpa [abs_of_nonneg hr0] using hs
    have hprod : T * Real.exp (C * T) * (ε m / h m) < δ := by
      rw [lt_div_iff₀ hcpos] at hratio
      simpa [mul_comm, mul_left_comm, mul_assoc] using hratio
    exact he.trans_lt (hu.trans_lt hprod)

end PerturbedEuler

end NCG
