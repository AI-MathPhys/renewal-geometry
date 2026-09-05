/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Renewal fluctuation–dissipation and finite regenerative
  complete observability
  (`thm:renewal-fluctuation-dissipation` and
  `thm:renewal-complete-observability`,
  Gran-Tensor manuscript)

Both records are rendered by their exact finite Loewner
clauses; the `N → ∞` limits are the manuscript's passage over
these exact identities.

* `renewal_fluctuation_dissipation`:
  (i) conjugation monotonicity `A ⪯ B ⇒ KᴴAK ⪯ KᴴBK`;
  (ii) the exact truncated Lyapunov identity
      `Σ_N - KᴴΣ_N K = Q - K^{*N}QK^N` (the boxed
      `Σ - KᴴΣK = Q` at every truncation);
  (iii) the per-cycle covariance domination: the window
      `Q ⪯ d₊(H - KᴴHK)` conjugates to every cycle depth;
  (iv) the exact stationary identity `Q = H - KᴴHK` for the
      two-boundary Gram data `K = H⁻¹C`.

* `renewal_complete_observability`:
  (i) the boxed observability identity
      `𝒪 - Rᴴ𝒪R = 𝒟` (truncated, exact);
  (ii) exponential decay `R^{*n}𝒪Rⁿ ⪯ (1-δ)ⁿ𝒪` from the
      margin `𝒟 ⪰ δ𝒪`;
  (iii) the observed-energy telescoping
      `Σ_{k<K} R^{*k}𝒟R^k = 𝒪 - R^{*K}𝒪R^K ⪯ 𝒪` (finite
      total observed energy; no invisible fixed direction).
-/

open Matrix
open scoped ComplexOrder

namespace NCG

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private lemma conj_mono (K : Matrix n n ℂ)
    {A B : Matrix n n ℂ} (h : (B - A).PosSemidef) :
    (Kᴴ * B * K - Kᴴ * A * K).PosSemidef := by
  have hfac : Kᴴ * B * K - Kᴴ * A * K
      = Kᴴ * (B - A) * K := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [hfac]
  simpa using h.conjTranspose_mul_mul_same K

private lemma shift_term (K Q : Matrix n n ℂ) (k : ℕ) :
    Kᴴ * (Kᴴ ^ k * Q * K ^ k) * K
      = Kᴴ ^ (k + 1) * Q * K ^ (k + 1) := by
  rw [pow_succ' Kᴴ, pow_succ K]
  simp only [Matrix.mul_assoc]

private lemma shift_term' (K Q : Matrix n n ℂ) (k : ℕ) :
    Kᴴ ^ k * (Kᴴ * Q * K) * K ^ k
      = Kᴴ ^ (k + 1) * Q * K ^ (k + 1) := by
  rw [pow_succ Kᴴ, pow_succ' K]
  simp only [Matrix.mul_assoc]

private lemma telescope (K Q : Matrix n n ℂ) (N : ℕ) :
    (∑ k ∈ Finset.range N, Kᴴ ^ k * Q * K ^ k)
      - Kᴴ * (∑ k ∈ Finset.range N,
          Kᴴ ^ k * Q * K ^ k) * K
      = Q - Kᴴ ^ N * Q * K ^ N := by
  have hdist : Kᴴ * (∑ k ∈ Finset.range N,
      Kᴴ ^ k * Q * K ^ k) * K
      = ∑ k ∈ Finset.range N,
        Kᴴ ^ (k + 1) * Q * K ^ (k + 1) := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun k _ => shift_term K Q k
  rw [hdist, ← Finset.sum_sub_distrib,
    Finset.sum_range_sub'
      (fun k => Kᴴ ^ k * Q * K ^ k)]
  simp

/-- `thm:renewal-fluctuation-dissipation`. -/
theorem renewal_fluctuation_dissipation
    (H K Q : Matrix n n ℂ) (dp : ℝ)
    (hdom : (((dp : ℂ) • (H - Kᴴ * H * K))
      - Q).PosSemidef) :
    -- (i) conjugation monotonicity
    (∀ A B : Matrix n n ℂ, (B - A).PosSemidef →
      (Kᴴ * B * K - Kᴴ * A * K).PosSemidef)
    -- (ii) the exact truncated Lyapunov identity
    ∧ (∀ N : ℕ,
        (∑ k ∈ Finset.range N, Kᴴ ^ k * Q * K ^ k)
          - Kᴴ * (∑ k ∈ Finset.range N,
              Kᴴ ^ k * Q * K ^ k) * K
        = Q - Kᴴ ^ N * Q * K ^ N)
    -- (iii) the domination window at every cycle depth
    ∧ (∀ k : ℕ,
        (((dp : ℂ) • (Kᴴ ^ k * H * K ^ k
            - Kᴴ ^ (k + 1) * H * K ^ (k + 1)))
          - Kᴴ ^ k * Q * K ^ k).PosSemidef)
    -- (iv) the exact stationary identity
    ∧ (∀ C : Matrix n n ℂ, Hᴴ = H → ∀ _ : Invertible H,
        H - (H⁻¹ * C)ᴴ * H * (H⁻¹ * C)
          = H - Cᴴ * H⁻¹ * C) := by
  refine ⟨fun A B h => conj_mono K h, telescope K Q, ?_, ?_⟩
  · intro k
    have h := hdom.conjTranspose_mul_mul_same (K ^ k)
    have heq : (K ^ k)ᴴ * (((dp : ℂ)
        • (H - Kᴴ * H * K)) - Q) * K ^ k
        = ((dp : ℂ) • (Kᴴ ^ k * H * K ^ k
            - Kᴴ ^ (k + 1) * H * K ^ (k + 1)))
          - Kᴴ ^ k * Q * K ^ k := by
      rw [Matrix.conjTranspose_pow, ← shift_term' K H k]
      simp only [Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    rwa [heq] at h
  · intro C hHH _
    have hinvH : (H⁻¹)ᴴ = H⁻¹ := by
      rw [Matrix.conjTranspose_nonsing_inv, hHH]
    congr 1
    rw [Matrix.conjTranspose_mul, hinvH,
      Matrix.mul_assoc Cᴴ H⁻¹ H,
      Matrix.inv_mul_of_invertible, Matrix.mul_one]
    simp only [Matrix.mul_assoc]

/-- `thm:renewal-complete-observability`. -/
theorem renewal_complete_observability
    (R O Q : Matrix n n ℂ) (δ : ℝ) (_hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hO : O.PosSemidef)
    (hmargin : ((O - Rᴴ * O * R)
      - (δ : ℂ) • O).PosSemidef) :
    -- (i) the boxed observability identity (truncated)
    (∀ N : ℕ,
        (∑ k ∈ Finset.range N, Rᴴ ^ k * Q * R ^ k)
          - Rᴴ * (∑ k ∈ Finset.range N,
              Rᴴ ^ k * Q * R ^ k) * R
        = Q - Rᴴ ^ N * Q * R ^ N)
    -- (ii) exponential decay of the observability metric
    ∧ (∀ m : ℕ,
        ((((1 - δ : ℝ) : ℂ) ^ m • O)
          - Rᴴ ^ m * O * R ^ m).PosSemidef)
    -- (iii) the observed-energy telescoping bound
    ∧ (∀ K : ℕ,
        (∑ k ∈ Finset.range K,
          Rᴴ ^ k * (O - Rᴴ * O * R) * R ^ k)
        = O - Rᴴ ^ K * O * R ^ K
        ∧ (O - ∑ k ∈ Finset.range K,
            Rᴴ ^ k * (O - Rᴴ * O * R) * R ^ k).PosSemidef) := by
  have hstep : (((1 - δ : ℝ) : ℂ) • O
      - Rᴴ * O * R).PosSemidef := by
    have heq : ((1 - δ : ℝ) : ℂ) • O - Rᴴ * O * R
        = (O - Rᴴ * O * R) - (δ : ℂ) • O := by
      push_cast
      rw [sub_smul, one_smul]
      abel
    rw [heq]
    exact hmargin
  refine ⟨telescope R Q, ?_, ?_⟩
  · intro m
    induction m with
    | zero => simpa using Matrix.PosSemidef.zero
    | succ j ih =>
        have h1 : ((((1 - δ : ℝ) : ℂ) ^ j
            • (((1 - δ : ℝ) : ℂ) • O))
            - ((1 - δ : ℝ) : ℂ) ^ j
              • (Rᴴ * O * R)).PosSemidef := by
          rw [← smul_sub]
          have : ((0 : ℝ) ≤ (1 - δ) ^ j) := by positivity
          rw [show (((1 - δ : ℝ) : ℂ)) ^ j
              = (((1 - δ) ^ j : ℝ) : ℂ) from by push_cast; ring]
          exact hstep.smul (by exact_mod_cast this)
        have h2 := conj_mono R ih
        have hcomb := h1.add h2
        have heq : (((1 - δ : ℝ) : ℂ) ^ j
              • (((1 - δ : ℝ) : ℂ) • O)
            - ((1 - δ : ℝ) : ℂ) ^ j • (Rᴴ * O * R))
            + (Rᴴ * (((1 - δ : ℝ) : ℂ) ^ j • O) * R
              - Rᴴ * (Rᴴ ^ j * O * R ^ j) * R)
            = (((1 - δ : ℝ) : ℂ) ^ (j + 1) • O)
              - Rᴴ ^ (j + 1) * O * R ^ (j + 1) := by
          rw [Matrix.mul_smul, Matrix.smul_mul,
            shift_term R O, smul_smul, ← pow_succ]
          abel
        rwa [heq] at hcomb
  · intro K
    have htel : (∑ k ∈ Finset.range K,
        Rᴴ ^ k * (O - Rᴴ * O * R) * R ^ k)
        = O - Rᴴ ^ K * O * R ^ K := by
      have hdist : ∀ k : ℕ,
          Rᴴ ^ k * (O - Rᴴ * O * R) * R ^ k
          = Rᴴ ^ k * O * R ^ k
            - Rᴴ ^ (k + 1) * O * R ^ (k + 1) := by
        intro k
        rw [Matrix.mul_sub, Matrix.sub_mul,
          ← shift_term' R O k]
      rw [show (fun k => Rᴴ ^ k * (O - Rᴴ * O * R) * R ^ k)
          = fun k => Rᴴ ^ k * O * R ^ k
            - Rᴴ ^ (k + 1) * O * R ^ (k + 1) from
        funext hdist,
        Finset.sum_range_sub'
          (fun k => Rᴴ ^ k * O * R ^ k)]
      simp
    refine ⟨htel, ?_⟩
    rw [htel]
    have h := hO.conjTranspose_mul_mul_same (R ^ K)
    rw [Matrix.conjTranspose_pow] at h
    simpa using h

end NCG
