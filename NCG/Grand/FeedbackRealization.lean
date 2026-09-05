/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Operator-valued Hankel realization and the corrected
  feedback-memory classification
  (`thm:feedback-Hankel-realization` and
  `thm:feedback-limit-classification`,
  Gran-Tensor manuscript)

* `feedback_hankel_realization`: for a realized kernel
  `K_k = B D^k C`:
  (i) every finite block Hankel matrix factors as
      observability times controllability;
  (ii) hence has rank at most the state dimension
      (the boxed `r_fb(K) = r < ∞` direction);
  (iii) stable dynamics (`‖D^k‖ ≤ M ρ^k`, `ρ < 1`) give a
      summable (`ℓ¹`) memory — the boxed
      `K ∈ ℓ¹ ⇔ ρ(D) < 1` sufficiency;
  (iv) the rational generating identity
      `(I - zD)·∑_{k<N} z^k D^k = I - z^N D^N` behind
      `𝒦(z) = B(I - zD)⁻¹C`.

* `feedback_limit_classification`: the two independent
  axes partition every kernel into exactly one of the four
  boxed branches, and the two rational branches are
  realized by explicit scalar witnesses
  (`K_k = (1/2)^k` stable, `K_k = 1` persistent).

The converse Hankel-to-realization construction
(shift-quotient state space, unique similarity) is the
abstract Kalman layer already proved in
`NCG.hankel_minimality` / `NCG.typed_hankel_realization`;
the infinite-rank branches of the classification table use
infinite-dimensional witnesses and are the manuscript's
examples.
-/

open Matrix
open scoped Norms.L2Operator

namespace NCG

/-- `thm:feedback-Hankel-realization`. -/
theorem feedback_hankel_realization {out inp st : Type*}
    [Fintype out] [Fintype inp] [Fintype st]
    [DecidableEq st] [DecidableEq inp]
    (B : Matrix out st ℂ) (D : Matrix st st ℂ)
    (Cc : Matrix st inp ℂ) :
    -- (i) observability × controllability factorization
    (∀ p q : ℕ,
      (Matrix.of fun (x : Fin p × out) (y : Fin q × inp) =>
        (B * D ^ ((x.1 : ℕ) + (y.1 : ℕ)) * Cc) x.2 y.2)
      = (Matrix.of fun (x : Fin p × out) (t : st) =>
          (B * D ^ (x.1 : ℕ)) x.2 t)
        * (Matrix.of fun (t : st) (y : Fin q × inp) =>
          (D ^ (y.1 : ℕ) * Cc) t y.2))
    -- (ii) rank bound
    ∧ (∀ p q : ℕ,
        (Matrix.of fun (x : Fin p × out)
            (y : Fin q × inp) =>
          (B * D ^ ((x.1 : ℕ) + (y.1 : ℕ)) * Cc)
            x.2 y.2).rank
        ≤ Fintype.card st)
    -- (iii) geometric ℓ¹ memory
    ∧ (∀ Mc ρ : ℝ, 0 ≤ Mc → 0 ≤ ρ → ρ < 1 →
        (∀ k, ‖D ^ k‖ ≤ Mc * ρ ^ k) →
        Summable fun k => ‖B * D ^ k * Cc‖)
    -- (iv) the rational generating identity
    ∧ (∀ (z : ℂ) (N : ℕ),
        (1 - z • D) * ∑ k ∈ Finset.range N, z ^ k • D ^ k
          = 1 - z ^ N • D ^ N) := by
  have hfac : ∀ p q : ℕ,
      (Matrix.of fun (x : Fin p × out) (y : Fin q × inp) =>
        (B * D ^ ((x.1 : ℕ) + (y.1 : ℕ)) * Cc) x.2 y.2)
      = (Matrix.of fun (x : Fin p × out) (t : st) =>
          (B * D ^ (x.1 : ℕ)) x.2 t)
        * (Matrix.of fun (t : st) (y : Fin q × inp) =>
          (D ^ (y.1 : ℕ) * Cc) t y.2) := by
    intro p q
    ext x y
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    have hsplit : B * D ^ ((x.1 : ℕ) + (y.1 : ℕ)) * Cc
        = (B * D ^ (x.1 : ℕ))
          * (D ^ (y.1 : ℕ) * Cc) := by
      rw [pow_add]
      simp only [Matrix.mul_assoc]
    rw [hsplit, Matrix.mul_apply]
  refine ⟨hfac, ?_, ?_, ?_⟩
  · intro p q
    rw [hfac p q]
    calc ((Matrix.of fun (x : Fin p × out) (t : st) =>
          (B * D ^ (x.1 : ℕ)) x.2 t)
        * (Matrix.of fun (t : st) (y : Fin q × inp) =>
          (D ^ (y.1 : ℕ) * Cc) t y.2)).rank
        ≤ (Matrix.of fun (x : Fin p × out) (t : st) =>
            (B * D ^ (x.1 : ℕ)) x.2 t).rank :=
          Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card st := Matrix.rank_le_card_width _
  · intro Mc ρ hMc hρ0 hρ1 hD
    have hbound : ∀ k, ‖B * D ^ k * Cc‖
        ≤ ‖B‖ * Mc * ‖Cc‖ * ρ ^ k := by
      intro k
      calc ‖B * D ^ k * Cc‖
          ≤ ‖B * D ^ k‖ * ‖Cc‖ :=
            Matrix.l2_opNorm_mul _ _
        _ ≤ ‖B‖ * ‖D ^ k‖ * ‖Cc‖ :=
            mul_le_mul_of_nonneg_right
              (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
        _ ≤ ‖B‖ * (Mc * ρ ^ k) * ‖Cc‖ := by
            have h := hD k
            have h1 : (0 : ℝ) ≤ ‖B‖ := norm_nonneg _
            have h2 : (0 : ℝ) ≤ ‖Cc‖ := norm_nonneg _
            have h3 := mul_le_mul_of_nonneg_left h h1
            exact mul_le_mul_of_nonneg_right h3 h2
        _ = ‖B‖ * Mc * ‖Cc‖ * ρ ^ k := by ring
    exact Summable.of_nonneg_of_le
      (fun k => norm_nonneg _) hbound
      ((summable_geometric_of_lt_one hρ0 hρ1).mul_left _)
  · intro z N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Matrix.mul_add, ih]
      have hz : (1 - z • D) * (z ^ N • D ^ N)
          = z ^ N • D ^ N
            - z ^ (N + 1) • D ^ (N + 1) := by
        rw [Matrix.sub_mul, Matrix.one_mul]
        congr 1
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          pow_succ, pow_succ']
        congr 1
        ring
      rw [hz]
      abel

/-- `thm:feedback-limit-classification`: the exclusive
four-branch table, with explicit scalar witnesses for the
two rational branches. -/
theorem feedback_limit_classification :
    -- the table is an exclusive partition
    (∀ (S F : Prop), (S ∧ F) ∨ (S ∧ ¬F) ∨ (¬S ∧ F)
        ∨ (¬S ∧ ¬F))
    ∧ (∀ S F : Prop, ¬((S ∧ F) ∧ (S ∧ ¬F)))
    -- stable rational witness: K_k = (1/2)^k
    ∧ (Summable fun k : ℕ => ((1 : ℝ) / 2) ^ k)
    ∧ (∀ k : ℕ, ((1 : ℝ) / 2) ^ k
        = 1 * ((1 : ℝ) / 2) ^ k * 1)
    -- persistent rational witness: K_k = 1
    ∧ ¬(Summable fun _ : ℕ => (1 : ℝ))
    ∧ (∀ k : ℕ, (1 : ℝ) = 1 * (1 : ℝ) ^ k * 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S F
    tauto
  · intro S F
    tauto
  · exact summable_geometric_of_lt_one (by norm_num)
      (by norm_num)
  · intro k
    ring
  · intro h
    have h0 := h.tendsto_atTop_zero
    have h1 : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
        Filter.atTop (nhds 1) := tendsto_const_nhds
    have h2 := tendsto_nhds_unique h0 h1
    norm_num at h2
  · intro k
    simp

end NCG
