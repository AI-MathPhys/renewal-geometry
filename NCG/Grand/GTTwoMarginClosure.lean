/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Two-margin source-complete coercivity
  (`thm:GT-two-margin-closure`, Gran-Tensor manuscript)

* `gt_two_margin_closure`: the boxed SA.11 ⟹ SA.12
  implication on the moment carrier — if the shifted
  Hankel localizer dominates the Hankel Gram,
  `𝕃^{≤θ} ⪰ β𝔾` (SA.11, rendered per coefficient
  vector), then for every vector
  `v = ∑ₙ cₙ Tⁿ j ∈ 𝒦_{J,N}` in the source-generated
  Krylov carrier, `⟨v, Tv⟩ ≤ (θ-β)⟨v, v⟩` — the boxed
  `T ⪯ (θ-β)I` on the carrier reached by the source.

The transfer from the Krylov carrier to the complete
physical carrier under the boxed atlas-margin condition
SA.10 (`‖U*(I-P_{J,N})U‖ < m_U`), and the constructive
failure branches (missing source bank via
`thm:GT-atlas-completeness`, soft response history from a
negative localizer vector), are the manuscript's atlas
layer.
-/

open scoped InnerProductSpace
open Finset

namespace NCG

/-- `thm:GT-two-margin-closure` (Hankel coercivity on the
source-generated carrier). -/
theorem gt_two_margin_closure {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : V →ₗ[ℝ] V)
    (hsa : ∀ x y : V, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ)
    (j : V) (N : ℕ) (θ β : ℝ)
    -- SA.11: the localizer dominates the Hankel Gram
    (hloc : ∀ c : ℕ → ℝ,
      β * (∑ i ∈ range N, ∑ l ∈ range N,
          c i * (c l * ⟪j, (T ^ (i + l)) j⟫_ℝ))
        ≤ ∑ i ∈ range N, ∑ l ∈ range N,
            c i * (c l * (θ * ⟪j, (T ^ (i + l)) j⟫_ℝ
              - ⟪j, (T ^ (i + l + 1)) j⟫_ℝ))) :
    -- SA.12 on the source-generated carrier
    ∀ c : ℕ → ℝ,
      ⟪∑ i ∈ range N, c i • (T ^ i) j,
        T (∑ i ∈ range N, c i • (T ^ i) j)⟫_ℝ
      ≤ (θ - β) * ⟪∑ i ∈ range N, c i • (T ^ i) j,
          ∑ i ∈ range N, c i • (T ^ i) j⟫_ℝ := by
  -- move powers of T across the inner product
  have hmove : ∀ (n : ℕ) (x y : V),
      ⟪(T ^ n) x, y⟫_ℝ = ⟪x, (T ^ n) y⟫_ℝ := by
    intro n
    induction n with
    | zero => intro x y; simp
    | succ n ih =>
      intro x y
      have h1 : (T ^ (n + 1)) x = T ((T ^ n) x) := by
        rw [pow_succ', Module.End.mul_apply]
      have h2 : (T ^ (n + 1)) y = (T ^ n) (T y) := by
        rw [pow_succ, Module.End.mul_apply]
      rw [h1, hsa, ih, h2]
  have hVij : ∀ i l : ℕ,
      ⟪(T ^ i) j, (T ^ l) j⟫_ℝ
        = ⟪j, (T ^ (i + l)) j⟫_ℝ := by
    intro i l
    rw [hmove i, ← Module.End.mul_apply, ← pow_add]
  intro c
  set v := ∑ i ∈ range N, c i • (T ^ i) j with hv
  have hgram : ⟪v, v⟫_ℝ
      = ∑ i ∈ range N, ∑ l ∈ range N,
          c i * (c l * ⟪j, (T ^ (i + l)) j⟫_ℝ) := by
    rw [hv, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right,
      hVij]
  have hTv : T v = ∑ l ∈ range N,
      c l • (T ^ (l + 1)) j := by
    rw [hv, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul]
    congr 1
    rw [pow_succ', Module.End.mul_apply]
  have hshift : ⟪v, T v⟫_ℝ
      = ∑ i ∈ range N, ∑ l ∈ range N,
          c i * (c l * ⟪j, (T ^ (i + l + 1)) j⟫_ℝ) := by
    rw [hTv, hv, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right,
      hVij]
    ring_nf
  have hsplit : ∑ i ∈ range N, ∑ l ∈ range N,
      c i * (c l * (θ * ⟪j, (T ^ (i + l)) j⟫_ℝ
        - ⟪j, (T ^ (i + l + 1)) j⟫_ℝ))
      = θ * (∑ i ∈ range N, ∑ l ∈ range N,
          c i * (c l * ⟪j, (T ^ (i + l)) j⟫_ℝ))
        - ∑ i ∈ range N, ∑ l ∈ range N,
            c i * (c l * ⟪j, (T ^ (i + l + 1)) j⟫_ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => by ring
  have h := hloc c
  rw [hsplit, ← hgram, ← hshift] at h
  linarith

end NCG
