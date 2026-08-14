/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTEffectiveShort

/-!
# Two-scale Yang–Mills Feshbach gap, invariant occurrence
  short, and the critical source–sheet Pythagoras
  (`thm:YM-two-scale-Feshbach`, `thm:Hodge-occurrence-short`,
  `thm:NS-source-sheet-pythagoras`, Gran-Tensor manuscript)

* `ym_two_scale_feshbach`:
  (i) the boxed combined floor
      `L ⪰ min{δ_IR/(1+2β²), γ_UV/2}` in quadratic-form
      terms, from the IR Schur floor, the UV block floor,
      and the norm domination
      `‖x⊕y‖² ≤ (1+2β²)‖x‖² + 2‖z‖²`;
  (ii) the norm domination itself, from
      `‖y‖ ≤ ‖z‖ + β‖x‖` (the corrector bound
      `‖C⁻¹B*x‖ ≤ β‖x‖`).

* `hodge_occurrence_short`: the kernel-return clause — a
  kernel vector `p` of the invariant Schur complement
  `S = A - BC⁻¹B*` returns the explicit invariant
  obstruction `p ⊕ (-C⁻¹B*p) ∈ Ker G` (instance of
  `NCG.gt_effective_action`).

* `ns_source_sheet_pythagoras`: the boxed NS.1 split — for
  orthogonal sheet writers and a residual orthogonal to
  both, `‖g‖² = a²D₊ + b²D₋ + ‖r‖²` with the sheet works
  `⟨v_σ, g⟩ = (coefficient)·D_σ`, so the visible term is
  `∑ D_σ† j_σ²` and the rest is the complete work-null
  source.

The reflection-positive regulator family, the exponentiation
`T = e^{-τL}` converting a generator floor into a transfer
contraction, and the NS.2 within-fibre refinement (the
weighted variance split, `NCG.gt_source_record_variance`)
are the manuscript's surrounding layers.
-/

open Matrix
open scoped InnerProductSpace

namespace NCG

/-- `thm:YM-two-scale-Feshbach` (quadratic-form
version). -/
theorem ym_two_scale_feshbach :
    -- (i) the boxed combined floor
    (∀ full s c nx nz ntot δ γ β : ℝ,
      0 < δ → 0 < γ → 0 ≤ β →
      0 ≤ nx → 0 ≤ nz →
      full = s + c → δ * nx ≤ s → γ * nz ≤ c →
      ntot ≤ (1 + 2 * β ^ 2) * nx + 2 * nz →
      min (δ / (1 + 2 * β ^ 2)) (γ / 2) * ntot ≤ full)
    -- (ii) the norm domination from the corrector bound
    ∧ (∀ a b β : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ β →
        a ^ 2 + (b + β * a) ^ 2
          ≤ (1 + 2 * β ^ 2) * a ^ 2 + 2 * b ^ 2) := by
  constructor
  · intro full s c nx nz ntot δ γ β hδ hγ hβ hnx hnz
      hfull hs hc hdom
    have hden : (0 : ℝ) < 1 + 2 * β ^ 2 := by positivity
    set m := min (δ / (1 + 2 * β ^ 2)) (γ / 2) with hm
    have hm1 : m ≤ δ / (1 + 2 * β ^ 2) := min_le_left _ _
    have hm2 : m ≤ γ / 2 := min_le_right _ _
    have hm0 : 0 ≤ m := by
      rw [hm]
      apply le_min <;> positivity
    have hk1 : m * (1 + 2 * β ^ 2) ≤ δ := by
      rw [← le_div_iff₀ hden]
      exact hm1
    have hk2 : m * 2 ≤ γ := by
      have := hm2
      linarith [((le_div_iff₀ (by norm_num : (0:ℝ) < 2)).mp
        hm2)]
    calc m * ntot
        ≤ m * ((1 + 2 * β ^ 2) * nx + 2 * nz) :=
          mul_le_mul_of_nonneg_left hdom hm0
      _ = (m * (1 + 2 * β ^ 2)) * nx + (m * 2) * nz := by
          ring
      _ ≤ δ * nx + γ * nz := by
          have h1 := mul_le_mul_of_nonneg_right hk1 hnx
          have h2 := mul_le_mul_of_nonneg_right hk2 hnz
          linarith
      _ ≤ s + c := by linarith
      _ = full := hfull.symm
  · intro a b β ha hb hβ
    nlinarith [sq_nonneg (b - β * a), sq_nonneg (β * a),
      mul_nonneg (mul_nonneg hβ ha) hb]

set_option linter.unusedFintypeInType false in
/-- `thm:Hodge-occurrence-short` (kernel-return clause). -/
theorem hodge_occurrence_short {P Q m : Type} [Fintype P]
    [Fintype Q] [Fintype m] [DecidableEq Q]
    (A : Matrix P P ℂ) (B : Matrix P Q ℂ)
    (C : Matrix Q Q ℂ) [Invertible C]
    (X : Matrix P m ℂ)
    (hker : (A - B * C⁻¹ * Bᴴ) * X = 0) :
    -- the boxed explicit invariant obstruction
    A * X + B * (-(C⁻¹ * (Bᴴ * X))) = 0
    ∧ Bᴴ * X + C * (-(C⁻¹ * (Bᴴ * X))) = 0 := by
  exact ((gt_effective_action A B C).1 X
    (-(C⁻¹ * (Bᴴ * X)))).mpr ⟨hker, rfl⟩

/-- `thm:NS-source-sheet-pythagoras` (the boxed NS.1
split). -/
theorem ns_source_sheet_pythagoras {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (vp vm r g : V) (a b : ℝ)
    (hg : g = a • vp + b • vm + r)
    (hpm : ⟪vp, vm⟫_ℝ = 0)
    (hpr : ⟪vp, r⟫_ℝ = 0) (hmr : ⟪vm, r⟫_ℝ = 0) :
    -- the boxed orthogonal energy split
    (‖g‖ ^ 2 = a ^ 2 * ‖vp‖ ^ 2 + b ^ 2 * ‖vm‖ ^ 2
      + ‖r‖ ^ 2)
    -- the signed sheet works identify the coefficients
    ∧ (⟪vp, g⟫_ℝ = a * ‖vp‖ ^ 2)
    ∧ (⟪vm, g⟫_ℝ = b * ‖vm‖ ^ 2) := by
  have hmp : ⟪vm, vp⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hpm
  have hrp : ⟪r, vp⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hpr
  have hrm : ⟪r, vm⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hmr
  refine ⟨?_, ?_, ?_⟩
  · have hexp : ‖g‖ ^ 2 = ⟪g, g⟫_ℝ :=
      (real_inner_self_eq_norm_sq g).symm
    rw [hexp, hg]
    simp only [inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right,
      hpm, hmp, hpr, hmr, hrp, hrm,
      real_inner_self_eq_norm_sq]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs]
    ring
  · rw [hg]
    simp only [inner_add_right, real_inner_smul_right,
      hpm, hpr, real_inner_self_eq_norm_sq]
    ring
  · rw [hg]
    simp only [inner_add_right, real_inner_smul_right,
      hmp, hmr, real_inner_self_eq_norm_sq]
    ring

end NCG
