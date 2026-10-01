/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.VectorLineTaylorRemainderBound
import RenewalGeometry.Gravity.GowdySplittingConsistencyExact

/-!
# Second-order consistency of characteristic Strang splitting

A semilinear hyperbolic system in one space dimension

`∂_τ Z = (Π₊ - Π₋) ∂_θ Z + F(Z)`,   `∂_τ λ = g₊(Z) + g₋(Z)`

(`Π₊, Π₋, Π₀` linear projections with `Π₊ + Π₋ + Π₀ = 1`, the right/left-moving
characteristic parts and the non-moving part) is discretised on a grid of spacing `ℓ = h`
by the symmetric splitting

* source half-step: implicit midpoint `Y = X + (h/2) F((X+Y)/2)` at every site;
* transport: exact characteristic shift `Y ↦ Π₊ Y_{j+1} + Π₋ Y_{j-1} + Π₀ Y_j`,
  `λ ↦ λ + (h/2)[g₊(Y_j) + g₊(Y_{j+1}) + g₋(Y_j) + g₋(Y_{j-1})]`;
* source half-step again.

This file proves that the composition is **second-order consistent**: started from the grid
sampling of a `C³` solution, one step reproduces the solution at time `τ + h` up to `C h³`
(`strangSplitting_local_error`).  The characteristic form of the PDE is used through its
directional derivatives along the characteristics,
`Π₊ (DZ·(1,-1)) = Π₊ F(Z)`, `Π₋ (DZ·(1,1)) = Π₋ F(Z)`, `Π₀ (DZ·(1,0)) = Π₀ F(Z)`,
`Dλ·(1,0) = g₊(Z) + g₋(Z)`, on the slab `τ ∈ [t₀, t₁]`.

The analytic inputs are elementary:

* one-dimensional Taylor/midpoint bounds along lines with *local* derivative bounds
  (`norm_line_midpoint_le`, `norm_line_symm_le`, `norm_line_taylor_one_le`,
  `norm_line_sub_le`);
* a bounded, Lipschitz source field with bounded second differences on a convex chart
  containing a fixed tube around the reference solution;
* the stage-wise residual/stability estimates of the implicit midpoint rule
  (`implicitMidpoint_increment_le`, `implicitMidpoint_explicit_error_le`,
  `implicitMidpoint_stability`).

The near-identity branch of the implicit-midpoint relation is selected by requiring the
stage increments to be at most the tube radius `δ`; on it the stages exist
(`implicitMidpoint_exists`, Banach fixed point; `StrangSetup.stage_one_exists`,
`StrangSetup.transportCombine_near`, `StrangSetup.stage_three_exists`).
-/

open Set
open scoped BigOperators

namespace RenewalGeometry.CharacteristicSplitting

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### One-dimensional bounds with local derivative control -/

section OneDim

theorem hasDerivAt_iteratedDeriv_of_contDiff {φ : ℝ → V} {n : ℕ} (hφ : ContDiff ℝ n φ)
    (k : ℕ) (hk : k < n) (s : ℝ) :
    HasDerivAt (iteratedDeriv k φ) (iteratedDeriv (k + 1) φ s) s := by
  rw [iteratedDeriv_succ]
  exact ((hφ.differentiable_iteratedDeriv k (by exact_mod_cast hk)) s).hasDerivAt

/-- Midpoint rule with a local third-derivative bound:
`‖φ(h) - φ(0) - h φ'(h/2)‖ ≤ M h³/24`. -/
theorem norm_midpoint_le (φ : ℝ → V) (hφ : ContDiff ℝ 3 φ) {h M : ℝ} (hh : 0 ≤ h)
    (hM : ∀ s ∈ Icc 0 h, ‖iteratedDeriv 3 φ s‖ ≤ M) :
    ‖φ h - φ 0 - h • iteratedDeriv 1 φ (h / 2)‖ ≤ M * h ^ 3 / 24 := by
  have h1 : ∀ s, HasDerivAt φ (iteratedDeriv 1 φ s) s := by
    intro s
    have := hasDerivAt_iteratedDeriv_of_contDiff hφ 0 (by norm_num) s
    simpa using this
  have h2 := hasDerivAt_iteratedDeriv_of_contDiff hφ 1 (by norm_num)
  have h3 := hasDerivAt_iteratedDeriv_of_contDiff hφ 2 (by norm_num)
  have := GowdyStaggered.midpoint_rule_bound φ (iteratedDeriv 1 φ) (iteratedDeriv 2 φ)
    (iteratedDeriv 3 φ) 0 h M hh h1 h2 h3 hM
  simpa using this

/-- Symmetric second difference with a local second-derivative bound:
`‖φ(0) + φ(h) - 2 φ(h/2)‖ ≤ M h²/4`. -/
theorem norm_symm_le (φ : ℝ → V) (hφ : ContDiff ℝ 2 φ) {h M : ℝ} (hh : 0 ≤ h)
    (hM : ∀ s ∈ Icc 0 h, ‖iteratedDeriv 2 φ s‖ ≤ M) :
    ‖φ 0 + φ h - (2 : ℝ) • φ (h / 2)‖ ≤ M * h ^ 2 / 4 := by
  have h1 : ∀ s, HasDerivAt φ (iteratedDeriv 1 φ s) s := by
    intro s
    have := hasDerivAt_iteratedDeriv_of_contDiff hφ 0 (by norm_num) s
    simpa using this
  have h2 := hasDerivAt_iteratedDeriv_of_contDiff hφ 1 (by norm_num)
  have := GowdyStaggered.symmetric_difference_bound φ (iteratedDeriv 1 φ) (iteratedDeriv 2 φ)
    0 h M h1 h2 hM (h / 2) ⟨by linarith, by linarith⟩
  have e1 : (0 + h) / 2 + h / 2 = h := by ring
  have e2 : (0 + h) / 2 - h / 2 = 0 := by ring
  have e3 : (0 + h) / 2 = h / 2 := by ring
  rw [e1, e2, e3] at this
  calc ‖φ 0 + φ h - (2 : ℝ) • φ (h / 2)‖ = ‖φ h + φ 0 - (2 : ℝ) • φ (h / 2)‖ := by
        rw [add_comm (φ 0)]
    _ ≤ M * (h / 2) ^ 2 := this
    _ = M * h ^ 2 / 4 := by ring

/-- First-order Taylor bound with a local second-derivative bound:
`‖φ(h) - φ(0) - h φ'(0)‖ ≤ M h²/2`. -/
theorem norm_taylor_one_le (φ : ℝ → V) (hφ : ContDiff ℝ 2 φ) {h M : ℝ} (hh : 0 ≤ h)
    (hM : ∀ s ∈ Icc 0 h, ‖iteratedDeriv 2 φ s‖ ≤ M) :
    ‖φ h - φ 0 - h • iteratedDeriv 1 φ 0‖ ≤ M * h ^ 2 / 2 := by
  have h1 : ∀ s, HasDerivAt φ (iteratedDeriv 1 φ s) s := by
    intro s
    have := hasDerivAt_iteratedDeriv_of_contDiff hφ 0 (by norm_num) s
    simpa using this
  have h2 := hasDerivAt_iteratedDeriv_of_contDiff hφ 1 (by norm_num)
  set χ : ℝ → V := fun s => φ s - φ 0 - s • iteratedDeriv 1 φ 0 with hχ
  set χ' : ℝ → V := fun s => iteratedDeriv 1 φ s - iteratedDeriv 1 φ 0 with hχ'
  have hχd : ∀ s, HasDerivAt χ (χ' s) s := by
    intro s
    have hl : HasDerivAt (fun s : ℝ => s • iteratedDeriv 1 φ 0) (iteratedDeriv 1 φ 0) s := by
      simpa using (hasDerivAt_id s).smul_const (iteratedDeriv 1 φ 0)
    exact ((h1 s).sub (hasDerivAt_const s (φ 0))).sub hl |>.congr_deriv (by simp [hχ'])
  have hbound : ∀ s ∈ Ico 0 h, ‖χ' s‖ ≤ M * s := by
    intro s hs
    have := (convex_Icc 0 h).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := iteratedDeriv 1 φ) (f' := iteratedDeriv 2 φ)
      (fun x _ => (h2 x).hasDerivWithinAt) hM (left_mem_Icc.mpr hh) (Ico_subset_Icc_self hs)
    simpa [hχ', Real.norm_eq_abs, abs_of_nonneg hs.1] using this
  have hB : ∀ s : ℝ, HasDerivAt (fun s => M * s ^ 2 / 2) (M * s) s := by
    intro s
    have := ((hasDerivAt_pow 2 s).const_mul M).div_const 2
    refine this.congr_deriv ?_
    push_cast; ring
  have hχ0 : ‖χ 0‖ ≤ M * (0 : ℝ) ^ 2 / 2 := by simp [hχ]
  have hfence := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := χ) (f' := χ') (a := 0) (b := h)
    (fun s _ => (hχd s).continuousAt.continuousWithinAt)
    (fun s _ => (hχd s).hasDerivWithinAt) hχ0 hB hbound
  simpa [hχ] using hfence (right_mem_Icc.mpr hh)

/-- Mean-value bound with a local first-derivative bound: `‖φ(h) - φ(0)‖ ≤ M h`. -/
theorem norm_sub_le_of_deriv (φ : ℝ → V) (hφ : ContDiff ℝ 1 φ) {h M : ℝ} (hh : 0 ≤ h)
    (hM : ∀ s ∈ Icc 0 h, ‖iteratedDeriv 1 φ s‖ ≤ M) :
    ‖φ h - φ 0‖ ≤ M * h := by
  have h1 : ∀ s, HasDerivAt φ (iteratedDeriv 1 φ s) s := by
    intro s
    have := hasDerivAt_iteratedDeriv_of_contDiff hφ 0 (by norm_num) s
    simpa using this
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := φ) (a := 0) (b := h)
    (fun x _ => (h1 x).hasDerivWithinAt) (fun x hx => hM x (Ico_subset_Icc_self hx)) h
    (right_mem_Icc.mpr hh)
  simpa using this

end OneDim

/-! ### The same bounds along lines in the `(τ, θ)` plane -/

section Lines

open RenewalGeometry.VectorLineTaylor

variable {Z : ℝ × ℝ → V}

theorem iteratedDeriv_one_line (hZ : ContDiff ℝ 3 Z) (p v : ℝ × ℝ) (s : ℝ) :
    iteratedDeriv 1 (fun s : ℝ => Z (p + s • v)) s = fderiv ℝ Z (p + s • v) v := by
  have := iteratedDeriv_lineMap (n := 3) hZ p v (k := 1) (by norm_num) s
  rw [iteratedFDeriv_one_apply] at this
  exact this

theorem norm_iteratedDeriv_line_le (hZ : ContDiff ℝ 3 Z) {p v : ℝ × ℝ} (hv : ‖v‖ ≤ 1)
    {k : ℕ} (hk : k ≤ 3) (s : ℝ) :
    ‖iteratedDeriv k (fun s : ℝ => Z (p + s • v)) s‖ ≤ ‖iteratedFDeriv ℝ k Z (p + s • v)‖ := by
  have := norm_iteratedDeriv_lineMap_le (n := 3) hZ p v hk s
  calc ‖iteratedDeriv k (fun s : ℝ => Z (p + s • v)) s‖
      ≤ ‖iteratedFDeriv ℝ k Z (p + s • v)‖ * ‖v‖ ^ k := this
    _ ≤ ‖iteratedFDeriv ℝ k Z (p + s • v)‖ * 1 := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) hv
    _ = _ := mul_one _

theorem contDiff_line (hZ : ContDiff ℝ 3 Z) (p v : ℝ × ℝ) :
    ContDiff ℝ 3 (fun s : ℝ => Z (p + s • v)) :=
  contDiff_lineMap hZ p v

/-- Midpoint rule along a line. -/
theorem norm_line_midpoint_le (hZ : ContDiff ℝ 3 Z) {p v : ℝ × ℝ} (hv : ‖v‖ ≤ 1)
    {h D : ℝ} (hh : 0 ≤ h) (hD : ∀ s ∈ Icc 0 h, ‖iteratedFDeriv ℝ 3 Z (p + s • v)‖ ≤ D) :
    ‖Z (p + h • v) - Z p - h • fderiv ℝ Z (p + (h / 2) • v) v‖ ≤ D * h ^ 3 / 24 := by
  have := norm_midpoint_le _ (contDiff_line hZ p v) hh
    (fun s hs => (norm_iteratedDeriv_line_le hZ hv (by norm_num) s).trans (hD s hs))
  simpa [iteratedDeriv_one_line hZ] using this

/-- Symmetric second difference along a line. -/
theorem norm_line_symm_le (hZ : ContDiff ℝ 3 Z) {p v : ℝ × ℝ} (hv : ‖v‖ ≤ 1)
    {h D : ℝ} (hh : 0 ≤ h) (hD : ∀ s ∈ Icc 0 h, ‖iteratedFDeriv ℝ 2 Z (p + s • v)‖ ≤ D) :
    ‖Z p + Z (p + h • v) - (2 : ℝ) • Z (p + (h / 2) • v)‖ ≤ D * h ^ 2 / 4 := by
  have := norm_symm_le _ ((contDiff_line hZ p v).of_le (by norm_num)) hh
    (fun s hs => (norm_iteratedDeriv_line_le hZ hv (by norm_num) s).trans (hD s hs))
  simpa using this

/-- First-order Taylor bound along a line. -/
theorem norm_line_taylor_one_le (hZ : ContDiff ℝ 3 Z) {p v : ℝ × ℝ} (hv : ‖v‖ ≤ 1)
    {h D : ℝ} (hh : 0 ≤ h) (hD : ∀ s ∈ Icc 0 h, ‖iteratedFDeriv ℝ 2 Z (p + s • v)‖ ≤ D) :
    ‖Z (p + h • v) - Z p - h • fderiv ℝ Z p v‖ ≤ D * h ^ 2 / 2 := by
  have := norm_taylor_one_le _ ((contDiff_line hZ p v).of_le (by norm_num)) hh
    (fun s hs => (norm_iteratedDeriv_line_le hZ hv (by norm_num) s).trans (hD s hs))
  simpa [iteratedDeriv_one_line hZ] using this

/-- Mean-value bound along a line. -/
theorem norm_line_sub_le (hZ : ContDiff ℝ 3 Z) {p v : ℝ × ℝ} (hv : ‖v‖ ≤ 1)
    {h D : ℝ} (hh : 0 ≤ h) (hD : ∀ s ∈ Icc 0 h, ‖iteratedFDeriv ℝ 1 Z (p + s • v)‖ ≤ D) :
    ‖Z (p + h • v) - Z p‖ ≤ D * h := by
  have := norm_sub_le_of_deriv _ ((contDiff_line hZ p v).of_le (by norm_num)) hh
    (fun s hs => (norm_iteratedDeriv_line_le hZ hv (by norm_num) s).trans (hD s hs))
  simpa using this

end Lines

/-! ### Stage estimates for the implicit midpoint rule -/

section Stages

variable {F : V → V} {K : Set V} {B L : ℝ}

/-- The increment of an implicit-midpoint step is at most `σ B`. -/
theorem implicitMidpoint_increment_le {σ : ℝ} (hσ : 0 ≤ σ) {X Y : V}
    (hY : Y = X + σ • F ((1 / 2 : ℝ) • (X + Y))) (hB : ‖F ((1 / 2 : ℝ) • (X + Y))‖ ≤ B) :
    ‖Y - X‖ ≤ σ * B := by
  have : Y - X = σ • F ((1 / 2 : ℝ) • (X + Y)) := sub_eq_iff_eq_add'.mpr hY
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
  exact mul_le_mul_of_nonneg_left hB hσ

theorem midpoint_sub_left (X Y : V) : (1 / 2 : ℝ) • (X + Y) - X = (1 / 2 : ℝ) • (Y - X) := by
  module

theorem norm_midpoint_sub_left (X Y : V) :
    ‖(1 / 2 : ℝ) • (X + Y) - X‖ = ‖Y - X‖ / 2 := by
  rw [midpoint_sub_left, norm_smul]
  norm_num
  ring

/-- Explicit first-order form of an implicit-midpoint step:
`‖Y - X - σ F(X)‖ ≤ σ² L B / 2`. -/
theorem implicitMidpoint_explicit_error_le {σ : ℝ} (hσ : 0 ≤ σ) {X Y : V}
    (hY : Y = X + σ • F ((1 / 2 : ℝ) • (X + Y))) (hX : X ∈ K)
    (hm : (1 / 2 : ℝ) • (X + Y) ∈ K) (hB : ∀ x ∈ K, ‖F x‖ ≤ B)
    (hL : ∀ x ∈ K, ∀ y ∈ K, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL0 : 0 ≤ L) :
    ‖Y - X - σ • F X‖ ≤ σ ^ 2 * L * B / 2 := by
  have hinc := implicitMidpoint_increment_le hσ hY (hB _ hm)
  have hmX : ‖(1 / 2 : ℝ) • (X + Y) - X‖ ≤ σ * B / 2 := by
    rw [norm_midpoint_sub_left]; linarith
  have e : Y - X - σ • F X = σ • (F ((1 / 2 : ℝ) • (X + Y)) - F X) := by
    rw [smul_sub]
    conv_lhs => rw [hY]
    abel
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
  calc σ * ‖F ((1 / 2 : ℝ) • (X + Y)) - F X‖ ≤ σ * (L * (σ * B / 2)) := by
        gcongr
        exact (hL _ hm _ hX).trans (mul_le_mul_of_nonneg_left hmX hL0)
    _ = σ ^ 2 * L * B / 2 := by ring

/-- Second-order explicit form of an implicit-midpoint step:
`‖Y - X - σ F(X + (σ/2) F X)‖ ≤ σ³ L² B / 4`. -/
theorem implicitMidpoint_second_error_le {σ : ℝ} (hσ : 0 ≤ σ) {X Y : V}
    (hY : Y = X + σ • F ((1 / 2 : ℝ) • (X + Y))) (hX : X ∈ K)
    (hm : (1 / 2 : ℝ) • (X + Y) ∈ K) (hq : X + (σ / 2) • F X ∈ K)
    (hB : ∀ x ∈ K, ‖F x‖ ≤ B)
    (hL : ∀ x ∈ K, ∀ y ∈ K, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL0 : 0 ≤ L) :
    ‖Y - X - σ • F (X + (σ / 2) • F X)‖ ≤ σ ^ 3 * L ^ 2 * B / 4 := by
  set m := (1 / 2 : ℝ) • (X + Y) with hmdef
  have hinc := implicitMidpoint_increment_le hσ hY (hB _ hm)
  have hmX : ‖m - X‖ ≤ σ * B / 2 := by
    rw [hmdef, norm_midpoint_sub_left]; linarith
  have hmq : m - (X + (σ / 2) • F X) = (σ / 2) • (F m - F X) := by
    have : m = X + (σ / 2) • F m := by
      rw [hmdef]
      conv_lhs => rw [hY]
      module
    rw [smul_sub]
    conv_lhs => rw [this]
    abel
  have hmq' : ‖m - (X + (σ / 2) • F X)‖ ≤ σ ^ 2 * L * B / 4 := by
    rw [hmq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    calc σ / 2 * ‖F m - F X‖ ≤ σ / 2 * (L * (σ * B / 2)) := by
          gcongr
          exact (hL _ hm _ hX).trans (mul_le_mul_of_nonneg_left hmX hL0)
      _ = σ ^ 2 * L * B / 4 := by ring
  have e : Y - X - σ • F (X + (σ / 2) • F X) = σ • (F m - F (X + (σ / 2) • F X)) := by
    rw [smul_sub]
    conv_lhs => rw [hY]
    abel
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
  calc σ * ‖F m - F (X + (σ / 2) • F X)‖ ≤ σ * (L * (σ ^ 2 * L * B / 4)) := by
        gcongr
        exact (hL _ hm _ hq).trans (mul_le_mul_of_nonneg_left hmq' hL0)
    _ = σ ^ 3 * L ^ 2 * B / 4 := by ring

/-- Stability of the final implicit-midpoint stage: if the target `W` satisfies the stage
relation from `Y₂` with the frozen midpoint `r = W - (σ/2) F W` up to a residual `ρ`, then the
actual stage output `Y₃` is within `3‖ρ‖ + σ³ L² B / 2` of `W` (for `σ L ≤ 1`). -/
theorem implicitMidpoint_stability {σ : ℝ} (hσ : 0 ≤ σ) {Y₂ Y₃ W : V}
    (hY : Y₃ = Y₂ + σ • F ((1 / 2 : ℝ) • (Y₂ + Y₃))) (hW : W ∈ K)
    (hm : (1 / 2 : ℝ) • (Y₂ + Y₃) ∈ K) (hr : W - (σ / 2) • F W ∈ K)
    (hB : ∀ x ∈ K, ‖F x‖ ≤ B)
    (hL : ∀ x ∈ K, ∀ y ∈ K, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL0 : 0 ≤ L) (hσL : σ * L ≤ 1) :
    ‖Y₃ - W‖ ≤ 3 * ‖W - Y₂ - σ • F (W - (σ / 2) • F W)‖ + σ ^ 3 * L ^ 2 * B / 2 := by
  set r := W - (σ / 2) • F W with hrdef
  set ρ := W - Y₂ - σ • F r with hρdef
  set m := (1 / 2 : ℝ) • (Y₂ + Y₃) with hmdef
  set e := Y₃ - W with hedef
  have he : e = σ • (F m - F r) - ρ := by
    rw [hedef, hρdef, smul_sub]
    conv_lhs => rw [hY]
    abel
  have hmr : m - r = (1 / 2 : ℝ) • e + (σ / 2) • (F W - F r) - (1 / 2 : ℝ) • ρ := by
    rw [hmdef, hrdef, hedef, hρdef]
    module
  have hWr : ‖W - r‖ ≤ σ * B / 2 := by
    rw [hrdef, sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have := hB _ hW
    nlinarith
  have hFWr : ‖F W - F r‖ ≤ L * (σ * B / 2) :=
    (hL _ hW _ hr).trans (mul_le_mul_of_nonneg_left hWr hL0)
  have hmr' : ‖m - r‖ ≤ ‖e‖ / 2 + σ / 2 * (L * (σ * B / 2)) + ‖ρ‖ / 2 := by
    rw [hmr]
    calc ‖(1 / 2 : ℝ) • e + (σ / 2) • (F W - F r) - (1 / 2 : ℝ) • ρ‖
        ≤ ‖(1 / 2 : ℝ) • e‖ + ‖(σ / 2) • (F W - F r)‖ + ‖(1 / 2 : ℝ) • ρ‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ ‖e‖ / 2 + σ / 2 * (L * (σ * B / 2)) + ‖ρ‖ / 2 := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ / 2)]
          norm_num
          gcongr
          · linarith
          · linarith
  have hFmr : ‖F m - F r‖ ≤ L * ‖m - r‖ := hL _ hm _ hr
  have he' : ‖e‖ ≤ σ * (L * ‖m - r‖) + ‖ρ‖ := by
    rw [he]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
    gcongr
  have hσLmr : σ * (L * ‖m - r‖) ≤
      σ * L * (‖e‖ / 2 + σ / 2 * (L * (σ * B / 2)) + ‖ρ‖ / 2) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left hmr' (mul_nonneg hσ hL0)
  have hρ0 := norm_nonneg ρ
  have he0 := norm_nonneg e
  have hσL0 : 0 ≤ σ * L := mul_nonneg hσ hL0
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB _ hW)
  -- `‖e‖ ≤ σL‖e‖/2 + σ³L²B/4 + σL‖ρ‖/2 + ‖ρ‖`
  have key : ‖e‖ * (1 - σ * L / 2) ≤ σ ^ 3 * L ^ 2 * B / 4 + ‖ρ‖ * (1 + σ * L / 2) := by
    nlinarith
  have h12 : (1 : ℝ) / 2 ≤ 1 - σ * L / 2 := by linarith
  have : ‖e‖ / 2 ≤ σ ^ 3 * L ^ 2 * B / 4 + ‖ρ‖ * (3 / 2) := by
    have h1 : ‖e‖ / 2 ≤ ‖e‖ * (1 - σ * L / 2) := by nlinarith
    have h2 : ‖ρ‖ * (1 + σ * L / 2) ≤ ‖ρ‖ * (3 / 2) := by
      apply mul_le_mul_of_nonneg_left _ hρ0; linarith
    linarith
  linarith

end Stages

/-! ### The characteristic system and its reference solution -/

/-- Data of a semilinear characteristic system `∂_τ Z = (Π₊ - Π₋)∂_θ Z + F(Z)`,
`∂_τ λ = g₊(Z) + g₋(Z)`, together with a `C³` reference solution `(Z, λ)` on the slab
`τ ∈ [t₀, t₁]` (in characteristic form) and a convex chart `K` containing the tube of
radius `δ` around the reference values, on which the source field is bounded, Lipschitz,
and has bounded second differences, and the quadratic densities `g±` are Lipschitz with
respect to their own characteristic part. -/
structure StrangSetup (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- reference state -/
  Z : ℝ × ℝ → V
  /-- reference background -/
  lam : ℝ × ℝ → ℝ
  /-- source field -/
  F : V → V
  /-- right-moving density -/
  gp : V → ℝ
  /-- left-moving density -/
  gm : V → ℝ
  /-- right-moving projection -/
  Pp : V →ₗ[ℝ] V
  /-- left-moving projection -/
  Pm : V →ₗ[ℝ] V
  /-- non-moving projection -/
  P0 : V →ₗ[ℝ] V
  /-- the chart -/
  K : Set V
  t₀ : ℝ
  t₁ : ℝ
  δ : ℝ
  B : ℝ
  L : ℝ
  M : ℝ
  Lg : ℝ
  Mg : ℝ
  D : ℝ
  proj_sum : ∀ v, Pp v + Pm v + P0 v = v
  norm_Pp : ∀ v, ‖Pp v‖ ≤ ‖v‖
  norm_Pm : ∀ v, ‖Pm v‖ ≤ ‖v‖
  norm_P0 : ∀ v, ‖P0 v‖ ≤ ‖v‖
  Z_smooth : ContDiff ℝ 3 Z
  lam_smooth : ContDiff ℝ 3 lam
  Z_bound1 : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → ‖iteratedFDeriv ℝ 1 Z p‖ ≤ D
  Z_bound2 : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → ‖iteratedFDeriv ℝ 2 Z p‖ ≤ D
  Z_bound3 : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → ‖iteratedFDeriv ℝ 3 Z p‖ ≤ D
  lam_bound3 : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → ‖iteratedFDeriv ℝ 3 lam p‖ ≤ D
  char_plus : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → Pp (fderiv ℝ Z p (1, -1)) = Pp (F (Z p))
  char_minus : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → Pm (fderiv ℝ Z p (1, 1)) = Pm (F (Z p))
  char_zero : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → P0 (fderiv ℝ Z p (1, 0)) = P0 (F (Z p))
  char_lam : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → fderiv ℝ lam p (1, 0) = gp (Z p) + gm (Z p)
  δ_pos : 0 < δ
  tube : ∀ p : ℝ × ℝ, p.1 ∈ Icc t₀ t₁ → ∀ v, ‖v - Z p‖ ≤ δ → v ∈ K
  convex : Convex ℝ K
  F_bound : ∀ x ∈ K, ‖F x‖ ≤ B
  F_lip : ∀ x ∈ K, ∀ y ∈ K, ‖F x - F y‖ ≤ L * ‖x - y‖
  F_symm : ∀ x ∈ K, ∀ y ∈ K,
    ‖F x + F y - (2 : ℝ) • F ((1 / 2 : ℝ) • (x + y))‖ ≤ M * ‖x - y‖ ^ 2
  gp_lip : ∀ x ∈ K, ∀ y ∈ K, |gp x - gp y| ≤ Lg * ‖Pp (x - y)‖
  gm_lip : ∀ x ∈ K, ∀ y ∈ K, |gm x - gm y| ≤ Lg * ‖Pm (x - y)‖
  gp_symm : ∀ x ∈ K, ∀ y ∈ K,
    |gp x + gp y - 2 * gp ((1 / 2 : ℝ) • (x + y))| ≤ Mg * ‖x - y‖ ^ 2
  gm_symm : ∀ x ∈ K, ∀ y ∈ K,
    |gm x + gm y - 2 * gm ((1 / 2 : ℝ) • (x + y))| ≤ Mg * ‖x - y‖ ^ 2
  B_nonneg : 0 ≤ B
  L_nonneg : 0 ≤ L
  M_nonneg : 0 ≤ M
  Lg_nonneg : 0 ≤ Lg
  Mg_nonneg : 0 ≤ Mg
  D_nonneg : 0 ≤ D

namespace StrangSetup

variable (S : StrangSetup V)

theorem mem_K_of_slab {p : ℝ × ℝ} (hp : p.1 ∈ Icc S.t₀ S.t₁) : S.Z p ∈ S.K :=
  S.tube p hp _ (by simpa using S.δ_pos.le)

theorem mem_K_add_smul {p : ℝ × ℝ} (hp : p.1 ∈ Icc S.t₀ S.t₁) {c : ℝ}
    (hc : |c| * S.B ≤ S.δ) : S.Z p + c • S.F (S.Z p) ∈ S.K := by
  apply S.tube p hp
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (S.F_bound _ (S.mem_K_of_slab hp)) (abs_nonneg c)).trans hc

theorem mem_K_midpoint {x y : V} (hx : x ∈ S.K) (hy : y ∈ S.K) :
    (1 / 2 : ℝ) • (x + y) ∈ S.K := by
  have := S.convex hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simpa [smul_add] using this

/-- A segment `s ↦ p + s • v`, `s ∈ [0, h]`, lies in the slab. -/
def SegInSlab (p v : ℝ × ℝ) (h : ℝ) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) h, (p + s • v).1 ∈ Icc S.t₀ S.t₁

/-- Second-order residual of one characteristic component of the final stage: along a
characteristic segment `p₀ → p₀ + h v` on which `Π (DZ·v) = Π F(Z)`,
`Π(Z(p₀+hv) - Z(p₀) - (h/2)(F(q) + F(r))) = O(h³)` with `q = Z(p₀) + (h/4) F(Z(p₀))` and
`r = Z(p₀+hv) - (h/4) F(Z(p₀+hv))`. -/
theorem char_component_residual (Pr : V →ₗ[ℝ] V) (hPr : ∀ x, ‖Pr x‖ ≤ ‖x‖)
    {p v : ℝ × ℝ} (hv : ‖v‖ ≤ 1) {h : ℝ} (hh : 0 ≤ h) (hseg : S.SegInSlab p v h)
    (hchar : Pr (fderiv ℝ S.Z (p + (h / 2) • v) v) = Pr (S.F (S.Z (p + (h / 2) • v))))
    (hq : S.Z p + (h / 4) • S.F (S.Z p) ∈ S.K)
    (hr : S.Z (p + h • v) - (h / 4) • S.F (S.Z (p + h • v)) ∈ S.K) :
    ‖Pr (S.Z (p + h • v) - S.Z p - (h / 2) • (S.F (S.Z p + (h / 4) • S.F (S.Z p)) +
        S.F (S.Z (p + h • v) - (h / 4) • S.F (S.Z (p + h • v)))))‖ ≤
      (S.D / 24 + S.M * (S.D + S.B / 2) ^ 2 / 2 + S.L * S.D * (1 + S.L) / 8) * h ^ 3 := by
  set X := S.Z p with hXdef
  set W := S.Z (p + h • v) with hWdef
  set Zh := S.Z (p + (h / 2) • v) with hZhdef
  set q := X + (h / 4) • S.F X with hqdef
  set r := W - (h / 4) • S.F W with hrdef
  have hp0 : p.1 ∈ Icc S.t₀ S.t₁ := by simpa using hseg 0 (left_mem_Icc.mpr hh)
  have hph : (p + h • v).1 ∈ Icc S.t₀ S.t₁ := hseg h (right_mem_Icc.mpr hh)
  have hpm : (p + (h / 2) • v).1 ∈ Icc S.t₀ S.t₁ := hseg (h / 2) ⟨by linarith, by linarith⟩
  have hXK : X ∈ S.K := S.mem_K_of_slab hp0
  have hWK : W ∈ S.K := S.mem_K_of_slab hph
  have hZhK : Zh ∈ S.K := S.mem_K_of_slab hpm
  have hcK : (1 / 2 : ℝ) • (q + r) ∈ S.K := S.mem_K_midpoint hq hr
  -- Taylor inputs
  have hmid := norm_line_midpoint_le S.Z_smooth hv hh (fun s hs => S.Z_bound3 _ (hseg s hs))
  have hsym := norm_line_symm_le S.Z_smooth hv hh (fun s hs => S.Z_bound2 _ (hseg s hs))
  have hlip := norm_line_sub_le S.Z_smooth hv hh (fun s hs => S.Z_bound1 _ (hseg s hs))
  -- the decomposition
  set Zd := fderiv ℝ S.Z (p + (h / 2) • v) v with hZddef
  have hdec : W - X - (h / 2) • (S.F q + S.F r) =
      (W - X - h • Zd) + h • (Zd - S.F Zh) +
        (h / 2) • ((2 : ℝ) • S.F Zh - (S.F q + S.F r)) := by
    module
  have hPr2 : Pr (h • (Zd - S.F Zh)) = 0 := by
    rw [map_smul, map_sub, hchar, sub_self, smul_zero]
  -- bound on `2F(Zh) - F q - F r`
  have hcZ : ‖(1 / 2 : ℝ) • (q + r) - Zh‖ ≤ S.D * h ^ 2 / 8 + S.L * S.D * h ^ 2 / 8 := by
    have e : (1 / 2 : ℝ) • (q + r) - Zh =
        (1 / 2 : ℝ) • (X + W - (2 : ℝ) • Zh) + (h / 8) • (S.F X - S.F W) := by
      rw [hqdef, hrdef]
      module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_nonneg (by linarith : 0 ≤ h / 8)]
    have h1 : ‖S.F X - S.F W‖ ≤ S.L * (S.D * h) := by
      refine (S.F_lip _ hXK _ hWK).trans (mul_le_mul_of_nonneg_left ?_ S.L_nonneg)
      rw [norm_sub_rev]; exact hlip
    have h2 : 1 / 2 * ‖X + W - (2 : ℝ) • Zh‖ ≤ 1 / 2 * (S.D * h ^ 2 / 4) := by
      gcongr
    have h3 : h / 8 * ‖S.F X - S.F W‖ ≤ h / 8 * (S.L * (S.D * h)) := by
      gcongr
    nlinarith
  have hqr : ‖q - r‖ ≤ (S.D + S.B / 2) * h := by
    have e : q - r = (X - W) + (h / 4) • (S.F X + S.F W) := by
      rw [hqdef, hrdef]; module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ h / 4)]
    have h1 : ‖X - W‖ ≤ S.D * h := by rw [norm_sub_rev]; exact hlip
    have h2 : ‖S.F X + S.F W‖ ≤ 2 * S.B :=
      (norm_add_le _ _).trans (by linarith [S.F_bound _ hXK, S.F_bound _ hWK])
    have h3 : h / 4 * ‖S.F X + S.F W‖ ≤ h / 4 * (2 * S.B) := by gcongr
    nlinarith
  have hthird : ‖(2 : ℝ) • S.F Zh - (S.F q + S.F r)‖ ≤
      (S.M * (S.D + S.B / 2) ^ 2 + S.L * S.D * (1 + S.L) / 4) * h ^ 2 := by
    have e : (2 : ℝ) • S.F Zh - (S.F q + S.F r) =
        (2 : ℝ) • (S.F Zh - S.F ((1 / 2 : ℝ) • (q + r))) -
          (S.F q + S.F r - (2 : ℝ) • S.F ((1 / 2 : ℝ) • (q + r))) := by
      module
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h1 : ‖S.F Zh - S.F ((1 / 2 : ℝ) • (q + r))‖ ≤
        S.L * (S.D * h ^ 2 / 8 + S.L * S.D * h ^ 2 / 8) := by
      refine (S.F_lip _ hZhK _ hcK).trans (mul_le_mul_of_nonneg_left ?_ S.L_nonneg)
      rw [norm_sub_rev]; exact hcZ
    have h2 := S.F_symm _ hq _ hr
    have h3 : S.M * ‖q - r‖ ^ 2 ≤ S.M * ((S.D + S.B / 2) * h) ^ 2 := by
      have := S.M_nonneg
      gcongr
    have h4 := S.L_nonneg
    nlinarith
  rw [hdec, map_add, map_add, hPr2, add_zero]
  refine (norm_add_le _ _).trans ?_
  have hA : ‖Pr (W - X - h • Zd)‖ ≤ S.D * h ^ 3 / 24 := (hPr _).trans hmid
  have hC : ‖Pr ((h / 2) • ((2 : ℝ) • S.F Zh - (S.F q + S.F r)))‖ ≤
      h / 2 * ((S.M * (S.D + S.B / 2) ^ 2 + S.L * S.D * (1 + S.L) / 4) * h ^ 2) := by
    refine (hPr _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ h / 2)]
    gcongr
  calc ‖Pr (W - X - h • Zd)‖ + ‖Pr ((h / 2) • ((2 : ℝ) • S.F Zh - (S.F q + S.F r)))‖
      ≤ S.D * h ^ 3 / 24 +
          h / 2 * ((S.M * (S.D + S.B / 2) ^ 2 + S.L * S.D * (1 + S.L) / 4) * h ^ 2) :=
        add_le_add hA hC
    _ = (S.D / 24 + S.M * (S.D + S.B / 2) ^ 2 / 2 + S.L * S.D * (1 + S.L) / 8) * h ^ 3 := by
        ring

end StrangSetup

namespace StrangSetup

variable (S : StrangSetup V)

theorem segInSlab_of {p v : ℝ × ℝ} {h : ℝ} (hh : 0 ≤ h) (hv0 : 0 ≤ v.1) (hv1 : v.1 ≤ 1)
    (hp : S.t₀ ≤ p.1) (hph : p.1 + h ≤ S.t₁) : S.SegInSlab p v h := by
  intro s hs
  obtain ⟨hs0, hsh⟩ := hs
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
  constructor
  · nlinarith
  · nlinarith

theorem segInSlab_shift {p v : ℝ × ℝ} {h a : ℝ} (ha : 0 ≤ a) (_hah : a ≤ h)
    (hseg : S.SegInSlab p v h) : S.SegInSlab (p + a • v) v (h - a) := by
  intro s hs
  have : p + a • v + s • v = p + (a + s) • v := by rw [add_assoc, ← add_smul]
  rw [this]
  exact hseg _ ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem segInSlab_mono {p v : ℝ × ℝ} {h h' : ℝ} (hh' : h' ≤ h)
    (hseg : S.SegInSlab p v h) : S.SegInSlab p v h' :=
  fun s hs => hseg s ⟨hs.1, hs.2.trans hh'⟩

/-- Second-order pairing of a characteristic density at two neighbouring sites after a
source half-step: with `Y_a, Y_b` within `ε` of `Z + (h/2) F(Z)` at `p_a`, `p_b = p_a + h u`,
`|g(Y_a) + g(Y_b) - 2 g(Z(p_t))| ≤ 2 L_g ε + O(h²)` where `p_t = p_c + (h/2) w` is reached
from the spatial midpoint `p_c` along the characteristic `w` of `g`. -/
theorem density_pair (Pr : V →ₗ[ℝ] V) (hPr : ∀ x, ‖Pr x‖ ≤ ‖x‖) (g : V → ℝ)
    (hg_lip : ∀ x ∈ S.K, ∀ y ∈ S.K, |g x - g y| ≤ S.Lg * ‖Pr (x - y)‖)
    (hg_symm : ∀ x ∈ S.K, ∀ y ∈ S.K,
      |g x + g y - 2 * g ((1 / 2 : ℝ) • (x + y))| ≤ S.Mg * ‖x - y‖ ^ 2)
    {pa u w : ℝ × ℝ} (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) {h ε : ℝ} (hh : 0 ≤ h)
    (hsegu : S.SegInSlab pa u h) (hsegw : S.SegInSlab (pa + (h / 2) • u) w (h / 2))
    (hchar : Pr (fderiv ℝ S.Z (pa + (h / 2) • u) w) = Pr (S.F (S.Z (pa + (h / 2) • u))))
    {Ya Yb : V} (hYaK : Ya ∈ S.K) (hYbK : Yb ∈ S.K)
    (hsa : S.Z pa + (h / 2) • S.F (S.Z pa) ∈ S.K)
    (hsb : S.Z (pa + h • u) + (h / 2) • S.F (S.Z (pa + h • u)) ∈ S.K)
    (hsc : S.Z (pa + (h / 2) • u) + (h / 2) • S.F (S.Z (pa + (h / 2) • u)) ∈ S.K)
    (hYa : ‖Ya - (S.Z pa + (h / 2) • S.F (S.Z pa))‖ ≤ ε)
    (hYb : ‖Yb - (S.Z (pa + h • u) + (h / 2) • S.F (S.Z (pa + h • u)))‖ ≤ ε) :
    |g Ya + g Yb - 2 * g (S.Z (pa + (h / 2) • u + (h / 2) • w))| ≤
      2 * S.Lg * ε + (S.Mg * (S.D + S.B) ^ 2 + 2 * S.Lg * (S.D / 8 + S.L * S.D / 4) +
        S.Lg * S.D / 4) * h ^ 2 := by
  set pb := pa + h • u with hpb
  set pc := pa + (h / 2) • u with hpc
  set pt := pc + (h / 2) • w with hpt
  set Za := S.Z pa
  set Zb := S.Z pb
  set Zc := S.Z pc
  set Zt := S.Z pt
  set sa := Za + (h / 2) • S.F Za with hsadef
  set sb := Zb + (h / 2) • S.F Zb with hsbdef
  set sc := Zc + (h / 2) • S.F Zc with hscdef
  have hh2 : 0 ≤ h / 2 := by linarith
  have hpa : pa.1 ∈ Icc S.t₀ S.t₁ := by simpa using hsegu 0 (left_mem_Icc.mpr hh)
  have hpbm : pb.1 ∈ Icc S.t₀ S.t₁ := hsegu h (right_mem_Icc.mpr hh)
  have hpcm : pc.1 ∈ Icc S.t₀ S.t₁ := hsegu (h / 2) ⟨hh2, by linarith⟩
  have hptm : pt.1 ∈ Icc S.t₀ S.t₁ := hsegw (h / 2) ⟨hh2, le_rfl⟩
  have hZaK := S.mem_K_of_slab hpa
  have hZbK := S.mem_K_of_slab hpbm
  have hZcK := S.mem_K_of_slab hpcm
  have hZtK := S.mem_K_of_slab hptm
  -- line estimates
  have hsym : ‖Za + Zb - (2 : ℝ) • Zc‖ ≤ S.D * h ^ 2 / 4 :=
    norm_line_symm_le S.Z_smooth hu hh (fun s hs => S.Z_bound2 _ (hsegu s hs))
  have hac : ‖Zc - Za‖ ≤ S.D * (h / 2) :=
    norm_line_sub_le S.Z_smooth hu hh2
      (fun s hs => S.Z_bound1 _ (hsegu s ⟨hs.1, by linarith [hs.2]⟩))
  have hcb : ‖Zb - Zc‖ ≤ S.D * (h / 2) := by
    have hseg' := S.segInSlab_shift hh2 (by linarith) hsegu
    have e : h - h / 2 = h / 2 := by ring
    rw [e] at hseg'
    have := norm_line_sub_le S.Z_smooth hu hh2 (fun s hs => S.Z_bound1 _ (hseg' s hs))
    have e2 : pc + (h / 2) • u = pb := by rw [hpc, hpb, add_assoc, ← add_smul]; ring_nf
    rw [e2] at this
    exact this
  have hab : ‖Zb - Za‖ ≤ S.D * h :=
    norm_line_sub_le S.Z_smooth hu hh (fun s hs => S.Z_bound1 _ (hsegu s hs))
  have htay : ‖Zt - Zc - (h / 2) • fderiv ℝ S.Z pc w‖ ≤ S.D * (h / 2) ^ 2 / 2 :=
    norm_line_taylor_one_le S.Z_smooth hw hh2 (fun s hs => S.Z_bound2 _ (hsegw s hs))
  -- the five pieces
  have hFa := S.F_bound _ hZaK
  have hFb := S.F_bound _ hZbK
  have hL0 := S.L_nonneg
  have hLg0 := S.Lg_nonneg
  have hD0 := S.D_nonneg
  have h1 : |g Ya - g sa| ≤ S.Lg * ε :=
    (hg_lip _ hYaK _ hsa).trans (mul_le_mul_of_nonneg_left ((hPr _).trans hYa) hLg0)
  have h2 : |g Yb - g sb| ≤ S.Lg * ε :=
    (hg_lip _ hYbK _ hsb).trans (mul_le_mul_of_nonneg_left ((hPr _).trans hYb) hLg0)
  have hsab : ‖sa - sb‖ ≤ (S.D + S.B) * h := by
    have e : sa - sb = (Za - Zb) + (h / 2) • (S.F Za - S.F Zb) := by
      rw [hsadef, hsbdef]; module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh2, norm_sub_rev]
    have : ‖S.F Za - S.F Zb‖ ≤ 2 * S.B := (norm_sub_le _ _).trans (by linarith)
    have : h / 2 * ‖S.F Za - S.F Zb‖ ≤ h / 2 * (2 * S.B) := by gcongr
    nlinarith
  have h3 : |g sa + g sb - 2 * g ((1 / 2 : ℝ) • (sa + sb))| ≤
      S.Mg * ((S.D + S.B) * h) ^ 2 := by
    refine (hg_symm _ hsa _ hsb).trans ?_
    have := S.Mg_nonneg
    gcongr
  have hmidK : (1 / 2 : ℝ) • (sa + sb) ∈ S.K := S.mem_K_midpoint hsa hsb
  have hcs : ‖(1 / 2 : ℝ) • (sa + sb) - sc‖ ≤ S.D * h ^ 2 / 8 + S.L * S.D * h ^ 2 / 4 := by
    have e : (1 / 2 : ℝ) • (sa + sb) - sc = (1 / 2 : ℝ) • (Za + Zb - (2 : ℝ) • Zc) +
        (h / 4) • ((S.F Za - S.F Zc) + (S.F Zb - S.F Zc)) := by
      rw [hsadef, hsbdef, hscdef]; module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_nonneg (by linarith : 0 ≤ h / 4)]
    have ha : ‖S.F Za - S.F Zc‖ ≤ S.L * (S.D * (h / 2)) := by
      refine (S.F_lip _ hZaK _ hZcK).trans (mul_le_mul_of_nonneg_left ?_ hL0)
      rw [norm_sub_rev]; exact hac
    have hb : ‖S.F Zb - S.F Zc‖ ≤ S.L * (S.D * (h / 2)) :=
      (S.F_lip _ hZbK _ hZcK).trans (mul_le_mul_of_nonneg_left hcb hL0)
    have hab' : ‖(S.F Za - S.F Zc) + (S.F Zb - S.F Zc)‖ ≤ 2 * (S.L * (S.D * (h / 2))) :=
      (norm_add_le _ _).trans (by linarith)
    have hx : 1 / 2 * ‖Za + Zb - (2 : ℝ) • Zc‖ ≤ 1 / 2 * (S.D * h ^ 2 / 4) := by gcongr
    have hy : h / 4 * ‖(S.F Za - S.F Zc) + (S.F Zb - S.F Zc)‖ ≤
        h / 4 * (2 * (S.L * (S.D * (h / 2)))) := by gcongr
    nlinarith
  have h4 : |g ((1 / 2 : ℝ) • (sa + sb)) - g sc| ≤
      S.Lg * (S.D * h ^ 2 / 8 + S.L * S.D * h ^ 2 / 4) :=
    (hg_lip _ hmidK _ hsc).trans (mul_le_mul_of_nonneg_left ((hPr _).trans hcs) hLg0)
  have hPrsc : Pr (sc - Zt) = -Pr (Zt - Zc - (h / 2) • fderiv ℝ S.Z pc w) := by
    have e : sc - Zt = -(Zt - Zc - (h / 2) • fderiv ℝ S.Z pc w) +
        (h / 2) • (S.F Zc - fderiv ℝ S.Z pc w) := by
      rw [hscdef]; module
    rw [e, map_add, map_smul, map_sub, hchar, sub_self, smul_zero, add_zero, map_neg]
  have h5 : |g sc - g Zt| ≤ S.Lg * (S.D * (h / 2) ^ 2 / 2) := by
    refine (hg_lip _ hsc _ hZtK).trans (mul_le_mul_of_nonneg_left ?_ hLg0)
    rw [hPrsc, norm_neg]
    exact (hPr _).trans htay
  have e : g Ya + g Yb - 2 * g Zt = (g Ya - g sa) + (g Yb - g sb) +
      (g sa + g sb - 2 * g ((1 / 2 : ℝ) • (sa + sb))) +
      2 * (g ((1 / 2 : ℝ) • (sa + sb)) - g sc) + 2 * (g sc - g Zt) := by ring
  rw [e]
  calc |(g Ya - g sa) + (g Yb - g sb) + (g sa + g sb - 2 * g ((1 / 2 : ℝ) • (sa + sb))) +
        2 * (g ((1 / 2 : ℝ) • (sa + sb)) - g sc) + 2 * (g sc - g Zt)|
      ≤ |g Ya - g sa| + |g Yb - g sb| + |g sa + g sb - 2 * g ((1 / 2 : ℝ) • (sa + sb))| +
          2 * |g ((1 / 2 : ℝ) • (sa + sb)) - g sc| + 2 * |g sc - g Zt| := by
        have := abs_add_le ((g Ya - g sa) + (g Yb - g sb) +
          (g sa + g sb - 2 * g ((1 / 2 : ℝ) • (sa + sb))) +
          2 * (g ((1 / 2 : ℝ) • (sa + sb)) - g sc)) (2 * (g sc - g Zt))
        have := abs_add_le ((g Ya - g sa) + (g Yb - g sb) +
          (g sa + g sb - 2 * g ((1 / 2 : ℝ) • (sa + sb))))
          (2 * (g ((1 / 2 : ℝ) • (sa + sb)) - g sc))
        have := abs_add_le ((g Ya - g sa) + (g Yb - g sb))
          (g sa + g sb - 2 * g ((1 / 2 : ℝ) • (sa + sb)))
        have := abs_add_le (g Ya - g sa) (g Yb - g sb)
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at *
        linarith
    _ ≤ S.Lg * ε + S.Lg * ε + S.Mg * ((S.D + S.B) * h) ^ 2 +
          2 * (S.Lg * (S.D * h ^ 2 / 8 + S.L * S.D * h ^ 2 / 4)) +
          2 * (S.Lg * (S.D * (h / 2) ^ 2 / 2)) := by linarith
    _ = 2 * S.Lg * ε + (S.Mg * (S.D + S.B) ^ 2 + 2 * S.Lg * (S.D / 8 + S.L * S.D / 4) +
          S.Lg * S.D / 4) * h ^ 2 := by ring

end StrangSetup

namespace StrangSetup

variable (S : StrangSetup V)

/-- The symmetric split step at one site `θ`, from three stage-one outputs. -/
def transportCombine (Y1m Y10 Y1p : V) : V := S.Pp Y1p + S.Pm Y1m + S.P0 Y10

/-- The coefficient of `h³` in the state part of the local error. -/
def stateConst : ℝ :=
  9 * (S.D / 24 + S.M * (S.D + S.B / 2) ^ 2 / 2 + S.L * S.D * (1 + S.L) / 8) +
    9 * (S.L ^ 2 * S.B / 32) + S.L ^ 2 * S.B / 16

/-- The coefficient of `h³` in the background part of the local error. -/
def lamConst : ℝ :=
  S.D / 24 + S.Lg * S.L * S.B / 4 + (S.Mg * (S.D + S.B) ^ 2 +
    2 * S.Lg * (S.D / 8 + S.L * S.D / 4) + S.Lg * S.D / 4)

/-- The step-size threshold. -/
def stepBound : ℝ := min (S.δ / (3 * S.B + 6 * S.D + 1)) (1 / (S.L + 1))

theorem stepBound_pos : 0 < S.stepBound := by
  have := S.B_nonneg; have := S.D_nonneg; have := S.L_nonneg; have := S.δ_pos
  unfold stepBound
  apply lt_min <;> positivity

set_option maxHeartbeats 1000000 in
/-- **Second-order local error of characteristic Strang splitting.**  Start from the samples
`Z(τ, θ - h), Z(τ, θ), Z(τ, θ + h)` of the reference solution; let `Y1m, Y10, Y1p` be
near-identity implicit-midpoint source half-steps (`σ = h/2`) from them, let
`Y₂ = Π₊ Y1p + Π₋ Y1m + Π₀ Y10` be the transported state at `θ`, and `Y₃` a near-identity
implicit-midpoint half-step from `Y₂`.  Then for `0 < h ≤ h₀` and `[τ, τ + h] ⊆ [t₀, t₁]`,
`‖Y₃ - Z(τ+h, θ)‖ ≤ C h³` and the background update
`λ(τ,θ) + (h/2)[g₊(Y10) + g₊(Y1p) + g₋(Y10) + g₋(Y1m)]` is within `C h³` of `λ(τ+h, θ)`. -/
theorem local_error {h τ θ : ℝ} (hh : 0 < h) (hh0 : h ≤ S.stepBound) (hτ : S.t₀ ≤ τ)
    (hτh : τ + h ≤ S.t₁) {Y1m Y10 Y1p Y3 : V}
    (h1m : Y1m = S.Z (τ, θ - h) + (h / 2) • S.F ((1 / 2 : ℝ) • (S.Z (τ, θ - h) + Y1m)))
    (h1m' : ‖Y1m - S.Z (τ, θ - h)‖ ≤ S.δ)
    (h10 : Y10 = S.Z (τ, θ) + (h / 2) • S.F ((1 / 2 : ℝ) • (S.Z (τ, θ) + Y10)))
    (h10' : ‖Y10 - S.Z (τ, θ)‖ ≤ S.δ)
    (h1p : Y1p = S.Z (τ, θ + h) + (h / 2) • S.F ((1 / 2 : ℝ) • (S.Z (τ, θ + h) + Y1p)))
    (h1p' : ‖Y1p - S.Z (τ, θ + h)‖ ≤ S.δ)
    (h3 : Y3 = S.transportCombine Y1m Y10 Y1p +
      (h / 2) • S.F ((1 / 2 : ℝ) • (S.transportCombine Y1m Y10 Y1p + Y3)))
    (h3' : ‖Y3 - S.transportCombine Y1m Y10 Y1p‖ ≤ S.δ) :
    ‖Y3 - S.Z (τ + h, θ)‖ ≤ S.stateConst * h ^ 3 ∧
      |S.lam (τ, θ) + h / 2 * ((S.gp Y10 + S.gp Y1p) + (S.gm Y10 + S.gm Y1m)) -
        S.lam (τ + h, θ)| ≤ S.lamConst * h ^ 3 := by
  have hB0 := S.B_nonneg
  have hD0 := S.D_nonneg
  have hL0 := S.L_nonneg
  have hM0 := S.M_nonneg
  have hLg0 := S.Lg_nonneg
  have hMg0 := S.Mg_nonneg
  have hδ0 := S.δ_pos
  have hh' : 0 ≤ h := hh.le
  have hh2 : 0 ≤ h / 2 := by linarith
  -- step-size consequences
  have hden : 0 < 3 * S.B + 6 * S.D + 1 := by positivity
  have hhδ : h * (3 * S.B + 6 * S.D + 1) ≤ S.δ := by
    have : h ≤ S.δ / (3 * S.B + 6 * S.D + 1) := hh0.trans (min_le_left _ _)
    rwa [le_div_iff₀ hden] at this
  have hhL : h * S.L ≤ 1 := by
    have : h ≤ 1 / (S.L + 1) := hh0.trans (min_le_right _ _)
    rw [le_div_iff₀ (by linarith)] at this
    nlinarith
  have hsmall : ∀ c : ℝ, |c| ≤ h / 2 → |c| * S.B ≤ S.δ := by
    intro c hc
    have : |c| * S.B ≤ h / 2 * S.B := mul_le_mul_of_nonneg_right hc hB0
    nlinarith
  -- points and directions
  set pm : ℝ × ℝ := (τ, θ - h)
  set p0 : ℝ × ℝ := (τ, θ)
  set pp : ℝ × ℝ := (τ, θ + h)
  set p1 : ℝ × ℝ := (τ + h, θ)
  set vp : ℝ × ℝ := (1, -1)
  set vm : ℝ × ℝ := (1, 1)
  set v0 : ℝ × ℝ := (1, 0)
  set e : ℝ × ℝ := (0, 1)
  have hvp : ‖vp‖ ≤ 1 := by simp [vp, Prod.norm_def]
  have hvm : ‖vm‖ ≤ 1 := by simp [vm, Prod.norm_def]
  have hv0 : ‖v0‖ ≤ 1 := by simp [v0, Prod.norm_def]
  have he : ‖e‖ ≤ 1 := by simp [e, Prod.norm_def]
  have epp : pp + h • vp = p1 := by simp [pp, vp, p1]; try ring
  have epm : pm + h • vm = p1 := by simp [pm, vm, p1]; try ring
  have ep0 : p0 + h • v0 = p1 := by simp [p0, v0, p1]; try ring
  have hslab : ∀ p : ℝ × ℝ, p.1 = τ → p.1 ∈ Icc S.t₀ S.t₁ := by
    intro p hp; rw [hp]; exact ⟨hτ, by linarith⟩
  have hp1 : p1.1 ∈ Icc S.t₀ S.t₁ := ⟨by simp [p1]; linarith, by simp [p1]; linarith⟩
  have hsegp : S.SegInSlab pp vp h := S.segInSlab_of hh' (by simp [vp]) (by simp [vp])
    (by simp [pp]; exact hτ) (by simp [pp]; exact hτh)
  have hsegm : S.SegInSlab pm vm h := S.segInSlab_of hh' (by simp [vm]) (by simp [vm])
    (by simp [pm]; exact hτ) (by simp [pm]; exact hτh)
  have hseg0 : S.SegInSlab p0 v0 h := S.segInSlab_of hh' (by simp [v0]) (by simp [v0])
    (by simp [p0]; exact hτ) (by simp [p0]; exact hτh)
  have hXmK := S.mem_K_of_slab (hslab pm rfl)
  have hX0K := S.mem_K_of_slab (hslab p0 rfl)
  have hXpK := S.mem_K_of_slab (hslab pp rfl)
  have hW := S.mem_K_of_slab hp1
  -- stage one at the three sites
  have hm1 : ∀ {p : ℝ × ℝ} {Y : V}, p.1 = τ → ‖Y - S.Z p‖ ≤ S.δ →
      (1 / 2 : ℝ) • (S.Z p + Y) ∈ S.K := by
    intro p Y hp hY
    apply S.tube p (hslab p hp)
    rw [norm_midpoint_sub_left]
    linarith
  have hq : ∀ {p : ℝ × ℝ}, p.1 = τ → S.Z p + ((h / 2) / 2) • S.F (S.Z p) ∈ S.K := by
    intro p hp
    apply S.mem_K_add_smul (hslab p hp)
    apply hsmall
    rw [abs_of_nonneg (by linarith)]; linarith
  have hs : ∀ {p : ℝ × ℝ}, p.1 = τ → S.Z p + (h / 2) • S.F (S.Z p) ∈ S.K := by
    intro p hp
    apply S.mem_K_add_smul (hslab p hp)
    apply hsmall
    rw [abs_of_nonneg (by linarith)]
  have hY1K : ∀ {p : ℝ × ℝ} {Y : V}, p.1 = τ → ‖Y - S.Z p‖ ≤ S.δ → Y ∈ S.K :=
    fun hp hY => S.tube _ (hslab _ hp) _ hY
  have hfour : (h / 2) / 2 = h / 4 := by ring
  -- second-order stage-one errors `δ_k`
  have hsec : ∀ {p : ℝ × ℝ} {Y : V}, p.1 = τ → ‖Y - S.Z p‖ ≤ S.δ →
      Y = S.Z p + (h / 2) • S.F ((1 / 2 : ℝ) • (S.Z p + Y)) →
      ‖Y - S.Z p - (h / 2) • S.F (S.Z p + (h / 4) • S.F (S.Z p))‖ ≤
        S.L ^ 2 * S.B / 32 * h ^ 3 := by
    intro p Y hp hYd hY
    have := implicitMidpoint_second_error_le hh2 hY (S.mem_K_of_slab (hslab p hp))
      (hm1 hp hYd) (hq hp) S.F_bound S.F_lip hL0
    rw [hfour] at this
    calc _ ≤ (h / 2) ^ 3 * S.L ^ 2 * S.B / 4 := this
      _ = S.L ^ 2 * S.B / 32 * h ^ 3 := by ring
  have hfirst : ∀ {p : ℝ × ℝ} {Y : V}, p.1 = τ → ‖Y - S.Z p‖ ≤ S.δ →
      Y = S.Z p + (h / 2) • S.F ((1 / 2 : ℝ) • (S.Z p + Y)) →
      ‖Y - (S.Z p + (h / 2) • S.F (S.Z p))‖ ≤ S.L * S.B / 8 * h ^ 2 := by
    intro p Y hp hYd hY
    have := implicitMidpoint_explicit_error_le hh2 hY (S.mem_K_of_slab (hslab p hp))
      (hm1 hp hYd) S.F_bound S.F_lip hL0
    rw [sub_add_eq_sub_sub]
    calc _ ≤ (h / 2) ^ 2 * S.L * S.B / 2 := this
      _ = S.L * S.B / 8 * h ^ 2 := by ring
  have hinc : ∀ {p : ℝ × ℝ} {Y : V}, p.1 = τ → ‖Y - S.Z p‖ ≤ S.δ →
      Y = S.Z p + (h / 2) • S.F ((1 / 2 : ℝ) • (S.Z p + Y)) →
      ‖Y - S.Z p‖ ≤ h / 2 * S.B := by
    intro p Y hp hYd hY
    exact implicitMidpoint_increment_le hh2 hY (S.F_bound _ (hm1 hp hYd))
  -- `Y₂` is close to `Z(τ+h, θ)`
  set Y2 := S.transportCombine Y1m Y10 Y1p with hY2def
  have hlipp : ‖S.Z p1 - S.Z pp‖ ≤ S.D * h := by
    have := norm_line_sub_le S.Z_smooth hvp hh' (fun s hs => S.Z_bound1 _ (hsegp s hs))
    rwa [epp] at this
  have hlipm : ‖S.Z p1 - S.Z pm‖ ≤ S.D * h := by
    have := norm_line_sub_le S.Z_smooth hvm hh' (fun s hs => S.Z_bound1 _ (hsegm s hs))
    rwa [epm] at this
  have hlip0 : ‖S.Z p1 - S.Z p0‖ ≤ S.D * h := by
    have := norm_line_sub_le S.Z_smooth hv0 hh' (fun s hs => S.Z_bound1 _ (hseg0 s hs))
    rwa [ep0] at this
  have hY2W : ‖Y2 - S.Z p1‖ ≤ 3 * (h / 2 * S.B + S.D * h) := by
    have e : Y2 - S.Z p1 = S.Pp (Y1p - S.Z p1) + S.Pm (Y1m - S.Z p1) + S.P0 (Y10 - S.Z p1) := by
      have hs := S.proj_sum (S.Z p1)
      rw [map_sub, map_sub, map_sub]
      conv_lhs => rw [← hs]
      rw [hY2def, transportCombine]
      abel
    have bnd : ∀ {p : ℝ × ℝ} {Y : V}, ‖Y - S.Z p‖ ≤ h / 2 * S.B → ‖S.Z p1 - S.Z p‖ ≤ S.D * h →
        ‖Y - S.Z p1‖ ≤ h / 2 * S.B + S.D * h := by
      intro p Y h1 h2
      calc ‖Y - S.Z p1‖ = ‖(Y - S.Z p) - (S.Z p1 - S.Z p)‖ := by congr 1; abel
        _ ≤ ‖Y - S.Z p‖ + ‖S.Z p1 - S.Z p‖ := norm_sub_le _ _
        _ ≤ _ := add_le_add h1 h2
    rw [e]
    have a1 := (S.norm_Pp _).trans (bnd (hinc rfl h1p' h1p) hlipp)
    have a2 := (S.norm_Pm _).trans (bnd (hinc rfl h1m' h1m) hlipm)
    have a3 := (S.norm_P0 _).trans (bnd (hinc rfl h10' h10) hlip0)
    calc _ ≤ ‖S.Pp (Y1p - S.Z p1)‖ + ‖S.Pm (Y1m - S.Z p1)‖ + ‖S.P0 (Y10 - S.Z p1)‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ _ := by linarith
  have hm3K : (1 / 2 : ℝ) • (Y2 + Y3) ∈ S.K := by
    apply S.tube p1 hp1
    have e : (1 / 2 : ℝ) • (Y2 + Y3) - S.Z p1 = (Y2 - S.Z p1) + (1 / 2 : ℝ) • (Y3 - Y2) := by
      module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have : h * (3 * S.B + 6 * S.D) ≤ S.δ := by nlinarith
    nlinarith
  have hrK : S.Z p1 - ((h / 2) / 2) • S.F (S.Z p1) ∈ S.K := by
    rw [sub_eq_add_neg, ← neg_smul]
    apply S.mem_K_add_smul hp1
    apply hsmall
    rw [abs_neg, abs_of_nonneg (by linarith)]; linarith
  -- stability of the last stage
  have hstab := implicitMidpoint_stability hh2 h3 hW hm3K hrK S.F_bound S.F_lip hL0
    (by nlinarith)
  rw [hfour] at hstab
  -- the residual
  set r := S.Z p1 - (h / 4) • S.F (S.Z p1) with hrdef
  set ρ := S.Z p1 - Y2 - (h / 2) • S.F r with hρdef
  set q : ℝ × ℝ → V := fun p => S.Z p + (h / 4) • S.F (S.Z p) with hqdef
  set ρc : ℝ × ℝ → V := fun p => S.Z p1 - S.Z p - (h / 2) • (S.F (q p) + S.F r) with hρcdef
  set dl : ℝ × ℝ → V → V := fun p Y => Y - S.Z p - (h / 2) • S.F (q p) with hdldef
  have hρdec : ρ = S.Pp (ρc pp) + S.Pm (ρc pm) + S.P0 (ρc p0) -
      (S.Pp (dl pp Y1p) + S.Pm (dl pm Y1m) + S.P0 (dl p0 Y10)) := by
    have hZ := S.proj_sum (S.Z p1)
    have hF := S.proj_sum (S.F r)
    have key : ρ - (S.Pp (ρc pp) + S.Pm (ρc pm) + S.P0 (ρc p0) -
        (S.Pp (dl pp Y1p) + S.Pm (dl pm Y1m) + S.P0 (dl p0 Y10))) =
        (S.Z p1 - (S.Pp (S.Z p1) + S.Pm (S.Z p1) + S.P0 (S.Z p1))) -
          (h / 2) • (S.F r - (S.Pp (S.F r) + S.Pm (S.F r) + S.P0 (S.F r))) := by
      simp only [hρdef, hρcdef, hdldef, hY2def, transportCombine, map_sub, map_add, map_smul]
      module
    rw [hZ, hF, sub_self, sub_self, smul_zero, sub_zero, sub_eq_zero] at key
    exact key
  have hqK : ∀ {p : ℝ × ℝ}, p.1 = τ → q p ∈ S.K := by
    intro p hp; have := hq hp; rwa [hfour] at this
  have hrK' : r ∈ S.K := by rw [hrdef]; rwa [hfour] at hrK
  have hρp : ‖S.Pp (ρc pp)‖ ≤
      (S.D / 24 + S.M * (S.D + S.B / 2) ^ 2 / 2 + S.L * S.D * (1 + S.L) / 8) * h ^ 3 := by
    have := S.char_component_residual S.Pp S.norm_Pp hvp hh' hsegp
      (S.char_plus _ (hsegp (h / 2) ⟨hh2, by linarith⟩)) (hqK rfl) (by rw [epp]; exact hrK')
    rw [epp] at this
    exact this
  have hρm : ‖S.Pm (ρc pm)‖ ≤
      (S.D / 24 + S.M * (S.D + S.B / 2) ^ 2 / 2 + S.L * S.D * (1 + S.L) / 8) * h ^ 3 := by
    have := S.char_component_residual S.Pm S.norm_Pm hvm hh' hsegm
      (S.char_minus _ (hsegm (h / 2) ⟨hh2, by linarith⟩)) (hqK rfl) (by rw [epm]; exact hrK')
    rw [epm] at this
    exact this
  have hρ0 : ‖S.P0 (ρc p0)‖ ≤
      (S.D / 24 + S.M * (S.D + S.B / 2) ^ 2 / 2 + S.L * S.D * (1 + S.L) / 8) * h ^ 3 := by
    have := S.char_component_residual S.P0 S.norm_P0 hv0 hh' hseg0
      (S.char_zero _ (hseg0 (h / 2) ⟨hh2, by linarith⟩)) (hqK rfl) (by rw [ep0]; exact hrK')
    rw [ep0] at this
    exact this
  have hdp := (S.norm_Pp _).trans (hsec (p := pp) rfl h1p' h1p)
  have hdm := (S.norm_Pm _).trans (hsec (p := pm) rfl h1m' h1m)
  have hd0 := (S.norm_P0 _).trans (hsec (p := p0) rfl h10' h10)
  have hρbound : ‖ρ‖ ≤
      3 * ((S.D / 24 + S.M * (S.D + S.B / 2) ^ 2 / 2 + S.L * S.D * (1 + S.L) / 8) * h ^ 3) +
        3 * (S.L ^ 2 * S.B / 32 * h ^ 3) := by
    rw [hρdec]
    refine (norm_sub_le _ _).trans ?_
    have n1 : ‖S.Pp (ρc pp) + S.Pm (ρc pm) + S.P0 (ρc p0)‖ ≤
        ‖S.Pp (ρc pp)‖ + ‖S.Pm (ρc pm)‖ + ‖S.P0 (ρc p0)‖ :=
      (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    have n2 : ‖S.Pp (dl pp Y1p) + S.Pm (dl pm Y1m) + S.P0 (dl p0 Y10)‖ ≤
        ‖S.Pp (dl pp Y1p)‖ + ‖S.Pm (dl pm Y1m)‖ + ‖S.P0 (dl p0 Y10)‖ :=
      (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    simp only [hdldef, hqdef] at n2 ⊢
    linarith
  -- state conclusion
  refine ⟨?_, ?_⟩
  · have h1 : ‖Y3 - S.Z p1‖ ≤ 3 * ‖ρ‖ + (h / 2) ^ 3 * S.L ^ 2 * S.B / 2 := hstab
    have h2 : S.stateConst * h ^ 3 =
        3 * (3 * ((S.D / 24 + S.M * (S.D + S.B / 2) ^ 2 / 2 + S.L * S.D * (1 + S.L) / 8) *
          h ^ 3) + 3 * (S.L ^ 2 * S.B / 32 * h ^ 3)) + (h / 2) ^ 3 * S.L ^ 2 * S.B / 2 := by
      unfold stateConst; ring
    rw [h2]
    linarith
  -- background conclusion
  · have hYp := hfirst (p := pp) rfl h1p' h1p
    have hYm := hfirst (p := pm) rfl h1m' h1m
    have hY0 := hfirst (p := p0) rfl h10' h10
    have hsegE0 : S.SegInSlab p0 e h := S.segInSlab_of hh' (by simp [e]) (by simp [e])
      (by simp [p0]; exact hτ) (by simp [p0]; exact hτh)
    have hsegEm : S.SegInSlab pm e h := S.segInSlab_of hh' (by simp [e]) (by simp [e])
      (by simp [pm]; exact hτ) (by simp [pm]; exact hτh)
    have hsegWp : S.SegInSlab (p0 + (h / 2) • e) vp (h / 2) := S.segInSlab_of hh2
      (by simp [vp]) (by simp [vp]) (by simp [p0, e]; exact hτ)
      (by simp [p0, e]; linarith)
    have hsegWm : S.SegInSlab (pm + (h / 2) • e) vm (h / 2) := S.segInSlab_of hh2
      (by simp [vm]) (by simp [vm]) (by simp [pm, e]; exact hτ)
      (by simp [pm, e]; linarith)
    have e0p : p0 + h • e = pp := by simp [p0, e, pp]
    have emp : pm + h • e = p0 := by simp [pm, e, p0]
    have ept : p0 + (h / 2) • e + (h / 2) • vp = (τ + h / 2, θ) := by
      refine Prod.ext ?_ ?_ <;> simp [p0, e, vp] <;> ring
    have emt : pm + (h / 2) • e + (h / 2) • vm = (τ + h / 2, θ) := by
      refine Prod.ext ?_ ?_ <;> simp [pm, e, vm] <;> ring
    have hcp : (p0 + (h / 2) • e).1 ∈ Icc S.t₀ S.t₁ := by
      simpa using hsegWp 0 ⟨le_rfl, hh2⟩
    have hcm : (pm + (h / 2) • e).1 ∈ Icc S.t₀ S.t₁ := by
      simpa using hsegWm 0 ⟨le_rfl, hh2⟩
    have hgp := S.density_pair S.Pp S.norm_Pp S.gp S.gp_lip S.gp_symm he hvp hh' hsegE0 hsegWp
      (S.char_plus _ hcp) (Ya := Y10) (Yb := Y1p)
      (hY1K rfl h10') (hY1K rfl h1p') (hs rfl) (by rw [e0p]; exact hs rfl)
      (S.mem_K_add_smul hcp (hsmall _ (by rw [abs_of_nonneg hh2])))
      hY0 (by rw [e0p]; exact hYp)
    rw [ept] at hgp
    have hgm := S.density_pair S.Pm S.norm_Pm S.gm S.gm_lip S.gm_symm he hvm hh' hsegEm hsegWm
      (S.char_minus _ hcm) (Ya := Y1m) (Yb := Y10)
      (hY1K rfl h1m') (hY1K rfl h10') (hs rfl) (by rw [emp]; exact hs rfl)
      (S.mem_K_add_smul hcm (hsmall _ (by rw [abs_of_nonneg hh2])))
      hYm (by rw [emp]; exact hY0)
    rw [emt] at hgm
    -- midpoint rule for `λ` along `(1, 0)`
    have hlm := norm_line_midpoint_le S.lam_smooth hv0 hh'
      (fun s hs => S.lam_bound3 _ (hseg0 s hs))
    have epm0 : p0 + (h / 2) • v0 = (τ + h / 2, θ) := by simp [p0, v0]
    rw [ep0, epm0, S.char_lam _ ⟨by linarith, by linarith⟩, Real.norm_eq_abs,
      smul_eq_mul] at hlm
    set G := S.Mg * (S.D + S.B) ^ 2 + 2 * S.Lg * (S.D / 8 + S.L * S.D / 4) + S.Lg * S.D / 4
    have hG : 0 ≤ G := by positivity
    have e2 : S.lam (τ, θ) + h / 2 * ((S.gp Y10 + S.gp Y1p) + (S.gm Y10 + S.gm Y1m)) -
        S.lam (τ + h, θ) =
        -(S.lam p1 - S.lam p0 - h * (S.gp (S.Z (τ + h / 2, θ)) + S.gm (S.Z (τ + h / 2, θ)))) +
        h / 2 * (S.gp Y10 + S.gp Y1p - 2 * S.gp (S.Z (τ + h / 2, θ))) +
        h / 2 * (S.gm Y1m + S.gm Y10 - 2 * S.gm (S.Z (τ + h / 2, θ))) := by
      simp only [p0, p1]; ring
    rw [e2]
    have hA : |h / 2 * (S.gp Y10 + S.gp Y1p - 2 * S.gp (S.Z (τ + h / 2, θ)))| ≤
        h / 2 * (2 * S.Lg * (S.L * S.B / 8 * h ^ 2) + G * h ^ 2) := by
      rw [abs_mul, abs_of_nonneg hh2]; gcongr
    have hB' : |h / 2 * (S.gm Y1m + S.gm Y10 - 2 * S.gm (S.Z (τ + h / 2, θ)))| ≤
        h / 2 * (2 * S.Lg * (S.L * S.B / 8 * h ^ 2) + G * h ^ 2) := by
      rw [abs_mul, abs_of_nonneg hh2]; gcongr
    have hsum := abs_add_le (-(S.lam p1 - S.lam p0 -
        h * (S.gp (S.Z (τ + h / 2, θ)) + S.gm (S.Z (τ + h / 2, θ)))) +
        h / 2 * (S.gp Y10 + S.gp Y1p - 2 * S.gp (S.Z (τ + h / 2, θ))))
      (h / 2 * (S.gm Y1m + S.gm Y10 - 2 * S.gm (S.Z (τ + h / 2, θ))))
    have hsum2 := abs_add_le (-(S.lam p1 - S.lam p0 -
        h * (S.gp (S.Z (τ + h / 2, θ)) + S.gm (S.Z (τ + h / 2, θ)))))
      (h / 2 * (S.gp Y10 + S.gp Y1p - 2 * S.gp (S.Z (τ + h / 2, θ))))
    rw [abs_neg] at hsum2
    have hfin : S.lamConst * h ^ 3 = S.D * h ^ 3 / 24 +
        2 * (h / 2 * (2 * S.Lg * (S.L * S.B / 8 * h ^ 2) + G * h ^ 2)) := by
      unfold lamConst; ring
    rw [hfin]
    linarith

end StrangSetup

/-! ### Existence of the near-identity implicit-midpoint steps -/

/-- **Existence of the near-identity implicit-midpoint step** (Banach fixed point): if the
closed ball of radius `ρ` around `X` lies in a set where `F` is bounded by `B` and
`L`-Lipschitz, `σ B ≤ ρ` and `σ L < 2`, then `Y = X + σ F((X+Y)/2)` has a solution with
`‖Y - X‖ ≤ ρ`. -/
theorem implicitMidpoint_exists [CompleteSpace V] {F : V → V} {K : Set V} {X : V}
    {σ ρ B L : ℝ} (hσ : 0 ≤ σ) (hρ : 0 ≤ ρ) (hK : ∀ y, ‖y - X‖ ≤ ρ → y ∈ K)
    (hB : ∀ x ∈ K, ‖F x‖ ≤ B) (hL : ∀ x ∈ K, ∀ y ∈ K, ‖F x - F y‖ ≤ L * ‖x - y‖)
    (hL0 : 0 ≤ L) (hσB : σ * B ≤ ρ) (hσL : σ * L < 2) :
    ∃ Y, ‖Y - X‖ ≤ ρ ∧ Y = X + σ • F ((1 / 2 : ℝ) • (X + Y)) := by
  set T : V → V := fun Y => X + σ • F ((1 / 2 : ℝ) • (X + Y)) with hT
  set s := Metric.closedBall X ρ with hs
  have hmid : ∀ Y ∈ s, (1 / 2 : ℝ) • (X + Y) ∈ K := by
    intro Y hY
    apply hK
    rw [norm_midpoint_sub_left]
    have := mem_closedBall_iff_norm.1 hY
    linarith [norm_nonneg (Y - X)]
  have hmaps : MapsTo T s s := by
    intro Y hY
    rw [hs, mem_closedBall_iff_norm]
    simp only [hT, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
    exact (mul_le_mul_of_nonneg_left (hB _ (hmid Y hY)) hσ).trans hσB
  have hk : 0 ≤ σ * L / 2 := by positivity
  have hc : ContractingWith ⟨σ * L / 2, hk⟩ (hmaps.restrict T s s) := by
    constructor
    · exact NNReal.coe_lt_coe.1 (show ((⟨σ * L / 2, hk⟩ : NNReal) : ℝ) < ((1 : NNReal) : ℝ) by
        simp only [NNReal.coe_mk, NNReal.coe_one]; linarith)
    · apply LipschitzWith.of_dist_le_mul
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      show dist (T a) (T b) ≤ (σ * L / 2) * dist a b
      rw [dist_eq_norm, dist_eq_norm, hT]
      have e : X + σ • F ((1 / 2 : ℝ) • (X + a)) - (X + σ • F ((1 / 2 : ℝ) • (X + b))) =
          σ • (F ((1 / 2 : ℝ) • (X + a)) - F ((1 / 2 : ℝ) • (X + b))) := by
        rw [smul_sub]; abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
      have hab : (1 / 2 : ℝ) • (X + a) - (1 / 2 : ℝ) • (X + b) = (1 / 2 : ℝ) • (a - b) := by
        module
      calc σ * ‖F ((1 / 2 : ℝ) • (X + a)) - F ((1 / 2 : ℝ) • (X + b))‖
          ≤ σ * (L * ‖(1 / 2 : ℝ) • (X + a) - (1 / 2 : ℝ) • (X + b)‖) :=
            mul_le_mul_of_nonneg_left (hL _ (hmid a ha) _ (hmid b hb)) hσ
        _ = σ * L / 2 * ‖a - b‖ := by
            rw [hab, norm_smul]; norm_num; ring
  obtain ⟨Y, hYs, hfix, -⟩ := hc.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hmaps
    (Metric.mem_closedBall_self hρ) (edist_ne_top _ _)
  exact ⟨Y, mem_closedBall_iff_norm.1 hYs, hfix.symm⟩

namespace StrangSetup

variable (S : StrangSetup V)

theorem step_consequences {h : ℝ} (hh : 0 < h) (hh0 : h ≤ S.stepBound) :
    h * (3 * S.B + 6 * S.D + 1) ≤ S.δ ∧ h * S.L ≤ 1 := by
  have hB0 := S.B_nonneg; have hD0 := S.D_nonneg; have hL0 := S.L_nonneg
  have hden : 0 < 3 * S.B + 6 * S.D + 1 := by positivity
  constructor
  · have : h ≤ S.δ / (3 * S.B + 6 * S.D + 1) := hh0.trans (min_le_left _ _)
    rwa [le_div_iff₀ hden] at this
  · have : h ≤ 1 / (S.L + 1) := hh0.trans (min_le_right _ _)
    rw [le_div_iff₀ (by linarith)] at this
    nlinarith

/-- The first source half-step from a sampled reference state exists on the near-identity
branch. -/
theorem stage_one_exists [CompleteSpace V] {h : ℝ} (hh : 0 < h) (hh0 : h ≤ S.stepBound)
    {p : ℝ × ℝ} (hp : p.1 ∈ Icc S.t₀ S.t₁) :
    ∃ Y, ‖Y - S.Z p‖ ≤ S.δ ∧ Y = S.Z p + (h / 2) • S.F ((1 / 2 : ℝ) • (S.Z p + Y)) := by
  obtain ⟨h1, h2⟩ := S.step_consequences hh hh0
  have hB0 := S.B_nonneg; have hD0 := S.D_nonneg; have hL0 := S.L_nonneg
  exact implicitMidpoint_exists (by linarith) S.δ_pos.le (fun y hy => S.tube p hp y hy)
    S.F_bound S.F_lip hL0 (by nlinarith) (by nlinarith)

/-- The transported state is within `δ/2` of the reference solution at the new time. -/
theorem transportCombine_near {h τ θ : ℝ} (hh : 0 < h) (hh0 : h ≤ S.stepBound)
    (hτ : S.t₀ ≤ τ) (hτh : τ + h ≤ S.t₁) {Y1m Y10 Y1p : V}
    (h1m : Y1m = S.Z (τ, θ - h) + (h / 2) • S.F ((1 / 2 : ℝ) • (S.Z (τ, θ - h) + Y1m)))
    (h1m' : ‖Y1m - S.Z (τ, θ - h)‖ ≤ S.δ)
    (h10 : Y10 = S.Z (τ, θ) + (h / 2) • S.F ((1 / 2 : ℝ) • (S.Z (τ, θ) + Y10)))
    (h10' : ‖Y10 - S.Z (τ, θ)‖ ≤ S.δ)
    (h1p : Y1p = S.Z (τ, θ + h) + (h / 2) • S.F ((1 / 2 : ℝ) • (S.Z (τ, θ + h) + Y1p)))
    (h1p' : ‖Y1p - S.Z (τ, θ + h)‖ ≤ S.δ) :
    ‖S.transportCombine Y1m Y10 Y1p - S.Z (τ + h, θ)‖ ≤ S.δ / 2 := by
  obtain ⟨hhδ, -⟩ := S.step_consequences hh hh0
  have hB0 := S.B_nonneg; have hD0 := S.D_nonneg
  have hh' : 0 ≤ h := hh.le
  have hh2 : 0 ≤ h / 2 := by linarith
  have hslab : ∀ p : ℝ × ℝ, p.1 = τ → p.1 ∈ Icc S.t₀ S.t₁ := by
    intro p hp; rw [hp]; exact ⟨hτ, by linarith⟩
  have hinc : ∀ {p : ℝ × ℝ} {Y : V}, p.1 = τ → ‖Y - S.Z p‖ ≤ S.δ →
      Y = S.Z p + (h / 2) • S.F ((1 / 2 : ℝ) • (S.Z p + Y)) → ‖Y - S.Z p‖ ≤ h / 2 * S.B := by
    intro p Y hp hYd hY
    refine implicitMidpoint_increment_le hh2 hY (S.F_bound _ ?_)
    apply S.tube p (hslab p hp)
    rw [norm_midpoint_sub_left]
    linarith [norm_nonneg (Y - S.Z p)]
  have hline : ∀ (p v : ℝ × ℝ), p.1 = τ → v.1 = 1 → ‖v‖ ≤ 1 →
      ‖S.Z (p + h • v) - S.Z p‖ ≤ S.D * h := by
    intro p v hp hv hvn
    have hseg : S.SegInSlab p v h :=
      S.segInSlab_of hh' (by rw [hv]; norm_num) (by rw [hv]) (by rw [hp]; exact hτ)
        (by rw [hp]; exact hτh)
    exact norm_line_sub_le S.Z_smooth hvn hh' (fun s hs => S.Z_bound1 _ (hseg s hs))
  have e1 : ((τ, θ + h) : ℝ × ℝ) + h • ((1 : ℝ), (-1 : ℝ)) = (τ + h, θ) := by
    refine Prod.ext ?_ ?_ <;> simp
  have e2 : ((τ, θ - h) : ℝ × ℝ) + h • ((1 : ℝ), (1 : ℝ)) = (τ + h, θ) := by
    refine Prod.ext ?_ ?_ <;> simp
  have e3 : ((τ, θ) : ℝ × ℝ) + h • ((1 : ℝ), (0 : ℝ)) = (τ + h, θ) := by
    refine Prod.ext ?_ ?_ <;> simp
  have lp := hline (τ, θ + h) (1, -1) rfl rfl (by simp [Prod.norm_def])
  have lm := hline (τ, θ - h) (1, 1) rfl rfl (by simp [Prod.norm_def])
  have l0 := hline (τ, θ) (1, 0) rfl rfl (by simp [Prod.norm_def])
  rw [e1] at lp; rw [e2] at lm; rw [e3] at l0
  set W := S.Z (τ + h, θ)
  have bnd : ∀ {p : ℝ × ℝ} {Y : V}, ‖Y - S.Z p‖ ≤ h / 2 * S.B → ‖W - S.Z p‖ ≤ S.D * h →
      ‖Y - W‖ ≤ h / 2 * S.B + S.D * h := by
    intro p Y h1 h2
    calc ‖Y - W‖ = ‖(Y - S.Z p) - (W - S.Z p)‖ := by congr 1; abel
      _ ≤ ‖Y - S.Z p‖ + ‖W - S.Z p‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add h1 h2
  have e : S.transportCombine Y1m Y10 Y1p - W =
      S.Pp (Y1p - W) + S.Pm (Y1m - W) + S.P0 (Y10 - W) := by
    have hs := S.proj_sum W
    rw [map_sub, map_sub, map_sub]
    conv_lhs => rw [← hs]
    rw [transportCombine]
    abel
  rw [e]
  have a1 := (S.norm_Pp _).trans (bnd (hinc rfl h1p' h1p) lp)
  have a2 := (S.norm_Pm _).trans (bnd (hinc rfl h1m' h1m) lm)
  have a3 := (S.norm_P0 _).trans (bnd (hinc rfl h10' h10) l0)
  calc _ ≤ ‖S.Pp (Y1p - W)‖ + ‖S.Pm (Y1m - W)‖ + ‖S.P0 (Y10 - W)‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ 3 * (h / 2 * S.B + S.D * h) := by linarith
    _ ≤ S.δ / 2 := by nlinarith

/-- The last source half-step from a transported state within `δ/2` of the reference exists
on the near-identity branch. -/
theorem stage_three_exists [CompleteSpace V] {h τ θ : ℝ} (hh : 0 < h)
    (hh0 : h ≤ S.stepBound) (hτ : S.t₀ ≤ τ) (hτh : τ + h ≤ S.t₁) {Y₂ : V}
    (hY₂ : ‖Y₂ - S.Z (τ + h, θ)‖ ≤ S.δ / 2) :
    ∃ Y₃, ‖Y₃ - Y₂‖ ≤ S.δ / 2 ∧ Y₃ = Y₂ + (h / 2) • S.F ((1 / 2 : ℝ) • (Y₂ + Y₃)) := by
  obtain ⟨h1, h2⟩ := S.step_consequences hh hh0
  have hB0 := S.B_nonneg; have hD0 := S.D_nonneg; have hL0 := S.L_nonneg
  have hδ := S.δ_pos
  refine implicitMidpoint_exists (by linarith) (by linarith) (fun y hy => ?_) S.F_bound S.F_lip
    hL0 (by nlinarith) (by nlinarith)
  apply S.tube (τ + h, θ) ⟨by simp; linarith, by simpa using hτh⟩
  calc ‖y - S.Z (τ + h, θ)‖ = ‖(y - Y₂) + (Y₂ - S.Z (τ + h, θ))‖ := by congr 1; abel
    _ ≤ ‖y - Y₂‖ + ‖Y₂ - S.Z (τ + h, θ)‖ := norm_add_le _ _
    _ ≤ S.δ := by linarith

end StrangSetup

end

end RenewalGeometry.CharacteristicSplitting
