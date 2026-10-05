/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.TorusSobolevTransfer
import RenewalGeometry.Analysis.TrigonometricTailBounds

/-!
# Fourier truncation `P_N` and Fourier multipliers on `H^r(𝕋³)`

Generic infrastructure (no renewal notions) for `app:generated-dynamics` of the
Einstein–Standard-Model action-closure manuscript (`thm:generated-dynamics`,
`prop:generated-initial`).  The torus is `𝕋³ = UnitAddTorus (Fin 3)`, the Sobolev norms are the
library's trigonometric norms `‖F‖²_{H^r} = trigSobSq r F = Σ_n W_r(n) |F̂(n)|²`,
`W_r(n) = Σ_{|α| ≤ r} |(2πi n)^α|²` (`TorusSobolevTransfer`), for which `H^r`, `r ≥ 2`, is an
algebra (`memH_mul`).

* `lapSym n = |2πn|² = Σᵢ (2π nᵢ)²` (the symbol of `-Δ`) and the weight recursion
  **`trigWeight_succ_le`**: `W_{r+1}(n) ≤ (1 + |2πn|²) W_r(n)` (the converse direction
  `W_r(n)(2πnᵢ)² ≤ W_{r+1}(n)` is `trigWeight_mul_sq_le`).
* `coeff_ext`: continuous functions on `𝕋³` with the same Fourier coefficients are equal.
* `fmul m F = Σ_n m(n) F̂(n) e_n` (Fourier multipliers; uniformly convergent series), with
  `mFourierCoeff_fmul` under absolute summability.
* The **Fourier truncation** `proj N F = P_N F = Σ_{|n|_∞ ≤ N} F̂(n) e_n` (a trigonometric
  polynomial): `mFourierCoeff_proj`, `memH_proj` (finite in every `H^r`), `sn_proj_le`
  (**`P_N` is a contraction on every `H^r`**), `proj_proj` (idempotent), linearity,
  `isLineDeriv_proj` (**`P_N` commutes with `∂ⱼ`**), `proj_fmul` (it commutes with every Fourier
  multiplier, in particular with `L_* = -8Δ + μ_*`), the **tail estimate**
  `sn_sub_proj_le` (`‖(I - P_N)F‖_{H^r} ≤ (2π(N+1))^{-p} ‖F‖_{H^{r+p}}`) and its paper form
  `sn_sub_proj_le_pow` (`≤ N^{-p}‖F‖_{H^{r+p}}`, `N ≥ 1`), the convergence
  `tendsto_sn_sub_proj` (`P_N F → F` in `H^r`), and the **inverse inequality**
  `sn_succ_proj_le` (`‖P_N F‖_{H^{r+1}} ≤ (1 + 12π²N²)^{1/2} ‖P_N F‖_{H^r}`).
-/

open Finset Filter Topology UnitAddTorus
open scoped BigOperators Real

namespace RenewalGeometry.TorusFourierTruncation

open TorusSobolevTransfer PeriodicGridSobolev PeriodicGridSobolev.Sampling
  PeriodicGridSobolev.Composition

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable section

/-! ### The Laplace symbol and the weight recursion -/

/-- The symbol `|2πn|² = Σᵢ (2π nᵢ)²` of `-Δ` on the unit torus. -/
def lapSym (n : Fin 3 → ℤ) : ℝ := ∑ i, (2 * π * n i) ^ 2

theorem lapSym_nonneg (n : Fin 3 → ℤ) : 0 ≤ lapSym n :=
  sum_nonneg fun _ _ => sq_nonneg _

theorem lapSym_neg (n : Fin 3 → ℤ) : lapSym (-n) = lapSym n := by
  simp [lapSym]

theorem tsymSq_add_single (α : Fin 3 → ℕ) (i : Fin 3) (n : Fin 3 → ℤ) :
    tsymSq (α + Pi.single i 1) n = tsymSq α n * (2 * π * n i) ^ 2 := by
  fin_cases i <;> simp [tsymSq, pow_add] <;> ring

/-- A coordinate in which a nonzero multi-index is positive. -/
def posIdx (β : Fin 3 → ℕ) : Fin 3 := if β 0 ≠ 0 then 0 else if β 1 ≠ 0 then 1 else 2

theorem one_le_posIdx {β : Fin 3 → ℕ} (h : deg β ≠ 0) : 1 ≤ β (posIdx β) := by
  unfold posIdx deg at *
  split_ifs with h0 h1
  · omega
  · omega
  · omega

theorem sub_single_add_single {β : Fin 3 → ℕ} {i : Fin 3} (h : 1 ≤ β i) :
    (β - Pi.single i 1) + Pi.single i 1 = β := by
  ext j
  simp only [Pi.add_apply, Pi.sub_apply]
  by_cases hj : j = i
  · subst hj; simp; omega
  · simp [hj]

theorem deg_sub_single {β : Fin 3 → ℕ} {i : Fin 3} (h : 1 ≤ β i) :
    deg (β - Pi.single i 1) + 1 = deg β := by
  fin_cases i <;> simp [deg] at h ⊢ <;> omega

/-- **Weight recursion** `W_{r+1}(n) ≤ (1 + |2πn|²) W_r(n)`. -/
theorem trigWeight_succ_le (r : ℕ) (n : Fin 3 → ℤ) :
    trigWeight (r + 1) n ≤ (1 + lapSym n) * trigWeight r n := by
  classical
  set x : Fin 3 → ℝ := fun i => (2 * π * n i) ^ 2 with hx
  unfold trigWeight
  rw [← sum_filter_add_sum_filter_not (multiIndices (r + 1)) (fun β => deg β ≤ r)]
  have h1 : (multiIndices (r + 1)).filter (fun β => deg β ≤ r) = multiIndices r := by
    ext β; simp only [mem_filter, mem_multiIndices]; omega
  rw [h1, add_mul, one_mul]
  refine add_le_add le_rfl ?_
  set D := (multiIndices (r + 1)).filter (fun β => ¬ deg β ≤ r) with hD
  have hDdeg : ∀ β ∈ D, deg β ≠ 0 := by
    intro β hβ; simp only [hD, mem_filter] at hβ; omega
  set g : (Fin 3 → ℕ) → Fin 3 × (Fin 3 → ℕ) := fun β => (posIdx β, β - Pi.single (posIdx β) 1)
  have hinj : Set.InjOn g D := by
    intro β hβ β' hβ' h
    simp only [g, Prod.mk.injEq] at h
    rw [← sub_single_add_single (one_le_posIdx (hDdeg β hβ)),
      ← sub_single_add_single (one_le_posIdx (hDdeg β' hβ')), h.2, h.1]
  have hterm : ∀ β ∈ D, tsymSq β n = x (g β).1 * tsymSq (g β).2 n := by
    intro β hβ
    have := tsymSq_add_single (β - Pi.single (posIdx β) 1) (posIdx β) n
    rw [sub_single_add_single (one_le_posIdx (hDdeg β hβ))] at this
    rw [this]; simp only [g, hx]; ring
  rw [sum_congr rfl hterm, ← sum_image (f := fun p : Fin 3 × (Fin 3 → ℕ) => x p.1 * tsymSq p.2 n)
    hinj]
  have hsub : D.image g ⊆ univ ×ˢ multiIndices r := by
    intro p hp
    obtain ⟨β, hβ, rfl⟩ := mem_image.mp hp
    refine mem_product.mpr ⟨mem_univ _, mem_multiIndices.mpr ?_⟩
    have hβ' := hβ
    simp only [hD, mem_filter, mem_multiIndices] at hβ'
    have := deg_sub_single (one_le_posIdx (hDdeg β hβ))
    simp only [g]; omega
  refine (sum_le_sum_of_subset_of_nonneg hsub fun p _ _ =>
    mul_nonneg (sq_nonneg _) (tsymSq_nonneg _ _)).trans (le_of_eq ?_)
  rw [sum_product, lapSym, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]

/-- Two steps: `W_{r+2}(n) ≤ (1 + |2πn|²)² W_r(n)`. -/
theorem trigWeight_add_two_le (r : ℕ) (n : Fin 3 → ℤ) :
    trigWeight (r + 2) n ≤ (1 + lapSym n) ^ 2 * trigWeight r n := by
  have h1 := trigWeight_succ_le (r + 1) n
  have h2 := trigWeight_succ_le r n
  have h0 : 0 ≤ 1 + lapSym n := by have := lapSym_nonneg n; linarith
  calc trigWeight (r + 2) n ≤ (1 + lapSym n) * trigWeight (r + 1) n := h1
    _ ≤ (1 + lapSym n) * ((1 + lapSym n) * trigWeight r n) :=
        mul_le_mul_of_nonneg_left h2 h0
    _ = _ := by ring

/-- `|2πn|² W_r(n) ≤ 3 W_{r+1}(n)`. -/
theorem lapSym_mul_trigWeight_le (r : ℕ) (n : Fin 3 → ℤ) :
    lapSym n * trigWeight r n ≤ 3 * trigWeight (r + 1) n := by
  rw [lapSym, sum_mul]
  calc ∑ i, (2 * π * n i) ^ 2 * trigWeight r n ≤ ∑ _i : Fin 3, trigWeight (r + 1) n :=
        sum_le_sum fun i _ => by rw [mul_comm]; exact trigWeight_mul_sq_le r n i
    _ = 3 * trigWeight (r + 1) n := by simp

/-- `|2πn|⁴ W_r(n) ≤ 9 W_{r+2}(n)` (the Laplacian costs two orders). -/
theorem lapSym_sq_mul_trigWeight_le (r : ℕ) (n : Fin 3 → ℤ) :
    lapSym n ^ 2 * trigWeight r n ≤ 9 * trigWeight (r + 2) n := by
  have h1 := lapSym_mul_trigWeight_le r n
  have h2 := lapSym_mul_trigWeight_le (r + 1) n
  have h0 := lapSym_nonneg n
  calc lapSym n ^ 2 * trigWeight r n = lapSym n * (lapSym n * trigWeight r n) := by ring
    _ ≤ lapSym n * (3 * trigWeight (r + 1) n) := mul_le_mul_of_nonneg_left h1 h0
    _ = 3 * (lapSym n * trigWeight (r + 1) n) := by ring
    _ ≤ 3 * (3 * trigWeight (r + 1 + 1) n) := by linarith
    _ = 9 * trigWeight (r + 2) n := by ring

theorem trigWeight_zero_freq (r : ℕ) : trigWeight r 0 = 1 := by
  unfold trigWeight
  rw [sum_eq_single (0 : Fin 3 → ℕ)]
  · exact tsymSq_zero 0
  · intro β _ hβ
    unfold tsymSq
    have : ∃ i, β i ≠ 0 := by
      by_contra h; push Not at h; exact hβ (funext h)
    obtain ⟨i, hi⟩ := this
    fin_cases i <;> simp_all
  · intro h; exact absurd (mem_multiIndices.mpr (by simp [deg])) h

/-- Iterated cost of a coordinate derivative: `W_r(n) ((2πnᵢ)²)^p ≤ W_{r+p}(n)`. -/
theorem trigWeight_mul_pow_le (r p : ℕ) (n : Fin 3 → ℤ) (i : Fin 3) :
    trigWeight r n * ((2 * π * n i) ^ 2) ^ p ≤ trigWeight (r + p) n := by
  induction p with
  | zero => simp
  | succ p ih =>
    calc trigWeight r n * ((2 * π * n i) ^ 2) ^ (p + 1)
        = trigWeight r n * ((2 * π * n i) ^ 2) ^ p * (2 * π * n i) ^ 2 := by ring
      _ ≤ trigWeight (r + p) n * (2 * π * n i) ^ 2 :=
          mul_le_mul_of_nonneg_right ih (sq_nonneg _)
      _ ≤ trigWeight (r + p + 1) n := trigWeight_mul_sq_le _ n i

/-! ### Coefficient uniqueness and absolutely convergent Fourier series -/

/-- **Continuous functions on `𝕋³` with the same Fourier coefficients are equal.** -/
theorem coeff_ext {F G : CT} (h : ∀ n, mFourierCoeff ⇑F n = mFourierCoeff ⇑G n) : F = G := by
  have hz : ∀ n, mFourierCoeff ⇑(F - G) n = 0 := fun n => by
    have := Sampling.mFourierCoeff_add (F - G) G n
    rw [sub_add_cancel, h n] at this
    linear_combination -this
  have hz' : mFourierCoeff ⇑(F - G) = 0 := funext hz
  ext x
  have h1 := hasSum_mFourier_series_apply_of_summable (f := F - G)
    (by rw [hz']; exact summable_zero) x
  rw [hz'] at h1
  simp only [Pi.zero_apply, zero_smul] at h1
  have h2 := h1.unique hasSum_zero
  rw [ContinuousMap.sub_apply] at h2
  exact sub_eq_zero.mp h2

theorem mFourierCoeff_sub' (F G : CT) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(F - G) n = mFourierCoeff ⇑F n - mFourierCoeff ⇑G n := by
  have := Sampling.mFourierCoeff_add (F - G) G n
  rw [sub_add_cancel] at this
  rw [this]; ring

theorem mFourierCoeff_const (c : ℂ) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(ContinuousMap.const (UnitAddTorus (Fin 3)) c) n =
      if n = 0 then c else 0 := by
  have e : ContinuousMap.const (UnitAddTorus (Fin 3)) c = c • mFourier 0 := by
    ext x; simp [mFourier_zero']
  rw [e, mFourierCoeff_smul', TorusSobolevTransfer.mFourierCoeff_mFourier, smul_eq_mul]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

/-- An `H^r` coefficient family, `r ≥ 2`, is absolutely summable. -/
theorem summable_norm_of_trigWeight {r : ℕ} (hr : 2 ≤ r) {c : (Fin 3 → ℤ) → ℂ}
    (hc : Summable fun n => trigWeight r n * ‖c n‖ ^ 2) : Summable fun n => ‖c n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((hc.add (summable_inv_trigWeight r hr)).mul_left (1 / 2))
  have hW := trigWeight_pos r n
  have e : 1 / 2 * (trigWeight r n * ‖c n‖ ^ 2 + (trigWeight r n)⁻¹) - ‖c n‖ =
      (trigWeight r n * ‖c n‖ - 1) ^ 2 / (2 * trigWeight r n) := by
    field_simp; ring
  have : 0 ≤ (trigWeight r n * ‖c n‖ - 1) ^ 2 / (2 * trigWeight r n) := by positivity
  linarith

/-- The Fourier multiplier `F ↦ Σ_n m(n) F̂(n) e_n`, a uniformly convergent series of
continuous functions when `Σ_n |m(n) F̂(n)| < ∞`. -/
def fmul (m : (Fin 3 → ℤ) → ℂ) (F : CT) : CT :=
  TorusSobolev.fourierSum fun n => m n * mFourierCoeff ⇑F n

theorem mFourierCoeff_fmul {m : (Fin 3 → ℤ) → ℂ} {F : CT}
    (h : Summable fun n => ‖m n * mFourierCoeff ⇑F n‖) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(fmul m F) n = m n * mFourierCoeff ⇑F n :=
  TorusSobolev.mFourierCoeff_fourierSum h n

/-! ### The Fourier truncation `P_N` -/

/-- The frequency box `{n ∈ ℤ³ : |nᵢ| ≤ N}`. -/
def box (N : ℕ) : Finset (Fin 3 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

theorem mem_box {N : ℕ} {n : Fin 3 → ℤ} : n ∈ box N ↔ ∀ i, |n i| ≤ N := by
  simp [box, Fintype.mem_piFinset, abs_le]

/-- **The Fourier truncation** `P_N F = Σ_{|n|_∞ ≤ N} F̂(n) e_n`. -/
def proj (N : ℕ) (F : CT) : CT := tp (box N) (mFourierCoeff ⇑F)

theorem mFourierCoeff_proj (N : ℕ) (F : CT) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(proj N F) n = if n ∈ box N then mFourierCoeff ⇑F n else 0 :=
  mFourierCoeff_tp _ _ _

/-- `P_N F` lies in every `H^r` (it is a trigonometric polynomial). -/
theorem memH_proj (r N : ℕ) (F : CT) : MemH r ⇑(proj N F) := summable_tp r _ _

theorem trigSobSq_proj (r N : ℕ) (F : CT) :
    trigSobSq r ⇑(proj N F) = ∑ n ∈ box N, trigWeight r n * ‖mFourierCoeff ⇑F n‖ ^ 2 := by
  unfold proj
  rw [trigSobSq_tp]

/-- **`P_N` is a contraction on `H^r`.** -/
theorem sn_proj_le {r : ℕ} (N : ℕ) {F : CT} (hF : MemH r ⇑F) : sn r ⇑(proj N F) ≤ sn r ⇑F := by
  unfold sn
  refine Real.sqrt_le_sqrt ?_
  rw [trigSobSq_proj]
  exact hF.sum_le_tsum _ fun n _ => mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _)

theorem proj_proj (N : ℕ) (F : CT) : proj N (proj N F) = proj N F :=
  coeff_ext fun n => by
    simp only [mFourierCoeff_proj]
    split_ifs <;> rfl

theorem proj_add (N : ℕ) (F G : CT) : proj N (F + G) = proj N F + proj N G :=
  coeff_ext fun n => by
    simp only [Sampling.mFourierCoeff_add, mFourierCoeff_proj]
    split_ifs <;> simp

theorem proj_smul (N : ℕ) (c : ℂ) (F : CT) : proj N (c • F) = c • proj N F :=
  coeff_ext fun n => by
    simp only [mFourierCoeff_smul', mFourierCoeff_proj]
    split_ifs <;> simp

theorem proj_sub (N : ℕ) (F G : CT) : proj N (F - G) = proj N F - proj N G :=
  coeff_ext fun n => by
    simp only [mFourierCoeff_sub', mFourierCoeff_proj]
    split_ifs <;> simp

theorem mFourierCoeff_sub_proj (N : ℕ) (F : CT) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(F - proj N F) n = if n ∈ box N then 0 else mFourierCoeff ⇑F n := by
  rw [mFourierCoeff_sub', mFourierCoeff_proj]
  split_ifs <;> simp

/-- Outside the box some coordinate is large. -/
theorem exists_large_of_not_mem_box {N : ℕ} {n : Fin 3 → ℤ} (hn : n ∉ box N) :
    ∃ i, ((N : ℝ) + 1) ^ 2 ≤ ((n i : ℤ) : ℝ) ^ 2 := by
  rw [mem_box] at hn
  push Not at hn
  obtain ⟨i, hi⟩ := hn
  refine ⟨i, ?_⟩
  have h1 : ((N : ℤ) + 1) ≤ |n i| := by omega
  have h2 : ((N : ℝ) + 1) ≤ |((n i : ℤ) : ℝ)| := by exact_mod_cast h1
  rw [← sq_abs ((n i : ℤ) : ℝ)]
  exact pow_le_pow_left₀ (by positivity) h2 2

/-- The weight inequality behind the tail estimate: outside the box,
`(2π(N+1))^{2p} W_r(n) ≤ W_{r+p}(n)`. -/
theorem trigWeight_le_of_not_mem_box {N : ℕ} {n : Fin 3 → ℤ} (hn : n ∉ box N) (r p : ℕ) :
    ((2 * π * (N + 1)) ^ 2) ^ p * trigWeight r n ≤ trigWeight (r + p) n := by
  obtain ⟨i, hi⟩ := exists_large_of_not_mem_box hn
  refine le_trans ?_ (trigWeight_mul_pow_le r p n i)
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ p)
    (trigWeight_nonneg _ _)
  have hπ : 0 ≤ 4 * π ^ 2 := by positivity
  calc (2 * π * (N + 1)) ^ 2 = 4 * π ^ 2 * ((N : ℝ) + 1) ^ 2 := by ring
    _ ≤ 4 * π ^ 2 * ((n i : ℤ) : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hi hπ
    _ = (2 * π * n i) ^ 2 := by ring

/-- **Tail estimate** `‖(I - P_N)F‖²_{H^r} ≤ (2π(N+1))^{-2p} ‖F‖²_{H^{r+p}}`. -/
theorem trigSobSq_sub_proj_le {r p : ℕ} (N : ℕ) {F : CT} (hF : MemH (r + p) ⇑F) :
    MemH r ⇑(F - proj N F) ∧
      trigSobSq r ⇑(F - proj N F) ≤ (((2 * π * (N + 1)) ^ 2) ^ p)⁻¹ * trigSobSq (r + p) ⇑F := by
  have hc : 0 < ((2 * π * (N + 1)) ^ 2) ^ p := by positivity
  have hpt : ∀ n, trigWeight r n * ‖mFourierCoeff ⇑(F - proj N F) n‖ ^ 2 ≤
      (((2 * π * (N + 1)) ^ 2) ^ p)⁻¹ * (trigWeight (r + p) n * ‖mFourierCoeff ⇑F n‖ ^ 2) := by
    intro n
    rw [mFourierCoeff_sub_proj]
    split_ifs with hn
    · have : 0 ≤ trigWeight (r + p) n * ‖mFourierCoeff ⇑F n‖ ^ 2 :=
        mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _)
      rw [norm_zero, zero_pow two_ne_zero, mul_zero]
      exact mul_nonneg (inv_nonneg.mpr hc.le) this
    · have hW := trigWeight_le_of_not_mem_box hn r p
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [le_inv_mul_iff₀ hc]
      exact hW
  have hs : MemH r ⇑(F - proj N F) := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _)) hpt (hF.mul_left _)
  refine ⟨hs, ?_⟩
  unfold trigSobSq
  rw [← tsum_mul_left]
  exact hs.tsum_le_tsum hpt (hF.mul_left _)

/-- **Tail estimate**, norm form: `‖(I - P_N)F‖_{H^r} ≤ (2π(N+1))^{-p} ‖F‖_{H^{r+p}}`. -/
theorem sn_sub_proj_le {r p : ℕ} (N : ℕ) {F : CT} (hF : MemH (r + p) ⇑F) :
    sn r ⇑(F - proj N F) ≤ ((2 * π * (N + 1)) ^ p)⁻¹ * sn (r + p) ⇑F := by
  obtain ⟨-, h⟩ := trigSobSq_sub_proj_le (r := r) (p := p) N hF
  unfold sn
  have hc : 0 < (2 * π * (N + 1)) ^ p := by positivity
  have e : ((2 * π * (N + 1)) ^ p)⁻¹ = Real.sqrt ((((2 * π * (N + 1)) ^ 2) ^ p)⁻¹) := by
    rw [← pow_mul, mul_comm 2 p, pow_mul, Real.sqrt_inv, Real.sqrt_sq hc.le]
  rw [e, ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt h

/-- **Tail estimate in the paper's form** `‖(I - P_N)F‖_{H^{q-p}} ≤ N^{-p} ‖F‖_{H^q}`
(`N ≥ 1`). -/
theorem sn_sub_proj_le_pow {r p : ℕ} {N : ℕ} (hN : 1 ≤ N) {F : CT} (hF : MemH (r + p) ⇑F) :
    sn r ⇑(F - proj N F) ≤ ((N : ℝ) ^ p)⁻¹ * sn (r + p) ⇑F := by
  refine (sn_sub_proj_le N hF).trans (mul_le_mul_of_nonneg_right ?_ (sn_nonneg _ _))
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ p)
  have := Real.pi_gt_three
  nlinarith

/-- **`P_N F → F` in `H^r`** for every `F ∈ H^r`. -/
theorem tendsto_sn_sub_proj {r : ℕ} {F : CT} (hF : MemH r ⇑F) :
    Tendsto (fun N => sn r ⇑(F - proj N F)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun N => trigSobSq r ⇑(F - proj N F)) atTop (𝓝 0) := by
    have key := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun N n => trigWeight r n * ‖mFourierCoeff ⇑(F - proj N F) n‖ ^ 2)
      (g := fun _ => (0 : ℝ)) (bound := fun n => trigWeight r n * ‖mFourierCoeff ⇑F n‖ ^ 2) hF
      (fun n => ?_) (Eventually.of_forall fun N n => ?_)
    · simpa [trigSobSq] using key
    · -- eventually `n ∈ box N`
      have hev : ∀ᶠ N in atTop, n ∈ box N := by
        obtain ⟨M, hM⟩ := exists_nat_ge (∑ i, |n i|).toNat
        refine eventually_atTop.mpr ⟨M, fun N hN => mem_box.mpr fun i => ?_⟩
        have h1 : |n i| ≤ ∑ j, |n j| :=
          single_le_sum (f := fun j => |n j|) (fun j _ => abs_nonneg _) (mem_univ i)
        have h2 : ∑ j, |n j| ≤ ((∑ j, |n j|).toNat : ℤ) := Int.self_le_toNat _
        have h3 : (((∑ j, |n j|).toNat : ℕ) : ℤ) ≤ N := by exact_mod_cast hM.trans hN
        omega
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with N hN
      rw [mFourierCoeff_sub_proj]; simp [hN]
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _))]
      refine mul_le_mul_of_nonneg_left ?_ (trigWeight_nonneg _ _)
      rw [mFourierCoeff_sub_proj]
      split_ifs
      · simp
      · exact le_rfl
  have := (Real.continuous_sqrt.tendsto 0).comp h2
  rw [Real.sqrt_zero] at this
  exact this

/-- On the box, `|2πn|² ≤ 12π²N²`. -/
theorem lapSym_le_of_mem_box {N : ℕ} {n : Fin 3 → ℤ} (hn : n ∈ box N) :
    lapSym n ≤ 12 * π ^ 2 * (N : ℝ) ^ 2 := by
  rw [mem_box] at hn
  have h : ∀ i, (2 * π * n i) ^ 2 ≤ 4 * π ^ 2 * (N : ℝ) ^ 2 := by
    intro i
    have h1 : |((n i : ℤ) : ℝ)| ≤ N := by exact_mod_cast hn i
    have h2 : ((n i : ℤ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith [sq_nonneg π]
  calc lapSym n ≤ ∑ _i : Fin 3, 4 * π ^ 2 * (N : ℝ) ^ 2 := sum_le_sum fun i _ => h i
    _ = 12 * π ^ 2 * (N : ℝ) ^ 2 := by simp; ring

/-- **Inverse (Bernstein) inequality on `Ran P_N`**:
`‖P_N F‖_{H^{r+1}} ≤ (1 + 12π²N²)^{1/2} ‖P_N F‖_{H^r}`. -/
theorem sn_succ_proj_le (r N : ℕ) (F : CT) :
    sn (r + 1) ⇑(proj N F) ≤ Real.sqrt (1 + 12 * π ^ 2 * (N : ℝ) ^ 2) * sn r ⇑(proj N F) := by
  unfold sn
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  rw [trigSobSq_proj, trigSobSq_proj, mul_sum]
  refine sum_le_sum fun n hn => ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  refine (trigWeight_succ_le r n).trans (mul_le_mul_of_nonneg_right ?_ (trigWeight_nonneg _ _))
  linarith [lapSym_le_of_mem_box hn]

/-- **`P_N` commutes with the coordinate derivatives**: if `F'` is the classical `∂ᵢ` of `F`, then
`P_N F'` is the classical `∂ᵢ` of `P_N F`. -/
theorem isLineDeriv_proj {i : Fin 3} {F F' : CT} (h : IsLineDeriv i ⇑F ⇑F') (N : ℕ) :
    IsLineDeriv i ⇑(proj N F) ⇑(proj N F') := by
  have e1 : proj N F = TorusSobolev.trigPoly (box N) (mFourierCoeff ⇑F) := rfl
  have e2 : proj N F' = TorusSobolev.trigPoly (box N)
      (TorusSobolev.dCoeff i (mFourierCoeff ⇑F)) := by
    have : mFourierCoeff ⇑F' = TorusSobolev.dCoeff i (mFourierCoeff ⇑F) := by
      funext n; rw [mFourierCoeff_of_isLineDeriv i F F' h n]; rfl
    rw [← this]; rfl
  rw [e1, e2]
  exact TrigTail.isLineDeriv_trigPoly (box N) (mFourierCoeff ⇑F) i

/-- `P_N` commutes with every Fourier multiplier. -/
theorem proj_fmul (N : ℕ) {m : (Fin 3 → ℤ) → ℂ} {F : CT}
    (h : Summable fun n => ‖m n * mFourierCoeff ⇑F n‖) :
    proj N (fmul m F) = fmul m (proj N F) := by
  have h2 : Summable fun n => ‖m n * mFourierCoeff ⇑(proj N F) n‖ :=
    summable_of_ne_finset_zero (s := box N) fun n hn => by
      rw [mFourierCoeff_proj]; simp [hn]
  refine coeff_ext fun n => ?_
  rw [mFourierCoeff_proj, mFourierCoeff_fmul h, mFourierCoeff_fmul h2, mFourierCoeff_proj]
  split_ifs <;> simp

end

end RenewalGeometry.TorusFourierTruncation
