/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.SobolevReaderCriterionExact

/-!
# Sharpness of the Sobolev-to-weighted-tail exponent and the `q > k + 5` threshold
  (`cor:native-reader-sobolev`, `eq:app-sharp-tail`, `eq:native-forcing-budget`;
  Einstein–Standard-Model action-closure manuscript)

This file completes `RenewalGeometry.Action.SobolevReaderCriterionExact`, which proves the
upper bound `τ_{h,j}(K;u) ≤ C_{q,j} K^{2-q} ‖u‖_{H^q}` (`tail_le_sobolev`) and the reader
criterion `eq:source-reader-Sobolev` (`sobolev_reader_criterion`).  Here:

* **Shell extremisers.**  For `K ≥ 1` the dyadic shell `𝒮_K = {ℓ ∈ ℤ⁴ : K < |ℓ|_∞ ≤ 2K}`
  has `#𝒮_K = (4K+1)⁴ - (2K+1)⁴ ≥ 175 K⁴` (`card_dyadicShell`, `card_dyadicShell_ge`).  The
  uniform-coefficient field `u = 𝟙_{𝒮_K} · v` (`shellField`) satisfies
  `τ_{h,j}(K;u) ≥ #𝒮_K ‖v‖` and `‖u‖_{H^q} ≤ √#𝒮_K (17K²)^{q/2} ‖v‖`, hence
  `c_q K^{2-q} ‖u‖_{H^q} ≤ τ_{h,j}(K;u)` with `c_q = √175 · 17^{-q/2}`, for every `j`, every
  `q ≥ 0` and every mode set `Λ ⊇ 𝒮_K` (`shellField_tail_ge`).
* **Sharpness of the exponent** (`sobolev_tail_exponent_sharp`): if some bound
  `τ_{h,j}(K;u) ≤ C K^p ‖u‖_{H^q}` holds for all `K ≥ 1` and all fields on the box
  `|ℓ|_∞ ≤ 2K`, then `p ≥ 2 - q`.  So `K^{2-q}` cannot be improved on this route.
* **The `q > k + 5` threshold.**  In the forcing budget `eq:native-forcing-budget` with
  `m = k + 2`, the measured tails enter through `ε_{c,h} K^{k+1} L^{k+1} ⊇ K^{k+3} τ_{h,2}`
  (`L_{h,k} ≥ 1`) and `K^{k+2} τ_{h,m}`.
  - `forcing_tail_le` (sufficiency): for `q > k + 5`,
    `K^{k+3} τ_{h,2}(K;u) + K^{k+2} τ_{h,k+2}(K;u) ≤ (C_{q,2} + C_{q,k+2}) K^{k+5-q} ‖u‖_{H^q}`,
    and `K^{k+5-q} → 0` (`tendsto_rpow_forcing_exponent`).
  - `forcing_tail_not_small` (necessity without extra cancellation): for `q ≤ k + 5`, the
    shell extremiser obeys `K^{k+3} τ_{h,2}(K;u_K) ≥ c_q ‖u_K‖_{H^q}` for every `K ≥ 1`, so the
    tail contribution to the forcing budget does not tend to zero relative to the `H^q`
    norm.
-/

open scoped BigOperators
open Filter

namespace RenewalGeometry
namespace SobolevReader

/-! ### The dyadic shell -/

/-- `|ℓ|₂² ≤ 4 |ℓ|_∞²` in four dimensions. -/
theorem l2sq_le_four_mul_sq_linf (ℓ : Mode) : l2sq ℓ ≤ 4 * (linf ℓ : ℝ) ^ 2 := by
  unfold l2sq
  have h : ∀ μ ∈ (Finset.univ : Finset (Fin 4)), (ℓ μ : ℝ) ^ 2 ≤ (linf ℓ : ℝ) ^ 2 := by
    intro μ _
    have hle : (ℓ μ).natAbs ≤ linf ℓ := by
      unfold linf
      exact Finset.le_sup (f := fun μ => (ℓ μ).natAbs) (Finset.mem_univ μ)
    have : |(ℓ μ : ℝ)| ≤ (linf ℓ : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      exact_mod_cast hle
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  calc ∑ μ, (ℓ μ : ℝ) ^ 2 ≤ ∑ _μ : Fin 4, (linf ℓ : ℝ) ^ 2 := Finset.sum_le_sum h
    _ = 4 * (linf ℓ : ℝ) ^ 2 := by simp

/-- The dyadic shell `𝒮_K = {ℓ ∈ ℤ⁴ : K < |ℓ|_∞ ≤ 2K}`. -/
noncomputable def dyadicShell (K : ℕ) : Finset Mode := box (2 * K) \ box K

theorem mem_dyadicShell {K : ℕ} {ℓ : Mode} : ℓ ∈ dyadicShell K ↔ K < linf ℓ ∧ linf ℓ ≤ 2 * K := by
  unfold dyadicShell
  rw [Finset.mem_sdiff, mem_box, mem_box]
  omega

/-- `#𝒮_K = (4K+1)⁴ - (2K+1)⁴`. -/
theorem card_dyadicShell (K : ℕ) :
    ((dyadicShell K).card : ℝ) = ((4 * K + 1 : ℕ) : ℝ) ^ 4 - ((2 * K + 1 : ℕ) : ℝ) ^ 4 := by
  unfold dyadicShell
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (box_mono (by omega)), card_box, card_box,
    Nat.cast_sub (Nat.pow_le_pow_left (by omega) 4)]
  push_cast
  ring

/-- **Lower shell count**: `#𝒮_K ≥ 175 K⁴` for `K ≥ 1` (complement of `card_shell_le`). -/
theorem card_dyadicShell_ge {K : ℕ} (hK : 1 ≤ K) :
    175 * (K : ℝ) ^ 4 ≤ ((dyadicShell K).card : ℝ) := by
  rw [card_dyadicShell]
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  push_cast
  nlinarith [pow_pos (by linarith : (0:ℝ) < K) 3, pow_pos (by linarith : (0:ℝ) < K) 2]

theorem card_dyadicShell_pos {K : ℕ} (hK : 1 ≤ K) : (0 : ℝ) < (dyadicShell K).card := by
  have := card_dyadicShell_ge hK
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have : (0 : ℝ) < 175 * (K : ℝ) ^ 4 := by positivity
  linarith

/-! ### The uniform-coefficient shell field -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
/-- The uniform-coefficient field on the dyadic shell: `û(ℓ) = v` for `ℓ ∈ 𝒮_K`, `0`
otherwise. -/
noncomputable def shellField (K : ℕ) (v : F) : Mode → F :=
  fun ℓ => if ℓ ∈ dyadicShell K then v else 0

omit [NormedSpace ℝ F] in
/-- The tail of the shell field is at least `#𝒮_K ‖v‖` (all weights are `≥ 1`). -/
theorem shellField_tail_ge_card (Λ : Finset Mode) (hΛ : dyadicShell K ⊆ Λ) (j : ℕ) (v : F) :
    ((dyadicShell K).card : ℝ) * ‖v‖ ≤ tail Λ j K (shellField K v) := by
  classical
  unfold tail
  have hsub : dyadicShell K ⊆ Λ.filter (fun ℓ => K < linf ℓ) := by
    intro ℓ hℓ
    rw [Finset.mem_filter]
    exact ⟨hΛ hℓ, (mem_dyadicShell.mp hℓ).1⟩
  have hnn : ∀ ℓ ∈ Λ.filter (fun ℓ => K < linf ℓ), ℓ ∉ dyadicShell K →
      0 ≤ (1 + l1 ℓ / K) ^ j * ‖shellField K v ℓ‖ := fun ℓ _ _ =>
    mul_nonneg (pow_nonneg (by have := l1_nonneg ℓ; positivity) _) (norm_nonneg _)
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn)
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro ℓ hℓ
  have hv : shellField K v ℓ = v := by simp [shellField, hℓ]
  rw [hv]
  have hw : 1 ≤ (1 + l1 ℓ / K) ^ j :=
    one_le_pow₀ (le_add_of_nonneg_right (div_nonneg (l1_nonneg ℓ) (Nat.cast_nonneg K)))
  nlinarith [norm_nonneg v]

omit [NormedSpace ℝ F] in
/-- The `H^q` norm of the shell field: `‖u‖²_{H^q} ≤ #𝒮_K (17K²)^q ‖v‖²` for `q ≥ 0`,
`K ≥ 1` and any mode set `Λ`. -/
theorem shellField_sobolevSq_le (Λ : Finset Mode) {K : ℕ} (hK : 1 ≤ K) {q : ℝ} (hq : 0 ≤ q)
    (v : F) :
    sobolevSq Λ q (shellField K v)
      ≤ ((dyadicShell K).card : ℝ) * ((17 * (K : ℝ) ^ 2) ^ q * ‖v‖ ^ 2) := by
  classical
  unfold sobolevSq
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hsplit : ∑ ℓ ∈ Λ, (1 + l2sq ℓ) ^ q * ‖shellField K v ℓ‖ ^ 2
      = ∑ ℓ ∈ Λ.filter (· ∈ dyadicShell K), (1 + l2sq ℓ) ^ q * ‖v‖ ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    by_cases h : ℓ ∈ dyadicShell K
    · simp [shellField, h]
    · simp [shellField, h]
  rw [hsplit]
  have hterm : ∀ ℓ ∈ Λ.filter (· ∈ dyadicShell K),
      (1 + l2sq ℓ) ^ q * ‖v‖ ^ 2 ≤ (17 * (K : ℝ) ^ 2) ^ q * ‖v‖ ^ 2 := by
    intro ℓ hℓ
    rw [Finset.mem_filter, mem_dyadicShell] at hℓ
    have h1 := l2sq_le_four_mul_sq_linf ℓ
    have h2 : (linf ℓ : ℝ) ≤ 2 * K := by exact_mod_cast hℓ.2.2
    have h3 : 1 + l2sq ℓ ≤ 17 * (K : ℝ) ^ 2 := by
      have : (linf ℓ : ℝ) ^ 2 ≤ (2 * K) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h2 2
      nlinarith
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by linarith [l2sq_nonneg ℓ]) h3 hq) (sq_nonneg _)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have : Λ.filter (· ∈ dyadicShell K) ⊆ dyadicShell K := fun ℓ hℓ => (Finset.mem_filter.mp hℓ).2
  exact_mod_cast Finset.card_le_card this

/-- The sharpness constant `c_q = √175 · 17^{-q/2}`. -/
noncomputable def sharpConst (q : ℝ) : ℝ := Real.sqrt 175 * (17 : ℝ) ^ (-(q / 2))

theorem sharpConst_pos (q : ℝ) : 0 < sharpConst q := by
  unfold sharpConst; positivity

/-- **Shell extremisers** (`eq:app-sharp-tail` is sharp on shell-supported examples): for
`K ≥ 1`, `q ≥ 0`, every `j` and every mode set `Λ ⊇ 𝒮_K`, the uniform-coefficient shell field
satisfies `c_q K^{2-q} ‖u‖_{H^q} ≤ τ_{h,j}(K;u)`. -/
theorem shellField_tail_ge (Λ : Finset Mode) {K : ℕ} (hK : 1 ≤ K) (hΛ : dyadicShell K ⊆ Λ)
    (j : ℕ) {q : ℝ} (hq : 0 ≤ q) (v : F) :
    sharpConst q * (K : ℝ) ^ (2 - q) * Real.sqrt (sobolevSq Λ q (shellField K v))
      ≤ tail Λ j K (shellField K v) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  set n : ℝ := ((dyadicShell K).card : ℝ) with hn
  have hnpos : 0 < n := card_dyadicShell_pos hK
  have hsob := shellField_sobolevSq_le Λ hK hq v
  -- `(17K²)^q = (17^{q/2} K^q)²`
  have hpow : (17 * (K : ℝ) ^ 2) ^ q = ((17 : ℝ) ^ (q / 2) * (K : ℝ) ^ q) ^ 2 := by
    rw [Real.mul_rpow (by norm_num) (by positivity), mul_pow]
    congr 1
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; push_cast; ring
    · rw [← Real.rpow_natCast, ← Real.rpow_mul hKpos.le, ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity)]
      congr 1; push_cast; ring
  have hsqrt : Real.sqrt (sobolevSq Λ q (shellField K v))
      ≤ Real.sqrt n * ((17 : ℝ) ^ (q / 2) * (K : ℝ) ^ q * ‖v‖) := by
    rw [show Real.sqrt n * ((17 : ℝ) ^ (q / 2) * (K : ℝ) ^ q * ‖v‖)
        = Real.sqrt (n * ((17 * (K : ℝ) ^ 2) ^ q * ‖v‖ ^ 2)) by
      rw [Real.sqrt_mul hnpos.le, hpow, ← mul_pow, Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hsob
  have hcoef : 0 ≤ sharpConst q * (K : ℝ) ^ (2 - q) :=
    mul_nonneg (sharpConst_pos q).le (by positivity)
  have hcancel : sharpConst q * (K : ℝ) ^ (2 - q) * ((17 : ℝ) ^ (q / 2) * (K : ℝ) ^ q)
      = Real.sqrt 175 * (K : ℝ) ^ 2 := by
    unfold sharpConst
    have h1 : (17 : ℝ) ^ (-(q / 2)) * (17 : ℝ) ^ (q / 2) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    have h2 : (K : ℝ) ^ (2 - q) * (K : ℝ) ^ q = (K : ℝ) ^ 2 := by
      rw [← Real.rpow_add hKpos]; simp
    calc Real.sqrt 175 * (17 : ℝ) ^ (-(q / 2)) * (K : ℝ) ^ (2 - q)
          * ((17 : ℝ) ^ (q / 2) * (K : ℝ) ^ q)
        = Real.sqrt 175 * ((17 : ℝ) ^ (-(q / 2)) * (17 : ℝ) ^ (q / 2))
          * ((K : ℝ) ^ (2 - q) * (K : ℝ) ^ q) := by ring
      _ = Real.sqrt 175 * (K : ℝ) ^ 2 := by rw [h1, h2, mul_one]
  have hcount : Real.sqrt 175 * (K : ℝ) ^ 2 ≤ Real.sqrt n := by
    rw [show (K : ℝ) ^ 2 = Real.sqrt ((K : ℝ) ^ 4) by
      rw [show (K : ℝ) ^ 4 = ((K : ℝ) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)],
      ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (card_dyadicShell_ge hK)
  calc sharpConst q * (K : ℝ) ^ (2 - q) * Real.sqrt (sobolevSq Λ q (shellField K v))
      ≤ sharpConst q * (K : ℝ) ^ (2 - q) *
          (Real.sqrt n * ((17 : ℝ) ^ (q / 2) * (K : ℝ) ^ q * ‖v‖)) :=
        mul_le_mul_of_nonneg_left hsqrt hcoef
    _ = (sharpConst q * (K : ℝ) ^ (2 - q) * ((17 : ℝ) ^ (q / 2) * (K : ℝ) ^ q))
          * Real.sqrt n * ‖v‖ := by ring
    _ = Real.sqrt 175 * (K : ℝ) ^ 2 * Real.sqrt n * ‖v‖ := by rw [hcancel]
    _ ≤ Real.sqrt n * Real.sqrt n * ‖v‖ := by
        gcongr
    _ = n * ‖v‖ := by rw [Real.mul_self_sqrt hnpos.le]
    _ ≤ tail Λ j K (shellField K v) := shellField_tail_ge_card Λ hΛ j v

/-- The shell field with `v = 1` has positive `H^q` norm. -/
theorem shellField_sobolevSq_pos (Λ : Finset Mode) {K : ℕ} (hK : 1 ≤ K)
    (hΛ : dyadicShell K ⊆ Λ) (q : ℝ) :
    0 < sobolevSq Λ q (shellField K (1 : ℝ)) := by
  classical
  obtain ⟨ℓ₀, hℓ₀⟩ : (dyadicShell K).Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast card_dyadicShell_pos hK
  unfold sobolevSq
  have hnn : ∀ ℓ ∈ Λ, 0 ≤ (1 + l2sq ℓ) ^ q * ‖shellField K (1 : ℝ) ℓ‖ ^ 2 := fun ℓ _ =>
    mul_nonneg (Real.rpow_nonneg (by linarith [l2sq_nonneg ℓ]) _) (sq_nonneg _)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hnn (hΛ hℓ₀))
  have : shellField K (1 : ℝ) ℓ₀ = 1 := by simp [shellField, hℓ₀]
  rw [this]
  simp only [norm_one, one_pow, mul_one]
  exact Real.rpow_pos_of_pos (by linarith [l2sq_nonneg ℓ₀]) _

/-- **Sharpness of `K^{2-q}`** (`cor:native-reader-sobolev`): if a Sobolev-to-weighted-tail
bound `τ_{h,j}(K;u) ≤ C K^p ‖u‖_{H^q}` holds for every `K ≥ 1` and every (real) field on the
box `|ℓ|_∞ ≤ 2K`, then `p ≥ 2 - q`.  Hence the exponent of `tail_le_sobolev` is optimal on the
four-dimensional Sobolev-to-weighted-tail route. -/
theorem sobolev_tail_exponent_sharp (j : ℕ) {q : ℝ} (hq : 0 ≤ q) (C p : ℝ)
    (hbound : ∀ K : ℕ, 1 ≤ K → ∀ u : Mode → ℝ,
      tail (box (2 * K)) j K u ≤ C * (K : ℝ) ^ p * Real.sqrt (sobolevSq (box (2 * K)) q u)) :
    2 - q ≤ p := by
  by_contra hlt
  rw [not_le] at hlt
  set e := 2 - q - p with he
  have he0 : 0 < e := by rw [he]; linarith
  -- for every `K ≥ 1`, `c_q K^{e} ≤ C`
  have hK : ∀ K : ℕ, 1 ≤ K → sharpConst q * (K : ℝ) ^ e ≤ C := by
    intro K hK1
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
    have hΛ : dyadicShell K ⊆ box (2 * K) := Finset.sdiff_subset
    have hlow := shellField_tail_ge (box (2 * K)) hK1 hΛ j hq (1 : ℝ)
    have hup := hbound K hK1 (shellField K (1 : ℝ))
    have hs : 0 < Real.sqrt (sobolevSq (box (2 * K)) q (shellField K (1 : ℝ))) :=
      Real.sqrt_pos.mpr (shellField_sobolevSq_pos _ hK1 hΛ q)
    have h1 : sharpConst q * (K : ℝ) ^ (2 - q) ≤ C * (K : ℝ) ^ p :=
      le_of_mul_le_mul_right (hlow.trans hup) hs
    have hKp : 0 < (K : ℝ) ^ p := Real.rpow_pos_of_pos hKpos p
    have h2 : (K : ℝ) ^ (2 - q) = (K : ℝ) ^ e * (K : ℝ) ^ p := by
      rw [← Real.rpow_add hKpos, he]; congr 1; ring
    rw [h2, ← mul_assoc] at h1
    exact le_of_mul_le_mul_right h1 hKp
  -- but `K^{e} → ∞`
  have htend : Tendsto (fun K : ℕ => sharpConst q * (K : ℝ) ^ e) atTop atTop :=
    ((tendsto_rpow_atTop he0).comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (sharpConst_pos q)
  obtain ⟨K, hKge⟩ := (htend.eventually (eventually_gt_atTop C)).and
    (eventually_ge_atTop 1) |>.exists
  exact absurd (hK K hKge.2) (not_le.mpr hKge.1)

/-! ### The `q > k + 5` threshold in the forcing budget -/

/-- **Sufficiency of `q > k + 5`.**  With `m = k + 2`, the tail contributions of
`eq:native-forcing-budget` (`K^{k+1} · K² τ_{h,2}` inside `ε_{c,h} K^{k+1}` and
`K^{k+2} τ_{h,m}`) are bounded by `(C_{q,2} + C_{q,k+2}) K^{k+5-q} ‖u‖_{H^q}`. -/
theorem forcing_tail_le (Λ : Finset Mode) (k K N : ℕ) {q : ℝ} (hq : (k : ℝ) + 5 < q)
    (hK : 1 ≤ K) (hKN : K ≤ N) (hΛ : ∀ ℓ ∈ Λ, linf ℓ ≤ N) (u : Mode → F) :
    (K : ℝ) ^ (k + 3) * tail Λ 2 K u + (K : ℝ) ^ (k + 2) * tail Λ (k + 2) K u
      ≤ (Real.sqrt (80 * 25 ^ 2 / (2 * q - 2 * 2 - 4))
          + Real.sqrt (80 * 25 ^ (k + 2) / (2 * q - 2 * (k + 2 : ℕ) - 4)))
          * (K : ℝ) ^ ((k : ℝ) + 5 - q) * Real.sqrt (sobolevSq Λ q u) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2 := tail_le_sobolev Λ 2 K N q (by push_cast; linarith) hK hKN hΛ u
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num] at h2
  have hm := tail_le_sobolev Λ (k + 2) K N q (by push_cast; linarith) hK hKN hΛ u
  set S := Real.sqrt (sobolevSq Λ q u)
  set A := Real.sqrt (80 * 25 ^ 2 / (2 * q - 2 * 2 - 4))
  set B := Real.sqrt (80 * 25 ^ (k + 2) / (2 * q - 2 * (k + 2 : ℕ) - 4))
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have e1 : (K : ℝ) ^ (k + 3) * (K : ℝ) ^ (2 - q) = (K : ℝ) ^ ((k : ℝ) + 5 - q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hKpos]; congr 1; push_cast; ring
  have e2 : (K : ℝ) ^ (k + 2) * (K : ℝ) ^ (2 - q) ≤ (K : ℝ) ^ ((k : ℝ) + 5 - q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hKpos]
    exact Real.rpow_le_rpow_of_exponent_le hK1 (by push_cast; linarith)
  have hpow3 : 0 ≤ (K : ℝ) ^ (k + 3) := by positivity
  have hpow2 : 0 ≤ (K : ℝ) ^ (k + 2) := by positivity
  calc (K : ℝ) ^ (k + 3) * tail Λ 2 K u + (K : ℝ) ^ (k + 2) * tail Λ (k + 2) K u
      ≤ (K : ℝ) ^ (k + 3) * (A * (K : ℝ) ^ (2 - q) * S)
          + (K : ℝ) ^ (k + 2) * (B * (K : ℝ) ^ (2 - q) * S) := by
        gcongr
    _ = A * ((K : ℝ) ^ (k + 3) * (K : ℝ) ^ (2 - q)) * S
          + B * ((K : ℝ) ^ (k + 2) * (K : ℝ) ^ (2 - q)) * S := by ring
    _ ≤ A * (K : ℝ) ^ ((k : ℝ) + 5 - q) * S + B * (K : ℝ) ^ ((k : ℝ) + 5 - q) * S := by
        rw [e1]; gcongr
    _ = (A + B) * (K : ℝ) ^ ((k : ℝ) + 5 - q) * S := by ring

/-- For `q > k + 5` the forcing-budget tail factor `K^{k+5-q}` tends to zero as `K → ∞`. -/
theorem tendsto_rpow_forcing_exponent (k : ℕ) {q : ℝ} (hq : (k : ℝ) + 5 < q) :
    Tendsto (fun K : ℕ => (K : ℝ) ^ ((k : ℝ) + 5 - q)) atTop (nhds 0) := by
  have h := tendsto_rpow_neg_atTop (y := q - k - 5) (by linarith)
  refine (h.comp tendsto_natCast_atTop_atTop).congr fun K => ?_
  simp only [Function.comp_apply]
  congr 1; ring

/-- **Necessity of `q > k + 5` without additional cancellation.**  If `q ≤ k + 5`, then for
every `K ≥ 1` the shell extremiser `u_K` (supported in `K < |ℓ|_∞ ≤ 2K ⊆ Λ`) satisfies
`K^{k+3} τ_{h,2}(K;u_K) ≥ c_q ‖u_K‖_{H^q}`; so the tail contribution `K^{k+1} · K² τ_{h,2}` to
the forcing budget `eq:native-forcing-budget` is not small relative to `‖u‖_{H^q}`. -/
theorem forcing_tail_not_small (Λ : Finset Mode) (k : ℕ) {K : ℕ} (hK : 1 ≤ K)
    (hΛ : dyadicShell K ⊆ Λ) {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ (k : ℝ) + 5) (v : F) :
    sharpConst q * Real.sqrt (sobolevSq Λ q (shellField K v))
      ≤ (K : ℝ) ^ (k + 3) * tail Λ 2 K (shellField K v) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hlow := shellField_tail_ge Λ hK hΛ 2 hq0 v
  have hS : 0 ≤ Real.sqrt (sobolevSq Λ q (shellField K v)) := Real.sqrt_nonneg _
  have hpow : 1 ≤ (K : ℝ) ^ ((k : ℝ) + 5 - q) := Real.one_le_rpow hK1 (by linarith)
  have e1 : (K : ℝ) ^ (k + 3) * (K : ℝ) ^ (2 - q) = (K : ℝ) ^ ((k : ℝ) + 5 - q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hKpos]; congr 1; push_cast; ring
  have hc := (sharpConst_pos q).le
  calc sharpConst q * Real.sqrt (sobolevSq Λ q (shellField K v))
      ≤ (K : ℝ) ^ ((k : ℝ) + 5 - q) * (sharpConst q * Real.sqrt (sobolevSq Λ q (shellField K v))) :=
        le_mul_of_one_le_left (mul_nonneg hc hS) hpow
    _ = (K : ℝ) ^ (k + 3) * (sharpConst q * (K : ℝ) ^ (2 - q)
          * Real.sqrt (sobolevSq Λ q (shellField K v))) := by rw [← e1]; ring
    _ ≤ (K : ℝ) ^ (k + 3) * tail Λ 2 K (shellField K v) :=
        mul_le_mul_of_nonneg_left hlow (by positivity)

/-- Non-vacuity: the shell extremiser at `K = 1` on the box `|ℓ|_∞ ≤ 2` is a nonzero field
with positive `H^q` norm. -/
example : 0 < sobolevSq (box 2) 3 (shellField 1 (1 : ℝ)) :=
  shellField_sobolevSq_pos (box 2) le_rfl Finset.sdiff_subset 3

end SobolevReader
end RenewalGeometry
