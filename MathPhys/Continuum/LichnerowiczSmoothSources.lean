/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.Continuum.LichnerowiczSmoothLift
import MathPhys.Continuum.ActualJetConstraintSlice

/-!
# Smooth periodic functions are in every weighted Wiener algebra

Generic infrastructure (no renewal notions) for `prop:generated-initial`: the sources of the
conformal equation built from smooth seeds have rapidly decaying Fourier coefficients.

* `trigWeight_two_le`: `W₂(n) ≤ 27 (2π)⁴ (1 + |n|₁)⁴`;
* `one_add_ab_pow_le`: `(1 + |n|₁)^q ≤ 4^q (1 + Σᵢ |nᵢ|^q)`;
* **`wsum_of_smooth`**: the descent of a smooth `ℤ³`-periodic function `g : ℝ³ → ℂ` satisfies
  `Σ_n (1 + |n|₁)^k |ĝ(n)| < ∞` for every `k` (integration by parts,
  `GevreyFourier.norm_mFourierCoeff_mul_pow_le`, against `Σ_n W₂(n)⁻¹ < ∞`).
-/

open Finset Filter Topology UnitAddTorus
open scoped BigOperators Real ContDiff

namespace MathPhys.LichReg

open SobolevOpen (pd)
open TorusFourierTruncation TorusSobolevTransfer PeriodicGridSobolev PeriodicGridSobolev.Sampling
  LichnerowiczContraction SobolevBoxCr

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable section

theorem abs_le_ab (n : Fin 3 → ℤ) (i : Fin 3) : |(n i : ℝ)| ≤ ab n :=
  single_le_sum (f := fun j => |(n j : ℝ)|) (fun _ _ => abs_nonneg _) (mem_univ i)

theorem trigWeight_two_le (n : Fin 3 → ℤ) :
    trigWeight 2 n ≤ 27 * (2 * π) ^ 4 * (1 + ab n) ^ 4 := by
  set X : ℝ := (2 * π * (1 + ab n)) ^ 2 with hX
  have hab := ab_nonneg n
  have hX1 : 1 ≤ X := by
    rw [hX]
    have : (1 : ℝ) ≤ 2 * π * (1 + ab n) := by nlinarith [Real.pi_gt_three]
    nlinarith
  have hfac : ∀ i : Fin 3, (2 * π * (n i : ℝ)) ^ 2 ≤ X := by
    intro i
    rw [hX, ← sq_abs (2 * π * (n i : ℝ))]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    have := abs_le_ab n i
    nlinarith [Real.pi_pos]
  have hterm : ∀ α ∈ multiIndices 2, tsymSq α n ≤ X ^ 2 := by
    intro α hα
    rw [mem_multiIndices] at hα
    unfold deg at hα
    have h0 : ((2 * π * (n 0 : ℝ)) ^ 2) ^ α 0 ≤ X ^ α 0 :=
      pow_le_pow_left₀ (sq_nonneg _) (hfac 0) _
    have h1 : ((2 * π * (n 1 : ℝ)) ^ 2) ^ α 1 ≤ X ^ α 1 :=
      pow_le_pow_left₀ (sq_nonneg _) (hfac 1) _
    have h2 : ((2 * π * (n 2 : ℝ)) ^ 2) ^ α 2 ≤ X ^ α 2 :=
      pow_le_pow_left₀ (sq_nonneg _) (hfac 2) _
    unfold tsymSq
    calc ((2 * π * (n 0 : ℝ)) ^ 2) ^ α 0 * ((2 * π * (n 1 : ℝ)) ^ 2) ^ α 1 *
          ((2 * π * (n 2 : ℝ)) ^ 2) ^ α 2 ≤ X ^ α 0 * X ^ α 1 * X ^ α 2 := by
          gcongr
      _ = X ^ (α 0 + α 1 + α 2) := by rw [pow_add, pow_add]
      _ ≤ X ^ 2 := pow_le_pow_right₀ hX1 hα
  have hcard : (multiIndices 2).card ≤ 27 := by
    unfold multiIndices
    refine (card_filter_le _ _).trans ?_
    simp
  unfold trigWeight
  calc ∑ α ∈ multiIndices 2, tsymSq α n ≤ ∑ _α ∈ multiIndices 2, X ^ 2 := sum_le_sum hterm
    _ = (multiIndices 2).card * X ^ 2 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 27 * X ^ 2 := by
        gcongr
        exact_mod_cast hcard
    _ = 27 * (2 * π) ^ 4 * (1 + ab n) ^ 4 := by rw [hX]; ring

theorem pow_max_le (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (q : ℕ) :
    max (max 1 a) (max b c) ^ q ≤ 1 + a ^ q + b ^ q + c ^ q := by
  have h1 : (0 : ℝ) ≤ a ^ q := pow_nonneg ha q
  have h2 : (0 : ℝ) ≤ b ^ q := pow_nonneg hb q
  have h3 : (0 : ℝ) ≤ c ^ q := pow_nonneg hc q
  rcases max_cases (max 1 a) (max b c) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · rcases max_cases 1 a with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h'] <;> simp <;> linarith
  · rcases max_cases b c with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h'] <;> linarith

theorem one_add_ab_pow_le (n : Fin 3 → ℤ) (q : ℕ) :
    (1 + ab n) ^ q ≤ 4 ^ q * (1 + |(n 0 : ℝ)| ^ q + |(n 1 : ℝ)| ^ q + |(n 2 : ℝ)| ^ q) := by
  set m := max (max 1 |(n 0 : ℝ)|) (max |(n 1 : ℝ)| |(n 2 : ℝ)|) with hm
  have hm1 : 1 ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
  have h0 : |(n 0 : ℝ)| ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
  have h1 : |(n 1 : ℝ)| ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
  have h2 : |(n 2 : ℝ)| ≤ m := le_trans (le_max_right _ _) (le_max_right _ _)
  have hle : 1 + ab n ≤ 4 * m := by
    unfold ab; rw [Fin.sum_univ_three]; linarith
  have hab := ab_nonneg n
  calc (1 + ab n) ^ q ≤ (4 * m) ^ q := pow_le_pow_left₀ (by linarith) hle q
    _ = 4 ^ q * m ^ q := mul_pow _ _ _
    _ ≤ 4 ^ q * (1 + |(n 0 : ℝ)| ^ q + |(n 1 : ℝ)| ^ q + |(n 2 : ℝ)| ^ q) := by
        gcongr
        exact pow_max_le _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) q

theorem iteratedFDeriv_per {g : (Fin 3 → ℝ) → ℂ} (hp : SobolevBoxCr.IsPeriodic g) (p : ℕ) :
    PeriodicCube.IsZPeriodic (fun y => iteratedFDeriv ℝ p g y) := by
  intro k y
  have e : (fun z => g (z + PeriodicCube.zvec k)) = g := funext fun z => hp k z
  have := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := g) p (PeriodicCube.zvec k) (x := y)
  rw [e] at this
  exact this.symm

/-- **Smooth periodic functions are in every weighted Wiener algebra.** -/
theorem wsum_of_smooth {g : (Fin 3 → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hp : SobolevBoxCr.IsPeriodic g) (k : ℕ) :
    WSum 1 k (SobolevBoxCr.descend hg.continuous hp) := by
  -- uniform bounds on the derivatives
  have hbd : ∀ p : ℕ, ∃ M, 0 ≤ M ∧ ∀ y, ‖iteratedFDeriv ℝ p g y‖ ≤ M := fun p =>
    GenSlice.exists_bound_of_zperiodic (hg.continuous_iteratedFDeriv (by exact_mod_cast le_top))
      (iteratedFDeriv_per hp p)
  set q := k + 4 with hq
  obtain ⟨B0, hB0, hb0⟩ := hbd 0
  obtain ⟨Bq, hBq, hbq⟩ := hbd q
  have hdir : ∀ p (M : ℝ), (∀ y, ‖iteratedFDeriv ℝ p g y‖ ≤ M) → ∀ (i : Fin 3) y,
      ‖iteratedFDeriv ℝ p g y (fun _ => Pi.single i 1)‖ ≤ M := by
    intro p M hM i y
    refine ((iteratedFDeriv ℝ p g y).le_opNorm _).trans ?_
    have : ∏ _j : Fin p, ‖(Pi.single i (1 : ℝ) : Fin 3 → ℝ)‖ = 1 := by
      refine Finset.prod_eq_one fun _ _ => ?_
      rw [Pi.norm_single, norm_one]
    rw [this, mul_one]; exact hM y
  set c : (Fin 3 → ℤ) → ℂ := mFourierCoeff (descendFun g) with hc
  have hc0 : ∀ n, ‖c n‖ ≤ B0 := by
    intro n
    have := GevreyFourier.norm_mFourierCoeff_mul_pow_le hg hp 0 0 (hdir 0 B0 hb0 0) n
    simpa using this
  have hcq : ∀ n (i : Fin 3), ‖c n‖ * |(n i : ℝ)| ^ q ≤ Bq / (2 * π) ^ q := by
    intro n i
    have := GevreyFourier.norm_mFourierCoeff_mul_pow_le hg hp i q (hdir q Bq hbq i) n
    rw [le_div_iff₀ (by positivity)]
    calc ‖c n‖ * |(n i : ℝ)| ^ q * (2 * π) ^ q
        = ‖c n‖ * (2 * π * |(n i : ℝ)|) ^ q := by ring
      _ ≤ Bq := this
  set K : ℝ := 4 ^ q * (B0 + 3 * (Bq / (2 * π) ^ q)) with hK
  have hKq : ∀ n, (1 + ab n) ^ q * ‖c n‖ ≤ K := by
    intro n
    have h := one_add_ab_pow_le n q
    have hcn := norm_nonneg (c n)
    calc (1 + ab n) ^ q * ‖c n‖
        ≤ 4 ^ q * (1 + |(n 0 : ℝ)| ^ q + |(n 1 : ℝ)| ^ q + |(n 2 : ℝ)| ^ q) * ‖c n‖ :=
          mul_le_mul_of_nonneg_right h hcn
      _ = 4 ^ q * (‖c n‖ + ‖c n‖ * |(n 0 : ℝ)| ^ q + ‖c n‖ * |(n 1 : ℝ)| ^ q +
            ‖c n‖ * |(n 2 : ℝ)| ^ q) := by ring
      _ ≤ K := by
          rw [hK]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [hc0 n, hcq n 0, hcq n 1, hcq n 2]
  have hK0' : 0 ≤ K := by rw [hK]; positivity
  clear_value K
  -- comparison with `Σ W₂⁻¹`
  have hsum := (summable_inv_trigWeight 2 le_rfl).mul_left (K * (27 * (2 * π) ^ 4))
  show Summable fun n => wt 1 k n * ‖c n‖
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (wt_pos one_pos k n).le (norm_nonneg _))
    (fun n => ?_) hsum
  have hab := ab_nonneg n
  have hpos : 0 < 1 + ab n := by linarith
  have hW := trigWeight_two_le n
  have hWpos := trigWeight_pos 2 n
  simp only [wt, div_one]
  have h4 : (1 + ab n) ^ k * ‖c n‖ ≤ K / (1 + ab n) ^ 4 := by
    rw [le_div_iff₀ (by positivity), mul_assoc, mul_comm ‖c n‖, ← mul_assoc, ← pow_add]
    exact hKq n
  have hK0 : 0 ≤ K := hK0'
  calc (1 + ab n) ^ k * ‖c n‖ ≤ K / (1 + ab n) ^ 4 := h4
    _ ≤ K * (27 * (2 * π) ^ 4) * (trigWeight 2 n)⁻¹ := by
        rw [div_eq_mul_inv, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hK0
        rw [← div_eq_mul_inv, le_div_iff₀ hWpos]
        calc ((1 + ab n) ^ 4)⁻¹ * trigWeight 2 n
            ≤ ((1 + ab n) ^ 4)⁻¹ * (27 * (2 * π) ^ 4 * (1 + ab n) ^ 4) :=
              mul_le_mul_of_nonneg_left hW (by positivity)
          _ = 27 * (2 * π) ^ 4 := by field_simp

end

end MathPhys.LichReg
