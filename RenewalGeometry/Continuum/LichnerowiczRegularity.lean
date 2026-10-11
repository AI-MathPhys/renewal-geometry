/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.LichnerowiczFourierAlgebra

/-!
# Elliptic regularity of the conformal factor at all orders

Einstein–Standard-Model action-closure manuscript, `prop:generated-initial`: the contraction of
`LichnerowiczContraction` produces a conformal factor `w = 1 + u ∈ H^{r+2}` with an
order-dependent smallness threshold.  Here we prove that **every** solution of the conformal
Hamiltonian equation `eq:generated-Hamiltonian` with `u ∈ H^{r+2}` (`r ≥ 2`), Wiener norm
`Σ|û| < 1` and sources in every weighted Wiener algebra has `u` in every weighted Wiener algebra:
`Σ_n (1 + |n|₁)^k |û(n)| < ∞` for every `k` (`wsum_all_of_hamiltonianEq`).  Hence (see
`LichnerowiczSmoothLift`) `w` is `C^∞`; no smallness at the higher orders is needed, because the
spectral radius of `u` in each weighted algebra is bounded by its Wiener norm
(`LichReg.exists_L_lt_one`).

* closure of the weighted algebras under sums, scalar multiples, products and the inverse
  `(1 + u)⁻¹` (`wsum_add`, `wsum_smul`, `wsum_const`, `wsum_mul_one`, `wsum_inv_one`);
* `lap_eq_rhs`: the equation in the form `Δu = R(u)` as continuous functions;
* `wsum_succ`: one step of the bootstrap (`Δ⁻¹` gains one weight power since
  `1 + |n|₁ ≤ |2πn|²` for `n ≠ 0`).
-/

open Finset Filter Topology UnitAddTorus
open scoped BigOperators Real

namespace RenewalGeometry.LichReg

open TorusFourierTruncation TorusSobolevTransfer PeriodicGridSobolev PeriodicGridSobolev.Sampling
  LichnerowiczContraction

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable section

/-! ### Closure properties (weight `L = 1`) -/

variable {k : ℕ}

theorem coeff_add (F G : CT) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(F + G) n = mFourierCoeff ⇑F n + mFourierCoeff ⇑G n := by
  rw [← coeffL_apply, map_add, coeffL_apply, coeffL_apply]

theorem coeff_smul (c : ℂ) (F : CT) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(c • F) n = c * mFourierCoeff ⇑F n := by
  rw [← coeffL_apply, map_smul, coeffL_apply, smul_eq_mul]

theorem wsum_add {F G : CT} (hF : WSum 1 k F) (hG : WSum 1 k G) : WSum 1 k (F + G) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (wt_pos one_pos k n).le (norm_nonneg _))
    (fun n => ?_) (hF.add hG)
  rw [coeff_add, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (wt_pos one_pos k n).le

theorem wsum_smul (c : ℂ) {F : CT} (hF : WSum 1 k F) : WSum 1 k (c • F) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (wt_pos one_pos k n).le (norm_nonneg _))
    (fun n => ?_) (hF.mul_left ‖c‖)
  rw [coeff_smul, norm_mul]
  exact le_of_eq (by ring)

theorem wsum_sub {F G : CT} (hF : WSum 1 k F) (hG : WSum 1 k G) : WSum 1 k (F - G) := by
  rw [sub_eq_add_neg]; exact wsum_add hF (wsum_neg hG).1

theorem wsum_mul_one {F G : CT} (hF : WSum 1 k F) (hG : WSum 1 k G) : WSum 1 k (F * G) :=
  (wsum_mul one_pos hF hG).1

theorem wsum_one' (k : ℕ) : WSum 1 k (1 : CT) := (wsum_one one_pos k).1

theorem wsum_const (c : ℂ) (k : ℕ) : WSum 1 k (ContinuousMap.const _ c) := by
  have : (ContinuousMap.const (UnitAddTorus (Fin 3)) c) = c • (1 : CT) := by ext; simp
  rw [this]; exact wsum_smul c (wsum_one' k)

theorem wsum_pow_one {F : CT} (hF : WSum 1 k F) (j : ℕ) : WSum 1 k (F ^ j) :=
  (wsum_pow one_pos hF j).1

/-- **The inverse `(1 + u)⁻¹` is in every weighted algebra containing `u`**, provided the Wiener
norm of `u` is `< 1`. -/
theorem wsum_inv_one {u : CT} (hu : WSum 1 k u) (h1 : ∑' n, ‖mFourierCoeff ⇑u n‖ < 1) :
    ∃ v : CT, (∀ x, v x = (1 + u x)⁻¹) ∧ WSum 1 k v := by
  obtain ⟨L, hL1, hLt⟩ := exists_L_lt_one hu h1
  obtain ⟨v, hv, hvw, -⟩ := wsum_inv (by linarith) (hu.of_one hL1) hLt
  exact ⟨v, hv, hvw.to_one hL1⟩

/-! ### The equation as an identity of continuous functions -/

variable (D : LichData)

/-- The right-hand side `R(u) = ⅛(-𝖠v⁷ - Gw - 𝖡v³ - 𝖸v + Cw⁵)` of `Δu = R(u)`, `w = 1 + u`,
`v = w⁻¹`. -/
def rhsC (δA δB Y u v : CT) : CT :=
  ((1 : ℂ) / 8) • (-((ContinuousMap.const _ (D.A : ℂ) + δA) * v ^ 7) -
    (D.G : ℂ) • (1 + u) - (ContinuousMap.const _ (D.B : ℂ) + δB) * v ^ 3 - Y * v +
    (D.C : ℂ) • (1 + u) ^ 5)

/-- **`eq:generated-Hamiltonian` as `Δu = R(u)`.** -/
theorem lap_eq_rhs {r : ℕ} (hr : 2 ≤ r) {δA δB Y u v : CT} (hu : MemH (r + 2) ⇑u)
    (hv : ∀ x, v x = (1 + u x)⁻¹) (hE : HamiltonianEq D δA δB Y (1 + u)) :
    lap u = rhsC D δA δB Y u v := by
  ext x
  have h := hE x
  rw [lap_one_add r hr hu] at h
  simp only [hamRes, ContinuousMap.add_apply, ContinuousMap.one_apply] at h
  simp only [rhsC, ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
    ContinuousMap.neg_apply, ContinuousMap.mul_apply, ContinuousMap.pow_apply,
    ContinuousMap.const_apply, ContinuousMap.one_apply, smul_eq_mul, hv x]
  linear_combination (-(1 : ℂ) / 8) * h

/-! ### The bootstrap -/

theorem lapSym_ge (n : Fin 3 → ℤ) (hn : n ≠ 0) : 1 + ab n ≤ lapSym n := by
  have hint : ∀ i, |(n i : ℝ)| ≤ (n i : ℝ) ^ 2 := by
    intro i
    rcases eq_or_ne (n i) 0 with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ |(n i : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
      rw [← sq_abs]; nlinarith
  have hab : 1 ≤ ab n := by
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra h; push_neg at h; exact hn (funext h)
    have h1 : (1 : ℝ) ≤ |(n i : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hi
    exact h1.trans (single_le_sum (f := fun j => |(n j : ℝ)|) (fun _ _ => abs_nonneg _)
      (mem_univ i))
  have hsq : ab n ≤ ∑ i, ((n i : ℝ)) ^ 2 := sum_le_sum fun i _ => hint i
  have hl : lapSym n = 4 * π ^ 2 * ∑ i, ((n i : ℝ)) ^ 2 := by
    unfold lapSym; rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  rw [hl]
  have hπ : (1 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  nlinarith

theorem wt_succ (n : Fin 3 → ℤ) : wt 1 (k + 1) n = (1 + ab n) * wt 1 k n := by
  simp [wt, pow_succ, mul_comm]

/-- **One bootstrap step**: if `Δu = R` with `R` in the `k`-th algebra, `u` is in the
`(k+1)`-th algebra. -/
theorem wsum_succ {r : ℕ} (hr : 2 ≤ r) {u R : CT} (hu : MemH (r + 2) ⇑u) (hk : WSum 1 k u)
    (hR : WSum 1 k R) (hlap : lap u = R) : WSum 1 (k + 1) u := by
  have hcoef : ∀ n, -((lapSym n : ℝ) : ℂ) * mFourierCoeff ⇑u n = mFourierCoeff ⇑R n := by
    intro n; rw [← mFourierCoeff_lap hr hu, hlap]
  set g : (Fin 3 → ℤ) → ℝ := fun n => wt 1 k n * ‖mFourierCoeff ⇑R n‖ +
    (if n = 0 then wt 1 (k + 1) n * ‖mFourierCoeff ⇑u n‖ else 0) with hg
  have hgs : Summable g := hR.add (summable_of_ne_finset_zero (s := {0}) fun n hn => by
    simp only [Finset.mem_singleton] at hn; simp [hn])
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (wt_pos one_pos _ n).le (norm_nonneg _))
    (fun n => ?_) hgs
  by_cases hn : n = 0
  · simp only [hg, hn, if_true]
    have := mul_nonneg (wt_pos one_pos k 0).le (norm_nonneg (mFourierCoeff ⇑R 0))
    linarith
  · simp only [hg, hn, if_false, add_zero]
    have hlap := lapSym_ge n hn
    have hpos : 0 < lapSym n := by have := ab_nonneg n; linarith
    have hR' : ‖mFourierCoeff ⇑R n‖ = lapSym n * ‖mFourierCoeff ⇑u n‖ := by
      rw [← hcoef n, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    rw [wt_succ, hR']
    have h0 := wt_pos one_pos k n
    have h1 := norm_nonneg (mFourierCoeff ⇑u n)
    calc (1 + ab n) * wt 1 k n * ‖mFourierCoeff ⇑u n‖
        ≤ lapSym n * wt 1 k n * ‖mFourierCoeff ⇑u n‖ := by gcongr
      _ = wt 1 k n * (lapSym n * ‖mFourierCoeff ⇑u n‖) := by ring

/-- **Elliptic regularity at all orders** for `eq:generated-Hamiltonian`: a solution
`w = 1 + u` with `u ∈ H^{r+2}` (`r ≥ 2`), Wiener norm `Σ|û| < 1` and sources `δ𝖠, δ𝖡, 𝖸` in every
weighted Wiener algebra has `u` in every weighted Wiener algebra. -/
theorem wsum_all_of_hamiltonianEq {r : ℕ} (hr : 2 ≤ r) {δA δB Y u : CT}
    (hu : MemH (r + 2) ⇑u) (h1 : ∑' n, ‖mFourierCoeff ⇑u n‖ < 1)
    (hA : ∀ k, WSum 1 k δA) (hB : ∀ k, WSum 1 k δB) (hY : ∀ k, WSum 1 k Y)
    (hE : HamiltonianEq D δA δB Y (1 + u)) : ∀ k, WSum 1 k u := by
  have h0 : WSum 1 0 u := by
    unfold WSum
    simp only [wt, pow_zero, one_mul]
    exact summable_norm_of_trigWeight (by omega) hu
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    obtain ⟨v, hv, hvw⟩ := wsum_inv_one ih h1
    have hR : WSum 1 k (rhsC D δA δB Y u v) := by
      unfold rhsC
      refine wsum_smul _ ?_
      refine wsum_add (wsum_sub (wsum_sub (wsum_sub ?_ ?_) ?_) ?_) ?_
      · exact (wsum_neg (wsum_mul_one (wsum_add (wsum_const _ k) (hA k))
          (wsum_pow_one hvw 7))).1
      · exact wsum_smul _ (wsum_add (wsum_one' k) ih)
      · exact wsum_mul_one (wsum_add (wsum_const _ k) (hB k)) (wsum_pow_one hvw 3)
      · exact wsum_mul_one (hY k) hvw
      · exact wsum_smul _ (wsum_pow_one (wsum_add (wsum_one' k) ih) 5)
    exact wsum_succ hr hu ih hR (lap_eq_rhs D hr hu hv hE)

end

end RenewalGeometry.LichReg
