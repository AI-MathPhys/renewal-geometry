/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.Continuum.LichnerowiczContraction

/-!
# Weighted Wiener algebras on `𝕋³`

Generic infrastructure (no renewal notions) for the elliptic regularity of the conformal factor
of `prop:generated-initial` (Einstein–Standard-Model action-closure manuscript).  For a weight
`wt L k n = (1 + |n|₁/L)^k` (`L > 0`) — submultiplicative, `wt(m + n) ≤ wt m · wt n` — the
continuous functions on `𝕋³` with `Σ_n wt(n)|F̂(n)| < ∞` form a Banach algebra:

* `hasSum_coeff_mul`: for absolutely summable Fourier series, `(FG)^ = F̂ ⋆ Ĝ`;
* `wsum_mul`: `‖FG‖_w ≤ ‖F‖_w ‖G‖_w`; `wsum_pow`: `‖F^j‖_w ≤ ‖F‖_w^j`;
* `wsum_inv` (**Neumann series**): if `‖u‖_w < 1` then `x ↦ (1 + u(x))⁻¹` is in the algebra with
  `‖(1 + u)⁻¹‖_w ≤ (1 - ‖u‖_w)⁻¹`;
* `exists_L_lt_one`: if `Σ_n (1 + |n|₁)^k |û(n)| < ∞` and `Σ_n |û(n)| < 1`, then
  `‖u‖_{wt L k} < 1` for a large `L` (dominated convergence) — the **spectral radius of `u` in every
  weighted algebra is at most its Wiener norm**, which is what makes elliptic regularity hold at
  all orders without an order-dependent smallness condition.
-/

open Finset Filter Topology UnitAddTorus
open scoped BigOperators Real

namespace MathPhys.LichReg

open TorusFourierTruncation TorusSobolevTransfer PeriodicGridSobolev PeriodicGridSobolev.Sampling

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable section

/-! ### Weights -/

/-- `|n|₁ = Σᵢ |nᵢ|`. -/
def ab (n : Fin 3 → ℤ) : ℝ := ∑ i, |(n i : ℝ)|

theorem ab_nonneg (n : Fin 3 → ℤ) : 0 ≤ ab n := sum_nonneg fun _ _ => abs_nonneg _

theorem ab_zero : ab 0 = 0 := by simp [ab]

theorem ab_add_le (m n : Fin 3 → ℤ) : ab (m + n) ≤ ab m + ab n := by
  unfold ab
  rw [← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  have e : (((m + n) i : ℤ) : ℝ) = (m i : ℝ) + (n i : ℝ) := by push_cast [Pi.add_apply]; ring
  rw [e]
  exact abs_add_le _ _

/-- The weight `(1 + |n|₁/L)^k`. -/
def wt (L : ℝ) (k : ℕ) (n : Fin 3 → ℤ) : ℝ := (1 + ab n / L) ^ k

variable {L : ℝ}

theorem one_le_wt (hL : 0 < L) (k : ℕ) (n : Fin 3 → ℤ) : 1 ≤ wt L k n := by
  have h0 := ab_nonneg n
  have h1 : 0 ≤ ab n / L := by positivity
  exact one_le_pow₀ (by linarith)

theorem wt_pos (hL : 0 < L) (k : ℕ) (n : Fin 3 → ℤ) : 0 < wt L k n :=
  lt_of_lt_of_le one_pos (one_le_wt hL k n)

theorem wt_zero (k : ℕ) : wt L k 0 = 1 := by simp [wt, ab_zero]

theorem wt_add_le (hL : 0 < L) (k : ℕ) (m n : Fin 3 → ℤ) :
    wt L k (m + n) ≤ wt L k m * wt L k n := by
  unfold wt
  rw [← mul_pow]
  have hm := ab_nonneg m
  have hn := ab_nonneg n
  have h1 : 0 ≤ ab (m + n) / L := by have := ab_nonneg (m + n); positivity
  refine pow_le_pow_left₀ (by linarith) ?_ k
  have h2 := ab_add_le m n
  have h3 : ab (m + n) / L ≤ ab m / L + ab n / L := by
    rw [← add_div]; exact div_le_div_of_nonneg_right h2 hL.le
  have h4 : 0 ≤ ab m / L * (ab n / L) := by positivity
  nlinarith

theorem wt_le_wt_one (hL : 1 ≤ L) (k : ℕ) (n : Fin 3 → ℤ) : wt L k n ≤ wt 1 k n := by
  unfold wt
  have h0 := ab_nonneg n
  refine pow_le_pow_left₀ (by positivity) ?_ k
  rw [div_one]
  have : ab n / L ≤ ab n := div_le_self h0 hL
  linarith

theorem wt_one_le (hL : 1 ≤ L) (k : ℕ) (n : Fin 3 → ℤ) : wt 1 k n ≤ L ^ k * wt L k n := by
  unfold wt
  rw [← mul_pow]
  have h0 := ab_nonneg n
  refine pow_le_pow_left₀ (by positivity) ?_ k
  rw [div_one, mul_add, mul_one, mul_div_cancel₀ _ (by positivity : L ≠ 0)]
  linarith

/-! ### Weighted Wiener norms -/

/-- `Σ_n wt(n)|F̂(n)| < ∞`. -/
def WSum (L : ℝ) (k : ℕ) (F : CT) : Prop :=
  Summable fun n => wt L k n * ‖mFourierCoeff ⇑F n‖

/-- `‖F‖_w = Σ_n wt(n)|F̂(n)|`. -/
def wn (L : ℝ) (k : ℕ) (F : CT) : ℝ := ∑' n, wt L k n * ‖mFourierCoeff ⇑F n‖

theorem wn_nonneg (hL : 0 < L) (k : ℕ) (F : CT) : 0 ≤ wn L k F :=
  tsum_nonneg fun n => mul_nonneg (wt_pos hL k n).le (norm_nonneg _)

theorem WSum.summable_norm (hL : 0 < L) {k : ℕ} {F : CT} (h : WSum L k F) :
    Summable fun n => ‖mFourierCoeff ⇑F n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => le_mul_of_one_le_left (norm_nonneg _) (one_le_wt hL k n)) h

theorem tsum_norm_le_wn (hL : 0 < L) {k : ℕ} {F : CT} (h : WSum L k F) :
    ∑' n, ‖mFourierCoeff ⇑F n‖ ≤ wn L k F :=
  (h.summable_norm hL).tsum_le_tsum
    (fun n => le_mul_of_one_le_left (norm_nonneg _) (one_le_wt hL k n)) h

theorem WSum.of_one (hL : 1 ≤ L) {k : ℕ} {F : CT} (h : WSum 1 k F) : WSum L k F :=
  Summable.of_nonneg_of_le
    (fun n => mul_nonneg (wt_pos (by linarith) k n).le (norm_nonneg _))
    (fun n => mul_le_mul_of_nonneg_right (wt_le_wt_one hL k n) (norm_nonneg _)) h

theorem WSum.to_one (hL : 1 ≤ L) {k : ℕ} {F : CT} (h : WSum L k F) : WSum 1 k F :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (wt_pos one_pos k n).le (norm_nonneg _))
    (fun n => by
      calc wt 1 k n * ‖mFourierCoeff ⇑F n‖ ≤ (L ^ k * wt L k n) * ‖mFourierCoeff ⇑F n‖ :=
            mul_le_mul_of_nonneg_right (wt_one_le hL k n) (norm_nonneg _)
        _ = L ^ k * (wt L k n * ‖mFourierCoeff ⇑F n‖) := by ring)
    (h.mul_left _)

/-! ### Fourier series and products -/

/-- The Fourier coefficient functional as a continuous linear map on `C(𝕋³, ℂ)`. -/
def coeffL (n : Fin 3 → ℤ) : CT →L[ℂ] ℂ :=
  (innerSL ℂ (mFourierLp (d := Fin 3) 2 n)).comp (ContinuousMap.toLp 2 MeasureTheory.volume ℂ)

theorem coeffL_apply (n : Fin 3 → ℤ) (F : CT) : coeffL n F = mFourierCoeff ⇑F n :=
  (TorusSobolev.mFourierCoeff_eq_inner F n).symm

theorem mFourier_add_fun (m n : Fin 3 → ℤ) :
    mFourier (m + n) = (mFourier m * mFourier n : CT) := by
  ext x
  rw [ContinuousMap.mul_apply]
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => fourier_add

theorem coeff_mFourier (m n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(mFourier m : CT) n = if m = n then 1 else 0 := by
  rw [TorusSobolev.mFourierCoeff_mFourier]
  by_cases h : m = n
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem hasSum_series {F : CT} (hF : Summable fun n => ‖mFourierCoeff ⇑F n‖) :
    HasSum (fun n => mFourierCoeff ⇑F n • mFourier n) F :=
  hasSum_mFourier_series_of_summable (hF.of_norm)

/-- **The Fourier coefficients of a product of absolutely convergent Fourier series are the
convolution of the coefficients.** -/
theorem hasSum_coeff_mul {F G : CT} (hF : Summable fun n => ‖mFourierCoeff ⇑F n‖)
    (hG : Summable fun n => ‖mFourierCoeff ⇑G n‖) (k : Fin 3 → ℤ) :
    HasSum (fun m => mFourierCoeff ⇑F m * mFourierCoeff ⇑G (k - m)) (mFourierCoeff ⇑(F * G) k) := by
  have hnF : Summable fun n => ‖mFourierCoeff ⇑F n • (mFourier n : CT)‖ := by
    simpa only [norm_smul, mFourier_norm, mul_one] using hF
  have hnG : Summable fun n => ‖mFourierCoeff ⇑G n • (mFourier n : CT)‖ := by
    simpa only [norm_smul, mFourier_norm, mul_one] using hG
  have hS := summable_mul_of_summable_norm hnF hnG
  have h1 := hasSum_series hF
  have h2 := hasSum_series hG
  have hP := HasSum.mul (α := CT) h1 h2 hS
  have hC := HasSum.mapL (coeffL k) hP
  rw [coeffL_apply] at hC
  have e : ∀ p : (Fin 3 → ℤ) × (Fin 3 → ℤ),
      coeffL k ((mFourierCoeff ⇑F p.1 • (mFourier p.1 : CT)) *
        (mFourierCoeff ⇑G p.2 • (mFourier p.2 : CT))) =
      if p.1 + p.2 = k then mFourierCoeff ⇑F p.1 * mFourierCoeff ⇑G p.2 else 0 := by
    intro p
    rw [smul_mul_smul_comm, ← mFourier_add_fun, map_smul, coeffL_apply, coeff_mFourier]
    split_ifs <;> simp
  simp only [e] at hC
  have hinj : Function.Injective (fun m : Fin 3 → ℤ => (m, k - m)) := by
    intro a b h; exact (Prod.mk.inj h).1
  rw [← hinj.hasSum_iff] at hC
  · convert hC using 1
    funext m
    simp
  · intro p hp
    rw [if_neg]
    intro hk
    exact hp ⟨p.1, by simp [← hk]⟩

/-- **The weighted product estimate** for a submultiplicative weight. -/
theorem wsum_mul (hL : 0 < L) {k : ℕ} {F G : CT} (hF : WSum L k F) (hG : WSum L k G) :
    WSum L k (F * G) ∧ wn L k (F * G) ≤ wn L k F * wn L k G := by
  set a : (Fin 3 → ℤ) → ℝ := fun n => wt L k n * ‖mFourierCoeff ⇑F n‖ with ha
  set b : (Fin 3 → ℤ) → ℝ := fun n => wt L k n * ‖mFourierCoeff ⇑G n‖ with hb
  have ha0 : ∀ n, 0 ≤ a n := fun n => mul_nonneg (wt_pos hL k n).le (norm_nonneg _)
  have hb0 : ∀ n, 0 ≤ b n := fun n => mul_nonneg (wt_pos hL k n).le (norm_nonneg _)
  -- the double series `Σ_{(m,n)} a m b n`
  have hab : HasSum (fun p : (Fin 3 → ℤ) × (Fin 3 → ℤ) => a p.1 * b p.2)
      ((∑' n, a n) * ∑' n, b n) := by
    have hna : Summable fun n => ‖a n‖ :=
      (summable_congr fun n => Real.norm_of_nonneg (ha0 n)).mpr hF
    have hnb : Summable fun n => ‖b n‖ :=
      (summable_congr fun n => Real.norm_of_nonneg (hb0 n)).mpr hG
    exact hF.hasSum.mul hG.hasSum (summable_mul_of_summable_norm hna hnb)
  -- reindex `(k, m) ↦ (m, k - m)`
  set e : (Fin 3 → ℤ) × (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
    { toFun := fun q => (q.2, q.1 - q.2)
      invFun := fun p => (p.1 + p.2, p.1)
      left_inv := fun q => by simp
      right_inv := fun p => by simp } with he
  have hab' : HasSum (fun q : (Fin 3 → ℤ) × (Fin 3 → ℤ) => a q.2 * b (q.1 - q.2))
      ((∑' n, a n) * ∑' n, b n) := by
    rw [← e.hasSum_iff] at hab
    exact hab
  have hfib : ∀ c : Fin 3 → ℤ, Summable fun m => a m * b (c - m) := fun c =>
    hab'.summable.prod_factor c
  have hconv : HasSum (fun c => ∑' m, a m * b (c - m)) ((∑' n, a n) * ∑' n, b n) :=
    hab'.prod_fiberwise fun c => (hfib c).hasSum
  -- pointwise bound
  have hpt : ∀ c, wt L k c * ‖mFourierCoeff ⇑(F * G) c‖ ≤ ∑' m, a m * b (c - m) := by
    intro c
    have hs := hasSum_coeff_mul (hF.summable_norm hL) (hG.summable_norm hL) c
    have hn : Summable fun m => ‖mFourierCoeff ⇑F m * mFourierCoeff ⇑G (c - m)‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) (hfib c)
      rw [norm_mul]
      have h1 := one_le_wt hL k m
      have h2 := one_le_wt hL k (c - m)
      exact mul_le_mul (le_mul_of_one_le_left (norm_nonneg _) h1)
        (le_mul_of_one_le_left (norm_nonneg _) h2) (norm_nonneg _)
        (mul_nonneg (wt_pos hL k m).le (norm_nonneg _))
    calc wt L k c * ‖mFourierCoeff ⇑(F * G) c‖
        = wt L k c * ‖∑' m, mFourierCoeff ⇑F m * mFourierCoeff ⇑G (c - m)‖ := by rw [hs.tsum_eq]
      _ ≤ wt L k c * ∑' m, ‖mFourierCoeff ⇑F m * mFourierCoeff ⇑G (c - m)‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hn) (wt_pos hL k c).le
      _ = ∑' m, wt L k c * ‖mFourierCoeff ⇑F m * mFourierCoeff ⇑G (c - m)‖ := by
          rw [tsum_mul_left]
      _ ≤ ∑' m, a m * b (c - m) := by
          refine (hn.mul_left _).tsum_le_tsum (fun m => ?_) (hfib c)
          rw [norm_mul]
          have hw := wt_add_le hL k m (c - m)
          rw [add_sub_cancel] at hw
          have h0 : 0 ≤ ‖mFourierCoeff ⇑F m‖ * ‖mFourierCoeff ⇑G (c - m)‖ :=
            mul_nonneg (norm_nonneg _) (norm_nonneg _)
          calc wt L k c * (‖mFourierCoeff ⇑F m‖ * ‖mFourierCoeff ⇑G (c - m)‖)
              ≤ (wt L k m * wt L k (c - m)) * (‖mFourierCoeff ⇑F m‖ *
                  ‖mFourierCoeff ⇑G (c - m)‖) := mul_le_mul_of_nonneg_right hw h0
            _ = a m * b (c - m) := by simp only [ha, hb]; ring
  have hsum : WSum L k (F * G) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (wt_pos hL k n).le (norm_nonneg _)) hpt
      hconv.summable
  refine ⟨hsum, ?_⟩
  calc wn L k (F * G) ≤ ∑' c, ∑' m, a m * b (c - m) := hsum.tsum_le_tsum hpt hconv.summable
    _ = wn L k F * wn L k G := hconv.tsum_eq

theorem coeff_one (n : Fin 3 → ℤ) : mFourierCoeff ⇑(1 : CT) n = if n = 0 then 1 else 0 := by
  have : (1 : CT) = mFourier 0 := by ext x; simp [mFourier]
  rw [this, coeff_mFourier]
  by_cases h : n = 0
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

theorem wsum_one (hL : 0 < L) (k : ℕ) : WSum L k (1 : CT) ∧ wn L k (1 : CT) = 1 := by
  have e : (fun n => wt L k n * ‖mFourierCoeff ⇑(1 : CT) n‖) = fun n => if n = 0 then 1 else 0 := by
    funext n; rw [coeff_one]; split_ifs with h
    · subst h; simp [wt_zero]
    · simp
  refine ⟨?_, ?_⟩
  · unfold WSum; rw [e]; exact (hasSum_ite_eq 0 (1 : ℝ)).summable
  · unfold wn; rw [e, tsum_ite_eq]

/-- `‖F^j‖_w ≤ ‖F‖_w^j`. -/
theorem wsum_pow (hL : 0 < L) {k : ℕ} {F : CT} (hF : WSum L k F) :
    ∀ j : ℕ, WSum L k (F ^ j) ∧ wn L k (F ^ j) ≤ wn L k F ^ j
  | 0 => by rw [pow_zero, pow_zero, (wsum_one hL k).2]; exact ⟨(wsum_one hL k).1, le_rfl⟩
  | j + 1 => by
    obtain ⟨h1, h2⟩ := wsum_pow hL hF j
    obtain ⟨h3, h4⟩ := wsum_mul hL h1 hF
    rw [pow_succ]
    refine ⟨h3, h4.trans ?_⟩
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right h2 (wn_nonneg hL k F)

theorem wsum_neg {k : ℕ} {F : CT} (hF : WSum L k F) : WSum L k (-F) ∧ wn L k (-F) = wn L k F := by
  have e : ∀ n, ‖mFourierCoeff ⇑(-F) n‖ = ‖mFourierCoeff ⇑F n‖ := fun n => by
    rw [← coeffL_apply, map_neg, coeffL_apply, norm_neg]
  refine ⟨?_, ?_⟩
  · unfold WSum; simp only [e]; exact hF
  · unfold wn; simp only [e]

/-- **Neumann series in the weighted Wiener algebra.** -/
theorem wsum_inv (hL : 0 < L) {k : ℕ} {u : CT} (hu : WSum L k u) (hq : wn L k u < 1) :
    ∃ v : CT, (∀ x, v x = (1 + u x)⁻¹) ∧ WSum L k v ∧ wn L k v ≤ (1 - wn L k u)⁻¹ := by
  have hq0 := wn_nonneg hL k u
  -- the sup norm of `u` is `< 1`
  have hsup : ‖u‖ < 1 := by
    rw [ContinuousMap.norm_lt_iff _ one_pos]
    intro x
    have hx := (hasSum_series (hu.summable_norm hL)).mapL (ContinuousMap.evalCLM ℂ x)
    simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul] at hx
    have hb : ‖u x‖ ≤ ∑' n, ‖mFourierCoeff ⇑u n‖ := by
      rw [← hx.tsum_eq]
      refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
      · simpa [norm_mul, norm_mFourier_apply'] using hu.summable_norm hL
      · simp [norm_mul, norm_mFourier_apply']
    exact hb.trans_lt ((tsum_norm_le_wn hL hu).trans_lt hq)
  have hsup' : ‖-u‖ < 1 := by rwa [norm_neg]
  have hgs : Summable fun j : ℕ => (-u) ^ j :=
    HasSummableGeomSeries.summable_geometric_of_norm_lt_one (-u) hsup'
  set v : CT := ∑' j : ℕ, (-u) ^ j with hv
  have hvu : v * (1 + u) = 1 := by
    have := geom_series_mul_neg (-u) hsup'
    rwa [sub_neg_eq_add] at this
  refine ⟨v, fun x => ?_, ?_⟩
  · have hx := congrArg (fun F : CT => F x) hvu
    simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.one_apply] at hx
    exact eq_inv_of_mul_eq_one_left hx
  -- coefficients of `v`
  obtain ⟨hnu, hnu'⟩ := wsum_neg hu
  have hpow := wsum_pow hL hnu
  have hcoef : ∀ n, HasSum (fun j : ℕ => mFourierCoeff ⇑((-u) ^ j) n) (mFourierCoeff ⇑v n) := by
    intro n
    have := hgs.hasSum.mapL (coeffL n)
    simpa only [coeffL_apply] using this
  set f : ℕ × (Fin 3 → ℤ) → ℝ := fun p => wt L k p.2 * ‖mFourierCoeff ⇑((-u) ^ p.1) p.2‖ with hf
  have hf0 : 0 ≤ f := fun p => mul_nonneg (wt_pos hL k p.2).le (norm_nonneg _)
  have hrow : ∀ j : ℕ, Summable fun n => f (j, n) := fun j => (hpow j).1
  have hrowle : ∀ j : ℕ, ∑' n, f (j, n) ≤ wn L k u ^ j := by
    intro j; have := (hpow j).2; rw [hnu'] at this; exact this
  have hgeo : Summable fun j : ℕ => wn L k u ^ j := summable_geometric_of_lt_one hq0 hq
  have hcol : Summable fun j : ℕ => ∑' n, f (j, n) :=
    Summable.of_nonneg_of_le (fun j => tsum_nonneg fun n => hf0 _) hrowle hgeo
  have hf : Summable f := (summable_prod_of_nonneg hf0).2 ⟨hrow, hcol⟩
  have hswap : Summable fun n => ∑' j : ℕ, f (j, n) := hf.prod_symm.prod
  have hpt : ∀ n, wt L k n * ‖mFourierCoeff ⇑v n‖ ≤ ∑' j : ℕ, f (j, n) := by
    intro n
    have hs : Summable fun j : ℕ => ‖mFourierCoeff ⇑((-u) ^ j) n‖ := by
      have h1 : Summable fun j : ℕ => f (j, n) := hf.prod_symm.prod_factor n
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_) h1
      exact le_mul_of_one_le_left (norm_nonneg _) (one_le_wt hL k n)
    calc wt L k n * ‖mFourierCoeff ⇑v n‖
        = wt L k n * ‖∑' j : ℕ, mFourierCoeff ⇑((-u) ^ j) n‖ := by rw [(hcoef n).tsum_eq]
      _ ≤ wt L k n * ∑' j : ℕ, ‖mFourierCoeff ⇑((-u) ^ j) n‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs) (wt_pos hL k n).le
      _ = ∑' j : ℕ, f (j, n) := by rw [← tsum_mul_left]
  have hsum : WSum L k v :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (wt_pos hL k n).le (norm_nonneg _)) hpt hswap
  refine ⟨hsum, ?_⟩
  calc wn L k v ≤ ∑' n, ∑' j : ℕ, f (j, n) := hsum.tsum_le_tsum hpt hswap
    _ = ∑' j : ℕ, ∑' n, f (j, n) := (Summable.tsum_comm' (f := fun j n => f (j, n)) hf hrow
          (fun n => hf.prod_symm.prod_factor n))
    _ ≤ ∑' j : ℕ, wn L k u ^ j := hcol.tsum_le_tsum hrowle hgeo
    _ = (1 - wn L k u)⁻¹ := tsum_geometric_of_lt_one hq0 hq

/-- **For large `L` the weighted norm approaches the Wiener norm.** -/
theorem exists_L_lt_one {k : ℕ} {u : CT} (hu : WSum 1 k u)
    (h1 : ∑' n, ‖mFourierCoeff ⇑u n‖ < 1) : ∃ L, 1 ≤ L ∧ wn L k u < 1 := by
  have hlim : Tendsto (fun L : ℝ => wn L k u) atTop (𝓝 (∑' n, ‖mFourierCoeff ⇑u n‖)) := by
    unfold wn
    refine tendsto_tsum_of_dominated_convergence (bound := fun n => wt 1 k n * ‖mFourierCoeff ⇑u n‖)
      hu (fun n => ?_) ?_
    · have h : Tendsto (fun L : ℝ => (1 + ab n / L) ^ k) atTop (𝓝 ((1 + 0) ^ k)) :=
        ((tendsto_const_nhds.div_atTop tendsto_id).const_add 1).pow k
      simp only [add_zero, one_pow] at h
      have := h.mul_const ‖mFourierCoeff ⇑u n‖
      simpa [wt] using this
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL n
      rw [Real.norm_of_nonneg (mul_nonneg (wt_pos (by linarith) k n).le (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_right (wt_le_wt_one hL k n) (norm_nonneg _)
  obtain ⟨L, hL⟩ := ((hlim.eventually (gt_mem_nhds h1)).and (eventually_ge_atTop 1)).exists
  exact ⟨L, hL.2, hL.1⟩

end

end MathPhys.LichReg
