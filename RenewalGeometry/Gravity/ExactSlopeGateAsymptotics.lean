/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ConstantShiftWardOrders
import RenewalGeometry.Gravity.ExactSlowBranchData

/-!
# The necessary quadratic slope gate of the reduced leading system
  (`thm:supp-exact-slope-gate`, `eq:supp-exact-slope-data`, `eq:supp-exact-slope-polynomial`,
  `eq:supp-exact-slope-estimate`; emergent-spacetime manuscript)

General Taylor estimates (via `WardOrders.VanishesToOrder.succ_of_fderiv`):
* `taylor_two`: for `φ` `C²` at `0`, `φ(q) - φ(0) - Dφ(0)q = O(‖q‖²)`;
* `taylor_three`: for `φ` `C³` at `0`, `φ(q) - φ(0) - Dφ(0)q - ½D²φ(0)[q, q] = O(‖q‖³)`.

**`slope_gate`** (`thm:supp-exact-slope-gate`).  Let `𝓕 : R × Y → R` be `C²` and
`𝓗 : R × Y → Ho` be `C³` at `0` with the paired zero `𝓗(0,0) = 0`, `𝓕_y(0,0) = 𝓗_y(0,0) = 0`
(`eq:supp-exact-paired-zero`), and let `(r, y)` be a Lipschitz solution of the reduced system
`r_τ = 𝓕(r, y)`, `𝓗(r, y) = 0` (`eq:supp-exact-reduced-dae`) on `[0, T]` with `r(0) = y(0) = 0`.
With `v = 𝓕(0,0)`, `u₀ = ½𝓕_r v`, `ρ₀ = 𝓗_r v` (`eq:supp-exact-slope-data`) and the slope
polynomial `𝒬 = ExactSlowBranch.slopePolynomial` (`eq:supp-exact-slope-polynomial`):
`ρ₀ = 0`, `r(τ) = τv + τ²u₀ + O(τ³)`, `𝒬(y(τ)/τ) = O(τ)` (`eq:supp-exact-slope-estimate`), and
every cluster point of `y(τ)/τ` as `τ ↓ 0` is a real zero of `𝒬`.
**`slope_gate_exists_root`**: in a proper (e.g. finite-dimensional) slope space, `𝒬` has a zero
in the admissible slope ball `‖c‖ ≤ K` (`K` the Lipschitz constant); hence if that ball contains
no real zero, no such Lipschitz trajectory exists (`slope_gate_no_trajectory`).

The regular equation is used in the classical form (one-sided derivative at every
`τ ∈ [0, T)`); for continuous `𝓕` and Lipschitz `(r, y)` this is equivalent to the integral form.
The paired zero is the conclusion of `thm:supp-exact-reduced-leading-system`
(`ExactReducedLeading.paired_zero`), which rests on the slope-entrance identities.
-/

open Filter Set Asymptotics
open scoped Topology NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry
namespace ExactSlopeGate

open WardOrders ExactSlowBranch

/-! ### Taylor estimates -/

section Taylor

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- Second-order Taylor estimate for a `C²` map. -/
theorem taylor_two {φ : E → G} (hφ : ContDiffAt ℝ 2 φ 0) :
    VanishesToOrder (fun q => φ q - φ 0 - fderiv ℝ φ 0 q) 0 2 := by
  have hev : ∀ᶠ q in 𝓝 (0 : E), ContDiffAt ℝ 2 φ q := hφ.eventually (by simp)
  have hd : ∀ᶠ q in 𝓝 (0 : E), HasFDerivAt (fun q => φ q - φ 0 - fderiv ℝ φ 0 q)
      (fderiv ℝ φ q - fderiv ℝ φ 0) q := by
    filter_upwards [hev] with q hq
    have h1 := (hq.differentiableAt (by simp)).hasFDerivAt
    exact (h1.sub_const (φ 0)).sub (fderiv ℝ φ 0).hasFDerivAt
  have hD1 : DifferentiableAt ℝ (fderiv ℝ φ) 0 :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have o1 : VanishesToOrder (fun q => fderiv ℝ φ q - fderiv ℝ φ 0) 0 1 :=
    vanishesToOrder_one_of_differentiableAt (hD1.sub_const _) (by simp)
  refine VanishesToOrder.succ_of_fderiv (hd.mono fun q hq => hq.differentiableAt) (by simp) ?_
  exact o1.congr' (hd.mono fun q hq => hq.fderiv.symm) EventuallyEq.rfl

/-- Third-order Taylor estimate for a `C³` map. -/
theorem taylor_three {φ : E → G} (hφ : ContDiffAt ℝ 3 φ 0) :
    VanishesToOrder (fun q => φ q - φ 0 - fderiv ℝ φ 0 q - (1 / 2 : ℝ) • sndDeriv φ 0 q q) 0 3 := by
  set B := fderiv ℝ (fderiv ℝ φ) 0
  have hsymm : IsSymmSndFDerivAt ℝ φ 0 := hφ.isSymmSndFDerivAt (by simp; norm_num)
  have hev : ∀ᶠ q in 𝓝 (0 : E), ContDiffAt ℝ 3 φ q := hφ.eventually (by simp)
  -- derivative of `q ↦ B q q`
  have hBq : ∀ q, HasFDerivAt (fun q => B q q) (B q + B.flip q) q := by
    intro q
    have := B.hasFDerivAt.clm_apply (hasFDerivAt_id q)
    simpa using this
  have hflip : ∀ q, B.flip q = B q := by
    intro q; ext w; simp [B, hsymm w q]
  have hd : ∀ᶠ q in 𝓝 (0 : E), HasFDerivAt
      (fun q => φ q - φ 0 - fderiv ℝ φ 0 q - (1 / 2 : ℝ) • sndDeriv φ 0 q q)
      (fderiv ℝ φ q - fderiv ℝ φ 0 - B q) q := by
    filter_upwards [hev] with q hq
    have h1 := (hq.differentiableAt (by simp)).hasFDerivAt
    have h2 : HasFDerivAt
        (fun q => φ q - φ 0 - fderiv ℝ φ 0 q - (1 / 2 : ℝ) • sndDeriv φ 0 q q)
        (fderiv ℝ φ q - fderiv ℝ φ 0 - (1 / 2 : ℝ) • (B q + B.flip q)) q :=
      ((h1.sub_const (φ 0)).sub (fderiv ℝ φ 0).hasFDerivAt).sub ((hBq q).const_smul (1 / 2 : ℝ))
    refine h2.congr_fderiv ?_
    rw [hflip, ← two_smul ℝ (B q), smul_smul]
    norm_num
  -- the derivative `h(q) = Dφ(q) - Dφ(0) - B q` vanishes to order two
  have hev2 : ∀ᶠ q in 𝓝 (0 : E), DifferentiableAt ℝ (fderiv ℝ φ) q :=
    hev.mono fun q hq => (hq.fderiv_right (m := 2) (by norm_num)).differentiableAt (by simp)
  have hdh : ∀ᶠ q in 𝓝 (0 : E), HasFDerivAt (fun q => fderiv ℝ φ q - fderiv ℝ φ 0 - B q)
      (fderiv ℝ (fderiv ℝ φ) q - B) q := by
    filter_upwards [hev2] with q hq
    exact (hq.hasFDerivAt.sub_const (fderiv ℝ φ 0)).sub B.hasFDerivAt
  have hD2 : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ φ)) 0 :=
    ((hφ.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by simp)
  have o1 : VanishesToOrder (fun q => fderiv ℝ (fderiv ℝ φ) q - B) 0 1 :=
    vanishesToOrder_one_of_differentiableAt (hD2.sub_const _) (by simp [B])
  have o2 : VanishesToOrder (fun q => fderiv ℝ φ q - fderiv ℝ φ 0 - B q) 0 2 :=
    VanishesToOrder.succ_of_fderiv (hdh.mono fun q hq => hq.differentiableAt) (by simp)
      (o1.congr' (hdh.mono fun q hq => hq.fderiv.symm) EventuallyEq.rfl)
  refine VanishesToOrder.succ_of_fderiv (hd.mono fun q hq => hq.differentiableAt)
    (by simp [sndDeriv]) ?_
  exact o2.congr' (hd.mono fun q hq => hq.fderiv.symm) EventuallyEq.rfl

/-- A `VanishesToOrder` estimate as an explicit bound on a ball. -/
theorem exists_ball_bound {f : E → G} {k : ℕ} (hf : VanishesToOrder f 0 k) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ q, ‖q‖ < δ → ‖f q‖ ≤ C * ‖q‖ ^ k := by
  obtain ⟨C, hC, hb⟩ := hf.exists_pos
  rw [IsBigOWith] at hb
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff_ball.mp hb
  refine ⟨C, δ, hC.le, hδ, fun q hq => ?_⟩
  have := h q (by rwa [Metric.mem_ball, dist_zero_right])
  rwa [sub_zero, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this

end Taylor

/-! ### The slope gate -/

section Gate

variable {R Y Ho : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup Ho] [NormedSpace ℝ Ho]

/-- The slope polynomial written with the full second derivative:
`𝒬(c) = 𝓗_r 𝓕_r v + D²𝓗(0)[(v, c), (v, c)]`. -/
theorem slopePolynomial_eq (F : R × Y → R) (H : R × Y → Ho) (hsymm : IsSymmSndFDerivAt ℝ H 0)
    (v : R) (c : Y) :
    slopePolynomial F H v c = fderiv ℝ H 0 (fderiv ℝ F 0 (v, 0), 0) + sndDeriv H 0 (v, c) (v, c) := by
  have hvc : ((v, c) : R × Y) = (v, 0) + (0, c) := by simp
  have hs : sndDeriv H 0 (0, c) (v, 0) = sndDeriv H 0 (v, 0) (0, c) := hsymm _ _
  simp only [slopePolynomial]
  rw [hvc]
  simp only [sndDeriv, map_add, add_apply] at hs ⊢
  rw [hs, two_smul]
  abel

theorem continuous_slopePolynomial (F : R × Y → R) (H : R × Y → Ho) (v : R) :
    Continuous fun c => slopePolynomial F H v c := by
  unfold slopePolynomial sndDeriv
  have h1 : Continuous fun c : Y => ((0 : R), c) := continuous_const.prodMk continuous_id
  have h2 : Continuous fun c : Y =>
      fderiv ℝ (fderiv ℝ H) 0 (0, c) (0, c) :=
    ((fderiv ℝ (fderiv ℝ H) 0).continuous.comp h1).clm_apply h1
  have h3 : Continuous fun c : Y => fderiv ℝ (fderiv ℝ H) 0 (v, 0) (0, c) :=
    (fderiv ℝ (fderiv ℝ H) 0 (v, 0)).continuous.comp h1
  exact (continuous_const.add (continuous_const.smul h3)).add h2

/-- Mean-value step: a path vanishing at `0` whose right derivative is bounded by `c sⁿ` on
`[0, τ)` is bounded by `c τⁿ⁺¹` at `τ`. -/
theorem norm_le_of_deriv_bound {f f' : ℝ → R} {τ c : ℝ} {n : ℕ} (hτ : 0 ≤ τ) (hc : 0 ≤ c)
    (hf : ContinuousOn f (Icc 0 τ)) (hf0 : f 0 = 0)
    (hd : ∀ s ∈ Ico 0 τ, HasDerivWithinAt f (f' s) (Ici s) s)
    (hb : ∀ s ∈ Ico 0 τ, ‖f' s‖ ≤ c * s ^ n) : ‖f τ‖ ≤ c * τ ^ (n + 1) := by
  have hb' : ∀ s ∈ Ico 0 τ, ‖f' s‖ ≤ c * τ ^ n := fun s hs =>
    (hb s hs).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.1 hs.2.le n) hc)
  have := norm_image_sub_le_of_norm_deriv_right_le_segment hf hd hb' τ ⟨hτ, le_rfl⟩
  rw [hf0, sub_zero, sub_zero] at this
  calc ‖f τ‖ ≤ c * τ ^ n * τ := this
    _ = c * τ ^ (n + 1) := by ring

set_option maxHeartbeats 1600000 in
/-- **`thm:supp-exact-slope-gate`.** -/
theorem slope_gate (F : R × Y → R) (H : R × Y → Ho) (hF : ContDiffAt ℝ 2 F 0)
    (hH : ContDiffAt ℝ 3 H 0) (hH0 : H 0 = 0) (hFy : ∀ c, fderiv ℝ F 0 (0, c) = 0)
    (hHy : ∀ c, fderiv ℝ H 0 (0, c) = 0) {T : ℝ} {K : ℝ≥0} (hT : 0 < T) (r : ℝ → R) (y : ℝ → Y)
    (hr0 : r 0 = 0) (hy0 : y 0 = 0) (hrL : LipschitzOnWith K r (Icc 0 T))
    (hyL : LipschitzOnWith K y (Icc 0 T))
    (hode : ∀ τ ∈ Ico 0 T, HasDerivWithinAt r (F (r τ, y τ)) (Ici τ) τ)
    (hcon : ∀ τ ∈ Icc 0 T, H (r τ, y τ) = 0) :
    fderiv ℝ H 0 (F 0, 0) = 0 ∧
      (fun τ => r τ - τ • F 0 - τ ^ 2 • ((1 / 2 : ℝ) • fderiv ℝ F 0 (F 0, 0))) =O[𝓝[>] 0]
        (fun τ => τ ^ 3) ∧
      (fun τ => slopePolynomial F H (F 0) (τ⁻¹ • y τ)) =O[𝓝[>] 0] (fun τ => τ) ∧
      ∀ k, MapClusterPt k (𝓝[>] 0) (fun τ => τ⁻¹ • y τ) → slopePolynomial F H (F 0) k = 0 := by
  have hsymm : IsSymmSndFDerivAt ℝ H 0 := hH.isSymmSndFDerivAt (by simp; norm_num)
  -- notation (opaque constants)
  obtain ⟨v, hv⟩ : ∃ v, v = F 0 := ⟨_, rfl⟩
  obtain ⟨Fr, hFr⟩ : ∃ Fr : R →L[ℝ] R, Fr = (fderiv ℝ F 0).comp (ContinuousLinearMap.inl ℝ R Y) :=
    ⟨_, rfl⟩
  obtain ⟨Hr, hHr⟩ : ∃ Hr : R →L[ℝ] Ho, Hr = (fderiv ℝ H 0).comp (ContinuousLinearMap.inl ℝ R Y) :=
    ⟨_, rfl⟩
  obtain ⟨u0, hu0⟩ : ∃ u0 : R, u0 = (1 / 2 : ℝ) • Fr v := ⟨_, rfl⟩
  have hDFq : ∀ a : R, ∀ b : Y, fderiv ℝ F 0 (a, b) = Fr a := by
    intro a b
    have : ((a, b) : R × Y) = (a, 0) + (0, b) := by simp
    rw [this, map_add, hFy, add_zero, hFr]; rfl
  have hDHq : ∀ a : R, ∀ b : Y, fderiv ℝ H 0 (a, b) = Hr a := by
    intro a b
    have : ((a, b) : R × Y) = (a, 0) + (0, b) := by simp
    rw [this, map_add, hHy, add_zero, hHr]; rfl
  set B2 := fderiv ℝ (fderiv ℝ H) 0 with hB2
  have hB2n : 0 ≤ ‖B2‖ := ContinuousLinearMap.opNorm_nonneg _
  -- Lipschitz bounds from the origin
  have hbd : ∀ τ ∈ Icc 0 T, ‖r τ‖ ≤ K * τ ∧ ‖y τ‖ ≤ K * τ := by
    intro τ hτ
    have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
    have e1 := lipschitzOnWith_iff_dist_le_mul.mp hrL τ hτ 0 h0
    have e2 := lipschitzOnWith_iff_dist_le_mul.mp hyL τ hτ 0 h0
    rw [hr0, dist_zero_right, Real.dist_eq, sub_zero, abs_of_nonneg hτ.1] at e1
    rw [hy0, dist_zero_right, Real.dist_eq, sub_zero, abs_of_nonneg hτ.1] at e2
    exact ⟨e1, e2⟩
  have hqbd : ∀ τ ∈ Icc 0 T, ‖((r τ, y τ) : R × Y)‖ ≤ K * τ := fun τ hτ =>
    (norm_prod_le_iff).mpr (hbd τ hτ)
  -- Taylor constants
  obtain ⟨C1, δ1, hC1, hδ1, hTF⟩ := exists_ball_bound (taylor_two hF)
  obtain ⟨C2, δ2, hC2, hδ2, hTH⟩ := exists_ball_bound (taylor_three hH)
  -- a common small time
  obtain ⟨τ0, hτ0pos, hτ0T, hKτ⟩ : ∃ τ0 : ℝ, 0 < τ0 ∧ τ0 < T ∧
      ∀ τ, 0 ≤ τ → τ ≤ τ0 → (K : ℝ) * τ < min δ1 δ2 := by
    refine ⟨min (T / 2) (min δ1 δ2 / (K + 1)),
      lt_min (by linarith) (div_pos (lt_min hδ1 hδ2) (by positivity)),
      lt_of_le_of_lt (min_le_left _ _) (by linarith), fun τ h0 h1 => ?_⟩
    have h2 : τ ≤ min δ1 δ2 / (K + 1) := h1.trans (min_le_right _ _)
    have h3 : (K : ℝ) * τ ≤ K * (min δ1 δ2 / (K + 1)) := mul_le_mul_of_nonneg_left h2 K.2
    have hm : 0 < min δ1 δ2 := lt_min hδ1 hδ2
    have h4 : (K : ℝ) * (min δ1 δ2 / (K + 1)) < min δ1 δ2 := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      have : (K : ℝ) * min δ1 δ2 < min δ1 δ2 * (K + 1) := by
        have := mul_lt_mul_of_pos_left (lt_add_one (K : ℝ)) hm
        linarith [mul_comm (K : ℝ) (min δ1 δ2)]
      exact this
    linarith
  have hIcc : ∀ τ, 0 ≤ τ → τ ≤ τ0 → τ ∈ Icc 0 T := fun τ h0 h1 => ⟨h0, h1.trans hτ0T.le⟩
  have hIco : ∀ τ, 0 ≤ τ → τ ≤ τ0 → τ ∈ Ico 0 T := fun τ h0 h1 => ⟨h0, lt_of_le_of_lt h1 hτ0T⟩
  have hq1 : ∀ τ, 0 ≤ τ → τ ≤ τ0 → ‖((r τ, y τ) : R × Y)‖ < δ1 := fun τ h0 h1 =>
    lt_of_lt_of_le (lt_of_le_of_lt (hqbd τ (hIcc τ h0 h1)) (hKτ τ h0 h1)) (min_le_left _ _)
  have hq2 : ∀ τ, 0 ≤ τ → τ ≤ τ0 → ‖((r τ, y τ) : R × Y)‖ < δ2 := fun τ h0 h1 =>
    lt_of_lt_of_le (lt_of_le_of_lt (hqbd τ (hIcc τ h0 h1)) (hKτ τ h0 h1)) (min_le_right _ _)
  have hrc : ∀ τ, τ ≤ τ0 → ContinuousOn r (Icc 0 τ) := fun τ h1 =>
    hrL.continuousOn.mono (Icc_subset_Icc le_rfl (h1.trans hτ0T.le))
  -- Taylor of `F` along the solution
  have hFt : ∀ τ, 0 ≤ τ → τ ≤ τ0 → ‖F (r τ, y τ) - v - Fr (r τ)‖ ≤ (C1 * K ^ 2) * τ ^ 2 := by
    intro τ h0 h1
    have h := hTF _ (hq1 τ h0 h1)
    rw [hDFq, ← hv] at h
    refine h.trans ?_
    calc C1 * ‖((r τ, y τ) : R × Y)‖ ^ 2 ≤ C1 * (K * τ) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hqbd τ (hIcc τ h0 h1)) 2) hC1
      _ = (C1 * K ^ 2) * τ ^ 2 := by ring
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hC1K : 0 ≤ C1 * K ^ 2 := mul_nonneg hC1 (sq_nonneg _)
  -- Step A
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ‖Fr‖ * K + C1 * K ^ 2 * τ0 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]; exact add_nonneg (mul_nonneg (norm_nonneg _) hK0) (mul_nonneg hC1K hτ0pos.le)
  have hstepA : ∀ τ, 0 ≤ τ → τ ≤ τ0 → ‖r τ - τ • v‖ ≤ A * τ ^ 2 := by
    intro τ h0 h1
    refine norm_le_of_deriv_bound (f := fun s => r s - s • v)
      (f' := fun s => F (r s, y s) - v) (n := 1) h0 hA0
      ((hrc τ h1).sub (continuous_id.smul continuous_const).continuousOn) (by simp [hr0])
      (fun s hs => ?_) (fun s hs => ?_)
    · have h2 := (hode s (hIco s hs.1 (hs.2.le.trans h1))).sub
        (((hasDerivAt_id s).smul_const v).hasDerivWithinAt (s := Ici s))
      exact h2.congr_deriv (by simp)
    · have hs0 := hs.1
      have hs1 : s ≤ τ0 := hs.2.le.trans h1
      have e1 := hFt s hs0 hs1
      have e2 : ‖Fr (r s)‖ ≤ ‖Fr‖ * (K * s) :=
        (Fr.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hbd s (hIcc s hs0 hs1)).1 (norm_nonneg _))
      have e3 : (C1 * K ^ 2) * s ^ 2 ≤ (C1 * K ^ 2 * τ0) * s :=
        calc (C1 * K ^ 2) * s ^ 2 = (C1 * K ^ 2) * (s * s) := by ring
          _ ≤ (C1 * K ^ 2) * (τ0 * s) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs1 hs0) hC1K
          _ = (C1 * K ^ 2 * τ0) * s := by ring
      calc ‖F (r s, y s) - v‖ ≤ ‖F (r s, y s) - v - Fr (r s)‖ + ‖Fr (r s)‖ := by
            have := norm_add_le (F (r s, y s) - v - Fr (r s)) (Fr (r s)); simpa using this
        _ ≤ (C1 * K ^ 2) * s ^ 2 + ‖Fr‖ * (K * s) := add_le_add e1 e2
        _ ≤ (C1 * K ^ 2 * τ0) * s + ‖Fr‖ * K * s := by
            have : ‖Fr‖ * (K * s) = ‖Fr‖ * K * s := by ring
            linarith
        _ = A * s ^ 1 := by rw [hA]; ring
  -- Step B
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = C1 * K ^ 2 + ‖Fr‖ * A := ⟨_, rfl⟩
  have hBc0 : 0 ≤ Bc := by rw [hBc]; exact add_nonneg hC1K (mul_nonneg (norm_nonneg _) hA0)
  have hstepB : ∀ τ, 0 ≤ τ → τ ≤ τ0 → ‖r τ - τ • v - τ ^ 2 • u0‖ ≤ Bc * τ ^ 3 := by
    intro τ h0 h1
    refine norm_le_of_deriv_bound (f := fun s => r s - s • v - s ^ 2 • u0)
      (f' := fun s => F (r s, y s) - v - s • Fr v) (n := 2) h0 hBc0
      (((hrc τ h1).sub (continuous_id.smul continuous_const).continuousOn).sub
        ((continuous_pow 2).smul continuous_const).continuousOn) (by simp [hr0])
      (fun s hs => ?_) (fun s hs => ?_)
    · have h2 : HasDerivAt (fun s : ℝ => s ^ 2 • u0) (s • Fr v) s := by
        have := (hasDerivAt_pow 2 s).smul_const u0
        convert this using 1
        rw [hu0, smul_smul]
        congr 1; push_cast; ring
      have h3 := ((hode s (hIco s hs.1 (hs.2.le.trans h1))).sub
        (((hasDerivAt_id s).smul_const v).hasDerivWithinAt (s := Ici s))).sub
        (h2.hasDerivWithinAt (s := Ici s))
      exact h3.congr_deriv (by simp)
    · have hs0 := hs.1
      have hs1 : s ≤ τ0 := hs.2.le.trans h1
      have e1 := hFt s hs0 hs1
      have e2 : ‖Fr (r s - s • v)‖ ≤ ‖Fr‖ * (A * s ^ 2) :=
        (Fr.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hstepA s hs0 hs1) (norm_nonneg _))
      have hsplit : F (r s, y s) - v - s • Fr v =
          (F (r s, y s) - v - Fr (r s)) + Fr (r s - s • v) := by
        rw [map_sub, map_smul]; abel
      rw [hsplit]
      calc ‖(F (r s, y s) - v - Fr (r s)) + Fr (r s - s • v)‖
          ≤ (C1 * K ^ 2) * s ^ 2 + ‖Fr‖ * (A * s ^ 2) := (norm_add_le _ _).trans (add_le_add e1 e2)
        _ = Bc * s ^ 2 := by rw [hBc]; ring
  -- Step C: the constraint expansion
  obtain ⟨M0, hM0⟩ : ∃ M0 : ℝ, M0 = max ‖v‖ K := ⟨_, rfl⟩
  have hM00 : 0 ≤ M0 := by rw [hM0]; exact le_max_of_le_right hK0
  let P : ℝ → Ho := fun τ => Hr u0 + (1 / 2 : ℝ) • B2 (v, τ⁻¹ • y τ) (v, τ⁻¹ • y τ)
  obtain ⟨Mc, hMc⟩ : ∃ Mc : ℝ, Mc = ‖Hr‖ * Bc + (1 / 2 : ℝ) * ‖B2‖ * A * (K + M0) + C2 * K ^ 3 :=
    ⟨_, rfl⟩
  have hMc0 : 0 ≤ Mc := by
    rw [hMc]
    refine add_nonneg (add_nonneg (mul_nonneg (norm_nonneg _) hBc0) ?_) (mul_nonneg hC2 (pow_nonneg hK0 3))
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB2n) hA0) (add_nonneg hK0 hM00)
  have hkbd : ∀ τ, 0 < τ → τ ≤ τ0 → ‖τ⁻¹ • y τ‖ ≤ K := by
    intro τ h0 h1
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos h0, inv_mul_le_iff₀ h0, mul_comm]
    exact (hbd τ (hIcc τ h0.le h1)).2
  have hexp : ∀ τ, 0 < τ → τ ≤ τ0 → ‖τ • Hr v + τ ^ 2 • P τ‖ ≤ Mc * τ ^ 3 := by
    intro τ h0 h1
    obtain ⟨q, hq⟩ : ∃ q : R × Y, q = (r τ, y τ) := ⟨_, rfl⟩
    obtain ⟨q', hq'⟩ : ∃ q' : R × Y, q' = (τ • v, y τ) := ⟨_, rfl⟩
    have hq'eq : q' = τ • ((v, τ⁻¹ • y τ) : R × Y) := by
      rw [hq']; simp [smul_smul, mul_inv_cancel₀ (ne_of_gt h0)]
    have hTay := hTH q (by rw [hq]; exact hq2 τ h0.le h1)
    have hHq : H q = 0 := by rw [hq]; exact hcon τ (hIcc τ h0.le h1)
    rw [hH0, hHq, sub_zero, zero_sub] at hTay
    have hDq : fderiv ℝ H 0 q = Hr (r τ) := by rw [hq]; exact hDHq _ _
    have hr_split : Hr (r τ) = τ • Hr v + τ ^ 2 • Hr u0 + Hr (r τ - τ • v - τ ^ 2 • u0) := by
      rw [map_sub, map_sub, map_smul, map_smul]; abel
    have hB_split : sndDeriv H 0 q q = sndDeriv H 0 q' q' +
        (B2 (q - q') q + B2 q' (q - q')) := by
      simp only [sndDeriv, ← hB2, map_sub, sub_apply]
      abel
    have hB' : sndDeriv H 0 q' q' = τ ^ 2 • B2 (v, τ⁻¹ • y τ) (v, τ⁻¹ • y τ) := by
      rw [hq'eq]
      simp only [sndDeriv, ← hB2, map_smul, smul_apply, smul_smul, sq]
    have hid : τ • Hr v + τ ^ 2 • P τ =
        -(-fderiv ℝ H 0 q - (1 / 2 : ℝ) • sndDeriv H 0 q q) - Hr (r τ - τ • v - τ ^ 2 • u0) -
          (1 / 2 : ℝ) • (B2 (q - q') q + B2 q' (q - q')) := by
      rw [hDq, hr_split, hB_split, hB']
      simp only [P, smul_add, smul_smul, mul_comm (τ ^ 2) (1 / 2 : ℝ)]
      abel
    rw [hid]
    have hqq' : ‖q - q'‖ ≤ A * τ ^ 2 := by
      have : q - q' = (r τ - τ • v, 0) := by rw [hq, hq']; simp
      rw [this, Prod.norm_def, norm_zero]
      exact max_le (hstepA τ h0.le h1) (mul_nonneg hA0 (sq_nonneg _))
    have hqn : ‖q‖ ≤ K * τ := by rw [hq]; exact hqbd τ (hIcc τ h0.le h1)
    have hq'n : ‖q'‖ ≤ M0 * τ := by
      rw [hq', Prod.norm_def]
      refine max_le ?_ ?_
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos h0, mul_comm, hM0]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) h0.le
      · rw [hM0]
        exact (hbd τ (hIcc τ h0.le h1)).2.trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) h0.le)
    have t1 : ‖-(-fderiv ℝ H 0 q - (1 / 2 : ℝ) • sndDeriv H 0 q q)‖ ≤ C2 * K ^ 3 * τ ^ 3 := by
      rw [norm_neg]
      refine hTay.trans ?_
      calc C2 * ‖q‖ ^ 3 ≤ C2 * (K * τ) ^ 3 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hqn 3) hC2
        _ = C2 * K ^ 3 * τ ^ 3 := by ring
    have t2 : ‖Hr (r τ - τ • v - τ ^ 2 • u0)‖ ≤ ‖Hr‖ * Bc * τ ^ 3 := by
      refine (Hr.le_opNorm _).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hstepB τ h0.le h1) (norm_nonneg _)
    have t3 : ‖(1 / 2 : ℝ) • (B2 (q - q') q + B2 q' (q - q'))‖ ≤
        (1 / 2 : ℝ) * ‖B2‖ * A * (K + M0) * τ ^ 3 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have b1 : ‖B2 (q - q') q‖ ≤ ‖B2‖ * ‖q - q'‖ * ‖q‖ := B2.le_opNorm₂ _ _
      have b2 : ‖B2 q' (q - q')‖ ≤ ‖B2‖ * ‖q'‖ * ‖q - q'‖ := B2.le_opNorm₂ _ _
      have hsum : ‖q‖ + ‖q'‖ ≤ (K + M0) * τ := by rw [add_mul]; exact add_le_add hqn hq'n
      calc (1 / 2 : ℝ) * ‖B2 (q - q') q + B2 q' (q - q')‖
          ≤ (1 / 2 : ℝ) * (‖B2‖ * ‖q - q'‖ * ‖q‖ + ‖B2‖ * ‖q'‖ * ‖q - q'‖) :=
            mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add b1 b2)) (by norm_num)
        _ = (1 / 2 : ℝ) * ‖B2‖ * ‖q - q'‖ * (‖q‖ + ‖q'‖) := by ring
        _ ≤ (1 / 2 : ℝ) * ‖B2‖ * (A * τ ^ 2) * ((K + M0) * τ) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hqq' (mul_nonneg (by norm_num) hB2n)) hsum
              (add_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg (mul_nonneg (by norm_num) hB2n)
                (mul_nonneg hA0 (sq_nonneg _)))
        _ = (1 / 2 : ℝ) * ‖B2‖ * A * (K + M0) * τ ^ 3 := by ring
    calc ‖-(-fderiv ℝ H 0 q - (1 / 2 : ℝ) • sndDeriv H 0 q q) - Hr (r τ - τ • v - τ ^ 2 • u0) -
          (1 / 2 : ℝ) • (B2 (q - q') q + B2 q' (q - q'))‖
        ≤ ‖-(-fderiv ℝ H 0 q - (1 / 2 : ℝ) • sndDeriv H 0 q q)‖ +
            ‖Hr (r τ - τ • v - τ ^ 2 • u0)‖ +
          ‖(1 / 2 : ℝ) • (B2 (q - q') q + B2 q' (q - q'))‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ C2 * K ^ 3 * τ ^ 3 + ‖Hr‖ * Bc * τ ^ 3 +
          (1 / 2 : ℝ) * ‖B2‖ * A * (K + M0) * τ ^ 3 := add_le_add (add_le_add t1 t2) t3
      _ = Mc * τ ^ 3 := by rw [hMc]; ring
  -- bound on `P`
  obtain ⟨Pb, hPbdef⟩ : ∃ Pb : ℝ, Pb = ‖Hr‖ * ‖u0‖ + (1 / 2 : ℝ) * (‖B2‖ * M0 * M0) := ⟨_, rfl⟩
  have hPb0 : 0 ≤ Pb := by
    rw [hPbdef]
    exact add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hB2n hM00) hM00))
  have hPb : ∀ τ, 0 < τ → τ ≤ τ0 → ‖P τ‖ ≤ Pb := by
    intro τ h0 h1
    have hk : ‖((v, τ⁻¹ • y τ) : R × Y)‖ ≤ M0 := by
      rw [Prod.norm_def, hM0]
      exact max_le (le_max_left _ _) ((hkbd τ h0 h1).trans (le_max_right _ _))
    have b1 := B2.le_opNorm₂ (v, τ⁻¹ • y τ) (v, τ⁻¹ • y τ)
    have b2 : ‖B2‖ * ‖((v, τ⁻¹ • y τ) : R × Y)‖ * ‖((v, τ⁻¹ • y τ) : R × Y)‖ ≤ ‖B2‖ * M0 * M0 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hk hB2n) hk (norm_nonneg _)
        (mul_nonneg hB2n hM00)
    calc ‖P τ‖ ≤ ‖Hr u0‖ + ‖(1 / 2 : ℝ) • B2 (v, τ⁻¹ • y τ) (v, τ⁻¹ • y τ)‖ := norm_add_le _ _
      _ ≤ ‖Hr‖ * ‖u0‖ + (1 / 2 : ℝ) * (‖B2‖ * M0 * M0) := by
          refine add_le_add (Hr.le_opNorm _) ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact mul_le_mul_of_nonneg_left (b1.trans b2) (by norm_num)
      _ = Pb := hPbdef.symm
  -- `ρ₀ = 0`
  have hρ : Hr v = 0 := by
    by_contra hne
    have hpos : 0 < ‖Hr v‖ := norm_pos_iff.mpr hne
    set S : ℝ := Pb + Mc * τ0 with hS
    have hS0 : 0 ≤ S := add_nonneg hPb0 (mul_nonneg hMc0 hτ0pos.le)
    have hden : 0 < 2 * (S + 1) := by linarith
    obtain ⟨τ, hτpos, hτ1, hτ2⟩ : ∃ τ : ℝ, 0 < τ ∧ τ ≤ τ0 ∧ τ ≤ ‖Hr v‖ / (2 * (S + 1)) :=
      ⟨min τ0 (‖Hr v‖ / (2 * (S + 1))), lt_min hτ0pos (div_pos hpos hden), min_le_left _ _,
        min_le_right _ _⟩
    have h := hexp τ hτpos hτ1
    have hP := hPb τ hτpos hτ1
    have h2 : τ * ‖Hr v‖ ≤ Mc * τ ^ 3 + τ ^ 2 * Pb := by
      have e : τ • Hr v = (τ • Hr v + τ ^ 2 • P τ) - τ ^ 2 • P τ := by abel
      have h5 := norm_sub_le (τ • Hr v + τ ^ 2 • P τ) (τ ^ 2 • P τ)
      rw [← e, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hτpos,
        abs_of_pos (pow_pos hτpos 2)] at h5
      exact h5.trans (add_le_add h (mul_le_mul_of_nonneg_left hP (sq_nonneg _)))
    have h3 : ‖Hr v‖ ≤ τ * S := by
      have h6 : τ * ‖Hr v‖ ≤ τ * (τ * S) := by
        have : Mc * τ ^ 3 ≤ τ * (τ * (Mc * τ0)) := by
          have := mul_le_mul_of_nonneg_left hτ1 (mul_nonneg hMc0 (sq_nonneg τ))
          calc Mc * τ ^ 3 = Mc * τ ^ 2 * τ := by ring
            _ ≤ Mc * τ ^ 2 * τ0 := this
            _ = τ * (τ * (Mc * τ0)) := by ring
        calc τ * ‖Hr v‖ ≤ Mc * τ ^ 3 + τ ^ 2 * Pb := h2
          _ ≤ τ * (τ * (Mc * τ0)) + τ ^ 2 * Pb := by linarith
          _ = τ * (τ * S) := by rw [hS]; ring
      exact le_of_mul_le_mul_left h6 hτpos
    have h4 : τ * S < ‖Hr v‖ := by
      calc τ * S ≤ ‖Hr v‖ / (2 * (S + 1)) * S := mul_le_mul_of_nonneg_right hτ2 hS0
        _ < ‖Hr v‖ := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
            have : ‖Hr v‖ * S < ‖Hr v‖ * (2 * (S + 1)) :=
              mul_lt_mul_of_pos_left (by linarith) hpos
            exact this
    linarith
  -- the slope polynomial is `2 P`
  have hQP : ∀ τ : ℝ, slopePolynomial F H v (τ⁻¹ • y τ) = (2 : ℝ) • P τ := by
    intro τ
    rw [slopePolynomial_eq F H hsymm]
    have e1 : (2 : ℝ) • Hr u0 = fderiv ℝ H 0 (fderiv ℝ F 0 (v, 0), 0) := by
      rw [hu0, map_smul, smul_smul, hDHq, hDFq]; norm_num
    simp only [P, smul_add, smul_smul, e1, sndDeriv, ← hB2]
    norm_num
  have hQbd : ∀ τ, 0 < τ → τ ≤ τ0 → ‖slopePolynomial F H v (τ⁻¹ • y τ)‖ ≤ 2 * Mc * τ := by
    intro τ h0 h1
    have h := hexp τ h0 h1
    rw [hρ, smul_zero, zero_add, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos h0 2)] at h
    rw [hQP τ, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h7 : τ ^ 2 * ‖P τ‖ ≤ τ ^ 2 * (Mc * τ) := by
      calc τ ^ 2 * ‖P τ‖ ≤ Mc * τ ^ 3 := h
        _ = τ ^ 2 * (Mc * τ) := by ring
    have := le_of_mul_le_mul_left h7 (pow_pos h0 2)
    linarith
  have hevτ : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 0 < τ ∧ τ ≤ τ0 :=
    Filter.mem_of_superset (Ioc_mem_nhdsGT hτ0pos) fun τ hτ => ⟨hτ.1, hτ.2⟩
  have hO : (fun τ => slopePolynomial F H v (τ⁻¹ • y τ)) =O[𝓝[>] 0] (fun τ => τ) := by
    refine IsBigO.of_bound (2 * Mc) ?_
    filter_upwards [hevτ] with τ hτ
    rw [Real.norm_eq_abs, abs_of_pos hτ.1]
    exact hQbd τ hτ.1 hτ.2
  subst hv
  refine ⟨?_, ?_, hO, ?_⟩
  · have := hρ
    rw [hHr] at this
    simpa using this
  · refine IsBigO.of_bound Bc ?_
    filter_upwards [hevτ] with τ hτ
    have := hstepB τ hτ.1.le hτ.2
    rw [Real.norm_eq_abs, abs_of_pos (pow_pos hτ.1 3)]
    rw [hu0, hFr] at this
    simpa using this
  · intro k hk
    have hlim : Tendsto (fun τ => slopePolynomial F H (F 0) (τ⁻¹ • y τ)) (𝓝[>] 0) (𝓝 0) :=
      hO.trans_tendsto (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto' 0 0 rfl))
    have hc := hk.continuousAt_comp ((continuous_slopePolynomial F H (F 0)).continuousAt (x := k))
    by_contra hne
    obtain ⟨U, V, hUo, hVo, hkU, h0V, hUV⟩ := t2_separation hne
    have h1 : ∀ᶠ τ in 𝓝[>] (0 : ℝ), slopePolynomial F H (F 0) (τ⁻¹ • y τ) ∈ V :=
      hlim (hVo.mem_nhds h0V)
    have h2 := (mapClusterPt_iff_frequently.mp hc) U (hUo.mem_nhds hkU)
    obtain ⟨τ, hτU, hτV⟩ := (h2.and_eventually h1).exists
    exact Set.disjoint_left.mp hUV hτU hτV

/-- **No-trajectory clause of `thm:supp-exact-slope-gate`.**  In a proper slope space (e.g.
`Y = ℝ³`), the slope polynomial has a real zero in the admissible slope ball `‖c‖ ≤ K`; hence if
that ball contains no real zero, no Lipschitz trajectory of the reduced system starts at
`(0, 0)`. -/
theorem slope_gate_exists_root [ProperSpace Y] (F : R × Y → R) (H : R × Y → Ho)
    (hF : ContDiffAt ℝ 2 F 0) (hH : ContDiffAt ℝ 3 H 0) (hH0 : H 0 = 0)
    (hFy : ∀ c, fderiv ℝ F 0 (0, c) = 0) (hHy : ∀ c, fderiv ℝ H 0 (0, c) = 0) {T : ℝ} {K : ℝ≥0}
    (hT : 0 < T) (r : ℝ → R) (y : ℝ → Y) (hr0 : r 0 = 0) (hy0 : y 0 = 0)
    (hrL : LipschitzOnWith K r (Icc 0 T)) (hyL : LipschitzOnWith K y (Icc 0 T))
    (hode : ∀ τ ∈ Ico 0 T, HasDerivWithinAt r (F (r τ, y τ)) (Ici τ) τ)
    (hcon : ∀ τ ∈ Icc 0 T, H (r τ, y τ) = 0) :
    ∃ k ∈ Metric.closedBall (0 : Y) K, slopePolynomial F H (F 0) k = 0 := by
  have hmem : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ⁻¹ • y τ ∈ Metric.closedBall (0 : Y) K := by
    filter_upwards [Ioo_mem_nhdsGT hT] with τ hτ
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos hτ.1, inv_mul_le_iff₀ hτ.1, mul_comm]
    have := lipschitzOnWith_iff_dist_le_mul.mp hyL τ ⟨hτ.1.le, hτ.2.le⟩ 0 ⟨le_rfl, hT.le⟩
    rwa [hy0, dist_zero_right, Real.dist_eq, sub_zero, abs_of_pos hτ.1] at this
  obtain ⟨k, hk, hcl⟩ := (isCompact_closedBall (0 : Y) K).exists_mapClusterPt
    (tendsto_principal.mpr hmem)
  exact ⟨k, hk, (slope_gate F H hF hH hH0 hFy hHy hT r y hr0 hy0 hrL hyL hode hcon).2.2.2 k hcl⟩

/-- Contrapositive form: if the admissible slope ball contains no real zero of `𝒬`, no such
Lipschitz trajectory exists. -/
theorem slope_gate_no_trajectory [ProperSpace Y] (F : R × Y → R) (H : R × Y → Ho)
    (hF : ContDiffAt ℝ 2 F 0) (hH : ContDiffAt ℝ 3 H 0) (hH0 : H 0 = 0)
    (hFy : ∀ c, fderiv ℝ F 0 (0, c) = 0) (hHy : ∀ c, fderiv ℝ H 0 (0, c) = 0) {T : ℝ} {K : ℝ≥0}
    (hT : 0 < T) (hnoroot : ∀ k ∈ Metric.closedBall (0 : Y) K, slopePolynomial F H (F 0) k ≠ 0)
    (r : ℝ → R) (y : ℝ → Y) (hr0 : r 0 = 0) (hy0 : y 0 = 0)
    (hrL : LipschitzOnWith K r (Icc 0 T)) (hyL : LipschitzOnWith K y (Icc 0 T))
    (hode : ∀ τ ∈ Ico 0 T, HasDerivWithinAt r (F (r τ, y τ)) (Ici τ) τ) :
    ¬ ∀ τ ∈ Icc 0 T, H (r τ, y τ) = 0 := by
  intro hcon
  obtain ⟨k, hk, h0⟩ := slope_gate_exists_root F H hF hH hH0 hFy hHy hT r y hr0 hy0 hrL hyL hode
    hcon
  exact hnoroot k hk h0

/-- Non-vacuity of the hypothesis packet of `slope_gate` (trivial reduced system on `ℝ × ℝ`). -/
example : fderiv ℝ (fun _ : ℝ × ℝ => (0 : ℝ)) 0 ((fun _ : ℝ × ℝ => (0 : ℝ)) 0, 0) = 0 :=
  (slope_gate (fun _ : ℝ × ℝ => (0 : ℝ)) (fun _ : ℝ × ℝ => (0 : ℝ)) contDiffAt_const
    contDiffAt_const rfl (fun _ => by simp) (fun _ => by simp) (T := 1) (K := 0) one_pos
    (fun _ => 0) (fun _ => 0) rfl rfl (LipschitzWith.const 0).lipschitzOnWith
    (LipschitzWith.const 0).lipschitzOnWith (fun _ _ => by simpa using hasDerivWithinAt_const _ _ _)
    (fun _ _ => rfl)).1

end Gate

end ExactSlopeGate
end RenewalGeometry

end
