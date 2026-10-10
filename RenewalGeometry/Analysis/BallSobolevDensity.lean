/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallNeumannHk

/-!
# Density of smooth functions in `H^k(B)` on a ball (dilation and mollification)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript (stage C4b/C5b of the ball rendering of
Uhlenbeck's small-energy gauge theorem).

* `dil c t x = c + t (x - c)` (dilation about the centre): `sqDist_dil`, `preimage_dil_ball`,
  `integral_comp_dil` (`∫ F(dil x) dx = t^{-n} ∫ F`), `eLpNorm_comp_dil`;
* `tendsto_eLpNorm_comp_dil_sub` — **continuity of dilations in `L²(ℝⁿ)`**;
* `HasWeakPartialR.comp_dil` — weak derivatives of `u ∘ dil c t` on the larger ball `B_{r/t}`;
* `pd_smoothApprox` — derivatives of the dilated mollifications are the dilated mollifications of
  the weak derivatives (on the ball);
* `memHk_iff_convHk` / `convHk_of_memHk` (**density**): every `u ∈ H^k(B_r(c))` (weak derivatives)
  is the `H^k(B)` limit of the explicit smooth functions
  `smoothApprox c r m u = ρ_{ε_m} ⋆ ((1_B u) ∘ dil c t_m)` (`t_m ↑ 1`, `ε_m ↓ 0`).
  Consequently `neumann_Hk_weak`: the Neumann solution of data in `H^k(B)` lies in `H^{k+2}(B)`.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Convolution

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallReg

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-! ### Dilations about the centre -/

section Dil

variable (c : Fin n → ℝ)

/-- The dilation `x ↦ c + t (x - c)`. -/
def dil (t : ℝ) (x : Fin n → ℝ) : Fin n → ℝ := c + t • (x - c)

theorem dil_eq_affine (t : ℝ) : dil c t = fun x => (c - t • c) + t • x := by
  funext x; simp only [dil, smul_sub]; abel

theorem sqDist_dil (t : ℝ) (x : Fin n → ℝ) : sqDist c (dil c t x) = t ^ 2 * sqDist c x := by
  simp only [sqDist, dil, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    add_sub_cancel_left, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dil_dil_inv {t : ℝ} (ht : t ≠ 0) (x : Fin n → ℝ) : dil c t (dil c t⁻¹ x) = x := by
  simp only [dil, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ ht, one_smul]; abel

theorem dil_inv_dil {t : ℝ} (ht : t ≠ 0) (x : Fin n → ℝ) : dil c t⁻¹ (dil c t x) = x := by
  simp only [dil, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]; abel

theorem preimage_dil_ball {t : ℝ} (ht : 0 < t) (r : ℝ) (hr : 0 ≤ r) :
    dil c t ⁻¹' euclBall c r = euclBall c (r / t) := by
  ext x
  simp only [mem_preimage, euclBall, mem_setOf_eq, sqDist_dil]
  rw [div_pow, lt_div_iff₀ (by positivity), mul_comm]

theorem contDiff_dil (t : ℝ) : ContDiff ℝ ∞ (dil c t) := by
  rw [dil_eq_affine]; exact contDiff_const.add (contDiff_id.const_smul t)

theorem continuous_dil (t : ℝ) : Continuous (dil c t) := (contDiff_dil c t).continuous

/-- The dilation as a homeomorphism (`t ≠ 0`). -/
def dilHomeo {t : ℝ} (ht : t ≠ 0) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) where
  toFun := dil c t
  invFun := dil c t⁻¹
  left_inv := dil_inv_dil c ht
  right_inv := dil_dil_inv c ht
  continuous_toFun := continuous_dil c t
  continuous_invFun := continuous_dil c t⁻¹

/-- Change of variables: `∫ F(c + t(x - c)) dx = t^{-n} ∫ F`. -/
theorem integral_comp_dil {t : ℝ} (ht : 0 < t) (F : (Fin n → ℝ) → ℝ) :
    ∫ x, F (dil c t x) = (t ^ n)⁻¹ * ∫ y, F y := by
  rw [dil_eq_affine]
  have := integral_comp_affine F (c - t • c) ht
  simp only [Fintype.card_fin, smul_eq_mul] at this
  exact this

theorem measurePreserving_dil {t : ℝ} (ht : 0 < t) :
    MeasurePreserving (dil c t) volume (ENNReal.ofReal ((t ^ n)⁻¹) • volume) := by
  rw [dil_eq_affine]
  have := measurePreserving_affine (ι := Fin n) (c - t • c) ht
  simpa only [Fintype.card_fin] using this

theorem eLpNorm_comp_dil {t : ℝ} (ht : 0 < t) {f : (Fin n → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (f ∘ dil c t) 2 volume =
      ENNReal.ofReal ((t ^ n)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm f 2 volume := by
  rw [eLpNorm_comp_measurePreserving (hf.smul_measure _) (measurePreserving_dil c ht),
    eLpNorm_smul_measure_of_ne_top (by norm_num)]
  rfl

theorem memLp_comp_dil {t : ℝ} (ht : 0 < t) {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 volume) :
    MemLp (f ∘ dil c t) 2 volume :=
  (hf.smul_measure ENNReal.ofReal_ne_top).comp_measurePreserving (measurePreserving_dil c ht)

/-- The `L²` scaling factor of dilations is at most `2^n` (in squared form) for `t ≥ 1/2`. -/
theorem dil_factor_le {t : ℝ} (ht : 1 / 2 ≤ t) :
    ENNReal.ofReal ((t ^ n)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal ≤ ENNReal.ofReal (2 ^ n) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have h1 : (t ^ n)⁻¹ ≤ 2 ^ n := by
    rw [← inv_pow]
    have h3 : t⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ ht0 two_pos]; norm_num; linarith
    exact pow_le_pow_left₀ (by positivity) h3 n
  have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  calc ENNReal.ofReal ((t ^ n)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal
      ≤ ENNReal.ofReal (2 ^ n) ^ (1 / (2 : ℝ≥0∞)).toReal := by
        gcongr
    _ ≤ ENNReal.ofReal (2 ^ n) ^ (1 : ℝ) := by
        apply ENNReal.rpow_le_rpow_of_exponent_le
        · rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h2
        · norm_num
    _ = ENNReal.ofReal (2 ^ n) := ENNReal.rpow_one _

/-- **Continuity of dilations in `L²(ℝⁿ)`**: `f ∘ dil c t_m → f` as `t_m → 1` (`t_m ≥ 1/2`). -/
theorem tendsto_eLpNorm_comp_dil_sub {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 volume)
    {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 1)) (ht2 : ∀ m, 1 / 2 ≤ t m) :
    Tendsto (fun m => eLpNorm (f ∘ dil c (t m) - f) 2 volume) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεt
  · exact Eventually.of_forall fun _ => le_top
  set e : ℝ := ε.toReal
  have he : 0 < e := ENNReal.toReal_pos hε.ne' hεt
  have hεe : ε = ENNReal.ofReal e := (ENNReal.ofReal_toReal hεt).symm
  -- approximate by a continuous compactly supported function
  set η : ℝ := e / 3 / (2 ^ n + 1)
  have hη : 0 < η := by positivity
  obtain ⟨h, hhc, hfh, hcont, hhL⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) (ENNReal.ofReal_pos.mpr hη).ne'
  -- a compact set containing all the supports
  obtain ⟨R, hR⟩ := hhc.isCompact.isBounded.subset_closedBall c
  set R' : ℝ := max R 0
  have hR' : tsupport h ⊆ closedBall c R' := hR.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hR'0 : 0 ≤ R' := le_max_right _ _
  set K := closedBall c (2 * R')
  have hKc : IsCompact K := isCompact_closedBall c (2 * R')
  have hdist : ∀ (s : ℝ) (x : Fin n → ℝ), 0 ≤ s → dist (dil c s x) c = s * dist x c := by
    intro s x hs
    simp only [dil, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  have hsupp : ∀ m, Function.support (h ∘ dil c (t m) - h) ⊆ K := by
    intro m x hx
    have htm0 : 0 < t m := lt_of_lt_of_le (by norm_num) (ht2 m)
    by_contra hxK
    apply hx
    simp only [Pi.sub_apply, Function.comp_apply]
    have hxR : 2 * R' < dist x c := by
      simp only [K, mem_closedBall, not_le] at hxK; exact hxK
    have h1 : h x = 0 := image_eq_zero_of_notMem_tsupport fun hx' => by
      have := mem_closedBall.mp (hR' hx'); linarith
    have h2 : h (dil c (t m) x) = 0 := image_eq_zero_of_notMem_tsupport fun hx' => by
      have hd := mem_closedBall.mp (hR' hx')
      rw [hdist _ _ htm0.le] at hd
      nlinarith [ht2 m]
    rw [h1, h2, sub_zero]
  -- uniform continuity of `h`
  have huc := hhc.uniformContinuous_of_continuous hcont
  have hVK : volume K < ⊤ := hKc.measure_lt_top
  set VK : ℝ := (volume K ^ (1 / (2 : ℝ≥0∞)).toReal).toReal
  set δ0 : ℝ := e / 3 / (VK + 1)
  have hδ0 : 0 < δ0 := by positivity
  obtain ⟨δ1, hδ1, hδ1h⟩ := Metric.uniformContinuous_iff.mp huc δ0 hδ0
  have hlim : Tendsto (fun m => |1 - t m| * (2 * R')) atTop (𝓝 0) := by
    have : Tendsto (fun m => |1 - t m|) atTop (𝓝 0) := by
      have h0 : Tendsto (fun m => 1 - t m) atTop (𝓝 0) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).sub ht; simpa using this
      simpa using h0.abs
    simpa using this.mul_const (2 * R')
  filter_upwards [hlim.eventually (gt_mem_nhds hδ1)] with m hm
  have htm0 : 0 < t m := lt_of_lt_of_le (by norm_num) (ht2 m)
  -- the three terms
  have hbound : ∀ x, ‖(h ∘ dil c (t m) - h) x‖ ≤ δ0 := by
    intro x
    by_cases hxK : x ∈ K
    · simp only [Pi.sub_apply, Function.comp_apply, Real.norm_eq_abs]
      have hd : dist (dil c (t m) x) x < δ1 := by
        have : dist (dil c (t m) x) x = |1 - t m| * dist x c := by
          simp only [dil, dist_eq_norm]
          rw [show c + t m • (x - c) - x = (t m - 1) • (x - c) by
            simp only [smul_sub, sub_smul, one_smul]; abel, norm_smul, Real.norm_eq_abs,
            abs_sub_comm]
        rw [this]
        have hxc : dist x c ≤ 2 * R' := mem_closedBall.mp hxK
        calc |1 - t m| * dist x c ≤ |1 - t m| * (2 * R') :=
              mul_le_mul_of_nonneg_left hxc (abs_nonneg _)
          _ < δ1 := hm
      have := hδ1h hd
      rw [Real.dist_eq] at this; exact this.le
    · have : (h ∘ dil c (t m) - h) x = 0 := by
        by_contra h0; exact hxK (hsupp m h0)
      rw [this, norm_zero]; exact hδ0.le
  have hT2 : eLpNorm (h ∘ dil c (t m) - h) 2 volume ≤ ENNReal.ofReal (e / 3) := by
    rw [← eLpNorm_restrict_eq_of_support_subset (hsupp m)]
    refine (eLpNorm_le_of_ae_bound (Eventually.of_forall hbound)).trans ?_
    rw [Measure.restrict_apply_univ]
    have hfin : volume K ^ (2 : ℝ≥0∞).toReal⁻¹ ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVK.ne
    have e1 : volume K ^ (2 : ℝ≥0∞).toReal⁻¹ = ENNReal.ofReal VK := by
      rw [ENNReal.ofReal_toReal (by simpa using hfin)]; congr 1; norm_num
    rw [e1, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hVK0 : 0 ≤ VK := ENNReal.toReal_nonneg
    calc VK * δ0 = VK / (VK + 1) * (e / 3) := by simp only [δ0]; field_simp
      _ ≤ 1 * (e / 3) := by
          gcongr; rw [div_le_one (by positivity)]; linarith
      _ = e / 3 := one_mul _
  have hT1 : eLpNorm ((f - h) ∘ dil c (t m)) 2 volume ≤ ENNReal.ofReal (2 ^ n) * ENNReal.ofReal η := by
    rw [eLpNorm_comp_dil c htm0 (hf.1.sub hhL.1)]
    exact mul_le_mul' (dil_factor_le (ht2 m)) hfh
  have hT3 : eLpNorm (h - f) 2 volume ≤ ENNReal.ofReal η := by rw [eLpNorm_sub_comm]; exact hfh
  have hdec : f ∘ dil c (t m) - f = (f - h) ∘ dil c (t m) + (h ∘ dil c (t m) - h) + (h - f) := by
    funext x; simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply]; ring
  have hm1 : AEStronglyMeasurable ((f - h) ∘ dil c (t m)) volume :=
    (hf.1.sub hhL.1).smul_measure (ENNReal.ofReal ((t m ^ n)⁻¹)) |>.comp_measurePreserving
      (measurePreserving_dil c htm0)
  have hm2 : AEStronglyMeasurable (h ∘ dil c (t m) - h) volume :=
    ((hcont.comp (continuous_dil c (t m))).sub hcont).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (h - f) volume := hhL.1.sub hf.1
  rw [hdec, hεe]
  calc eLpNorm ((f - h) ∘ dil c (t m) + (h ∘ dil c (t m) - h) + (h - f)) 2 volume
      ≤ eLpNorm ((f - h) ∘ dil c (t m)) 2 volume + eLpNorm (h ∘ dil c (t m) - h) 2 volume +
          eLpNorm (h - f) 2 volume := by
        refine (eLpNorm_add_le (hm1.add hm2) hm3 (by norm_num)).trans ?_
        gcongr
        exact eLpNorm_add_le hm1 hm2 (by norm_num)
    _ ≤ ENNReal.ofReal (2 ^ n) * ENNReal.ofReal η + ENNReal.ofReal (e / 3) + ENNReal.ofReal η := by
        gcongr
    _ = ENNReal.ofReal ((2 ^ n + 1) * η + e / 3) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
    _ ≤ ENNReal.ofReal e := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : (2 ^ n + 1) * η = e / 3 := by simp only [η]; field_simp
        rw [this]; linarith

end Dil

/-! ### Weak derivatives of dilations, and the dilated mollifications -/

section DilWeak

variable (c : Fin n → ℝ)

theorem tsupport_comp_dil_inv {t : ℝ} (ht : 0 < t) {φ : (Fin n → ℝ) → ℝ} :
    tsupport (fun y => φ (dil c t⁻¹ y)) = dil c t⁻¹ ⁻¹' tsupport φ := by
  have := tsupport_comp_eq_preimage φ (dilHomeo c (inv_ne_zero ht.ne'))
  exact this

theorem pd_comp_dil {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (s : ℝ) (i : Fin n)
    (y : Fin n → ℝ) : pd (fun y => φ (dil c s y)) i y = s * pd φ i (dil c s y) := by
  have hd : HasFDerivAt (dil c s) (s • ContinuousLinearMap.id ℝ (Fin n → ℝ)) y := by
    rw [dil_eq_affine]
    exact ((hasFDerivAt_id y).const_smul s).const_add _
  have h2 := ((hφ.differentiable one_ne_zero) (dil c s y)).hasFDerivAt.comp y hd
  unfold pd
  rw [show (fun y => φ (dil c s y)) = φ ∘ dil c s from rfl, h2.fderiv]
  simp [smul_eq_mul]

/-- **Weak derivatives of dilations**: if `g = ∂_i u` weakly on `B_r(c)`, then
`∂_i (u ∘ dil c t) = t (g ∘ dil c t)` weakly on `B_{r/t}(c)`. -/
theorem HasWeakPartialR.comp_dil {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) {i : Fin n}
    {u g : (Fin n → ℝ) → ℝ} (h : HasWeakPartialR (euclBall c r) i u g) :
    HasWeakPartialR (euclBall c (r / t)) i (fun x => u (dil c t x))
      (fun x => t * g (dil c t x)) := by
  intro φ hφ
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  set ψ : (Fin n → ℝ) → ℝ := fun y => φ (dil c t⁻¹ y)
  have hψ : IsTest (euclBall c r) ψ := by
    refine ⟨hφ.smooth.comp (contDiff_dil c t⁻¹), ?_, ?_⟩
    · exact hφ.compact.comp_homeomorph (dilHomeo c (inv_ne_zero ht.ne'))
    · rw [tsupport_comp_dil_inv c ht]
      intro y hy
      have h1 := hφ.subset hy
      rw [← preimage_dil_ball c ht r hr, mem_preimage, dil_dil_inv c ht.ne'] at h1
      exact h1
  have hpdψ : ∀ y, pd ψ i y = t⁻¹ * pd φ i (dil c t⁻¹ y) := fun y => pd_comp_dil c hφ1 t⁻¹ i y
  have key := h ψ hψ
  -- change of variables on both sides
  have e1 : ∫ x, pd φ i x * u (dil c t x) = (t ^ n)⁻¹ * (t * ∫ y, pd ψ i y * u y) := by
    calc ∫ x, pd φ i x * u (dil c t x) = ∫ x, t * (pd ψ i (dil c t x) * u (dil c t x)) := by
          congr 1; funext x
          rw [hpdψ, dil_inv_dil c ht.ne']
          field_simp
      _ = (t ^ n)⁻¹ * ∫ y, t * (pd ψ i y * u y) :=
          integral_comp_dil c ht (fun y => t * (pd ψ i y * u y))
      _ = (t ^ n)⁻¹ * (t * ∫ y, pd ψ i y * u y) := by rw [integral_const_mul]
  have e2 : ∫ x, φ x * (t * g (dil c t x)) = (t ^ n)⁻¹ * (t * ∫ y, ψ y * g y) := by
    calc ∫ x, φ x * (t * g (dil c t x)) = ∫ x, t * (ψ (dil c t x) * g (dil c t x)) := by
          congr 1; funext x
          simp only [ψ, dil_inv_dil c ht.ne']
          ring
      _ = (t ^ n)⁻¹ * ∫ y, t * (ψ y * g y) := integral_comp_dil c ht (fun y => t * (ψ y * g y))
      _ = (t ^ n)⁻¹ * (t * ∫ y, ψ y * g y) := by rw [integral_const_mul]
  rw [e1, e2, key]; ring

/-- The scales `t_m = 1 - 1/(m+2) ∈ [1/2, 1)`. -/
def tD (m : ℕ) : ℝ := 1 - 1 / ((m : ℝ) + 2)

theorem tD_pos (m : ℕ) : 0 < tD m := by
  unfold tD
  have : 1 / ((m : ℝ) + 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; have := (Nat.cast_nonneg m : (0:ℝ) ≤ m); linarith
  linarith

theorem half_le_tD (m : ℕ) : 1 / 2 ≤ tD m := by
  unfold tD
  have : 1 / ((m : ℝ) + 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; have := (Nat.cast_nonneg m : (0:ℝ) ≤ m); linarith
  linarith

theorem tD_lt_one (m : ℕ) : tD m < 1 := by
  unfold tD
  have : 0 < 1 / ((m : ℝ) + 2) := by positivity
  linarith

theorem tendsto_tD : Tendsto tD atTop (𝓝 1) := by
  have h : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 2)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    refine this.congr fun m => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  rw [sub_zero] at this
  exact this

variable (r : ℝ) [hr : Fact (0 < r)]

/-- The mollification radii `ε_m = (r/t_m - r)/(n+1) → 0`. -/
def epsD (m : ℕ) : ℝ := (r / tD m - r) / ((n : ℝ) + 1)

theorem epsD_pos (m : ℕ) : 0 < epsD (n := n) r m := by
  have hr0 := hr.out
  have := tD_pos m
  have := tD_lt_one m
  unfold epsD
  apply div_pos _ (by positivity)
  rw [sub_pos, lt_div_iff₀ (tD_pos m)]
  nlinarith

theorem tendsto_epsD : Tendsto (epsD (n := n) r) atTop (𝓝 0) := by
  show Tendsto (fun m => (r / tD m - r) / ((n : ℝ) + 1)) atTop (𝓝 0)
  have h1 : Tendsto (fun m => r / tD m) atTop (𝓝 (r / 1)) :=
    tendsto_const_nhds.div tendsto_tD one_ne_zero
  have h2 := (h1.sub (tendsto_const_nhds (x := r))).div_const ((n : ℝ) + 1)
  simpa [epsD] using h2

/-- The mollifier bumps of radius `ε_m`. -/
def bumpD (m : ℕ) : ContDiffBump (0 : Fin n → ℝ) :=
  ⟨epsD (n := n) r m / 2, epsD (n := n) r m, by have := epsD_pos (n := n) r m; positivity,
    half_lt_self (epsD_pos (n := n) r m)⟩

/-- **The smooth approximants** `ρ_{ε_m} ⋆ ((1_B u) ∘ dil c t_m)`. -/
def smoothApprox (m : ℕ) (u : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  (bumpD (n := n) r m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    (fun x => (euclBall c r).indicator u (dil c (tD m) x))

theorem memLp_indicator_ball {u : (Fin n → ℝ) → ℝ}
    (hu : MemLp u 2 (volume.restrict (euclBall c r))) :
    MemLp ((euclBall c r).indicator u) 2 volume :=
  (memLp_indicator_iff_restrict (measurableSet_euclBall c r)).mpr hu

theorem locallyIntegrable_dil_indicator {u : (Fin n → ℝ) → ℝ}
    (hu : MemLp u 2 (volume.restrict (euclBall c r))) (m : ℕ) :
    LocallyIntegrable (fun x => (euclBall c r).indicator u (dil c (tD m) x)) volume :=
  (memLp_comp_dil c (tD_pos m) (memLp_indicator_ball c r hu)).locallyIntegrable (by norm_num)

theorem contDiff_smoothApprox {u : (Fin n → ℝ) → ℝ}
    (hu : MemLp u 2 (volume.restrict (euclBall c r))) (m : ℕ) :
    ContDiff ℝ ∞ (smoothApprox c r m u) :=
  (bumpD (n := n) r m).hasCompactSupport_normed.contDiff_convolution_left _
    (bumpD (n := n) r m).contDiff_normed (locallyIntegrable_dil_indicator c r hu m)

/-- The Euclidean length is at most `√n` times the sup norm (squared form). -/
theorem sqDist_le_card_mul (x y : Fin n → ℝ) : sqDist x y ≤ n * ‖y - x‖ ^ 2 := by
  unfold sqDist
  calc ∑ i, (y i - x i) ^ 2 ≤ ∑ _i : Fin n, ‖y - x‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := norm_le_pi_norm (y - x) i
        rw [Pi.sub_apply, Real.norm_eq_abs] at this
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
    _ = n * ‖y - x‖ ^ 2 := by simp

/-- Triangle inequality for the Euclidean distance. -/
theorem sqrt_sqDist_triangle (c x y : Fin n → ℝ) :
    Real.sqrt (sqDist c y) ≤ Real.sqrt (sqDist c x) + Real.sqrt (sqDist x y) := by
  have e : ∀ a b : Fin n → ℝ, Real.sqrt (sqDist a b) =
      ‖(WithLp.toLp 2 (b - a) : EuclideanSpace ℝ (Fin n))‖ := by
    intro a b
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp [sqDist, sq_abs]
  rw [e, e, e]
  have : (WithLp.toLp 2 (y - c) : EuclideanSpace ℝ (Fin n)) =
      WithLp.toLp 2 (x - c) + WithLp.toLp 2 (y - x) := by
    rw [← WithLp.toLp_add]; congr 1; abel
  rw [this]
  exact norm_add_le _ _

/-- The mollifier at a point of the ball only sees the larger ball `B_{r/t_m}`. -/
theorem mem_bigBall_of_bump {m : ℕ} {x y : Fin n → ℝ} (hx : x ∈ euclBall c r)
    (hy : ‖x - y‖ ≤ epsD (n := n) r m) : y ∈ euclBall c (r / tD m) := by
  have hr0 := hr.out
  have ht := tD_pos m
  have hε := epsD_pos (n := n) r m
  show sqDist c y < (r / tD m) ^ 2
  have h1 : Real.sqrt (sqDist c x) < r := by
    rw [Real.sqrt_lt' hr0]; exact hx
  have h2 : Real.sqrt (sqDist x y) ≤ ((n : ℝ) + 1) * epsD (n := n) r m := by
    rw [Real.sqrt_le_left (by positivity)]
    have := sqDist_le_card_mul x y
    have hyx : ‖y - x‖ ≤ epsD (n := n) r m := by rw [norm_sub_rev]; exact hy
    calc sqDist x y ≤ n * ‖y - x‖ ^ 2 := this
      _ ≤ n * (epsD (n := n) r m) ^ 2 := by gcongr
      _ ≤ ((n : ℝ) + 1) ^ 2 * epsD (n := n) r m ^ 2 := by
          gcongr; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      _ = (((n : ℝ) + 1) * epsD (n := n) r m) ^ 2 := by ring
  have h3 : ((n : ℝ) + 1) * epsD (n := n) r m = r / tD m - r := by
    unfold epsD; field_simp
  have h4 := sqrt_sqDist_triangle c x y
  have h5 : Real.sqrt (sqDist c y) < r / tD m := by linarith
  have h6 := Real.sq_sqrt (sqDist_nonneg c y)
  have h7 := Real.sqrt_nonneg (sqDist c y)
  nlinarith

/-- **Derivatives of the smooth approximants** on the ball:
`∂_i (smoothApprox u) = t_m · smoothApprox (∂_i u)`. -/
theorem pd_smoothApprox {i : Fin n} {u g : (Fin n → ℝ) → ℝ}
    (h : HasWeakPartialR (euclBall c r) i u g) (huL : MemLp u 2 (volume.restrict (euclBall c r)))
    (hgL : MemLp g 2 (volume.restrict (euclBall c r))) (m : ℕ) {x : Fin n → ℝ}
    (hx : x ∈ euclBall c r) :
    pd (smoothApprox c r m u) i x = tD m * smoothApprox c r m g x := by
  have hr0 := hr.out
  set t := tD m
  have ht := tD_pos m
  set ρ := (bumpD (n := n) r m).normed volume
  have hρ1 : ContDiff ℝ 1 ρ := (bumpD (n := n) r m).contDiff_normed
  have hρc : HasCompactSupport ρ := (bumpD (n := n) r m).hasCompactSupport_normed
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : (Fin n → ℝ) → ℝ, ψ = fun y => ρ (x - y) := ⟨_, rfl⟩
  have hψs : ContDiff ℝ ∞ ψ := by
    rw [hψdef]; exact (bumpD (n := n) r m).contDiff_normed.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := by
    rw [hψdef]; exact hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hψsupp : tsupport ψ ⊆ euclBall c (r / t) := by
    intro y hy
    have h1 : x - y ∈ tsupport ρ := by
      rw [hψdef] at hy
      have := tsupport_comp_eq_preimage ρ (Homeomorph.subLeft x)
      rw [show (fun y => ρ (x - y)) = ρ ∘ Homeomorph.subLeft x from rfl, this] at hy
      exact hy
    rw [(bumpD (n := n) r m).tsupport_normed_eq] at h1
    have h2 : ‖x - y‖ ≤ epsD (n := n) r m := by
      have := mem_closedBall.mp h1
      rw [dist_zero_right] at this; exact this
    exact mem_bigBall_of_bump c r hx h2
  have hψ : IsTest (euclBall c (r / t)) ψ := ⟨hψs, hψc, hψsupp⟩
  have hpdψ : ∀ y, pd ψ i y = -(fderiv ℝ ρ (x - y) (Pi.single i 1)) := by
    intro y
    unfold pd
    have h1 : HasFDerivAt (fun y : Fin n → ℝ => x - y) (-ContinuousLinearMap.id ℝ (Fin n → ℝ)) y :=
      (hasFDerivAt_id y).const_sub x
    have h2 := ((hρ1.differentiable one_ne_zero) (x - y)).hasFDerivAt.comp y h1
    rw [hψdef, show (fun y => ρ (x - y)) = ρ ∘ fun y => x - y from rfl, h2.fderiv]
    simp
  have hweak := h.comp_dil c hr0.le ht
  have key := hweak ψ hψ
  -- `U = u ∘ dil` on the support
  have hU : ∀ (v : (Fin n → ℝ) → ℝ) y, y ∈ euclBall c (r / t) →
      (euclBall c r).indicator v (dil c t y) = v (dil c t y) := by
    intro v y hy
    have : dil c t y ∈ euclBall c r := by
      rw [← preimage_dil_ball c ht r hr0.le] at hy; exact hy
    simp [this]
  have eL : ∫ y, pd ψ i y * (euclBall c r).indicator u (dil c t y) =
      ∫ y, pd ψ i y * u (dil c t y) := by
    congr 1; funext y
    by_cases hy : y ∈ euclBall c (r / t)
    · rw [hU u y hy]
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hy (hψsupp (tsupport_pd_subset ψ i h'))),
        zero_mul, zero_mul]
  have eR : ∫ y, ψ y * (t * g (dil c t y)) =
      t * ∫ y, ψ y * (euclBall c r).indicator g (dil c t y) := by
    rw [← integral_const_mul]
    congr 1; funext y
    by_cases hy : y ∈ euclBall c (r / t)
    · rw [hU g y hy]; ring
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hy (hψsupp h'))]; ring
  -- the derivative of the convolution
  show fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    (fun x => (euclBall c r).indicator u (dil c t x))) x (Pi.single i 1) = _
  rw [Mollifier.fderiv_convolution_apply hρ1 hρc (locallyIntegrable_dil_indicator c r huL m) x
    (Pi.single i 1)]
  rw [← integral_sub_left_eq_self (fun s => fderiv ℝ ρ s (Pi.single i 1) •
    (euclBall c r).indicator u (dil c t (x - s))) volume x]
  simp only [sub_sub_cancel, smul_eq_mul]
  have e3 : ∫ y, fderiv ℝ ρ (x - y) (Pi.single i 1) * (euclBall c r).indicator u (dil c t y) =
      -∫ y, pd ψ i y * (euclBall c r).indicator u (dil c t y) := by
    rw [← integral_neg]; congr 1; funext y; rw [hpdψ]; ring
  rw [e3, eL, key, neg_neg, eR]
  congr 1
  unfold smoothApprox
  rw [convolution_def, ← integral_sub_left_eq_self (fun s => (ContinuousLinearMap.lsmul ℝ ℝ)
    (ρ s) ((euclBall c r).indicator g (dil c t (x - s)))) volume x]
  simp only [sub_sub_cancel, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hψdef]

end DilWeak

/-! ### Density of smooth functions in `H^k(B)` -/

section Density

/-- Sequences agreeing on an open set have the same `H^k(Ω)` limits. -/
theorem ConvHk.congr_seq {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {k : ℕ}
    {ψ ψ' : ℕ → (Fin n → ℝ) → ℝ} (h : ∀ m, ∀ x ∈ Ω, ψ m x = ψ' m x) {u : (Fin n → ℝ) → ℝ}
    (hc : ConvHk Ω k ψ u) : ConvHk Ω k ψ' u := by
  have hb : ∀ {ψ ψ' : ℕ → (Fin n → ℝ) → ℝ}, (∀ m, ∀ x ∈ Ω, ψ m x = ψ' m x) →
      ∀ {u : (Fin n → ℝ) → ℝ}, (MemLp u 2 (volume.restrict Ω) ∧
        Tendsto (fun m => eLpNorm (ψ m - u) 2 (volume.restrict Ω)) atTop (𝓝 0)) →
      (MemLp u 2 (volume.restrict Ω) ∧
        Tendsto (fun m => eLpNorm (ψ' m - u) 2 (volume.restrict Ω)) atTop (𝓝 0)) := by
    intro ψ ψ' h u hb
    refine ⟨hb.1, hb.2.congr fun m => eLpNorm_congr_ae ?_⟩
    rw [EventuallyEq, ae_restrict_iff' hΩ.measurableSet]
    exact Eventually.of_forall fun x hx => by simp [h m x hx]
  induction k generalizing ψ ψ' u with
  | zero => exact hb h hc
  | succ k ih =>
    refine ⟨hb h hc.1, fun i => ?_⟩
    obtain ⟨g, hg⟩ := hc.2 i
    refine ⟨g, ih (fun m x hx => ?_) hg⟩
    have hev : ψ m =ᶠ[𝓝 x] ψ' m := Filter.eventually_of_mem (hΩ.mem_nhds hx) fun y hy => h m y hy
    unfold pd; rw [hev.fderiv_eq]

/-- Scaling by factors `t_m → 1` preserves `H^k` limits. -/
theorem ConvHk.scale {Ω : Set (Fin n → ℝ)} {k : ℕ} {ψ : ℕ → (Fin n → ℝ) → ℝ}
    (hψ : ∀ m, ContDiff ℝ ∞ (ψ m)) {u : (Fin n → ℝ) → ℝ} (hc : ConvHk Ω k ψ u) {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝 1)) : ConvHk Ω k (fun m x => t m * ψ m x) u := by
  have hb : ∀ {ψ : ℕ → (Fin n → ℝ) → ℝ}, (∀ m, ContDiff ℝ ∞ (ψ m)) →
      ∀ {u : (Fin n → ℝ) → ℝ}, (MemLp u 2 (volume.restrict Ω) ∧
        Tendsto (fun m => eLpNorm (ψ m - u) 2 (volume.restrict Ω)) atTop (𝓝 0)) →
      (MemLp u 2 (volume.restrict Ω) ∧
        Tendsto (fun m => eLpNorm ((fun x => t m * ψ m x) - u) 2 (volume.restrict Ω)) atTop
          (𝓝 0)) := by
    intro ψ hψ u hb
    refine ⟨hb.1, ?_⟩
    have hle : ∀ m, eLpNorm ((fun x => t m * ψ m x) - u) 2 (volume.restrict Ω) ≤
        ENNReal.ofReal |t m| * eLpNorm (ψ m - u) 2 (volume.restrict Ω) +
          ENNReal.ofReal |t m - 1| * eLpNorm u 2 (volume.restrict Ω) := by
      intro m
      have e : ((fun x => t m * ψ m x) - u) = t m • (ψ m - u) + (t m - 1) • u := by
        funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [e]
      refine (eLpNorm_add_le (((hψ m).continuous.aestronglyMeasurable.sub hb.1.1).const_smul _)
        (hb.1.1.const_smul _) (by norm_num)).trans ?_
      rw [eLpNorm_const_smul, eLpNorm_const_smul, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
        Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : Tendsto (fun m => ENNReal.ofReal |t m|) atTop (𝓝 (ENNReal.ofReal |1|)) :=
      (ENNReal.continuous_ofReal.comp continuous_abs).continuousAt.tendsto.comp ht
    have h2 : Tendsto (fun m => ENNReal.ofReal |t m - 1|) atTop (𝓝 (ENNReal.ofReal |1 - 1|)) :=
      (ENNReal.continuous_ofReal.comp (continuous_abs.comp (continuous_sub_right 1))).continuousAt.tendsto.comp ht
    simp only [abs_one, sub_self, abs_zero, ENNReal.ofReal_one, ENNReal.ofReal_zero] at h1 h2
    have h3 := ENNReal.Tendsto.mul h1 (Or.inr ENNReal.zero_ne_top) hb.2 (Or.inr ENNReal.one_ne_top)
    have h4 := ENNReal.Tendsto.mul h2 (Or.inr hb.1.eLpNorm_ne_top) tendsto_const_nhds
      (Or.inr ENNReal.zero_ne_top)
    rw [mul_zero] at h3
    rw [zero_mul] at h4
    have h5 := h3.add h4
    rw [add_zero] at h5
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h5 (fun m => zero_le) hle
  induction k generalizing ψ u with
  | zero => exact hb hψ hc
  | succ k ih =>
    refine ⟨hb hψ hc.1, fun i => ?_⟩
    obtain ⟨g, hg⟩ := hc.2 i
    refine ⟨g, ?_⟩
    have e : (fun m => pd (fun x => t m * ψ m x) i) = fun m x => t m * pd (ψ m) i x := by
      funext m x
      exact pd_mul contDiff_const ((hψ m).of_le (by simp)) i x |>.trans (by simp [pd])
    rw [e]
    exact ih (fun m => contDiff_pd (hψ m) i) hg

variable (c : Fin n → ℝ) (r : ℝ) [hr : Fact (0 < r)]

/-- `L²(B)` convergence of the smooth approximants. -/
theorem tendsto_smoothApprox {u : (Fin n → ℝ) → ℝ}
    (hu : MemLp u 2 (volume.restrict (euclBall c r))) :
    Tendsto (fun m => eLpNorm (smoothApprox c r m u - u) 2 (volume.restrict (euclBall c r)))
      atTop (𝓝 0) := by
  set V := (euclBall c r).indicator u
  have hV : MemLp V 2 volume := memLp_indicator_ball c r hu
  set Vt : ℕ → (Fin n → ℝ) → ℝ := fun m x => V (dil c (tD m) x)
  have hVt : ∀ m, MemLp (Vt m) 2 volume := fun m => memLp_comp_dil c (tD_pos m) hV
  set ρ : ℕ → (Fin n → ℝ) → ℝ := fun m => (bumpD (n := n) r m).normed volume
  have hconv : ∀ m (w : (Fin n → ℝ) → ℝ), LocallyIntegrable w volume → ∀ x,
      ConvolutionExistsAt (ρ m) w x (ContinuousLinearMap.lsmul ℝ ℝ) volume := fun m w hw x =>
    (bumpD (n := n) r m).hasCompactSupport_normed.convolutionExists_left _
      (bumpD (n := n) r m).continuous_normed hw x
  have hloc : ∀ {w : (Fin n → ℝ) → ℝ}, MemLp w 2 volume → LocallyIntegrable w volume :=
    fun hw => hw.locallyIntegrable (by norm_num)
  -- the two sources of error
  have hdil : Tendsto (fun m => eLpNorm (Vt m - V) 2 volume) atTop (𝓝 0) :=
    tendsto_eLpNorm_comp_dil_sub c hV tendsto_tD half_le_tD
  have hmol : Tendsto (fun m => eLpNorm ((ρ m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V) - V) 2
      volume) atTop (𝓝 0) :=
    Mollifier.tendsto_eLpNorm_normed_bump_convolution_sub (tendsto_epsD r) (by norm_num)
      (by norm_num) hV
  have hbound : ∀ m, eLpNorm (smoothApprox c r m u - u) 2 (volume.restrict (euclBall c r)) ≤
      3 * eLpNorm (Vt m - V) 2 volume +
        eLpNorm ((ρ m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V) - V) 2 volume := by
    intro m
    have e0 : eLpNorm (smoothApprox c r m u - u) 2 (volume.restrict (euclBall c r)) =
        eLpNorm (smoothApprox c r m u - V) 2 (volume.restrict (euclBall c r)) := by
      refine eLpNorm_congr_ae ?_
      rw [EventuallyEq, ae_restrict_iff' (measurableSet_euclBall c r)]
      exact Eventually.of_forall fun x hx => by simp [V, hx]
    rw [e0]
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    have hdec : smoothApprox c r m u - V =
        ((ρ m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (Vt m - V)) - (Vt m - V)) +
          ((ρ m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V) - V) + (Vt m - V) := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [Mollifier.convolution_sub_apply (hconv m _ (hloc (hVt m)) x) (hconv m _ (hloc hV) x)]
      simp only [smoothApprox, Vt, ρ]
      ring
    have hm1 : AEStronglyMeasurable (ρ m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (Vt m - V)) volume :=
      ((bumpD (n := n) r m).hasCompactSupport_normed.continuous_convolution_left _
        (bumpD (n := n) r m).continuous_normed (hloc ((hVt m).sub hV))).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (ρ m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V) volume :=
      ((bumpD (n := n) r m).hasCompactSupport_normed.continuous_convolution_left _
        (bumpD (n := n) r m).continuous_normed (hloc hV)).aestronglyMeasurable
    have hmd : AEStronglyMeasurable (Vt m - V) volume := ((hVt m).sub hV).1
    have hY : eLpNorm (ρ m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (Vt m - V)) 2 volume ≤
        eLpNorm (Vt m - V) 2 volume :=
      Mollifier.eLpNorm_convolution_le (bumpD (n := n) r m).continuous_normed.measurable
        (fun x => (bumpD (n := n) r m).nonneg_normed x) (bumpD (n := n) r m).integral_normed hmd
        (by norm_num) (by norm_num)
    rw [hdec]
    calc eLpNorm (((ρ m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (Vt m - V)) - (Vt m - V)) +
          ((ρ m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V) - V) + (Vt m - V)) 2 volume
        ≤ eLpNorm ((ρ m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (Vt m - V)) - (Vt m - V)) 2
            volume + eLpNorm ((ρ m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V) - V) 2 volume +
            eLpNorm (Vt m - V) 2 volume := by
          refine (eLpNorm_add_le ((hm1.sub hmd).add (hm2.sub hV.1)) hmd (by norm_num)).trans ?_
          gcongr
          exact eLpNorm_add_le (hm1.sub hmd) (hm2.sub hV.1) (by norm_num)
      _ ≤ (eLpNorm (Vt m - V) 2 volume + eLpNorm (Vt m - V) 2 volume) +
            eLpNorm ((ρ m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V) - V) 2 volume +
            eLpNorm (Vt m - V) 2 volume := by
          gcongr
          exact (eLpNorm_sub_le hm1 hmd (by norm_num)).trans (add_le_add hY le_rfl)
      _ = 3 * eLpNorm (Vt m - V) 2 volume +
            eLpNorm ((ρ m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V) - V) 2 volume := by ring
  have hlim : Tendsto (fun m => 3 * eLpNorm (Vt m - V) 2 volume +
      eLpNorm ((ρ m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V) - V) 2 volume) atTop (𝓝 0) := by
    have := (ENNReal.Tendsto.const_mul hdil (Or.inr (by norm_num : (3 : ℝ≥0∞) ≠ ⊤))).add hmol
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun m => zero_le) hbound

/-- **Density of smooth functions in `H^k(B)`**: every `u ∈ H^k(B_r(c))` (weak derivatives) is the
`H^k(B)` limit of the explicit smooth functions `smoothApprox c r m u`. -/
theorem convHk_smoothApprox (k : ℕ) : ∀ {u : (Fin n → ℝ) → ℝ},
    MemHk (euclBall c r) k u → ConvHk (euclBall c r) k (fun m => smoothApprox c r m u) u := by
  induction k with
  | zero => intro u hu; exact ⟨hu, tendsto_smoothApprox c r hu⟩
  | succ k ih =>
    intro u hu
    refine ⟨⟨hu.1, tendsto_smoothApprox c r hu.1⟩, fun i => ?_⟩
    obtain ⟨g, hg, hgm⟩ := hu.2 i
    refine ⟨g, ?_⟩
    have h1 := (ih hgm).scale (fun m => contDiff_smoothApprox c r hgm.memLp m) tendsto_tD
    exact h1.congr_seq (isOpen_euclBall c r) fun m x hx =>
      (pd_smoothApprox c r hg hu.1 hgm.memLp m hx).symm

/-- `H^k(B)` (weak derivatives) coincides with the class of `H^k` limits of smooth functions. -/
theorem memHk_iff_exists_convHk (k : ℕ) {u : (Fin n → ℝ) → ℝ} :
    MemHk (euclBall c r) k u ↔ ∃ φ : ℕ → (Fin n → ℝ) → ℝ, (∀ m, ContDiff ℝ ∞ (φ m)) ∧
      ConvHk (euclBall c r) k φ u := by
  constructor
  · intro hu
    exact ⟨fun m => smoothApprox c r m u, fun m => contDiff_smoothApprox c r hu.memLp m,
      convHk_smoothApprox c r k hu⟩
  · rintro ⟨φ, hφ, hc⟩
    exact hc.memHk ((isBounded_closedBall (x := c) (r := |r|)).subset fun x hx =>
      mem_closedBall_of_sqDist_le (abs_nonneg r) (by rw [sq_abs]; exact le_of_lt hx))
      (measurableSet_euclBall c r) hφ

/-- Weak `H¹(B)` functions belong to `H¹(B)` = closure of the `C¹` graphs. -/
theorem exists_H1B_of_memHk [NeZero n] {F : L2B c r} (hF : MemHk (euclBall c r) 1 (F : (Fin n → ℝ) → ℝ)) :
    ∃ Fh ∈ H1B c r, Fh none = F := by
  obtain ⟨Fh, hFh, h0, -⟩ := exists_H1B_of_conv c r (fun m => contDiff_smoothApprox c r hF.memLp m)
    (convHk_smoothApprox c r 1 hF)
  exact ⟨Fh, hFh, h0⟩

/-- **`H^{k+2}` regularity of the weak Neumann problem on a ball, weak form**: for `F ∈ H^k(B)`
(weak derivatives up to order `k` in `L²(B)`), the mean-zero weak solution `ξ = solCLM F` of
`Δξ = F - avg F`, `∂_νξ = 0` lies in `H^{k+2}(B)`. -/
theorem neumann_Hk_weak [NeZero n] (k : ℕ) {F : L2B c r}
    (hF : MemHk (euclBall c r) k (F : (Fin n → ℝ) → ℝ)) :
    MemHk (euclBall c r) (k + 2) (solFn c r F) :=
  neumann_Hk c r k F _ (fun m => contDiff_smoothApprox c r hF.memLp m) (convHk_smoothApprox c r k hF)

end Density

end RenewalGeometry.BallAnalysis.BallReg
