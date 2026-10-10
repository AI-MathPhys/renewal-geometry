/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallSobolevDensity
import RenewalGeometry.Analysis.BallLinearizedCoulomb

/-!
# The Sobolev embedding `H³(B) ⊂ L^∞` on a ball of `ℝ⁴`

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript (stage C5b of the ball rendering of Uhlenbeck's
small-energy gauge theorem: the Banach algebra `H^s(B)`, `s ≥ 3`).

Proof by averaging the second-order Taylor formula over the ball (a Riesz-potential argument):
for `x, y ∈ B`,
`u(x) = u(y) + ∇u(y)·(x - y) + ∫₀¹ (1-t) D²u(y + t(x - y))[x - y, x - y] dt`;
averaging over `y ∈ B` and changing variables `z = y + t(x - y)` gives
`|B| |u(x)| ≤ ‖u‖_{L¹(B)} + 2r ‖∇u‖_{L¹(B)} + ((2r)⁴/4) ∫_B |D²u(z)| |x - z|^{-2} dz`,
and Hölder with `|x - ·|^{-2} ∈ L^{4/3}` (polar coordinates) and `D²u ∈ L⁴` (`sobolev_ball` for the
first derivatives of `D²u`) bounds `u(x)` by the `H³(B)` norm.

* `taylor2_eq` (generic `n`): the second-order Taylor formula with integral remainder;
* `abs_le_taylor_bound`: the pointwise bound;
* ...
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallReg

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-! ### The second-order Taylor formula -/

section Taylor

/-- The segment `t ↦ y + t (x - y)`. -/
def seg (x y : Fin n → ℝ) (t : ℝ) : Fin n → ℝ := y + t • (x - y)

theorem hasDerivAt_seg (x y : Fin n → ℝ) (t : ℝ) : HasDerivAt (seg x y) (x - y) t := by
  have := ((hasDerivAt_id t).smul_const (x - y)).const_add y
  rw [one_smul] at this
  exact this

theorem continuous_seg (x y : Fin n → ℝ) : Continuous (seg x y) :=
  continuous_const.add (continuous_id.smul continuous_const)

/-- The second directional derivative along `x - y`. -/
def d2Dir (u : (Fin n → ℝ) → ℝ) (x y z : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, (x i - y i) * (x j - y j) * pd (pd u i) j z

theorem hasDerivAt_comp_seg {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) (x y : Fin n → ℝ)
    (t : ℝ) : HasDerivAt (fun t => u (seg x y t))
      (∑ i, (x i - y i) * pd u i (seg x y t)) t := by
  have hd := ((hu.differentiable one_ne_zero) (seg x y t)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_seg x y t)
  refine hd.congr_deriv ?_
  rw [fderiv_apply_eq_sum_pd]
  simp

/-- **Second-order Taylor formula with integral remainder**:
`u(x) = u(y) + Σ_i (x_i - y_i) ∂_iu(y) + ∫₀¹ (1 - t) D²u(y + t(x-y))[x - y, x - y] dt`. -/
theorem taylor2_eq {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) (x y : Fin n → ℝ) :
    u x = u y + (∑ i, (x i - y i) * pd u i y) +
      ∫ t in (0 : ℝ)..1, (1 - t) * d2Dir u x y (seg x y t) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hpd1 : ∀ i, ContDiff ℝ 1 (pd u i) := fun i => contDiff_pd_of_two hu i
  set g' : ℝ → ℝ := fun t => ∑ i, (x i - y i) * pd u i (seg x y t)
  have hg' : ∀ t, HasDerivAt g' (d2Dir u x y (seg x y t)) t := by
    intro t
    have : ∀ i, HasDerivAt (fun t => (x i - y i) * pd u i (seg x y t))
        ((x i - y i) * ∑ j, (x j - y j) * pd (pd u i) j (seg x y t)) t := fun i =>
      (hasDerivAt_comp_seg (hpd1 i) x y t).const_mul _
    have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => this i
    refine hs.congr_deriv ?_
    simp only [d2Dir, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  set h : ℝ → ℝ := fun t => u (seg x y t) + (1 - t) * g' t
  have hh : ∀ t, HasDerivAt h ((1 - t) * d2Dir u x y (seg x y t)) t := by
    intro t
    have h1 := hasDerivAt_comp_seg hu1 x y t
    have h2 := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul (hg' t)
    refine (h1.add h2).congr_deriv ?_
    simp only [g', Pi.sub_apply, id]; ring
  have hcont : Continuous fun t => (1 - t) * d2Dir u x y (seg x y t) := by
    have hd : Continuous fun z => d2Dir u x y z := by
      unfold d2Dir
      exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
        continuous_const.mul (continuous_pd (hpd1 i) j)
    exact (continuous_const.sub continuous_id).mul (hd.comp (continuous_seg x y))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hh t)
    (hcont.intervalIntegrable 0 1)
  rw [hFTC]
  simp only [h, g', seg]
  simp

/-- `|D²u[v, v]| ≤ |v|² Σ_{ij} |∂_i∂_ju|`. -/
theorem abs_d2Dir_le (u : (Fin n → ℝ) → ℝ) (x y z : Fin n → ℝ) :
    |d2Dir u x y z| ≤ sqDist x y * ∑ i, ∑ j, |pd (pd u i) j z| := by
  unfold d2Dir
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have hi := sq_le_sqDist y x i
  have hj := sq_le_sqDist y x j
  have e : sqDist y x = sqDist x y := by
    unfold sqDist; exact Finset.sum_congr rfl fun k _ => by ring
  rw [e] at hi hj
  nlinarith [sq_nonneg (|x i - y i| - |x j - y j|), sq_abs (x i - y i), sq_abs (x j - y j),
    abs_nonneg (x i - y i), abs_nonneg (x j - y j)]

/-- **The pointwise Taylor bound**. -/
theorem abs_le_taylor_bound {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) (x y : Fin n → ℝ) :
    |u x| ≤ |u y| + (∑ i, |x i - y i| * |pd u i y|) +
      ∫ t in (0 : ℝ)..1, (1 - t) * (sqDist x y * ∑ i, ∑ j, |pd (pd u i) j (seg x y t)|) := by
  have hpd1 : ∀ i, ContDiff ℝ 1 (pd u i) := fun i => contDiff_pd_of_two hu i
  rw [taylor2_eq hu x y]
  have hd : Continuous fun z => d2Dir u x y z := by
    unfold d2Dir
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      continuous_const.mul (continuous_pd (hpd1 i) j)
  have hH : Continuous fun z => ∑ i, ∑ j, |pd (pd u i) j z| :=
    continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (continuous_pd (hpd1 i) j).abs
  have hrem : |∫ t in (0 : ℝ)..1, (1 - t) * d2Dir u x y (seg x y t)| ≤
      ∫ t in (0 : ℝ)..1, (1 - t) * (sqDist x y * ∑ i, ∑ j, |pd (pd u i) j (seg x y t)|) := by
    refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
    refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ fun t ht => ?_
    · exact ((continuous_const.sub continuous_id).mul (hd.comp (continuous_seg x y))).abs.intervalIntegrable 0 1
    · exact ((continuous_const.sub continuous_id).mul (continuous_const.mul
        (hH.comp (continuous_seg x y)))).intervalIntegrable 0 1
    · rw [abs_mul, abs_of_nonneg (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t)]
      exact mul_le_mul_of_nonneg_left (abs_d2Dir_le u x y _) (by linarith [ht.2])
  calc |u y + (∑ i, (x i - y i) * pd u i y) + ∫ t in (0 : ℝ)..1, (1 - t) * d2Dir u x y (seg x y t)|
      ≤ |u y| + (∑ i, |x i - y i| * |pd u i y|) +
          |∫ t in (0 : ℝ)..1, (1 - t) * d2Dir u x y (seg x y t)| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl ?_))
          le_rfl)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp [abs_mul]
    _ ≤ _ := by gcongr

end Taylor

/-! ### The Riesz-potential estimate for the averaged remainder -/

section Potential

theorem seg_eq_dil (x y : Fin n → ℝ) (t : ℝ) : seg x y t = dil x (1 - t) y := by
  funext i
  simp only [seg, dil, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem sqDist_comm (x y : Fin n → ℝ) : sqDist x y = sqDist y x := by
  unfold sqDist; exact Finset.sum_congr rfl fun k _ => by ring

/-- `∫_{a}^{∞} s^{-(n+1)} ds = a^{-n}/n`, as a lower integral. -/
theorem lintegral_Ici_rpow [NeZero n] {a : ℝ} (ha : 0 < a) :
    ∫⁻ s in Ici a, ENNReal.ofReal (s ^ (-((n : ℝ) + 1))) = ENNReal.ofReal (a ^ (-(n : ℝ)) / n) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hlt : -((n : ℝ) + 1) < -1 := by linarith
  rw [← setLIntegral_congr Ioi_ae_eq_Ici]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hlt ha)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => Real.rpow_nonneg (le_of_lt
      (lt_trans ha hs)) _)]
  rw [integral_Ioi_rpow_of_lt hlt ha]
  congr 1
  have : -((n : ℝ) + 1) + 1 = -(n : ℝ) := by ring
  rw [this, neg_div, div_neg, neg_neg]

/-- `∫⁻_{t ∈ (0,1)} 1{d ≤ R²(1-t)²} (1-t)^{-(n+1)} dt ≤ R^n d^{-n/2} / n` for `d > 0`. -/
theorem lintegral_cut_le [NeZero n] {d R : ℝ} (hd : 0 < d) (hR : 0 < R) :
    ∫⁻ t in Ioo (0 : ℝ) 1, (Set.indicator {t | d ≤ R ^ 2 * (1 - t) ^ 2}
      (fun t => ENNReal.ofReal ((1 - t) ^ (-((n : ℝ) + 1))))) t ≤
      ENNReal.ofReal (R ^ n * d ^ (-(n : ℝ) / 2) / n) := by
  set a : ℝ := Real.sqrt d / R
  have ha : 0 < a := div_pos (Real.sqrt_pos.mpr hd) hR
  set F : ℝ → ℝ≥0∞ := Set.indicator (Ici a) (fun s => ENNReal.ofReal (s ^ (-((n : ℝ) + 1))))
  have hF : Measurable F :=
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Ici
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, (Set.indicator {t | d ≤ R ^ 2 * (1 - t) ^ 2}
      (fun t => ENNReal.ofReal ((1 - t) ^ (-((n : ℝ) + 1))))) t ≤ F (1 - t) := by
    intro t ht
    by_cases hmem : t ∈ {t | d ≤ R ^ 2 * (1 - t) ^ 2}
    · rw [Set.indicator_of_mem hmem]
      have h1 : a ≤ 1 - t := by
        have hs : 0 < 1 - t := by linarith [ht.2]
        rw [div_le_iff₀ hR, Real.sqrt_le_left (by positivity)]
        have : d ≤ R ^ 2 * (1 - t) ^ 2 := hmem
        nlinarith
      rw [show F (1 - t) = ENNReal.ofReal ((1 - t) ^ (-((n : ℝ) + 1))) from
        Set.indicator_of_mem (show 1 - t ∈ Ici a from h1) _]
    · rw [Set.indicator_of_notMem hmem]; exact zero_le
  calc ∫⁻ t in Ioo (0 : ℝ) 1, (Set.indicator {t | d ≤ R ^ 2 * (1 - t) ^ 2}
        (fun t => ENNReal.ofReal ((1 - t) ^ (-((n : ℝ) + 1))))) t
      ≤ ∫⁻ t in Ioo (0 : ℝ) 1, F (1 - t) := setLIntegral_mono (hF.comp
          (measurable_const.sub measurable_id)) hpt
    _ ≤ ∫⁻ t, F (1 - t) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ s, F s := lintegral_sub_left_eq_self F 1
    _ = ∫⁻ s in Ici a, ENNReal.ofReal (s ^ (-((n : ℝ) + 1))) :=
        lintegral_indicator measurableSet_Ici _
    _ = ENNReal.ofReal (a ^ (-(n : ℝ)) / n) := lintegral_Ici_rpow ha
    _ = ENNReal.ofReal (R ^ n * d ^ (-(n : ℝ) / 2) / n) := by
        congr 2
        have hsd : Real.sqrt d = d ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow d
        rw [Real.div_rpow (Real.sqrt_nonneg d) hR.le, hsd, ← Real.rpow_mul hd.le,
          Real.rpow_neg hR.le, Real.rpow_natCast, div_inv_eq_mul, mul_comm]
        congr 2; ring

end Potential

/-! ### The potential estimate -/

section Potential2

variable [NeZero n] (c : Fin n → ℝ) {r : ℝ}

theorem measurableEmbedding_dil {s : ℝ} (hs : s ≠ 0) (x : Fin n → ℝ) :
    MeasurableEmbedding (dil x s) := (dilHomeo x hs).measurableEmbedding

/-- Change of variables for lower integrals under dilations: `∫⁻ K(dil x s y) dy = s^{-n} ∫⁻ K`. -/
theorem lintegral_comp_dil {s : ℝ} (hs : 0 < s) (x : Fin n → ℝ) (K : (Fin n → ℝ) → ℝ≥0∞) :
    ∫⁻ y, K (dil x s y) = ENNReal.ofReal ((s ^ n)⁻¹) * ∫⁻ z, K z := by
  rw [(measurePreserving_dil x hs).lintegral_comp_emb (measurableEmbedding_dil hs.ne' x),
    lintegral_smul_measure]
  rfl

/-- One slice of the averaged remainder, after the change of variables `z = y + t(x - y)`. -/
theorem slice_le {H : (Fin n → ℝ) → ℝ} (hH0 : ∀ z, 0 ≤ H z) {x : Fin n → ℝ}
    (hx : x ∈ euclBall c r) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∫⁻ y in euclBall c r, ENNReal.ofReal ((1 - t) * (sqDist x y * H (seg x y t))) ≤
      ∫⁻ z, (euclBall c r).indicator (fun z => ENNReal.ofReal (sqDist x z * H z)) z *
        ({t | sqDist x z ≤ (2 * r) ^ 2 * (1 - t) ^ 2}.indicator
          (fun t => ENNReal.ofReal ((1 - t) ^ (-((n : ℝ) + 1)))) t) := by
  set s := 1 - t
  have hs : 0 < s := by simp only [s]; linarith [ht.2]
  have hs1 : s ≤ 1 := by simp only [s]; linarith [ht.1]
  set K : (Fin n → ℝ) → ℝ≥0∞ := fun z => (euclBall c r).indicator
    (fun y => ENNReal.ofReal (s * (sqDist x y * H (dil x s y)))) (dil x s⁻¹ z)
  have e1 : ∫⁻ y in euclBall c r, ENNReal.ofReal ((1 - t) * (sqDist x y * H (seg x y t))) =
      ∫⁻ y, K (dil x s y) := by
    rw [← lintegral_indicator (measurableSet_euclBall c r)]
    congr 1; funext y
    simp only [K, dil_inv_dil x hs.ne', seg_eq_dil]
    rfl
  rw [e1, lintegral_comp_dil hs x K, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun z => ?_
  simp only [K]
  set y := dil x s⁻¹ z
  have hzy : dil x s y = z := dil_dil_inv x hs.ne' z
  by_cases hy : y ∈ euclBall c r
  · rw [Set.indicator_of_mem hy, hzy]
    have hsq : sqDist x y = (s ^ 2)⁻¹ * sqDist x z := by
      simp only [y]; rw [sqDist_dil, inv_pow]
    have hzB : z ∈ euclBall c r := by
      rw [← hzy]
      have := mem_euclBall_convex hy hx hs.le hs1
      convert this using 1
      funext i; simp only [dil, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    have hdz : sqDist x z ≤ (2 * r) ^ 2 * s ^ 2 := by
      have h1 := sqDist_sub_le hx hy
      have h2 : sqDist x y = ∑ i, (x i - y i) ^ 2 := by
        unfold sqDist; exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsq] at h2
      have h3 : sqDist x z = s ^ 2 * sqDist x y := by rw [hsq]; field_simp
      rw [h3, sqDist_comm x y] at *
      nlinarith [sqDist_nonneg y x, sq_nonneg s, sqDist_nonneg x y]
    rw [Set.indicator_of_mem hzB, Set.indicator_of_mem (show t ∈ {t | sqDist x z ≤
      (2 * r) ^ 2 * (1 - t) ^ 2} from hdz), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by have := sqDist_nonneg x z; have := hH0 z; positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [hsq]
    have hpow : s ^ (-((n : ℝ) + 1)) = (s ^ n)⁻¹ * s⁻¹ := by
      rw [Real.rpow_neg hs.le, Real.rpow_add hs, Real.rpow_natCast, Real.rpow_one, mul_inv]
    rw [hpow]
    field_simp
  · rw [Set.indicator_of_notMem hy, mul_zero]; exact zero_le

/-- **The averaged Taylor remainder is a Riesz potential**:
`∫_B ∫₀¹ (1-t) |x-y|² H(y + t(x-y)) dt dy ≤ ((2r)^n/n) ∫_B H(z) |x - z|^{2-n} dz`. -/
theorem lintegral_remainder_le (hr : 0 < r) {H : (Fin n → ℝ) → ℝ} (hH : Continuous H)
    (hH0 : ∀ z, 0 ≤ H z) {x : Fin n → ℝ} (hx : x ∈ euclBall c r) :
    ∫⁻ y in euclBall c r, ∫⁻ t in Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((1 - t) * (sqDist x y * H (seg x y t))) ≤
      ENNReal.ofReal ((2 * r) ^ n / n) *
        ∫⁻ z in euclBall c r, ENNReal.ofReal (H z * sqDist x z ^ (1 - (n : ℝ) / 2)) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  set Φ : (Fin n → ℝ) → ℝ → ℝ≥0∞ := fun z t =>
    (euclBall c r).indicator (fun z => ENNReal.ofReal (sqDist x z * H z)) z *
      ({t | sqDist x z ≤ (2 * r) ^ 2 * (1 - t) ^ 2}.indicator
        (fun t => ENNReal.ofReal ((1 - t) ^ (-((n : ℝ) + 1)))) t)
  have hΦm : Measurable (Function.uncurry Φ) := by
    have h1 : Measurable fun p : (Fin n → ℝ) × ℝ =>
        (euclBall c r).indicator (fun z => ENNReal.ofReal (sqDist x z * H z)) p.1 :=
      ((Measurable.ennreal_ofReal ((continuous_sqDist x).mul hH).measurable).indicator
        (measurableSet_euclBall c r)).comp measurable_fst
    have hset : MeasurableSet {p : (Fin n → ℝ) × ℝ | sqDist x p.1 ≤ (2 * r) ^ 2 * (1 - p.2) ^ 2} :=
      measurableSet_le ((continuous_sqDist x).comp continuous_fst).measurable
        (continuous_const.mul ((continuous_const.sub continuous_snd).pow 2)).measurable
    have h2 : Measurable fun p : (Fin n → ℝ) × ℝ =>
        ({t | sqDist x p.1 ≤ (2 * r) ^ 2 * (1 - t) ^ 2}.indicator
          (fun t => ENNReal.ofReal ((1 - t) ^ (-((n : ℝ) + 1)))) p.2) := by
      have : (fun p : (Fin n → ℝ) × ℝ => ({t | sqDist x p.1 ≤ (2 * r) ^ 2 * (1 - t) ^ 2}.indicator
          (fun t => ENNReal.ofReal ((1 - t) ^ (-((n : ℝ) + 1)))) p.2)) =
          {p : (Fin n → ℝ) × ℝ | sqDist x p.1 ≤ (2 * r) ^ 2 * (1 - p.2) ^ 2}.indicator
            (fun p => ENNReal.ofReal ((1 - p.2) ^ (-((n : ℝ) + 1)))) := by
        funext p; simp only [Set.indicator, mem_setOf_eq]
      rw [this]
      exact (Measurable.ennreal_ofReal ((measurable_const.sub measurable_snd).pow_const _)).indicator
        hset
    exact h1.mul h2
  have hjoint : Measurable fun p : (Fin n → ℝ) × ℝ =>
      ENNReal.ofReal ((1 - p.2) * (sqDist x p.1 * H (seg x p.1 p.2))) := by
    refine Measurable.ennreal_ofReal (Continuous.measurable ?_)
    have : Continuous fun p : (Fin n → ℝ) × ℝ => seg x p.1 p.2 := by
      unfold seg; fun_prop
    exact (continuous_const.sub continuous_snd).mul (((continuous_sqDist x).comp continuous_fst).mul
      (hH.comp this))
  calc ∫⁻ y in euclBall c r, ∫⁻ t in Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((1 - t) * (sqDist x y * H (seg x y t)))
      = ∫⁻ t in Ioo (0 : ℝ) 1, ∫⁻ y in euclBall c r,
          ENNReal.ofReal ((1 - t) * (sqDist x y * H (seg x y t))) :=
        lintegral_lintegral_swap hjoint.aemeasurable
    _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ∫⁻ z, Φ z t :=
        setLIntegral_mono' measurableSet_Ioo fun t ht => slice_le c hH0 hx ht
    _ = ∫⁻ z, ∫⁻ t in Ioo (0 : ℝ) 1, Φ z t :=
        lintegral_lintegral_swap (hΦm.comp measurable_swap).aemeasurable
    _ ≤ ∫⁻ z, (euclBall c r).indicator (fun z => ENNReal.ofReal ((2 * r) ^ n / n) *
          ENNReal.ofReal (H z * sqDist x z ^ (1 - (n : ℝ) / 2))) z := by
        refine lintegral_mono fun z => ?_
        simp only [Φ]
        rw [lintegral_const_mul' _ _ (by
          by_cases hz : z ∈ euclBall c r <;> simp [Set.indicator, hz])]
        by_cases hz : z ∈ euclBall c r
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
          rcases eq_or_lt_of_le (sqDist_nonneg x z) with h0 | hpos
          · rw [← h0, zero_mul, ENNReal.ofReal_zero, zero_mul]; exact zero_le
          · refine (mul_le_mul' le_rfl (lintegral_cut_le hpos (by linarith : 0 < 2 * r))).trans
              (le_of_eq ?_)
            rw [← ENNReal.ofReal_mul (by have := hH0 z; positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            have hpow : sqDist x z ^ (1 - (n : ℝ) / 2) = sqDist x z * sqDist x z ^ (-(n : ℝ) / 2) := by
              rw [show (1 - (n : ℝ) / 2) = 1 + (-(n : ℝ) / 2) by ring, Real.rpow_add hpos,
                Real.rpow_one]
            rw [hpow]
            field_simp
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]
    _ = ENNReal.ofReal ((2 * r) ^ n / n) *
          ∫⁻ z in euclBall c r, ENNReal.ofReal (H z * sqDist x z ^ (1 - (n : ℝ) / 2)) := by
        rw [lintegral_indicator (measurableSet_euclBall c r), lintegral_const_mul']
        exact ENNReal.ofReal_ne_top

end Potential2

/-! ### The singular weight `|x - z|^{-2}` in four dimensions -/

section Singular

/-- `|w|^{-8/3}` is integrable near the origin of `ℝ⁴`. -/
theorem lintegral_sqDist_rpow_lt_top {R : ℝ} (hR : 0 < R) :
    ∫⁻ w in euclBall (0 : Fin 4 → ℝ) R, ENNReal.ofReal (sqDist 0 w ^ (-(4 : ℝ) / 3)) < ⊤ := by
  -- transfer to `EuclideanSpace`
  have hint : IntegrableOn (fun v : EuclideanSpace ℝ (Fin 4) => ‖v‖ ^ (-(8 : ℝ) / 3))
      (Metric.ball 0 R) := by
    rw [integrableOn_fun_norm_addHaar (μ := volume) (f := fun y : ℝ => y ^ (-(8 : ℝ) / 3))]
    have hc : ContinuousOn (fun y : ℝ => y ^ (1 / 3 : ℝ)) (Icc 0 R) :=
      continuousOn_id.rpow_const fun _ _ => Or.inr (by norm_num)
    have h1 : IntegrableOn (fun y : ℝ => y ^ (1 / 3 : ℝ)) (Ioo 0 R) :=
      (hc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
    refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioo
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
    have hy0 : 0 < y := hy.1
    rw [show (4 - 1 : ℕ) = 3 by norm_num, ← Real.rpow_natCast, ← Real.rpow_add hy0]
    norm_num
  have hlt := hint.setLIntegral_lt_top
  have hmp := PiLp.volume_preserving_ofLp (Fin 4)
  have e : ∫⁻ w in euclBall (0 : Fin 4 → ℝ) R, ENNReal.ofReal (sqDist 0 w ^ (-(4 : ℝ) / 3)) =
      ∫⁻ v in Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) R,
        ENNReal.ofReal (‖v‖ ^ (-(8 : ℝ) / 3)) := by
    rw [← lintegral_indicator (measurableSet_euclBall 0 R),
      ← lintegral_indicator measurableSet_ball]
    rw [← hmp.lintegral_comp_emb (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).symm.measurableEmbedding]
    congr 1; funext v
    have hsq : sqDist 0 (WithLp.ofLp v) = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      simp [sqDist, sq_abs]
    have hmem : WithLp.ofLp v ∈ euclBall (0 : Fin 4 → ℝ) R ↔ v ∈ Metric.ball 0 R := by
      rw [Metric.mem_ball, dist_zero_right]
      show sqDist 0 (WithLp.ofLp v) < R ^ 2 ↔ _
      rw [hsq]
      exact pow_lt_pow_iff_left₀ (norm_nonneg _) hR.le two_ne_zero
    by_cases h : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) R
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mpr h)]
      show ENNReal.ofReal (sqDist 0 (WithLp.ofLp v) ^ (-(4 : ℝ) / 3)) = _
      rw [hsq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      norm_num
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hmem.mp h'))]
  rw [e]; exact hlt

/-- The `L^{4/3}(B)` norm of `|x - ·|^{-2}` is bounded uniformly in `x ∈ B`. -/
theorem lintegral_inv_sqDist_le (c : Fin 4 → ℝ) {r : ℝ} (hr : 0 < r) {x : Fin 4 → ℝ}
    (hx : x ∈ euclBall c r) :
    ∫⁻ z in euclBall c r, ENNReal.ofReal (sqDist x z ^ (-(1 : ℝ))) ^ (4 / 3 : ℝ) ≤
      ∫⁻ w in euclBall (0 : Fin 4 → ℝ) (3 * r), ENNReal.ofReal (sqDist 0 w ^ (-(4 : ℝ) / 3)) := by
  have e1 : ∀ z, ENNReal.ofReal (sqDist x z ^ (-(1 : ℝ))) ^ (4 / 3 : ℝ) =
      ENNReal.ofReal (sqDist x z ^ (-(4 : ℝ) / 3)) := by
    intro z
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (sqDist_nonneg x z) _) (by norm_num),
      ← Real.rpow_mul (sqDist_nonneg x z)]
    norm_num
  simp only [e1]
  have hsub : euclBall c r ⊆ euclBall x (3 * r) := by
    intro z hz
    show sqDist x z < (3 * r) ^ 2
    have := sqDist_sub_le hx hz
    have e : sqDist x z = ∑ i, (x i - z i) ^ 2 := by
      unfold sqDist; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]; nlinarith
  refine (lintegral_mono_set hsub).trans (le_of_eq ?_)
  rw [← lintegral_indicator (measurableSet_euclBall x (3 * r)),
    ← lintegral_indicator (measurableSet_euclBall 0 (3 * r))]
  rw [← lintegral_add_left_eq_self _ x]
  congr 1; funext w
  have hs : sqDist x (x + w) = sqDist 0 w := by simp [sqDist]
  have hm : x + w ∈ euclBall x (3 * r) ↔ w ∈ euclBall 0 (3 * r) := by
    show sqDist x (x + w) < _ ↔ sqDist 0 w < _
    rw [hs]
  simp only [Set.indicator, hm, hs]

end Singular

/-! ### `H³(B) ⊂ L^∞` for smooth functions (four dimensions) -/

section Embedding

variable (c : Fin 4 → ℝ) (r : ℝ)

/-- The `H³(B)` norm of a smooth function (sum of the `L²(B)` norms of all classical partial
derivatives of order `≤ 3`, counted along words). -/
def n3 (u : (Fin 4 → ℝ) → ℝ) : ℝ≥0∞ :=
  eLpNorm u 2 (volume.restrict (euclBall c r)) +
    ∑ i, eLpNorm (pd u i) 2 (volume.restrict (euclBall c r)) +
    ∑ i, ∑ j, eLpNorm (pd (pd u i) j) 2 (volume.restrict (euclBall c r)) +
    ∑ i, ∑ j, ∑ k, eLpNorm (pd (pd (pd u i) j) k) 2 (volume.restrict (euclBall c r))

theorem ofReal_intervalIntegral_eq {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t) :
    ENNReal.ofReal (∫ t in (0 : ℝ)..1, f t) = ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (f t) := by
  rw [intervalIntegral.integral_of_le zero_le_one, ofReal_integral_eq_lintegral_ofReal
    (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self) (Eventually.of_forall hf0),
    setLIntegral_congr Ioo_ae_eq_Ioc.symm]

theorem eLpNorm_one_le_two {f : (Fin 4 → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (euclBall c r))) :
    ∫⁻ y in euclBall c r, ENNReal.ofReal |f y| ≤
      eLpNorm f 2 (volume.restrict (euclBall c r)) * volume (euclBall c r) ^ (1 / 2 : ℝ) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hf
  rw [Measure.restrict_apply_univ] at h
  rw [eLpNorm_one_eq_lintegral_enorm] at h
  refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
  · congr 1; funext y; rw [Real.enorm_eq_ofReal_abs]
  · congr 2; norm_num

/-- **`H³(B) ⊂ L^∞(B)` on balls of `ℝ⁴`, smooth functions**: there is `C` such that
`|u(x)| ≤ C ‖u‖_{H³(B)}` for all `x ∈ B` and all smooth `u`. -/
theorem abs_le_n3 (hr : 0 < r) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : (Fin 4 → ℝ) → ℝ, ContDiff ℝ ∞ u →
    ∀ x ∈ euclBall c r, ENNReal.ofReal |u x| ≤ C * n3 c r u := by
  obtain ⟨CS, hCS⟩ := sobolev_ball_real (n := 4) (by norm_num) (p' := 4) (by norm_num)
  set B := euclBall c r
  set V := volume B
  have hV0 : V ≠ 0 := by
    have hc : c ∈ B := by show sqDist c c < r ^ 2; simp [sqDist]; positivity
    exact ((isOpen_euclBall c r).measure_pos volume ⟨c, hc⟩).ne'
  have hVt : V ≠ ⊤ := (volume_euclBall_lt_top c hr.le).ne
  set K := ∫⁻ w in euclBall (0 : Fin 4 → ℝ) (3 * r), ENNReal.ofReal (sqDist 0 w ^ (-(4 : ℝ) / 3))
  have hKt : K ≠ ⊤ := (lintegral_sqDist_rpow_lt_top (by positivity)).ne
  set S := V ^ (1 / 2 : ℝ)
  have hSt : S ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVt
  set A1 := S + ENNReal.ofReal (2 * r) * S
  set A2 := ENNReal.ofReal ((2 * r) ^ 4 / 4) * K ^ (1 / (4 / 3 : ℝ)) * CS *
    (1 + ENNReal.ofReal r⁻¹)
  refine ⟨V⁻¹ * (A1 + A2), ?_, fun u hu x hx => ?_⟩
  · refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hV0) (ENNReal.add_ne_top.mpr ⟨?_, ?_⟩)
    · exact ENNReal.add_ne_top.mpr ⟨hSt, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSt⟩
    · refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hKt)) ENNReal.coe_ne_top)
        (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩)
  have hu2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hpd : ∀ i, ContDiff ℝ ∞ (pd u i) := fun i => contDiff_pd hu i
  have hpdpd : ∀ i j, ContDiff ℝ ∞ (pd (pd u i) j) := fun i j => contDiff_pd (hpd i) j
  have hpd3 : ∀ i j k, ContDiff ℝ ∞ (pd (pd (pd u i) j) k) := fun i j k =>
    contDiff_pd (hpdpd i j) k
  set H : (Fin 4 → ℝ) → ℝ := fun z => ∑ i, ∑ j, |pd (pd u i) j z|
  have hHc : Continuous H := continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (hpdpd i j).continuous.abs
  have hH0 : ∀ z, 0 ≤ H z := fun z => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    abs_nonneg _
  -- the pointwise bound
  set R : (Fin 4 → ℝ) → ℝ≥0∞ := fun y => ENNReal.ofReal |u y| +
    (∑ i, ENNReal.ofReal (2 * r) * ENNReal.ofReal |pd u i y|) +
    ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * (sqDist x y * H (seg x y t)))
  have hpt : ∀ y ∈ B, ENNReal.ofReal |u x| ≤ R y := by
    intro y hy
    have h := abs_le_taylor_bound hu2 x y
    have hxy : ∀ i, |x i - y i| ≤ 2 * r := by
      intro i
      have h1 := sqDist_sub_le hx hy
      have h2 : (x i - y i) ^ 2 ≤ ∑ k, (x k - y k) ^ 2 :=
        Finset.single_le_sum (f := fun k => (x k - y k) ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ i)
      have h3 : (x i - y i) ^ 2 ≤ (2 * r) ^ 2 := by nlinarith
      exact abs_le_of_sq_le_sq' h3 (by positivity) |> fun h => abs_le.mpr h
    have hcont : Continuous fun t => (1 - t) * (sqDist x y * H (seg x y t)) :=
      (continuous_const.sub continuous_id).mul (continuous_const.mul (hHc.comp (continuous_seg x y)))
    have hnn : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (1 - t) * (sqDist x y * H (seg x y t)) := fun t ht =>
      mul_nonneg (by linarith [ht.2]) (mul_nonneg (sqDist_nonneg x y) (hH0 _))
    have hI0 : 0 ≤ ∫ t in (0 : ℝ)..1, (1 - t) * (sqDist x y * H (seg x y t)) :=
      intervalIntegral.integral_nonneg zero_le_one fun t ht => hnn t ht
    have hI : ENNReal.ofReal (∫ t in (0 : ℝ)..1, (1 - t) * (sqDist x y * H (seg x y t))) ≤
        ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * (sqDist x y * H (seg x y t))) := by
      rw [intervalIntegral.integral_of_le zero_le_one, ofReal_integral_eq_lintegral_ofReal
        (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht =>
          hnn t (Ioc_subset_Icc_self ht))), setLIntegral_congr Ioo_ae_eq_Ioc.symm]
    calc ENNReal.ofReal |u x|
        ≤ ENNReal.ofReal (|u y| + (∑ i, |x i - y i| * |pd u i y|) +
            ∫ t in (0 : ℝ)..1, (1 - t) * (sqDist x y * H (seg x y t))) :=
          ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal |u y| + ∑ i, ENNReal.ofReal (|x i - y i| * |pd u i y|) +
            ENNReal.ofReal (∫ t in (0 : ℝ)..1, (1 - t) * (sqDist x y * H (seg x y t))) := by
          rw [ENNReal.ofReal_add (by positivity) hI0, ENNReal.ofReal_add (abs_nonneg _)
            (Finset.sum_nonneg fun i _ => by positivity),
            ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
      _ ≤ R y := by
          simp only [R]
          gcongr with i
          rw [← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hxy i) (abs_nonneg _))
  -- integrate over the ball
  have hmeas1 : Measurable fun y => ENNReal.ofReal |u y| := hu.continuous.abs.measurable.ennreal_ofReal
  have hmeas2 : Measurable fun y => ∑ i, ENNReal.ofReal (2 * r) * ENNReal.ofReal |pd u i y| :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul
      (hpd i).continuous.abs.measurable.ennreal_ofReal
  have hT : ENNReal.ofReal |u x| * V ≤ ∫⁻ y in B, R y := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' (measurableSet_euclBall c r) hpt
  have hsplit : ∫⁻ y in B, R y = (∫⁻ y in B, ENNReal.ofReal |u y|) +
      (∑ i, ENNReal.ofReal (2 * r) * ∫⁻ y in B, ENNReal.ofReal |pd u i y|) +
      ∫⁻ y in B, ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * (sqDist x y * H (seg x y t))) := by
    simp only [R]
    rw [lintegral_add_left (f := fun y => ENNReal.ofReal |u y| +
        ∑ i, ENNReal.ofReal (2 * r) * ENNReal.ofReal |pd u i y|) (hmeas1.add hmeas2),
      lintegral_add_left (f := fun y => ENNReal.ofReal |u y|) hmeas1,
      lintegral_finsetSum (f := fun i y => ENNReal.ofReal (2 * r) * ENNReal.ofReal |pd u i y|) _
        fun i _ => measurable_const.mul (hpd i).continuous.abs.measurable.ennreal_ofReal]
    rw [Finset.sum_congr rfl fun i _ => lintegral_const_mul _
      (hpd i).continuous.abs.measurable.ennreal_ofReal]
  -- the three terms
  have hT1 := eLpNorm_one_le_two c r (f := u) hu.continuous.aestronglyMeasurable
  have hT2 : ∀ i, ∫⁻ y in B, ENNReal.ofReal |pd u i y| ≤
      eLpNorm (pd u i) 2 (volume.restrict B) * S := fun i =>
    eLpNorm_one_le_two c r (hpd i).continuous.aestronglyMeasurable
  have hT3 := lintegral_remainder_le c hr hHc hH0 hx
  have hpow : (1 - ((4 : ℕ) : ℝ) / 2) = -1 := by norm_num
  rw [hpow] at hT3
  -- Hölder on the potential
  have hhol : ∫⁻ z in B, ENNReal.ofReal (H z * sqDist x z ^ (-1 : ℝ)) ≤
      eLpNorm H 4 (volume.restrict B) * K ^ (1 / (4 / 3 : ℝ)) := by
    have e1 : ∀ z, ENNReal.ofReal (H z * sqDist x z ^ (-1 : ℝ)) =
        ENNReal.ofReal (H z) * ENNReal.ofReal (sqDist x z ^ (-1 : ℝ)) := fun z =>
      ENNReal.ofReal_mul (hH0 z)
    simp only [e1]
    have hconj : (4 : ℝ).HolderConjugate (4 / 3) := by
      rw [Real.holderConjugate_iff_eq_conjExponent (by norm_num)]; norm_num
    have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict B) hconj
      (f := fun z => ENNReal.ofReal (H z)) (g := fun z => ENNReal.ofReal (sqDist x z ^ (-1 : ℝ)))
      hHc.measurable.ennreal_ofReal.aemeasurable
      ((continuous_sqDist x).measurable.pow_const _).ennreal_ofReal.aemeasurable
    refine hh.trans ?_
    gcongr
    · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      refine le_of_eq ?_
      congr 1
      congr 1; funext z
      rw [Real.enorm_eq_ofReal (hH0 z)]; norm_num
    · exact lintegral_inv_sqDist_le c hr hx
  have hHL4 : eLpNorm H 4 (volume.restrict B) ≤
      ∑ i, ∑ j, CS * (∑ k, eLpNorm (pd (pd (pd u i) j) k) 2 (volume.restrict B) +
        ENNReal.ofReal r⁻¹ * eLpNorm (pd (pd u i) j) 2 (volume.restrict B)) := by
    have hs : eLpNorm H 4 (volume.restrict B) ≤
        ∑ i, ∑ j, eLpNorm (pd (pd u i) j) 4 (volume.restrict B) := by
      have h1 : H = ∑ i, fun z => ∑ j, |pd (pd u i) j z| := by
        funext z; simp [H, Finset.sum_apply]
      rw [h1]
      refine (eLpNorm_sum_le (fun i _ => (continuous_finset_sum _ fun j _ =>
        (hpdpd i j).continuous.abs).aestronglyMeasurable) (by norm_num)).trans ?_
      refine Finset.sum_le_sum fun i _ => ?_
      have h2 : (fun z => ∑ j, |pd (pd u i) j z|) = ∑ j, fun z => |pd (pd u i) j z| := by
        funext z; simp [Finset.sum_apply]
      rw [h2]
      refine (eLpNorm_sum_le (fun j _ => (hpdpd i j).continuous.abs.aestronglyMeasurable)
        (by norm_num)).trans ?_
      refine Finset.sum_le_sum fun j _ => le_of_eq ?_
      have := eLpNorm_norm (f := pd (pd u i) j) (p := 4) (μ := volume.restrict B)
      simpa [Real.norm_eq_abs] using this
    refine hs.trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_)
    exact hCS c r hr _ ((hpdpd i j).of_le (by simp))
  -- assembly
  set N0 := eLpNorm u 2 (volume.restrict B)
  set N1 := ∑ i, eLpNorm (pd u i) 2 (volume.restrict B)
  set N2 := ∑ i, ∑ j, eLpNorm (pd (pd u i) j) 2 (volume.restrict B)
  set N3 := ∑ i, ∑ j, ∑ k, eLpNorm (pd (pd (pd u i) j) k) 2 (volume.restrict B)
  have hn3 : n3 c r u = N0 + N1 + N2 + N3 := rfl
  have hHL4' : eLpNorm H 4 (volume.restrict B) ≤ CS * (N3 + ENNReal.ofReal r⁻¹ * N2) := by
    refine hHL4.trans (le_of_eq ?_)
    simp only [N2, N3, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  have hmain : ENNReal.ofReal |u x| * V ≤ (A1 + A2) * n3 c r u := by
    refine hT.trans ?_
    rw [hsplit]
    calc (∫⁻ y in B, ENNReal.ofReal |u y|) +
          (∑ i, ENNReal.ofReal (2 * r) * ∫⁻ y in B, ENNReal.ofReal |pd u i y|) +
          ∫⁻ y in B, ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * (sqDist x y * H (seg x y t)))
        ≤ N0 * S + (∑ i, ENNReal.ofReal (2 * r) * (eLpNorm (pd u i) 2 (volume.restrict B) * S)) +
          ENNReal.ofReal ((2 * r) ^ 4 / 4) * (CS * (N3 + ENNReal.ofReal r⁻¹ * N2) *
            K ^ (1 / (4 / 3 : ℝ))) := by
          have h3 : ∫⁻ y in B, ∫⁻ t in Ioo (0 : ℝ) 1,
              ENNReal.ofReal ((1 - t) * (sqDist x y * H (seg x y t))) ≤
              ENNReal.ofReal ((2 * r) ^ 4 / 4) * (CS * (N3 + ENNReal.ofReal r⁻¹ * N2) *
                K ^ (1 / (4 / 3 : ℝ))) := by
            refine hT3.trans ?_
            have e : ((2 * r) ^ 4 / ((4 : ℕ) : ℝ)) = (2 * r) ^ 4 / 4 := by norm_num
            rw [e]
            exact mul_le_mul' le_rfl (hhol.trans (mul_le_mul' hHL4' le_rfl))
          exact add_le_add (add_le_add hT1 (Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl (hT2 i)))
            h3
      _ = S * N0 + ENNReal.ofReal (2 * r) * S * N1 +
          ENNReal.ofReal ((2 * r) ^ 4 / 4) * K ^ (1 / (4 / 3 : ℝ)) * CS *
            (N3 + ENNReal.ofReal r⁻¹ * N2) := by
          simp only [N1, Finset.mul_sum]
          congr 1
          · congr 1
            · ring
            · exact Finset.sum_congr rfl fun i _ => by ring
          · ring
      _ ≤ S * (N0 + N1 + N2 + N3) + ENNReal.ofReal (2 * r) * S * (N0 + N1 + N2 + N3) +
          ENNReal.ofReal ((2 * r) ^ 4 / 4) * K ^ (1 / (4 / 3 : ℝ)) * CS *
            ((1 + ENNReal.ofReal r⁻¹) * (N0 + N1 + N2 + N3)) := by
          gcongr
          · calc N0 ≤ N0 + N1 := le_self_add
              _ ≤ N0 + N1 + N2 := le_self_add
              _ ≤ N0 + N1 + N2 + N3 := le_self_add
          · calc N1 ≤ N0 + N1 := le_add_self
              _ ≤ N0 + N1 + N2 := le_self_add
              _ ≤ N0 + N1 + N2 + N3 := le_self_add
          · rw [add_mul, one_mul]
            gcongr
            · exact le_add_self
            · calc N2 ≤ N0 + N1 + N2 := le_add_self
                _ ≤ N0 + N1 + N2 + N3 := le_self_add
      _ = (A1 + A2) * n3 c r u := by
          rw [hn3]; simp only [A1, A2]; ring
  rw [mul_assoc, ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hVt)]
  exact hmain

end Embedding

end RenewalGeometry.BallAnalysis.BallReg
