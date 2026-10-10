/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallSobolevEmbedding

/-!
# The Poincaré–Wirtinger inequality on Euclidean balls
  (stage C4, coercivity of the Neumann problem, ball rendering of Uhlenbeck's theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `mem_euclBall_convex`, `integral_ball_affine_le` (**affine change of variables into the
  ball**): `∫_{y∈B} G(s y + (1-s) p) dy ≤ s^{-n} ∫_B G` for `0 < s ≤ 1`, `p ∈ B`, `G ≥ 0`;
* `sq_sub_le_segment_len` (**segment estimate**):
  `(u a - u b)² ≤ |a - b|² ∫_0^1 |∇u|²(b + t(a - b)) dt` (fundamental theorem of calculus along the
  segment and Cauchy–Schwarz);
* `integral_swap_of_continuous`, `integrable_prod_ball`: Fubini for continuous integrands on
  bounded sets;
* `double_integral_sq_sub` (variance identity) and `half_double_le` (the segment from the
  midpoint `(x+y)/2`, integrated with the favourable Jacobian `≥ 2^{-n}`);
* `poincare_wirtinger_ball` (**Poincaré–Wirtinger on a ball**, no compactness): for real `C¹`
  `u` with `∫_{B_r(c)} u = 0`, `∫_{B_r(c)} u² ≤ 2^{n+1} r² ∫_{B_r(c)} |∇u|²`; and the general form
  `poincare_wirtinger_ball'` with the mean subtracted.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-! ### Convexity of balls and an affine change of variables -/

theorem sqDist_convex (c y p : Fin n → ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    sqDist c (s • y + (1 - s) • p) ≤ s * sqDist c y + (1 - s) * sqDist c p := by
  unfold sqDist
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [sq_nonneg (y i - p i), mul_nonneg hs0 (sub_nonneg.mpr hs1)]

theorem mem_euclBall_convex {c y p : Fin n → ℝ} {r : ℝ} (hy : y ∈ euclBall c r)
    (hp : p ∈ euclBall c r) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s • y + (1 - s) • p ∈ euclBall c r := by
  show sqDist c _ < r ^ 2
  have hy' : sqDist c y < r ^ 2 := hy
  have hp' : sqDist c p < r ^ 2 := hp
  refine (sqDist_convex c y p hs0 hs1).trans_lt ?_
  rcases eq_or_lt_of_le hs0 with h | h
  · subst h; simp only [zero_mul, sub_zero, one_mul, zero_add]; exact hp'
  · nlinarith [mul_lt_mul_of_pos_left hy' h, mul_le_mul_of_nonneg_left hp'.le (sub_nonneg.mpr hs1)]

theorem sqDist_sub_le {c x y : Fin n → ℝ} {r : ℝ} (hx : x ∈ euclBall c r)
    (hy : y ∈ euclBall c r) : ∑ i, (x i - y i) ^ 2 ≤ 4 * r ^ 2 := by
  have hx' : sqDist c x < r ^ 2 := hx
  have hy' : sqDist c y < r ^ 2 := hy
  unfold sqDist at hx' hy'
  have : ∑ i, (x i - y i) ^ 2 ≤ ∑ i, (2 * (x i - c i) ^ 2 + 2 * (y i - c i) ^ 2) :=
    Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (x i - c i + (y i - c i))]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
  linarith

variable [NeZero n]

/-- **Affine change of variables into the ball**: for `0 < s ≤ 1`, `p ∈ B` and continuous
`G ≥ 0`, `∫_{y ∈ B} G(s y + (1-s) p) dy ≤ s^{-n} ∫_B G`. -/
theorem integral_ball_affine_le (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {G : (Fin n → ℝ) → ℝ}
    (hG : Continuous G) (hG0 : ∀ x, 0 ≤ G x) {p : Fin n → ℝ} (hp : p ∈ euclBall c r) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∫ y in euclBall c r, G (s • y + (1 - s) • p) ≤ (s ^ n)⁻¹ * ∫ y in euclBall c r, G y := by
  set B := euclBall c r
  set q : Fin n → ℝ := (1 - s) • p
  have hB := measurableSet_euclBall c r
  have hIG : Integrable (B.indicator G) :=
    (integrable_indicator_iff hB).mpr (integrableOn_euclBall hr.le hG)
  have hcomp : Integrable fun y => B.indicator G (s • y + q) := by
    have h1 : Integrable fun z => B.indicator G (z + q) := hIG.comp_add_right q
    exact h1.comp_smul hs0.ne'
  rw [← integral_indicator hB, ← integral_indicator hB]
  calc ∫ y, B.indicator (fun y => G (s • y + q)) y
      ≤ ∫ y, B.indicator G (s • y + q) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => ?_) hcomp
          (Eventually.of_forall fun y => ?_)
        · by_cases hy : y ∈ B
          · simp [hy, hG0]
          · simp [hy]
        · by_cases hy : y ∈ B
          · have hm : s • y + q ∈ B := mem_euclBall_convex hy hp hs0.le hs1
            simp [hy, hm]
          · simp only [indicator_of_notMem hy]
            by_cases hm : s • y + q ∈ B
            · simp [hm, hG0]
            · simp [hm]
    _ = (s ^ n)⁻¹ * ∫ y, B.indicator G y := by
        have := MeasureTheory.Measure.integral_comp_smul_of_nonneg (volume : Measure (Fin n → ℝ))
          (fun z => B.indicator G (z + q)) s (hR := hs0.le)
        rw [this, integral_add_right_eq_self (fun z => B.indicator G z) q, Module.finrank_fin_fun,
          smul_eq_mul]

/-! ### The segment estimate -/

theorem sq_integral_le_integral_sq {h : ℝ → ℝ} (hh : Continuous h) :
    (∫ t in (0 : ℝ)..1, h t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, h t ^ 2 := by
  obtain ⟨I, hI⟩ : ∃ I, (∫ t in (0 : ℝ)..1, h t) = I := ⟨_, rfl⟩
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, (h t - I) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
  have e : ∫ t in (0 : ℝ)..1, (h t - I) ^ 2 =
      (∫ t in (0 : ℝ)..1, h t ^ 2) - 2 * I * (∫ t in (0 : ℝ)..1, h t) + I ^ 2 := by
    have e1 : (fun t => (h t - I) ^ 2) = fun t => h t ^ 2 - 2 * I * h t + I ^ 2 := by
      funext t; ring
    rw [e1, intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    · simp only [sub_zero, one_smul]
    · exact (hh.pow 2).intervalIntegrable _ _
    · exact (continuous_const.mul hh).intervalIntegrable _ _
    · exact ((hh.pow 2).sub (continuous_const.mul hh)).intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
  rw [hI] at e ⊢
  nlinarith

/-- `|∇u|² = Σ_i (∂_i u)²`. -/
def gradSqF (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, pd u i x ^ 2

theorem continuous_gradSqF {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous (gradSqF u) :=
  continuous_finset_sum _ fun i _ => (continuous_pd hu i).pow 2

theorem gradSqF_nonneg (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : 0 ≤ gradSqF u x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Segment estimate**: for `x, y ∈ B_r(c)`,
`(u x - u y)² ≤ 4 r² ∫_0^1 |∇u|²(y + t(x - y)) dt`. -/
theorem sq_sub_le_segment {c x y : Fin n → ℝ} {r : ℝ} (hx : x ∈ euclBall c r)
    (hy : y ∈ euclBall c r) {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) :
    (u x - u y) ^ 2 ≤ 4 * r ^ 2 * ∫ t in (0 : ℝ)..1, gradSqF u (y + t • (x - y)) := by
  set γ : ℝ → Fin n → ℝ := fun t => y + t • (x - y)
  set h : ℝ → ℝ := fun t => ∑ i, (x i - y i) * pd u i (γ t)
  have hγc : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hhc : Continuous h := continuous_finset_sum _ fun i _ =>
    continuous_const.mul ((continuous_pd hu i).comp hγc)
  have hderiv : ∀ t, HasDerivAt (fun t => u (γ t)) (h t) t := by
    intro t
    have hγ : HasDerivAt γ (x - y) t :=
      (((hasDerivAt_id t).smul_const (x - y)).const_add y).congr_deriv (one_smul ℝ _)
    have := ((hu.differentiable (by norm_num)) (γ t)).hasFDerivAt.comp_hasDerivAt t hγ
    refine this.congr_deriv ?_
    rw [fderiv_apply_eq_sum_pd]
    simp only [h, Pi.sub_apply]
  have hFTC : ∫ t in (0 : ℝ)..1, h t = u x - u y := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hhc.intervalIntegrable _ _)]
    simp [γ]
  have hD := sqDist_sub_le hx hy
  have hpt : ∀ t, h t ^ 2 ≤ 4 * r ^ 2 * gradSqF u (γ t) := fun t => by
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => x i - y i)
      (fun i => pd u i (γ t))
    exact hCS.trans (mul_le_mul_of_nonneg_right hD (gradSqF_nonneg u _))
  rw [← hFTC]
  refine (sq_integral_le_integral_sq hhc).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on (by norm_num) ((hhc.pow 2).intervalIntegrable _ _)
    ((continuous_const.mul ((continuous_gradSqF hu).comp hγc)).intervalIntegrable _ _)
    fun t _ => hpt t


/-- Segment estimate with an explicit length: `(u a - u b)² ≤ |a - b|² ∫_0^1 |∇u|²(b + t(a - b)) dt`. -/
theorem sq_sub_le_segment_len {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) (a b : Fin n → ℝ) :
    (u a - u b) ^ 2 ≤ (∑ i, (a i - b i) ^ 2) * ∫ t in (0 : ℝ)..1, gradSqF u (b + t • (a - b)) := by
  set γ : ℝ → Fin n → ℝ := fun t => b + t • (a - b)
  set h : ℝ → ℝ := fun t => ∑ i, (a i - b i) * pd u i (γ t)
  have hγc : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hhc : Continuous h := continuous_finset_sum _ fun i _ =>
    continuous_const.mul ((continuous_pd hu i).comp hγc)
  have hderiv : ∀ t, HasDerivAt (fun t => u (γ t)) (h t) t := by
    intro t
    have hγ : HasDerivAt γ (a - b) t :=
      (((hasDerivAt_id t).smul_const (a - b)).const_add b).congr_deriv (one_smul ℝ _)
    have := ((hu.differentiable (by norm_num)) (γ t)).hasFDerivAt.comp_hasDerivAt t hγ
    refine this.congr_deriv ?_
    rw [fderiv_apply_eq_sum_pd]
    simp only [h, Pi.sub_apply]
  have hFTC : ∫ t in (0 : ℝ)..1, h t = u a - u b := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hhc.intervalIntegrable _ _)]
    simp [γ]
  have hpt : ∀ t, h t ^ 2 ≤ (∑ i, (a i - b i) ^ 2) * gradSqF u (γ t) := fun t =>
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => a i - b i) (fun i => pd u i (γ t))
  rw [← hFTC]
  refine (sq_integral_le_integral_sq hhc).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on (by norm_num) ((hhc.pow 2).intervalIntegrable _ _)
    ((continuous_const.mul ((continuous_gradSqF hu).comp hγc)).intervalIntegrable _ _)
    fun t _ => hpt t

/-! ### Fubini for continuous integrands on bounded sets -/

theorem integral_swap_of_continuous {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X] [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {S : Set X} {T : Set Y} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμ : μ S < ⊤) (hν : ν T < ⊤) {K : Set X} {L : Set Y} (hK : IsCompact K) (hL : IsCompact L)
    (hSK : S ⊆ K) (hTL : T ⊆ L) {F : X → Y → ℝ} (hF : Continuous (Function.uncurry F)) :
    ∫ x in S, ∫ y in T, F x y ∂ν ∂μ = ∫ y in T, ∫ x in S, F x y ∂μ ∂ν := by
  have : IsFiniteMeasure (μ.restrict S) := ⟨by rw [Measure.restrict_apply_univ]; exact hμ⟩
  have : IsFiniteMeasure (ν.restrict T) := ⟨by rw [Measure.restrict_apply_univ]; exact hν⟩
  obtain ⟨C, hC⟩ := (hK.prod hL).exists_bound_of_continuousOn hF.continuousOn
  refine integral_integral_swap (Integrable.of_bound hF.aestronglyMeasurable C ?_)
  rw [Measure.prod_restrict]
  refine ae_restrict_of_forall_mem (hS.prod hT) fun p hp => hC p ⟨hSK hp.1, hTL hp.2⟩

theorem volume_euclBall_lt_top (c : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (euclBall c r) < ⊤ :=
  (measure_mono (euclBall_subset_closedBall c hr)).trans_lt (isCompact_closedBall c r).measure_lt_top

theorem intervalIntegral_eq_Icc (f : ℝ → ℝ) :
    ∫ t in (0 : ℝ)..1, f t = ∫ t in Icc (0 : ℝ) 1, f t := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

/-- Half of the double integral: `∫_{x∈B}∫_{y∈B} (u y - u((x+y)/2))² ≤ 2^n r² |B| ∫_B |∇u|²`. -/
theorem half_double_le (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 1 u) :
    ∫ x in euclBall c r, ∫ y in euclBall c r, (u y - u ((1 / 2 : ℝ) • (x + y))) ^ 2 ≤
      2 ^ n * r ^ 2 * (volume (euclBall c r)).toReal * ∫ y in euclBall c r, gradSqF u y := by
  set B := euclBall c r
  have hB := measurableSet_euclBall c r
  have hBf := volume_euclBall_lt_top c hr.le
  have hG := continuous_gradSqF hu
  have hcu : Continuous u := hu.continuous
  -- for each x ∈ B the inner integral is bounded
  have hinner : ∀ x ∈ B, ∫ y in B, (u y - u ((1 / 2 : ℝ) • (x + y))) ^ 2 ≤
      2 ^ n * r ^ 2 * ∫ y in B, gradSqF u y := by
    intro x hx
    -- the segment from the midpoint `m` to `y`: `m + t (y - m) = s y + (1 - s) x`, `s = (1+t)/2`
    have hseg : ∀ y ∈ B, (u y - u ((1 / 2 : ℝ) • (x + y))) ^ 2 ≤
        r ^ 2 * ∫ t in Icc (0 : ℝ) 1, gradSqF u (((1 + t) / 2) • y + (1 - (1 + t) / 2) • x) := by
      intro y hy
      have h1 := sq_sub_le_segment_len hu y ((1 / 2 : ℝ) • (x + y))
      have hlen : ∑ i, (y i - ((1 / 2 : ℝ) • (x + y)) i) ^ 2 ≤ r ^ 2 := by
        have := sqDist_sub_le hy hx
        have e : ∀ i, (y i - ((1 / 2 : ℝ) • (x + y)) i) ^ 2 = (y i - x i) ^ 2 / 4 := fun i => by
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
        simp only [e, ← Finset.sum_div]
        linarith
      have hpts : ∀ t : ℝ, (1 / 2 : ℝ) • (x + y) + t • (y - (1 / 2 : ℝ) • (x + y)) =
          ((1 + t) / 2) • y + (1 - (1 + t) / 2) • x := fun t => by
        ext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
      simp only [hpts] at h1
      rw [intervalIntegral_eq_Icc] at h1
      have hI0 : 0 ≤ ∫ t in Icc (0 : ℝ) 1, gradSqF u (((1 + t) / 2) • y + (1 - (1 + t) / 2) • x) :=
        setIntegral_nonneg measurableSet_Icc fun t _ => gradSqF_nonneg u _
      exact h1.trans (mul_le_mul_of_nonneg_right hlen hI0)
    have hcont : Continuous (Function.uncurry fun (y : Fin n → ℝ) (t : ℝ) =>
        gradSqF u (((1 + t) / 2) • y + (1 - (1 + t) / 2) • x)) := by
      show Continuous fun p : (Fin n → ℝ) × ℝ =>
        gradSqF u (((1 + p.2) / 2) • p.1 + (1 - (1 + p.2) / 2) • x)
      exact hG.comp (by fun_prop)
    have hint_y : IntegrableOn (fun y => (u y - u ((1 / 2 : ℝ) • (x + y))) ^ 2) B :=
      integrableOn_euclBall hr.le (by fun_prop)
    have hcpar : Continuous fun y => ∫ t in Icc (0 : ℝ) 1,
        gradSqF u (((1 + t) / 2) • y + (1 - (1 + t) / 2) • x) :=
      continuous_parametric_integral_of_continuous hcont isCompact_Icc
    calc ∫ y in B, (u y - u ((1 / 2 : ℝ) • (x + y))) ^ 2
        ≤ ∫ y in B, r ^ 2 * ∫ t in Icc (0 : ℝ) 1,
            gradSqF u (((1 + t) / 2) • y + (1 - (1 + t) / 2) • x) := by
          exact setIntegral_mono_on hint_y (integrableOn_euclBall hr.le
            (continuous_const.mul hcpar)) hB hseg
      _ = r ^ 2 * ∫ t in Icc (0 : ℝ) 1, ∫ y in B,
            gradSqF u (((1 + t) / 2) • y + (1 - (1 + t) / 2) • x) := by
          rw [integral_const_mul]
          congr 1
          exact integral_swap_of_continuous hB measurableSet_Icc hBf
            (by simp [Real.volume_Icc]) (isCompact_closedBall c r) isCompact_Icc
            (euclBall_subset_closedBall c hr.le) subset_rfl hcont
      _ ≤ r ^ 2 * ∫ t in Icc (0 : ℝ) 1, 2 ^ n * ∫ y in B, gradSqF u y := by
          refine mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
            (Eventually.of_forall fun t => setIntegral_nonneg hB fun y _ => gradSqF_nonneg u _)
            continuous_const.integrableOn_Icc
            (ae_restrict_of_forall_mem measurableSet_Icc fun t ht => ?_)) (by positivity)
          · have hs0 : 0 < (1 + t) / 2 := by linarith [ht.1]
            have hs1 : (1 + t) / 2 ≤ 1 := by linarith [ht.2]
            refine (integral_ball_affine_le c hr hG (gradSqF_nonneg u) hx hs0 hs1).trans ?_
            refine mul_le_mul_of_nonneg_right ?_ (setIntegral_nonneg hB fun y _ =>
              gradSqF_nonneg u y)
            rw [inv_le_iff_one_le_mul₀ (by positivity), ← mul_pow]
            exact one_le_pow₀ (by linarith [ht.1])
      _ = 2 ^ n * r ^ 2 * ∫ y in B, gradSqF u y := by
          rw [setIntegral_const, Real.volume_real_Icc_of_le zero_le_one]; simp; ring
  refine (integral_mono_of_nonneg (Eventually.of_forall fun x =>
    setIntegral_nonneg hB fun y _ => sq_nonneg _) (integrableOn_const hBf.ne)
    (ae_restrict_of_forall_mem hB hinner)).trans (le_of_eq ?_)
  rw [setIntegral_const, smul_eq_mul, measureReal_def]
  ring


theorem integrable_prod_ball {c : Fin n → ℝ} {r : ℝ} (hr : 0 < r)
    {F : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} (hF : Continuous F) :
    Integrable F ((volume.restrict (euclBall c r)).prod (volume.restrict (euclBall c r))) := by
  have := isFiniteMeasure_restrict_euclBall c hr.le
  obtain ⟨C, hC⟩ := ((isCompact_closedBall c r).prod (isCompact_closedBall c r)
    ).exists_bound_of_continuousOn hF.continuousOn
  refine Integrable.of_bound hF.aestronglyMeasurable C ?_
  rw [Measure.prod_restrict]
  exact ae_restrict_of_forall_mem ((measurableSet_euclBall c r).prod (measurableSet_euclBall c r))
    fun p hp => hC p ⟨euclBall_subset_closedBall c hr.le hp.1,
      euclBall_subset_closedBall c hr.le hp.2⟩

/-- The variance identity: `∫_B∫_B (u x - u y)² = 2|B| ∫_B u² - 2 (∫_B u)²`. -/
theorem double_integral_sq_sub (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {u : (Fin n → ℝ) → ℝ}
    (hu : Continuous u) :
    ∫ x in euclBall c r, ∫ y in euclBall c r, (u x - u y) ^ 2 =
      2 * (volume (euclBall c r)).toReal * (∫ x in euclBall c r, u x ^ 2) -
        2 * (∫ x in euclBall c r, u x) ^ 2 := by
  have i1 : IntegrableOn u (euclBall c r) := integrableOn_euclBall hr.le hu
  have i2 : IntegrableOn (fun x => u x ^ 2) (euclBall c r) := integrableOn_euclBall hr.le (hu.pow 2)
  have hBf := (volume_euclBall_lt_top c hr.le).ne
  have hin : ∀ x, ∫ y in euclBall c r, (u x - u y) ^ 2 =
      (volume (euclBall c r)).toReal * u x ^ 2 - 2 * u x * (∫ y in euclBall c r, u y) +
        ∫ y in euclBall c r, u y ^ 2 := by
    intro x
    have e : (fun y => (u x - u y) ^ 2) = fun y => (u x ^ 2 - 2 * u x * u y) + u y ^ 2 := by
      funext y; ring
    have hc : IntegrableOn (fun _ : Fin n → ℝ => u x ^ 2) (euclBall c r) := integrableOn_const hBf
    have hd : IntegrableOn (fun y => u x ^ 2 - 2 * u x * u y) (euclBall c r) :=
      hc.sub (i1.const_mul (2 * u x))
    rw [e, integral_add (f := fun y => u x ^ 2 - 2 * u x * u y) (g := fun y => u y ^ 2) hd i2,
      integral_sub (f := fun _ => u x ^ 2) (g := fun y => 2 * u x * u y) hc (i1.const_mul _),
      setIntegral_const, integral_const_mul, smul_eq_mul, measureReal_def]
  have e2 : (fun x => ∫ y in euclBall c r, (u x - u y) ^ 2) = fun x =>
      ((volume (euclBall c r)).toReal * u x ^ 2 - (2 * ∫ y in euclBall c r, u y) * u x) +
        ∫ y in euclBall c r, u y ^ 2 := by
    funext x; rw [hin]; ring
  have hd2 : IntegrableOn (fun x => (volume (euclBall c r)).toReal * u x ^ 2 -
      (2 * ∫ y in euclBall c r, u y) * u x) (euclBall c r) :=
    (i2.const_mul _).sub (i1.const_mul _)
  rw [e2, integral_add (f := fun x => (volume (euclBall c r)).toReal * u x ^ 2 -
      (2 * ∫ y in euclBall c r, u y) * u x) (g := fun _ => ∫ y in euclBall c r, u y ^ 2) hd2
      (integrableOn_const (C := ∫ y in euclBall c r, u y ^ 2) hBf),
    integral_sub (f := fun x => (volume (euclBall c r)).toReal * u x ^ 2)
      (g := fun x => (2 * ∫ y in euclBall c r, u y) * u x) (i2.const_mul _) (i1.const_mul _),
    integral_const_mul, integral_const_mul, setIntegral_const, smul_eq_mul, measureReal_def]
  ring

/-- **The Poincaré–Wirtinger inequality on a Euclidean ball** for real `C¹` functions of mean
zero: `∫_{B_r(c)} u² ≤ 2^{n+1} r² ∫_{B_r(c)} |∇u|²`.  (Segment argument through the midpoint
`(x + y)/2`, an affine change of variables into the ball, Fubini; no compactness.) -/
theorem poincare_wirtinger_ball (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 1 u) (hmean : ∫ x in euclBall c r, u x = 0) :
    ∫ x in euclBall c r, u x ^ 2 ≤ 2 ^ (n + 1) * r ^ 2 * ∫ x in euclBall c r, gradSqF u x := by
  have hcu := hu.continuous
  have hD := double_integral_sq_sub c hr hcu
  rw [hmean, show (2 : ℝ) * 0 ^ 2 = 0 by norm_num, sub_zero] at hD
  -- the pointwise splitting through the midpoint
  have hm : Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) => (1 / 2 : ℝ) • (p.1 + p.2) := by
    fun_prop
  have hf1 : Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (u p.1 - u ((1 / 2 : ℝ) • (p.1 + p.2))) ^ 2 :=
    ((hcu.comp continuous_fst).sub (hcu.comp hm)).pow 2
  have hf2 : Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (u p.2 - u ((1 / 2 : ℝ) • (p.1 + p.2))) ^ 2 :=
    ((hcu.comp continuous_snd).sub (hcu.comp hm)).pow 2
  have hf0 : Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) => (u p.1 - u p.2) ^ 2 :=
    ((hcu.comp continuous_fst).sub (hcu.comp continuous_snd)).pow 2
  have I0 := integrable_prod_ball (c := c) hr hf0
  have I1 := integrable_prod_ball (c := c) hr hf1
  have I2 := integrable_prod_ball (c := c) hr hf2
  have hsplit : ∫ p, (u p.1 - u p.2) ^ 2 ∂((volume.restrict (euclBall c r)).prod
        (volume.restrict (euclBall c r))) ≤
      2 * ∫ p, (u p.1 - u ((1 / 2 : ℝ) • (p.1 + p.2))) ^ 2 ∂((volume.restrict (euclBall c r)).prod
        (volume.restrict (euclBall c r))) +
      2 * ∫ p, (u p.2 - u ((1 / 2 : ℝ) • (p.1 + p.2))) ^ 2 ∂((volume.restrict (euclBall c r)).prod
        (volume.restrict (euclBall c r))) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (I1.const_mul 2)
      (I2.const_mul 2)]
    refine integral_mono I0 ((I1.const_mul 2).add (I2.const_mul 2)) fun p => ?_
    simp only
    nlinarith [sq_nonneg (u p.1 + u p.2 - 2 * u ((1 / 2 : ℝ) • (p.1 + p.2)))]
  have hH := half_double_le c hr hu
  have h2 : ∫ p, (u p.2 - u ((1 / 2 : ℝ) • (p.1 + p.2))) ^ 2 ∂((volume.restrict
        (euclBall c r)).prod (volume.restrict (euclBall c r))) ≤
      2 ^ n * r ^ 2 * (volume (euclBall c r)).toReal * ∫ y in euclBall c r, gradSqF u y := by
    rw [integral_prod _ I2]
    exact hH
  have h1 : ∫ p, (u p.1 - u ((1 / 2 : ℝ) • (p.1 + p.2))) ^ 2 ∂((volume.restrict
        (euclBall c r)).prod (volume.restrict (euclBall c r))) ≤
      2 ^ n * r ^ 2 * (volume (euclBall c r)).toReal * ∫ y in euclBall c r, gradSqF u y := by
    have I1s : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        (u z.swap.1 - u ((1 / 2 : ℝ) • (z.swap.1 + z.swap.2))) ^ 2)
        ((volume.restrict (euclBall c r)).prod (volume.restrict (euclBall c r))) :=
      integrable_prod_ball hr (by fun_prop)
    rw [← integral_prod_swap, integral_prod _ I1s]
    have e : ∀ x y : Fin n → ℝ, (u (x, y).swap.1 - u ((1 / 2 : ℝ) • ((x, y).swap.1 +
        (x, y).swap.2))) ^ 2 = (u y - u ((1 / 2 : ℝ) • (x + y))) ^ 2 := fun x y => by
      simp only [Prod.swap_prod_mk, add_comm y x]
    simp only [e]
    exact hH
  rw [← integral_prod _ I0] at hD
  have key : 2 * (volume (euclBall c r)).toReal * ∫ x in euclBall c r, u x ^ 2 ≤
      4 * (2 ^ n * r ^ 2 * (volume (euclBall c r)).toReal *
        ∫ y in euclBall c r, gradSqF u y) := by
    have := hsplit.trans (add_le_add (mul_le_mul_of_nonneg_left h1 zero_le_two)
      (mul_le_mul_of_nonneg_left h2 zero_le_two))
    rw [hD] at this
    linarith
  have hpos : 0 < (volume (euclBall c r)).toReal := by
    refine ENNReal.toReal_pos ?_ (volume_euclBall_lt_top c hr.le).ne
    have hc : c ∈ euclBall c r := by show sqDist c c < r ^ 2; simp [sqDist]; positivity
    exact ((isOpen_euclBall c r).measure_pos volume ⟨c, hc⟩).ne'
  have e4 : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  rw [e4]
  have hG0 : 0 ≤ ∫ y in euclBall c r, gradSqF u y := setIntegral_nonneg (measurableSet_euclBall c r)
    fun y _ => gradSqF_nonneg u y
  have hU0 : 0 ≤ ∫ x in euclBall c r, u x ^ 2 := setIntegral_nonneg (measurableSet_euclBall c r)
    fun y _ => sq_nonneg _
  nlinarith

theorem gradSqF_sub_const (u : (Fin n → ℝ) → ℝ) (k : ℝ) (hu : ContDiff ℝ 1 u) (x : Fin n → ℝ) :
    gradSqF (fun y => u y - k) x = gradSqF u x := by
  unfold gradSqF
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pd_sub_real ((hu.differentiable (by norm_num)) x) (differentiableAt_const k)]
  simp [pd]

/-- **Poincaré–Wirtinger on a ball**, general form: with `ū = |B|⁻¹ ∫_B u`,
`∫_B (u - ū)² ≤ 2^{n+1} r² ∫_B |∇u|²`. -/
theorem poincare_wirtinger_ball' (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 1 u) :
    ∫ x in euclBall c r, (u x - (volume (euclBall c r)).toReal⁻¹ * ∫ y in euclBall c r, u y) ^ 2 ≤
      2 ^ (n + 1) * r ^ 2 * ∫ x in euclBall c r, gradSqF u x := by
  set k := (volume (euclBall c r)).toReal⁻¹ * ∫ y in euclBall c r, u y
  have hpos : 0 < (volume (euclBall c r)).toReal := by
    refine ENNReal.toReal_pos ?_ (volume_euclBall_lt_top c hr.le).ne
    have hc : c ∈ euclBall c r := by show sqDist c c < r ^ 2; simp [sqDist]; positivity
    exact ((isOpen_euclBall c r).measure_pos volume ⟨c, hc⟩).ne'
  have hmean : ∫ x in euclBall c r, (u x - k) = 0 := by
    rw [integral_sub (integrableOn_euclBall hr.le hu.continuous)
      (integrableOn_const (volume_euclBall_lt_top c hr.le).ne), setIntegral_const, smul_eq_mul,
      measureReal_def]
    simp only [k]
    field_simp
    ring
  have h := poincare_wirtinger_ball c hr (hu.sub contDiff_const) hmean
  simp only [gradSqF_sub_const u k hu] at h
  exact h

end RenewalGeometry.BallAnalysis
