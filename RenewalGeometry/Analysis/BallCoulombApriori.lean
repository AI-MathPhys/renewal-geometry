/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallSobolevEmbedding
import RenewalGeometry.Analysis.CovariantGradientCompactness
import RenewalGeometry.Analysis.CoulombHodgeAbsorption

/-!
# The critical Coulomb a-priori estimate on Euclidean balls of `ℝ⁴`
  (stage C3 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript (Uhlenbeck, CMP 83 (1982), the closedness
estimate of Thm 2.1/2.2 on a ball, classical rendering).

* `eLpNorm_pd_le_curl_ball` (**Hodge estimate on a ball**): for a co-closed complex `C²` one-form
  with vanishing normal component on `∂B_r(c)`,
  `‖∂_μ w_ν‖_{L²(B)} ≤ Σ_{μ'ν'} ‖∂_{μ'}w_{ν'} - ∂_{ν'}w_{μ'}‖_{L²(B)}` (Gaffney's inequality);
* `eLpNorm_le_curl_ball` (**Poincaré**): `‖w_ν‖_{L²(B_r)} ≤ r Σ_{μ'ν'} ‖curl‖_{L²(B_r)}`;
* matrix-valued forms on `B_r(o) ⊂ ℝ⁴`: curvature `bCurv` (`F = da + [a ∧ a]`), the class
  `IsBallCoulomb o r a` (`C²`, `d^*a = 0` on the ball, `(x - o)·a = 0` on the sphere), the norms
  `bL4`, `bGradNorm`, `bCurvNorm` (sums of entry norms on the ball);
* `coulomb_apriori_ball` (**the critical Coulomb a-priori estimate on balls**, no mean-zero
  hypothesis, constants depending only on the matrix size): if `Σ‖a‖_{L⁴(B)} ≤ δ` then
  `Σ‖a‖_{L⁴(B)} ≤ C ‖F_a‖_{L²(B)}`, `Σ‖∇a‖_{L²(B)} ≤ 32 m² ‖F_a‖_{L²(B)}`,
  `‖a_{ν,ce}‖_{L²(B_r)} ≤ 2r ‖F_a‖_{L²(B_r)}`;
* non-vacuity: the zero form and the rotation field `(-x₁, x₀, 0, 0)` are in `IsBallCoulomb`.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ} [NeZero n]

/-! ### `L²` Hodge and Poincaré estimates for co-closed tangential forms on balls -/

theorem eLpNorm_two_sq_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : Integrable (fun x => ‖f x‖ ^ 2) μ) :
    eLpNorm f 2 μ ^ 2 = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  rw [eLpNorm_two_eq_ofReal hf, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem sum_sq_le_sq_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [sq]
  exact Finset.single_le_sum (f := fun j => f i * f j) (fun _ _ => zero_le) hi

theorem sum_sum_sq_le {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ → ℝ≥0∞) :
    ∑ i, ∑ j, f i j ^ 2 ≤ (∑ i, ∑ j, f i j) ^ 2 :=
  (Finset.sum_le_sum fun i _ => sum_sq_le_sq_sum _ (f i)).trans (sum_sq_le_sq_sum _ _)

/-- The curl components `∂_{μ'} w_{ν'} - ∂_{ν'} w_{μ'}` of a complex one-form. -/
def curlC (w : Fin n → (Fin n → ℝ) → ℂ) (μ' ν' : Fin n) (x : Fin n → ℝ) : ℂ :=
  pd (w ν') μ' x - pd (w μ') ν' x

theorem continuous_curlC {w : Fin n → (Fin n → ℝ) → ℂ} (hw : ∀ ν, ContDiff ℝ 1 (w ν))
    (μ' ν' : Fin n) : Continuous (curlC w μ' ν') :=
  (continuous_pd (hw ν') μ').sub (continuous_pd (hw μ') ν')

/-- `∫_B Σ‖curl‖² = Σ ‖curl_{μ'ν'}‖²_{L²(B)}`. -/
theorem ofReal_integral_curlSqC {c : Fin n → ℝ} {r : ℝ} (hr : 0 < r)
    {w : Fin n → (Fin n → ℝ) → ℂ} (hw : ∀ ν, ContDiff ℝ 1 (w ν)) :
    ENNReal.ofReal (∫ x in euclBall c r, curlSqC w x) =
      ∑ μ', ∑ ν', eLpNorm (curlC w μ' ν') 2 (volume.restrict (euclBall c r)) ^ 2 := by
  have hc : ∀ μ' ν', Continuous fun x => ‖curlC w μ' ν' x‖ ^ 2 := fun μ' ν' =>
    (continuous_curlC hw μ' ν').norm.pow 2
  have e : ∫ x in euclBall c r, curlSqC w x =
      ∑ μ', ∑ ν', ∫ x in euclBall c r, ‖curlC w μ' ν' x‖ ^ 2 := by
    have e' : curlSqC w = fun x => ∑ μ', ∑ ν', ‖curlC w μ' ν' x‖ ^ 2 := rfl
    rw [e', integral_finset_sum (f := fun μ' x => ∑ ν', ‖curlC w μ' ν' x‖ ^ 2) _
      fun μ' _ => integrableOn_euclBall hr.le (continuous_finset_sum _ fun ν' _ => hc μ' ν')]
    refine Finset.sum_congr rfl fun μ' _ => ?_
    exact integral_finset_sum _ fun ν' _ => integrableOn_euclBall hr.le (hc μ' ν')
  rw [e, ENNReal.ofReal_sum_of_nonneg fun μ' _ => Finset.sum_nonneg fun ν' _ =>
    setIntegral_nonneg (measurableSet_euclBall c r) fun x _ => by positivity]
  refine Finset.sum_congr rfl fun μ' _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun ν' _ =>
    setIntegral_nonneg (measurableSet_euclBall c r) fun x _ => by positivity]
  refine Finset.sum_congr rfl fun ν' _ => ?_
  rw [eLpNorm_two_sq_eq (integrableOn_euclBall hr.le (hc μ' ν'))]

/-- **Hodge estimate on a ball** for a co-closed (`div w = 0` on `B`) complex `C²` one-form with
vanishing normal component on `∂B`: `‖∂_μ w_ν‖_{L²(B)} ≤ Σ_{μ'ν'} ‖∂_{μ'}w_{ν'} - ∂_{ν'}w_{μ'}‖_{L²(B)}`
(from Gaffney's inequality). -/
theorem eLpNorm_pd_le_curl_ball (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    {w : Fin n → (Fin n → ℝ) → ℂ} (hw : ∀ ν, ContDiff ℝ 2 (w ν))
    (hS : ∀ y, sqDist c y = r ^ 2 → ∑ μ, ((y μ - c μ : ℝ) : ℂ) * w μ y = 0)
    (hdiv : ∀ x ∈ euclBall c r, divC w x = 0) (ν μ : Fin n) :
    eLpNorm (pd (w ν) μ) 2 (volume.restrict (euclBall c r)) ≤
      ∑ μ', ∑ ν', eLpNorm (curlC w μ' ν') 2 (volume.restrict (euclBall c r)) := by
  have hw1 : ∀ ν, ContDiff ℝ 1 (w ν) := fun ν => (hw ν).of_le (by norm_num)
  have hB := measurableSet_euclBall c r
  have hcg : Continuous (gradSqC w) := by
    unfold gradSqC
    exact continuous_finset_sum _ fun μ _ => continuous_finset_sum _ fun ν _ =>
      (continuous_pd (hw1 ν) μ).norm.pow 2
  have hcc : Continuous (curlSqC w) := by
    unfold curlSqC
    exact continuous_finset_sum _ fun μ _ => continuous_finset_sum _ fun ν _ =>
      ((continuous_pd (hw1 ν) μ).sub (continuous_pd (hw1 μ) ν)).norm.pow 2
  have h1 : ∫ x in euclBall c r, ‖pd (w ν) μ x‖ ^ 2 ≤ ∫ x in euclBall c r, gradSqC w x := by
    refine setIntegral_mono_on (integrableOn_euclBall hr.le ((continuous_pd (hw1 ν) μ).norm.pow 2))
      (integrableOn_euclBall hr.le hcg) hB fun x _ => ?_
    unfold gradSqC
    refine (Finset.single_le_sum (f := fun ν' => ‖pd (w ν') μ x‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ ν)).trans ?_
    exact Finset.single_le_sum (f := fun μ' => ∑ ν', ‖pd (w ν') μ' x‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ μ)
  have h2 : ∫ x in euclBall c r, gradSqC w x ≤ ∫ x in euclBall c r, curlSqC w x := by
    refine (gaffney_ball_complex c hr hw hS).trans ?_
    have hcd : Continuous (divC w) := by
      unfold divC; exact continuous_finset_sum _ fun μ _ => (continuous_pd (hw1 μ) μ)
    refine setIntegral_mono_on (integrableOn_euclBall hr.le
      ((hcc.div_const 2).add (hcd.norm.pow 2)))
      (integrableOn_euclBall hr.le hcc) hB fun x hx => ?_
    rw [hdiv x hx, norm_zero]
    have : 0 ≤ curlSqC w x := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
      positivity
    linarith
  have h3 : eLpNorm (pd (w ν) μ) 2 (volume.restrict (euclBall c r)) ^ 2 ≤
      (∑ μ', ∑ ν', eLpNorm (curlC w μ' ν') 2 (volume.restrict (euclBall c r))) ^ 2 := by
    rw [eLpNorm_two_sq_eq (integrableOn_euclBall hr.le ((continuous_pd (hw1 ν) μ).norm.pow 2))]
    refine (ENNReal.ofReal_le_ofReal (h1.trans h2)).trans ?_
    rw [ofReal_integral_curlSqC hr hw1]
    exact sum_sum_sq_le _
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).mp h3

/-- **Poincaré estimate on a ball** for a co-closed tangential complex `C²` one-form:
`‖w_ν‖_{L²(B_r)} ≤ r Σ_{μ'ν'} ‖∂_{μ'}w_{ν'} - ∂_{ν'}w_{μ'}‖_{L²(B_r)}` (`n ≥ 2`). -/
theorem eLpNorm_le_curl_ball (hn : 2 ≤ n) (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    {w : Fin n → (Fin n → ℝ) → ℂ} (hw : ∀ ν, ContDiff ℝ 2 (w ν))
    (hS : ∀ y, sqDist c y = r ^ 2 → ∑ μ, ((y μ - c μ : ℝ) : ℂ) * w μ y = 0)
    (hdiv : ∀ x ∈ euclBall c r, divC w x = 0) (ν : Fin n) :
    eLpNorm (w ν) 2 (volume.restrict (euclBall c r)) ≤
      ENNReal.ofReal r * ∑ μ', ∑ ν', eLpNorm (curlC w μ' ν') 2 (volume.restrict (euclBall c r)) := by
  have hw1 : ∀ ν, ContDiff ℝ 1 (w ν) := fun ν => (hw ν).of_le (by norm_num)
  have hB := measurableSet_euclBall c r
  have hcc : Continuous (curlSqC w) := by
    unfold curlSqC
    exact continuous_finset_sum _ fun μ _ => continuous_finset_sum _ fun ν _ =>
      ((continuous_pd (hw1 ν) μ).sub (continuous_pd (hw1 μ) ν)).norm.pow 2
  have hcn : Continuous (normSqC w) := by
    unfold normSqC
    exact continuous_finset_sum _ fun ν _ => (hw1 ν).continuous.norm.pow 2
  have hP := poincare_ball_complex c hr hw hS
  have hdivI : ∫ x in euclBall c r, (curlSqC w x / 2 + ‖divC w x‖ ^ 2) =
      ∫ x in euclBall c r, curlSqC w x / 2 :=
    setIntegral_congr_fun hB fun x hx => by rw [hdiv x hx, norm_zero]; ring
  rw [hdivI, integral_div] at hP
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hI0 : 0 ≤ ∫ x in euclBall c r, normSqC w x :=
    setIntegral_nonneg hB fun x _ => Finset.sum_nonneg fun _ _ => by positivity
  have hC0 : 0 ≤ ∫ x in euclBall c r, curlSqC w x :=
    setIntegral_nonneg hB fun x _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
      positivity
  have h1 : ∫ x in euclBall c r, ‖w ν x‖ ^ 2 ≤ ∫ x in euclBall c r, normSqC w x := by
    refine setIntegral_mono_on (integrableOn_euclBall hr.le ((hw1 ν).continuous.norm.pow 2))
      (integrableOn_euclBall hr.le hcn) hB fun x _ => ?_
    exact Finset.single_le_sum (f := fun ν' => ‖w ν' x‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ ν)
  have h2 : ∫ x in euclBall c r, ‖w ν x‖ ^ 2 ≤ r ^ 2 * ∫ x in euclBall c r, curlSqC w x := by
    refine h1.trans ?_
    have : ∫ x in euclBall c r, normSqC w x ≤
        ((n : ℝ) - 1) * ∫ x in euclBall c r, normSqC w x := le_mul_of_one_le_left hI0 hn1
    nlinarith [sq_nonneg r]
  have h3 : eLpNorm (w ν) 2 (volume.restrict (euclBall c r)) ^ 2 ≤
      (ENNReal.ofReal r * ∑ μ', ∑ ν', eLpNorm (curlC w μ' ν') 2
        (volume.restrict (euclBall c r))) ^ 2 := by
    rw [eLpNorm_two_sq_eq (integrableOn_euclBall hr.le ((hw1 ν).continuous.norm.pow 2))]
    refine (ENNReal.ofReal_le_ofReal h2).trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ofReal_integral_curlSqC hr hw1, mul_pow,
      ENNReal.ofReal_pow hr.le]
    gcongr
    exact sum_sum_sq_le _
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).mp h3


/-! ### Matrix-valued Coulomb forms on a ball in `ℝ⁴` -/

section Matrix

variable {m : ℕ}

/-- The commutator `[a_μ, a_ν]_{ce} = Σ_k (a_{μ,ck} a_{ν,ke} - a_{ν,ck} a_{μ,ke})`. -/
def bComm (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ) (μ ν : Fin 4) (c e : Fin m)
    (x : Fin 4 → ℝ) : ℂ :=
  ∑ k, (a μ c k x * a ν k e x - a ν c k x * a μ k e x)

/-- The curvature entries `F_{μν,ce} = ∂_μ a_{ν,ce} - ∂_ν a_{μ,ce} + [a_μ, a_ν]_{ce}` of a
classical matrix-valued one-form (the convention of `CubeNeumann.cCurv`). -/
def bCurv (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ) (μ ν : Fin 4) (c e : Fin m)
    (x : Fin 4 → ℝ) : ℂ :=
  pd (a ν c e) μ x - pd (a μ c e) ν x + bComm a μ ν c e x

/-- The `(c,e)` entry of a matrix-valued one-form, as a complex one-form. -/
def entryForm (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ) (c e : Fin m) :
    Fin 4 → (Fin 4 → ℝ) → ℂ := fun ν => a ν c e

/-- **Coulomb forms on a ball with vanishing normal component** (the Neumann–Coulomb gauge
condition of Uhlenbeck's theorem on `B_r(o)`), classical version: `C²` entries,
`(x - o)·a = 0` on `∂B_r(o)`, `d^*a = 0` on `B_r(o)`. -/
structure IsBallCoulomb (o : Fin 4 → ℝ) (r : ℝ) (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ) :
    Prop where
  smooth : ∀ ν c e, ContDiff ℝ 2 (a ν c e)
  tangent : ∀ y, sqDist o y = r ^ 2 → ∀ c e, ∑ μ, ((y μ - o μ : ℝ) : ℂ) * a μ c e y = 0
  coulomb : ∀ x ∈ euclBall o r, ∀ c e, ∑ μ, pd (a μ c e) μ x = 0

/-- `Σ_{νce} ‖a_{ν,ce}‖_{L⁴(B)}`. -/
def bL4 (o : Fin 4 → ℝ) (r : ℝ) (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ) : ℝ≥0∞ :=
  ∑ ν, ∑ c, ∑ e, eLpNorm (a ν c e) 4 (volume.restrict (euclBall o r))

/-- `Σ_{νceμ} ‖∂_μ a_{ν,ce}‖_{L²(B)}`. -/
def bGradNorm (o : Fin 4 → ℝ) (r : ℝ) (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ) : ℝ≥0∞ :=
  ∑ ν, ∑ c, ∑ e, ∑ μ, eLpNorm (pd (a ν c e) μ) 2 (volume.restrict (euclBall o r))

/-- `Σ_{μνce} ‖F_{μν,ce}‖_{L²(B)}`. -/
def bCurvNorm (o : Fin 4 → ℝ) (r : ℝ) (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ) : ℝ≥0∞ :=
  ∑ μ, ∑ ν, ∑ c, ∑ e, eLpNorm (bCurv a μ ν c e) 2 (volume.restrict (euclBall o r))

theorem curlC_entryForm (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ) (c e : Fin m)
    (μ' ν' : Fin 4) (x : Fin 4 → ℝ) :
    curlC (entryForm a c e) μ' ν' x = bCurv a μ' ν' c e x - bComm a μ' ν' c e x := by
  simp only [curlC, entryForm, bCurv]; ring

theorem le_bL4 (o : Fin 4 → ℝ) (r : ℝ) (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
    (ν : Fin 4) (c e : Fin m) :
    eLpNorm (a ν c e) 4 (volume.restrict (euclBall o r)) ≤ bL4 o r a :=
  (Finset.single_le_sum (f := fun e => eLpNorm (a ν c e) 4 (volume.restrict (euclBall o r)))
    (fun _ _ => zero_le) (Finset.mem_univ e)).trans
    ((Finset.single_le_sum (f := fun c => ∑ e, eLpNorm (a ν c e) 4 (volume.restrict (euclBall o r)))
      (fun _ _ => zero_le) (Finset.mem_univ c)).trans
    (Finset.single_le_sum (f := fun ν => ∑ c, ∑ e,
      eLpNorm (a ν c e) 4 (volume.restrict (euclBall o r))) (fun _ _ => zero_le)
      (Finset.mem_univ ν)))

theorem sum_curv_le_bCurvNorm (o : Fin 4 → ℝ) (r : ℝ)
    (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ) (c e : Fin m) :
    ∑ μ', ∑ ν', eLpNorm (bCurv a μ' ν' c e) 2 (volume.restrict (euclBall o r)) ≤
      bCurvNorm o r a := by
  unfold bCurvNorm
  refine Finset.sum_le_sum fun μ' _ => Finset.sum_le_sum fun ν' _ => ?_
  exact (Finset.single_le_sum (f := fun e => eLpNorm (bCurv a μ' ν' c e) 2
      (volume.restrict (euclBall o r))) (fun _ _ => zero_le) (Finset.mem_univ e)).trans
    (Finset.single_le_sum (f := fun c => ∑ e, eLpNorm (bCurv a μ' ν' c e) 2
      (volume.restrict (euclBall o r))) (fun _ _ => zero_le) (Finset.mem_univ c))

/-- Hölder for the commutator on the ball: `‖[a_μ,a_ν]_{ce}‖_{L²(B)} ≤ 2m (Σ‖a‖_{L⁴(B)})²`. -/
theorem eLpNorm_bComm_le (o : Fin 4 → ℝ) (r : ℝ) {a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ}
    (ha : ∀ ν c e, Continuous (a ν c e)) (μ ν : Fin 4) (c e : Fin m) :
    eLpNorm (bComm a μ ν c e) 2 (volume.restrict (euclBall o r)) ≤
      2 * m * (bL4 o r a * bL4 o r a) := by
  set ρ := volume.restrict (euclBall o r)
  have ham : ∀ ν c e, AEStronglyMeasurable (a ν c e) ρ := fun ν c e =>
    (ha ν c e).aestronglyMeasurable
  have e' : bComm a μ ν c e =
      ∑ k, (fun x => a μ c k x * a ν k e x - a ν c k x * a μ k e x) := by
    funext x; simp only [bComm, Finset.sum_apply]
  rw [e']
  refine (eLpNorm_sum_le (f := fun k x => a μ c k x * a ν k e x - a ν c k x * a μ k e x)
    (fun k _ => ((ham μ c k).mul (ham ν k e)).sub ((ham ν c k).mul (ham μ k e)))
    (by norm_num)).trans ?_
  calc ∑ k, eLpNorm (fun x => a μ c k x * a ν k e x - a ν c k x * a μ k e x) 2 ρ
      ≤ ∑ _k : Fin m, (bL4 o r a * bL4 o r a + bL4 o r a * bL4 o r a) := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine (eLpNorm_sub_le ((ham μ c k).mul (ham ν k e)) ((ham ν c k).mul (ham μ k e))
          (by norm_num)).trans (add_le_add ?_ ?_)
        · exact (eLpNorm_mul_le_L4 (ham μ c k) (ham ν k e)).trans
            (mul_le_mul' (le_bL4 o r a μ c k) (le_bL4 o r a ν k e))
        · exact (eLpNorm_mul_le_L4 (ham ν c k) (ham μ k e)).trans
            (mul_le_mul' (le_bL4 o r a ν c k) (le_bL4 o r a μ k e))
    _ = 2 * m * (bL4 o r a * bL4 o r a) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The curl of each entry is bounded by the curvature and the quadratic term. -/
theorem sum_curl_entry_le (o : Fin 4 → ℝ) (r : ℝ)
    {a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ} (ha : ∀ ν c e, ContDiff ℝ 1 (a ν c e))
    (c e : Fin m) :
    ∑ μ', ∑ ν', eLpNorm (curlC (entryForm a c e) μ' ν') 2 (volume.restrict (euclBall o r)) ≤
      bCurvNorm o r a + 32 * m * (bL4 o r a * bL4 o r a) := by
  set ρ := volume.restrict (euclBall o r)
  have hcont : ∀ μ' ν', Continuous (bComm a μ' ν' c e) := fun μ' ν' => by
    unfold bComm
    exact continuous_finset_sum _ fun k _ => (((ha μ' c k).continuous.mul (ha ν' k e).continuous).sub
      ((ha ν' c k).continuous.mul (ha μ' k e).continuous))
  have hcurv : ∀ μ' ν', Continuous (bCurv a μ' ν' c e) := fun μ' ν' =>
    ((continuous_pd (ha ν' c e) μ').sub (continuous_pd (ha μ' c e) ν')).add (hcont μ' ν')
  have h1 : ∀ μ' ν', eLpNorm (curlC (entryForm a c e) μ' ν') 2 ρ ≤
      eLpNorm (bCurv a μ' ν' c e) 2 ρ + 2 * m * (bL4 o r a * bL4 o r a) := fun μ' ν' => by
    have e1 : curlC (entryForm a c e) μ' ν' = fun x => bCurv a μ' ν' c e x - bComm a μ' ν' c e x :=
      funext (curlC_entryForm a c e μ' ν')
    rw [e1]
    exact (eLpNorm_sub_le (hcurv μ' ν').aestronglyMeasurable (hcont μ' ν').aestronglyMeasurable
      (by norm_num)).trans (add_le_add le_rfl
        (eLpNorm_bComm_le o r (fun ν c e => (ha ν c e).continuous) μ' ν' c e))
  calc ∑ μ', ∑ ν', eLpNorm (curlC (entryForm a c e) μ' ν') 2 ρ
      ≤ ∑ μ', ∑ ν', (eLpNorm (bCurv a μ' ν' c e) 2 ρ + 2 * m * (bL4 o r a * bL4 o r a)) :=
        Finset.sum_le_sum fun μ' _ => Finset.sum_le_sum fun ν' _ => h1 μ' ν'
    _ = ∑ μ', ∑ ν', eLpNorm (bCurv a μ' ν' c e) 2 ρ + 32 * m * (bL4 o r a * bL4 o r a) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring
    _ ≤ bCurvNorm o r a + 32 * m * (bL4 o r a * bL4 o r a) := by
        gcongr; exact sum_curv_le_bCurvNorm o r a c e

theorem entry_hyps {o : Fin 4 → ℝ} {r : ℝ} {a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ}
    (ha : IsBallCoulomb o r a) (c e : Fin m) :
    (∀ ν, ContDiff ℝ 2 (entryForm a c e ν)) ∧
      (∀ y, sqDist o y = r ^ 2 → ∑ μ, ((y μ - o μ : ℝ) : ℂ) * entryForm a c e μ y = 0) ∧
      (∀ x ∈ euclBall o r, divC (entryForm a c e) x = 0) :=
  ⟨fun ν => ha.smooth ν c e, fun y hy => ha.tangent y hy c e,
    fun x hx => ha.coulomb x hx c e⟩

/-- The `L⁴` bound of each entry by the curl (critical Sobolev on the ball + Hodge + Poincaré). -/
theorem eLpNorm_four_entry_le_ball {CS : ℝ≥0}
    (hCS : ∀ (o : Fin 4 → ℝ) (r : ℝ), 0 < r → ∀ u : (Fin 4 → ℝ) → ℂ, ContDiff ℝ 1 u →
      eLpNorm u (4 : ℝ≥0) (volume.restrict (euclBall o r)) ≤
        CS * (∑ i, eLpNorm (pd u i) 2 (volume.restrict (euclBall o r)) +
          ENNReal.ofReal r⁻¹ * eLpNorm u 2 (volume.restrict (euclBall o r))))
    {o : Fin 4 → ℝ} {r : ℝ} (hr : 0 < r) {a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ}
    (ha : IsBallCoulomb o r a) (ν : Fin 4) (c e : Fin m) :
    eLpNorm (a ν c e) 4 (volume.restrict (euclBall o r)) ≤
      5 * CS * ∑ μ', ∑ ν', eLpNorm (curlC (entryForm a c e) μ' ν') 2
        (volume.restrict (euclBall o r)) := by
  obtain ⟨hs, ht, hd⟩ := entry_hyps ha c e
  set K := ∑ μ', ∑ ν', eLpNorm (curlC (entryForm a c e) μ' ν') 2 (volume.restrict (euclBall o r))
  have h1 := hCS o r hr (a ν c e) ((ha.smooth ν c e).of_le (by norm_num))
  have hgrad : ∀ i, eLpNorm (pd (a ν c e) i) 2 (volume.restrict (euclBall o r)) ≤ K := fun i =>
    eLpNorm_pd_le_curl_ball o hr hs ht hd ν i
  have hL2 : eLpNorm (a ν c e) 2 (volume.restrict (euclBall o r)) ≤ ENNReal.ofReal r * K :=
    eLpNorm_le_curl_ball (by norm_num) o hr hs ht hd ν
  have hrr : ENNReal.ofReal r⁻¹ * ENNReal.ofReal r = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hr.ne', ENNReal.ofReal_one]
  have e4 : ((4 : ℝ≥0) : ℝ≥0∞) = 4 := rfl
  rw [e4] at h1
  refine h1.trans ?_
  calc (CS : ℝ≥0∞) * (∑ i, eLpNorm (pd (a ν c e) i) 2 (volume.restrict (euclBall o r)) +
        ENNReal.ofReal r⁻¹ * eLpNorm (a ν c e) 2 (volume.restrict (euclBall o r)))
      ≤ CS * (∑ _i : Fin 4, K + ENNReal.ofReal r⁻¹ * (ENNReal.ofReal r * K)) := by
        gcongr with i
        · exact hgrad i
    _ = 5 * CS * K := by
        rw [← mul_assoc (ENNReal.ofReal r⁻¹), hrr]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Matrix


/-! ### The critical Coulomb a-priori estimate on balls -/

/-- **The critical Coulomb a-priori estimate on a Euclidean ball of `ℝ⁴`** (Uhlenbeck's
closedness estimate, ball rendering, classical forms; no mean-zero hypothesis): there are
`δ > 0` and `C`, depending only on the matrix size `m` (not on the ball), such that every
`C²` matrix-valued one-form `a` on `ℝ⁴` which on `B = B_r(o)` is in Coulomb gauge `d^*a = 0`, has
vanishing normal component `(x - o)·a = 0` on `∂B`, and has small critical norm
`Σ‖a_{ν,ce}‖_{L⁴(B)} ≤ δ` satisfies, with `‖F_a‖ = Σ_{μνce} ‖F_{μν,ce}‖_{L²(B)}`,
* `Σ ‖a_{ν,ce}‖_{L⁴(B)} ≤ C ‖F_a‖` (scale invariant),
* `Σ ‖∂_μ a_{ν,ce}‖_{L²(B)} ≤ 32 m² ‖F_a‖`,
* `‖a_{ν,ce}‖_{L²(B)} ≤ 2 r ‖F_a‖`.
Proof: Gaffney + Poincaré for co-closed tangential forms (`eLpNorm_pd_le_curl_ball`,
`eLpNorm_le_curl_ball`), critical Sobolev on balls (`sobolev_ball`), `da = F - [a ∧ a]` with
Hölder, and absorption of the quadratic term. -/
theorem coulomb_apriori_ball (m : ℕ) : ∃ δ : ℝ≥0, 0 < δ ∧ ∃ C : ℝ≥0,
    ∀ (o : Fin 4 → ℝ) (r : ℝ), 0 < r → ∀ a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ,
      IsBallCoulomb o r a → bL4 o r a ≤ δ →
      bL4 o r a ≤ C * bCurvNorm o r a ∧
      bGradNorm o r a ≤ 32 * (m : ℝ≥0∞) ^ 2 * bCurvNorm o r a ∧
      (∀ ν c e, eLpNorm (a ν c e) 2 (volume.restrict (euclBall o r)) ≤
        2 * ENNReal.ofReal r * bCurvNorm o r a) := by
  obtain ⟨CS, hCS⟩ := sobolev_ball (n := 4) (by norm_num) (p' := 4) (by norm_num)
  set κ : ℝ≥0 := 640 * (m : ℝ≥0) ^ 3 * CS
  set δ : ℝ≥0 := (2 * κ + 1)⁻¹
  refine ⟨δ, by positivity, 40 * (m : ℝ≥0) ^ 2 * CS, fun o r hr a ha hX => ?_⟩
  have hq : (κ : ℝ≥0∞) * δ ≤ 2⁻¹ := coulombKappa_mul_le le_rfl
  set X := bL4 o r a
  set B := bCurvNorm o r a
  set ρ := volume.restrict (euclBall o r)
  have hXt : X ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hX
  have ha1 : ∀ ν c e, ContDiff ℝ 1 (a ν c e) := fun ν c e => (ha.smooth ν c e).of_le (by norm_num)
  have hK := fun c e => sum_curl_entry_le o r ha1 c e
  have hent : ∀ ν c e, eLpNorm (a ν c e) 4 ρ ≤ 5 * CS * (B + 32 * m * (X * X)) := fun ν c e =>
    (eLpNorm_four_entry_le_ball hCS hr ha ν c e).trans (by gcongr; exact hK c e)
  -- the quadratic inequality
  have hquad : X ≤ 20 * (m : ℝ≥0∞) ^ 2 * CS * B + (κ * δ : ℝ≥0∞) * X := by
    have h1 : X ≤ ∑ _ν : Fin 4, ∑ _c : Fin m, ∑ _e : Fin m,
        5 * (CS : ℝ≥0∞) * (B + 32 * m * (X * X)) :=
      Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun e _ =>
        hent ν c e
    have h2 : X * X ≤ (δ : ℝ≥0∞) * X := by gcongr
    refine h1.trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc (4 : ℝ≥0∞) * (m * (m * (5 * CS * (B + 32 * m * (X * X)))))
        = 20 * (m : ℝ≥0∞) ^ 2 * CS * B + 640 * (m : ℝ≥0∞) ^ 3 * CS * (X * X) := by
          push_cast; ring
      _ ≤ 20 * (m : ℝ≥0∞) ^ 2 * CS * B + 640 * (m : ℝ≥0∞) ^ 3 * CS * (δ * X) := by gcongr
      _ = 20 * (m : ℝ≥0∞) ^ 2 * CS * B + (κ * δ : ℝ≥0∞) * X := by
          simp only [κ]; push_cast; ring
  have hXB : X ≤ ((40 * (m : ℝ≥0) ^ 2 * CS : ℝ≥0) : ℝ≥0∞) * B := by
    have := le_two_mul_of_le_add_mul hXt hq hquad
    refine this.trans (le_of_eq ?_)
    push_cast; ring
  -- each curl sum is at most `2 B`
  have hK2 : ∀ c e, ∑ μ', ∑ ν', eLpNorm (curlC (entryForm a c e) μ' ν') 2 ρ ≤ 2 * B := by
    intro c e
    refine (hK c e).trans ?_
    have h3 : 32 * (m : ℝ≥0∞) * (X * X) ≤ (2 * (κ * δ : ℝ≥0∞)) * B := by
      calc 32 * (m : ℝ≥0∞) * (X * X) ≤ 32 * (m : ℝ≥0∞) * (δ * X) := by
            gcongr
        _ ≤ 32 * (m : ℝ≥0∞) * (δ * (((40 * (m : ℝ≥0) ^ 2 * CS : ℝ≥0) : ℝ≥0∞) * B)) := by
            gcongr
        _ = (2 * (κ * δ : ℝ≥0∞)) * B := by simp only [κ]; push_cast; ring
    have h4 : (2 * (κ * δ : ℝ≥0∞)) * B ≤ B := by
      calc (2 * (κ * δ : ℝ≥0∞)) * B ≤ (2 * 2⁻¹) * B := by gcongr
        _ = B := by rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    calc B + 32 * (m : ℝ≥0∞) * (X * X) ≤ B + B := add_le_add le_rfl (h3.trans h4)
      _ = 2 * B := by ring
  refine ⟨hXB, ?_, fun ν c e => ?_⟩
  · calc bGradNorm o r a ≤ ∑ _ν : Fin 4, ∑ _c : Fin m, ∑ _e : Fin m, ∑ _μ : Fin 4, 2 * B := by
          unfold bGradNorm
          refine Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun c _ =>
            Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun μ _ => ?_
          obtain ⟨hs, ht, hd⟩ := entry_hyps ha c e
          exact (eLpNorm_pd_le_curl_ball o hr hs ht hd ν μ).trans (hK2 c e)
      _ = 32 * (m : ℝ≥0∞) ^ 2 * B := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  · obtain ⟨hs, ht, hd⟩ := entry_hyps ha c e
    calc eLpNorm (a ν c e) 2 ρ ≤ ENNReal.ofReal r *
          ∑ μ', ∑ ν', eLpNorm (curlC (entryForm a c e) μ' ν') 2 ρ :=
          eLpNorm_le_curl_ball (by norm_num) o hr hs ht hd ν
      _ ≤ ENNReal.ofReal r * (2 * B) := by gcongr; exact hK2 c e
      _ = 2 * ENNReal.ofReal r * B := by ring

/-- Non-vacuity: the zero form is a Coulomb form with vanishing normal component on every ball. -/
example (m : ℕ) (o : Fin 4 → ℝ) (r : ℝ) :
    IsBallCoulomb (m := m) o r (fun _ _ _ _ => 0) :=
  ⟨fun _ _ _ => contDiff_const, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp [pd]⟩

/-- Non-vacuity with a nonzero form: the rotation field `(-x₁, x₀, 0, 0)` (abelian, `m = 1`) is a
Coulomb form tangent to every sphere centred at `0`. -/
example (r : ℝ) : IsBallCoulomb (m := 1) 0 r
    (fun ν _ _ x => ((rotField ν x : ℝ) : ℂ)) := by
  have hsm : ∀ ν, ContDiff ℝ 2 (rotField ν) := by
    intro ν
    fin_cases ν <;> simp [rotField]
    · exact (contDiff_apply ℝ ℝ (1 : Fin 4)).neg
    · exact contDiff_apply ℝ ℝ (0 : Fin 4)
    · exact contDiff_const
    · exact contDiff_const
  have hrot : ∀ μ x, pd (rotField μ) μ x = 0 := by
    intro μ x
    have h1 : HasFDerivAt (fun y : Fin 4 → ℝ => y 1)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1) x := hasFDerivAt_apply 1 x
    have h0 : HasFDerivAt (fun y : Fin 4 → ℝ => y 0)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0) x := hasFDerivAt_apply 0 x
    fin_cases μ
    · show pd (fun y : Fin 4 → ℝ => -y 1) 0 x = 0
      have h1n : HasFDerivAt (fun y : Fin 4 → ℝ => -y 1)
          (-ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1) x := h1.neg
      unfold pd; rw [h1n.fderiv]; simp
    · show pd (fun y : Fin 4 → ℝ => y 0) 1 x = 0
      unfold pd; rw [h0.fderiv]; simp
    · show pd (fun _ : Fin 4 → ℝ => (0 : ℝ)) 2 x = 0
      simp [pd]
    · show pd (fun _ : Fin 4 → ℝ => (0 : ℝ)) 3 x = 0
      simp [pd]
  refine ⟨fun ν _ _ => Complex.ofRealCLM.contDiff.comp (hsm ν), fun y _ _ _ => ?_,
    fun x _ _ _ => ?_⟩
  · simp only [Pi.zero_apply, sub_zero]
    simp [rotField, Fin.sum_univ_four]; ring
  · have h : ∀ μ, pd (fun x : Fin 4 → ℝ => ((rotField μ x : ℝ) : ℂ)) μ x = 0 := fun μ => by
      rw [pd_ofReal ((hsm μ).of_le (by norm_num)), hrot, Complex.ofReal_zero]
    simp [h]

end RenewalGeometry.BallAnalysis
