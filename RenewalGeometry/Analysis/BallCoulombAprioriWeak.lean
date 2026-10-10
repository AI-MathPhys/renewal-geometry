/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallCoulombApriori

/-!
# The critical Coulomb a-priori estimate on balls for weak (`H¹`) Coulomb forms
  (stage D2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

The classical estimate `coulomb_apriori_ball` is stated for globally `C²` one-forms.  The
continuity method produces Coulomb gauges of Sobolev regularity only; this file proves the same
estimate for one-forms which are `H¹(B)`-limits of `C²` **tangential** forms (not necessarily
co-closed) and are weakly co-closed.

* `sq_ofReal_gaffney_le`, `eLpNorm_pd_le_curl_div_ball`, `eLpNorm_le_curl_div_ball` — Gaffney and
  Poincaré for tangential `C²` forms **with the divergence term** (no co-closedness);
* `IsWeakBallCoulomb o r a ga` — weak Coulomb forms with gradient data `ga ν c e μ = ∂_μ a_{ν,ce}`:
  `L²` data, `H¹(B)`-limits of `C²` tangential forms, `Σ_μ ∂_μ a_μ = 0` a.e.;
* `weak_hodge`, `weak_poincare`, `weak_sobolev` — the three ingredients passed to the limit
  (lower semicontinuity of the `L⁴` norm along an a.e. convergent subsequence);
* `coulomb_apriori_weak` (**main result**): the critical a-priori estimate of
  `coulomb_apriori_ball` for weak Coulomb forms (same constants: `δ`, `C` depend only on `m`);
* `IsBallCoulomb.isWeakBallCoulomb` — classical Coulomb forms are weak Coulomb forms (non-vacuity).
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis.WeakCoulomb

open SobolevOpen

set_option linter.unusedSectionVars false

/-! ### Generic limit lemmas -/

theorem le_of_le_add_of_tendsto {X Y : ℝ≥0∞} {e : ℕ → ℝ≥0∞} (h : ∀ k, X ≤ Y + e k)
    (he : Tendsto e atTop (𝓝 0)) : X ≤ Y := by
  have h1 : Tendsto (fun k => Y + e k) atTop (𝓝 (Y + 0)) := tendsto_const_nhds.add he
  rw [add_zero] at h1
  exact ge_of_tendsto' h1 h

theorem eLpNorm_le_add_sub {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm f p μ ≤ eLpNorm g p μ + eLpNorm (g - f) p μ := by
  have e : f = g - (g - f) := by funext x; simp
  conv_lhs => rw [e]
  exact eLpNorm_sub_le hg (hg.sub hf) hp

/-! ### Gaffney and Poincaré with the divergence term (classical tangential forms) -/

section Classical

variable {n : ℕ} [NeZero n]

theorem sq_ofReal_gaffney_le (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    {w : Fin n → (Fin n → ℝ) → ℂ} (hw : ∀ ν, ContDiff ℝ 1 (w ν)) :
    ENNReal.ofReal (∫ x in euclBall c r, (curlSqC w x / 2 + ‖divC w x‖ ^ 2)) ≤
      (∑ μ', ∑ ν', eLpNorm (curlC w μ' ν') 2 (volume.restrict (euclBall c r)) +
        eLpNorm (divC w) 2 (volume.restrict (euclBall c r))) ^ 2 := by
  have hcc : Continuous (curlSqC w) := by
    unfold curlSqC
    exact continuous_finsetSum _ fun μ _ => continuous_finsetSum _ fun ν _ =>
      ((continuous_pd (hw ν) μ).sub (continuous_pd (hw μ) ν)).norm.pow 2
  have hcd : Continuous (divC w) := by
    unfold divC; exact continuous_finsetSum _ fun μ _ => (continuous_pd (hw μ) μ)
  have hi1 : IntegrableOn (fun x => curlSqC w x / 2) (euclBall c r) :=
    integrableOn_euclBall (c := c) hr.le (hcc.div_const 2)
  have hi2 : IntegrableOn (fun x => ‖divC w x‖ ^ 2) (euclBall c r) :=
    integrableOn_euclBall (c := c) hr.le (hcd.norm.pow 2)
  have hi3 := integrableOn_euclBall (c := c) hr.le hcc
  have hC0 : ∀ x, 0 ≤ curlSqC w x := fun x =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  rw [integral_add hi1 hi2]
  have hle : ∫ x in euclBall c r, curlSqC w x / 2 ≤ ∫ x in euclBall c r, curlSqC w x :=
    setIntegral_mono_on hi1 hi3 (measurableSet_euclBall c r) fun x _ => by linarith [hC0 x]
  calc ENNReal.ofReal ((∫ x in euclBall c r, curlSqC w x / 2) +
        ∫ x in euclBall c r, ‖divC w x‖ ^ 2)
      ≤ ENNReal.ofReal (∫ x in euclBall c r, curlSqC w x) +
          ENNReal.ofReal (∫ x in euclBall c r, ‖divC w x‖ ^ 2) :=
        (ENNReal.ofReal_le_ofReal (by linarith)).trans ENNReal.ofReal_add_le
    _ = (∑ μ', ∑ ν', eLpNorm (curlC w μ' ν') 2 (volume.restrict (euclBall c r)) ^ 2) +
          eLpNorm (divC w) 2 (volume.restrict (euclBall c r)) ^ 2 := by
        rw [ofReal_integral_curlSqC hr hw, eLpNorm_two_sq_eq hi2]
    _ ≤ (∑ μ', ∑ ν', eLpNorm (curlC w μ' ν') 2 (volume.restrict (euclBall c r))) ^ 2 +
          eLpNorm (divC w) 2 (volume.restrict (euclBall c r)) ^ 2 := by
        gcongr; exact sum_sum_sq_le _
    _ ≤ (∑ μ', ∑ ν', eLpNorm (curlC w μ' ν') 2 (volume.restrict (euclBall c r)) +
          eLpNorm (divC w) 2 (volume.restrict (euclBall c r))) ^ 2 := by
        rw [add_sq]
        gcongr
        exact le_self_add

/-- **Gaffney's inequality with the divergence term** for tangential complex `C²` forms:
`‖∂_μ w_ν‖_{L²(B)} ≤ Σ_{μ'ν'} ‖curl w‖_{L²(B)} + ‖div w‖_{L²(B)}`. -/
theorem eLpNorm_pd_le_curl_div_ball (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    {w : Fin n → (Fin n → ℝ) → ℂ} (hw : ∀ ν, ContDiff ℝ 2 (w ν))
    (hS : ∀ y, sqDist c y = r ^ 2 → ∑ μ, ((y μ - c μ : ℝ) : ℂ) * w μ y = 0) (ν μ : Fin n) :
    eLpNorm (pd (w ν) μ) 2 (volume.restrict (euclBall c r)) ≤
      ∑ μ', ∑ ν', eLpNorm (curlC w μ' ν') 2 (volume.restrict (euclBall c r)) +
        eLpNorm (divC w) 2 (volume.restrict (euclBall c r)) := by
  have hw1 : ∀ ν, ContDiff ℝ 1 (w ν) := fun ν => (hw ν).of_le (by norm_num)
  have hB := measurableSet_euclBall c r
  have hcg : Continuous (gradSqC w) := by
    unfold gradSqC
    exact continuous_finsetSum _ fun μ _ => continuous_finsetSum _ fun ν _ =>
      (continuous_pd (hw1 ν) μ).norm.pow 2
  have h1 : ∫ x in euclBall c r, ‖pd (w ν) μ x‖ ^ 2 ≤ ∫ x in euclBall c r, gradSqC w x := by
    refine setIntegral_mono_on (integrableOn_euclBall hr.le ((continuous_pd (hw1 ν) μ).norm.pow 2))
      (integrableOn_euclBall hr.le hcg) hB fun x _ => ?_
    unfold gradSqC
    refine (Finset.single_le_sum (f := fun ν' => ‖pd (w ν') μ x‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ ν)).trans ?_
    exact Finset.single_le_sum (f := fun μ' => ∑ ν', ‖pd (w ν') μ' x‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ μ)
  have h2 := gaffney_ball_complex c hr hw hS
  have h3 : eLpNorm (pd (w ν) μ) 2 (volume.restrict (euclBall c r)) ^ 2 ≤
      (∑ μ', ∑ ν', eLpNorm (curlC w μ' ν') 2 (volume.restrict (euclBall c r)) +
        eLpNorm (divC w) 2 (volume.restrict (euclBall c r))) ^ 2 := by
    rw [eLpNorm_two_sq_eq (integrableOn_euclBall hr.le ((continuous_pd (hw1 ν) μ).norm.pow 2))]
    exact (ENNReal.ofReal_le_ofReal (h1.trans h2)).trans (sq_ofReal_gaffney_le c hr hw1)
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).mp h3

/-- **Poincaré's inequality with the divergence term** for tangential complex `C²` forms
(`n ≥ 2`): `‖w_ν‖_{L²(B_r)} ≤ r (Σ ‖curl w‖ + ‖div w‖)`. -/
theorem eLpNorm_le_curl_div_ball (hn : 2 ≤ n) (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    {w : Fin n → (Fin n → ℝ) → ℂ} (hw : ∀ ν, ContDiff ℝ 2 (w ν))
    (hS : ∀ y, sqDist c y = r ^ 2 → ∑ μ, ((y μ - c μ : ℝ) : ℂ) * w μ y = 0) (ν : Fin n) :
    eLpNorm (w ν) 2 (volume.restrict (euclBall c r)) ≤
      ENNReal.ofReal r * (∑ μ', ∑ ν', eLpNorm (curlC w μ' ν') 2 (volume.restrict (euclBall c r)) +
        eLpNorm (divC w) 2 (volume.restrict (euclBall c r))) := by
  have hw1 : ∀ ν, ContDiff ℝ 1 (w ν) := fun ν => (hw ν).of_le (by norm_num)
  have hB := measurableSet_euclBall c r
  have hcn : Continuous (normSqC w) := by
    unfold normSqC
    exact continuous_finsetSum _ fun ν _ => (hw1 ν).continuous.norm.pow 2
  have hP := poincare_ball_complex c hr hw hS
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hI0 : 0 ≤ ∫ x in euclBall c r, normSqC w x :=
    setIntegral_nonneg hB fun x _ => Finset.sum_nonneg fun _ _ => by positivity
  have h1 : ∫ x in euclBall c r, ‖w ν x‖ ^ 2 ≤ ∫ x in euclBall c r, normSqC w x := by
    refine setIntegral_mono_on (integrableOn_euclBall hr.le ((hw1 ν).continuous.norm.pow 2))
      (integrableOn_euclBall hr.le hcn) hB fun x _ => ?_
    exact Finset.single_le_sum (f := fun ν' => ‖w ν' x‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ ν)
  have h2 : ∫ x in euclBall c r, ‖w ν x‖ ^ 2 ≤
      r ^ 2 * ∫ x in euclBall c r, (curlSqC w x / 2 + ‖divC w x‖ ^ 2) := by
    refine h1.trans ?_
    have : ∫ x in euclBall c r, normSqC w x ≤
        ((n : ℝ) - 1) * ∫ x in euclBall c r, normSqC w x := le_mul_of_one_le_left hI0 hn1
    linarith
  have h3 : eLpNorm (w ν) 2 (volume.restrict (euclBall c r)) ^ 2 ≤
      (ENNReal.ofReal r * (∑ μ', ∑ ν', eLpNorm (curlC w μ' ν') 2
        (volume.restrict (euclBall c r)) + eLpNorm (divC w) 2 (volume.restrict (euclBall c r)))) ^ 2 := by
    rw [eLpNorm_two_sq_eq (integrableOn_euclBall hr.le ((hw1 ν).continuous.norm.pow 2))]
    refine (ENNReal.ofReal_le_ofReal h2).trans ?_
    rw [ENNReal.ofReal_mul (by positivity), mul_pow, ENNReal.ofReal_pow hr.le]
    gcongr
    exact sq_ofReal_gaffney_le c hr hw1
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).mp h3

end Classical

/-! ### Weak Coulomb forms -/

section Weak

variable {m : ℕ}

/-- Weak curl of the `(c,e)` entry: `∂_{μ'} a_{ν'} - ∂_{ν'} a_{μ'}` from gradient data. -/
def wCurl (ga : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) (c e : Fin m) (μ' ν' : Fin 4)
    (x : Fin 4 → ℝ) : ℂ :=
  ga ν' c e μ' x - ga μ' c e ν' x

/-- Weak curvature `F_{μν,ce} = ∂_μ a_{ν,ce} - ∂_ν a_{μ,ce} + [a_μ,a_ν]_{ce}`. -/
def wCurv (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
    (ga : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) (μ ν : Fin 4) (c e : Fin m)
    (x : Fin 4 → ℝ) : ℂ :=
  ga ν c e μ x - ga μ c e ν x + bComm a μ ν c e x

/-- `Σ_{μνce} ‖F_{μν,ce}‖_{L²(B)}` for weak curvature. -/
def wCurvNorm (o : Fin 4 → ℝ) (r : ℝ) (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
    (ga : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) : ℝ≥0∞ :=
  ∑ μ, ∑ ν, ∑ c, ∑ e, eLpNorm (wCurv a ga μ ν c e) 2 (volume.restrict (euclBall o r))

/-- `Σ_{νceμ} ‖∂_μ a_{ν,ce}‖_{L²(B)}` for gradient data. -/
def wGradNorm (o : Fin 4 → ℝ) (r : ℝ) (ga : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) :
    ℝ≥0∞ :=
  ∑ ν, ∑ c, ∑ e, ∑ μ, eLpNorm (ga ν c e μ) 2 (volume.restrict (euclBall o r))

/-- **Weak Coulomb forms on a ball with vanishing normal component**: `L²` entries `a ν c e` with
`L²` gradient data `ga ν c e μ`, which are `H¹(B)`-limits of globally `C²` forms with vanishing
normal component on the sphere, and are weakly co-closed (`Σ_μ ∂_μ a_μ = 0` a.e. on the ball). -/
structure IsWeakBallCoulomb (o : Fin 4 → ℝ) (r : ℝ)
    (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
    (ga : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) : Prop where
  memLp : ∀ ν c e, MemLp (a ν c e) 2 (volume.restrict (euclBall o r))
  memLp_grad : ∀ ν c e μ, MemLp (ga ν c e μ) 2 (volume.restrict (euclBall o r))
  approx : ∃ at' : ℕ → Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ,
    (∀ k ν c e, ContDiff ℝ 2 (at' k ν c e)) ∧
    (∀ k y, sqDist o y = r ^ 2 → ∀ c e, ∑ μ, ((y μ - o μ : ℝ) : ℂ) * at' k μ c e y = 0) ∧
    (∀ ν c e, Tendsto (fun k => eLpNorm (at' k ν c e - a ν c e) 2
      (volume.restrict (euclBall o r))) atTop (𝓝 0)) ∧
    (∀ ν c e μ, Tendsto (fun k => eLpNorm (pd (at' k ν c e) μ - ga ν c e μ) 2
      (volume.restrict (euclBall o r))) atTop (𝓝 0))
  coulomb : ∀ c e, ∀ᵐ x ∂(volume.restrict (euclBall o r)), ∑ μ, ga μ c e μ x = 0

variable {o : Fin 4 → ℝ} {r : ℝ} {a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ}
  {ga : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ}

/-- The approximation error of the curl and the divergence. -/
theorem curl_div_errors (ha : IsWeakBallCoulomb o r a ga)
    {at' : ℕ → Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ} (hs : ∀ k ν c e, ContDiff ℝ 2 (at' k ν c e))
    (k : ℕ) (c e : Fin m) :
    (∀ μ' ν', eLpNorm (curlC (fun ν => at' k ν c e) μ' ν') 2 (volume.restrict (euclBall o r)) ≤
      eLpNorm (wCurl ga c e μ' ν') 2 (volume.restrict (euclBall o r)) +
        (eLpNorm (pd (at' k ν' c e) μ' - ga ν' c e μ') 2 (volume.restrict (euclBall o r)) +
          eLpNorm (pd (at' k μ' c e) ν' - ga μ' c e ν') 2 (volume.restrict (euclBall o r)))) ∧
    eLpNorm (divC (fun ν => at' k ν c e)) 2 (volume.restrict (euclBall o r)) ≤
      ∑ μ, eLpNorm (pd (at' k μ c e) μ - ga μ c e μ) 2 (volume.restrict (euclBall o r)) := by
  set ρ := volume.restrict (euclBall o r)
  have hpd : ∀ ν μ, AEStronglyMeasurable (pd (at' k ν c e) μ) ρ := fun ν μ =>
    (continuous_pd ((hs k ν c e).of_le (by norm_num)) μ).aestronglyMeasurable
  have hg : ∀ ν μ, AEStronglyMeasurable (ga ν c e μ) ρ := fun ν μ =>
    (ha.memLp_grad ν c e μ).aestronglyMeasurable
  refine ⟨fun μ' ν' => ?_, ?_⟩
  · have hcm : AEStronglyMeasurable (curlC (fun ν => at' k ν c e) μ' ν') ρ :=
      (hpd ν' μ').sub (hpd μ' ν')
    have hwm : AEStronglyMeasurable (wCurl ga c e μ' ν') ρ := (hg ν' μ').sub (hg μ' ν')
    refine (eLpNorm_le_add_sub (by norm_num) hcm hwm).trans (add_le_add le_rfl ?_)
    have e1 : wCurl ga c e μ' ν' - curlC (fun ν => at' k ν c e) μ' ν' =
        (pd (at' k μ' c e) ν' - ga μ' c e ν') - (pd (at' k ν' c e) μ' - ga ν' c e μ') := by
      funext x; simp only [wCurl, curlC, Pi.sub_apply]; ring
    rw [e1, add_comm]
    exact eLpNorm_sub_le ((hpd μ' ν').sub (hg μ' ν')) ((hpd ν' μ').sub (hg ν' μ')) (by norm_num)
  · have e1 : divC (fun ν => at' k ν c e) =ᵐ[ρ]
        ∑ μ, (pd (at' k μ c e) μ - ga μ c e μ) := by
      filter_upwards [ha.coulomb c e] with x hx
      simp only [divC, Finset.sum_apply, Pi.sub_apply, Finset.sum_sub_distrib, hx, sub_zero]
    rw [eLpNorm_congr_ae e1]
    exact eLpNorm_sum_le (fun μ _ => (hpd μ μ).sub (hg μ μ)) (by norm_num)

/-- **Weak Hodge estimate**: `‖∂_μ a_{ν,ce}‖_{L²(B)} ≤ Σ_{μ'ν'} ‖curl a_{ce}‖_{L²(B)}`. -/
theorem weak_hodge (hr : 0 < r) (ha : IsWeakBallCoulomb o r a ga) (c e : Fin m) (ν μ : Fin 4) :
    eLpNorm (ga ν c e μ) 2 (volume.restrict (euclBall o r)) ≤
      ∑ μ', ∑ ν', eLpNorm (wCurl ga c e μ' ν') 2 (volume.restrict (euclBall o r)) := by
  set ρ := volume.restrict (euclBall o r)
  obtain ⟨at', hs, ht, -, hgl⟩ := ha.approx
  set d : ℕ → Fin 4 → Fin 4 → ℝ≥0∞ := fun k ν μ => eLpNorm (pd (at' k ν c e) μ - ga ν c e μ) 2 ρ
  have hd : ∀ ν μ, Tendsto (fun k => d k ν μ) atTop (𝓝 0) := fun ν μ => hgl ν c e μ
  refine le_of_le_add_of_tendsto (e := fun k => d k ν μ +
    (∑ μ', ∑ ν', (d k ν' μ' + d k μ' ν') + ∑ μ, d k μ μ)) (fun k => ?_) ?_
  · obtain ⟨hcurl, hdiv⟩ := curl_div_errors ha hs k c e
    have hcl := eLpNorm_pd_le_curl_div_ball o hr (w := fun ν => at' k ν c e)
      (fun ν => hs k ν c e) (fun y hy => ht k y hy c e) ν μ
    have h0 : eLpNorm (ga ν c e μ) 2 ρ ≤ eLpNorm (pd (at' k ν c e) μ) 2 ρ + d k ν μ := by
      refine (eLpNorm_le_add_sub (by norm_num) (ha.memLp_grad ν c e μ).aestronglyMeasurable
        (continuous_pd ((hs k ν c e).of_le (by norm_num)) μ).aestronglyMeasurable).trans ?_
      exact le_rfl
    refine h0.trans ?_
    calc eLpNorm (pd (at' k ν c e) μ) 2 ρ + d k ν μ
        ≤ (∑ μ', ∑ ν', eLpNorm (curlC (fun ν => at' k ν c e) μ' ν') 2 ρ +
            eLpNorm (divC (fun ν => at' k ν c e)) 2 ρ) + d k ν μ := by gcongr
      _ ≤ (∑ μ', ∑ ν', (eLpNorm (wCurl ga c e μ' ν') 2 ρ + (d k ν' μ' + d k μ' ν')) +
            ∑ μ, d k μ μ) + d k ν μ := by
          gcongr with μ' _ ν' _
          all_goals first | exact hcurl μ' ν' | skip
      _ = _ := by
          simp only [Finset.sum_add_distrib]; ring
  · have h1 : Tendsto (fun k => d k ν μ +
        (∑ μ', ∑ ν', (d k ν' μ' + d k μ' ν') + ∑ μ, d k μ μ)) atTop
        (𝓝 (0 + ((∑ _μ' : Fin 4, ∑ _ν' : Fin 4, ((0 : ℝ≥0∞) + 0)) + ∑ _μ : Fin 4, (0 : ℝ≥0∞)))) :=
      (hd ν μ).add ((tendsto_finsetSum _ fun μ' _ => tendsto_finsetSum _ fun ν' _ =>
        (hd ν' μ').add (hd μ' ν')).add (tendsto_finsetSum _ fun μ _ => hd μ μ))
    simpa using h1

/-- **Weak Poincaré estimate**: `‖a_{ν,ce}‖_{L²(B_r)} ≤ r Σ_{μ'ν'} ‖curl a_{ce}‖_{L²(B_r)}`. -/
theorem weak_poincare (hr : 0 < r) (ha : IsWeakBallCoulomb o r a ga) (c e : Fin m) (ν : Fin 4) :
    eLpNorm (a ν c e) 2 (volume.restrict (euclBall o r)) ≤
      ENNReal.ofReal r * ∑ μ', ∑ ν', eLpNorm (wCurl ga c e μ' ν') 2 (volume.restrict (euclBall o r)) := by
  set ρ := volume.restrict (euclBall o r)
  obtain ⟨at', hs, ht, hal, hgl⟩ := ha.approx
  set d : ℕ → Fin 4 → Fin 4 → ℝ≥0∞ := fun k ν μ => eLpNorm (pd (at' k ν c e) μ - ga ν c e μ) 2 ρ
  have hd : ∀ ν μ, Tendsto (fun k => d k ν μ) atTop (𝓝 0) := fun ν μ => hgl ν c e μ
  refine le_of_le_add_of_tendsto (e := fun k => eLpNorm (at' k ν c e - a ν c e) 2 ρ +
    ENNReal.ofReal r * (∑ μ', ∑ ν', (d k ν' μ' + d k μ' ν') + ∑ μ, d k μ μ)) (fun k => ?_) ?_
  · obtain ⟨hcurl, hdiv⟩ := curl_div_errors ha hs k c e
    have hcl := eLpNorm_le_curl_div_ball (by norm_num) o hr (w := fun ν => at' k ν c e)
      (fun ν => hs k ν c e) (fun y hy => ht k y hy c e) ν
    have h0 : eLpNorm (a ν c e) 2 ρ ≤ eLpNorm (at' k ν c e) 2 ρ +
        eLpNorm (at' k ν c e - a ν c e) 2 ρ :=
      eLpNorm_le_add_sub (by norm_num) (ha.memLp ν c e).aestronglyMeasurable
        (hs k ν c e).continuous.aestronglyMeasurable
    refine h0.trans ?_
    calc eLpNorm (at' k ν c e) 2 ρ + eLpNorm (at' k ν c e - a ν c e) 2 ρ
        ≤ ENNReal.ofReal r * (∑ μ', ∑ ν', eLpNorm (curlC (fun ν => at' k ν c e) μ' ν') 2 ρ +
            eLpNorm (divC (fun ν => at' k ν c e)) 2 ρ) +
            eLpNorm (at' k ν c e - a ν c e) 2 ρ := by gcongr
      _ ≤ ENNReal.ofReal r * (∑ μ', ∑ ν', (eLpNorm (wCurl ga c e μ' ν') 2 ρ +
            (d k ν' μ' + d k μ' ν')) + ∑ μ, d k μ μ) + eLpNorm (at' k ν c e - a ν c e) 2 ρ := by
          gcongr with μ' _ ν' _
          all_goals first | exact hcurl μ' ν' | skip
      _ = _ := by
          simp only [Finset.sum_add_distrib]; ring
  · have h1 : Tendsto (fun k => eLpNorm (at' k ν c e - a ν c e) 2 ρ +
        ENNReal.ofReal r * (∑ μ', ∑ ν', (d k ν' μ' + d k μ' ν') + ∑ μ, d k μ μ)) atTop
        (𝓝 (0 + ENNReal.ofReal r * ((∑ _μ' : Fin 4, ∑ _ν' : Fin 4, ((0 : ℝ≥0∞) + 0)) +
          ∑ _μ : Fin 4, (0 : ℝ≥0∞)))) :=
      (hal ν c e).add (ENNReal.Tendsto.const_mul ((tendsto_finsetSum _ fun μ' _ =>
        tendsto_finsetSum _ fun ν' _ => (hd ν' μ').add (hd μ' ν')).add
        (tendsto_finsetSum _ fun μ _ => hd μ μ)) (Or.inr ENNReal.ofReal_ne_top))
    simpa using h1

/-- **Weak critical Sobolev inequality** on the ball (lower semicontinuity of the `L⁴` norm). -/
theorem weak_sobolev {CS : ℝ≥0}
    (hCS : ∀ (o : Fin 4 → ℝ) (r : ℝ), 0 < r → ∀ u : (Fin 4 → ℝ) → ℂ, ContDiff ℝ 1 u →
      eLpNorm u (4 : ℝ≥0) (volume.restrict (euclBall o r)) ≤
        CS * (∑ i, eLpNorm (pd u i) 2 (volume.restrict (euclBall o r)) +
          ENNReal.ofReal r⁻¹ * eLpNorm u 2 (volume.restrict (euclBall o r))))
    (hr : 0 < r) (ha : IsWeakBallCoulomb o r a ga) (ν : Fin 4) (c e : Fin m) :
    eLpNorm (a ν c e) 4 (volume.restrict (euclBall o r)) ≤
      CS * (∑ i, eLpNorm (ga ν c e i) 2 (volume.restrict (euclBall o r)) +
        ENNReal.ofReal r⁻¹ * eLpNorm (a ν c e) 2 (volume.restrict (euclBall o r))) := by
  set ρ := volume.restrict (euclBall o r)
  obtain ⟨at', hs, -, hal, hgl⟩ := ha.approx
  set R := (CS : ℝ≥0∞) * (∑ i, eLpNorm (ga ν c e i) 2 ρ + ENNReal.ofReal r⁻¹ * eLpNorm (a ν c e) 2 ρ)
  set err : ℕ → ℝ≥0∞ := fun k => (CS : ℝ≥0∞) * (∑ i, eLpNorm (pd (at' k ν c e) i - ga ν c e i) 2 ρ +
    ENNReal.ofReal r⁻¹ * eLpNorm (at' k ν c e - a ν c e) 2 ρ)
  have hk : ∀ k, eLpNorm (at' k ν c e) 4 ρ ≤ R + err k := by
    intro k
    have h1 := hCS o r hr (at' k ν c e) ((hs k ν c e).of_le (by norm_num))
    have e4 : ((4 : ℝ≥0) : ℝ≥0∞) = 4 := rfl
    rw [e4] at h1
    refine h1.trans ?_
    have hp : ∀ i, eLpNorm (pd (at' k ν c e) i) 2 ρ ≤ eLpNorm (ga ν c e i) 2 ρ +
        eLpNorm (pd (at' k ν c e) i - ga ν c e i) 2 ρ := fun i => by
      have := eLpNorm_le_add_sub (μ := ρ) (p := 2) (by norm_num)
        (continuous_pd ((hs k ν c e).of_le (by norm_num)) i).aestronglyMeasurable
        (ha.memLp_grad ν c e i).aestronglyMeasurable
      rwa [eLpNorm_sub_comm] at this
    have hq : eLpNorm (at' k ν c e) 2 ρ ≤ eLpNorm (a ν c e) 2 ρ +
        eLpNorm (at' k ν c e - a ν c e) 2 ρ := by
      have := eLpNorm_le_add_sub (μ := ρ) (p := 2) (by norm_num)
        (hs k ν c e).continuous.aestronglyMeasurable (ha.memLp ν c e).aestronglyMeasurable
      rwa [eLpNorm_sub_comm] at this
    calc (CS : ℝ≥0∞) * (∑ i, eLpNorm (pd (at' k ν c e) i) 2 ρ +
          ENNReal.ofReal r⁻¹ * eLpNorm (at' k ν c e) 2 ρ)
        ≤ CS * (∑ i, (eLpNorm (ga ν c e i) 2 ρ + eLpNorm (pd (at' k ν c e) i - ga ν c e i) 2 ρ) +
            ENNReal.ofReal r⁻¹ * (eLpNorm (a ν c e) 2 ρ + eLpNorm (at' k ν c e - a ν c e) 2 ρ)) := by
          gcongr with i
          · exact hp i
      _ = R + err k := by
          simp only [R, err, Finset.sum_add_distrib]; ring
  have herr : Tendsto err atTop (𝓝 0) := by
    have h1 : Tendsto err atTop (𝓝 ((CS : ℝ≥0∞) * (∑ _i : Fin 4, (0 : ℝ≥0∞) +
        ENNReal.ofReal r⁻¹ * 0))) :=
      ENNReal.Tendsto.const_mul ((tendsto_finsetSum _ fun i _ => hgl ν c e i).add
        (ENNReal.Tendsto.const_mul (hal ν c e) (Or.inr ENNReal.ofReal_ne_top)))
        (Or.inr ENNReal.coe_ne_top)
    simpa using h1
  -- an a.e. convergent subsequence
  have hTM : TendstoInMeasure ρ (fun k => at' k ν c e) atTop (a ν c e) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (fun k => (hs k ν c e).continuous.aestronglyMeasurable)
      (ha.memLp ν c e).aestronglyMeasurable (hal ν c e)
  obtain ⟨ns, hns, hae⟩ := hTM.exists_seq_tendsto_ae
  have hlsc := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 4)
    (fun k => (hs (ns k) ν c e).continuous.aestronglyMeasurable) (a ν c e) hae
  refine hlsc.trans ?_
  have hlim : Tendsto (fun k => R + err (ns k)) atTop (𝓝 R) := by
    have := tendsto_const_nhds (x := R) |>.add (herr.comp hns.tendsto_atTop)
    simpa [Function.comp_def] using this
  calc atTop.liminf (fun k => eLpNorm (at' (ns k) ν c e) 4 ρ)
      ≤ atTop.liminf (fun k => R + err (ns k)) :=
        liminf_le_liminf (Eventually.of_forall fun k => hk (ns k))
    _ = R := hlim.liminf_eq

/-- Hölder for the commutator (measurable entries). -/
theorem eLpNorm_bComm_le' (o : Fin 4 → ℝ) (r : ℝ)
    (ham : ∀ ν c e, AEStronglyMeasurable (a ν c e) (volume.restrict (euclBall o r)))
    (μ ν : Fin 4) (c e : Fin m) :
    eLpNorm (bComm a μ ν c e) 2 (volume.restrict (euclBall o r)) ≤
      2 * m * (bL4 o r a * bL4 o r a) := by
  set ρ := volume.restrict (euclBall o r)
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

theorem sum_wcurv_le_wCurvNorm (o : Fin 4 → ℝ) (r : ℝ) (c e : Fin m) :
    ∑ μ', ∑ ν', eLpNorm (wCurv a ga μ' ν' c e) 2 (volume.restrict (euclBall o r)) ≤
      wCurvNorm o r a ga := by
  unfold wCurvNorm
  refine Finset.sum_le_sum fun μ' _ => Finset.sum_le_sum fun ν' _ => ?_
  exact (Finset.single_le_sum (f := fun e => eLpNorm (wCurv a ga μ' ν' c e) 2
      (volume.restrict (euclBall o r))) (fun _ _ => zero_le) (Finset.mem_univ e)).trans
    (Finset.single_le_sum (f := fun c => ∑ e, eLpNorm (wCurv a ga μ' ν' c e) 2
      (volume.restrict (euclBall o r))) (fun _ _ => zero_le) (Finset.mem_univ c))

/-- The weak curl of each entry is bounded by the curvature and the quadratic term. -/
theorem sum_wcurl_le (o : Fin 4 → ℝ) (r : ℝ)
    (ham : ∀ ν c e, AEStronglyMeasurable (a ν c e) (volume.restrict (euclBall o r)))
    (hgm : ∀ ν c e μ, AEStronglyMeasurable (ga ν c e μ) (volume.restrict (euclBall o r)))
    (c e : Fin m) :
    ∑ μ', ∑ ν', eLpNorm (wCurl ga c e μ' ν') 2 (volume.restrict (euclBall o r)) ≤
      wCurvNorm o r a ga + 32 * m * (bL4 o r a * bL4 o r a) := by
  set ρ := volume.restrict (euclBall o r)
  have hcm : ∀ μ' ν', AEStronglyMeasurable (bComm a μ' ν' c e) ρ := fun μ' ν' => by
    have e' : bComm a μ' ν' c e =
        ∑ k, (fun x => a μ' c k x * a ν' k e x - a ν' c k x * a μ' k e x) := by
      funext x; simp only [bComm, Finset.sum_apply]
    rw [e']
    exact Finset.aestronglyMeasurable_sum _ fun k _ =>
      ((ham μ' c k).mul (ham ν' k e)).sub ((ham ν' c k).mul (ham μ' k e))
  have hcv : ∀ μ' ν', AEStronglyMeasurable (wCurv a ga μ' ν' c e) ρ := fun μ' ν' =>
    ((hgm ν' c e μ').sub (hgm μ' c e ν')).add (hcm μ' ν')
  have h1 : ∀ μ' ν', eLpNorm (wCurl ga c e μ' ν') 2 ρ ≤
      eLpNorm (wCurv a ga μ' ν' c e) 2 ρ + 2 * m * (bL4 o r a * bL4 o r a) := fun μ' ν' => by
    have e1 : wCurl ga c e μ' ν' = fun x => wCurv a ga μ' ν' c e x - bComm a μ' ν' c e x := by
      funext x; simp only [wCurl, wCurv]; ring
    rw [e1]
    exact (eLpNorm_sub_le (hcv μ' ν') (hcm μ' ν') (by norm_num)).trans
      (add_le_add le_rfl (eLpNorm_bComm_le' o r ham μ' ν' c e))
  calc ∑ μ', ∑ ν', eLpNorm (wCurl ga c e μ' ν') 2 ρ
      ≤ ∑ μ', ∑ ν', (eLpNorm (wCurv a ga μ' ν' c e) 2 ρ + 2 * m * (bL4 o r a * bL4 o r a)) :=
        Finset.sum_le_sum fun μ' _ => Finset.sum_le_sum fun ν' _ => h1 μ' ν'
    _ = ∑ μ', ∑ ν', eLpNorm (wCurv a ga μ' ν' c e) 2 ρ + 32 * m * (bL4 o r a * bL4 o r a) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring
    _ ≤ wCurvNorm o r a ga + 32 * m * (bL4 o r a * bL4 o r a) := by
        gcongr; exact sum_wcurv_le_wCurvNorm o r c e

/-- The `L⁴` bound of each entry by the weak curl (Sobolev + Hodge + Poincaré). -/
theorem eLpNorm_four_le_weak {CS : ℝ≥0}
    (hCS : ∀ (o : Fin 4 → ℝ) (r : ℝ), 0 < r → ∀ u : (Fin 4 → ℝ) → ℂ, ContDiff ℝ 1 u →
      eLpNorm u (4 : ℝ≥0) (volume.restrict (euclBall o r)) ≤
        CS * (∑ i, eLpNorm (pd u i) 2 (volume.restrict (euclBall o r)) +
          ENNReal.ofReal r⁻¹ * eLpNorm u 2 (volume.restrict (euclBall o r))))
    (hr : 0 < r) (ha : IsWeakBallCoulomb o r a ga) (ν : Fin 4) (c e : Fin m) :
    eLpNorm (a ν c e) 4 (volume.restrict (euclBall o r)) ≤
      5 * CS * ∑ μ', ∑ ν', eLpNorm (wCurl ga c e μ' ν') 2 (volume.restrict (euclBall o r)) := by
  set K := ∑ μ', ∑ ν', eLpNorm (wCurl ga c e μ' ν') 2 (volume.restrict (euclBall o r))
  have h1 := weak_sobolev hCS hr ha ν c e
  have hgrad : ∀ i, eLpNorm (ga ν c e i) 2 (volume.restrict (euclBall o r)) ≤ K := fun i =>
    weak_hodge hr ha c e ν i
  have hL2 := weak_poincare hr ha c e ν
  have hrr : ENNReal.ofReal r⁻¹ * ENNReal.ofReal r = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hr.ne', ENNReal.ofReal_one]
  refine h1.trans ?_
  calc (CS : ℝ≥0∞) * (∑ i, eLpNorm (ga ν c e i) 2 (volume.restrict (euclBall o r)) +
        ENNReal.ofReal r⁻¹ * eLpNorm (a ν c e) 2 (volume.restrict (euclBall o r)))
      ≤ CS * (∑ _i : Fin 4, K + ENNReal.ofReal r⁻¹ * (ENNReal.ofReal r * K)) := by
        gcongr with i
        · exact hgrad i
    _ = 5 * CS * K := by
        rw [← mul_assoc (ENNReal.ofReal r⁻¹), hrr]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Weak

/-! ### The critical a-priori estimate for weak Coulomb forms -/

/-- **The critical Coulomb a-priori estimate on a Euclidean ball of `ℝ⁴`, weak forms**: there are
`δ > 0` and `C` depending only on `m` such that every weak Coulomb form `a` on `B = B_r(o)`
(`IsWeakBallCoulomb`: `H¹(B)`-limit of `C²` forms with vanishing normal component, weakly
co-closed) with `Σ‖a_{ν,ce}‖_{L⁴(B)} ≤ δ` satisfies `Σ‖a‖_{L⁴(B)} ≤ C ‖F_a‖_{L²(B)}`,
`Σ‖∂a‖_{L²(B)} ≤ 32 m² ‖F_a‖_{L²(B)}` and `‖a_{ν,ce}‖_{L²(B_r)} ≤ 2 r ‖F_a‖_{L²(B_r)}`, where
`F_a = ∂a - ∂a + [a, a]` is computed from the gradient data. -/
theorem coulomb_apriori_weak (m : ℕ) : ∃ δ : ℝ≥0, 0 < δ ∧ ∃ C : ℝ≥0,
    ∀ (o : Fin 4 → ℝ) (r : ℝ), 0 < r → ∀ (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
      (ga : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ),
      IsWeakBallCoulomb o r a ga → bL4 o r a ≤ δ →
      bL4 o r a ≤ C * wCurvNorm o r a ga ∧
      wGradNorm o r ga ≤ 32 * (m : ℝ≥0∞) ^ 2 * wCurvNorm o r a ga ∧
      (∀ ν c e, eLpNorm (a ν c e) 2 (volume.restrict (euclBall o r)) ≤
        2 * ENNReal.ofReal r * wCurvNorm o r a ga) := by
  obtain ⟨CS, hCS⟩ := sobolev_ball (n := 4) (by norm_num) (p' := 4) (by norm_num)
  set κ : ℝ≥0 := 640 * (m : ℝ≥0) ^ 3 * CS
  set δ : ℝ≥0 := (2 * κ + 1)⁻¹
  refine ⟨δ, by positivity, 40 * (m : ℝ≥0) ^ 2 * CS, fun o r hr a ga ha hX => ?_⟩
  have hq : (κ : ℝ≥0∞) * δ ≤ 2⁻¹ := coulombKappa_mul_le le_rfl
  set X := bL4 o r a
  set B := wCurvNorm o r a ga
  set ρ := volume.restrict (euclBall o r)
  have hXt : X ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hX
  have ham : ∀ ν c e, AEStronglyMeasurable (a ν c e) ρ := fun ν c e =>
    (ha.memLp ν c e).aestronglyMeasurable
  have hgm : ∀ ν c e μ, AEStronglyMeasurable (ga ν c e μ) ρ := fun ν c e μ =>
    (ha.memLp_grad ν c e μ).aestronglyMeasurable
  have hK := fun c e => sum_wcurl_le o r ham hgm c e
  have hent : ∀ ν c e, eLpNorm (a ν c e) 4 ρ ≤ 5 * CS * (B + 32 * m * (X * X)) := fun ν c e =>
    (eLpNorm_four_le_weak hCS hr ha ν c e).trans (by gcongr; exact hK c e)
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
  have hK2 : ∀ c e, ∑ μ', ∑ ν', eLpNorm (wCurl ga c e μ' ν') 2 ρ ≤ 2 * B := by
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
  · calc wGradNorm o r ga ≤ ∑ _ν : Fin 4, ∑ _c : Fin m, ∑ _e : Fin m, ∑ _μ : Fin 4, 2 * B := by
          unfold wGradNorm
          refine Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun c _ =>
            Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun μ _ => ?_
          exact (weak_hodge hr ha c e ν μ).trans (hK2 c e)
      _ = 32 * (m : ℝ≥0∞) ^ 2 * B := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  · calc eLpNorm (a ν c e) 2 ρ ≤ ENNReal.ofReal r *
          ∑ μ', ∑ ν', eLpNorm (wCurl ga c e μ' ν') 2 ρ := weak_poincare hr ha c e ν
      _ ≤ ENNReal.ofReal r * (2 * B) := by gcongr; exact hK2 c e
      _ = 2 * ENNReal.ofReal r * B := by ring

/-- Classical Coulomb forms are weak Coulomb forms (with their classical gradients). -/
theorem _root_.RenewalGeometry.BallAnalysis.IsBallCoulomb.isWeakBallCoulomb {m : ℕ}
    {o : Fin 4 → ℝ} {r : ℝ} (hr : 0 < r) {a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ}
    (ha : IsBallCoulomb o r a) :
    IsWeakBallCoulomb o r a (fun ν c e μ => pd (a ν c e) μ) := by
  have hfin := isFiniteMeasure_restrict_euclBall o hr.le
  refine ⟨fun ν c e => ?_, fun ν c e μ => ?_, ⟨fun _ => a, fun _ => ha.smooth, fun _ => ha.tangent,
    fun ν c e => by simp, fun ν c e μ => by simp⟩, fun c e => ?_⟩
  · have hc := (ha.smooth ν c e).continuous
    exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
      (integrableOn_euclBall hr.le (hc.norm.pow 2))
  · have hc := continuous_pd ((ha.smooth ν c e).of_le (by norm_num)) μ
    exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
      (integrableOn_euclBall hr.le (hc.norm.pow 2))
  · rw [ae_restrict_iff' (measurableSet_euclBall o r)]
    exact Eventually.of_forall fun x hx => ha.coulomb x hx c e

/-- Non-vacuity: the zero form is a weak Coulomb form, and the estimate applies to it. -/
example (m : ℕ) (o : Fin 4 → ℝ) (r : ℝ) (hr : 0 < r) :
    IsWeakBallCoulomb (m := m) o r (fun _ _ _ _ => 0) (fun _ _ _ _ _ => 0) := by
  have h := (show IsBallCoulomb (m := m) o r (fun _ _ _ _ => 0) from
    ⟨fun _ _ _ => contDiff_const, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp [pd]⟩).isWeakBallCoulomb hr
  have e : (fun (ν : Fin 4) (c e : Fin m) (μ : Fin 4) => pd (fun _ : Fin 4 → ℝ => (0 : ℂ)) μ) =
      fun _ _ _ _ => (fun _ => (0 : ℂ)) := by
    funext ν c e μ x; simp [pd]
  simpa [e] using h

end RenewalGeometry.BallAnalysis.WeakCoulomb
