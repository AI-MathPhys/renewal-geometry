/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallWeakProduct

/-!
# The normal trace of smooth approximants of weakly tangential fields
  (stage D2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

Let `w ∈ H⁴(B)⁴` be weakly tangential on `B = B_r(c) ⊂ ℝ⁴` (`IsWeakTangential`) and let `W_m` be
smooth fields converging to `w` in `H¹(B)` which are uniformly Cauchy on `B`.  Then the normal
component `f_m(y) = Σ_ν (y_ν - c_ν) W_{m,ν}(y)` tends to zero **uniformly on the sphere**:

* `abs_le_of_sqDist_le` — bounds on the open ball pass to the closed ball (continuity);
* `bounds_of_convHk4` — smooth `H⁴(B)`-convergent sequences are uniformly Cauchy and uniformly
  bounded on `B` together with their first derivatives (`H³(B) ⊂ L^∞`, `abs_le_n3`);
* `sphere_integral_eq` — the divergence theorem in the form
  `r² ∫_{S³} φ(c + rz) f(c + rz) dσ(z) = ∫_B div(φ W)`;
* `eq_zero_of_integral_sq` — a continuous function on the sphere with `∫ g² dσ = 0` vanishes
  (Mathlib: `volume.toSphere` charges open sets);
* `normal_trace_le` (**main result**): `|f_m(y)| ≤ 4 r e_m` on the sphere, where `e_m → 0` is the
  uniform Cauchy modulus.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis.TanApprox

open SobolevOpen BallReg BallAlg

set_option linter.unusedSectionVars false

variable (c : Fin 4 → ℝ) (r : ℝ)

theorem sqDist_line (y : Fin 4 → ℝ) (t : ℝ) : sqDist c (c + t • (y - c)) = t ^ 2 * sqDist c y := by
  simp only [sqDist, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Bounds on the open ball pass to the closed ball. -/
theorem abs_le_of_sqDist_le {r : ℝ} (hr : 0 < r) {u : (Fin 4 → ℝ) → ℝ} (hu : Continuous u) {K : ℝ}
    (h : ∀ x ∈ euclBall c r, |u x| ≤ K) {y : Fin 4 → ℝ} (hy : sqDist c y ≤ r ^ 2) : |u y| ≤ K := by
  have hcl : Continuous (fun t : ℝ => u (c + t • (y - c))) :=
    hu.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hlim : Tendsto (fun t : ℝ => u (c + t • (y - c))) (𝓝[<] 1) (𝓝 (u y)) := by
    have := hcl.continuousAt (x := 1) |>.tendsto
    simp only [one_smul, add_sub_cancel] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim.abs ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
  apply h
  show sqDist c (c + t • (y - c)) < r ^ 2
  rw [sqDist_line]
  have ht2 : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
  have hr2 : 0 < r ^ 2 := by positivity
  nlinarith [sqDist_nonneg' c y]
where
  sqDist_nonneg' (c y : Fin 4 → ℝ) : 0 ≤ sqDist c y :=
    Finset.sum_nonneg fun i _ => sq_nonneg _

theorem abs_sub_le_of_sqDist_le {r : ℝ} {y : Fin 4 → ℝ} (hy : sqDist c y ≤ r ^ 2) (hr : 0 ≤ r)
    (ν : Fin 4) : |y ν - c ν| ≤ r := by
  have h1 : (y ν - c ν) ^ 2 ≤ sqDist c y :=
    Finset.single_le_sum (f := fun i => (y i - c i) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ ν)
  exact abs_le_of_sq_le_sq' (by nlinarith) hr |>.elim (fun h1 h2 => abs_le.mpr ⟨h1, h2⟩)

/-! ### Uniform bounds from `H⁴(B)` convergence -/

/-- **Smooth `H⁴(B)`-convergent sequences are uniformly Cauchy and bounded on `B`, with their
first derivatives.** -/
theorem bounds_of_convHk4 {r : ℝ} (hr : 0 < r) {φ : ℕ → (Fin 4 → ℝ) → ℝ}
    (hφ : ∀ m, ContDiff ℝ ∞ (φ m)) {u : (Fin 4 → ℝ) → ℝ} (hc : ConvHk (euclBall c r) 4 φ u) :
    ∃ (N : ℕ) (e : ℕ → ℝ) (M : ℝ), Tendsto e atTop (𝓝 0) ∧ (∀ m, 0 ≤ e m) ∧ 0 ≤ M ∧
      ∀ m ≥ N, ∀ x ∈ euclBall c r, (∀ p ≥ N, |φ m x - φ p x| ≤ e m + e p) ∧
        |φ m x| ≤ M ∧ ∀ i, |pd (φ m) i x| ≤ M := by
  obtain ⟨C, hC, hb⟩ := abs_le_n3 c r hr
  obtain ⟨D, G, hG, hD, hd, hdG⟩ := exists_word_data c r hr hφ hc
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hD.eventually (gt_mem_nhds zero_lt_one))
  have hDt : ∀ m ≥ N, D m ≠ ⊤ := fun m hm => ne_top_of_lt (hN m hm)
  have hC4 : C * 4 ≠ ⊤ := ENNReal.mul_ne_top hC (by norm_num)
  set e : ℕ → ℝ := fun m => (C * 4 * D m).toReal
  set M : ℝ := (C * 4 * (G + 1)).toReal
  have hM : C * 4 * (G + 1) ≠ ⊤ := ENNReal.mul_ne_top hC4 (by simp [hG])
  refine ⟨N, e, M, ?_, fun m => ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, fun m hm x hx => ?_⟩
  · have h1 : Tendsto (fun m => C * 4 * D m) atTop (𝓝 (C * 4 * 0)) :=
      ENNReal.Tendsto.const_mul hD (Or.inr hC4)
    rw [mul_zero] at h1
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [e, Function.comp_def] using this
  have hnW : ∀ v : (Fin 4 → ℝ) → ℝ, n3 c r v ≤ 4 * nW c r 4 v := fun v =>
    (n3_le_nW c r (le_refl 3) v).trans (by gcongr; exact nW_mono c r (by norm_num) v)
  have hφm : nW c r 4 (φ m) ≤ G + 1 := (hdG m).trans (by gcongr; exact (hN m hm).le)
  refine ⟨fun p hp => ?_, ?_, fun i => ?_⟩
  · have h1 := hb (fun y => φ m y - φ p y) ((hφ m).sub (hφ p)) x hx
    have h2 : C * n3 c r (fun y => φ m y - φ p y) ≤ C * 4 * D m + C * 4 * D p := by
      calc C * n3 c r (fun y => φ m y - φ p y) ≤ C * (4 * (D m + D p)) := by
            gcongr; exact (hnW _).trans (by gcongr; exact hd m p)
        _ = C * 4 * D m + C * 4 * D p := by ring
    have hfin : C * 4 * D m + C * 4 * D p ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hC4 (hDt m hm), ENNReal.mul_ne_top hC4 (hDt p hp)⟩
    have := (ENNReal.ofReal_le_iff_le_toReal hfin).mp (h1.trans h2)
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top hC4 (hDt m hm))
      (ENNReal.mul_ne_top hC4 (hDt p hp))] at this
  · have h1 := hb (φ m) (hφ m) x hx
    have h2 : C * n3 c r (φ m) ≤ C * 4 * (G + 1) := by
      calc C * n3 c r (φ m) ≤ C * (4 * (G + 1)) := by gcongr; exact (hnW _).trans (by gcongr)
        _ = C * 4 * (G + 1) := by ring
    exact (ENNReal.ofReal_le_iff_le_toReal hM).mp (h1.trans h2)
  · have h1 := hb (pd (φ m) i) (contDiff_pd (hφ m) i) x hx
    have h2 : C * n3 c r (pd (φ m) i) ≤ C * 4 * (G + 1) := by
      have h3 : n3 c r (pd (φ m) i) ≤ 4 * nW c r 4 (φ m) := by
        have := n3_pdw_le c r (φ m) (a := [i]) (s := 4) (by simp)
        simpa using this
      calc C * n3 c r (pd (φ m) i) ≤ C * (4 * (G + 1)) := by gcongr; exact h3.trans (by gcongr)
        _ = C * 4 * (G + 1) := by ring
    exact (ENNReal.ofReal_le_iff_le_toReal hM).mp (h1.trans h2)

/-! ### The divergence theorem on the sphere subtype -/

/-- The unit sphere of `ℝ⁴` (Euclidean) and its surface measure. -/
abbrev S3 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- The point `c + r z` of the sphere `∂B_r(c)`. -/
def sph (z : S3) : Fin 4 → ℝ := c + r • sphereEmb 4 z

theorem continuous_sph : Continuous (sph c r) := by
  unfold sph sphereEmb
  exact continuous_const.add
    (((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val).const_smul r)

theorem sqDist_sph (z : S3) : sqDist c (sph c r z) = r ^ 2 := by
  have h := sum_sq_sphereEmb z
  simp only [sqDist, sph, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
  calc ∑ i, (r * sphereEmb 4 z i) ^ 2 = r ^ 2 * ∑ i, sphereEmb 4 z i ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = r ^ 2 := by rw [h, mul_one]

/-- Every point of the sphere `∂B_r(c)` is `c + r z`. -/
theorem exists_sph {r : ℝ} (hr : 0 < r) {y : Fin 4 → ℝ} (hy : sqDist c y = r ^ 2) :
    ∃ z : S3, sph c r z = y := by
  set v : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2 (r⁻¹ • (y - c))
  have hv : v ∈ S3 := by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simp only [v, PiLp.toLp_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Real.norm_eq_abs,
      sq_abs]
    have : ∑ i, (r⁻¹ * (y i - c i)) ^ 2 = (r⁻¹) ^ 2 * sqDist c y := by
      simp only [sqDist, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hy]; field_simp
  refine ⟨⟨v, hv⟩, ?_⟩
  funext i
  simp only [sph, sphereEmb, v, Pi.add_apply, Pi.smul_apply, smul_eq_mul, WithLp.ofLp_toLp,
    Pi.sub_apply]
  field_simp
  ring

/-- **The divergence theorem against the normal component**:
`r² ∫_{S³} φ(c + rz) f(c + rz) dσ = ∫_B Σ_ν ∂_ν(φ W_ν)`, `f(y) = Σ_ν (y_ν - c_ν) W_ν(y)`. -/
theorem sphere_integral_eq {r : ℝ} (hr : 0 < r) {φ : (Fin 4 → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ)
    {W : Fin 4 → (Fin 4 → ℝ) → ℝ} (hW : ∀ ν, ContDiff ℝ 1 (W ν)) :
    r ^ 2 * ∫ z : S3, φ (sph c r z) * ∑ ν, (sph c r z ν - c ν) * W ν (sph c r z)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere =
      ∫ x in euclBall c r, ∑ ν, pd (fun y => φ y * W ν y) ν x := by
  have hX : ∀ ν, ContDiff ℝ 1 (fun y => φ y * W ν y) := fun ν => hφ.mul (hW ν)
  rw [divergence_ball c hr _ hX, integral_sphereMeasure]
  have e : ∀ z : S3, (∑ i, φ (c + r • sphereEmb 4 z) * W i (c + r • sphereEmb 4 z) *
      sphereEmb 4 z i) * r = φ (sph c r z) * ∑ ν, (sph c r z ν - c ν) * W ν (sph c r z) := by
    intro z
    simp only [sph, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [← e]
  rw [integral_mul_const]
  norm_num
  ring

/-- A continuous function on the sphere with `∫ g² dσ = 0` vanishes identically. -/
theorem eq_zero_of_integral_sq {g : S3 → ℝ} (hg : Continuous g)
    (h : ∫ z, g z ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere = 0) : g = 0 := by
  have hi : Integrable (fun z => g z ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere :=
    (hg.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h0 := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg (g z)) hi).mp h
  have h1 : (fun z => g z ^ 2) = fun _ => (0 : ℝ) :=
    (Continuous.ae_eq_iff_eq _ (hg.pow 2) continuous_const).mp h0
  funext z
  have := congrFun h1 z
  simpa using this

/-! ### The normal trace tends to zero on the sphere -/

/-- The normal component `f(y) = Σ_ν (y_ν - c_ν) W_ν(y)`. -/
def nrm (W : Fin 4 → (Fin 4 → ℝ) → ℝ) (y : Fin 4 → ℝ) : ℝ := ∑ ν, (y ν - c ν) * W ν y

theorem contDiff_nrm {W : Fin 4 → (Fin 4 → ℝ) → ℝ} {k : WithTop ℕ∞} (hW : ∀ ν, ContDiff ℝ k (W ν)) :
    ContDiff ℝ k (nrm c W) := by
  unfold nrm
  exact ContDiff.sum fun ν _ => ((contDiff_apply ℝ ℝ ν).sub contDiff_const).mul (hW ν)

variable [hr : Fact (0 < r)]

/-- The divergence integrals converge to zero for a weakly tangential limit. -/
theorem tendsto_div_integral {W : ℕ → Fin 4 → (Fin 4 → ℝ) → ℝ}
    (hW : ∀ m ν, ContDiff ℝ 1 (W m ν)) {w : Fin 4 → (Fin 4 → ℝ) → ℝ}
    {gw : Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℝ}
    (hwm : ∀ ν, MemLp (w ν) 2 (volume.restrict (euclBall c r)))
    (hgm : ∀ ν μ, MemLp (gw ν μ) 2 (volume.restrict (euclBall c r)))
    (hL2 : ∀ ν, Tendsto (fun m => eLpNorm (W m ν - w ν) 2 (volume.restrict (euclBall c r)))
      atTop (𝓝 0))
    (hD : ∀ ν μ, Tendsto (fun m => eLpNorm (pd (W m ν) μ - gw ν μ) 2
      (volume.restrict (euclBall c r))) atTop (𝓝 0))
    (htan : IsWeakTangential c r w (fun x => ∑ ν, gw ν ν x))
    {φ : (Fin 4 → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Tendsto (fun m => ∫ x in euclBall c r, ∑ ν, pd (fun y => φ y * W m ν y) ν x) atTop (𝓝 0) := by
  set ρ := volume.restrict (euclBall c r)
  have hfin := isFiniteMeasure_restrict_euclBall c hr.out.le
  have hB := measurableSet_euclBall c r
  -- bounds of the test function and its gradient on the ball
  have hbd : ∀ {h : (Fin 4 → ℝ) → ℝ}, Continuous h → ∃ M, 0 ≤ M ∧ ∀ᵐ x ∂ρ, |h x| ≤ M := by
    intro h hh
    obtain ⟨M, hM⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hh.continuousOn
    refine ⟨max M 0, le_max_right _ _, ?_⟩
    rw [ae_restrict_iff' hB]
    refine Eventually.of_forall fun x hx => ?_
    have hx' : x ∈ closedBall c r := euclBall_subset_closedBall c hr.out.le hx
    exact (Real.norm_eq_abs _ ▸ hM x hx').trans (le_max_left _ _)
  -- pointwise expansion of the divergence
  have hexp : ∀ m, ∫ x in euclBall c r, ∑ ν, pd (fun y => φ y * W m ν y) ν x =
      (∑ ν, ∫ x in euclBall c r, pd φ ν x * W m ν x) +
        ∫ x in euclBall c r, φ x * ∑ ν, pd (W m ν) ν x := by
    intro m
    have hpt : ∀ x, ∑ ν, pd (fun y => φ y * W m ν y) ν x =
        ∑ ν, pd φ ν x * W m ν x + φ x * ∑ ν, pd (W m ν) ν x := by
      intro x
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ν _ =>
        pd_mul_real ((hφ.differentiable one_ne_zero) x) (((hW m ν).differentiable one_ne_zero) x) ν
    simp_rw [hpt]
    have hi1 : ∀ ν, Integrable (fun x => pd φ ν x * W m ν x) ρ := fun ν =>
      integrableOn_euclBall hr.out.le ((continuous_pd hφ ν).mul (hW m ν).continuous)
    have hi2 : Integrable (fun x => φ x * ∑ ν, pd (W m ν) ν x) ρ :=
      integrableOn_euclBall hr.out.le (hφ.continuous.mul
        (continuous_finsetSum _ fun ν _ => continuous_pd (hW m ν) ν))
    rw [integral_add (integrable_finsetSum _ fun ν _ => hi1 ν) hi2,
      integral_finsetSum _ fun ν _ => hi1 ν]
  refine Tendsto.congr (fun m => (hexp m).symm) ?_
  -- the limit
  have hlim1 : ∀ ν, Tendsto (fun m => ∫ x in euclBall c r, pd φ ν x * W m ν x) atTop
      (𝓝 (∫ x in euclBall c r, pd φ ν x * w ν x)) := by
    intro ν
    obtain ⟨M, hM0, hM⟩ := hbd (continuous_pd hφ ν)
    exact tendsto_setIntegral_mul c r hM0 (continuous_pd hφ ν).aestronglyMeasurable hM
      (fun m => integrableOn_euclBall hr.out.le (hW m ν).continuous)
      ((hwm ν).integrable (by norm_num))
      (tendsto_eLpNorm_one_of_two c r (fun m => (hW m ν).continuous.aestronglyMeasurable)
        (hwm ν).aestronglyMeasurable (hL2 ν))
  have hdivm : ∀ m, AEStronglyMeasurable (fun x => ∑ ν, pd (W m ν) ν x) ρ := fun m =>
    (continuous_finsetSum _ fun ν _ => continuous_pd (hW m ν) ν).aestronglyMeasurable
  have hdivw : MemLp (fun x => ∑ ν, gw ν ν x) 2 ρ := by
    have := memLp_finset_sum' (Finset.univ : Finset (Fin 4)) fun ν _ => hgm ν ν
    convert this using 1
    funext x; simp [Finset.sum_apply]
  have hdivL2 : Tendsto (fun m => eLpNorm ((fun x => ∑ ν, pd (W m ν) ν x) -
      fun x => ∑ ν, gw ν ν x) 2 ρ) atTop (𝓝 0) := by
    have hle : ∀ m, eLpNorm ((fun x => ∑ ν, pd (W m ν) ν x) - fun x => ∑ ν, gw ν ν x) 2 ρ ≤
        ∑ ν, eLpNorm (pd (W m ν) ν - gw ν ν) 2 ρ := by
      intro m
      have e : ((fun x => ∑ ν, pd (W m ν) ν x) - fun x => ∑ ν, gw ν ν x) =
          ∑ ν, (pd (W m ν) ν - gw ν ν) := by
        funext x; simp [Finset.sum_apply, Finset.sum_sub_distrib]
      rw [e]
      exact eLpNorm_sum_le (fun ν _ => (continuous_pd (hW m ν) ν).aestronglyMeasurable.sub
        (hgm ν ν).aestronglyMeasurable) (by norm_num)
    have hs : Tendsto (fun m => ∑ ν, eLpNorm (pd (W m ν) ν - gw ν ν) 2 ρ) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun ν _ => hD ν ν
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => bot_le) hle
  have hlim2 : Tendsto (fun m => ∫ x in euclBall c r, φ x * ∑ ν, pd (W m ν) ν x) atTop
      (𝓝 (∫ x in euclBall c r, φ x * ∑ ν, gw ν ν x)) := by
    obtain ⟨M, hM0, hM⟩ := hbd hφ.continuous
    exact tendsto_setIntegral_mul c r hM0 hφ.continuous.aestronglyMeasurable hM
      (fun m => integrableOn_euclBall hr.out.le
        (continuous_finsetSum _ fun ν _ => continuous_pd (hW m ν) ν))
      (hdivw.integrable (by norm_num))
      (tendsto_eLpNorm_one_of_two c r hdivm hdivw.aestronglyMeasurable hdivL2)
  have hzero : (∑ ν, ∫ x in euclBall c r, pd φ ν x * w ν x) +
      ∫ x in euclBall c r, φ x * ∑ ν, gw ν ν x = 0 := by
    have h1 := htan φ hφ
    have e1 : ∑ ν, ∫ x in euclBall c r, pd φ ν x * w ν x =
        ∑ ν, ∫ x in euclBall c r, w ν x * pd φ ν x :=
      Finset.sum_congr rfl fun ν _ => by congr 1; funext x; ring
    have e2 : ∫ x in euclBall c r, φ x * ∑ ν, gw ν ν x =
        ∫ x in euclBall c r, (∑ ν, gw ν ν x) * φ x := by congr 1; funext x; ring
    rw [e1, e2, h1]; ring
  rw [← hzero]
  exact (tendsto_finsetSum _ fun ν _ => hlim1 ν).add hlim2

/-- **The normal trace of the approximants tends to zero uniformly on the sphere**: if smooth
fields `W_m` converge to a weakly tangential field `w` in `H¹(B)` and are uniformly Cauchy on `B`
(`|W_{m,ν} - W_{p,ν}| ≤ e_m + e_p`, `e_m → 0`), then `|Σ_ν (y_ν - c_ν) W_{m,ν}(y)| ≤ 4 r e_m` on
the sphere `∂B_r(c)`. -/
theorem normal_trace_le {W : ℕ → Fin 4 → (Fin 4 → ℝ) → ℝ}
    (hW : ∀ m ν, ContDiff ℝ ∞ (W m ν)) {w : Fin 4 → (Fin 4 → ℝ) → ℝ}
    {gw : Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℝ}
    (hwm : ∀ ν, MemLp (w ν) 2 (volume.restrict (euclBall c r)))
    (hgm : ∀ ν μ, MemLp (gw ν μ) 2 (volume.restrict (euclBall c r)))
    (hL2 : ∀ ν, Tendsto (fun m => eLpNorm (W m ν - w ν) 2 (volume.restrict (euclBall c r)))
      atTop (𝓝 0))
    (hD : ∀ ν μ, Tendsto (fun m => eLpNorm (pd (W m ν) μ - gw ν μ) 2
      (volume.restrict (euclBall c r))) atTop (𝓝 0))
    (htan : IsWeakTangential c r w (fun x => ∑ ν, gw ν ν x))
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) {N : ℕ}
    (hcau : ∀ m ≥ N, ∀ p ≥ N, ∀ x ∈ euclBall c r, ∀ ν, |W m ν x - W p ν x| ≤ e m + e p) :
    ∀ m ≥ N, ∀ y, sqDist c y = r ^ 2 → |nrm c (W m) y| ≤ 4 * r * e m := by
  have hr0 := hr.out
  set σ := (volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere
  have hW1 : ∀ m ν, ContDiff ℝ 1 (W m ν) := fun m ν => (hW m ν).of_le (by simp)
  -- Cauchy bounds on the sphere
  have hcs : ∀ m ≥ N, ∀ p ≥ N, ∀ y, sqDist c y = r ^ 2 →
      |nrm c (W m) y - nrm c (W p) y| ≤ 4 * r * (e m + e p) := by
    intro m hm p hp y hy
    have h1 : ∀ ν, |W m ν y - W p ν y| ≤ e m + e p := fun ν =>
      abs_le_of_sqDist_le c hr0 ((hW m ν).continuous.sub (hW p ν).continuous)
        (fun x hx => hcau m hm p hp x hx ν) hy.le
    have e1 : nrm c (W m) y - nrm c (W p) y = ∑ ν, (y ν - c ν) * (W m ν y - W p ν y) := by
      simp only [nrm, ← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun ν _ => by ring
    rw [e1]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ ν, |(y ν - c ν) * (W m ν y - W p ν y)| ≤ ∑ _ν : Fin 4, r * (e m + e p) := by
          refine Finset.sum_le_sum fun ν _ => ?_
          rw [abs_mul]
          exact mul_le_mul (abs_sub_le_of_sqDist_le c hy.le hr0.le ν) (h1 ν) (abs_nonneg _)
            hr0.le
      _ = 4 * r * (e m + e p) := by simp; ring
  -- the functions on the sphere subtype
  set G : ℕ → S3 → ℝ := fun m z => nrm c (W m) (sph c r z)
  have hGc : ∀ m, Continuous (G m) := fun m =>
    (contDiff_nrm c (hW m)).continuous.comp (continuous_sph c r)
  -- pointwise limits
  have hcauchy : ∀ z, CauchySeq fun m => G m z := by
    intro z
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have h4 : Tendsto (fun m => 4 * r * (e m + e m)) atTop (𝓝 (4 * r * (0 + 0))) :=
      (he.add he).const_mul _
    rw [add_zero, mul_zero] at h4
    obtain ⟨N1, hN1⟩ := eventually_atTop.mp (he.eventually (gt_mem_nhds (show 0 < ε / (8 * r + 1) by
      positivity)))
    refine ⟨max N N1, fun m hm => ?_⟩
    rw [Real.dist_eq]
    have hb := hcs m (le_of_max_le_left hm) (max N N1) (le_max_left _ _) (sph c r z)
      (sqDist_sph c r z)
    have h1 := hN1 m (le_of_max_le_right hm)
    have h2 := hN1 (max N N1) (le_max_right _ _)
    have h3 : 4 * r * (e m + e (max N N1)) < ε := by
      have : 4 * r * (e m + e (max N N1)) ≤ 8 * r * (ε / (8 * r + 1)) := by nlinarith
      have h5 : 8 * r * (ε / (8 * r + 1)) < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
      linarith
    exact lt_of_le_of_lt hb h3
  choose Gl hGl using fun z => cauchySeq_tendsto_of_complete (hcauchy z)
  have hGb : ∀ m ≥ N, ∀ z, |G m z - Gl z| ≤ 4 * r * e m := by
    intro m hm z
    have hlim : Tendsto (fun p => |G m z - G p z|) atTop (𝓝 |G m z - Gl z|) :=
      (tendsto_const_nhds.sub (hGl z)).abs
    have hlim2 : Tendsto (fun p => 4 * r * (e m + e p)) atTop (𝓝 (4 * r * (e m + 0))) :=
      (tendsto_const_nhds.add he).const_mul _
    rw [add_zero] at hlim2
    refine le_of_tendsto_of_tendsto hlim hlim2 ?_
    filter_upwards [eventually_ge_atTop N] with p hp
    exact hcs m hm p hp _ (sqDist_sph c r z)
  have hTU : TendstoUniformly G Gl atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have h4 : Tendsto (fun m => 4 * r * e m) atTop (𝓝 (4 * r * 0)) := he.const_mul _
    rw [mul_zero] at h4
    filter_upwards [eventually_ge_atTop N, h4.eventually (gt_mem_nhds hε)] with m hm hm2
    intro z
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt (hGb m hm z) hm2
  have hGlc : Continuous Gl := hTU.continuous (Eventually.of_forall hGc).frequently
  -- integrals against `G p` vanish in the limit
  have hint0 : ∀ p, ∫ z, G p z * Gl z ∂σ = 0 := by
    intro p
    have hφ : ContDiff ℝ 1 (nrm c (W p)) := (contDiff_nrm c (hW p)).of_le (by simp)
    -- `r² ∫ G_p G_m → 0`
    have h1 : Tendsto (fun m => r ^ 2 * ∫ z, G p z * G m z ∂σ) atTop (𝓝 0) := by
      have := tendsto_div_integral c r (fun m ν => hW1 m ν) hwm hgm hL2 hD htan hφ
      refine this.congr fun m => ?_
      exact (sphere_integral_eq c hr0 hφ (hW1 m)).symm
    have h2 : Tendsto (fun m => ∫ z, G p z * G m z ∂σ) atTop (𝓝 0) := by
      have := h1.const_mul (r ^ 2)⁻¹
      rw [mul_zero] at this
      refine this.congr fun m => ?_
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    -- and `∫ G_p G_m → ∫ G_p Gl`
    obtain ⟨Mp, hMp⟩ : ∃ M, ∀ z, |G p z| ≤ M := by
      obtain ⟨M, hM⟩ := (isCompact_univ (X := S3)).exists_bound_of_continuousOn
        (hGc p).continuousOn
      exact ⟨M, fun z => by simpa [Real.norm_eq_abs] using hM z (mem_univ z)⟩
    have h3 : Tendsto (fun m => ∫ z, G p z * G m z ∂σ) atTop (𝓝 (∫ z, G p z * Gl z ∂σ)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hb : ∀ m ≥ N, ‖(∫ z, G p z * G m z ∂σ) - ∫ z, G p z * Gl z ∂σ‖ ≤
          Mp * (4 * r * e m) * (σ univ).toReal := by
        intro m hm
        have hi1 : Integrable (fun z => G p z * G m z) σ :=
          ((hGc p).mul (hGc m)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        have hi2 : Integrable (fun z => G p z * Gl z) σ :=
          ((hGc p).mul hGlc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        rw [← integral_sub hi1 hi2]
        refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
        exact mul_le_mul (hMp z) (hGb m hm z) (abs_nonneg _) ((abs_nonneg _).trans (hMp z))
      have hlim : Tendsto (fun m => Mp * (4 * r * e m) * (σ univ).toReal) atTop
          (𝓝 (Mp * (4 * r * 0) * (σ univ).toReal)) :=
        ((he.const_mul (4 * r)).const_mul Mp).mul_const _
      rw [mul_zero, mul_zero, zero_mul] at hlim
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
      filter_upwards [eventually_ge_atTop N] with m hm using hb m hm
    exact tendsto_nhds_unique h3 h2
  -- hence `∫ Gl² = 0`
  have hsq : ∫ z, Gl z ^ 2 ∂σ = 0 := by
    have h1 : Tendsto (fun p => ∫ z, G p z * Gl z ∂σ) atTop (𝓝 (∫ z, Gl z * Gl z ∂σ)) := by
      have hb : ∀ᶠ p in atTop, ‖(∫ z, G p z * Gl z ∂σ) - ∫ z, Gl z * Gl z ∂σ‖ ≤
          (4 * r * e p) * (sSup (range fun z => |Gl z|) ) * (σ univ).toReal := by
        filter_upwards [eventually_ge_atTop N] with p hp
        have hbdd : BddAbove (range fun z => |Gl z|) := by
          obtain ⟨M, hM⟩ := (isCompact_univ (X := S3)).exists_bound_of_continuousOn
            hGlc.continuousOn
          exact ⟨M, by rintro _ ⟨z, rfl⟩; simpa [Real.norm_eq_abs] using hM z (mem_univ z)⟩
        have hi1 : Integrable (fun z => G p z * Gl z) σ :=
          ((hGc p).mul hGlc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        have hi2 : Integrable (fun z => Gl z * Gl z) σ :=
          (hGlc.mul hGlc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        rw [← integral_sub hi1 hi2]
        refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
        exact mul_le_mul (hGb p hp z) (le_csSup hbdd ⟨z, rfl⟩) (abs_nonneg _)
          (by have := hGb p hp z; linarith [abs_nonneg (G p z - Gl z)])
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hlim : Tendsto (fun p => (4 * r * e p) * (sSup (range fun z => |Gl z|)) *
          (σ univ).toReal) atTop (𝓝 ((4 * r * 0) * (sSup (range fun z => |Gl z|)) *
          (σ univ).toReal)) := ((he.const_mul (4 * r)).mul_const _).mul_const _
      rw [mul_zero, zero_mul, zero_mul] at hlim
      exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb hlim
    have h2 := tendsto_nhds_unique h1 (tendsto_const_nhds.congr fun p => (hint0 p).symm)
    simpa [sq] using h2
  have hGl0 := eq_zero_of_integral_sq hGlc hsq
  intro m hm y hy
  obtain ⟨z, rfl⟩ := exists_sph c hr0 hy
  have := hGb m hm z
  rw [hGl0] at this
  simpa using this

end RenewalGeometry.BallAnalysis.TanApprox
