/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallGaffney

/-!
# Gluing across a sphere and the reflection extension of functions on a ball
  (stage C2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `integral_pd_ball_complex`, `integral_ofReal_pd_mul_ball`: Gauss–Green and integration by
  parts on `B_r(c)` for complex `C¹` functions (real and imaginary parts of `divergence_ball`);
* `hasWeakPartial_glue` (**gluing lemma**): if `v₁, v₂ ∈ C¹(ℝⁿ)` agree on `∂B_r(c)`, the
  function equal to `v₁` in the ball and to `v₂` outside has weak partial derivatives on `ℝⁿ`,
  equal to `∂_i v₁` in the ball and `∂_i v₂` outside (the boundary terms of the two
  integrations by parts cancel);
* the **radial reflection** `reflBall c r x = c + (2r/|x - c| - 1)(x - c)` across the sphere
  (`reflBall_ray`: `c + ρω ↦ c + (2r - ρ)ω`; `reflBall_eq_self` on the sphere), the cutoff
  `extCut` (`1` on `[1/2, 2]`, `0` off `(1/4, 9/4)`), the outer piece
  `extOut c r u = θ(|x-c|²/r²) · u ∘ reflBall` (`C¹` on `ℝⁿ`, `contDiff_extOut`; equal to `u` on
  the sphere) and the **extension** `ballExt c r u` (`u` in the ball, `extOut` outside) with weak
  gradient `ballExtGrad` (`hasWeakPartial_ballExt`).
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ} [NeZero n]

instance decidableMemEuclBall (c : Fin n → ℝ) (r : ℝ) : DecidablePred (· ∈ euclBall c r) :=
  fun x => inferInstanceAs (Decidable (sqDist c x < r ^ 2))

theorem pd_mul_cc {f g : (Fin n → ℝ) → ℂ} {x : Fin n → ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (μ : Fin n) :
    pd (fun y => f y * g y) μ x = pd f μ x * g x + f x * pd g μ x := by
  unfold pd
  rw [show (fun y => f y * g y) = f * g from rfl, (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-! ### Complex Gauss–Green and the gluing lemma -/

/-- **Gauss–Green on a ball for complex `C¹` functions**:
`∫_{B_r(c)} ∂_i f = r^{n-1} ∫_{S^{n-1}} f(c + rω) ω_i dσ`. -/
theorem integral_pd_ball_complex (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ 1 f) (i : Fin n) :
    ∫ x in euclBall c r, pd f i x =
      ((r ^ (n - 1) : ℝ) : ℂ) * ∫ w, f (c + r • w) * ((w i : ℝ) : ℂ) ∂(sphereMeasure n) := by
  have hre := integral_pd_ball c hr (Complex.reCLM.contDiff.comp hf) i
  have him := integral_pd_ball c hr (Complex.imCLM.contDiff.comp hf) i
  have hint1 : Integrable (fun x => pd f i x) (volume.restrict (euclBall c r)) :=
    integrableOn_euclBall hr.le (continuous_pd hf i)
  have hcf : Continuous fun w : Fin n → ℝ => f (c + r • w) * ((w i : ℝ) : ℂ) := by
    have := hf.continuous; fun_prop
  have hint2 := integrable_sphereMeasure (n := n) hcf
  have e1 : ∀ x, pd (Complex.reCLM ∘ f) i x = (pd f i x).re := fun x => pd_re hf i x
  have e2 : ∀ x, pd (Complex.imCLM ∘ f) i x = (pd f i x).im := fun x => pd_im hf i x
  simp only [e1, e2] at hre him
  apply Complex.ext
  · rw [Complex.re_ofReal_mul, ← RCLike.re_to_complex, ← integral_re hint1,
      ← RCLike.re_to_complex, ← integral_re hint2]
    simpa [Complex.mul_re] using hre
  · rw [Complex.im_ofReal_mul, ← RCLike.im_to_complex, ← integral_im hint1,
      ← RCLike.im_to_complex, ← integral_im hint2]
    simpa [Complex.mul_im] using him

theorem pd_ofReal_fun {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (i : Fin n) (x : Fin n → ℝ) :
    pd (fun y => ((φ y : ℝ) : ℂ)) i x = ((pd φ i x : ℝ) : ℂ) := pd_ofReal hφ i x

/-- **Integration by parts on a ball** for a real `C¹` weight `φ` and a complex `C¹` `v`:
`∫_B (∂_i φ) v = r^{n-1} ∫ φ v ω_i dσ - ∫_B φ ∂_i v`. -/
theorem integral_ofReal_pd_mul_ball (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) {v : (Fin n → ℝ) → ℂ} (hv : ContDiff ℝ 1 v)
    (i : Fin n) :
    ∫ x in euclBall c r, ((pd φ i x : ℝ) : ℂ) * v x =
      ((r ^ (n - 1) : ℝ) : ℂ) *
          ∫ w, ((φ (c + r • w) : ℝ) : ℂ) * v (c + r • w) * ((w i : ℝ) : ℂ) ∂(sphereMeasure n) -
        ∫ x in euclBall c r, ((φ x : ℝ) : ℂ) * pd v i x := by
  have hφc : ContDiff ℝ 1 (fun y => ((φ y : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have hprod : ContDiff ℝ 1 (fun y => ((φ y : ℝ) : ℂ) * v y) := hφc.mul hv
  have h := integral_pd_ball_complex c hr hprod i
  have hpd : ∀ x, pd (fun y => ((φ y : ℝ) : ℂ) * v y) i x =
      ((pd φ i x : ℝ) : ℂ) * v x + ((φ x : ℝ) : ℂ) * pd v i x := fun x => by
    rw [pd_mul_cc ((hφc.differentiable (by norm_num)) x) ((hv.differentiable (by norm_num)) x),
      pd_ofReal_fun hφ]
  simp only [hpd] at h
  rw [integral_add (f := fun x => ((pd φ i x : ℝ) : ℂ) * v x)
    (g := fun x => ((φ x : ℝ) : ℂ) * pd v i x) (integrableOn_euclBall hr.le
    ((Complex.continuous_ofReal.comp (continuous_pd hφ i)).mul hv.continuous))
    (integrableOn_euclBall hr.le (hφc.continuous.mul (continuous_pd hv i)))] at h
  rw [← h]; ring

/-- **The gluing lemma**: let `v₁, v₂` be complex `C¹` functions on `ℝⁿ` that agree on the
sphere `∂B_r(c)`.  The function equal to `v₁` in the open ball and to `v₂` outside has weak
partial derivatives on `ℝⁿ`, equal to `∂_i v₁` in the ball and `∂_i v₂` outside. -/
theorem hasWeakPartial_glue (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {v₁ v₂ : (Fin n → ℝ) → ℂ}
    (h₁ : ContDiff ℝ 1 v₁) (h₂ : ContDiff ℝ 1 v₂)
    (hS : ∀ y, sqDist c y = r ^ 2 → v₁ y = v₂ y) (i : Fin n) :
    HasWeakPartial univ i ((euclBall c r).piecewise v₁ v₂)
      ((euclBall c r).piecewise (pd v₁ i) (pd v₂ i)) := by
  intro φ hφ
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  have hB := measurableSet_euclBall c r
  have hcpd : Continuous fun x => ((pd φ i x : ℝ) : ℂ) := Complex.continuous_ofReal.comp
    (continuous_pd hφ1 i)
  have hcφ : Continuous fun x => ((φ x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hφ.continuous
  have hcs1 : HasCompactSupport fun x => ((pd φ i x : ℝ) : ℂ) :=
    (hasCompactSupport_pd hφ.compact i).comp_left Complex.ofReal_zero
  have hcs2 : HasCompactSupport fun x => ((φ x : ℝ) : ℂ) :=
    hφ.compact.comp_left Complex.ofReal_zero
  -- integrability of the four pieces
  have i1 : Integrable fun x => ((pd φ i x : ℝ) : ℂ) * v₂ x :=
    (hcpd.mul h₂.continuous).integrable_of_hasCompactSupport hcs1.mul_right
  have i2 : Integrable fun x => ((φ x : ℝ) : ℂ) * pd v₂ i x :=
    (hcφ.mul (continuous_pd h₂ i)).integrable_of_hasCompactSupport hcs2.mul_right
  -- whole-space integration by parts for v₂
  have hw2 := hasWeakPartial_of_contDiff univ h₂ i φ hφ
  have i3 : Integrable fun x => ((pd φ i x : ℝ) : ℂ) * v₁ x :=
    (hcpd.mul h₁.continuous).integrable_of_hasCompactSupport hcs1.mul_right
  have i4 : Integrable fun x => ((φ x : ℝ) : ℂ) * pd v₁ i x :=
    (hcφ.mul (continuous_pd h₁ i)).integrable_of_hasCompactSupport hcs2.mul_right
  have eL : ∫ x, ((pd φ i x : ℝ) : ℂ) * (euclBall c r).piecewise v₁ v₂ x =
      (∫ x in euclBall c r, ((pd φ i x : ℝ) : ℂ) * v₁ x) +
        ∫ x in (euclBall c r)ᶜ, ((pd φ i x : ℝ) : ℂ) * v₂ x := by
    have : (fun x => ((pd φ i x : ℝ) : ℂ) * (euclBall c r).piecewise v₁ v₂ x) =
        (euclBall c r).piecewise (fun x => ((pd φ i x : ℝ) : ℂ) * v₁ x)
          (fun x => ((pd φ i x : ℝ) : ℂ) * v₂ x) := by
      funext x; by_cases hx : x ∈ euclBall c r <;> simp [piecewise, hx]
    rw [this, integral_piecewise hB i3.integrableOn i1.integrableOn]
  have eR : ∫ x, ((φ x : ℝ) : ℂ) * (euclBall c r).piecewise (pd v₁ i) (pd v₂ i) x =
      (∫ x in euclBall c r, ((φ x : ℝ) : ℂ) * pd v₁ i x) +
        ∫ x in (euclBall c r)ᶜ, ((φ x : ℝ) : ℂ) * pd v₂ i x := by
    have : (fun x => ((φ x : ℝ) : ℂ) * (euclBall c r).piecewise (pd v₁ i) (pd v₂ i) x) =
        (euclBall c r).piecewise (fun x => ((φ x : ℝ) : ℂ) * pd v₁ i x)
          (fun x => ((φ x : ℝ) : ℂ) * pd v₂ i x) := by
      funext x; by_cases hx : x ∈ euclBall c r <;> simp [piecewise, hx]
    rw [this, integral_piecewise hB i4.integrableOn i2.integrableOn]
  have c1 := integral_add_compl hB i1
  have c2 := integral_add_compl hB i2
  have b1 := integral_ofReal_pd_mul_ball c hr hφ1 h₁ i
  have b2 := integral_ofReal_pd_mul_ball c hr hφ1 h₂ i
  have hbd : ∫ w, ((φ (c + r • w) : ℝ) : ℂ) * v₁ (c + r • w) * ((w i : ℝ) : ℂ) ∂(sphereMeasure n) =
      ∫ w, ((φ (c + r • w) : ℝ) : ℂ) * v₂ (c + r • w) * ((w i : ℝ) : ℂ) ∂(sphereMeasure n) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_sphereMeasure n] with w hw
    rw [hS _ (sqDist_add_smul c w r hw)]
  rw [eL, eR]
  rw [hbd] at b1
  have hw2' : ∫ x, ((pd φ i x : ℝ) : ℂ) * v₂ x = -∫ x, ((φ x : ℝ) : ℂ) * pd v₂ i x := hw2
  linear_combination b1 - b2 + c1 + c2 + hw2'


/-! ### The radial reflection across the sphere -/

/-- The radial factor `λ(x) = 2r/|x - c| - 1` of the reflection across `∂B_r(c)`. -/
def reflScale (c : Fin n → ℝ) (r : ℝ) (x : Fin n → ℝ) : ℝ := 2 * r / Real.sqrt (sqDist c x) - 1

/-- The radial reflection `Φ(x) = c + λ(x)(x - c)` across `∂B_r(c)`: `|Φ(x) - c| = 2r - |x - c|`
on rays, fixing the sphere. -/
def reflBall (c : Fin n → ℝ) (r : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  c + reflScale c r x • (x - c)

/-- The extension cutoff `θ(t) = s(4t - 1) s(9 - 4t)`: `1` on `[1/2, 2]`, `0` off `(1/4, 9/4)`. -/
def extCut (t : ℝ) : ℝ := Real.smoothTransition (4 * t - 1) * Real.smoothTransition (9 - 4 * t)

theorem contDiff_extCut {k : ℕ∞} : ContDiff ℝ k extCut := by
  unfold extCut
  have h1 : ContDiff ℝ k Real.smoothTransition := Real.smoothTransition.contDiff
  exact (h1.comp (by fun_prop)).mul (h1.comp (by fun_prop))

theorem extCut_eq_one {t : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 2) : extCut t = 1 := by
  unfold extCut
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem extCut_eq_zero_of_le {t : ℝ} (h : t ≤ 1 / 4) : extCut t = 0 := by
  unfold extCut
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem extCut_eq_zero_of_ge {t : ℝ} (h : 9 / 4 ≤ t) : extCut t = 0 := by
  unfold extCut
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 9 - 4 * t ≤ 0), mul_zero]

theorem extCut_nonneg (t : ℝ) : 0 ≤ extCut t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem extCut_le_one (t : ℝ) : extCut t ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem deriv_extCut_eq_zero_of_ge {t : ℝ} (h : 9 / 4 ≤ t) : deriv extCut t = 0 := by
  have hd : HasDerivAt extCut (deriv Real.smoothTransition (4 * t - 1) * 4 *
      Real.smoothTransition (9 - 4 * t) + Real.smoothTransition (4 * t - 1) *
        (deriv Real.smoothTransition (9 - 4 * t) * (-4))) t := by
    have hs := fun y => ((Real.smoothTransition.contDiff (n := 1)).differentiable
      (by norm_num) y).hasDerivAt
    have h1 : HasDerivAt (fun t : ℝ => 4 * t - 1) 4 t := by
      simpa using ((hasDerivAt_id t).const_mul 4).sub_const 1
    have h2 : HasDerivAt (fun t : ℝ => 9 - 4 * t) (-4) t := by
      simpa using ((hasDerivAt_id t).const_mul 4).const_sub 9
    exact ((hs _).comp t h1).mul ((hs _).comp t h2)
  rw [hd.deriv, Real.smoothTransition.zero_of_nonpos (by linarith : 9 - 4 * t ≤ 0),
    deriv_smoothTransition_eq_zero (Or.inl (by linarith : 9 - 4 * t ≤ 0))]
  ring

theorem exists_bound_deriv_extCut : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |deriv extCut t| ≤ M := by
  have hc : Continuous (deriv extCut) := (contDiff_extCut (k := 1)).continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 3)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 3
  · exact (hM t ht).trans (le_max_left _ _)
  · have : deriv extCut t = 0 := by
      rcases not_and_or.mp ht with h | h
      · have hlt : t < 0 := not_le.mp h
        have : extCut =ᶠ[𝓝 t] fun _ => 0 := by
          filter_upwards [Iio_mem_nhds (by linarith : t < 1 / 4)] with y hy
          exact extCut_eq_zero_of_le (le_of_lt hy)
        simp [this.deriv_eq]
      · exact deriv_extCut_eq_zero_of_ge (by linarith [not_le.mp h])
    rw [this, abs_zero]; exact le_max_right _ _

theorem sqrt_sqDist_add_smul (c w : Fin n → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hw : ∑ i, w i ^ 2 = 1) :
    Real.sqrt (sqDist c (c + ρ • w)) = ρ := by
  rw [sqDist_add_smul c w ρ hw, Real.sqrt_sq hρ]

/-- On rays, `Φ(c + ρω) = c + (2r - ρ) ω`. -/
theorem reflBall_ray (c w : Fin n → ℝ) {r ρ : ℝ} (hρ : 0 < ρ) (hw : ∑ i, w i ^ 2 = 1) :
    reflBall c r (c + ρ • w) = c + (2 * r - ρ) • w := by
  unfold reflBall reflScale
  rw [sqrt_sqDist_add_smul c w hρ.le hw, add_sub_cancel_left, smul_smul]
  congr 2
  field_simp

/-- `Φ` fixes the sphere. -/
theorem reflBall_eq_self {c x : Fin n → ℝ} {r : ℝ} (hr : 0 < r) (hx : sqDist c x = r ^ 2) :
    reflBall c r x = x := by
  unfold reflBall reflScale
  rw [hx, Real.sqrt_sq hr.le, mul_div_assoc, div_self hr.ne', mul_one]
  norm_num

theorem contDiffAt_reflScale {c x : Fin n → ℝ} (r : ℝ) (hx : 0 < sqDist c x)
    {k : WithTop ℕ∞} : ContDiffAt ℝ k (reflScale c r) x := by
  unfold reflScale
  have hs : ContDiffAt ℝ k (fun y => Real.sqrt (sqDist c y)) x :=
    (contDiff_sqDist c).contDiffAt.sqrt hx.ne'
  exact (contDiffAt_const.div hs (Real.sqrt_pos.mpr hx).ne').sub contDiffAt_const

theorem contDiffAt_reflBall {c x : Fin n → ℝ} (r : ℝ) (hx : 0 < sqDist c x)
    {k : WithTop ℕ∞} : ContDiffAt ℝ k (reflBall c r) x := by
  unfold reflBall
  exact contDiffAt_const.add ((contDiffAt_reflScale r hx).smul (contDiffAt_id.sub contDiffAt_const))

/-- The outer piece of the extension: `θ(|x - c|²/r²) u(Φ(x))`. -/
def extOut (c : Fin n → ℝ) (r : ℝ) (u : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  ((extCut (sqDist c x / r ^ 2) : ℝ) : ℂ) * u (reflBall c r x)

theorem contDiff_extOut (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {u : (Fin n → ℝ) → ℂ}
    (hu : ContDiff ℝ 1 u) : ContDiff ℝ 1 (extOut c r u) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : sqDist c x / r ^ 2 < 1 / 4
  · have : extOut c r u =ᶠ[𝓝 x] fun _ => 0 := by
      have hopen : IsOpen {y : Fin n → ℝ | sqDist c y / r ^ 2 < 1 / 4} :=
        isOpen_lt ((continuous_sqDist c).div_const _) continuous_const
      filter_upwards [hopen.mem_nhds hx] with y hy
      simp only [extOut, extCut_eq_zero_of_le (le_of_lt hy), Complex.ofReal_zero, zero_mul]
    exact (contDiffAt_const).congr_of_eventuallyEq this
  · have hpos : 0 < sqDist c x := by
      have : 1 / 4 ≤ sqDist c x / r ^ 2 := not_lt.mp hx
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < r ^ 2)).mp this
      nlinarith [sq_nonneg r, hr]
    unfold extOut
    have h1 : ContDiffAt ℝ 1 (fun y => ((extCut (sqDist c y / r ^ 2) : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x
        ((contDiff_extCut.comp ((contDiff_sqDist c).div_const _)).contDiffAt)
    have h2 : ContDiffAt ℝ 1 (fun y => u (reflBall c r y)) x :=
      hu.contDiffAt.comp x (contDiffAt_reflBall r hpos)
    exact h1.mul h2

theorem extOut_eq_on_sphere {c x : Fin n → ℝ} {r : ℝ} (hr : 0 < r) (u : (Fin n → ℝ) → ℂ)
    (hx : sqDist c x = r ^ 2) : u x = extOut c r u x := by
  unfold extOut
  rw [reflBall_eq_self hr hx, hx, div_self (by positivity), extCut_eq_one (by norm_num) (by norm_num)]
  simp

theorem extOut_eq_zero {c x : Fin n → ℝ} {r : ℝ} (hr : 0 < r) (u : (Fin n → ℝ) → ℂ)
    (hx : 9 / 4 * r ^ 2 ≤ sqDist c x) : extOut c r u x = 0 := by
  unfold extOut
  rw [extCut_eq_zero_of_ge ((le_div_iff₀ (by positivity)).mpr hx)]
  simp

/-- **The reflection extension** of `u` across `∂B_r(c)`: `u` in the ball,
`θ(|x - c|²/r²) u(Φ(x))` outside. -/
def ballExt (c : Fin n → ℝ) (r : ℝ) (u : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  (euclBall c r).piecewise u (extOut c r u)

/-- Its weak gradient. -/
def ballExtGrad (c : Fin n → ℝ) (r : ℝ) (u : (Fin n → ℝ) → ℂ) (i : Fin n) :
    (Fin n → ℝ) → ℂ :=
  (euclBall c r).piecewise (pd u i) (pd (extOut c r u) i)

theorem hasWeakPartial_ballExt (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {u : (Fin n → ℝ) → ℂ}
    (hu : ContDiff ℝ 1 u) (i : Fin n) :
    HasWeakPartial univ i (ballExt c r u) (ballExtGrad c r u i) :=
  hasWeakPartial_glue c hr hu (contDiff_extOut c hr hu) (fun _ hy => extOut_eq_on_sphere hr u hy) i

end RenewalGeometry.BallAnalysis
