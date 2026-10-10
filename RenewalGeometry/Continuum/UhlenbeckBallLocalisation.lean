/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.UhlenbeckGaugeTheorem

/-!
# Localising Uhlenbeck's theorem from a ball to a torus: cutting off in the given gauge fails

`prop:critical-uhlenbeck` of the Einstein–Standard-Model action-closure manuscript uses the local
Coulomb theorem of Uhlenbeck (CMP 83 (1982), Thm 1.3) on smaller concentric balls
(`UhlenbeckGauge.UhlenbeckSmallEnergyGaugeIn`).  A tempting route to it from a periodic
(torus) version is to cut the connection off, `χ A`, with a cutoff `χ` equal to `1` on the
inner ball and supported in the outer ball, and to apply the torus theorem to `χ A`.  Its
curvature is `F_{χA} = χ F_A + dχ ∧ A + (χ² - χ) A ∧ A`, which involves `A` itself on the collar
`{0 < χ < 1}`, in the gauge in which `A` is given.  This file shows that this energy is **not**
controlled by the energy of `A`:

* `pureConn s` — the constant abelian connection `A_s = i s dx₁` (flat; on `ℝ⁴` it is the pure
  gauge `e^{-isx₁}·0`); `curvEnergy_pureConn`: `∫_T |F_{A_s}|² = 0` for every set `T`.
* `cutoffConn χ A = χ A` and `curvEnergy_cutoffConn_pureConn`:
  `∫_S |F_{χ A_s}|² = s² ∫_S |F_{χ A_1}|²`.
* `cutoff_energy_not_controlled`: for every `C¹` function `χ` whose derivative `∂₀χ` does not
  vanish at some point of an open set `S` (every cutoff that is not constant in `x₀` on `S`),
  and every bound `M`, some flat smooth unitary connection `A_s` (zero energy on every set) has
  `∫_S |F_{χ A_s}|² ≥ M`.

So the cutoff energy is bounded by the energy of `A` only after `A` has been put into a gauge
controlling `‖A‖_{L²∩L⁴}` on the collar by `‖F_A‖_{L²}` — which is the conclusion of the theorem
being localised.  (No gauge fixed without solving an elliptic problem does this at the critical
exponent: the radial gauge `A(x) = ∫₀¹ t x^ν F_{νμ}(tx) dt` is not bounded in `L²` of an annulus by
`‖F‖_{L²}`.)  Together with `UhlenbeckObstruction.not_coulomb_apriori_without_mean_zero` (the
torus a-priori estimate needs mean-zero / reflection-symmetric forms), this shows that the
localisation step needs a genuine boundary-value theory (Uhlenbeck's Neumann problem on the
ball, or on a cube with its edge singularities), not a cutoff.
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.UhlenbeckBallLocalisation

open SobolevOpen CriticalGauge

set_option linter.unusedSectionVars false

/-- The constant abelian connection `A_s = i s dx₁` (a `1 × 1` skew-Hermitian matrix). -/
def pureConn (s : ℝ) : MConn 1 := fun μ _ => Matrix.of fun _ _ =>
  if μ = 1 then Complex.I * s else 0

/-- The connection cut off in its given gauge: `(χ A)_μ(y) = χ(y) A_μ(y)`. -/
def cutoffConn {m : ℕ} (χ : (Fin 4 → ℝ) → ℝ) (A : MConn m) : MConn m :=
  fun μ y => (χ y : ℂ) • A μ y

theorem isSmoothUnitaryConn_pureConn (s : ℝ) : IsSmoothUnitaryConn (pureConn s) := by
  refine ⟨fun μ c e => ?_, fun μ y => ?_⟩
  · simp only [pureConn, Matrix.of_apply]
    exact contDiff_const
  · ext c e
    by_cases hμ : μ = 1
    · simp [pureConn, hμ, Matrix.star_apply, Complex.conj_ofReal]
    · simp [pureConn, hμ, Matrix.star_apply]

theorem curvVec_pureConn (s : ℝ) (x : Fin 4 → ℝ) : curvVec (pureConn s) x = 0 := by
  ext p
  simp only [curvVec, curvatureW, entries, entryGrad, pureConn, Matrix.of_apply,
    Fin.sum_univ_one, PiLp.toLp_apply, PiLp.zero_apply]
  have h0 : ∀ ν μ, pd (fun _ : Fin 4 → ℝ => if ν = (1 : Fin 4) then Complex.I * s else 0) μ x =
      0 := fun ν μ => by simp [pd]
  rw [h0, h0]
  ring

/-- **The constant connections `A_s` are flat**: zero curvature energy on every set. -/
theorem curvEnergy_pureConn (s : ℝ) (T : Set (Fin 4 → ℝ)) : curvEnergy (pureConn s) T = 0 := by
  simp [curvEnergy, curvVec_pureConn]

theorem entries_cutoff_pureConn (χ : (Fin 4 → ℝ) → ℝ) (s : ℝ) (ν : Fin 4) (c e : Fin 1)
    (y : Fin 4 → ℝ) :
    entries (cutoffConn χ (pureConn s)) ν c e y =
      (s : ℂ) * entries (cutoffConn χ (pureConn 1)) ν c e y := by
  simp only [entries, cutoffConn, pureConn, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

theorem entryGrad_cutoff_pureConn {χ : (Fin 4 → ℝ) → ℝ} (hχ : Differentiable ℝ χ) (s : ℝ)
    (ν : Fin 4) (c e : Fin 1) (μ : Fin 4) (y : Fin 4 → ℝ) :
    entryGrad (cutoffConn χ (pureConn s)) ν c e μ y =
      (s : ℂ) * entryGrad (cutoffConn χ (pureConn 1)) ν c e μ y := by
  have e1 : (fun y => cutoffConn χ (pureConn s) ν y c e) =
      fun y => (s : ℂ) * cutoffConn χ (pureConn 1) ν y c e := by
    funext y; exact entries_cutoff_pureConn χ s ν c e y
  have hd : DifferentiableAt ℝ (fun y => cutoffConn χ (pureConn 1) ν y c e) y := by
    simp only [cutoffConn, pureConn, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact ((Complex.ofRealCLM.differentiable.comp hχ) y).mul_const _
  simp only [entryGrad, pd]
  rw [e1, fderiv_const_mul hd]
  rfl

/-- **Scaling of the cut-off curvature**: `F_{χ A_s} = s F_{χ A_1}` (abelian). -/
theorem curvVec_cutoff_pureConn {χ : (Fin 4 → ℝ) → ℝ} (hχ : Differentiable ℝ χ) (s : ℝ)
    (x : Fin 4 → ℝ) :
    curvVec (cutoffConn χ (pureConn s)) x = (s : ℂ) • curvVec (cutoffConn χ (pureConn 1)) x := by
  ext ⟨μ, ν, c, e⟩
  have hc : c = 0 := Subsingleton.elim _ _
  have he : e = 0 := Subsingleton.elim _ _
  subst hc he
  simp only [curvVec, curvatureW, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul,
    entryGrad_cutoff_pureConn hχ s, entries_cutoff_pureConn χ s, Fin.sum_univ_one]
  ring

/-- `∫_S |F_{χ A_s}|² = s² ∫_S |F_{χ A_1}|²`. -/
theorem curvEnergy_cutoffConn_pureConn {χ : (Fin 4 → ℝ) → ℝ} (hχ : Differentiable ℝ χ) (s : ℝ)
    (S : Set (Fin 4 → ℝ)) :
    curvEnergy (cutoffConn χ (pureConn s)) S =
      ‖(s : ℂ)‖ₑ ^ 2 * curvEnergy (cutoffConn χ (pureConn 1)) S := by
  unfold curvEnergy
  simp only [curvVec_cutoff_pureConn hχ s, enorm_smul, mul_pow]
  exact lintegral_const_mul' _ _ (by simp)

/-- The `(0,1)` curvature entry of `χ A_1` is `i ∂₀χ`. -/
theorem curvVec_cutoff_one_apply {χ : (Fin 4 → ℝ) → ℝ} (hχ : Differentiable ℝ χ)
    (x : Fin 4 → ℝ) :
    curvVec (cutoffConn χ (pureConn 1)) x (0, 1, 0, 0) = Complex.I * ((pd χ 0 x : ℝ) : ℂ) := by
  have hA0 : (fun y => cutoffConn χ (pureConn 1) 0 y 0 0) = fun _ => 0 := by
    funext y; simp [cutoffConn, pureConn]
  have hA1 : (fun y => cutoffConn χ (pureConn 1) 1 y 0 0) =
      fun y => Complex.I * (Complex.ofRealCLM (χ y)) := by
    funext y; simp [cutoffConn, pureConn]; ring
  have hder : HasFDerivAt (fun y => Complex.I * (Complex.ofRealCLM (χ y)))
      (Complex.I • (Complex.ofRealCLM.comp (fderiv ℝ χ x))) x :=
    ((Complex.ofRealCLM.hasFDerivAt.comp x (hχ x).hasFDerivAt)).const_mul Complex.I
  simp only [curvVec, curvatureW, PiLp.toLp_apply, entryGrad, entries, Fin.sum_univ_one]
  rw [hA0, hA1]
  simp only [pd, hder.fderiv]
  simp [cutoffConn, pureConn]

/-- If `∂₀χ` is continuous and nonzero at a point of an open set `S`, then the cut-off connection
`χ A_1` has positive curvature energy on `S`. -/
theorem curvEnergy_cutoff_one_ne_zero {χ : (Fin 4 → ℝ) → ℝ} (hχ : ContDiff ℝ 1 χ)
    {S : Set (Fin 4 → ℝ)} (hS : IsOpen S) {x₀ : Fin 4 → ℝ} (hx₀ : x₀ ∈ S)
    (h0 : pd χ 0 x₀ ≠ 0) : curvEnergy (cutoffConn χ (pureConn 1)) S ≠ 0 := by
  have hd : Differentiable ℝ χ := hχ.differentiable one_ne_zero
  have hcont : Continuous fun x => pd χ 0 x :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  set c : ℝ := |pd χ 0 x₀| / 2
  have hc : 0 < c := by positivity
  set U : Set (Fin 4 → ℝ) := S ∩ {x | c < |pd χ 0 x|}
  have hUo : IsOpen U := hS.inter (isOpen_lt continuous_const (continuous_abs.comp hcont))
  have hUx : x₀ ∈ U := ⟨hx₀, by show c < |pd χ 0 x₀|; simp only [c]; linarith [abs_pos.2 h0]⟩
  have hUpos : 0 < volume U := hUo.measure_pos volume ⟨x₀, hUx⟩
  have hlow : ∀ x ∈ U, ENNReal.ofReal c ^ 2 ≤ ‖curvVec (cutoffConn χ (pureConn 1)) x‖ₑ ^ 2 := by
    intro x hx
    refine pow_le_pow_left₀ zero_le ?_ 2
    refine le_trans ?_ (PiLp.enorm_apply_le _ (0, 1, 0, 0))
    rw [curvVec_cutoff_one_apply hd x, ← ofReal_norm, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal hx.2.le
  intro hE
  have h1 : ∫⁻ x in U, ENNReal.ofReal c ^ 2 ≤ curvEnergy (cutoffConn χ (pureConn 1)) S := by
    calc ∫⁻ x in U, ENNReal.ofReal c ^ 2
        ≤ ∫⁻ x in U, ‖curvVec (cutoffConn χ (pureConn 1)) x‖ₑ ^ 2 :=
          setLIntegral_mono' hUo.measurableSet hlow
      _ ≤ curvEnergy (cutoffConn χ (pureConn 1)) S :=
          lintegral_mono_set (inter_subset_left)
  rw [hE, setLIntegral_const] at h1
  have : ENNReal.ofReal c ^ 2 * volume U ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (ENNReal.ofReal_pos.2 hc).ne') hUpos.ne'
  exact this (le_antisymm h1 zero_le)

/-- **Cutting a connection off in its given gauge does not control the energy.**  For every
`C¹` function `χ` with `∂₀χ(x₀) ≠ 0` at a point of an open set `S` (in particular every cutoff
that is not constant in `x₀` on `S`) and every `M`, there is a flat smooth unitary connection
`A_s` — zero curvature energy on every set — whose cut-off `χ A_s` has
`∫_S |F_{χ A_s}|² ≥ M`. -/
theorem cutoff_energy_not_controlled {χ : (Fin 4 → ℝ) → ℝ} (hχ : ContDiff ℝ 1 χ)
    {S : Set (Fin 4 → ℝ)} (hS : IsOpen S) {x₀ : Fin 4 → ℝ} (hx₀ : x₀ ∈ S)
    (h0 : pd χ 0 x₀ ≠ 0) (M : ℝ≥0) :
    ∃ s : ℝ, IsSmoothUnitaryConn (pureConn s) ∧ (∀ T, curvEnergy (pureConn s) T = 0) ∧
      (M : ℝ≥0∞) ≤ curvEnergy (cutoffConn χ (pureConn s)) S := by
  have hd : Differentiable ℝ χ := hχ.differentiable one_ne_zero
  set E := curvEnergy (cutoffConn χ (pureConn 1)) S
  have hE : E ≠ 0 := curvEnergy_cutoff_one_ne_zero hχ hS hx₀ h0
  obtain ⟨q, hq0, hqE⟩ : ∃ q : ℝ≥0, 0 < q ∧ (q : ℝ≥0∞) ≤ E := by
    obtain ⟨q, hq0, hqE⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hE)
    exact ⟨q, by exact_mod_cast hq0, hqE.le⟩
  set s : ℝ := Real.sqrt ((M : ℝ) / q)
  refine ⟨s, isSmoothUnitaryConn_pureConn s, curvEnergy_pureConn s, ?_⟩
  rw [curvEnergy_cutoffConn_pureConn hd]
  have hs2 : ‖(s : ℂ)‖ₑ ^ 2 = ENNReal.ofReal ((M : ℝ) / q) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
  rw [hs2]
  calc (M : ℝ≥0∞) = ENNReal.ofReal ((M : ℝ) / q) * q := by
        rw [← ENNReal.ofReal_coe_nnreal (p := q), ← ENNReal.ofReal_mul (by positivity),
          div_mul_cancel₀ _ (by exact_mod_cast hq0.ne'), ENNReal.ofReal_coe_nnreal]
    _ ≤ ENNReal.ofReal ((M : ℝ) / q) * E := mul_le_mul_right hqE _

/-- Non-vacuity of `cutoff_energy_not_controlled`: the coordinate function `χ(y) = y₀` has
`∂₀χ = 1`. -/
example (M : ℝ≥0) : ∃ s : ℝ, IsSmoothUnitaryConn (pureConn s) ∧
    (∀ T, curvEnergy (pureConn s) T = 0) ∧
    (M : ℝ≥0∞) ≤ curvEnergy (cutoffConn (fun y => y 0) (pureConn s)) (eBall 0 1) := by
  have hχ : ContDiff ℝ 1 (fun y : Fin 4 → ℝ => y 0) := (contDiff_apply ℝ ℝ 0)
  refine cutoff_energy_not_controlled hχ (isOpen_eBall 0 1) (x₀ := 0) ?_ ?_ M
  · simp [eBall]
  · have : pd (fun y : Fin 4 → ℝ => y 0) 0 0 = 1 := by
      simp only [pd]
      rw [show (fun y : Fin 4 → ℝ => y 0) = ⇑(ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 4 => ℝ) 0) from rfl, ContinuousLinearMap.fderiv]
      simp
    rw [this]; exact one_ne_zero

end RenewalGeometry.UhlenbeckBallLocalisation
