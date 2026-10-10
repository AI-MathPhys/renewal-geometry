/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.UhlenbeckContinuity

/-!
# Two obstructions to a purely periodic proof of Uhlenbeck's small-energy gauge theorem

Generic statements (no renewal notions) recording why the periodic analytic core of
`Analysis/UhlenbeckHodgeEstimate.lean`, `UhlenbeckCoulombApriori.lean`, `UhlenbeckContinuity.lean`
(the critical Coulomb a-priori estimate on the flat torus `𝕋⁴`) cannot by itself be transported to
the small-energy Coulomb gauge theorem on Euclidean balls (`prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript; K. Uhlenbeck, CMP 83 (1982), Thm 1.3).

* **The harmonic part on `𝕋⁴` is not controlled by the curvature.**  `flatForm θ` is an explicit
  `𝔰𝔲(2)`-valued one-form on `𝕋⁴`
  `a = iθ (e^{4πi x₁} E₁₂ + e^{-4πi x₁} E₂₁) dx₀ + 2πi diag(-1, 1) dx₁`
  (the gauge transform of the constant flat connection `iθ σ₁ dx₀` by
  `g = diag(e^{2πi x₁}, e^{-2πi x₁})`): it is smooth, skew-Hermitian, traceless, **flat**
  (`tCurv = 0`), **in Coulomb gauge**, with `‖∇a‖_{L²} = 8πθ > 0`, and its `dx₁` component has
  the nonzero mean `2πi diag(-1, 1)`.  Hence (`not_coulomb_apriori_without_mean_zero`) no estimate
  `‖∇a‖ ≤ C ‖F_a‖` can hold for small Coulomb `H¹` forms on `𝕋⁴` without the mean-zero hypothesis
  of `coulomb_apriori_torus` — and the mean of a Coulomb representative cannot be prescribed by a
  gauge transformation.  So a continuity method run on genuinely periodic connections has no
  closedness estimate; only the reflection-symmetric (Neumann) class of
  `coulomb_apriori_torus_neumann` has vanishing means, and general connections on a cube are not in
  that class (their normal components do not vanish on the faces).

The second obstruction (cutting a connection off in its given gauge) is recorded in
`Continuum/UhlenbeckBallLocalisation.lean`.
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace RenewalGeometry.UhlenbeckObstruction

open SobolevOpen TorusSobolev UhlenbeckTorus

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation "𝕋⁴" => UnitAddTorus (Fin 4)

/-! ### Monomials on the torus -/

section Monomial

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem norm_mFourier_apply (n : d → ℤ) (x : UnitAddTorus d) : ‖mFourier n x‖ = 1 := by
  simp only [mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod, Circle.norm_coe,
    Finset.prod_const_one]

/-- Fourier coefficients of a monomial `z e_n`. -/
theorem mFourierCoeff_monomial (z : ℂ) (n k : d → ℤ) :
    mFourierCoeff (fun x => z * mFourier n x) k = if k = n then z else 0 := by
  have e : (fun x => z * mFourier n x) = ⇑(trigPoly ({n} : Finset (d → ℤ)) fun _ => z) := by
    funext x; simp [trigPoly]
  rw [e, mFourierCoeff_trigPoly]
  simp

/-- `∂_μ (z e_n) = 2πi n_μ z e_n` in the torus (Fourier) sense. -/
theorem isTPartial_monomial (μ : d) (z : ℂ) (n : d → ℤ) :
    IsTPartial μ (fun x => z * mFourier n x) (fun x => sym μ n * (z * mFourier n x)) := by
  intro k
  have e : (fun x => sym μ n * (z * mFourier n x)) = fun x => (sym μ n * z) * mFourier n x := by
    funext x; ring
  rw [e, mFourierCoeff_monomial, mFourierCoeff_monomial]
  split_ifs with h
  · subst h; rfl
  · simp

theorem memLp_monomial (z : ℂ) (n : d → ℤ) (p : ℝ≥0∞) :
    MemLp (fun x => z * mFourier n x) p (volume : Measure (UnitAddTorus d)) :=
  MemLp.of_bound (continuous_const.mul (mFourier n).continuous).aestronglyMeasurable ‖z‖
    (Eventually.of_forall fun x => by rw [norm_mul, norm_mFourier_apply, mul_one])

theorem eLpNorm_monomial (z : ℂ) (n : d → ℤ) :
    eLpNorm (fun x => z * mFourier n x) 2 (volume : Measure (UnitAddTorus d)) = ‖z‖ₑ := by
  rw [eLpNorm_congr_norm_ae (g := fun _ => z) (Eventually.of_forall fun x => by
    rw [norm_mul, norm_mFourier_apply, mul_one]), eLpNorm_const' z (by norm_num) (by norm_num)]
  simp

end Monomial

/-! ### The flat Coulomb connection with nonzero harmonic part -/

/-- The frequency `n₊ = 2 e₁`. -/
def nPlus : Fin 4 → ℤ := fun i => if i = 1 then 2 else 0

/-- Coefficients of `flatForm θ`. -/
def coef (θ : ℝ) (ν : Fin 4) (c e : Fin 2) : ℂ :=
  if ν = 0 then (if c = e then 0 else Complex.I * θ)
  else if ν = 1 then (if c = e then (if c = 0 then -(2 * π * Complex.I) else 2 * π * Complex.I)
    else 0)
  else 0

/-- Frequencies of `flatForm θ`. -/
def freq (ν : Fin 4) (c e : Fin 2) : Fin 4 → ℤ :=
  if ν = 0 ∧ c = 0 ∧ e = 1 then nPlus else if ν = 0 ∧ c = 1 ∧ e = 0 then -nPlus else 0

/-- **The flat Coulomb `𝔰𝔲(2)` connection with nonzero harmonic part**:
`a_0 = iθ [[0, e_{n₊}], [e_{-n₊}, 0]]`, `a_1 = 2πi diag(-1, 1)`, `a_2 = a_3 = 0`. -/
def flatForm (θ : ℝ) : Fin 4 → Fin 2 → Fin 2 → 𝕋⁴ → ℂ :=
  fun ν c e x => coef θ ν c e * mFourier (freq ν c e) x

/-- Its torus partial derivatives `∂_μ a_{ν,ce}`. -/
def flatGrad (θ : ℝ) : Fin 4 → Fin 2 → Fin 2 → Fin 4 → 𝕋⁴ → ℂ :=
  fun ν c e μ x => sym μ (freq ν c e) * flatForm θ ν c e x

theorem flatForm_isH1Form (θ : ℝ) : IsH1Form (flatForm θ) (flatGrad θ) := by
  refine ⟨fun ν c e => memLp_monomial _ _ _, fun ν c e μ => ?_, fun ν c e μ =>
    isTPartial_monomial μ _ _⟩
  have e' : flatGrad θ ν c e μ = fun x => (sym μ (freq ν c e) * coef θ ν c e) *
      mFourier (freq ν c e) x := by
    funext x; simp only [flatGrad, flatForm]; ring
  rw [e']
  exact memLp_monomial _ _ _

theorem flatGrad_coulomb (θ : ℝ) : IsCoulomb (flatGrad θ) := by
  intro c e
  refine Eventually.of_forall fun x => ?_
  fin_cases c <;> fin_cases e <;>
    simp [flatGrad, flatForm, coef, freq, sym, nPlus]

theorem tCurv_flatForm (θ : ℝ) (μ ν : Fin 4) (c e : Fin 2) (x : 𝕋⁴) :
    tCurv (flatForm θ) (flatGrad θ) μ ν c e x = 0 := by
  fin_cases μ <;> fin_cases ν <;> fin_cases c <;> fin_cases e <;>
    simp [tCurv, Fin.sum_univ_two, flatGrad, flatForm, coef, freq, sym, nPlus, mFourier_zero] <;>
    ring

theorem curvNorm_flatForm (θ : ℝ) : curvNorm (flatForm θ) (flatGrad θ) = 0 := by
  have h : ∀ μ ν c e, tCurv (flatForm θ) (flatGrad θ) μ ν c e = fun _ => 0 := fun μ ν c e =>
    funext fun x => tCurv_flatForm θ μ ν c e x
  simp [curvNorm, h]

theorem eLpNorm_flatGrad (θ : ℝ) (ν : Fin 4) (c e : Fin 2) (μ : Fin 4) :
    eLpNorm (flatGrad θ ν c e μ) 2 volume = ‖sym μ (freq ν c e) * coef θ ν c e‖ₑ := by
  have e' : flatGrad θ ν c e μ = fun x => (sym μ (freq ν c e) * coef θ ν c e) *
      mFourier (freq ν c e) x := by
    funext x; simp only [flatGrad, flatForm]; ring
  rw [e', eLpNorm_monomial]

theorem gradNorm_flatGrad {θ : ℝ} (hθ : 0 ≤ θ) :
    gradNorm (flatGrad θ) = ENNReal.ofReal (8 * π * θ) := by
  have h1 : gradNorm (flatGrad θ) = ‖(2 * π * Complex.I * 2) * (Complex.I * θ)‖ₑ +
      ‖(2 * π * Complex.I * (-2)) * (Complex.I * θ)‖ₑ := by
    simp only [gradNorm, eLpNorm_flatGrad]
    simp [Fin.sum_univ_four, Fin.sum_univ_two, coef, freq, sym, nPlus]
  have h2 : ∀ s : ℝ, ‖(2 * π * Complex.I * s) * (Complex.I * θ)‖ₑ =
      ENNReal.ofReal (2 * π * |s| * θ) := by
    intro s
    rw [← ofReal_norm]
    congr 1
    have : (2 * π * Complex.I * s) * (Complex.I * θ) = ((-(2 * π * s * θ) : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg hθ, abs_of_pos Real.pi_pos]
    norm_num
  have h3 := h2 2
  have h4 := h2 (-2)
  push_cast at h3 h4
  rw [h1, h3, h4, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  norm_num
  ring

/-- **The flat Coulomb connection has a nonzero harmonic part**: the mean of `a_{1,11}` is
`-2πi ≠ 0`. -/
theorem flatForm_mean_ne_zero (θ : ℝ) : mFourierCoeff (flatForm θ 1 0 0) 0 ≠ 0 := by
  have e' : flatForm θ 1 0 0 = fun x => -(2 * π * Complex.I) * mFourier (0 : Fin 4 → ℤ) x := by
    funext x; simp [flatForm, coef, freq]
  rw [e', mFourierCoeff_monomial]
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- The matrices `a_ν(x)` are skew-Hermitian (with `θ` real) and traceless: `flatForm θ` is an
`𝔰𝔲(2)`-valued connection. -/
theorem flatForm_su2 (θ : ℝ) (ν : Fin 4) (x : 𝕋⁴) :
    star (Matrix.of fun c e => flatForm θ ν c e x) = -(Matrix.of fun c e => flatForm θ ν c e x) ∧
      Matrix.trace (Matrix.of fun c e => flatForm θ ν c e x) = 0 := by
  constructor
  · ext c e
    fin_cases ν <;> fin_cases c <;> fin_cases e <;>
      simp [Matrix.star_apply, flatForm, coef, freq, mFourier_neg, mFourier_zero]
  · fin_cases ν <;> simp [Matrix.trace, Fin.sum_univ_two, flatForm, coef, freq, mFourier_zero]

/-- **The flat Coulomb counterexample, packaged**: for every `θ > 0`, `flatForm θ` is a smooth
`𝔰𝔲(2)` one-form on `𝕋⁴` with `H¹` entries, in Coulomb gauge, flat, with
`‖∇a‖_{L²} = 8πθ > 0` and a component of nonzero mean. -/
theorem flat_coulomb_counterexample {θ : ℝ} (hθ : 0 < θ) :
    IsH1Form (flatForm θ) (flatGrad θ) ∧ IsCoulomb (flatGrad θ) ∧
      curvNorm (flatForm θ) (flatGrad θ) = 0 ∧
      gradNorm (flatGrad θ) = ENNReal.ofReal (8 * π * θ) ∧ 0 < gradNorm (flatGrad θ) ∧
      mFourierCoeff (flatForm θ 1 0 0) 0 ≠ 0 :=
  ⟨flatForm_isH1Form θ, flatGrad_coulomb θ, curvNorm_flatForm θ, gradNorm_flatGrad hθ.le, by
    rw [gradNorm_flatGrad hθ.le]; exact ENNReal.ofReal_pos.2 (by positivity),
    flatForm_mean_ne_zero θ⟩

/-- **No critical Coulomb a-priori estimate on `𝕋⁴` without the mean-zero hypothesis.**  There
are no `δ > 0` and `C` such that every Coulomb one-form on `𝕋⁴` with `H¹` entries and
`‖∇a‖_{L²} ≤ δ` satisfies `‖∇a‖_{L²} ≤ C ‖F_a‖_{L²}` (already for `m = 2`, `𝔰𝔲(2)`-valued
forms).  Compare `coulomb_apriori_torus` (mean-zero forms) and `coulomb_apriori_torus_neumann`
(reflection-odd normal components). -/
theorem not_coulomb_apriori_without_mean_zero :
    ¬ ∃ δ C : ℝ≥0, 0 < δ ∧ ∀ (a : Fin 4 → Fin 2 → Fin 2 → 𝕋⁴ → ℂ)
      (da : Fin 4 → Fin 2 → Fin 2 → Fin 4 → 𝕋⁴ → ℂ),
      IsH1Form a da → IsCoulomb da → gradNorm da ≤ δ → gradNorm da ≤ C * curvNorm a da := by
  rintro ⟨δ, C, hδ, h⟩
  set θ : ℝ := (δ : ℝ) / (8 * π)
  have hθ : 0 < θ := by positivity
  have hg : gradNorm (flatGrad θ) = δ := by
    rw [gradNorm_flatGrad hθ.le]
    have : 8 * π * θ = (δ : ℝ) := by
      simp only [θ]; field_simp
    rw [this, ENNReal.ofReal_coe_nnreal]
  have := h (flatForm θ) (flatGrad θ) (flatForm_isH1Form θ) (flatGrad_coulomb θ) hg.le
  rw [curvNorm_flatForm, mul_zero, hg] at this
  exact (ne_of_gt (by exact_mod_cast hδ)) (le_antisymm this zero_le)

end RenewalGeometry.UhlenbeckObstruction
