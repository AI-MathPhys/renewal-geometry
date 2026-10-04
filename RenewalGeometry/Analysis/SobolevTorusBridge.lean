/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.SobolevOpenSet
import RenewalGeometry.Analysis.TorusSobolevEmbedding

/-!
# Periodisation of compactly supported `W^{1,2}` functions: the bridge from `ℝ^d` to `𝕋^d`

Generic infrastructure (no renewal notions).  A function `u : ℝ^ι → ℂ` vanishing outside the
closed ball `‖x‖ ≤ R` (sup norm) lives in the open cube `(-(R+1), R+1)^ι` of side
`L = 2(R+1)`; its **periodisation** `periodize R u : 𝕋^ι → ℂ`,
`periodize R u (t) = u(c + L · rep t)` (`c = -(R+1)`, `rep t ∈ (0,1]^ι` the representative),
is a function on the flat torus `𝕋^ι = UnitAddTorus ι` of `TorusSobolevEmbedding.lean`.

* `integral_comp_affine`: `∫ f(c + L y) dy = L^{-d} ∫ f`.
* `integral_periodize`: `∫_{𝕋^ι} F(t, periodize u t) dt = ∫_{(0,1]^ι} F(y, u(c + L y)) dy`.
* `mFourierCoeff_periodize`: `(periodize u)^(n) = L^{-d} ∫ e_n((x - c)/L) u(x) dx`.
* `mFourierCoeff_periodize_weak` (**Fourier rule for weak derivatives**): if `g` is the weak
  `i`-th partial of `u` on `ℝ^ι` and both vanish off the ball, then
  `(periodize g)^(n) = (2π i n_i / L) (periodize u)^(n)`.  Proof: the weak-derivative identity
  tested against the smooth compactly supported function `ψ(x) e_n((x - c)/L)`, where `ψ` is a
  bump equal to `1` on a neighbourhood of the ball.
* `memLp_periodize`, `hasSum_sq_mFourierCoeff_of_memLp`, `integral_sq_periodize` (Parseval):
  `Σ_n |(periodize u)^(n)|² = ‖periodize u‖²_{L²(𝕋^ι)} = L^{-d} ‖u‖²_{L²}`.
* `sobSq_one_periodize` (**the bridge**): for `u ∈ W^{1,2}(ℝ^ι)` with `u`, `∂u` vanishing off
  the ball, `periodize u ∈ H¹(𝕋^ι)` and
  `‖periodize u‖²_{H¹(𝕋^ι)} = L^{-d} (‖u‖²_{L²} + L² Σ_i ‖∂_i u‖²_{L²})`.
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped ENNReal NNReal ContDiff Real

noncomputable section

namespace RenewalGeometry.SobolevOpen

open TorusSobolev

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Affine change of variables -/

theorem finrank_pi_real : Module.finrank ℝ (ι → ℝ) = Fintype.card ι :=
  Module.finrank_fintype_fun_eq_card ℝ

/-- `∫ f(c + L y) dy = L^{-d} ∫ f(x) dx` for `L > 0`. -/
theorem integral_comp_affine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (ι → ℝ) → F) (c : ι → ℝ) {L : ℝ} (hL : 0 < L) :
    ∫ y, f (c + L • y) = ((L ^ Fintype.card ι)⁻¹ : ℝ) • ∫ x, f x := by
  have h1 := Measure.integral_comp_smul (μ := (volume : Measure (ι → ℝ))) (fun z => f (c + z)) L
  rw [h1, integral_add_left_eq_self, finrank_pi_real,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hL.le _))]

/-- The affine map `y ↦ c + L y` pushes Lebesgue measure to `L^{-d}` times Lebesgue measure. -/
theorem measurePreserving_affine (c : ι → ℝ) {L : ℝ} (hL : 0 < L) :
    MeasurePreserving (fun y : ι → ℝ => c + L • y) volume
      (ENNReal.ofReal ((L ^ Fintype.card ι)⁻¹) • volume) := by
  have hs : MeasurePreserving (fun y : ι → ℝ => L • y) volume
      (ENNReal.ofReal ((L ^ Fintype.card ι)⁻¹) • volume) := by
    refine ⟨measurable_const_smul L, ?_⟩
    rw [Measure.map_addHaar_smul volume hL.ne', finrank_pi_real,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hL.le _))]
  exact (measurePreserving_add_left _ c).comp hs

/-- `u ∈ L^p ⟹ u(c + L ·) ∈ L^p`. -/
theorem memLp_comp_affine {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} {u : (ι → ℝ) → F}
    (hu : MemLp u p volume) (c : ι → ℝ) {L : ℝ} (hL : 0 < L) :
    MemLp (fun y => u (c + L • y)) p volume :=
  (hu.smul_measure ENNReal.ofReal_ne_top).comp_measurePreserving (measurePreserving_affine c hL)

/-! ### Characters -/

/-- The character `e_n(y) = exp(-2π i n·y)` on `ℝ^ι`. -/
def charE (n : ι → ℤ) (y : ι → ℝ) : ℂ :=
  Complex.exp (-(2 * π * Complex.I) * ∑ j, (n j : ℂ) * (y j : ℂ))

theorem mFourier_neg_mk (n : ι → ℤ) (y : ι → ℝ) :
    mFourier (-n) (fun i => (y i : UnitAddCircle)) = charE n y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_coe_apply, charE,
    Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  push_cast
  ring

theorem norm_charE (n : ι → ℤ) (y : ι → ℝ) : ‖charE n y‖ = 1 := by
  rw [charE, Complex.norm_exp]
  have : (-(2 * π * Complex.I) * ∑ j, (n j : ℂ) * (y j : ℂ)).re = 0 := by
    rw [show (∑ j, (n j : ℂ) * (y j : ℂ)) = ((∑ j, (n j : ℝ) * y j : ℝ) : ℂ) by push_cast; rfl]
    simp
  rw [this, Real.exp_zero]

/-- The linear form `y ↦ -2π i n·y`. -/
def charLin (n : ι → ℤ) : (ι → ℝ) →L[ℝ] ℂ :=
  ∑ j, (-(2 * π * Complex.I) * (n j : ℂ)) • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj j))

theorem charLin_apply (n : ι → ℤ) (y : ι → ℝ) :
    charLin n y = -(2 * π * Complex.I) * ∑ j, (n j : ℂ) * (y j : ℂ) := by
  simp [charLin, Finset.mul_sum, mul_assoc]

theorem charLin_single (n : ι → ℤ) (i : ι) :
    charLin n (Pi.single i 1) = -(2 * π * Complex.I) * (n i : ℂ) := by
  rw [charLin_apply]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

theorem charE_eq (n : ι → ℤ) : charE n = fun y => Complex.exp (charLin n y) := by
  funext y; rw [charE, charLin_apply]

/-- The shifted and rescaled character `x ↦ e_n((x - c)/L)`. -/
def charS (n : ι → ℤ) (c : ι → ℝ) (L : ℝ) (x : ι → ℝ) : ℂ := charE n (L⁻¹ • (x - c))

theorem hasFDerivAt_charS (n : ι → ℤ) (c : ι → ℝ) (L : ℝ) (x : ι → ℝ) :
    HasFDerivAt (charS n c L)
      (charS n c L x • (charLin n).comp (L⁻¹ • ContinuousLinearMap.id ℝ (ι → ℝ))) x := by
  have ha : HasFDerivAt (fun x : ι → ℝ => L⁻¹ • (x - c))
      (L⁻¹ • ContinuousLinearMap.id ℝ (ι → ℝ)) x :=
    ((hasFDerivAt_id x).sub_const c).const_smul L⁻¹
  have he := ((charLin n).hasFDerivAt.comp x ha).cexp
  have e1 : charS n c L = fun x => Complex.exp ((charLin n ∘ fun x => L⁻¹ • (x - c)) x) := by
    funext y; simp [charS, charE_eq]
  have e2 : charS n c L x = Complex.exp ((charLin n ∘ fun x => L⁻¹ • (x - c)) x) := by
    rw [e1]
  rw [e2, e1]
  exact he

theorem contDiff_charS (n : ι → ℤ) (c : ι → ℝ) (L : ℝ) : ContDiff ℝ ∞ (charS n c L) := by
  have e1 : charS n c L = fun x => Complex.exp (charLin n (L⁻¹ • (x - c))) := by
    funext y; simp [charS, charE_eq]
  rw [e1]
  exact Complex.contDiff_exp.comp ((charLin n).contDiff.comp
    ((contDiff_id.sub contDiff_const).const_smul L⁻¹))

theorem pd_charS (n : ι → ℤ) (c : ι → ℝ) (L : ℝ) (i : ι) (x : ι → ℝ) :
    pd (charS n c L) i x = charS n c L x * (L⁻¹ * (-(2 * π * Complex.I) * (n i : ℂ))) := by
  unfold pd
  rw [(hasFDerivAt_charS n c L x).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, charLin_single, smul_eq_mul, Complex.real_smul]

theorem norm_charS (n : ι → ℤ) (c : ι → ℝ) (L : ℝ) (x : ι → ℝ) : ‖charS n c L x‖ = 1 :=
  norm_charE n _

theorem charS_affine (n : ι → ℤ) (c : ι → ℝ) {L : ℝ} (hL : L ≠ 0) (y : ι → ℝ) :
    charS n c L (c + L • y) = charE n y := by
  simp [charS, smul_smul, inv_mul_cancel₀ hL]

/-! ### The torus as the unit cube -/

/-- The representative `rep t ∈ (0,1]^ι` of a point of `𝕋^ι`. -/
def torusRep (t : UnitAddTorus ι) : ι → ℝ := fun i => ((AddCircle.equivIoc 1 0 (t i) : ℝ))

/-- The unit cube `(0,1]^ι`. -/
def unitCube : Set (ι → ℝ) := {y | ∀ i, y i ∈ Ioc (0 : ℝ) 1}

theorem unitCube_eq : (unitCube : Set (ι → ℝ)) =
    {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} := by
  ext x; simp [unitCube]

theorem measurableSet_unitCube : MeasurableSet (unitCube : Set (ι → ℝ)) := by
  rw [unitCube_eq]; exact MeasurableSet.univ_pi' (fun i => measurableSet_Ioc)

theorem torusRep_mk {y : ι → ℝ} (hy : y ∈ unitCube) :
    torusRep (fun i => (y i : UnitAddCircle)) = y := by
  funext i
  have h : y i ∈ Ioc (0 : ℝ) (0 + 1) := by simpa using hy i
  simp only [torusRep]
  rw [AddCircle.equivIoc_coe_eq h]

/-- `∫_{𝕋^ι} F = ∫_{(0,1]^ι} F(y mod 1) dy` (Mathlib's `UnitAddTorus.integral_preimage`). -/
theorem integral_torus_eq_unitCube {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : UnitAddTorus ι → E) :
    ∫ t, F t = ∫ y in unitCube, F (fun i => (y i : UnitAddCircle)) := by
  rw [unitCube_eq]; exact UnitAddTorus.integral_preimage F 0

theorem lintegral_torus_eq_unitCube (F : UnitAddTorus ι → ℝ≥0∞) :
    ∫⁻ t, F t = ∫⁻ y in unitCube, F (fun i => (y i : UnitAddCircle)) := by
  rw [unitCube_eq]; exact UnitAddTorus.lintegral_preimage F 0

/-- The representative map `𝕋^ι → (0,1]^ι` is measure preserving. -/
theorem measurePreserving_torusRep :
    MeasurePreserving (torusRep (ι := ι)) volume (volume.restrict unitCube) := by
  have hm : MeasurableSet {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} :=
    MeasurableSet.univ_pi' (fun i => measurableSet_Ioc)
  have h := (measurePreserving_subtype_coe hm).comp
    (UnitAddTorus.measurePreserving_equivPiIoc (d := ι) 0)
  rw [unitCube_eq]
  exact h

/-! ### Periodisation -/

/-- Lower corner `c = -(R+1)` of the cube carrying the ball of radius `R`. -/
def cubeCorner (R : ℝ) : ι → ℝ := fun _ => -(R + 1)

/-- Side `L = 2(R+1)` of the cube carrying the ball of radius `R`. -/
def cubeSide (R : ℝ) : ℝ := 2 * (R + 1)

theorem cubeSide_pos {R : ℝ} (hR : 0 ≤ R) : 0 < cubeSide R := by unfold cubeSide; linarith

/-- **Periodisation** of a function supported in the ball of radius `R`:
`periodize R u (t) = u(c + L · rep t)`. -/
def periodize (R : ℝ) (u : (ι → ℝ) → ℂ) (t : UnitAddTorus ι) : ℂ :=
  u (cubeCorner R + cubeSide R • torusRep t)

theorem integral_periodize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ)
    (u : (ι → ℝ) → ℂ) (F : UnitAddTorus ι → ℂ → E) :
    ∫ t, F t (periodize R u t) =
      ∫ y in unitCube, F (fun i => (y i : UnitAddCircle)) (u (cubeCorner R + cubeSide R • y)) := by
  rw [integral_torus_eq_unitCube]
  refine setIntegral_congr_fun measurableSet_unitCube fun y hy => ?_
  simp only [periodize, torusRep_mk hy]

/-- Points `c + L y` with `y` outside the unit cube lie outside the ball of radius `R`. -/
theorem lt_norm_affine_of_notMem {R : ℝ} (hR : 0 ≤ R) {y : ι → ℝ} (hy : y ∉ unitCube) :
    R < ‖cubeCorner R + cubeSide R • y‖ := by
  simp only [unitCube, mem_setOf_eq, not_forall, mem_Ioc, not_and_or, not_lt, not_le] at hy
  obtain ⟨i, hi⟩ := hy
  refine lt_of_lt_of_le ?_ (norm_le_pi_norm (cubeCorner R + cubeSide R • y) i)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cubeCorner, cubeSide, Real.norm_eq_abs]
  rcases hi with hi | hi
  · rw [abs_of_neg (by nlinarith)]; nlinarith
  · rw [abs_of_pos (by nlinarith)]; nlinarith

/-- For `u` vanishing off the ball, torus integrals of the periodisation are rescaled
whole-space integrals. -/
theorem integral_periodize_of_vanish {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 ≤ R) {u : (ι → ℝ) → ℂ} (hu0 : ∀ x, R < ‖x‖ → u x = 0)
    (F : (ι → ℝ) → ℂ → E) (hF0 : ∀ x, F x 0 = 0) :
    ∫ t, F (cubeCorner R + cubeSide R • torusRep t) (periodize R u t) =
      ((cubeSide R ^ Fintype.card ι)⁻¹ : ℝ) • ∫ x, F x (u x) := by
  have e := integral_periodize (E := E) R u
    (fun t z => F (cubeCorner R + cubeSide R • torusRep t) z)
  rw [e]
  have e2 : ∫ y in unitCube, F (cubeCorner R + cubeSide R • torusRep fun i => (y i : UnitAddCircle))
      (u (cubeCorner R + cubeSide R • y)) =
      ∫ y in unitCube, F (cubeCorner R + cubeSide R • y) (u (cubeCorner R + cubeSide R • y)) :=
    setIntegral_congr_fun measurableSet_unitCube fun y hy => by simp only [torusRep_mk hy]
  rw [e2, setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
    rw [hu0 _ (lt_norm_affine_of_notMem hR hy), hF0])]
  exact integral_comp_affine (fun x => F x (u x)) _ (cubeSide_pos hR)


theorem mk_torusRep (t : UnitAddTorus ι) : (fun i => (torusRep t i : UnitAddCircle)) = t := by
  funext i; simp [torusRep]

theorem mFourier_neg_eq_charS (n : ι → ℤ) (R : ℝ) (hR : 0 ≤ R) (t : UnitAddTorus ι) :
    mFourier (-n) t =
      charS n (cubeCorner R) (cubeSide R) (cubeCorner R + cubeSide R • torusRep t) := by
  rw [charS_affine n _ (cubeSide_pos hR).ne', ← mFourier_neg_mk, mk_torusRep]

/-- Fourier coefficients of a periodisation: `(periodize u)^(n) = L^{-d} ∫ e_n((x-c)/L) u(x) dx`. -/
theorem mFourierCoeff_periodize {R : ℝ} (hR : 0 ≤ R) {u : (ι → ℝ) → ℂ}
    (hu0 : ∀ x, R < ‖x‖ → u x = 0) (n : ι → ℤ) :
    mFourierCoeff (periodize R u) n = ((cubeSide R ^ Fintype.card ι)⁻¹ : ℝ) •
      ∫ x, charS n (cubeCorner R) (cubeSide R) x * u x := by
  have e := integral_periodize_of_vanish (E := ℂ) hR hu0
    (fun x z => charS n (cubeCorner R) (cubeSide R) x * z) (fun x => mul_zero _)
  rw [← e]
  unfold mFourierCoeff
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul, mFourier_neg_eq_charS n R hR t]

/-- **Fourier rule for weak derivatives.**  If `g` is the weak `i`-th partial derivative of `u` on
`ℝ^ι` and both vanish off the ball of radius `R`, then the Fourier coefficients of the
periodisations satisfy `(periodize g)^(n) = (2π i n_i / L) (periodize u)^(n)`. -/
theorem mFourierCoeff_periodize_weak {R : ℝ} (hR : 0 ≤ R) {i : ι} {u g : (ι → ℝ) → ℂ}
    (hw : HasWeakPartial univ i u g) (hu : LocallyIntegrable u volume)
    (hg : LocallyIntegrable g volume) (hu0 : ∀ x, R < ‖x‖ → u x = 0)
    (hg0 : ∀ x, R < ‖x‖ → g x = 0) (n : ι → ℤ) :
    mFourierCoeff (periodize R g) n =
      (2 * π * Complex.I * (n i : ℂ) / (cubeSide R : ℂ)) * mFourierCoeff (periodize R u) n := by
  set c := cubeCorner (ι := ι) R
  set L := cubeSide R
  have hL : 0 < L := cubeSide_pos hR
  set β : ContDiffBump (0 : ι → ℝ) := ⟨R + 1 / 2, R + 1, by linarith, by linarith⟩ with hβ
  set ψ : (ι → ℝ) → ℂ := fun x => ((β x : ℝ) : ℂ)
  set Φ : (ι → ℝ) → ℂ := fun x => ψ x * charS n c L x
  have hψs : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp β.contDiff
  have hΦs : ContDiff ℝ ∞ Φ := hψs.mul (contDiff_charS n c L)
  have hΦc : HasCompactSupport Φ :=
    (β.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have key := hw.complex_test (hu.locallyIntegrableOn univ) (hg.locallyIntegrableOn univ) hΦs hΦc
    (subset_univ _)
  set k : ℂ := (L : ℂ)⁻¹ * (-(2 * π * Complex.I) * (n i : ℂ))
  -- near the ball, `Φ = charS`
  have hnear : ∀ x : ι → ℝ, ‖x‖ ≤ R → Φ =ᶠ[𝓝 x] charS n c L := by
    intro x hx
    have hxb : x ∈ Metric.ball (0 : ι → ℝ) β.rIn := by
      rw [Metric.mem_ball, dist_zero_right]; simp only [hβ]; linarith
    filter_upwards [β.eventuallyEq_one_of_mem_ball hxb] with y hy
    simp only [Φ, ψ, hy, Pi.one_apply, Complex.ofReal_one, one_mul]
  have e1 : (fun x => pd Φ i x * u x) = fun x => k * (charS n c L x * u x) := by
    funext x
    by_cases hx : ‖x‖ ≤ R
    · have : pd Φ i x = pd (charS n c L) i x := by
        unfold pd; rw [(hnear x hx).fderiv_eq]
      rw [this, pd_charS]; simp only [k]; push_cast; ring
    · rw [hu0 x (not_le.mp hx)]; ring
  have e2 : (fun x => Φ x * g x) = fun x => charS n c L x * g x := by
    funext x
    by_cases hx : ‖x‖ ≤ R
    · rw [(hnear x hx).self_of_nhds]
    · rw [hg0 x (not_le.mp hx)]; ring
  rw [e1, e2, integral_const_mul] at key
  rw [mFourierCoeff_periodize hR hg0, mFourierCoeff_periodize hR hu0]
  have hk : ∫ x, charS n c L x * g x = -k * ∫ x, charS n c L x * u x := by
    rw [neg_mul, key, neg_neg]
  rw [hk]
  simp only [Complex.real_smul, k]
  field_simp
  ring

/-! ### Parseval for periodisations and the `H¹` bridge -/

/-- Parseval on `𝕋^ι` for an `L²` function (not necessarily an `Lp` class). -/
theorem hasSum_sq_mFourierCoeff_of_memLp {f : UnitAddTorus ι → ℂ} (hf : MemLp f 2 volume) :
    HasSum (fun n => ‖mFourierCoeff f n‖ ^ 2) (∫ t, ‖f t‖ ^ 2) := by
  have h := hasSum_sq_mFourierCoeff (hf.toLp f)
  have e1 : mFourierCoeff ⇑(hf.toLp f) = mFourierCoeff f := by
    funext n
    unfold mFourierCoeff
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with t ht
    rw [ht]
  have e2 : ∫ t, ‖(hf.toLp f) t‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with t ht
    rw [ht]
  rw [e1, e2] at h
  exact h

/-- The periodisation of an `L²(ℝ^ι)` function is in `L²(𝕋^ι)`. -/
theorem memLp_periodize {R : ℝ} (hR : 0 ≤ R) {u : (ι → ℝ) → ℂ} (hu : MemLp u 2 volume) :
    MemLp (periodize R u) 2 volume :=
  ((memLp_comp_affine hu (cubeCorner R) (cubeSide_pos hR)).restrict unitCube).comp_measurePreserving
    measurePreserving_torusRep

theorem integral_sq_periodize {R : ℝ} (hR : 0 ≤ R) {u : (ι → ℝ) → ℂ}
    (hu0 : ∀ x, R < ‖x‖ → u x = 0) :
    ∫ t, ‖periodize R u t‖ ^ 2 = (cubeSide R ^ Fintype.card ι)⁻¹ * ∫ x, ‖u x‖ ^ 2 := by
  have e := integral_periodize_of_vanish (E := ℝ) hR hu0 (fun _ z => ‖z‖ ^ 2) (fun _ => by simp)
  simpa only [smul_eq_mul] using e

/-- **The `H¹` bridge.**  Let `u ∈ W^{1,2}(ℝ^ι)` with weak gradient `g`, all vanishing off the
ball of radius `R`.  Then the periodisation `periodize R u` lies in `H¹(𝕋^ι)` (Fourier norm of
`TorusSobolevEmbedding.lean`) and
`‖periodize R u‖²_{H¹(𝕋^ι)} = L^{-d} (‖u‖²_{L²} + L² Σ_i ‖∂_i u‖²_{L²})`, `L = 2(R+1)`. -/
theorem sobSq_one_periodize {R : ℝ} (hR : 0 ≤ R) {u : (ι → ℝ) → ℂ} {g : ι → (ι → ℝ) → ℂ}
    (hW : MemW12 univ u g) (hu0 : ∀ x, R < ‖x‖ → u x = 0)
    (hg0 : ∀ i x, R < ‖x‖ → g i x = 0) :
    MemH 1 (periodize R u) ∧ sobSq 1 (periodize R u) =
      (cubeSide R ^ Fintype.card ι)⁻¹ *
        ((∫ x, ‖u x‖ ^ 2) + cubeSide R ^ 2 * ∑ i, ∫ x, ‖g i x‖ ^ 2) := by
  set L := cubeSide R
  have hL : 0 < L := cubeSide_pos hR
  have hu2 : MemLp u 2 volume := by simpa using hW.memLp
  have hg2 : ∀ i, MemLp (g i) 2 volume := fun i => by simpa using hW.memLp_grad i
  have hloc : LocallyIntegrable u volume := hu2.locallyIntegrable (by norm_num)
  have hlocg : ∀ i, LocallyIntegrable (g i) volume := fun i =>
    (hg2 i).locallyIntegrable (by norm_num)
  have hA := hasSum_sq_mFourierCoeff_of_memLp (memLp_periodize hR hu2)
  have hB : ∀ i, HasSum (fun n => L ^ 2 * ‖mFourierCoeff (periodize R (g i)) n‖ ^ 2)
      (L ^ 2 * ∫ t, ‖periodize R (g i) t‖ ^ 2) := fun i =>
    (hasSum_sq_mFourierCoeff_of_memLp (memLp_periodize hR (hg2 i))).mul_left _
  have hS := hA.add (hasSum_sum (s := Finset.univ) fun i _ => hB i)
  have hterm : ∀ n : ι → ℤ, sobWeight n ^ (1 : ℝ) * ‖mFourierCoeff (periodize R u) n‖ ^ 2 =
      ‖mFourierCoeff (periodize R u) n‖ ^ 2 +
        ∑ i, L ^ 2 * ‖mFourierCoeff (periodize R (g i)) n‖ ^ 2 := by
    intro n
    have hrule : ∀ i, ‖mFourierCoeff (periodize R (g i)) n‖ ^ 2 =
        (2 * π * (n i : ℝ) / L) ^ 2 * ‖mFourierCoeff (periodize R u) n‖ ^ 2 := by
      intro i
      rw [mFourierCoeff_periodize_weak hR (hW.weak i) hloc (hlocg i) hu0 (hg0 i) n, norm_mul,
        mul_pow]
      congr 1
      have : (2 * π * Complex.I * (n i : ℂ) / (L : ℂ)) =
          (((2 * π * (n i : ℝ) / L : ℝ)) : ℂ) * Complex.I := by push_cast; ring
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp only [hrule, Real.rpow_one, sobWeight]
    have hs : ∑ x, L ^ 2 * ((2 * π * (n x : ℝ) / L) ^ 2 * ‖mFourierCoeff (periodize R u) n‖ ^ 2) =
        (4 * π ^ 2 * ∑ i, (n i : ℝ) ^ 2) * ‖mFourierCoeff (periodize R u) n‖ ^ 2 := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
      ring
    rw [hs]; ring
  have hS' : HasSum (fun n => sobWeight n ^ (1 : ℝ) * ‖mFourierCoeff (periodize R u) n‖ ^ 2)
      ((∫ t, ‖periodize R u t‖ ^ 2) + ∑ i, L ^ 2 * ∫ t, ‖periodize R (g i) t‖ ^ 2) := by
    simpa only [hterm] using hS
  refine ⟨hS'.summable, ?_⟩
  unfold sobSq coeffSobSq
  rw [hS'.tsum_eq, integral_sq_periodize hR hu0]
  simp only [integral_sq_periodize hR (hg0 _)]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end RenewalGeometry.SobolevOpen
