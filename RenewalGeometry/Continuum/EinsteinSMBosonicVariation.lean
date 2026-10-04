/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMVariationJets

/-!
# The bosonic matter densities on jets: Yang–Mills and Higgs
  (`eq:SM-action`; part of `prop:reduced-continuity` and `prop:variation-continuity`,
  Einstein–Standard-Model action-closure manuscript)

The Yang–Mills, Higgs-kinetic and Higgs-potential densities of the library
(`ymDensity`, `higgsKinetic`, `higgsPotential`, times `volFactor`) are written as a function
`bosonPt θ` of the reduced jet (`RJet`): coefficient maps of the coframe (smooth on the
nondegenerate chart) applied bilinearly to the curvature and covariant-gradient slots, plus the
quartic potential.

* `lieMetricL`: the invariant metric on `𝔰(𝔲(3) ⊕ 𝔲(2))` as a continuous bilinear form, split
  into its three parts with the coefficients `g_j^{-2}`;
* `volFactor_eq_abs_det`: `√|det g| = |det e|`;
* `ymCoeff`, `higgsCoeff`: the coefficient maps `e ↦ (F, F') ↦ -¼ g^{μα}g^{νβ}⟨F_{μν},F'_{αβ}⟩ √|g|`
  and `e ↦ (K, K') ↦ -g^{μν} Re⟨K_μ, K'_ν⟩ √|g|`, smooth on the chart;
* `bosonPt`, `bosonDensity_eq_bosonPt`: the factorization of the library density through the
  jet, `contDiffOn_bosonPt`: smoothness on `{R | det R.e ≠ 0}`.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM

open SobolevOpen (pd)

/-! ### Constructing continuous bilinear maps on finite-dimensional spaces -/

section Constructors

variable {V₁ V₂ W : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]
  [NormedAddCommGroup V₂] [NormedSpace ℝ V₂] [FiniteDimensional ℝ V₂] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- A bilinear map on finite-dimensional spaces as a continuous bilinear map. -/
def mkBilinL (f : V₁ → V₂ → W) (h₁ : ∀ x x' y, f (x + x') y = f x y + f x' y)
    (h₂ : ∀ (c : ℝ) x y, f (c • x) y = c • f x y) (h₃ : ∀ x y y', f x (y + y') = f x y + f x y')
    (h₄ : ∀ (c : ℝ) x y, f x (c • y) = c • f x y) : V₁ →L[ℝ] V₂ →L[ℝ] W :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => LinearMap.toContinuousLinearMap
        { toFun := f x, map_add' := h₃ x, map_smul' := fun c y => h₄ c x y }
      map_add' := fun x x' => ContinuousLinearMap.ext fun y => by
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          ContinuousLinearMap.add_apply, h₁]
      map_smul' := fun c x => ContinuousLinearMap.ext fun y => by
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          ContinuousLinearMap.smul_apply, RingHom.id_apply, h₂] }

@[simp] theorem mkBilinL_apply (f : V₁ → V₂ → W) (h₁ h₂ h₃ h₄) (x : V₁) (y : V₂) :
    mkBilinL f h₁ h₂ h₃ h₄ x y = f x y := rfl

/-- A linear map on a finite-dimensional space as a continuous linear map. -/
def mkLinL (f : V₁ → W) (h₁ : ∀ x x', f (x + x') = f x + f x')
    (h₂ : ∀ (c : ℝ) x, f (c • x) = c • f x) : V₁ →L[ℝ] W :=
  LinearMap.toContinuousLinearMap { toFun := f, map_add' := h₁, map_smul' := h₂ }

@[simp] theorem mkLinL_apply (f : V₁ → W) (h₁ h₂) (x : V₁) : mkLinL f h₁ h₂ x = f x := rfl

end Constructors

/-! ### Linearity of the matrix operations -/

section MatrixLinear

theorem block3_add (X Y : LieFibre) : block3 (X + Y) = block3 X + block3 Y := rfl
theorem block3_smul (c : ℝ) (X : LieFibre) : block3 (c • X) = c • block3 X := rfl
theorem block2_add (X Y : LieFibre) : block2 (X + Y) = block2 X + block2 Y := rfl
theorem block2_smul (c : ℝ) (X : LieFibre) : block2 (c • X) = c • block2 X := rfl

theorem mtrace_add {n : ℕ} (X Y : Fin n → Fin n → ℂ) : mtrace (X + Y) = mtrace X + mtrace Y := by
  simp [mtrace, Finset.sum_add_distrib]

theorem mtrace_smul {n : ℕ} (c : ℝ) (X : Fin n → Fin n → ℂ) : mtrace (c • X) = c • mtrace X := by
  simp [mtrace, Finset.smul_sum]

theorem traceless_add {n : ℕ} (X Y : Fin n → Fin n → ℂ) :
    traceless (X + Y) = traceless X + traceless Y := by
  funext i j
  simp only [traceless, Pi.add_apply, mtrace_add]
  split_ifs <;> ring

theorem traceless_smul {n : ℕ} (c : ℝ) (X : Fin n → Fin n → ℂ) :
    traceless (c • X) = c • traceless X := by
  funext i j
  simp only [traceless, Pi.smul_apply, mtrace_smul, Complex.real_smul]
  split_ifs <;> ring

end MatrixLinear

/-! ### The invariant metric as a bilinear form -/

/-- The colour part `-2 Re tr(X₃' Z₃')`. -/
def lieP3 (X Z : LieFibre) : ℝ :=
  -2 * (mtrace (mmul (traceless (block3 X)) (traceless (block3 Z)))).re

/-- The weak part `-2 Re tr(X₂' Z₂')`. -/
def lieP2 (X Z : LieFibre) : ℝ :=
  -2 * (mtrace (mmul (traceless (block2 X)) (traceless (block2 Z)))).re

/-- The hypercharge part `Im tr X₂ · Im tr Z₂`. -/
def lieP1 (X Z : LieFibre) : ℝ := (mtrace (block2 X)).im * (mtrace (block2 Z)).im

theorem lieMetric_eq {Y : Type} (θ : CoefficientBank Y) (X Z : LieFibre) :
    lieMetric θ X Z = (θ.g3 ^ 2)⁻¹ * lieP3 X Z + (θ.g2 ^ 2)⁻¹ * lieP2 X Z +
      (θ.g1 ^ 2)⁻¹ * lieP1 X Z := rfl

/-- `lieP3` as a continuous bilinear form. -/
def lieP3L : LieFibre →L[ℝ] LieFibre →L[ℝ] ℝ :=
  mkBilinL lieP3
    (fun X X' Z => by
      simp only [lieP3, block3_add, traceless_add, mmul_add_left', mtrace_add, Complex.add_re]
      ring)
    (fun c X Z => by
      simp only [lieP3, block3_smul, traceless_smul, mmul_smul_left', mtrace_smul,
        Complex.real_smul, Complex.re_ofReal_mul, smul_eq_mul]
      ring)
    (fun X Z Z' => by
      simp only [lieP3, block3_add, traceless_add, mmul_add_right', mtrace_add, Complex.add_re]
      ring)
    (fun c X Z => by
      simp only [lieP3, block3_smul, traceless_smul, mmul_smul_right', mtrace_smul,
        Complex.real_smul, Complex.re_ofReal_mul, smul_eq_mul]
      ring)

/-- `lieP2` as a continuous bilinear form. -/
def lieP2L : LieFibre →L[ℝ] LieFibre →L[ℝ] ℝ :=
  mkBilinL lieP2
    (fun X X' Z => by
      simp only [lieP2, block2_add, traceless_add, mmul_add_left', mtrace_add, Complex.add_re]
      ring)
    (fun c X Z => by
      simp only [lieP2, block2_smul, traceless_smul, mmul_smul_left', mtrace_smul,
        Complex.real_smul, Complex.re_ofReal_mul, smul_eq_mul]
      ring)
    (fun X Z Z' => by
      simp only [lieP2, block2_add, traceless_add, mmul_add_right', mtrace_add, Complex.add_re]
      ring)
    (fun c X Z => by
      simp only [lieP2, block2_smul, traceless_smul, mmul_smul_right', mtrace_smul,
        Complex.real_smul, Complex.re_ofReal_mul, smul_eq_mul]
      ring)

/-- `lieP1` as a continuous bilinear form. -/
def lieP1L : LieFibre →L[ℝ] LieFibre →L[ℝ] ℝ :=
  mkBilinL lieP1
    (fun X X' Z => by simp only [lieP1, block2_add, mtrace_add, Complex.add_im]; ring)
    (fun c X Z => by
      simp only [lieP1, block2_smul, mtrace_smul, Complex.real_smul, Complex.im_ofReal_mul,
        smul_eq_mul]; ring)
    (fun X Z Z' => by simp only [lieP1, block2_add, mtrace_add, Complex.add_im]; ring)
    (fun c X Z => by
      simp only [lieP1, block2_smul, mtrace_smul, Complex.real_smul, Complex.im_ofReal_mul,
        smul_eq_mul]; ring)

/-- The three bilinear parts of the invariant metric. -/
def liePL : Fin 3 → LieFibre →L[ℝ] LieFibre →L[ℝ] ℝ := ![lieP3L, lieP2L, lieP1L]

/-- The three coupling factors `g₃^{-2}, g₂^{-2}, g₁^{-2}`. -/
def gaugeScalars {Y : Type} (θ : CoefficientBank Y) : Fin 3 → ℝ :=
  ![(θ.g3 ^ 2)⁻¹, (θ.g2 ^ 2)⁻¹, (θ.g1 ^ 2)⁻¹]

theorem lieMetric_eq_sum {Y : Type} (θ : CoefficientBank Y) (X Z : LieFibre) :
    lieMetric θ X Z = ∑ j, gaugeScalars θ j * liePL j X Z := by
  simp [lieMetric_eq, Fin.sum_univ_three, gaugeScalars, liePL, lieP3L, lieP2L, lieP1L]

/-! ### The volume factor -/

theorem volFactor_eq_abs_det (e : CoframeFibre) : volFactor e = |(Matrix.of e).det| := by
  rw [volFactor, det_metricAt, abs_neg, abs_pow, Real.sqrt_sq (abs_nonneg _)]

theorem contDiffAt_volFactor {n : WithTop ℕ∞} {e : CoframeFibre} (he : e ∈ coframeGL) :
    ContDiffAt ℝ n volFactor e := by
  have : volFactor = fun e : CoframeFibre => |(Matrix.of e).det| := funext volFactor_eq_abs_det
  rw [this]
  have h1 : ContDiffAt ℝ n (fun e : CoframeFibre => (Matrix.of e).det) e :=
    (contDiff_det_coframe (n := n)).contDiffAt
  have h2 : ContDiffAt ℝ n (fun t : ℝ => |t|) ((Matrix.of e).det) := by
    rcases lt_or_gt_of_ne he with hneg | hpos
    · refine (contDiffAt_id.neg).congr_of_eventuallyEq ?_
      filter_upwards [gt_mem_nhds hneg] with t ht
      simp [abs_of_neg ht]
    · refine contDiffAt_id.congr_of_eventuallyEq ?_
      filter_upwards [lt_mem_nhds hpos] with t ht
      simp [abs_of_pos ht]
  exact h2.comp e h1

attribute [fun_prop] contDiffAt_volFactor

/-! ### Coefficient maps of the coframe -/

/-- The inverse metric entries as a real function. -/
def gInv (e : CoframeFibre) (μ ν : Fin 4) : ℝ := metricInv e μ ν

theorem contDiffAt_gInv (μ ν : Fin 4) {n : WithTop ℕ∞} {e : CoframeFibre} (he : e ∈ coframeGL) :
    ContDiffAt ℝ n (fun e => gInv e μ ν) e := contDiffAt_metricInv μ ν he

attribute [fun_prop] contDiffAt_gInv

/-- The `(μ, ν)` entry of a two-index family, as a continuous linear map. -/
def proj2 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (μ ν : Fin 4) :
    (Fin 4 → Fin 4 → V) →L[ℝ] V :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => V) ν).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 4 → V) μ)

@[simp] theorem proj2_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (μ ν : Fin 4)
    (F : Fin 4 → Fin 4 → V) : proj2 μ ν F = F μ ν := rfl

/-- `e ↦ (F, F') ↦ -¼ g^{μα}g^{νβ} P_j(F_{μν}, F'_{αβ}) √|g|`, `P_j` the parts of the invariant
metric. -/
def ymCoeff (j : Fin 3) (e : CoframeFibre) :
    (Fin 4 → ConnFibre) →L[ℝ] (Fin 4 → ConnFibre) →L[ℝ] ℝ :=
  (-(1 / 4) * volFactor e) • ∑ μ, ∑ ν, ∑ α, ∑ β, (gInv e μ α * gInv e ν β) •
    (liePL j).bilinearComp (proj2 μ ν) (proj2 α β)

theorem ymCoeff_apply (j : Fin 3) (e : CoframeFibre) (F F' : Fin 4 → ConnFibre) :
    ymCoeff j e F F' = -(1 / 4) * (∑ μ, ∑ ν, ∑ α, ∑ β, metricInv e μ α * metricInv e ν β *
      liePL j (F μ ν) (F' α β)) * volFactor e := by
  simp only [ymCoeff, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.bilinearComp_apply, proj2_apply, smul_eq_mul, gInv]
  ring

/-- Real part of the Higgs Hermitian product as a real bilinear form. -/
def hInnerReL : HiggsFibre →L[ℝ] HiggsFibre →L[ℝ] ℝ :=
  mkBilinL (fun u v => (hInner u v).re)
    (fun u u' v => by simp [hInner, add_mul, Finset.sum_add_distrib])
    (fun c u v => by
      simp [hInner, Finset.mul_sum, Complex.real_smul, star_mul', Complex.conj_ofReal]
      ring)
    (fun u v v' => by simp [hInner, mul_add, Finset.sum_add_distrib])
    (fun c u v => by
      simp [hInner, Finset.mul_sum, Complex.real_smul]
      ring)

/-- `e ↦ (K, K') ↦ -g^{μν} Re⟨K_μ, K'_ν⟩ √|g|`. -/
def higgsCoeff (e : CoframeFibre) :
    (Fin 4 → HiggsFibre) →L[ℝ] (Fin 4 → HiggsFibre) →L[ℝ] ℝ :=
  (-volFactor e) • ∑ μ, ∑ ν, gInv e μ ν •
    hInnerReL.bilinearComp (ContinuousLinearMap.proj μ) (ContinuousLinearMap.proj ν)

theorem higgsCoeff_apply (e : CoframeFibre) (K K' : Fin 4 → HiggsFibre) :
    higgsCoeff e K K' = -(∑ μ, ∑ ν, metricInv e μ ν * hInnerReL (K μ) (K' ν)) * volFactor e := by
  simp only [higgsCoeff, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, gInv]
  ring

/-- The Higgs modulus squared `|H|² = Re⟨H, H⟩`. -/
def higgsQuad (H : HiggsFibre) : ℝ := hInnerReL H H

theorem higgsQuad_eq (H : HiggsFibre) : higgsQuad H = ∑ i, Complex.normSq (H i) := by
  simp only [higgsQuad, hInnerReL, mkBilinL_apply, hInner, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_apply]
  simp [Complex.mul_re]

/-- **The bosonic matter density on jets**:
`Σ_j g_j^{-2} YM_j(e)(F, F) + Higgs(e)(K, K) - λ_H(|H|² - v_H²)² √|g|`. -/
def bosonPt {Y : Type} (θ : CoefficientBank Y) {C : Type} [Fintype C] (R : RJet C) : ℝ :=
  ∑ j, gaugeScalars θ j * ymCoeff j R.e R.F R.F + higgsCoeff R.e R.K R.K -
    θ.lambdaH * (higgsQuad R.H - θ.vH ^ 2) ^ 2 * volFactor R.e

theorem ymDensity_mul_vol {Y : Type} (θ : CoefficientBank Y) (e : E4 → CoframeFibre)
    (A : E4 → ConnFibre) (x : E4) :
    ymDensity θ e A x * volFactor (e x) =
      ∑ j, gaugeScalars θ j * ymCoeff j (e x) (curvatureF A x) (curvatureF A x) := by
  simp only [ymCoeff_apply, ymDensity, lieMetric_eq_sum, Fin.sum_univ_three, Finset.mul_sum,
    Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib]
  congr 1; congr 1
  all_goals exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem higgsKinetic_mul_vol (e : E4 → CoframeFibre) (A : E4 → ConnFibre) (H : E4 → HiggsFibre)
    (x : E4) :
    higgsKinetic e A H x * volFactor (e x) =
      higgsCoeff (e x) (covDerivHiggs A H x) (covDerivHiggs A H x) := by
  simp only [higgsCoeff_apply, higgsKinetic, hInnerReL, mkBilinL_apply]

/-- **Factorization of the library density through the jet**: for every field tuple,
`(YM + Higgs kinetic - V)(z)(x) √|g| = bosonPt θ (redJet z x)`. -/
theorem bosonDensity_eq_bosonPt {Y : Type} (θ : CoefficientBank Y) {C : Type} [Fintype C]
    (z : FieldTuple C) (x : E4) :
    (ymDensity θ z.e z.A x + higgsKinetic z.e z.A z.H x - higgsPotential θ (z.H x)) *
      volFactor (z.e x) = bosonPt θ (redJet z x) := by
  rw [add_sub_assoc, add_mul, sub_mul, ymDensity_mul_vol, higgsKinetic_mul_vol]
  simp only [bosonPt, redJet, RJet.mk_e, RJet.mk_F, RJet.mk_K, RJet.mk_H, higgsPotential,
    higgsQuad_eq]
  ring

/-! ### Smoothness on the nondegenerate chart -/

section Smooth

variable {C : Type} [Fintype C]

theorem contDiffAt_ymCoeff (j : Fin 3) {n : WithTop ℕ∞} {e : CoframeFibre} (he : e ∈ coframeGL) :
    ContDiffAt ℝ n (ymCoeff j) e := by
  have : ContDiffOn ℝ n (ymCoeff j) coframeGL := by
    refine contDiffOn_clm_apply.mpr fun F => contDiffOn_clm_apply.mpr fun F' => ?_
    intro e' he'
    refine ContDiffAt.contDiffWithinAt ?_
    simp only [ymCoeff_apply]
    fun_prop (disch := assumption)
  exact this.contDiffAt (isOpen_coframeGL.mem_nhds he)

theorem contDiffAt_higgsCoeff {n : WithTop ℕ∞} {e : CoframeFibre} (he : e ∈ coframeGL) :
    ContDiffAt ℝ n higgsCoeff e := by
  have : ContDiffOn ℝ n higgsCoeff coframeGL := by
    refine contDiffOn_clm_apply.mpr fun K => contDiffOn_clm_apply.mpr fun K' => ?_
    intro e' he'
    refine ContDiffAt.contDiffWithinAt ?_
    simp only [higgsCoeff_apply]
    fun_prop (disch := assumption)
  exact this.contDiffAt (isOpen_coframeGL.mem_nhds he)


/-- The bosonic jet density is `C¹` (indeed smooth) on the nondegenerate chart. -/
theorem contDiffOn_bosonPt {Y : Type} (θ : CoefficientBank Y) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (bosonPt (C := C) θ) (jetGL C) := by
  intro R hR
  refine ContDiffAt.contDiffWithinAt ?_
  have he : ContDiffAt ℝ n (fun R : RJet C => R.e) R := (πe (C := C)).contDiff.contDiffAt
  have hF : ContDiffAt ℝ n (fun R : RJet C => R.F) R := (πF (C := C)).contDiff.contDiffAt
  have hK : ContDiffAt ℝ n (fun R : RJet C => R.K) R := (πK (C := C)).contDiff.contDiffAt
  have hH : ContDiffAt ℝ n (fun R : RJet C => R.H) R := (πH (C := C)).contDiff.contDiffAt
  have hY : ∀ j, ContDiffAt ℝ n (fun R : RJet C => ymCoeff j R.e) R := fun j =>
    (contDiffAt_ymCoeff j hR).comp R he
  have hHi : ContDiffAt ℝ n (fun R : RJet C => higgsCoeff R.e) R :=
    (contDiffAt_higgsCoeff hR).comp R he
  have hV : ContDiffAt ℝ n (fun R : RJet C => volFactor R.e) R :=
    (contDiffAt_volFactor hR).comp R he
  have hq : ContDiffAt ℝ n (fun R : RJet C => higgsQuad R.H) R :=
    (contDiffAt_const.clm_apply hH).clm_apply hH
  unfold bosonPt
  refine ContDiffAt.sub (ContDiffAt.add (ContDiffAt.sum fun j _ =>
    contDiffAt_const.mul (((hY j).clm_apply hF).clm_apply hF)) ((hHi.clm_apply hK).clm_apply hK))
    ((contDiffAt_const.mul ((hq.sub contDiffAt_const).pow 2)).mul hV)

end Smooth

/-! ### The explicit first variation -/

section Variation

variable {C : Type} [Fintype C]

theorem hasFDerivAt_coeff_bilin {Z V₁ V₂ : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [NormedAddCommGroup V₂] [NormedSpace ℝ V₂]
    {Φ : Z → V₁ →L[ℝ] V₂ →L[ℝ] ℝ} (pz : RJet C →L[ℝ] Z) (p₁ : RJet C →L[ℝ] V₁)
    (p₂ : RJet C →L[ℝ] V₂) {R : RJet C} (hΦ : DifferentiableAt ℝ Φ (pz R)) :
    DifferentiableAt ℝ (fun R => Φ (pz R) (p₁ R) (p₂ R)) R ∧ ∀ dR,
      fderiv ℝ (fun R => Φ (pz R) (p₁ R) (p₂ R)) R dR =
        fderiv ℝ Φ (pz R) (pz dR) (p₁ R) (p₂ R) + Φ (pz R) (p₁ dR) (p₂ R) +
          Φ (pz R) (p₁ R) (p₂ dR) := by
  have h1 : HasFDerivAt (fun R => Φ (pz R)) ((fderiv ℝ Φ (pz R)).comp pz) R :=
    hΦ.hasFDerivAt.comp R pz.hasFDerivAt
  have h3 := (h1.clm_apply p₁.hasFDerivAt).clm_apply p₂.hasFDerivAt
  refine ⟨h3.differentiableAt, fun dR => ?_⟩
  rw [h3.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.flip_apply]
  abel

end Variation

/-! ### The derivative of the bosonic density -/

section Derivative

variable {C : Type} [Fintype C]

/-- The explicit derivative of `bosonPt θ` at `R` in the direction `dR`. -/
def bosonDeriv {Y : Type} (θ : CoefficientBank Y) (R dR : RJet C) : ℝ :=
  (∑ j, gaugeScalars θ j * (fderiv ℝ (ymCoeff j) R.e dR.e R.F R.F + ymCoeff j R.e dR.F R.F +
    ymCoeff j R.e R.F dR.F)) +
  (fderiv ℝ higgsCoeff R.e dR.e R.K R.K + higgsCoeff R.e dR.K R.K + higgsCoeff R.e R.K dR.K) -
  θ.lambdaH * ((2 * (higgsQuad R.H - θ.vH ^ 2) * (hInnerReL dR.H R.H + hInnerReL R.H dR.H)) *
    volFactor R.e + (higgsQuad R.H - θ.vH ^ 2) ^ 2 * fderiv ℝ volFactor R.e dR.e)

theorem hasFDerivAt_bosonPt {Y : Type} (θ : CoefficientBank Y) {R : RJet C} (hR : R ∈ jetGL C) :
    DifferentiableAt ℝ (bosonPt θ) R ∧ ∀ dR, fderiv ℝ (bosonPt θ) R dR = bosonDeriv θ R dR := by
  have hY := fun j => hasFDerivAt_coeff_bilin (C := C) πe πF πF
    ((contDiffAt_ymCoeff j hR (n := 1)).differentiableAt one_ne_zero)
  have hK := hasFDerivAt_coeff_bilin (C := C) πe πK πK
    ((contDiffAt_higgsCoeff hR (n := 1)).differentiableAt one_ne_zero)
  have hq := hasFDerivAt_coeff_bilin (C := C) (Φ := fun _ : CoframeFibre => hInnerReL) (R := R)
    πe πH πH (differentiableAt_const _)
  have hV : DifferentiableAt ℝ (fun R : RJet C => volFactor R.e) R :=
    ((contDiffAt_volFactor hR (n := 1)).differentiableAt one_ne_zero).comp R
      (πe (C := C)).differentiableAt
  have hVd : ∀ dR, fderiv ℝ (fun R : RJet C => volFactor R.e) R dR =
      fderiv ℝ volFactor R.e dR.e := fun dR => by
    have h : HasFDerivAt (fun R : RJet C => volFactor (πe R))
        ((fderiv ℝ volFactor R.e).comp (πe (C := C))) R :=
      ((contDiffAt_volFactor hR (n := 1)).differentiableAt one_ne_zero).hasFDerivAt.comp R
        (πe (C := C)).hasFDerivAt
    rw [show (fun R : RJet C => volFactor R.e) = fun R => volFactor (πe R) from rfl, h.fderiv]
    rfl
  -- assemble
  set q : RJet C → ℝ := fun R => hInnerReL (πH R) (πH R)
  have hqf : HasFDerivAt q (fderiv ℝ q R) R := hq.1.hasFDerivAt
  have hpotf := (((hqf.sub_const (θ.vH ^ 2)).pow 2).const_mul θ.lambdaH).mul hV.hasFDerivAt
  have hYf := fun j => (hY j).1.hasFDerivAt.const_mul (gaugeScalars θ j)
  have hsumf := HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => hYf j
  have hfun : bosonPt (C := C) θ = fun R => (∑ j ∈ Finset.univ, gaugeScalars θ j *
      ymCoeff j (πe R) (πF R) (πF R)) + higgsCoeff (πe R) (πK R) (πK R) -
      θ.lambdaH * (q R - θ.vH ^ 2) ^ 2 * volFactor R.e := rfl
  have htot : HasFDerivAt (fun R => (∑ j ∈ Finset.univ, gaugeScalars θ j *
      ymCoeff j (πe R) (πF R) (πF R)) + higgsCoeff (πe R) (πK R) (πK R) -
      θ.lambdaH * (q R - θ.vH ^ 2) ^ 2 * volFactor R.e) _ R :=
    (hsumf.add hK.1.hasFDerivAt).sub hpotf
  rw [hfun]
  refine ⟨htot.differentiableAt, fun dR => ?_⟩
  rw [htot.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, (hY _).2,
    hK.2, hq.2, hVd, bosonDeriv, q]
  simp only [πe_apply, πF_apply, πK_apply, πH_apply, fderiv_const_apply,
    ContinuousLinearMap.zero_apply, zero_add, Nat.cast_ofNat, pow_one, mul_add, higgsQuad]
  ring

end Derivative

/-! ### Covector-valued multilinear maps -/

section Covectors

variable {C : Type} [Fintype C]
variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]
  [NormedAddCommGroup V₂] [NormedSpace ℝ V₂] [FiniteDimensional ℝ V₂]

/-- A map `V₁ → (RJet → ℝ)`, linear in both arguments, as a continuous linear map into
covectors on test jets. -/
def mkCov1 (f : V₁ → RJet C → ℝ) (h₁ : ∀ y y' T, f (y + y') T = f y T + f y' T)
    (h₂ : ∀ (c : ℝ) y T, f (c • y) T = c * f y T) (h₃ : ∀ y T T', f y (T + T') = f y T + f y T')
    (h₄ : ∀ (c : ℝ) y T, f y (c • T) = c * f y T) : V₁ →L[ℝ] (RJet C →L[ℝ] ℝ) :=
  mkLinL (fun y => mkLinL (f y) (h₃ y) (fun c T => h₄ c y T))
    (fun y y' => ContinuousLinearMap.ext fun T => by simp [h₁])
    (fun c y => ContinuousLinearMap.ext fun T => by simp [h₂])

@[simp] theorem mkCov1_apply (f : V₁ → RJet C → ℝ) (h₁ h₂ h₃ h₄) (y : V₁) (T : RJet C) :
    mkCov1 f h₁ h₂ h₃ h₄ y T = f y T := rfl

/-- A map `V₁ → V₂ → (RJet → ℝ)`, linear in all three arguments, as a continuous bilinear map
into covectors on test jets. -/
def mkCov2 (f : V₁ → V₂ → RJet C → ℝ) (h₁ : ∀ y y' z T, f (y + y') z T = f y z T + f y' z T)
    (h₂ : ∀ (c : ℝ) y z T, f (c • y) z T = c * f y z T)
    (h₃ : ∀ y z z' T, f y (z + z') T = f y z T + f y z' T)
    (h₄ : ∀ (c : ℝ) y z T, f y (c • z) T = c * f y z T)
    (h₅ : ∀ y z T T', f y z (T + T') = f y z T + f y z T')
    (h₆ : ∀ (c : ℝ) y z T, f y z (c • T) = c * f y z T) :
    V₁ →L[ℝ] V₂ →L[ℝ] (RJet C →L[ℝ] ℝ) :=
  mkBilinL (fun y z => mkLinL (f y z) (h₅ y z) (fun c T => h₆ c y z T))
    (fun y y' z => ContinuousLinearMap.ext fun T => by simp [h₁])
    (fun c y z => ContinuousLinearMap.ext fun T => by simp [h₂])
    (fun y z z' => ContinuousLinearMap.ext fun T => by simp [h₃])
    (fun c y z => ContinuousLinearMap.ext fun T => by simp [h₄])

@[simp] theorem mkCov2_apply (f : V₁ → V₂ → RJet C → ℝ) (h₁ h₂ h₃ h₄ h₅ h₆) (y : V₁) (z : V₂)
    (T : RJet C) : mkCov2 f h₁ h₂ h₃ h₄ h₅ h₆ y z T = f y z T := rfl

/-- Continuity of a family of covector-valued bilinear maps from the continuity of its scalar
values. -/
theorem continuousOn_cov2 {Z : Type*} [TopologicalSpace Z] {s : Set Z}
    {Φ : Z → V₁ →L[ℝ] V₂ →L[ℝ] (RJet C →L[ℝ] ℝ)}
    (h : ∀ y z T, ContinuousOn (fun w => Φ w y z T) s) : ContinuousOn Φ s :=
  continuousOn_clm_apply.mpr fun y => continuousOn_clm_apply.mpr fun z =>
    continuousOn_clm_apply.mpr fun T => h y z T

theorem continuousOn_cov1 {Z : Type*} [TopologicalSpace Z] {s : Set Z}
    {Φ : Z → V₁ →L[ℝ] (RJet C →L[ℝ] ℝ)} (h : ∀ y T, ContinuousOn (fun w => Φ w y T) s) :
    ContinuousOn Φ s :=
  continuousOn_clm_apply.mpr fun y => continuousOn_clm_apply.mpr fun T => h y T

end Covectors

/-! ### The bosonic covector pieces -/

section BosonPieces

variable {C : Type} [Fintype C]

/-- `∂a ↦ (∂_μa_ν - ∂_νa_μ)`. -/
def FdaL : (Fin 4 → ConnFibre) →L[ℝ] (Fin 4 → ConnFibre) :=
  mkLinL (fun da μ ν => da μ ν - da ν μ) (fun _ _ => by funext μ ν; simp; abel)
    (fun _ _ => by funext μ ν; simp [smul_sub])

/-- `(A, a) ↦ [a_μ, A_ν] + [A_μ, a_ν]`. -/
def FcaL : ConnFibre →L[ℝ] ConnFibre →L[ℝ] (Fin 4 → ConnFibre) :=
  mkBilinL (fun A a μ ν => comm (a μ) (A ν) + comm (A μ) (a ν))
    (fun A A' a => by
      funext μ ν; simp only [Pi.add_apply, comm, mmul_add_left', mmul_add_right']; abel)
    (fun c A a => by
      funext μ ν; simp only [Pi.smul_apply, comm, mmul_smul_left', mmul_smul_right', smul_add,
        smul_sub])
    (fun A a a' => by
      funext μ ν; simp only [Pi.add_apply, comm, mmul_add_left', mmul_add_right']; abel)
    (fun c A a => by
      funext μ ν; simp only [Pi.smul_apply, comm, mmul_smul_left', mmul_smul_right', smul_add,
        smul_sub])

theorem Fdot_eq (A a : ConnFibre) (da : Fin 4 → ConnFibre) :
    Fdot A a da = FdaL da + FcaL A a := by
  funext μ ν; simp [Fdot, FdaL, FcaL]; abel

/-- `(a, H) ↦ (ρ_H(a_μ) H)_μ`. -/
def higgsActL : ConnFibre →L[ℝ] HiggsFibre →L[ℝ] (Fin 4 → HiggsFibre) :=
  mkBilinL (fun a H μ => higgsAct (a μ) H)
    (fun a a' H => by
      funext μ i; simp only [higgsAct, Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c a H => by
      funext μ i; simp only [higgsAct, Pi.smul_apply, Complex.real_smul, mul_assoc,
        Finset.mul_sum])
    (fun a H H' => by
      funext μ i; simp only [higgsAct, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c a H => by
      funext μ i
      simp only [higgsAct, Pi.smul_apply, Complex.real_smul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)

theorem Kdot_eq (A : ConnFibre) (H : HiggsFibre) (a : ConnFibre) (η : HiggsFibre)
    (dη : Fin 4 → HiggsFibre) : Kdot A H a η dη = dη + higgsActL a H + higgsActL A η := by
  funext μ; simp [Kdot, higgsActL]

end BosonPieces

/-! ### The bosonic covector -/

section BosonCovector

variable {C : Type} [Fintype C]

/-- Metric variation of the Yang–Mills coefficient: `(F, F', T) ↦ DYM_j(e)[ė(k)](F, F')`. -/
def ymMetCoeff (j : Fin 3) (e : CoframeFibre) :
    (Fin 4 → ConnFibre) →L[ℝ] (Fin 4 → ConnFibre) →L[ℝ] (RJet C →L[ℝ] ℝ) :=
  mkCov2 (fun F F' T => fderiv ℝ (ymCoeff j) e (metricLiftL e T.e) F F')
    (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp)
    (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp)

/-- Gauge variation of the Yang–Mills term through `∂a`. -/
def ymDaCoeff (j : Fin 3) (e : CoframeFibre) : (Fin 4 → ConnFibre) →L[ℝ] (RJet C →L[ℝ] ℝ) :=
  mkCov1 (fun F T => ymCoeff j e (FdaL T.F) F + ymCoeff j e F (FdaL T.F))
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring)

/-- Gauge variation of the Yang–Mills term through `a` (commutators with `A`). -/
def ymACoeff (j : Fin 3) (e : CoframeFibre) :
    ConnFibre →L[ℝ] (Fin 4 → ConnFibre) →L[ℝ] (RJet C →L[ℝ] ℝ) :=
  mkCov2 (fun A F T => ymCoeff j e (FcaL A T.A) F + ymCoeff j e F (FcaL A T.A))
    (fun _ _ _ _ => by simp; ring) (fun _ _ _ _ => by simp; ring)
    (fun _ _ _ _ => by simp; ring) (fun _ _ _ _ => by simp; ring)
    (fun _ _ _ _ => by simp; ring) (fun _ _ _ _ => by simp; ring)

/-- Metric variation of the Higgs-kinetic coefficient. -/
def higgsMetCoeff (e : CoframeFibre) :
    (Fin 4 → HiggsFibre) →L[ℝ] (Fin 4 → HiggsFibre) →L[ℝ] (RJet C →L[ℝ] ℝ) :=
  mkCov2 (fun K K' T => fderiv ℝ higgsCoeff e (metricLiftL e T.e) K K')
    (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp)
    (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp)

/-- Higgs variation of the kinetic term through `∂η`. -/
def higgsDCoeff (e : CoframeFibre) : (Fin 4 → HiggsFibre) →L[ℝ] (RJet C →L[ℝ] ℝ) :=
  mkCov1 (fun K T => higgsCoeff e T.K K + higgsCoeff e K T.K)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring)

/-- Gauge variation of the kinetic term (`ρ_H(a) H`). -/
def higgsHCoeff (e : CoframeFibre) :
    HiggsFibre →L[ℝ] (Fin 4 → HiggsFibre) →L[ℝ] (RJet C →L[ℝ] ℝ) :=
  mkCov2 (fun H K T => higgsCoeff e (higgsActL T.A H) K + higgsCoeff e K (higgsActL T.A H))
    (fun _ _ _ _ => by simp; ring) (fun _ _ _ _ => by simp; ring)
    (fun _ _ _ _ => by simp; ring) (fun _ _ _ _ => by simp; ring)
    (fun _ _ _ _ => by simp; ring) (fun _ _ _ _ => by simp; ring)

/-- Higgs variation of the kinetic term through `ρ_H(A) η`. -/
def higgsACoeff (e : CoframeFibre) :
    ConnFibre →L[ℝ] (Fin 4 → HiggsFibre) →L[ℝ] (RJet C →L[ℝ] ℝ) :=
  mkCov2 (fun A K T => higgsCoeff e (higgsActL A T.H) K + higgsCoeff e K (higgsActL A T.H))
    (fun _ _ _ _ => by simp; ring) (fun _ _ _ _ => by simp; ring)
    (fun _ _ _ _ => by simp; ring) (fun _ _ _ _ => by simp; ring)
    (fun _ _ _ _ => by simp; ring) (fun _ _ _ _ => by simp; ring)

/-- Higgs variation of the potential: `(Y, T) ↦ -2 (Re⟨η, Y⟩ + Re⟨Y, η⟩) √|g|`. -/
def potHCoeff (e : CoframeFibre) : HiggsFibre →L[ℝ] (RJet C →L[ℝ] ℝ) :=
  mkCov1 (fun Y T => -2 * (hInnerReL T.H Y + hInnerReL Y T.H) * volFactor e)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring)

/-- Metric variation of the potential (volume factor): `(s, T) ↦ -s D√|g|[ė(k)]`. -/
def potVCoeff (e : CoframeFibre) : ℝ →L[ℝ] (RJet C →L[ℝ] ℝ) :=
  mkCov1 (fun s T => -(s * fderiv ℝ volFactor e (metricLiftL e T.e)))
    (fun _ _ _ => by ring) (fun _ _ _ => by ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring)

/-- **The bosonic first-variation covector** `T ↦ D(bosonPt)(R)[redVar R T]`. -/
def bosonCov {Y : Type} (θ : CoefficientBank Y) (R : RJet C) : RJet C →L[ℝ] ℝ :=
  (∑ j, gaugeScalars θ j • (ymMetCoeff j R.e R.F R.F + ymDaCoeff j R.e R.F +
      ymACoeff j R.e R.A R.F)) +
    (higgsMetCoeff R.e R.K R.K + higgsDCoeff R.e R.K + higgsHCoeff R.e R.H R.K +
      higgsACoeff R.e R.A R.K) +
    θ.lambdaH • (potHCoeff R.e ((higgsQuad R.H - θ.vH ^ 2) • R.H) +
      potVCoeff R.e ((higgsQuad R.H - θ.vH ^ 2) ^ 2))

theorem bosonCov_apply {Y : Type} (θ : CoefficientBank Y) (R T : RJet C) :
    bosonCov θ R T = bosonDeriv θ R (redVar R T) := by
  simp only [bosonCov, bosonDeriv, redVar, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ymMetCoeff,
    ymDaCoeff, ymACoeff, higgsMetCoeff, higgsDCoeff, higgsHCoeff, higgsACoeff, potHCoeff,
    potVCoeff, mkCov1_apply, mkCov2_apply, RJet.mk_e, RJet.mk_F, RJet.mk_K, RJet.mk_H,
    Fdot_eq, Kdot_eq, map_add, ContinuousLinearMap.add_apply, map_smul, smul_eq_mul]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

end BosonCovector

/-! ### Continuity of the coefficients on the chart -/

section CoeffContinuity

variable {C : Type} [Fintype C]

theorem contDiffOn_ymCoeff (j : Fin 3) {n : WithTop ℕ∞} : ContDiffOn ℝ n (ymCoeff j) coframeGL :=
  fun _ he => (contDiffAt_ymCoeff j he).contDiffWithinAt

theorem contDiffOn_higgsCoeff {n : WithTop ℕ∞} : ContDiffOn ℝ n higgsCoeff coframeGL :=
  fun _ he => (contDiffAt_higgsCoeff he).contDiffWithinAt

theorem contDiffOn_volFactor {n : WithTop ℕ∞} : ContDiffOn ℝ n volFactor coframeGL :=
  fun _ he => (contDiffAt_volFactor he).contDiffWithinAt

theorem continuous_metricLiftL : Continuous metricLiftL :=
  (contDiff_metricLiftL (n := 0)).continuous

theorem continuousOn_ymMetCoeff (j : Fin 3) :
    ContinuousOn (ymMetCoeff (C := C) j) coframeGL := by
  have hD := (contDiffOn_ymCoeff j (n := 1)).continuousOn_fderiv_of_isOpen isOpen_coframeGL le_rfl
  refine continuousOn_cov2 fun F F' T => ?_
  exact ((hD.clm_apply (continuous_metricLiftL.clm_apply continuous_const).continuousOn).clm_apply
    continuousOn_const).clm_apply continuousOn_const

theorem continuousOn_ymDaCoeff (j : Fin 3) : ContinuousOn (ymDaCoeff (C := C) j) coframeGL := by
  have hY := (contDiffOn_ymCoeff j (n := 0)).continuousOn
  refine continuousOn_cov1 fun F T => ?_
  exact ((hY.clm_apply continuousOn_const).clm_apply continuousOn_const).add
    ((hY.clm_apply continuousOn_const).clm_apply continuousOn_const)

theorem continuousOn_ymACoeff (j : Fin 3) : ContinuousOn (ymACoeff (C := C) j) coframeGL := by
  have hY := (contDiffOn_ymCoeff j (n := 0)).continuousOn
  refine continuousOn_cov2 fun A F T => ?_
  exact ((hY.clm_apply continuousOn_const).clm_apply continuousOn_const).add
    ((hY.clm_apply continuousOn_const).clm_apply continuousOn_const)

theorem continuousOn_higgsMetCoeff : ContinuousOn (higgsMetCoeff (C := C)) coframeGL := by
  have hD := (contDiffOn_higgsCoeff (n := 1)).continuousOn_fderiv_of_isOpen isOpen_coframeGL le_rfl
  refine continuousOn_cov2 fun K K' T => ?_
  exact ((hD.clm_apply (continuous_metricLiftL.clm_apply continuous_const).continuousOn).clm_apply
    continuousOn_const).clm_apply continuousOn_const

theorem continuousOn_higgsDCoeff : ContinuousOn (higgsDCoeff (C := C)) coframeGL := by
  have hY := (contDiffOn_higgsCoeff (n := 0)).continuousOn
  refine continuousOn_cov1 fun K T => ?_
  exact ((hY.clm_apply continuousOn_const).clm_apply continuousOn_const).add
    ((hY.clm_apply continuousOn_const).clm_apply continuousOn_const)

theorem continuousOn_higgsHCoeff : ContinuousOn (higgsHCoeff (C := C)) coframeGL := by
  have hY := (contDiffOn_higgsCoeff (n := 0)).continuousOn
  refine continuousOn_cov2 fun H K T => ?_
  exact ((hY.clm_apply continuousOn_const).clm_apply continuousOn_const).add
    ((hY.clm_apply continuousOn_const).clm_apply continuousOn_const)

theorem continuousOn_higgsACoeff : ContinuousOn (higgsACoeff (C := C)) coframeGL := by
  have hY := (contDiffOn_higgsCoeff (n := 0)).continuousOn
  refine continuousOn_cov2 fun A K T => ?_
  exact ((hY.clm_apply continuousOn_const).clm_apply continuousOn_const).add
    ((hY.clm_apply continuousOn_const).clm_apply continuousOn_const)

theorem continuousOn_potHCoeff : ContinuousOn (potHCoeff (C := C)) coframeGL := by
  have hV := (contDiffOn_volFactor (n := 0)).continuousOn
  refine continuousOn_cov1 fun Y T => ?_
  exact continuousOn_const.mul hV

theorem continuousOn_potVCoeff : ContinuousOn (potVCoeff (C := C)) coframeGL := by
  have hD := (contDiffOn_volFactor (n := 1)).continuousOn_fderiv_of_isOpen isOpen_coframeGL le_rfl
  refine continuousOn_cov1 fun s T => ?_
  exact (continuousOn_const.mul (hD.clm_apply
    (continuous_metricLiftL.clm_apply continuous_const).continuousOn)).neg

end CoeffContinuity

/-! ### Convergence of the bosonic covector -/

section BosonConvergence

variable {C : Type} [Fintype C] {X : Type*} [MeasurableSpace X] {μ : Measure X}
  [IsFiniteMeasure μ]

open FirstVariationCalculus

/-- Measurability of chart coefficients along a.e.-measurable coframes in the chart. -/
theorem aesm_coeff {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] {Φ : CoframeFibre → W} (hΦ : ContinuousOn Φ coframeGL)
    {e : X → CoframeFibre} (he : AEMeasurable e μ) (hin : ∀ᵐ x ∂μ, e x ∈ coframeGL) :
    AEStronglyMeasurable (fun x => Φ (e x)) μ :=
  aestronglyMeasurable_comp_of_continuousOn' isOpen_coframeGL hΦ he hin

/-- Hypotheses on a coframe sequence: values in a compact subset of the chart, convergence in
measure. -/
structure CoframeConv (μ : Measure X) (Ke : Set CoframeFibre) (e : ℕ → X → CoframeFibre)
    (e₀ : X → CoframeFibre) : Prop where
  compact : IsCompact Ke
  sub : Ke ⊆ coframeGL
  meas : ∀ n, AEMeasurable (e n) μ
  mem : ∀ n, ∀ᵐ x ∂μ, e n x ∈ Ke
  mem₀ : ∀ᵐ x ∂μ, e₀ x ∈ Ke
  tendsto : TendstoInMeasure μ e atTop e₀

theorem CoframeConv.memGL {Ke : Set CoframeFibre} {e : ℕ → X → CoframeFibre}
    {e₀ : X → CoframeFibre} (h : CoframeConv μ Ke e e₀) (n : ℕ) :
    ∀ᵐ x ∂μ, e n x ∈ coframeGL := by
  filter_upwards [h.mem n] with x hx using h.sub hx

/-- Coefficient bilinear convergence along a converging coframe sequence (`L² × L² → L¹`). -/
theorem CoframeConv.bilin {Ke : Set CoframeFibre} {e : ℕ → X → CoframeFibre}
    {e₀ : X → CoframeFibre} (h : CoframeConv μ Ke e e₀) {V₁ V₂ W : Type*}
    [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]
    [NormedAddCommGroup V₂] [NormedSpace ℝ V₂] [FiniteDimensional ℝ V₂]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : CoframeFibre → V₁ →L[ℝ] V₂ →L[ℝ] W} (hΦ : ContinuousOn Φ coframeGL)
    {y : ℕ → X → V₁} {y₀ : X → V₁} (hy : RenewalGeometry.LpTendsto μ 2 y y₀)
    {z : ℕ → X → V₂} {z₀ : X → V₂} (hz : RenewalGeometry.LpTendsto μ 2 z z₀) :
    RenewalGeometry.LpTendsto μ 1 (fun n x => Φ (e n x) (y n x) (z n x))
      (fun x => Φ (e₀ x) (y₀ x) (z₀ x)) :=
  tendsto_coeff_bilin (p := 2) (q := 2) (r := 1) h.compact (hΦ.mono h.sub) h.mem h.mem₀
    h.tendsto (fun n => aesm_coeff hΦ (h.meas n) (h.memGL n)) (by norm_num) hy hz

/-- Coefficient-linear convergence along a converging coframe sequence (`L^p → L^p`). -/
theorem CoframeConv.apply {Ke : Set CoframeFibre} {e : ℕ → X → CoframeFibre}
    {e₀ : X → CoframeFibre} (h : CoframeConv μ Ke e e₀) {V₁ W : Type*}
    [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : CoframeFibre → V₁ →L[ℝ] W} (hΦ : ContinuousOn Φ coframeGL) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) {y : ℕ → X → V₁} {y₀ : X → V₁} (hy : RenewalGeometry.LpTendsto μ p y y₀) :
    RenewalGeometry.LpTendsto μ p (fun n x => Φ (e n x) (y n x)) (fun x => Φ (e₀ x) (y₀ x)) :=
  tendsto_coeff_apply h.compact (hΦ.mono h.sub) h.mem h.mem₀ h.tendsto
    (fun n => aesm_coeff hΦ (h.meas n) (h.memGL n)) hp hy

theorem ymPart_tendsto {Ke : Set CoframeFibre} {e : ℕ → X → CoframeFibre} {e₀ : X → CoframeFibre}
    (he : CoframeConv μ Ke e e₀) {F : ℕ → X → Fin 4 → ConnFibre} {F₀ : X → Fin 4 → ConnFibre}
    (hF : RenewalGeometry.LpTendsto μ 2 F F₀) {A : ℕ → X → ConnFibre} {A₀ : X → ConnFibre}
    (hA : RenewalGeometry.LpTendsto μ 2 A A₀) (j : Fin 3) :
    RenewalGeometry.LpTendsto μ 1
      (fun n x => (ymMetCoeff (C := C) j (e n x) (F n x) (F n x) + ymDaCoeff j (e n x) (F n x) +
        ymACoeff j (e n x) (A n x) (F n x)))
      (fun x => ymMetCoeff j (e₀ x) (F₀ x) (F₀ x) + ymDaCoeff j (e₀ x) (F₀ x) +
        ymACoeff j (e₀ x) (A₀ x) (F₀ x)) :=
  ((he.bilin (continuousOn_ymMetCoeff j) hF hF).add
    ((he.apply (continuousOn_ymDaCoeff j) (p := 2) (by norm_num) hF).mono (by norm_num)
      (by norm_num))).add (he.bilin (continuousOn_ymACoeff j) hA hF)

theorem higgsPart_tendsto {Ke : Set CoframeFibre} {e : ℕ → X → CoframeFibre}
    {e₀ : X → CoframeFibre} (he : CoframeConv μ Ke e e₀) {K : ℕ → X → Fin 4 → HiggsFibre}
    {K₀ : X → Fin 4 → HiggsFibre} (hK : RenewalGeometry.LpTendsto μ 2 K K₀)
    {H : ℕ → X → HiggsFibre} {H₀ : X → HiggsFibre} (hH : RenewalGeometry.LpTendsto μ 2 H H₀)
    {A : ℕ → X → ConnFibre} {A₀ : X → ConnFibre} (hA : RenewalGeometry.LpTendsto μ 2 A A₀) :
    RenewalGeometry.LpTendsto μ 1
      (fun n x => higgsMetCoeff (C := C) (e n x) (K n x) (K n x) + higgsDCoeff (e n x) (K n x) +
        higgsHCoeff (e n x) (H n x) (K n x) + higgsACoeff (e n x) (A n x) (K n x))
      (fun x => higgsMetCoeff (e₀ x) (K₀ x) (K₀ x) + higgsDCoeff (e₀ x) (K₀ x) +
        higgsHCoeff (e₀ x) (H₀ x) (K₀ x) + higgsACoeff (e₀ x) (A₀ x) (K₀ x)) :=
  (((he.bilin continuousOn_higgsMetCoeff hK hK).add
    ((he.apply continuousOn_higgsDCoeff (p := 2) (by norm_num) hK).mono (by norm_num)
      (by norm_num))).add (he.bilin continuousOn_higgsHCoeff hH hK)).add
    (he.bilin continuousOn_higgsACoeff hA hK)

theorem potPart_tendsto {Ke : Set CoframeFibre} {e : ℕ → X → CoframeFibre}
    {e₀ : X → CoframeFibre} (he : CoframeConv μ Ke e e₀) {H : ℕ → X → HiggsFibre}
    {H₀ : X → HiggsFibre} (hH : RenewalGeometry.LpTendsto μ 4 H H₀) {v : ℕ → ℝ} {v₀ : ℝ}
    (hv : Tendsto v atTop (𝓝 v₀)) :
    RenewalGeometry.LpTendsto μ 1
      (fun n x => potHCoeff (C := C) (e n x) ((higgsQuad (H n x) - v n ^ 2) • H n x) +
        potVCoeff (e n x) ((higgsQuad (H n x) - v n ^ 2) ^ 2))
      (fun x => potHCoeff (e₀ x) ((higgsQuad (H₀ x) - v₀ ^ 2) • H₀ x) +
        potVCoeff (e₀ x) ((higgsQuad (H₀ x) - v₀ ^ 2) ^ 2)) := by
  have h442 : ENNReal.HolderTriple 4 4 2 := holderTriple_four_four_two
  have h14 : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
  have hH2 := hH.mono (by norm_num) (by norm_num : (2 : ℝ≥0∞) ≤ 4)
  have hq : RenewalGeometry.LpTendsto μ 2 (fun n x => higgsQuad (H n x) - v n ^ 2)
      (fun x => higgsQuad (H₀ x) - v₀ ^ 2) :=
    (RenewalGeometry.LpTendsto.bilin (p := 4) (q := 4) (r := 2) hInnerReL hH hH).sub
      (LpTendsto.const_seq (μ := μ) (p := 2) (X := X) (hv.pow 2))
  have hYv : RenewalGeometry.LpTendsto μ 1 (fun n x => (higgsQuad (H n x) - v n ^ 2) • H n x)
      (fun x => (higgsQuad (H₀ x) - v₀ ^ 2) • H₀ x) :=
    RenewalGeometry.LpTendsto.bilin (p := 2) (q := 2) (r := 1) (ContinuousLinearMap.lsmul ℝ ℝ)
      hq hH2
  have hS : RenewalGeometry.LpTendsto μ 1 (fun n x => (higgsQuad (H n x) - v n ^ 2) ^ 2)
      (fun x => (higgsQuad (H₀ x) - v₀ ^ 2) ^ 2) := by
    have := RenewalGeometry.LpTendsto.bilin (p := 2) (q := 2) (r := 1)
      (ContinuousLinearMap.mul ℝ ℝ) hq hq
    exact this.congr (fun n => Eventually.of_forall fun x => by
      simp only [ContinuousLinearMap.mul_apply', sq]) (Eventually.of_forall fun x => by
      simp only [ContinuousLinearMap.mul_apply', sq])
  exact (he.apply continuousOn_potHCoeff (p := 1) (by norm_num) hYv).add
    (he.apply continuousOn_potVCoeff (p := 1) (by norm_num) hS)

/-- **Strong `L¹` convergence of the bosonic first-variation covector.**  If the coframes converge
in measure inside a compact subset of the nondegenerate chart, `F_h → F` and `K_h → K` in `L²`,
`A_h → A` and `H_h → H` in `L⁴`, and the couplings converge, then the covectors
`T ↦ D(bosonPt)(R_h)[redVar R_h T]` converge in `L¹` in operator norm. -/
theorem bosonCov_tendsto {Ke : Set CoframeFibre} {R : ℕ → X → RJet C} {R₀ : X → RJet C}
    (he : CoframeConv μ Ke (fun n x => (R n x).e) (fun x => (R₀ x).e))
    (hF : RenewalGeometry.LpTendsto μ 2 (fun n x => (R n x).F) (fun x => (R₀ x).F))
    (hA : RenewalGeometry.LpTendsto μ 4 (fun n x => (R n x).A) (fun x => (R₀ x).A))
    (hK : RenewalGeometry.LpTendsto μ 2 (fun n x => (R n x).K) (fun x => (R₀ x).K))
    (hH : RenewalGeometry.LpTendsto μ 4 (fun n x => (R n x).H) (fun x => (R₀ x).H))
    {Y : Type} {θ : ℕ → CoefficientBank Y} {θ₀ : CoefficientBank Y}
    (hs : ∀ j, Tendsto (fun n => gaugeScalars (θ n) j) atTop (𝓝 (gaugeScalars θ₀ j)))
    (hl : Tendsto (fun n => (θ n).lambdaH) atTop (𝓝 θ₀.lambdaH))
    (hv : Tendsto (fun n => (θ n).vH) atTop (𝓝 θ₀.vH)) :
    RenewalGeometry.LpTendsto μ 1 (fun n x => bosonCov (θ n) (R n x))
      (fun x => bosonCov θ₀ (R₀ x)) := by
  have hA2 := hA.mono (by norm_num) (by norm_num : (2 : ℝ≥0∞) ≤ 4)
  have hH2 := hH.mono (by norm_num) (by norm_num : (2 : ℝ≥0∞) ≤ 4)
  have hYMs := LpTendsto.finset_sum (μ := μ) (p := 1) Finset.univ fun j _ =>
    LpTendsto.smul_seq (hs j) (ymPart_tendsto (C := C) he hF hA2 j)
  exact (hYMs.add (higgsPart_tendsto (C := C) he hK hH2 hA2)).add
    (LpTendsto.smul_seq hl (potPart_tendsto (C := C) he hH hv))

end BosonConvergence

end EinsteinSM
end RenewalGeometry
