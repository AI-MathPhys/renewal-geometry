/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterEnergyIdentity
import RenewalGeometry.Gravity.HarmonicDefectForcingExact

/-!
# The harmonic coefficient chart of the open writer: analyticity and the explicit source
  (`eq:main-harmonic-normal-row`, `eq:main-open-compensator`, `eq:main-open-writer`;
  emergent-spacetime manuscript)

* `analyticAt_det`, `analyticAt_adjugate`, `analyticAt_inv_entry`: the entries of the inverse
  `4 × 4` record are analytic wherever the determinant does not vanish (Cramer's rule);
  `det_minkowski`: `det η = -1`.
* `analyticAt_harmA`, `analyticAt_harmB`, `analyticAt_harmC`, `analyticAt_harmA_inv`: the
  harmonic normal-row coefficients `a = -g^{00}`, `b^i = -g^{0i}`, `c^{ij} = g^{ij}` and `a⁻¹` are
  analytic at Minkowski.
* `harmonicSource` (**the explicit first-jet source**): the manuscript's `F` is "the analytic
  first-jet source of the harmonic-reduced vacuum Ricci equation".  By the reduced Ricci identity
  `R_{μν} - ∇_{(μ}C_{ν)} = -½ g^{αβ}∂_α∂_β g_{μν} + 𝓠_{μν}(g, ∂g)`
  (`HarmonicDefect.ricci_sub_symDefect`) and `g^{αβ}∂_α∂_β g = -a q_tt - 2b^i∂_i q_t + c^{ij}∂_i∂_j q`,
  the reduced vacuum equation is the normal row with `F = -2𝓠(g, g⁻¹, ∂g)`, where
  `∂_0 g = q_t = v` and `∂_i g = ∂_i q` (`metricJet`).  `harmonicWriterAcceleration` is the open
  writer `eq:main-open-writer` with this source.
* `compensatorMap` (the first-jet compensator `𝖦_h` of `eq:main-open-compensator` as a function of
  the site jet `(q, v, D⁺q)`), `compensator_eq`; `analyticAt_compensatorMap` (analytic at every
  `(0, Y)`), `compensatorMap_smul` (quadratic in the first jet, from `qRem_smul`),
  `hasFDerivAt_compensatorMap_zero` and `compensator_series_one_eq_zero` (vanishing linear part).
-/

open Finset Filter Topology
open scoped BigOperators

namespace RenewalGeometry.OpenWriterChart

open OpenWriterEnergy HarmonicWriter HarmonicDefect RootParityConnector

noncomputable section

set_option linter.unusedSectionVars false

/-! ### `fun_prop` leaves for analyticity -/

section Leaves

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

@[fun_prop] theorem chart_analyticAt_fst (x : E × F) : AnalyticAt ℝ (fun p : E × F => p.1) x :=
  analyticAt_fst

@[fun_prop] theorem chart_analyticAt_snd (x : E × F) : AnalyticAt ℝ (fun p : E × F => p.2) x :=
  analyticAt_snd

@[fun_prop] theorem chart_analyticAt_apply {ι : Type*} [Fintype ι] (i : ι) (x : ι → E) :
    AnalyticAt ℝ (fun f : ι → E => f i) x :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => E) i).analyticAt x

end Leaves

/-! ### The inverse record is analytic -/

theorem analyticAt_coord (i j : Fin 4) (x : MetricRec) : AnalyticAt ℝ (fun g : MetricRec => g i j) x := by
  fun_prop

theorem analyticAt_det (g₀ : MetricRec) :
    AnalyticAt ℝ (fun g : MetricRec => (Matrix.of g).det) g₀ := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine AnalyticAt.mul analyticAt_const ?_
  refine Finset.analyticAt_fun_prod _ (fun i _ => ?_)
  exact analyticAt_coord _ _ g₀

theorem analyticAt_adjugate (g₀ : MetricRec) (i j : Fin 4) :
    AnalyticAt ℝ (fun g : MetricRec => (Matrix.of g).adjugate i j) g₀ := by
  simp only [Matrix.adjugate_apply, Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine AnalyticAt.mul analyticAt_const ?_
  refine Finset.analyticAt_fun_prod _ (fun k _ => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact analyticAt_const
  · exact analyticAt_coord _ _ g₀

/-- Entries of the inverse record are analytic where `det g ≠ 0` (Cramer's rule). -/
theorem analyticAt_inv_entry (g₀ : MetricRec) (h : (Matrix.of g₀).det ≠ 0) (i j : Fin 4) :
    AnalyticAt ℝ (fun g : MetricRec => (Matrix.of g)⁻¹ i j) g₀ := by
  have e : (fun g : MetricRec => (Matrix.of g)⁻¹ i j) =
      fun g => ((Matrix.of g).det)⁻¹ * (Matrix.of g).adjugate i j := by
    funext g
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [e]
  exact ((analyticAt_det g₀).inv h).mul (analyticAt_adjugate g₀ i j)

theorem minkowski_eq_diagonal :
    Matrix.of minkowski = Matrix.diagonal (fun i : Fin 4 => if i = 0 then (-1 : ℝ) else 1) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [minkowski, Matrix.of_apply]
  · simp [minkowski, Matrix.of_apply, h]

theorem det_minkowski : (Matrix.of minkowski).det = -1 := by
  rw [minkowski_eq_diagonal, Matrix.det_diagonal, Fin.prod_univ_four]
  simp [Fin.ext_iff]

theorem det_minkowski_ne : (Matrix.of minkowski).det ≠ 0 := by
  rw [det_minkowski]; norm_num

theorem analyticAt_harmA : AnalyticAt ℝ harmA minkowski :=
  (analyticAt_inv_entry minkowski det_minkowski_ne 0 0).neg

theorem analyticAt_harmB (i : Fin 3) : AnalyticAt ℝ (harmB i) minkowski :=
  (analyticAt_inv_entry minkowski det_minkowski_ne 0 i.succ).neg

theorem analyticAt_harmC (i j : Fin 3) : AnalyticAt ℝ (harmC i j) minkowski :=
  analyticAt_inv_entry minkowski det_minkowski_ne i.succ j.succ

theorem analyticAt_harmA_inv : AnalyticAt ℝ (fun g => (harmA g)⁻¹) minkowski :=
  analyticAt_harmA.inv (by rw [harm_minkowski.1]; norm_num)

/-- The inverse of a symmetric record is symmetric, so `c^{ij}` is symmetric on ten-component
records. -/
theorem harmC_symm (g : MetricRec) (hg : ∀ μ ν, g μ ν = g ν μ) (i j : Fin 3) :
    harmC i j g = harmC j i g := by
  have hT : Matrix.transpose (Matrix.of g) = Matrix.of g := by
    ext μ ν; simp [Matrix.transpose_apply, Matrix.of_apply, hg]
  unfold harmC
  have h := Matrix.transpose_nonsing_inv (Matrix.of g)
  rw [hT] at h
  have := congrFun (congrFun h j.succ) i.succ
  rw [Matrix.transpose_apply] at this
  exact this

/-! ### The explicit first-jet source -/

/-- The metric first jet `∂_α g_{μν}` from the site jet `Y = (v, ∂_1 q, ∂_2 q, ∂_3 q)`:
`∂_0 g = v`, `∂_{i+1} g = ∂_i q`. -/
def metricJet (Y : MetricRec × (Fin 3 → MetricRec)) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  Fin.cons (α := fun _ => MetricRec) Y.1 Y.2

theorem metricJet_smul (t : ℝ) (Y : MetricRec × (Fin 3 → MetricRec)) :
    metricJet (t • Y) = fun α a b => t * metricJet Y α a b := by
  funext α a b
  refine Fin.cases ?_ (fun i => ?_) α
  · simp [metricJet]
  · simp [metricJet]

/-- The inverse record `g^{μν}` (matrix inverse, as an array). -/
def recInv (g : MetricRec) : MetricRec := fun i j => (Matrix.of g)⁻¹ i j

/-- **The harmonic first-jet source** `F(g, Y) = -2 𝓠(g, g⁻¹, ∂g)` of the harmonic-reduced
vacuum Ricci equation `R_{μν} - ∇_{(μ}C_{ν)} = 0` written as the normal row
`a q_tt + 2b^i ∂_i q_t - c^{ij}∂_i∂_j q - F = 0` (`eq:main-harmonic-normal-row`). -/
def harmonicSource (g : MetricRec) (Y : MetricRec × (Fin 3 → MetricRec)) : MetricRec :=
  fun μ ν => -2 * qRem g (recInv g) (metricJet Y) μ ν

/-- The open writer `eq:main-open-writer` with the explicit harmonic source. -/
def harmonicWriterAcceleration {N : ℕ} (q v : Grid N → MetricRec) (x : Grid N) : MetricRec :=
  openWriterAcceleration harmonicSource q v x

theorem harmonicSource_smul (g : MetricRec) (t : ℝ) (Y : MetricRec × (Fin 3 → MetricRec)) :
    harmonicSource g (t • Y) = t ^ 2 • harmonicSource g Y := by
  funext μ ν
  simp only [harmonicSource, metricJet_smul, qRem_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The compensator as a function of the site jet -/

/-- The site-jet space `(q, v, D₁⁺q, D₂⁺q, D₃⁺q)`. -/
abbrev JetSpace := MetricRec × (MetricRec × (Fin 3 → MetricRec))

/-- The first-jet compensator `𝖦_h` of `eq:main-open-compensator` as a function of the site jet
`w = (q, v, D⁺q)`, with `g = η + q`, the harmonic source and the coefficient differentials the
Fréchet derivatives of `c^{ij}`, `b^i`. -/
def compensatorMap (w : JetSpace) : MetricRec :=
  harmonicSource (minkowski + w.1) w.2
    - ∑ i, ∑ j, fderiv ℝ (harmC i j) (minkowski + w.1) (w.2.2 i) • w.2.2 j
    + ∑ i, fderiv ℝ (harmB i) (minkowski + w.1) (w.2.2 i) • w.2.1

theorem compensator_eq {N : ℕ} (q v : Grid N → MetricRec) (x : Grid N) :
    compensator harmonicSource (fun i j g w => fderiv ℝ (harmC i j) g w)
        (fun i g w => fderiv ℝ (harmB i) g w) minkowski (N : ℝ)⁻¹ (e N) q v x =
      compensatorMap (q x, v x, fun i => fwd (N : ℝ)⁻¹ (e N) i q x) := rfl

theorem compensatorMap_apply (w : JetSpace) (μ ν : Fin 4) :
    compensatorMap w μ ν = harmonicSource (minkowski + w.1) w.2 μ ν
      - ∑ i, ∑ j, fderiv ℝ (harmC i j) (minkowski + w.1) (w.2.2 i) * w.2.2 j μ ν
      + ∑ i, fderiv ℝ (harmB i) (minkowski + w.1) (w.2.2 i) * w.2.1 μ ν := by
  simp [compensatorMap, Finset.sum_apply]

/-- The compensator is quadratic in the first jet. -/
theorem compensatorMap_smul (q₀ : MetricRec) (Y : MetricRec × (Fin 3 → MetricRec)) (t : ℝ) :
    compensatorMap (q₀, t • Y) = t ^ 2 • compensatorMap (q₀, Y) := by
  funext μ ν
  simp only [compensatorMap_apply, harmonicSource_smul, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply, smul_eq_mul, map_smul, mul_sub, mul_add, Finset.mul_sum]
  congr 1
  · congr 1
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    ring
  · refine sum_congr rfl fun i _ => ?_
    ring

theorem compensatorMap_zero_jet (q₀ : MetricRec) : compensatorMap (q₀, 0) = 0 := by
  have := compensatorMap_smul q₀ 0 0
  simpa using this

/-- The compensator components are analytic at every point `(0, Y)` of the site-jet space. -/
theorem analyticAt_compensatorMap (μ ν : Fin 4) (y : MetricRec × (Fin 3 → MetricRec)) :
    AnalyticAt ℝ (fun w : JetSpace => compensatorMap w μ ν) (0, y) := by
  have hg : AnalyticAt ℝ (fun w : JetSpace => minkowski + w.1) (0, y) := by fun_prop
  have hg0 : minkowski + (0, y).1 = minkowski := by simp
  -- the source
  have hinv : AnalyticAt ℝ (fun w : JetSpace => recInv (minkowski + w.1)) (0, y) := by
    refine AnalyticAt.pi fun i => AnalyticAt.pi fun j => ?_
    exact (analyticAt_inv_entry minkowski det_minkowski_ne i j).comp_of_eq hg hg0
  have hjet : AnalyticAt ℝ (fun w : JetSpace => metricJet w.2) (0, y) := by
    refine AnalyticAt.pi fun α => ?_
    refine Fin.cases ?_ (fun i => ?_) α
    · simp only [metricJet, Fin.cons_zero]; fun_prop
    · simp only [metricJet, Fin.cons_succ]; fun_prop
  have hpoly : ∀ z : MetricRec × MetricRec × (Fin 4 → Fin 4 → Fin 4 → ℝ),
      AnalyticAt ℝ (fun p : MetricRec × MetricRec × (Fin 4 → Fin 4 → Fin 4 → ℝ) =>
        qRem p.1 p.2.1 p.2.2 μ ν) z := by
    intro z
    simp only [qRem, ricciJ, nablaC, dcUp, cDown, cUp, chr, dchr1, dginv]
    fun_prop
  have hF : AnalyticAt ℝ (fun w : JetSpace => harmonicSource (minkowski + w.1) w.2 μ ν) (0, y) := by
    have := (hpoly _).comp (hg.prod (hinv.prod hjet))
    simp only [harmonicSource]
    simp only [Function.comp_def] at this
    exact analyticAt_const.mul this
  -- the coefficient differentials
  have hev : ∀ (A : MetricRec → ℝ), AnalyticAt ℝ A minkowski → ∀ (L : JetSpace → MetricRec),
      AnalyticAt ℝ L (0, y) →
      AnalyticAt ℝ (fun w : JetSpace => fderiv ℝ A (minkowski + w.1) (L w)) (0, y) := by
    intro A hA L hL
    have hD : AnalyticAt ℝ (fun w : JetSpace => fderiv ℝ A (minkowski + w.1)) (0, y) :=
      hA.fderiv.comp_of_eq hg hg0
    exact ((ContinuousLinearMap.id ℝ (MetricRec →L[ℝ] ℝ)).analyticAt_bilinear _).comp
      (hD.prod hL)
  have hC : ∀ i j, AnalyticAt ℝ (fun w : JetSpace =>
      fderiv ℝ (harmC i j) (minkowski + w.1) (w.2.2 i) * w.2.2 j μ ν) (0, y) := fun i j =>
    (hev _ (analyticAt_harmC i j) (fun w => w.2.2 i) (by fun_prop)).mul (by fun_prop)
  have hB : ∀ i, AnalyticAt ℝ (fun w : JetSpace =>
      fderiv ℝ (harmB i) (minkowski + w.1) (w.2.2 i) * w.2.1 μ ν) (0, y) := fun i =>
    (hev _ (analyticAt_harmB i) (fun w => w.2.2 i) (by fun_prop)).mul (by fun_prop)
  have e : (fun w : JetSpace => compensatorMap w μ ν) = fun w =>
      harmonicSource (minkowski + w.1) w.2 μ ν
      - ∑ i, ∑ j, fderiv ℝ (harmC i j) (minkowski + w.1) (w.2.2 i) * w.2.2 j μ ν
      + ∑ i, fderiv ℝ (harmB i) (minkowski + w.1) (w.2.2 i) * w.2.1 μ ν := by
    funext w; exact compensatorMap_apply w μ ν
  rw [e]
  refine (hF.sub ?_).add ?_
  · exact Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j _ => hC i j
  · exact Finset.analyticAt_fun_sum _ fun i _ => hB i

/-- The compensator components have zero derivative at the flat jet `0`. -/
theorem hasFDerivAt_compensatorMap_zero (μ ν : Fin 4) :
    HasFDerivAt (fun w : JetSpace => compensatorMap w μ ν) (0 : JetSpace →L[ℝ] ℝ) 0 := by
  have hdiff := (analyticAt_compensatorMap μ ν 0).differentiableAt
  have hL : fderiv ℝ (fun w : JetSpace => compensatorMap w μ ν) 0 = 0 := by
    refine ContinuousLinearMap.ext fun d => ?_
    -- `t ↦ G(t d) = t² G(t d.1, d.2)` has derivative `0` at `0`
    have hψ : DifferentiableAt ℝ (fun t : ℝ => compensatorMap (t • d.1, d.2) μ ν) 0 := by
      have h1 := (analyticAt_compensatorMap μ ν d.2).differentiableAt
      have h2 : DifferentiableAt ℝ (fun t : ℝ => ((t • d.1, d.2) : JetSpace)) 0 := by fun_prop
      have h3 : ((fun t : ℝ => ((t • d.1, d.2) : JetSpace)) 0) = (0, d.2) := by simp
      have h1' : DifferentiableAt ℝ (fun w : JetSpace => compensatorMap w μ ν)
          ((fun t : ℝ => ((t • d.1, d.2) : JetSpace)) 0) := by rw [h3]; exact h1
      exact h1'.comp (0 : ℝ) h2
    have hφ : HasDerivAt (fun t : ℝ => compensatorMap (t • d) μ ν)
        (fderiv ℝ (fun w : JetSpace => compensatorMap w μ ν) 0 d) 0 := by
      have h2 : HasDerivAt (fun t : ℝ => t • d) d 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const d
      exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h2 (by simp)
    have hφ' : HasDerivAt (fun t : ℝ => compensatorMap (t • d) μ ν) 0 0 := by
      have e : (fun t : ℝ => compensatorMap (t • d) μ ν) =
          fun t => t ^ 2 * compensatorMap (t • d.1, d.2) μ ν := by
        funext t
        have := congrFun (congrFun (compensatorMap_smul (t • d.1) d.2 t) μ) ν
        simp only [Pi.smul_apply, smul_eq_mul] at this
        rw [← this]; rfl
      rw [e]
      have h := (hasDerivAt_pow 2 (0 : ℝ)).fun_mul hψ.hasDerivAt
      refine h.congr_deriv ?_
      norm_num
    simpa using hφ.unique hφ'
  rw [← hL]
  exact hdiff.hasFDerivAt

/-- The linear term of the power series of a compensator component at `0` vanishes. -/
theorem compensator_series_one_eq_zero (μ ν : Fin 4) (p : FormalMultilinearSeries ℝ JetSpace ℝ)
    (hp : HasFPowerSeriesAt (fun w : JetSpace => compensatorMap w μ ν) p 0) : p 1 = 0 := by
  have h1 := hp.hasFDerivAt
  have h2 := hasFDerivAt_compensatorMap_zero μ ν
  have := h1.unique h2
  rw [LinearIsometryEquiv.map_eq_zero_iff] at this
  exact this

theorem compensatorMap_zero (μ ν : Fin 4) : compensatorMap 0 μ ν = 0 := by
  show compensatorMap (0, 0) μ ν = 0
  rw [compensatorMap_zero_jet]; rfl

end

end RenewalGeometry.OpenWriterChart
