/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterContinuumComparison
import RenewalGeometry.Gravity.CoordinateCurvature

/-!
# Real interpolants of writer records and the continuum limit of the open writer
  (`thm:supp-open-einstein`, `lem:supp-open-reduced-consistency`; emergent-spacetime manuscript)

* `reC` (real part of a continuous function on `𝕋³`) with its Fourier coefficients
  `mFourierCoeff_reC` and `memH_reC` (`‖Re F‖_{H^r} ≤ ‖F‖_{H^r}`).
* `reField`, `interpRec` — the real trigonometric interpolant of a grid record array, a continuous
  record field on `𝕋³` (`sampleRec_interpRec`: `𝒮_h 𝓘_h q = q`); `isLineDeriv_reField` (its
  classical coordinate derivatives are the interpolants of the spectral derivatives) and
  `hasDerivAt_reField_time` (time derivatives commute with interpolation).
* `normalRow_sn_le` (the continuum normal row in `H^r`) and `interp_row_small` (**the continuum
  residual of the interpolant of a writer state is `O(h)` in `H^{s-2}`**).
* `comparison_of_force`, `interp_cauchy_grid`, `interp_cauchy_cont`, `init_mismatch_le`,
  `interp_cauchy` (**the interpolated writer solutions on two meshes differ by
  `C e^{Kt}(1 + t)(h + h')ε`**), `exists_limit_of_rate`, `trigSobSq_le_of_tendsto` (Fatou).
* `writer_continuum_limit` (**whole-sequence convergence with rate**), `writer_limit_solves` (the
  limit is a classical solution of the ten-component harmonic reduced equation with `∂ₜQ = V`,
  `∂ₜV = A`), `contSolution_eq_limit` (uniqueness in `IsContSolution`), and
  `writer_limit_curvature_rate` (the coordinate Riemann tensors converge at rate `O(h ε)` in
  `H^{s-3}`, `eq:supp-open-curvature-rate`) — `thm:supp-open-einstein` except the vacuum clause
  `G(g) = 0`.
-/

open Finset Filter Topology UnitAddTorus ComplexConjugate
open scoped BigOperators Real

namespace RenewalGeometry.OpenWriterContinuum

open TorusSobolevTransfer OpenWriterLifespan OpenWriterEnergyEstimate OpenWriterChart
  OpenWriterEnergy OpenWriterGridBridge RootParityConnector PeriodicGridSobolev.Composition
  HarmonicWriter

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

attribute [local irreducible] harmA harmB harmC compensatorMap

/-! ### Real parts -/

/-- The real part of a continuous function on `𝕋³`, as a continuous complex function. -/
def reC (F : CT) : CT := ⟨fun y => ((F y).re : ℂ), Complex.continuous_ofReal.comp
  (Complex.continuous_re.comp F.continuous)⟩

@[simp] theorem reC_apply (F : CT) (y : T3) : reC F y = ((F y).re : ℂ) := rfl

/-- The pointwise conjugate of a continuous function. -/
def conjC (F : CT) : CT := ⟨fun y => conj (F y), Complex.continuous_conj.comp F.continuous⟩

theorem mFourierCoeff_conjC (F : CT) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(conjC F) n = conj (mFourierCoeff ⇑F (-n)) := by
  unfold mFourierCoeff
  rw [← integral_conj]
  congr 1
  funext y
  simp only [conjC, ContinuousMap.coe_mk, smul_eq_mul, map_mul, neg_neg, mFourier_neg]

theorem reC_eq (F : CT) : reC F = (2 : ℂ)⁻¹ • (F + conjC F) := by
  ext y
  simp only [reC_apply, ContinuousMap.smul_apply, ContinuousMap.add_apply, conjC,
    ContinuousMap.coe_mk, smul_eq_mul]
  rw [Complex.re_eq_add_conj]
  ring

theorem mFourierCoeff_reC (F : CT) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(reC F) n = (2 : ℂ)⁻¹ * (mFourierCoeff ⇑F n + conj (mFourierCoeff ⇑F (-n))) := by
  rw [reC_eq, mFourierCoeff_smul', PeriodicGridSobolev.Sampling.mFourierCoeff_add,
    mFourierCoeff_conjC, smul_eq_mul]

theorem tsymSq_neg (α : Fin 3 → ℕ) (n : Fin 3 → ℤ) :
    PeriodicGridSobolev.tsymSq α (-n) = PeriodicGridSobolev.tsymSq α n := by
  simp [PeriodicGridSobolev.tsymSq]

theorem trigWeight_neg (r : ℕ) (n : Fin 3 → ℤ) :
    PeriodicGridSobolev.trigWeight r (-n) = PeriodicGridSobolev.trigWeight r n := by
  simp only [PeriodicGridSobolev.trigWeight, tsymSq_neg]

/-- `Re F ∈ H^r` with `‖Re F‖_{H^r} ≤ ‖F‖_{H^r}`. -/
theorem memH_reC {r : ℕ} {F : CT} (hF : MemH r ⇑F) : MemH r ⇑(reC F) ∧ sn r ⇑(reC F) ≤ sn r ⇑F := by
  have hneg : MemH r (fun y => F y) → Summable fun n =>
      PeriodicGridSobolev.trigWeight r n * ‖mFourierCoeff ⇑F (-n)‖ ^ 2 := by
    intro h
    have := (Equiv.neg (Fin 3 → ℤ)).summable_iff.mpr h
    refine this.congr fun n => ?_
    simp [trigWeight_neg]
  have hFn := hneg hF
  have hpt : ∀ n, PeriodicGridSobolev.trigWeight r n * ‖mFourierCoeff ⇑(reC F) n‖ ^ 2 ≤
      (1 / 2) * (PeriodicGridSobolev.trigWeight r n * ‖mFourierCoeff ⇑F n‖ ^ 2) +
        (1 / 2) * (PeriodicGridSobolev.trigWeight r n * ‖mFourierCoeff ⇑F (-n)‖ ^ 2) := by
    intro n
    rw [mFourierCoeff_reC, norm_mul]
    have hW := PeriodicGridSobolev.Sampling.trigWeight_nonneg r n
    have h1 := norm_add_le (mFourierCoeff ⇑F n) (conj (mFourierCoeff ⇑F (-n)))
    rw [Complex.norm_conj] at h1
    have h2 : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by rw [norm_inv]; norm_num
    rw [h2]
    have h3 : (1 / 2 * ‖mFourierCoeff ⇑F n + conj (mFourierCoeff ⇑F (-n))‖) ^ 2 ≤
        (1 / 2) * ‖mFourierCoeff ⇑F n‖ ^ 2 + (1 / 2) * ‖mFourierCoeff ⇑F (-n)‖ ^ 2 := by
      have := norm_nonneg (mFourierCoeff ⇑F n + conj (mFourierCoeff ⇑F (-n)))
      nlinarith [sq_nonneg (‖mFourierCoeff ⇑F n‖ - ‖mFourierCoeff ⇑F (-n)‖),
        norm_nonneg (mFourierCoeff ⇑F n), norm_nonneg (mFourierCoeff ⇑F (-n))]
    nlinarith
  have hS : Summable fun n =>
      (1 / 2) * (PeriodicGridSobolev.trigWeight r n * ‖mFourierCoeff ⇑F n‖ ^ 2) +
        (1 / 2) * (PeriodicGridSobolev.trigWeight r n * ‖mFourierCoeff ⇑F (-n)‖ ^ 2) :=
    (hF.mul_left _).add (hFn.mul_left _)
  have hs : MemH r ⇑(reC F) := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (PeriodicGridSobolev.Sampling.trigWeight_nonneg _ _) (sq_nonneg _)) hpt hS
  refine ⟨hs, ?_⟩
  unfold sn PeriodicGridSobolev.trigSobSq
  refine Real.sqrt_le_sqrt ((hs.tsum_le_tsum hpt hS).trans (le_of_eq ?_))
  rw [(hF.mul_left _).tsum_add (hFn.mul_left _), tsum_mul_left, tsum_mul_left]
  have e : ∑' n, PeriodicGridSobolev.trigWeight r n * ‖mFourierCoeff ⇑F (-n)‖ ^ 2 =
      ∑' n, PeriodicGridSobolev.trigWeight r n * ‖mFourierCoeff ⇑F n‖ ^ 2 := by
    rw [← (Equiv.neg (Fin 3 → ℤ)).tsum_eq]
    exact tsum_congr fun n => by simp [trigWeight_neg]
  rw [e]
  ring

/-! ### Real interpolants of grid records -/

section Interp

variable {N : ℕ} [NeZero N]

/-- The trigonometric interpolation as a linear map. -/
def interpL : (Grid N → ℂ) →ₗ[ℂ] CT where
  toFun := PeriodicGridSobolev.interp
  map_add' := interp_add
  map_smul' := interp_smul

/-- The real interpolant field of a family of complex grid arrays: `y ↦ (Re 𝓘_h w_{μν}(y))_{μν}`. -/
def reField (w : Fin 4 → Fin 4 → Grid N → ℂ) : C(T3, MetricRec) :=
  ⟨fun y μ ν => (PeriodicGridSobolev.interp (w μ ν) y).re, by
    refine continuous_pi fun μ => continuous_pi fun ν => ?_
    exact Complex.continuous_re.comp (PeriodicGridSobolev.interp (w μ ν)).continuous⟩

@[simp] theorem reField_apply (w : Fin 4 → Fin 4 → Grid N → ℂ) (y : T3) (μ ν : Fin 4) :
    reField w y μ ν = (PeriodicGridSobolev.interp (w μ ν) y).re := rfl

theorem cmp_reField (w : Fin 4 → Fin 4 → Grid N → ℂ) (μ ν : Fin 4) :
    cmp (reField w) μ ν = reC (PeriodicGridSobolev.interp (w μ ν)) := by
  ext y; simp

/-- **The real interpolant of a grid record**, `𝓘_h q`. -/
def interpRec (u : Grid N → MetricRec) : C(T3, MetricRec) :=
  reField fun μ ν => cx (comp u μ ν)

theorem sampleRec_interpRec (u : Grid N → MetricRec) : sampleRec N ⇑(interpRec u) = u := by
  funext x μ ν
  simp [interpRec, sampleRec, PeriodicGridSobolev.interp_sample, cx, comp]

/-- Every point of the torus lifts to `ℝ³`. -/
theorem exists_lift (x : T3) : ∃ y : Fin 3 → ℝ, x = fun j => ((y j : ℝ) : UnitAddCircle) := by
  choose y hy using fun j => QuotientAddGroup.mk_surjective (x j)
  exact ⟨y, funext fun j => (hy j).symm⟩

theorem lift_add_lineShift (y : Fin 3 → ℝ) (i : Fin 3) (t : ℝ) :
    (fun j => ((y j : ℝ) : UnitAddCircle)) + lineShift i t =
      PeriodicGridSobolev.Sampling.linePt y i t := by
  funext j
  simp only [Pi.add_apply, lineShift, PeriodicGridSobolev.Sampling.linePt]
  by_cases hj : j = i
  · subst hj; simp [AddCircle.coe_add]
  · simp [hj]

/-- **Classical derivatives of the real interpolant**: the coordinate derivative of
`Re 𝓘_h w` is `Re 𝓘_h(specD_i w)`. -/
theorem isLineDeriv_reField (i : Fin 3) (w : Fin 4 → Fin 4 → Grid N → ℂ) :
    IsLineDeriv i ⇑(reField w)
      ⇑(reField fun μ ν => PeriodicGridSobolev.Sampling.specD i (w μ ν)) := by
  intro x
  obtain ⟨y, rfl⟩ := exists_lift x
  refine hasDerivAt_pi.2 fun μ => hasDerivAt_pi.2 fun ν => ?_
  have h := PeriodicGridSobolev.Sampling.hasDerivAt_interp_line (w μ ν) y i
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e1 : (fun t : ℝ => reField w ((fun j => ((y j : ℝ) : UnitAddCircle)) + lineShift i t) μ ν) =
      ⇑Complex.reCLM ∘ fun t => PeriodicGridSobolev.interp (w μ ν)
        (PeriodicGridSobolev.Sampling.linePt y i t) := by
    funext t; simp [lift_add_lineShift]
  have e0 : PeriodicGridSobolev.Sampling.linePt y i 0 = fun j => ((y j : ℝ) : UnitAddCircle) := by
    funext j; simp [PeriodicGridSobolev.Sampling.linePt]
  rw [e1]
  convert h2 using 1
  simp [e0]

/-- The interpolant is a fixed real-linear combination of the grid values. -/
theorem interp_apply_eq_sum (u : Grid N → ℂ) (y : T3) :
    PeriodicGridSobolev.interp u y = ∑ x, u x *
      PeriodicGridSobolev.interp (fun z => if z = x then (1 : ℂ) else 0) y := by
  have e : u = ∑ x, u x • (fun z => if z = x then (1 : ℂ) else 0) := by
    funext z; simp [Finset.sum_apply]
  conv_lhs => rw [e]
  rw [show PeriodicGridSobolev.interp (∑ x, u x • fun z => if z = x then (1 : ℂ) else 0) =
    interpL (∑ x, u x • fun z => if z = x then (1 : ℂ) else 0) from rfl, map_sum]
  simp only [map_smul, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rfl

/-- **Time derivatives commute with real interpolation.** -/
theorem hasDerivAt_reField_time {w : ℝ → Fin 4 → Fin 4 → Grid N → ℂ}
    {w' : Fin 4 → Fin 4 → Grid N → ℂ} {t : ℝ}
    (hw : ∀ μ ν x, HasDerivAt (fun τ => w τ μ ν x) (w' μ ν x) t) (y : T3) :
    HasDerivAt (fun τ => reField (w τ) y) (reField w' y) t := by
  refine hasDerivAt_pi.2 fun μ => hasDerivAt_pi.2 fun ν => ?_
  have e1 : (fun τ => reField (w τ) y μ ν) = fun τ => (∑ x, w τ μ ν x *
      PeriodicGridSobolev.interp (fun z => if z = x then (1 : ℂ) else 0) y).re :=
    funext fun τ => congrArg Complex.re (interp_apply_eq_sum _ y)
  have e2 : reField w' y μ ν = (∑ x, w' μ ν x *
      PeriodicGridSobolev.interp (fun z => if z = x then (1 : ℂ) else 0) y).re :=
    congrArg Complex.re (interp_apply_eq_sum _ y)
  show HasDerivAt (fun τ => reField (w τ) y μ ν) (reField w' y μ ν) t
  rw [e1, e2]
  have h : HasDerivAt (fun τ => ∑ x, w τ μ ν x *
      PeriodicGridSobolev.interp (fun z => if z = x then (1 : ℂ) else 0) y)
      (∑ x, w' μ ν x * PeriodicGridSobolev.interp (fun z => if z = x then (1 : ℂ) else 0) y) t :=
    HasDerivAt.fun_sum fun x _ => (hw μ ν x).mul_const _
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h

/-- Interpolants of grid arrays are in every `H^r`, with
`‖𝓘_h u‖²_{H^r} ≤ (π/2)^{2r} ‖u‖²_{r,h}`. -/
theorem memH_interp (r : ℕ) (u : Grid N → ℂ) :
    MemH r ⇑(PeriodicGridSobolev.interp u) ∧
      sn r ⇑(PeriodicGridSobolev.interp u) ≤ Real.sqrt (pc r) * PeriodicGridSobolev.sobNorm r u := by
  refine ⟨(isTP_interp u).summable r, ?_⟩
  have h := trigSobSq_proj_le_sobSq (N := N) r (⇑(PeriodicGridSobolev.interp u))
  rw [show PeriodicGridSobolev.Sampling.proj N ⇑(PeriodicGridSobolev.interp u) =
    PeriodicGridSobolev.interp u by
      unfold PeriodicGridSobolev.Sampling.proj
      congr 1
      funext x
      exact PeriodicGridSobolev.interp_sample u x] at h
  have e : PeriodicGridSobolev.Sampling.sample N ⇑(PeriodicGridSobolev.interp u) = u := by
    funext x; exact PeriodicGridSobolev.interp_sample u x
  rw [e] at h
  unfold sn PeriodicGridSobolev.sobNorm
  rw [← Real.sqrt_mul (pc_pos r).le]
  exact Real.sqrt_le_sqrt h

theorem memH_cmp_reField (r : ℕ) (w : Fin 4 → Fin 4 → Grid N → ℂ) (μ ν : Fin 4) :
    MemH r ⇑(cmp (reField w) μ ν) ∧
      sn r ⇑(cmp (reField w) μ ν) ≤ Real.sqrt (pc r) * PeriodicGridSobolev.sobNorm r (w μ ν) := by
  rw [cmp_reField]
  obtain ⟨h1, h2⟩ := memH_interp r (w μ ν)
  obtain ⟨h3, h4⟩ := memH_reC h1
  exact ⟨h3, h4.trans h2⟩

end Interp

/-! ### The continuum normal row in `H^r` -/

open HarmonicDefect in
/-- The harmonic first-jet source is analytic in the site jet at the flat jet. -/
theorem analyticAt_source_jet (μ ν : Fin 4) :
    AnalyticAt ℝ (fun w : JetSpace => harmonicSource (minkowski + w.1) w.2 μ ν) 0 := by
  have hg : AnalyticAt ℝ (fun w : JetSpace => minkowski + w.1) 0 := by fun_prop
  have hg0 : minkowski + (0 : JetSpace).1 = minkowski := by simp
  have hinv : AnalyticAt ℝ (fun w : JetSpace => recInv (minkowski + w.1)) 0 := by
    refine AnalyticAt.pi fun i => AnalyticAt.pi fun j => ?_
    exact (analyticAt_inv_entry minkowski det_minkowski_ne i j).comp_of_eq hg hg0
  have hjet : AnalyticAt ℝ (fun w : JetSpace => metricJet w.2) 0 := by
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
  have := (hpoly _).comp (hg.prod (hinv.prod hjet))
  simp only [harmonicSource]
  simp only [Function.comp_def] at this
  exact analyticAt_const.mul this

/-- The continuum site-jet field `y ↦ (Q(y), V(y), ∂Q(y))`. -/
def jetField (Q V : C(T3, MetricRec)) (Qd : Fin 3 → C(T3, MetricRec)) : C(T3, JetSpace) :=
  ⟨fun y => (Q y, V y, fun i => Qd i y),
    Q.continuous.prodMk (V.continuous.prodMk (continuous_pi fun i => (Qd i).continuous))⟩

theorem ccoord_jetField_inl (Q V : C(T3, MetricRec)) (Qd : Fin 3 → C(T3, MetricRec))
    (k : Σ _ : Fin 4, Fin 4) : ccoord bJ (jetField Q V Qd) (Sum.inl k) = ccoord bM Q k := by
  ext y; simp [ccoord_apply, bJ, Module.Basis.prod_repr_inl, jetField]

theorem ccoord_jetField_inr_inl (Q V : C(T3, MetricRec)) (Qd : Fin 3 → C(T3, MetricRec))
    (k : Σ _ : Fin 4, Fin 4) : ccoord bJ (jetField Q V Qd) (Sum.inr (Sum.inl k)) = ccoord bM V k := by
  ext y; simp [ccoord_apply, bJ, Module.Basis.prod_repr_inr, Module.Basis.prod_repr_inl, jetField]

theorem ccoord_jetField_inr_inr (Q V : C(T3, MetricRec)) (Qd : Fin 3 → C(T3, MetricRec))
    (i : Fin 3) (k : Σ _ : Fin 4, Fin 4) :
    ccoord bJ (jetField Q V Qd) (Sum.inr (Sum.inr ⟨i, k⟩)) = ccoord bM (Qd i) k := by
  ext y; simp [ccoord_apply, bJ, Module.Basis.prod_repr_inr, Pi.basis_repr, jetField]

theorem ccoordSum_jetField (r : ℕ) (Q V : C(T3, MetricRec)) (Qd : Fin 3 → C(T3, MetricRec)) :
    ccoordSum r bJ (jetField Q V Qd) =
      ccoordSum r bM Q + ccoordSum r bM V + ∑ i, ccoordSum r bM (Qd i) := by
  unfold ccoordSum
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [ccoord_jetField_inl, ccoord_jetField_inr_inl]
  have e : ∑ x : (Σ _ : Fin 3, Σ _ : Fin 4, Fin 4),
      sn r ⇑(ccoord bJ (jetField Q V Qd) (Sum.inr (Sum.inr x))) =
      ∑ i, ∑ k, sn r ⇑(ccoord bM (Qd i) k) := by
    rw [Fintype.sum_sigma]
    exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by rw [ccoord_jetField_inr_inr]
  rw [e]
  ring

theorem memH_jetField {r : ℕ} {Q V : C(T3, MetricRec)} {Qd : Fin 3 → C(T3, MetricRec)}
    (hQ : ∀ k, MemH r ⇑(ccoord bM Q k)) (hV : ∀ k, MemH r ⇑(ccoord bM V k))
    (hQd : ∀ i k, MemH r ⇑(ccoord bM (Qd i) k)) : ∀ k, MemH r ⇑(ccoord bJ (jetField Q V Qd) k) := by
  rintro (k | k | ⟨i, k⟩)
  · rw [ccoord_jetField_inl]; exact hQ k
  · rw [ccoord_jetField_inr_inl]; exact hV k
  · rw [ccoord_jetField_inr_inr]; exact hQd i k

theorem sn_sum_le' {r : ℕ} {ι : Type*} (s : Finset ι) {F : ι → CT} (hF : ∀ i, MemH r ⇑(F i)) :
    MemH r ⇑(∑ i ∈ s, F i) ∧ sn r ⇑(∑ i ∈ s, F i) ≤ ∑ i ∈ s, sn r ⇑(F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [sum_empty, sum_empty]
    refine ⟨memH_zero r, ?_⟩
    unfold sn PeriodicGridSobolev.trigSobSq
    simp [mFourierCoeff_zero']
  | insert a t ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact ⟨memH_add (hF a) ih.1, (sn_add_le' (hF a) ih.1).trans (add_le_add le_rfl ih.2)⟩

/-- **The continuum normal row in `H^r`** (`r ≥ 2`): on a small ball, for `Q ∈ H^{r+2}`,
`V ∈ H^{r+1}`, `W ∈ H^r`, every component of the normal row of the jet is in `H^r` with
`‖ρ_{μν}‖_{H^r} ≤ C (‖Q‖_{H^{r+2}} + ‖V‖_{H^{r+1}} + ‖W‖_{H^r})`. -/
theorem normalRow_sn_le (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (Q V W : C(T3, MetricRec)) (Qd Vd : Fin 3 → C(T3, MetricRec))
      (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)), IsContJet Q V Qd Vd Qdd →
      (∀ k, MemH (r + 2) ⇑(ccoord bM Q k)) → (∀ k, MemH (r + 1) ⇑(ccoord bM V k)) →
      (∀ k, MemH r ⇑(ccoord bM W k)) →
      ccoordSum (r + 2) bM Q + ccoordSum (r + 1) bM V ≤ δ → ∀ μ ν : Fin 4,
      ∃ R : CT, ⇑R = rowF Q V W Qd Vd Qdd μ ν ∧ MemH r ⇑R ∧
        sn r ⇑R ≤ C * (ccoordSum (r + 2) bM Q + ccoordSum (r + 1) bM V + ccoordSum r bM W) := by
  obtain ⟨δA, hδA, KA, hKA, hLA⟩ := coef_mul_family r hr (fun _ : Unit => harmA)
    (fun _ => analyticAt_harmA)
  obtain ⟨δL, hδL, KL, hKL, hL⟩ := coef_mul_family r hr coefFam analyticAt_coefFam
  have hS : ∀ μ ν : Fin 4, ∃ δ > 0, ∃ C ≥ 0, ∀ J : C(T3, JetSpace),
      (∀ k, MemH r ⇑(ccoord bJ J k)) → ccoordSum r bJ J ≤ δ →
      ∃ F : CT, (∀ y, F y = ((harmonicSource (minkowski + (0 + J y).1) (0 + J y).2 μ ν -
        harmonicSource (minkowski + (0 : JetSpace).1) (0 : JetSpace).2 μ ν : ℝ) : ℂ)) ∧
        MemH r ⇑F ∧ sn r ⇑F ≤ C * ccoordSum r bJ J := by
    intro μ ν
    obtain ⟨p, R, hp⟩ := analyticAt_source_jet μ ν
    obtain ⟨δ, hδ, C, hC, hm⟩ := cont_moser r hr bJ hp
    exact ⟨δ, hδ, C, hC, fun J hJ hJδ => (hm J hJ hJδ).2⟩
  choose δS hδS CS hCS hSm using hS
  set δS0 : ℝ := (univ : Finset (Fin 4 × Fin 4)).inf' univ_nonempty (fun p => δS p.1 p.2)
  have hδS0 : 0 < δS0 := by
    rw [Finset.lt_inf'_iff]; intro p _; exact hδS p.1 p.2
  have hδS0le : ∀ μ ν, δS0 ≤ δS μ ν := fun μ ν =>
    Finset.inf'_le _ (mem_univ (μ, ν))
  set CS0 : ℝ := ∑ p : Fin 4 × Fin 4, CS p.1 p.2
  have hCS0 : ∀ μ ν, CS μ ν ≤ CS0 := fun μ ν =>
    single_le_sum (f := fun p : Fin 4 × Fin 4 => CS p.1 p.2) (fun p _ => hCS p.1 p.2)
      (mem_univ (μ, ν))
  have hCS0n : 0 ≤ CS0 := sum_nonneg fun p _ => hCS p.1 p.2
  set δ : ℝ := min (min δA δL) (δS0 / 5)
  have hδ : 0 < δ := by positivity
  refine ⟨δ, hδ, KA + 2 * 3 * KL + 9 * KL + 5 * CS0, by positivity,
    fun Q V W Qd Vd Qdd hJ hQ hV hW hX μ ν => ?_⟩
  set X := ccoordSum (r + 2) bM Q + ccoordSum (r + 1) bM V
  have hQX : ccoordSum (r + 2) bM Q ≤ X := le_add_of_nonneg_right (ccoordSum_nonneg _ _ _)
  have hVX : ccoordSum (r + 1) bM V ≤ X := le_add_of_nonneg_left (ccoordSum_nonneg _ _ _)
  have hQr : ∀ k, MemH r ⇑(ccoord bM Q k) := fun k => memH_mono (by omega) (hQ k)
  have hQrX : ccoordSum r bM Q ≤ X := (ccoordSum_mono (by omega) hQ).trans hQX
  have hVr : ∀ k, MemH r ⇑(ccoord bM V k) := fun k => memH_mono (by omega) (hV k)
  have hVrX : ccoordSum r bM V ≤ X := (ccoordSum_mono (by omega) hV).trans hVX
  have hQd : ∀ i, (∀ k, MemH (r + 1) ⇑(ccoord bM (Qd i) k)) ∧
      ccoordSum (r + 1) bM (Qd i) ≤ ccoordSum (r + 2) bM Q := fun i =>
    ccoordSum_deriv_le (hJ.dQ i) hQ
  have hQdd : ∀ i j, (∀ k, MemH r ⇑(ccoord bM (Qdd i j) k)) ∧
      ccoordSum r bM (Qdd i j) ≤ ccoordSum (r + 1) bM (Qd j) := fun i j =>
    ccoordSum_deriv_le (hJ.dQd i j) (hQd j).1
  have hVd : ∀ i, (∀ k, MemH r ⇑(ccoord bM (Vd i) k)) ∧
      ccoordSum r bM (Vd i) ≤ ccoordSum (r + 1) bM V := fun i =>
    ccoordSum_deriv_le (hJ.dV i) hV
  have hQδ : ccoordSum r bM Q ≤ min δA δL := hQrX.trans (hX.trans (min_le_left _ _))
  -- the four kinds of terms
  obtain ⟨PA, hPA, hPAm, hPAs⟩ := hLA () Q hQr (hQδ.trans (min_le_left _ _)) (cmp W μ ν)
    (memH_cmp hW μ ν)
  have hPB : ∀ i, ∃ P : CT, (∀ y, P y = ((harmB i (minkowski + Q y) : ℝ) : ℂ) *
      cmp (Vd i) μ ν y) ∧ MemH r ⇑P ∧ sn r ⇑P ≤ KL * sn r ⇑(cmp (Vd i) μ ν) := fun i =>
    hL (Sum.inr i) Q hQr (hQδ.trans (min_le_right _ _)) _ (memH_cmp (hVd i).1 μ ν)
  have hPC : ∀ i j, ∃ P : CT, (∀ y, P y = ((harmC i j (minkowski + Q y) : ℝ) : ℂ) *
      cmp (Qdd i j) μ ν y) ∧ MemH r ⇑P ∧ sn r ⇑P ≤ KL * sn r ⇑(cmp (Qdd i j) μ ν) := fun i j =>
    hL (Sum.inl (i, j)) Q hQr (hQδ.trans (min_le_right _ _)) _ (memH_cmp (hQdd i j).1 μ ν)
  choose PB hPBe hPBm hPBs using hPB
  choose PC hPCe hPCm hPCs using hPC
  have hJm := memH_jetField hQr hVr (fun i k => memH_mono (by omega) ((hQd i).1 k))
  have hJs : ccoordSum r bJ (jetField Q V Qd) ≤ 5 * X := by
    rw [ccoordSum_jetField]
    have h3 : ∀ i, ccoordSum r bM (Qd i) ≤ X := fun i =>
      ((ccoordSum_mono (by omega) (hQd i).1).trans (hQd i).2).trans hQX
    have h4 : ∑ i, ccoordSum r bM (Qd i) ≤ 3 * X := by
      calc _ ≤ ∑ _i : Fin 3, X := sum_le_sum fun i _ => h3 i
        _ = 3 * X := by simp
    linarith
  have hJδ : ccoordSum r bJ (jetField Q V Qd) ≤ δS μ ν := by
    refine hJs.trans ?_
    have : X ≤ δS0 / 5 := hX.trans (min_le_right _ _)
    have := hδS0le μ ν
    linarith
  obtain ⟨PS, hPSe, hPSm, hPSs⟩ := hSm μ ν (jetField Q V Qd) hJm hJδ
  -- assembly
  refine ⟨PA + (2 : ℂ) • ∑ i, PB i - ∑ i, ∑ j, PC i j - PS, ?_, ?_, ?_⟩
  · funext y
    have h0 : harmonicSource (minkowski + (0 : JetSpace).1) (0 : JetSpace).2 μ ν = 0 := by
      have := harmonicSource_zero_jet (minkowski + (0 : JetSpace).1)
      rw [show (0 : JetSpace).2 = 0 from rfl, this]; rfl
    simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.coe_sum, Finset.sum_apply, hPA, hPBe, hPCe, hPSe, h0, smul_eq_mul]
    simp only [rowF, normalRow, cmp_apply, jetField, ContinuousMap.coe_mk, zero_add, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, sub_zero]
    push_cast
    ring
  · have hB := sn_sum_le' univ hPBm
    have hC := sn_sum_le' univ fun i => (sn_sum_le' univ (hPCm i)).1
    exact memH_sub (memH_sub (memH_add hPAm (memH_smul (2 : ℂ) hB.1)) hC.1) hPSm
  · have hB := sn_sum_le' univ hPBm
    have hCi : ∀ i, MemH r ⇑(∑ j, PC i j) ∧ sn r ⇑(∑ j, PC i j) ≤ ∑ j, sn r ⇑(PC i j) :=
      fun i => sn_sum_le' univ (hPCm i)
    have hC := sn_sum_le' univ fun i => (hCi i).1
    have hW0 : ∀ μ ν, sn r ⇑(cmp W μ ν) ≤ ccoordSum r bM W := fun μ ν =>
      sn_cmp_le_ccoordSum _ _ _ _
    have hBi : ∀ i, sn r ⇑(PB i) ≤ KL * X := fun i =>
      (hPBs i).trans (mul_le_mul_of_nonneg_left ((sn_cmp_le_ccoordSum _ _ _ _).trans
        ((hVd i).2.trans hVX)) hKL)
    have hCij : ∀ i j, sn r ⇑(PC i j) ≤ KL * X := fun i j =>
      (hPCs i j).trans (mul_le_mul_of_nonneg_left ((sn_cmp_le_ccoordSum _ _ _ _).trans
        ((hQdd i j).2.trans ((hQd j).2.trans hQX))) hKL)
    have hBs : sn r ⇑(∑ i, PB i) ≤ 3 * (KL * X) := hB.2.trans (by
      calc _ ≤ ∑ _i : Fin 3, KL * X := sum_le_sum fun i _ => hBi i
        _ = 3 * (KL * X) := by simp)
    have hCs : sn r ⇑(∑ i, ∑ j, PC i j) ≤ 9 * (KL * X) := hC.2.trans (by
      calc _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, KL * X :=
            sum_le_sum fun i _ => (hCi i).2.trans (sum_le_sum fun j _ => hCij i j)
        _ = 9 * (KL * X) := by simp; ring)
    have hSs : sn r ⇑PS ≤ CS0 * (5 * X) :=
      hPSs.trans (mul_le_mul (hCS0 μ ν) hJs (ccoordSum_nonneg _ _ _) hCS0n)
    have hAs : sn r ⇑PA ≤ KA * ccoordSum r bM W := hPAs.trans (mul_le_mul_of_nonneg_left (hW0 μ ν) hKA)
    have hX0 : 0 ≤ X := add_nonneg (ccoordSum_nonneg _ _ _) (ccoordSum_nonneg _ _ _)
    have hW00 := ccoordSum_nonneg r bM W
    have t1 := sn_sub_le' (memH_sub (memH_add hPAm (memH_smul (2 : ℂ) hB.1)) hC.1) hPSm
    have t2 := sn_sub_le' (memH_add hPAm (memH_smul (2 : ℂ) hB.1)) hC.1
    have t3 := sn_add_le' hPAm (memH_smul (2 : ℂ) hB.1)
    have t4 := sn_smul r (2 : ℂ) (∑ i, PB i)
    have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [hn2] at t4
    have p1 := mul_nonneg hKA hX0
    have p2 := mul_nonneg hKL hW00
    have p3 := mul_nonneg hCS0n hW00
    calc sn r ⇑(PA + (2 : ℂ) • ∑ i, PB i - ∑ i, ∑ j, PC i j - PS)
        ≤ sn r ⇑PA + 2 * sn r ⇑(∑ i, PB i) + sn r ⇑(∑ i, ∑ j, PC i j) + sn r ⇑PS := by
          linarith
      _ ≤ KA * ccoordSum r bM W + 2 * (3 * (KL * X)) + 9 * (KL * X) + CS0 * (5 * X) := by
          linarith
      _ ≤ (KA + 2 * 3 * KL + 9 * KL + 5 * CS0) * (X + ccoordSum r bM W) := by
          nlinarith

/-! ### The interpolant jet of a grid record -/

section InterpJet

variable {N : ℕ} [NeZero N]

/-- `∂ᵢ` of the real interpolant: the real interpolant of the spectral derivative. -/
def interpD (u : Grid N → MetricRec) (i : Fin 3) : C(T3, MetricRec) :=
  reField fun μ ν => PeriodicGridSobolev.Sampling.specD i (cx (comp u μ ν))

/-- `∂ᵢ∂ⱼ` of the real interpolant. -/
def interpDD (u : Grid N → MetricRec) (i j : Fin 3) : C(T3, MetricRec) :=
  reField fun μ ν => PeriodicGridSobolev.Sampling.specD i
    (PeriodicGridSobolev.Sampling.specD j (cx (comp u μ ν)))

theorem isContJet_interp (q v : Grid N → MetricRec) :
    IsContJet (interpRec q) (interpRec v) (interpD q) (interpD v) (interpDD q) where
  dQ i := isLineDeriv_reField i _
  dQd i j := isLineDeriv_reField i _
  dV i := isLineDeriv_reField i _

theorem memH_interpRec (r : ℕ) (u : Grid N → MetricRec) (k : Σ _ : Fin 4, Fin 4) :
    MemH r ⇑(ccoord bM (interpRec u) k) ∧
      sn r ⇑(ccoord bM (interpRec u) k) ≤
        Real.sqrt (pc r) * PeriodicGridSobolev.sobNorm r (cx (comp u k.1 k.2)) := by
  rw [ccoord_bM]
  exact memH_cmp_reField r _ k.1 k.2

theorem ccoordSum_interpRec_le (r s : ℕ) {q : Grid N → MetricRec} (hq : IsSymRec q)
    (v : Grid N → MetricRec) (hr : r ≤ s + 1) :
    ccoordSum r bM (interpRec q) ≤ 16 * Real.sqrt (pc r) * Xnorm s q v := by
  unfold ccoordSum
  calc ∑ k, sn r ⇑(ccoord bM (interpRec q) k)
      ≤ ∑ _k : Σ _ : Fin 4, Fin 4, Real.sqrt (pc r) * Xnorm s q v := by
        refine sum_le_sum fun k _ => (memH_interpRec r q k).2.trans ?_
        exact mul_le_mul_of_nonneg_left (sobNorm_q_le s hq v _ _ hr) (Real.sqrt_nonneg _)
    _ = 16 * Real.sqrt (pc r) * Xnorm s q v := by simp; ring

theorem ccoordSum_interpRec_v_le (r s : ℕ) (q : Grid N → MetricRec) {v : Grid N → MetricRec}
    (hv : IsSymRec v) (hr : r ≤ s) :
    ccoordSum r bM (interpRec v) ≤ 16 * Real.sqrt (pc r) * Xnorm s q v := by
  unfold ccoordSum
  calc ∑ k, sn r ⇑(ccoord bM (interpRec v) k)
      ≤ ∑ _k : Σ _ : Fin 4, Fin 4, Real.sqrt (pc r) * Xnorm s q v := by
        refine sum_le_sum fun k _ => (memH_interpRec r v k).2.trans ?_
        exact mul_le_mul_of_nonneg_left (sobNorm_v_le s q hv _ _ hr) (Real.sqrt_nonneg _)
    _ = 16 * Real.sqrt (pc r) * Xnorm s q v := by simp; ring

theorem contTop_interp_le (s : ℕ) {q v : Grid N → MetricRec} (hq : IsSymRec q) (hv : IsSymRec v) :
    contTop s (interpRec q) (interpRec v) ≤
      16 * (Real.sqrt (pc (s + 1)) + Real.sqrt (pc s)) * Xnorm s q v := by
  unfold contTop
  have h1 := ccoordSum_interpRec_le (s + 1) s hq v le_rfl
  have h2 := ccoordSum_interpRec_v_le s s q hv le_rfl
  linarith

theorem comp_symRec_eq (u : Grid N → MetricRec) (μ ν : Fin 4) :
    comp (symRec u) μ ν = comp u (upperOf μ ν).1.1 (upperOf μ ν).1.2 := rfl

/-- **The continuum residual of the interpolant of a writer state is `O(h)`** (upper components):
for a symmetric record `X = (q, v)` in the small top ball, the continuum normal row `ρ` of the
interpolant jet `(𝓘_h q, 𝓘_h v, 𝓘_h V_{0,h}(q, v))` satisfies
`‖ρ_κ‖_{H^{s-2}} ≤ C h ‖X‖_{X^s_h}` for every upper component `κ`. -/
theorem interp_row_small (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (q v : Grid N → MetricRec), IsSymRec q → IsSymRec v →
      Xnorm s q v ≤ δ → ∀ κ : Upper, ∃ R : CT,
        ⇑R = rowF (interpRec q) (interpRec v) (interpRec (symRec (harmonicWriterAcceleration q v)))
          (interpD q) (interpD v) (interpDD q) κ.1.1 κ.1.2 ∧ MemH (s - 2) ⇑R ∧
        sn (s - 2) ⇑R ≤ C * (N : ℝ)⁻¹ * Xnorm s q v := by
  obtain ⟨δc, hδc, Cc, hCc, hcons⟩ := sampled_row_consistency s (by omega)
  obtain ⟨δn, hδn, Cn, hCn, hrow⟩ := normalRow_sn_le (s - 1) (by omega)
  obtain ⟨Ce, hCe, herr⟩ := PeriodicGridSobolev.Sampling.sampling_error (s - 2) 1 (by omega)
  obtain ⟨δA, hδA, KA, hKA, hacc⟩ := accel_bound s (by omega)
  set Ct : ℝ := 16 * (Real.sqrt (pc (s + 1)) + Real.sqrt (pc s))
  have hCt : 0 ≤ Ct := by positivity
  set δ : ℝ := min δA (min (δc / (Ct + 1)) (δn / (Ct + 1)))
  have hδ : 0 < δ := by positivity
  set Cw : ℝ := 16 * Real.sqrt (pc (s - 1)) * KA
  refine ⟨δ, hδ, Real.sqrt (pc (s - 2)) * Cc * Ct + Real.sqrt Ce * Cn * (Ct + Cw),
    by positivity, fun N _ q v hq hv hX κ => ?_⟩
  set X := Xnorm s q v
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  set V0 := harmonicWriterAcceleration q v
  have hct : contTop s (interpRec q) (interpRec v) ≤ Ct * X := contTop_interp_le s hq hv
  have hctδ : ∀ a, 0 < a → δ ≤ a / (Ct + 1) → Ct * X ≤ a := by
    intro a ha hδa
    have h1 : X ≤ a / (Ct + 1) := hX.trans hδa
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  -- (1) the sampled residual
  have hQm : ∀ k, MemH (s + 1) ⇑(ccoord bM (interpRec q) k) := fun k => (memH_interpRec _ _ k).1
  have hVm : ∀ k, MemH s ⇑(ccoord bM (interpRec v) k) := fun k => (memH_interpRec _ _ k).1
  obtain ⟨-, hc⟩ := hcons N (interpRec q) (interpRec v) (interpRec (symRec V0)) (interpD q)
    (interpD v) (interpDD q) (isContJet_interp q v) hQm hVm
    (hct.trans (hctδ δc hδc ((min_le_right _ _).trans (min_le_left _ _))))
  have hS : PeriodicGridSobolev.sobNorm (s - 2) (PeriodicGridSobolev.Sampling.sample N
      (rowF (interpRec q) (interpRec v) (interpRec (symRec V0)) (interpD q) (interpD v)
        (interpDD q) κ.1.1 κ.1.2)) ≤ Cc * (N : ℝ)⁻¹ * (Ct * X) := by
    have h1 := hc κ.1.1 κ.1.2
    rw [sampleRec_interpRec, sampleRec_interpRec, sampleRec_interpRec] at h1
    have e : comp (symRec V0 - V0) κ.1.1 κ.1.2 = 0 := by
      funext x
      simp only [comp, Pi.sub_apply, symRec_upper, sub_self, Pi.zero_apply]
    have e2 : cx (comp (symRec V0 - V0) κ.1.1 κ.1.2) = 0 := by
      rw [e]; funext x; simp [cx]
    rw [e2, mul_zero, zero_sub, PeriodicGridSobolev.Moser.sobNorm_neg] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hct (by positivity))
  -- (2) the residual is in `H^{s-1}`
  have hWm : ∀ k, MemH (s - 1) ⇑(ccoord bM (interpRec (symRec V0)) k) := fun k =>
    (memH_interpRec _ _ k).1
  have hWs : ccoordSum (s - 1) bM (interpRec (symRec V0)) ≤ Cw * X := by
    unfold ccoordSum
    calc ∑ k, sn (s - 1) ⇑(ccoord bM (interpRec (symRec V0)) k)
        ≤ ∑ _k : Σ _ : Fin 4, Fin 4, Real.sqrt (pc (s - 1)) * (KA * X) := by
          refine sum_le_sum fun k _ => (memH_interpRec _ _ k).2.trans ?_
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          rw [comp_symRec_eq]
          exact hacc N q v hq hv (hX.trans (min_le_left _ _)) _ _
      _ = Cw * X := by simp only [Cw]; simp; ring
  have hQ1 : ∀ k, MemH (s - 1 + 2) ⇑(ccoord bM (interpRec q) k) := fun k =>
    memH_mono (by omega) (hQm k)
  have hV1 : ∀ k, MemH (s - 1 + 1) ⇑(ccoord bM (interpRec v) k) := fun k =>
    memH_mono (by omega) (hVm k)
  have hsz : ccoordSum (s - 1 + 2) bM (interpRec q) + ccoordSum (s - 1 + 1) bM (interpRec v) ≤
      Ct * X := by
    have e1 : s - 1 + 2 = s + 1 := by omega
    have e2 : s - 1 + 1 = s := by omega
    rw [e1, e2]
    exact hct
  obtain ⟨R, hR, hRm, hRs⟩ := hrow (interpRec q) (interpRec v) (interpRec (symRec V0)) (interpD q)
    (interpD v) (interpDD q) (isContJet_interp q v) hQ1 hV1 hWm
    (hsz.trans (hctδ δn hδn ((min_le_right _ _).trans (min_le_right _ _)))) κ.1.1 κ.1.2
  have hRs' : sn (s - 1) ⇑R ≤ Cn * ((Ct + Cw) * X) := by
    refine hRs.trans (mul_le_mul_of_nonneg_left ?_ hCn)
    linarith
  refine ⟨R, hR, memH_mono (by omega) hRm, ?_⟩
  -- (3) aliasing: `R = 𝒫_h R - (𝒫_h R - R)`
  have hRm1 : MemH (s - 2 + 1) ⇑R := by
    have e : s - 2 + 1 = s - 1 := by omega
    rw [e]; exact hRm
  obtain ⟨hEm, hEb⟩ := herr N R hRm1
  have hPm : MemH (s - 2) ⇑(PeriodicGridSobolev.Sampling.proj N ⇑R) :=
    (isTP_interp _).summable _
  have eR : R = PeriodicGridSobolev.Sampling.proj N ⇑R - (PeriodicGridSobolev.Sampling.proj N ⇑R - R) := by
    abel
  have h1 : sn (s - 2) ⇑(PeriodicGridSobolev.Sampling.proj N ⇑R) ≤
      Real.sqrt (pc (s - 2)) * (Cc * (N : ℝ)⁻¹ * (Ct * X)) := by
    have hp := trigSobSq_proj_le_sobSq (N := N) (s - 2) ⇑R
    have hS' : PeriodicGridSobolev.sobNorm (s - 2) (PeriodicGridSobolev.Sampling.sample N ⇑R) ≤
        Cc * (N : ℝ)⁻¹ * (Ct * X) := by rw [hR]; exact hS
    unfold sn
    have h0 : 0 ≤ Cc * (N : ℝ)⁻¹ * (Ct * X) := by positivity
    calc Real.sqrt (PeriodicGridSobolev.trigSobSq (s - 2) ⇑(PeriodicGridSobolev.Sampling.proj N ⇑R))
        ≤ Real.sqrt (pc (s - 2) * (Cc * (N : ℝ)⁻¹ * (Ct * X)) ^ 2) := by
          refine Real.sqrt_le_sqrt (hp.trans ?_)
          refine mul_le_mul_of_nonneg_left ?_ (pc_pos _).le
          rw [← PeriodicGridSobolev.sobNorm_sq]
          exact pow_le_pow_left₀ (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _) hS' 2
      _ = Real.sqrt (pc (s - 2)) * (Cc * (N : ℝ)⁻¹ * (Ct * X)) := by
          rw [Real.sqrt_mul (pc_pos _).le, Real.sqrt_sq h0]
  have h2 : sn (s - 2) ⇑(PeriodicGridSobolev.Sampling.proj N ⇑R - R) ≤
      Real.sqrt Ce * (N : ℝ)⁻¹ * sn (s - 1) ⇑R := by
    unfold sn
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have e : s - 2 + 1 = s - 1 := by omega
    rw [e] at hEb
    have e2 : Ce * (((N : ℝ) ^ 2) ^ 1)⁻¹ * PeriodicGridSobolev.trigSobSq (s - 1) ⇑R =
        (Real.sqrt Ce * (N : ℝ)⁻¹ * Real.sqrt (PeriodicGridSobolev.trigSobSq (s - 1) ⇑R)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hCe, Real.sq_sqrt (trigSobSq_nonneg _ _)]
      field_simp
    rw [e2] at hEb
    calc Real.sqrt (PeriodicGridSobolev.trigSobSq (s - 2) ⇑(PeriodicGridSobolev.Sampling.proj N ⇑R - R))
        ≤ Real.sqrt ((Real.sqrt Ce * (N : ℝ)⁻¹ *
            Real.sqrt (PeriodicGridSobolev.trigSobSq (s - 1) ⇑R)) ^ 2) := Real.sqrt_le_sqrt hEb
      _ = _ := Real.sqrt_sq (by positivity)
  have h3 := sn_sub_le' hPm hEm
  rw [← eR] at h3
  have hh : 0 ≤ (N : ℝ)⁻¹ := by positivity
  calc sn (s - 2) ⇑R ≤ Real.sqrt (pc (s - 2)) * (Cc * (N : ℝ)⁻¹ * (Ct * X)) +
        Real.sqrt Ce * (N : ℝ)⁻¹ * (Cn * ((Ct + Cw) * X)) := by
        have := mul_le_mul_of_nonneg_left hRs' (by positivity : 0 ≤ Real.sqrt Ce * (N : ℝ)⁻¹)
        linarith
    _ = (Real.sqrt (pc (s - 2)) * Cc * Ct + Real.sqrt Ce * Cn * (Ct + Cw)) * (N : ℝ)⁻¹ * X := by
        ring

end InterpJet

/-! ### Comparison of a forced sampled history with the writer -/

/-- **Comparison with a forced record** (the difference estimate in the form used by the
comparison and Cauchy arguments): for `s ≥ 5` there are mesh-independent `δ, K, C` such that a
writer solution `(q, v)` and any symmetric forced history `(p, w)` (`p_t = w`,
`w_t = V_{0,h}(p, w) + f` on the upper components, `f` continuous, `‖f‖_{s-2,h} ≤ F₀`), both in
the grid top ball, satisfy `‖(q - p, v - w)(t)‖_{X^{s-2}_h} ≤ C e^{Kt}(e₀ + (1 + t) F₀)` and the
same bound for the acceleration difference in `H^{s-3}_h`. -/
theorem comparison_of_force (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (T : ℝ) (q v p w f : ℝ → Grid N → MetricRec)
      (F₀ : ℝ), IsWriterSolution T q v → (∀ t ∈ Set.Icc 0 T, Xnorm s (q t) (v t) ≤ δ) →
      (∀ t ∈ Set.Icc 0 T, IsSymRec (p t) ∧ IsSymRec (w t) ∧
        (∀ x, HasDerivAt (fun τ => p τ x) (w t x) t) ∧
        (∀ x (κ : Upper), HasDerivAt (fun τ => w τ x κ.1.1 κ.1.2)
          (harmonicWriterAcceleration (p t) (w t) x κ.1.1 κ.1.2 + f t x κ.1.1 κ.1.2) t) ∧
        Xnorm s (p t) (w t) ≤ δ ∧ Fnorm (s - 2) (f t) ≤ F₀) →
      ContinuousOn f (Set.Icc 0 T) → ∀ t ∈ Set.Icc 0 T,
        Xnorm (s - 2) (q t - p t) (v t - w t) ≤
          C * Real.exp (K * t) * (Xnorm (s - 2) (q 0 - p 0) (v 0 - w 0) + (1 + t) * F₀) ∧
        ∀ κ : Upper, PeriodicGridSobolev.sobNorm (s - 3)
          (cx (comp (harmonicWriterAcceleration (q t) (v t) -
            (harmonicWriterAcceleration (p t) (w t) + f t)) κ.1.1 κ.1.2)) ≤
          C * Real.exp (K * t) * (Xnorm (s - 2) (q 0 - p 0) (v 0 - w 0) + (1 + t) * F₀) := by
  obtain ⟨δd, hδd, Kd, hKd, hdiff⟩ := open_writer_difference s (s - 2) (by omega) (by omega)
  obtain ⟨δa, hδa, Ka, hKa, hacc⟩ := dAcc_bound s (s - 2) (by omega) (by omega)
  refine ⟨min δd δa, lt_min hδd hδa, Kd, hKd, (Ka + 1) * (6 + 2 * Kd + 1), by positivity,
    fun N _ T q v p w f F₀ hsol hXq hY hfc t ht => ?_⟩
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hF0 : 0 ≤ F₀ := (Fnorm_nonneg _ _).trans (hY 0 ⟨le_rfl, hT⟩).2.2.2.2.2
  have hpair : IsForcedPair s δd T q p v w (fun _ => 0) f := by
    intro τ hτ
    obtain ⟨hqs, hvs, hq, hv⟩ := hsol τ hτ
    obtain ⟨hps, hws, hp, hw, hYX, -⟩ := hY τ hτ
    refine ⟨hqs, hvs, hps, hws, hq, hp, fun x κ => ?_, hw,
      (hXq τ hτ).trans (min_le_left _ _), hYX.trans (min_le_left _ _)⟩
    simpa using hv x κ
  have hD := hdiff N T q p v w (fun _ => 0) f hpair continuousOn_const hfc t ht
  have hint : ∫ τ in (0)..t, Fnorm (s - 2) ((fun _ => (0 : Grid N → MetricRec)) τ - f τ) ≤
      t * F₀ := by
    have hic : ContinuousOn (fun τ => Fnorm (s - 2) ((fun _ => (0 : Grid N → MetricRec)) τ - f τ))
        (Set.Icc 0 t) :=
      (continuous_Fnorm (s - 2)).comp_continuousOn
        (continuousOn_const.sub (hfc.mono (Set.Icc_subset_Icc le_rfl ht.2)))
    have h1 : ∫ τ in (0)..t, Fnorm (s - 2) ((fun _ => (0 : Grid N → MetricRec)) τ - f τ) ≤
        ∫ _τ in (0)..t, F₀ := intervalIntegral.integral_mono_on ht.1
      (hic.intervalIntegrable_of_Icc ht.1) intervalIntegrable_const
      (fun τ hτ => by
        simp only [zero_sub, Fnorm_neg]
        exact (hY τ ⟨hτ.1, hτ.2.trans ht.2⟩).2.2.2.2.2)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
    exact h1
  set e0 := Xnorm (s - 2) (q 0 - p 0) (v 0 - w 0)
  have he0 : 0 ≤ e0 := Xnorm_nonneg _ _ _
  set E := e0 + (1 + t) * F₀
  have hE0 : 0 ≤ E := add_nonneg he0 (mul_nonneg (by linarith [ht.1]) hF0)
  have hexp1 : 1 ≤ Real.exp (Kd * t) := Real.one_le_exp (mul_nonneg hKd ht.1)
  have hDiff : Xnorm (s - 2) (q t - p t) (v t - w t) ≤ Real.exp (Kd * t) * ((6 + 2 * Kd) * E) := by
    refine hD.trans ?_
    have h1 : Kd * ∫ τ in (0)..t, Fnorm (s - 2) ((fun _ => (0 : Grid N → MetricRec)) τ - f τ) ≤
        Kd * (t * F₀) := mul_le_mul_of_nonneg_left hint hKd
    have h2 : 3 * e0 + Kd * (t * F₀) ≤ (6 + 2 * Kd) * E / 2 := by
      have h3 : t * F₀ ≤ (1 + t) * F₀ := by nlinarith
      have h4 := mul_le_mul_of_nonneg_left h3 hKd
      have h5 := mul_nonneg hKd he0
      have h6 : 0 ≤ (1 + t) * F₀ := mul_nonneg (by linarith [ht.1]) hF0
      simp only [E]
      nlinarith
    calc 2 * Real.exp (Kd * t) * (3 * e0 + Kd * ∫ τ in (0)..t,
          Fnorm (s - 2) ((fun _ => (0 : Grid N → MetricRec)) τ - f τ))
        ≤ 2 * Real.exp (Kd * t) * (3 * e0 + Kd * (t * F₀)) := by gcongr
      _ ≤ 2 * Real.exp (Kd * t) * ((6 + 2 * Kd) * E / 2) := by gcongr
      _ = Real.exp (Kd * t) * ((6 + 2 * Kd) * E) := by ring
  refine ⟨?_, fun κ => ?_⟩
  · refine hDiff.trans ?_
    have : (6 + 2 * Kd) ≤ (Ka + 1) * (6 + 2 * Kd + 1) := by nlinarith
    calc Real.exp (Kd * t) * ((6 + 2 * Kd) * E) ≤
          Real.exp (Kd * t) * ((Ka + 1) * (6 + 2 * Kd + 1) * E) := by gcongr
      _ = (Ka + 1) * (6 + 2 * Kd + 1) * Real.exp (Kd * t) * E := by ring
  · obtain ⟨hqs, hvs, -, -⟩ := hsol t ht
    obtain ⟨hps, hws, -, -, hYX, hft⟩ := hY t ht
    have hA := hacc N (q t) (p t) (v t) (w t) 0 (f t) hqs hps hvs hws
      ((hXq t ht).trans (min_le_right _ _)) (hYX.trans (min_le_right _ _)) κ
    have edA : dAcc (q t) (p t) (v t) (w t) 0 (f t) =
        harmonicWriterAcceleration (q t) (v t) - (harmonicWriterAcceleration (p t) (w t) + f t) := by
      simp only [dAcc, add_zero]
    have es : s - 2 - 1 = s - 3 := by omega
    rw [edA, es, zero_sub, Fnorm_neg] at hA
    refine hA.trans ?_
    have hFE : F₀ ≤ Real.exp (Kd * t) * E := by
      have : F₀ ≤ E := by
        have : 0 ≤ t * F₀ := mul_nonneg ht.1 hF0
        simp only [E]; nlinarith
      nlinarith
    calc Ka * (Xnorm (s - 2) (q t - p t) (v t - w t) + Fnorm (s - 2) (f t))
        ≤ Ka * (Real.exp (Kd * t) * ((6 + 2 * Kd) * E) + Real.exp (Kd * t) * E) := by
          gcongr
          exact hft.trans hFE
      _ = Ka * ((6 + 2 * Kd + 1) * (Real.exp (Kd * t) * E)) := by ring
      _ ≤ (Ka + 1) * ((6 + 2 * Kd + 1) * (Real.exp (Kd * t) * E)) := by
          have : 0 ≤ (6 + 2 * Kd + 1) * (Real.exp (Kd * t) * E) := by positivity
          nlinarith
      _ = (Ka + 1) * (6 + 2 * Kd + 1) * Real.exp (Kd * t) * E := by ring

/-! ### Interpolated histories -/

section History

variable {N : ℕ} [NeZero N]

theorem interpRec_symm {u : Grid N → MetricRec} (hu : IsSymRec u) (y : T3) (μ ν : Fin 4) :
    interpRec u y μ ν = interpRec u y ν μ := by
  have e : comp u μ ν = comp u ν μ := funext fun x => hu x μ ν
  simp only [interpRec, reField_apply, e]

theorem isSymRec_sampleRec_interpRec {M : ℕ} [NeZero M] {u : Grid N → MetricRec}
    (hu : IsSymRec u) : IsSymRec (sampleRec M ⇑(interpRec u)) := fun x μ ν =>
  interpRec_symm hu _ μ ν

/-- Time derivatives of interpolated histories. -/
theorem hasDerivAt_interpRec {u : ℝ → Grid N → MetricRec} {u' : Grid N → MetricRec} {t : ℝ}
    (hu : ∀ x, HasDerivAt (fun τ => u τ x) (u' x) t) (y : T3) :
    HasDerivAt (fun τ => interpRec (u τ) y) (interpRec u' y) t := by
  refine hasDerivAt_reField_time (w := fun τ μ ν => cx (comp (u τ) μ ν)) (fun μ ν x => ?_) y
  have h := hasDerivAt_pi.mp (hasDerivAt_pi.mp (hu x) μ) ν
  exact h.ofReal_comp

theorem hasDerivAt_interpRec_symRec {u : ℝ → Grid N → MetricRec} {u' : Grid N → MetricRec}
    {t : ℝ} (hu : ∀ x (κ : Upper), HasDerivAt (fun τ => u τ x κ.1.1 κ.1.2) (u' x κ.1.1 κ.1.2) t)
    (y : T3) :
    HasDerivAt (fun τ => interpRec (symRec (u τ)) y) (interpRec (symRec u') y) t := by
  refine hasDerivAt_reField_time (w := fun τ μ ν => cx (comp (symRec (u τ)) μ ν))
    (fun μ ν x => ?_) y
  have h := hu x (upperOf μ ν)
  exact h.ofReal_comp

theorem continuous_interpRec_apply (y : T3) :
    Continuous fun u : Grid N → MetricRec => interpRec u y := by
  refine continuous_pi fun μ => continuous_pi fun ν => ?_
  have e : (fun u : Grid N → MetricRec => interpRec u y μ ν) = fun u =>
      (∑ x, ((u x μ ν : ℝ) : ℂ) *
        PeriodicGridSobolev.interp (fun z => if z = x then (1 : ℂ) else 0) y).re := by
    funext u
    simp only [interpRec, reField_apply]
    rw [interp_apply_eq_sum]
    rfl
  rw [e]
  refine Complex.continuous_re.comp (continuous_finset_sum _ fun x _ => ?_)
  exact (Complex.continuous_ofReal.comp ((continuous_apply ν).comp ((continuous_apply μ).comp
    (continuous_apply x)))).mul continuous_const

theorem continuous_symRec : Continuous (symRec (N := N)) :=
  continuous_pi fun x => continuous_pi fun μ => continuous_pi fun ν =>
    (continuous_apply _).comp ((continuous_apply _).comp (continuous_apply x))

end History

theorem prod_succ_bounds {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    1 ≤ (a + 1) * (b + 1) * (c + 1) * (d + 1) ∧ b ≤ (a + 1) * (b + 1) * (c + 1) * (d + 1) ∧
      a * b ≤ (a + 1) * (b + 1) * (c + 1) * (d + 1) ∧
      c * b ≤ (a + 1) * (b + 1) * (c + 1) * (d + 1) ∧
      d * c * b ≤ (a + 1) * (b + 1) * (c + 1) * (d + 1) := by
  have e : (a + 1) * (b + 1) * (c + 1) * (d + 1) = a * b * c * d + a * b * c + a * b * d +
      a * c * d + b * c * d + a * b + a * c + a * d + b * c + b * d + c * d + a + b + c + d + 1 := by
    ring
  have h1 := mul_nonneg ha hb; have h2 := mul_nonneg ha hc; have h3 := mul_nonneg ha hd
  have h4 := mul_nonneg hb hc; have h5 := mul_nonneg hb hd; have h6 := mul_nonneg hc hd
  have h7 := mul_nonneg h1 hc; have h8 := mul_nonneg h1 hd; have h9 := mul_nonneg h2 hd
  have h10 := mul_nonneg h4 hd; have h11 := mul_nonneg h7 hd
  rw [e]
  refine ⟨by linarith, by linarith, by linarith, by linarith [mul_comm c b], ?_⟩
  have : d * c * b = b * c * d := by ring
  rw [this]; linarith

/-! ### The grid Cauchy estimate between two meshes -/

/-- **Two meshes are close** (the core of whole-sequence convergence in `thm:supp-open-einstein`):
for `s ≥ 5` there are mesh-independent `δ, K, C` such that for writer solutions `(q, v)` on the
grid of mesh `h = 1/N` and `(q', v')` on the grid of mesh `h' = 1/N'` over `[0, T]`, both in the top
ball (`‖(q', v')‖_{X^s_{h'}} ≤ ε ≤ δ`), the `h`-samples of the real interpolant of `(q', v')`
satisfy `‖(q - 𝒮_h 𝓘_{h'} q', v - 𝒮_h 𝓘_{h'} v')(t)‖_{X^{s-2}_h} ≤ C e^{Kt}(e₀ + (1 + t)(h + h') ε)`,
`e₀` the same norm at `t = 0`, and the acceleration difference obeys the same bound in
`H^{s-3}_h` (upper components). -/
theorem interp_cauchy_grid (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∃ C ≥ 0, ∀ (N N' : ℕ) [NeZero N] [NeZero N'] (T : ℝ)
      (q v : ℝ → Grid N → MetricRec) (q' v' : ℝ → Grid N' → MetricRec) (ε : ℝ),
      IsWriterSolution T q v → IsWriterSolution T q' v' →
      (∀ t ∈ Set.Icc 0 T, Xnorm s (q t) (v t) ≤ δ) → (∀ t ∈ Set.Icc 0 T, Xnorm s (q' t) (v' t) ≤ ε) →
      ε ≤ δ → ∀ t ∈ Set.Icc 0 T,
        Xnorm (s - 2) (q t - sampleRec N ⇑(interpRec (q' t)))
            (v t - sampleRec N ⇑(interpRec (v' t))) ≤
          C * Real.exp (K * t) * (Xnorm (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
            (v 0 - sampleRec N ⇑(interpRec (v' 0))) + (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)) ∧
        ∀ κ : Upper, PeriodicGridSobolev.sobNorm (s - 3)
          (cx (comp (harmonicWriterAcceleration (q t) (v t) -
            sampleRec N ⇑(interpRec (symRec (harmonicWriterAcceleration (q' t) (v' t))))) κ.1.1 κ.1.2)) ≤
          C * Real.exp (K * t) * (Xnorm (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
            (v 0 - sampleRec N ⇑(interpRec (v' 0))) + (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)) := by
  obtain ⟨δF, hδF, KF, hKF, CF, hCF, hcmp⟩ := comparison_of_force s hs
  obtain ⟨δR, hδR, CR, hCR, hsmall⟩ := interp_row_small s hs
  obtain ⟨δc, hδc, Cc, hCc, hcons⟩ := sampled_row_consistency s (by omega)
  obtain ⟨δmc, hδmc, Cmc, hCmc, hmc⟩ := moser_coefficients (s - 2) (by omega)
  obtain ⟨Cs, hCs, hsamp⟩ := coordSum_sample_le (E := MetricRec) (ι := Σ _ : Fin 4, Fin 4)
    (s - 2) (by omega)
  obtain ⟨Css, hCss, hsn⟩ := sobNorm_sample_le (s - 2) (by omega)
  obtain ⟨Cx, hCx, hXs⟩ := Xnorm_sample_le s (by omega)
  obtain ⟨ρ1, hρ1, hcont1⟩ := continuousOn_accel_history s (by omega)
  set Ct : ℝ := 16 * (Real.sqrt (pc (s + 1)) + Real.sqrt (pc s))
  have hCt : 0 ≤ Ct := by positivity
  set A := PeriodicGridSobolev.Moser.algConst (s - 2)
  have hA := PeriodicGridSobolev.Moser.algConst_pos (s - 2)
  set B : ℝ := (Cx + 1) * (Ct + 1) * (Cs + 1) * (Cmc + 1)
  obtain ⟨hB1, hB0, hBxt, hBst, hBmst⟩ := prod_succ_bounds hCx hCt hCs hCmc
  set δ : ℝ := min (min (min δF δR) ρ1) (min (min δF ρ1) (min δc (min δmc 1))) / B
  have hδ : 0 < δ := by positivity
  set Cf : ℝ := 16 * ((A + 1) * (Cc * Ct + Css * CR))
  refine ⟨δ, hδ, KF, hKF, CF * (1 + Cf), by positivity,
    fun N N' _ _ T q v q' v' ε hsol hsol' hXq hXq' hεδ t ht => ?_⟩
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hε0 : 0 ≤ ε := (Xnorm_nonneg _ _ _).trans (hXq' 0 ⟨le_rfl, hT⟩)
  have hδB : δ * B ≤ min (min (min δF δR) ρ1) (min (min δF ρ1) (min δc (min δmc 1))) := by
    simp only [δ]; rw [div_mul_cancel₀ _ (by positivity)]
  have hεB : ε * B ≤ min (min (min δF δR) ρ1) (min (min δF ρ1) (min δc (min δmc 1))) :=
    (mul_le_mul_of_nonneg_right hεδ (by positivity)).trans hδB
  have hδle : δ ≤ min (min (min δF δR) ρ1) (min (min δF ρ1) (min δc (min δmc 1))) := by
    calc δ ≤ δ * B := le_mul_of_one_le_right hδ.le hB1
      _ ≤ _ := hδB
  -- the interpolated history
  set V' : ℝ → Grid N' → MetricRec := fun τ => symRec (v' τ)
  set A' : ℝ → Grid N' → MetricRec := fun τ => harmonicWriterAcceleration (q' τ) (V' τ)
  set p : ℝ → Grid N → MetricRec := fun τ => sampleRec N ⇑(interpRec (q' τ))
  set w : ℝ → Grid N → MetricRec := fun τ => sampleRec N ⇑(interpRec (V' τ))
  set f : ℝ → Grid N → MetricRec := fun τ =>
    sampleRec N ⇑(interpRec (symRec (A' τ))) - harmonicWriterAcceleration (p τ) (w τ)
  have hV'eq : ∀ τ ∈ Set.Icc 0 T, V' τ = v' τ := fun τ hτ =>
    symRec_of_isSymRec (hsol' τ hτ).2.1
  have hX' : ∀ τ ∈ Set.Icc 0 T, Xnorm s (q' τ) (V' τ) ≤ ε := fun τ hτ => by
    rw [hV'eq τ hτ]; exact hXq' τ hτ
  have hsymV' : ∀ τ, IsSymRec (V' τ) := fun τ => isSymRec_symRec _
  -- the size of the interpolant
  have hct : ∀ τ ∈ Set.Icc 0 T, contTop s (interpRec (q' τ)) (interpRec (V' τ)) ≤ Ct * ε :=
    fun τ hτ => (contTop_interp_le s (hsol' τ hτ).1 (hsymV' τ)).trans
      (mul_le_mul_of_nonneg_left (hX' τ hτ) hCt)
  have hsmallε : ∀ a, (min (min (min δF δR) ρ1) (min (min δF ρ1) (min δc (min δmc 1)))) ≤ a →
      (Cx + 1) * (Ct + 1) * (Cs + 1) * (Cmc + 1) * ε ≤ a := fun a ha => by
    have := hεB.trans ha; simp only [B] at this; linarith
  have hfac : ∀ c : ℝ, 0 ≤ c → c ≤ (Cx + 1) * (Ct + 1) * (Cs + 1) * (Cmc + 1) →
      ∀ a, (min (min (min δF δR) ρ1) (min (min δF ρ1) (min δc (min δmc 1)))) ≤ a → c * ε ≤ a :=
    fun c hc hcB a ha => (mul_le_mul_of_nonneg_right hcB hε0).trans (hsmallε a ha)
  -- sizes of the sampled history
  have hpw : ∀ τ ∈ Set.Icc 0 T, Xnorm s (p τ) (w τ) ≤ min δF ρ1 := by
    intro τ hτ
    refine (hXs N (interpRec (q' τ)) (interpRec (V' τ)) (fun k => (memH_interpRec _ _ k).1)
      (fun k => (memH_interpRec _ _ k).1)).trans ?_
    have h1 := mul_le_mul_of_nonneg_left (hct τ hτ) hCx
    refine h1.trans ?_
    have h2 : Cx * (Ct * ε) = (Cx * Ct) * ε := by ring
    rw [h2]
    exact hfac (Cx * Ct) (by positivity) hBxt _ ((min_le_right _ _).trans (min_le_left _ _))
  -- the force bound
  set F₀ : ℝ := Cf * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)
  have hforce : ∀ τ ∈ Set.Icc 0 T, Fnorm (s - 2) (f τ) ≤ F₀ := by
    intro τ hτ
    have hqs := (hsol' τ hτ).1
    have hctc : contTop s (interpRec (q' τ)) (interpRec (V' τ)) ≤ δc :=
      (hct τ hτ).trans (hfac Ct hCt hB0 _ ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))))
    obtain ⟨ha, hc⟩ := hcons N (interpRec (q' τ)) (interpRec (V' τ)) (interpRec (symRec (A' τ)))
      (interpD (q' τ)) (interpD (V' τ)) (interpDD (q' τ)) (isContJet_interp _ _)
      (fun k => (memH_interpRec _ _ k).1) (fun k => (memH_interpRec _ _ k).1) hctc
    have hXR : Xnorm s (q' τ) (V' τ) ≤ δR :=
      (hX' τ hτ).trans ((le_mul_of_one_le_right hε0 hB1).trans (hεB.trans
        ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))))
    -- the `a⁻¹` coefficient
    have hq2 : PeriodicGridSobolev.Moser.coordSum (s - 2) bM (p τ) ≤ Cs * (Ct * ε) := by
      refine (hsamp N bM (interpRec (q' τ)) (fun k => (memH_interpRec _ _ k).1)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCs
      refine ((ccoordSum_mono (by omega) (fun k => (memH_interpRec (s + 1) _ k).1)).trans ?_)
      exact (le_add_of_nonneg_right (ccoordSum_nonneg _ _ _)).trans (hct τ hτ)
    have hCsCt : Cs * Ct ≤ (Cx + 1) * (Ct + 1) * (Cs + 1) * (Cmc + 1) := hBst
    have hq2δ : PeriodicGridSobolev.Moser.coordSum (s - 2) bM (p τ) ≤ δmc := by
      refine hq2.trans ?_
      rw [show Cs * (Ct * ε) = (Cs * Ct) * ε by ring]
      exact hfac _ (by positivity) hCsCt _ ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))))
    have hq2one : Cmc * PeriodicGridSobolev.Moser.coordSum (s - 2) bM (p τ) ≤ 1 := by
      have h1 := mul_le_mul_of_nonneg_left hq2 hCmc
      have h2 : Cmc * (Cs * (Ct * ε)) ≤ 1 := by
        rw [show Cmc * (Cs * (Ct * ε)) = (Cmc * Cs * Ct) * ε by ring]
        exact hfac _ (by positivity) hBmst _ ((min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _))))
      linarith
    obtain ⟨-, hinv, -, -⟩ := hmc N (p τ) hq2δ
    have hinv1 : PeriodicGridSobolev.sobNorm (s - 2)
        (cx (fun x => (harmA (minkowski + p τ x))⁻¹) - fun _ => (1 : ℂ)) ≤ 1 := hinv.trans hq2one
    have hh : 0 ≤ (N : ℝ)⁻¹ := by positivity
    have hh' : 0 ≤ (N' : ℝ)⁻¹ := by positivity
    refine (lawDiff_Fnorm_le_of_comp_le (s - 2) _
      (M := (A + 1) * (Cc * (N : ℝ)⁻¹ * (Ct * ε) + Css * (CR * (N' : ℝ)⁻¹ * ε)))
      (by positivity) fun κ => ?_).trans ?_
    · obtain ⟨R, hR, hRm, hRs⟩ := hsmall N' (q' τ) (V' τ) hqs (hsymV' τ) hXR κ
      have h1 := hc κ.1.1 κ.1.2
      have hf : f τ = sampleRec N ⇑(interpRec (symRec (A' τ))) -
          harmonicWriterAcceleration (sampleRec N ⇑(interpRec (q' τ)))
            (sampleRec N ⇑(interpRec (V' τ))) := rfl
      rw [← hf] at h1
      have hSR : PeriodicGridSobolev.sobNorm (s - 2) (PeriodicGridSobolev.Sampling.sample N
          (rowF (interpRec (q' τ)) (interpRec (V' τ)) (interpRec (symRec (A' τ))) (interpD (q' τ))
            (interpD (V' τ)) (interpDD (q' τ)) κ.1.1 κ.1.2)) ≤ Css * (CR * (N' : ℝ)⁻¹ * ε) := by
        rw [← hR]
        refine (hsn N R hRm).trans (mul_le_mul_of_nonneg_left (hRs.trans ?_) hCss)
        exact mul_le_mul_of_nonneg_left (hX' τ hτ) (by positivity)
      have hAf : PeriodicGridSobolev.sobNorm (s - 2) (cx (aArr (p τ)) * cx (comp (f τ) κ.1.1 κ.1.2)) ≤
          Cc * (N : ℝ)⁻¹ * (Ct * ε) + Css * (CR * (N' : ℝ)⁻¹ * ε) := by
        have e : cx (aArr (p τ)) * cx (comp (f τ) κ.1.1 κ.1.2) =
            (cx (aArr (p τ)) * cx (comp (f τ) κ.1.1 κ.1.2) -
              PeriodicGridSobolev.Sampling.sample N (rowF (interpRec (q' τ)) (interpRec (V' τ))
                (interpRec (symRec (A' τ))) (interpD (q' τ)) (interpD (V' τ)) (interpDD (q' τ))
                κ.1.1 κ.1.2)) +
            PeriodicGridSobolev.Sampling.sample N (rowF (interpRec (q' τ)) (interpRec (V' τ))
                (interpRec (symRec (A' τ))) (interpD (q' τ)) (interpD (V' τ)) (interpDD (q' τ))
                κ.1.1 κ.1.2) := by abel
        rw [e]
        refine (PeriodicGridSobolev.Moser.sobNorm_add_le _ _ _).trans (add_le_add ?_ hSR)
        exact h1.trans (mul_le_mul_of_nonneg_left (hct τ hτ) (by positivity))
      have e : cx (comp (f τ) κ.1.1 κ.1.2) = cx (fun x => (harmA (minkowski + p τ x))⁻¹) *
          (cx (aArr (p τ)) * cx (comp (f τ) κ.1.1 κ.1.2)) := by
        funext x
        simp only [Pi.mul_apply, cx_apply, aArr]
        have hax := ha x
        simp only [aArr] at hax
        have hax' : ((harmA (minkowski + p τ x) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hax
        push_cast
        field_simp
      rw [e]
      refine (sobNorm_coef_mul_le (s - 2) (by omega) _ _ 1 (by simp) hinv1).trans ?_
      exact mul_le_mul_of_nonneg_left hAf (by positivity)
    · simp only [F₀, Cf]
      have t1 : 0 ≤ 16 * (A + 1) * (Cc * Ct) * ((N' : ℝ)⁻¹ * ε) := by positivity
      have t2 : 0 ≤ 16 * (A + 1) * (Css * CR) * ((N : ℝ)⁻¹ * ε) := by positivity
      linarith
  -- the forced history
  have hpd : ∀ τ ∈ Set.Icc 0 T, ∀ x, HasDerivAt (fun σ => p σ x) (w τ x) τ := by
    intro τ hτ x
    have h := hasDerivAt_interpRec (u := q') (u' := v' τ) (t := τ) (hsol' τ hτ).2.2.1
      (PeriodicGridSobolev.samplePt x)
    simp only [w, sampleRec]
    rw [hV'eq τ hτ]
    exact h
  have hwd : ∀ τ ∈ Set.Icc 0 T, ∀ x (κ : Upper), HasDerivAt (fun σ => w σ x κ.1.1 κ.1.2)
      (harmonicWriterAcceleration (p τ) (w τ) x κ.1.1 κ.1.2 + f τ x κ.1.1 κ.1.2) τ := by
    intro τ hτ x κ
    have h := hasDerivAt_interpRec_symRec (u := v')
      (u' := harmonicWriterAcceleration (q' τ) (v' τ)) (t := τ) (hsol' τ hτ).2.2.2
      (PeriodicGridSobolev.samplePt x)
    have h2 := hasDerivAt_pi.mp (hasDerivAt_pi.mp h κ.1.1) κ.1.2
    refine h2.congr_deriv ?_
    have eA : A' τ = harmonicWriterAcceleration (q' τ) (v' τ) := by
      simp only [A']; rw [hV'eq τ hτ]
    simp only [f, Pi.sub_apply, sampleRec, eA]
    ring
  have hpc : ∀ τ ∈ Set.Icc 0 T, ContinuousAt p τ := fun τ hτ =>
    (hasDerivAt_pi.2 fun x => hpd τ hτ x).continuousAt
  have hV'c : ∀ τ ∈ Set.Icc 0 T, ContinuousAt V' τ := by
    intro τ hτ
    have h : HasDerivAt V' (symRec (harmonicWriterAcceleration (q' τ) (v' τ))) τ := by
      refine hasDerivAt_pi.2 fun x => hasDerivAt_pi.2 fun μ => hasDerivAt_pi.2 fun ν => ?_
      exact (hsol' τ hτ).2.2.2 x (upperOf μ ν)
    exact h.continuousAt
  have hwc : ∀ τ ∈ Set.Icc 0 T, ContinuousAt w τ := by
    intro τ hτ
    refine continuousAt_pi.2 fun x => ?_
    exact ((continuous_interpRec_apply _).continuousAt).comp (hV'c τ hτ)
  have hq'c : ∀ τ ∈ Set.Icc 0 T, ContinuousAt q' τ := fun τ hτ =>
    (hasDerivAt_pi.2 fun x => (hsol' τ hτ).2.2.1 x).continuousAt
  have hfc : ContinuousOn f (Set.Icc 0 T) := by
    have hA'c : ContinuousOn A' (Set.Icc 0 T) :=
      hcont1 N' T q' V' hq'c hV'c (fun τ hτ => (hsol' τ hτ).1) (fun τ hτ =>
        (hX' τ hτ).trans ((le_mul_of_one_le_right hε0 hB1).trans (hεB.trans
          ((min_le_left _ _).trans (min_le_right _ _)))))
    have h1 : ContinuousOn (fun τ => sampleRec N ⇑(interpRec (symRec (A' τ)))) (Set.Icc 0 T) :=
      continuousOn_pi.2 fun x => ((continuous_interpRec_apply _).comp continuous_symRec).comp_continuousOn hA'c
    exact h1.sub (hcont1 N T p w hpc hwc (fun τ hτ => isSymRec_sampleRec_interpRec (hsol' τ hτ).1)
      (fun τ hτ => (hpw τ hτ).trans (min_le_right _ _)))
  have hY : ∀ τ ∈ Set.Icc 0 T, IsSymRec (p τ) ∧ IsSymRec (w τ) ∧
      (∀ x, HasDerivAt (fun σ => p σ x) (w τ x) τ) ∧
      (∀ x (κ : Upper), HasDerivAt (fun σ => w σ x κ.1.1 κ.1.2)
        (harmonicWriterAcceleration (p τ) (w τ) x κ.1.1 κ.1.2 + f τ x κ.1.1 κ.1.2) τ) ∧
      Xnorm s (p τ) (w τ) ≤ δF ∧ Fnorm (s - 2) (f τ) ≤ F₀ := fun τ hτ =>
    ⟨isSymRec_sampleRec_interpRec (hsol' τ hτ).1, isSymRec_sampleRec_interpRec (hsymV' τ),
      hpd τ hτ, hwd τ hτ, (hpw τ hτ).trans (min_le_left _ _), hforce τ hτ⟩
  have hXqF : ∀ τ ∈ Set.Icc 0 T, Xnorm s (q τ) (v τ) ≤ δF := fun τ hτ =>
    (hXq τ hτ).trans (hδle.trans ((min_le_left _ _).trans ((min_le_left _ _).trans
      (min_le_left _ _))))
  obtain ⟨h1, h2⟩ := hcmp N T q v p w f F₀ hsol hXqF hY hfc t ht
  have ew : w t = sampleRec N ⇑(interpRec (v' t)) := by simp only [w]; rw [hV'eq t ht]
  have ew0 : w 0 = sampleRec N ⇑(interpRec (v' 0)) := by
    simp only [w]; rw [hV'eq 0 ⟨le_rfl, hT⟩]
  have hE : 0 ≤ Xnorm (s - 2) (q 0 - p 0) (v 0 - w 0) + (1 + t) * F₀ := by
    have hF : 0 ≤ F₀ := by simp only [F₀, Cf]; positivity
    have h1 : 0 ≤ (1 + t) * F₀ := mul_nonneg (by linarith [ht.1]) hF
    have := Xnorm_nonneg (s - 2) (q 0 - p 0) (v 0 - w 0)
    linarith
  have hfinal : CF * Real.exp (KF * t) * (Xnorm (s - 2) (q 0 - p 0) (v 0 - w 0) + (1 + t) * F₀) ≤
      CF * (1 + Cf) * Real.exp (KF * t) * (Xnorm (s - 2) (q 0 - p 0) (v 0 - w 0) +
        (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)) := by
    have he := Real.exp_pos (KF * t)
    have hz : 0 ≤ (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε) := by
      have : 0 ≤ ((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε := by positivity
      exact mul_nonneg (by linarith [ht.1]) this
    have hx := Xnorm_nonneg (s - 2) (q 0 - p 0) (v 0 - w 0)
    have hCf0 : 0 ≤ Cf := by positivity
    have key : Xnorm (s - 2) (q 0 - p 0) (v 0 - w 0) + (1 + t) * F₀ ≤
        (1 + Cf) * (Xnorm (s - 2) (q 0 - p 0) (v 0 - w 0) +
          (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)) := by
      simp only [F₀]
      have h1 := mul_nonneg hCf0 hx
      have h2 := mul_nonneg hCf0 hz
      have e : (1 + t) * (Cf * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)) =
          Cf * ((1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)) := by ring
      rw [e]
      linarith
    calc CF * Real.exp (KF * t) * (Xnorm (s - 2) (q 0 - p 0) (v 0 - w 0) + (1 + t) * F₀)
        ≤ CF * Real.exp (KF * t) * ((1 + Cf) * (Xnorm (s - 2) (q 0 - p 0) (v 0 - w 0) +
          (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε))) := by gcongr
      _ = _ := by ring
  refine ⟨?_, fun κ => ?_⟩
  · rw [← ew, ← ew0]
    exact h1.trans hfinal
  · have h3 := h2 κ
    have ef : harmonicWriterAcceleration (p t) (w t) + f t =
        sampleRec N ⇑(interpRec (symRec (harmonicWriterAcceleration (q' t) (v' t)))) := by
      simp only [f, A']
      rw [hV'eq t ht]
      abel
    rw [ef] at h3
    rw [← ew0]
    exact h3.trans hfinal

/-! ### The continuum Cauchy estimate between two meshes -/

section ContCauchy

theorem interpRec_sub {N : ℕ} [NeZero N] (u w : Grid N → MetricRec) :
    interpRec (u - w) = interpRec u - interpRec w := by
  ext y μ ν
  have e : cx (comp (u - w) μ ν) = cx (comp u μ ν) - cx (comp w μ ν) := by
    funext x; simp [cx, comp]
  simp only [interpRec, reField_apply, ContinuousMap.sub_apply, Pi.sub_apply, e,
    PeriodicGridSobolev.Sampling.interp_sub, Complex.sub_re]

theorem cmp_sub (F G : C(T3, MetricRec)) (μ ν : Fin 4) : cmp (F - G) μ ν = cmp F μ ν - cmp G μ ν := by
  ext y; simp

theorem reC_cmp (F : C(T3, MetricRec)) (μ ν : Fin 4) : reC (cmp F μ ν) = cmp F μ ν := by
  ext y; simp

theorem reC_sub (F G : CT) : reC (F - G) = reC F - reC G := by
  ext y; simp

/-- The real interpolant of the `h`-samples of a field is `Re 𝒫_h`. -/
theorem cmp_interpRec_sampleRec {N : ℕ} [NeZero N] (F : C(T3, MetricRec)) (μ ν : Fin 4) :
    cmp (interpRec (sampleRec N ⇑F)) μ ν = reC (PeriodicGridSobolev.Sampling.proj N ⇑(cmp F μ ν)) := by
  rw [interpRec, cmp_reField, cx_comp_sampleRec]
  rfl

/-- **The aliasing error of a real interpolant**: for `F ∈ H^{r+1}` (componentwise),
`‖Re 𝒫_h F_{μν} - F_{μν}‖_{H^r} ≤ C h ‖F_{μν}‖_{H^{r+1}}`. -/
theorem sn_alias_le (r : ℕ) (hr : 1 ≤ r) :
    ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (F : C(T3, MetricRec)) (μ ν : Fin 4),
      MemH (r + 1) ⇑(cmp F μ ν) →
      MemH r ⇑(cmp (interpRec (sampleRec N ⇑F)) μ ν - cmp F μ ν) ∧
      sn r ⇑(cmp (interpRec (sampleRec N ⇑F)) μ ν - cmp F μ ν) ≤
        C * (N : ℝ)⁻¹ * sn (r + 1) ⇑(cmp F μ ν) := by
  obtain ⟨Ce, hCe, herr⟩ := PeriodicGridSobolev.Sampling.sampling_error r 1 (by omega)
  refine ⟨Real.sqrt Ce, Real.sqrt_nonneg _, fun N _ F μ ν hF => ?_⟩
  obtain ⟨hEm, hEb⟩ := herr N (cmp F μ ν) hF
  have e : cmp (interpRec (sampleRec N ⇑F)) μ ν - cmp F μ ν =
      reC (PeriodicGridSobolev.Sampling.proj N ⇑(cmp F μ ν) - cmp F μ ν) := by
    rw [cmp_interpRec_sampleRec, reC_sub, reC_cmp]
  rw [e]
  obtain ⟨h1, h2⟩ := memH_reC hEm
  refine ⟨h1, h2.trans ?_⟩
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold sn
  have e2 : Ce * (((N : ℝ) ^ 2) ^ 1)⁻¹ * PeriodicGridSobolev.trigSobSq (r + 1) ⇑(cmp F μ ν) =
      (Real.sqrt Ce * (N : ℝ)⁻¹ * Real.sqrt (PeriodicGridSobolev.trigSobSq (r + 1) ⇑(cmp F μ ν))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hCe, Real.sq_sqrt (trigSobSq_nonneg _ _)]
    field_simp
  rw [e2] at hEb
  calc Real.sqrt (PeriodicGridSobolev.trigSobSq r
        ⇑(PeriodicGridSobolev.Sampling.proj N ⇑(cmp F μ ν) - cmp F μ ν))
      ≤ Real.sqrt ((Real.sqrt Ce * (N : ℝ)⁻¹ *
          Real.sqrt (PeriodicGridSobolev.trigSobSq (r + 1) ⇑(cmp F μ ν))) ^ 2) :=
        Real.sqrt_le_sqrt hEb
    _ = _ := Real.sqrt_sq (by positivity)

/-- **Two meshes are close in the continuum**: under the hypotheses of `interp_cauchy_grid`, the real
interpolants satisfy, componentwise,
`‖𝓘_h q - 𝓘_{h'} q'‖_{H^{s-1}} + ‖𝓘_h v - 𝓘_{h'} v'‖_{H^{s-2}} ≤ C e^{Kt}(e₀ + (1 + t)(h + h')ε)`
and the same for the interpolated accelerations in `H^{s-3}` (upper components). -/
theorem interp_cauchy_cont (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∃ C ≥ 0, ∀ (N N' : ℕ) [NeZero N] [NeZero N'] (T : ℝ)
      (q v : ℝ → Grid N → MetricRec) (q' v' : ℝ → Grid N' → MetricRec) (ε : ℝ),
      IsWriterSolution T q v → IsWriterSolution T q' v' →
      (∀ t ∈ Set.Icc 0 T, Xnorm s (q t) (v t) ≤ δ) → (∀ t ∈ Set.Icc 0 T, Xnorm s (q' t) (v' t) ≤ ε) →
      ε ≤ δ → ∀ t ∈ Set.Icc 0 T, ∀ κ : Upper,
        sn (s - 1) ⇑(cmp (interpRec (q t)) κ.1.1 κ.1.2 - cmp (interpRec (q' t)) κ.1.1 κ.1.2) ≤
          C * Real.exp (K * t) * (Xnorm (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
            (v 0 - sampleRec N ⇑(interpRec (v' 0))) + (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)) ∧
        sn (s - 2) ⇑(cmp (interpRec (v t)) κ.1.1 κ.1.2 - cmp (interpRec (v' t)) κ.1.1 κ.1.2) ≤
          C * Real.exp (K * t) * (Xnorm (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
            (v 0 - sampleRec N ⇑(interpRec (v' 0))) + (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)) ∧
        sn (s - 3) ⇑(cmp (interpRec (harmonicWriterAcceleration (q t) (v t))) κ.1.1 κ.1.2 -
            cmp (interpRec (harmonicWriterAcceleration (q' t) (v' t))) κ.1.1 κ.1.2) ≤
          C * Real.exp (K * t) * (Xnorm (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
            (v 0 - sampleRec N ⇑(interpRec (v' 0))) + (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)) := by
  obtain ⟨δg, hδg, K, hK, Cg, hCg, hgrid⟩ := interp_cauchy_grid s hs
  obtain ⟨δA, hδA, KA, hKA, hacc⟩ := accel_bound s (by omega)
  obtain ⟨Ca1, hCa1, hal1⟩ := sn_alias_le (s - 1) (by omega)
  obtain ⟨Ca2, hCa2, hal2⟩ := sn_alias_le (s - 2) (by omega)
  obtain ⟨Ca3, hCa3, hal3⟩ := sn_alias_le (s - 3) (by omega)
  set P1 := Real.sqrt (pc (s - 1))
  set P2 := Real.sqrt (pc (s - 2))
  set P3 := Real.sqrt (pc (s - 3))
  set Ps := Real.sqrt (pc s)
  set Ps1 := Real.sqrt (pc (s - 1 + 1))
  set Ps2 := Real.sqrt (pc (s - 2 + 1))
  set Ps3 := Real.sqrt (pc (s - 3 + 1))
  set Cfin : ℝ := (P1 + P2 + P3) + (Ca1 * Ps1 + Ca2 * Ps2 + Ca3 * Ps3 * (KA + 1)) + 1
  refine ⟨min δg δA, lt_min hδg hδA, K, hK, Cfin * (Cg + 1), by positivity,
    fun N N' _ _ T q v q' v' ε hsol hsol' hXq hXq' hεδ t ht κ => ?_⟩
  have hεg : ε ≤ δg := hεδ.trans (min_le_left _ _)
  have hXqg : ∀ τ ∈ Set.Icc 0 T, Xnorm s (q τ) (v τ) ≤ δg := fun τ hτ =>
    (hXq τ hτ).trans (min_le_left _ _)
  obtain ⟨hG1, hG2⟩ := hgrid N N' T q v q' v' ε hsol hsol' hXqg hXq' hεg t ht
  set E := Cg * Real.exp (K * t) * (Xnorm (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
    (v 0 - sampleRec N ⇑(interpRec (v' 0))) + (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε))
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hε0 : 0 ≤ ε := (Xnorm_nonneg _ _ _).trans (hXq' 0 ⟨le_rfl, hT⟩)
  obtain ⟨hqs, hvs, -, -⟩ := hsol t ht
  obtain ⟨hqs', hvs', -, -⟩ := hsol' t ht
  set p := sampleRec N ⇑(interpRec (q' t))
  set w := sampleRec N ⇑(interpRec (v' t))
  have hps : IsSymRec p := isSymRec_sampleRec_interpRec hqs'
  have hws : IsSymRec w := isSymRec_sampleRec_interpRec hvs'
  have hE0 : 0 ≤ Real.exp (K * t) * (Xnorm (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
      (v 0 - sampleRec N ⇑(interpRec (v' 0))) + (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)) := by
    have := Xnorm_nonneg (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
      (v 0 - sampleRec N ⇑(interpRec (v' 0)))
    have : 0 ≤ (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε) :=
      mul_nonneg (by linarith [ht.1]) (by positivity)
    positivity
  have hhε : (N : ℝ)⁻¹ * ε ≤ Real.exp (K * t) * (Xnorm (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
      (v 0 - sampleRec N ⇑(interpRec (v' 0))) + (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)) := by
    have hexp := Real.one_le_exp (mul_nonneg hK ht.1)
    have h1 : (N : ℝ)⁻¹ * ε ≤ (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε) := by
      have h2 : 0 ≤ (N' : ℝ)⁻¹ * ε := by positivity
      have h3 : 0 ≤ t * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε) := mul_nonneg ht.1 (by positivity)
      nlinarith
    have hx := Xnorm_nonneg (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
      (v 0 - sampleRec N ⇑(interpRec (v' 0)))
    have h4 : (N : ℝ)⁻¹ * ε ≤ Xnorm (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
        (v 0 - sampleRec N ⇑(interpRec (v' 0))) + (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε) := by
      linarith
    have h5 : 0 ≤ Xnorm (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
        (v 0 - sampleRec N ⇑(interpRec (v' 0))) + (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε) :=
      le_trans (by positivity) h4
    nlinarith
  set D := Real.exp (K * t) * (Xnorm (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
      (v 0 - sampleRec N ⇑(interpRec (v' 0))) + (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε))
  have hD0 : 0 ≤ D := hE0
  have hfinal : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ≤ Cfin → b ≤ Cfin →
      a * (Cg * D) + b * ((N : ℝ)⁻¹ * ε) ≤ Cfin * (Cg + 1) * Real.exp (K * t) *
        (Xnorm (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
          (v 0 - sampleRec N ⇑(interpRec (v' 0))) + (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)) := by
    intro a b ha hb haC hbC
    have h1 : a * (Cg * D) ≤ Cfin * (Cg * D) := mul_le_mul_of_nonneg_right haC (by positivity)
    have h2 : b * ((N : ℝ)⁻¹ * ε) ≤ Cfin * D :=
      mul_le_mul hbC hhε (by positivity) (by positivity)
    have e : Cfin * (Cg + 1) * Real.exp (K * t) *
        (Xnorm (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
          (v 0 - sampleRec N ⇑(interpRec (v' 0))) + (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)) =
        Cfin * (Cg * D) + Cfin * D := by simp only [D]; ring
    rw [e]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · -- position
    have e : cmp (interpRec (q t)) κ.1.1 κ.1.2 - cmp (interpRec (q' t)) κ.1.1 κ.1.2 =
        cmp (interpRec (q t - p)) κ.1.1 κ.1.2 +
          (cmp (interpRec p) κ.1.1 κ.1.2 - cmp (interpRec (q' t)) κ.1.1 κ.1.2) := by
      rw [interpRec_sub, cmp_sub]; abel
    rw [e]
    obtain ⟨hm1, hs1⟩ := memH_cmp_reField (s - 1) (fun μ ν => cx (comp (q t - p) μ ν)) κ.1.1 κ.1.2
    have hq'm : MemH (s - 1 + 1) ⇑(cmp (interpRec (q' t)) κ.1.1 κ.1.2) := by
      exact (memH_cmp_reField _ (fun μ ν => cx (comp _ μ ν)) _ _).1
    obtain ⟨hm2, hs2⟩ := hal1 N (interpRec (q' t)) κ.1.1 κ.1.2 hq'm
    refine (sn_add_le' hm1 hm2).trans ?_
    have b1 : sn (s - 1) ⇑(cmp (interpRec (q t - p)) κ.1.1 κ.1.2) ≤ P1 * (Cg * D) := by
      refine hs1.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
      refine (sobNorm_q_le (s - 2) (isSymRec_sub hqs hps) (v t - w) _ _ (by omega)).trans ?_
      exact hG1.trans (le_of_eq (by simp only [D]; ring))
    have b2 : sn (s - 1) ⇑(cmp (interpRec p) κ.1.1 κ.1.2 - cmp (interpRec (q' t)) κ.1.1 κ.1.2) ≤
        Ca1 * Ps1 * ((N : ℝ)⁻¹ * ε) := by
      refine hs2.trans ?_
      have h3 : sn (s - 1 + 1) ⇑(cmp (interpRec (q' t)) κ.1.1 κ.1.2) ≤ Ps1 * ε := by
        refine (memH_cmp_reField _ (fun μ ν => cx (comp _ μ ν)) _ _).2.trans
          (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
        exact (sobNorm_q_le s hqs' (v' t) _ _ (by omega)).trans (hXq' t ht)
      calc Ca1 * (N : ℝ)⁻¹ * sn (s - 1 + 1) ⇑(cmp (interpRec (q' t)) κ.1.1 κ.1.2)
          ≤ Ca1 * (N : ℝ)⁻¹ * (Ps1 * ε) := by gcongr
        _ = Ca1 * Ps1 * ((N : ℝ)⁻¹ * ε) := by ring
    refine (add_le_add b1 b2).trans (hfinal _ _ (by positivity) (by positivity) ?_ ?_)
    · simp only [Cfin]
      have := Real.sqrt_nonneg (pc (s - 1)); have := Real.sqrt_nonneg (pc (s - 2))
      have := Real.sqrt_nonneg (pc (s - 3))
      have : 0 ≤ Ca1 * Ps1 + Ca2 * Ps2 + Ca3 * Ps3 * (KA + 1) := by positivity
      linarith
    · simp only [Cfin]
      have := Real.sqrt_nonneg (pc (s - 1)); have := Real.sqrt_nonneg (pc (s - 2))
      have := Real.sqrt_nonneg (pc (s - 3))
      have := mul_nonneg hCa1 (Real.sqrt_nonneg (pc (s - 1 + 1)))
      have := mul_nonneg hCa2 (Real.sqrt_nonneg (pc (s - 2 + 1)))
      have := mul_nonneg (mul_nonneg hCa3 (Real.sqrt_nonneg (pc (s - 3 + 1)))) (by linarith : (0:ℝ) ≤ KA + 1)
      linarith
  · -- velocity
    have e : cmp (interpRec (v t)) κ.1.1 κ.1.2 - cmp (interpRec (v' t)) κ.1.1 κ.1.2 =
        cmp (interpRec (v t - w)) κ.1.1 κ.1.2 +
          (cmp (interpRec w) κ.1.1 κ.1.2 - cmp (interpRec (v' t)) κ.1.1 κ.1.2) := by
      rw [interpRec_sub, cmp_sub]; abel
    rw [e]
    obtain ⟨hm1, hs1⟩ := memH_cmp_reField (s - 2) (fun μ ν => cx (comp (v t - w) μ ν)) κ.1.1 κ.1.2
    have hv'm : MemH (s - 2 + 1) ⇑(cmp (interpRec (v' t)) κ.1.1 κ.1.2) := by
      exact (memH_cmp_reField _ (fun μ ν => cx (comp _ μ ν)) _ _).1
    obtain ⟨hm2, hs2⟩ := hal2 N (interpRec (v' t)) κ.1.1 κ.1.2 hv'm
    refine (sn_add_le' hm1 hm2).trans ?_
    have b1 : sn (s - 2) ⇑(cmp (interpRec (v t - w)) κ.1.1 κ.1.2) ≤ P2 * (Cg * D) := by
      refine hs1.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
      refine (sobNorm_v_le (s - 2) (q t - p) (isSymRec_sub hvs hws) _ _ le_rfl).trans ?_
      exact hG1.trans (le_of_eq (by simp only [D]; ring))
    have b2 : sn (s - 2) ⇑(cmp (interpRec w) κ.1.1 κ.1.2 - cmp (interpRec (v' t)) κ.1.1 κ.1.2) ≤
        Ca2 * Ps2 * ((N : ℝ)⁻¹ * ε) := by
      refine hs2.trans ?_
      have h3 : sn (s - 2 + 1) ⇑(cmp (interpRec (v' t)) κ.1.1 κ.1.2) ≤ Ps2 * ε := by
        refine (memH_cmp_reField _ (fun μ ν => cx (comp _ μ ν)) _ _).2.trans
          (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
        exact (sobNorm_v_le s (q' t) hvs' _ _ (by omega)).trans (hXq' t ht)
      calc Ca2 * (N : ℝ)⁻¹ * sn (s - 2 + 1) ⇑(cmp (interpRec (v' t)) κ.1.1 κ.1.2)
          ≤ Ca2 * (N : ℝ)⁻¹ * (Ps2 * ε) := by gcongr
        _ = Ca2 * Ps2 * ((N : ℝ)⁻¹ * ε) := by ring
    refine (add_le_add b1 b2).trans (hfinal _ _ (by positivity) (by positivity) ?_ ?_)
    · simp only [Cfin]
      have := Real.sqrt_nonneg (pc (s - 1)); have := Real.sqrt_nonneg (pc (s - 2))
      have := Real.sqrt_nonneg (pc (s - 3))
      have : 0 ≤ Ca1 * Ps1 + Ca2 * Ps2 + Ca3 * Ps3 * (KA + 1) := by positivity
      linarith
    · simp only [Cfin]
      have := Real.sqrt_nonneg (pc (s - 1)); have := Real.sqrt_nonneg (pc (s - 2))
      have := Real.sqrt_nonneg (pc (s - 3))
      have := mul_nonneg hCa1 (Real.sqrt_nonneg (pc (s - 1 + 1)))
      have := mul_nonneg hCa2 (Real.sqrt_nonneg (pc (s - 2 + 1)))
      have := mul_nonneg (mul_nonneg hCa3 (Real.sqrt_nonneg (pc (s - 3 + 1)))) (by linarith : (0:ℝ) ≤ KA + 1)
      linarith
  · -- acceleration
    set A := harmonicWriterAcceleration (q t) (v t)
    set A' := harmonicWriterAcceleration (q' t) (v' t)
    set S := sampleRec N ⇑(interpRec (symRec A'))
    have eA : cmp (interpRec A) κ.1.1 κ.1.2 = cmp (interpRec (symRec A)) κ.1.1 κ.1.2 := by
      ext y; simp [interpRec, cmp_reField, comp_symRec_eq, upperOf_upper]
    have eA' : cmp (interpRec A') κ.1.1 κ.1.2 = cmp (interpRec (symRec A')) κ.1.1 κ.1.2 := by
      ext y; simp [interpRec, cmp_reField, comp_symRec_eq, upperOf_upper]
    have e : cmp (interpRec A) κ.1.1 κ.1.2 - cmp (interpRec A') κ.1.1 κ.1.2 =
        cmp (interpRec (A - S)) κ.1.1 κ.1.2 +
          (cmp (interpRec S) κ.1.1 κ.1.2 - cmp (interpRec (symRec A')) κ.1.1 κ.1.2) := by
      rw [eA', interpRec_sub, cmp_sub]; abel
    rw [e]
    obtain ⟨hm1, hs1⟩ := memH_cmp_reField (s - 3) (fun μ ν => cx (comp (A - S) μ ν)) κ.1.1 κ.1.2
    have hAm : MemH (s - 3 + 1) ⇑(cmp (interpRec (symRec A')) κ.1.1 κ.1.2) := by
      exact (memH_cmp_reField _ (fun μ ν => cx (comp _ μ ν)) _ _).1
    obtain ⟨hm2, hs2⟩ := hal3 N (interpRec (symRec A')) κ.1.1 κ.1.2 hAm
    refine (sn_add_le' hm1 hm2).trans ?_
    have b1 : sn (s - 3) ⇑(cmp (interpRec (A - S)) κ.1.1 κ.1.2) ≤ P3 * (Cg * D) :=
      hs1.trans (mul_le_mul_of_nonneg_left ((hG2 κ).trans (le_of_eq (by simp only [D]; ring)))
        (Real.sqrt_nonneg _))
    have b2 : sn (s - 3) ⇑(cmp (interpRec S) κ.1.1 κ.1.2 - cmp (interpRec (symRec A')) κ.1.1 κ.1.2) ≤
        Ca3 * Ps3 * (KA + 1) * ((N : ℝ)⁻¹ * ε) := by
      refine hs2.trans ?_
      have h3 : sn (s - 3 + 1) ⇑(cmp (interpRec (symRec A')) κ.1.1 κ.1.2) ≤ Ps3 * ((KA + 1) * ε) := by
        refine (memH_cmp_reField _ (fun μ ν => cx (comp _ μ ν)) _ _).2.trans
          (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
        rw [comp_symRec_eq]
        have hle : s - 3 + 1 ≤ s - 1 := by omega
        refine (PeriodicGridSobolev.Moser.sobNorm_mono hle _).trans ?_
        refine (hacc N' (q' t) (v' t) hqs' hvs'
          ((hXq' t ht).trans (hεδ.trans (min_le_right _ _))) _ _).trans ?_
        have := hXq' t ht
        nlinarith [Xnorm_nonneg s (q' t) (v' t)]
      calc Ca3 * (N : ℝ)⁻¹ * sn (s - 3 + 1) ⇑(cmp (interpRec (symRec A')) κ.1.1 κ.1.2)
          ≤ Ca3 * (N : ℝ)⁻¹ * (Ps3 * ((KA + 1) * ε)) := by gcongr
        _ = Ca3 * Ps3 * (KA + 1) * ((N : ℝ)⁻¹ * ε) := by ring
    refine (add_le_add b1 b2).trans (hfinal _ _ (by positivity) (by positivity) ?_ ?_)
    · simp only [Cfin]
      have := Real.sqrt_nonneg (pc (s - 1)); have := Real.sqrt_nonneg (pc (s - 2))
      have := Real.sqrt_nonneg (pc (s - 3))
      have : 0 ≤ Ca1 * Ps1 + Ca2 * Ps2 + Ca3 * Ps3 * (KA + 1) := by positivity
      linarith
    · simp only [Cfin]
      have := Real.sqrt_nonneg (pc (s - 1)); have := Real.sqrt_nonneg (pc (s - 2))
      have := Real.sqrt_nonneg (pc (s - 3))
      have := mul_nonneg hCa1 (Real.sqrt_nonneg (pc (s - 1 + 1)))
      have := mul_nonneg hCa2 (Real.sqrt_nonneg (pc (s - 2 + 1)))
      have := mul_nonneg (mul_nonneg hCa3 (Real.sqrt_nonneg (pc (s - 3 + 1)))) (by linarith : (0:ℝ) ≤ KA + 1)
      linarith

end ContCauchy

/-! ### Sampled continuum initial data -/

/-- The initial mismatch of two meshes started from samples of the same continuum data is `O(h')`:
`‖𝒮_h(Q₀ - 𝓘_{h'}𝒮_{h'}Q₀), 𝒮_h(V₀ - 𝓘_{h'}𝒮_{h'}V₀)‖_{X^{s-2}_h} ≤ C h' ‖(Q₀, V₀)‖_top`. -/
theorem init_mismatch_le (s : ℕ) (hs : 5 ≤ s) :
    ∃ C ≥ 0, ∀ (N N' : ℕ) [NeZero N] [NeZero N'] (Q₀ V₀ : C(T3, MetricRec)),
      (∀ k, MemH (s + 1) ⇑(ccoord bM Q₀ k)) → (∀ k, MemH s ⇑(ccoord bM V₀ k)) →
      Xnorm (s - 2) (sampleRec N ⇑Q₀ - sampleRec N ⇑(interpRec (sampleRec N' ⇑Q₀)))
        (sampleRec N ⇑V₀ - sampleRec N ⇑(interpRec (sampleRec N' ⇑V₀))) ≤
        C * (N' : ℝ)⁻¹ * contTop s Q₀ V₀ := by
  obtain ⟨C1, hC1, hs1⟩ := sobNorm_sample_le (s - 2 + 1) (by omega)
  obtain ⟨C2, hC2, hs2⟩ := sobNorm_sample_le (s - 2) (by omega)
  obtain ⟨Ca1, hCa1, hal1⟩ := sn_alias_le (s - 2 + 1) (by omega)
  obtain ⟨Ca2, hCa2, hal2⟩ := sn_alias_le (s - 2) (by omega)
  refine ⟨16 * (C1 * Ca1 + C2 * Ca2), by positivity, fun N N' _ _ Q₀ V₀ hQ hV => ?_⟩
  refine (Xnorm_le_sum (s - 2) _ _).trans ?_
  set X := contTop s Q₀ V₀
  have hX0 : 0 ≤ X := contTop_nonneg _ _ _
  have hterm : ∀ κ : Upper, PeriodicGridSobolev.sobNorm (s - 2 + 1)
      (cx (comp (sampleRec N ⇑Q₀ - sampleRec N ⇑(interpRec (sampleRec N' ⇑Q₀))) κ.1.1 κ.1.2)) +
      PeriodicGridSobolev.sobNorm (s - 2)
      (cx (comp (sampleRec N ⇑V₀ - sampleRec N ⇑(interpRec (sampleRec N' ⇑V₀))) κ.1.1 κ.1.2)) ≤
      (C1 * Ca1 + C2 * Ca2) * ((N' : ℝ)⁻¹ * X) := by
    intro κ
    have eQ : cx (comp (sampleRec N ⇑Q₀ - sampleRec N ⇑(interpRec (sampleRec N' ⇑Q₀))) κ.1.1 κ.1.2) =
        PeriodicGridSobolev.Sampling.sample N
          ⇑(-(cmp (interpRec (sampleRec N' ⇑Q₀)) κ.1.1 κ.1.2 - cmp Q₀ κ.1.1 κ.1.2)) := by
      funext x; simp [cx, comp, sampleRec, PeriodicGridSobolev.Sampling.sample]
    have eV : cx (comp (sampleRec N ⇑V₀ - sampleRec N ⇑(interpRec (sampleRec N' ⇑V₀))) κ.1.1 κ.1.2) =
        PeriodicGridSobolev.Sampling.sample N
          ⇑(-(cmp (interpRec (sampleRec N' ⇑V₀)) κ.1.1 κ.1.2 - cmp V₀ κ.1.1 κ.1.2)) := by
      funext x; simp [cx, comp, sampleRec, PeriodicGridSobolev.Sampling.sample]
    rw [eQ, eV]
    have hQm : MemH (s - 2 + 1 + 1) ⇑(cmp Q₀ κ.1.1 κ.1.2) :=
      memH_mono (by omega) (memH_cmp hQ κ.1.1 κ.1.2)
    have hVm : MemH (s - 2 + 1) ⇑(cmp V₀ κ.1.1 κ.1.2) :=
      memH_mono (by omega) (memH_cmp hV κ.1.1 κ.1.2)
    obtain ⟨hm1, hb1⟩ := hal1 N' Q₀ κ.1.1 κ.1.2 hQm
    obtain ⟨hm2, hb2⟩ := hal2 N' V₀ κ.1.1 κ.1.2 hVm
    have a1 := hs1 N _ (memH_neg hm1)
    have a2 := hs2 N _ (memH_neg hm2)
    rw [sn_neg] at a1 a2
    have c1 : sn (s - 2 + 1 + 1) ⇑(cmp Q₀ κ.1.1 κ.1.2) ≤ X := by
      refine (sn_mono' (by omega) (memH_cmp hQ κ.1.1 κ.1.2)).trans ?_
      exact (sn_cmp_le_ccoordSum _ _ _ _).trans (le_add_of_nonneg_right (ccoordSum_nonneg _ _ _))
    have c2 : sn (s - 2 + 1) ⇑(cmp V₀ κ.1.1 κ.1.2) ≤ X := by
      refine (sn_mono' (by omega) (memH_cmp hV κ.1.1 κ.1.2)).trans ?_
      exact (sn_cmp_le_ccoordSum _ _ _ _).trans (le_add_of_nonneg_left (ccoordSum_nonneg _ _ _))
    have d1 : C1 * sn (s - 2 + 1) ⇑(cmp (interpRec (sampleRec N' ⇑Q₀)) κ.1.1 κ.1.2 -
        cmp Q₀ κ.1.1 κ.1.2) ≤ C1 * (Ca1 * (N' : ℝ)⁻¹ * X) :=
      mul_le_mul_of_nonneg_left (hb1.trans (mul_le_mul_of_nonneg_left c1 (by positivity))) hC1
    have d2 : C2 * sn (s - 2) ⇑(cmp (interpRec (sampleRec N' ⇑V₀)) κ.1.1 κ.1.2 -
        cmp V₀ κ.1.1 κ.1.2) ≤ C2 * (Ca2 * (N' : ℝ)⁻¹ * X) :=
      mul_le_mul_of_nonneg_left (hb2.trans (mul_le_mul_of_nonneg_left c2 (by positivity))) hC2
    have e : (C1 * Ca1 + C2 * Ca2) * ((N' : ℝ)⁻¹ * X) =
        C1 * (Ca1 * (N' : ℝ)⁻¹ * X) + C2 * (Ca2 * (N' : ℝ)⁻¹ * X) := by ring
    rw [e]
    exact add_le_add (a1.trans d1) (a2.trans d2)
  calc ∑ κ : Upper, (PeriodicGridSobolev.sobNorm (s - 2 + 1)
        (cx (comp (sampleRec N ⇑Q₀ - sampleRec N ⇑(interpRec (sampleRec N' ⇑Q₀))) κ.1.1 κ.1.2)) +
        PeriodicGridSobolev.sobNorm (s - 2)
        (cx (comp (sampleRec N ⇑V₀ - sampleRec N ⇑(interpRec (sampleRec N' ⇑V₀))) κ.1.1 κ.1.2)))
      ≤ ∑ _κ : Upper, (C1 * Ca1 + C2 * Ca2) * ((N' : ℝ)⁻¹ * X) := sum_le_sum fun κ _ => hterm κ
    _ = (Fintype.card Upper : ℝ) * ((C1 * Ca1 + C2 * Ca2) * ((N' : ℝ)⁻¹ * X)) := by simp
    _ ≤ 16 * ((C1 * Ca1 + C2 * Ca2) * ((N' : ℝ)⁻¹ * X)) :=
        mul_le_mul_of_nonneg_right card_upper_le (by positivity)
    _ = 16 * (C1 * Ca1 + C2 * Ca2) * (N' : ℝ)⁻¹ * X := by ring

/-- **Whole-sequence Cauchy property of the interpolated writer solutions** (the core of
`thm:supp-open-einstein`, existence half): for `s ≥ 5` there are mesh-independent `δ, K, C` such
that any two writer solutions on meshes `h = 1/N`, `h' = 1/N'` over `[0, T]`, started from the
samples of the same continuum data `(Q₀, V₀)` and staying in the top ball of size `ε ≤ δ`
(with `‖(Q₀, V₀)‖_top ≤ ε`), have real interpolants with
`‖𝓘_h q - 𝓘_{h'} q'‖_{H^{s-1}} + ‖𝓘_h v - 𝓘_{h'} v'‖_{H^{s-2}} + ‖𝓘_h q_tt - 𝓘_{h'} q'_tt‖_{H^{s-3}}
  ≤ C e^{Kt}(1 + t)(h + h') ε` (each upper component). -/
theorem interp_cauchy (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∃ C ≥ 0, ∀ (N N' : ℕ) [NeZero N] [NeZero N'] (T : ℝ)
      (q v : ℝ → Grid N → MetricRec) (q' v' : ℝ → Grid N' → MetricRec)
      (Q₀ V₀ : C(T3, MetricRec)) (ε : ℝ),
      IsWriterSolution T q v → IsWriterSolution T q' v' →
      q 0 = sampleRec N ⇑Q₀ → v 0 = sampleRec N ⇑V₀ →
      q' 0 = sampleRec N' ⇑Q₀ → v' 0 = sampleRec N' ⇑V₀ →
      (∀ k, MemH (s + 1) ⇑(ccoord bM Q₀ k)) → (∀ k, MemH s ⇑(ccoord bM V₀ k)) →
      contTop s Q₀ V₀ ≤ ε →
      (∀ t ∈ Set.Icc 0 T, Xnorm s (q t) (v t) ≤ ε) → (∀ t ∈ Set.Icc 0 T, Xnorm s (q' t) (v' t) ≤ ε) →
      ε ≤ δ → ∀ t ∈ Set.Icc 0 T, ∀ κ : Upper,
        sn (s - 1) ⇑(cmp (interpRec (q t)) κ.1.1 κ.1.2 - cmp (interpRec (q' t)) κ.1.1 κ.1.2) ≤
          C * Real.exp (K * t) * ((1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)) ∧
        sn (s - 2) ⇑(cmp (interpRec (v t)) κ.1.1 κ.1.2 - cmp (interpRec (v' t)) κ.1.1 κ.1.2) ≤
          C * Real.exp (K * t) * ((1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)) ∧
        sn (s - 3) ⇑(cmp (interpRec (harmonicWriterAcceleration (q t) (v t))) κ.1.1 κ.1.2 -
            cmp (interpRec (harmonicWriterAcceleration (q' t) (v' t))) κ.1.1 κ.1.2) ≤
          C * Real.exp (K * t) * ((1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)) := by
  obtain ⟨δc, hδc, K, hK, Cc, hCc, hcc⟩ := interp_cauchy_cont s hs
  obtain ⟨Ci, hCi, hinit⟩ := init_mismatch_le s hs
  refine ⟨δc, hδc, K, hK, Cc * (Ci + 1), by positivity,
    fun N N' _ _ T q v q' v' Q₀ V₀ ε hsol hsol' hq0 hv0 hq0' hv0' hQ hV hX0 hXq hXq' hεδ t ht κ => ?_⟩
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hε0 : 0 ≤ ε := (contTop_nonneg _ _ _).trans hX0
  have h := hcc N N' T q v q' v' ε hsol hsol' (fun τ hτ => (hXq τ hτ).trans hεδ) hXq' hεδ t ht κ
  have he0 : Xnorm (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
      (v 0 - sampleRec N ⇑(interpRec (v' 0))) ≤ Ci * ((1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)) := by
    rw [hq0, hv0, hq0', hv0']
    refine (hinit N N' Q₀ V₀ hQ hV).trans ?_
    have h1 : Ci * (N' : ℝ)⁻¹ * contTop s Q₀ V₀ ≤ Ci * ((N' : ℝ)⁻¹ * ε) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX0 (by positivity)) hCi
    have h2 : (N' : ℝ)⁻¹ * ε ≤ (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε) := by
      have a1 : 0 ≤ (N : ℝ)⁻¹ * ε := by positivity
      have a2 : 0 ≤ t * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε) := mul_nonneg ht.1 (by positivity)
      have e : (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε) =
          (N : ℝ)⁻¹ * ε + (N' : ℝ)⁻¹ * ε + t * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε) := by ring
      rw [e]; linarith
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hCi)
  set R := (1 + t) * (((N : ℝ)⁻¹ + (N' : ℝ)⁻¹) * ε)
  have hR0 : 0 ≤ R := mul_nonneg (by linarith [ht.1]) (by positivity)
  have hexp := Real.exp_pos (K * t)
  have hbound : Cc * Real.exp (K * t) * (Xnorm (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
      (v 0 - sampleRec N ⇑(interpRec (v' 0))) + R) ≤ Cc * (Ci + 1) * Real.exp (K * t) * R := by
    have h1 : Xnorm (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
        (v 0 - sampleRec N ⇑(interpRec (v' 0))) + R ≤ (Ci + 1) * R := by
      have := he0; linarith
    calc Cc * Real.exp (K * t) * (Xnorm (s - 2) (q 0 - sampleRec N ⇑(interpRec (q' 0)))
          (v 0 - sampleRec N ⇑(interpRec (v' 0))) + R)
        ≤ Cc * Real.exp (K * t) * ((Ci + 1) * R) := by gcongr
      _ = Cc * (Ci + 1) * Real.exp (K * t) * R := by ring
  exact ⟨h.1.trans hbound, h.2.1.trans hbound, h.2.2.trans hbound⟩

/-! ### Passing to the limit -/

/-- **Fatou for uniformly convergent sequences**: if `G_m → F` uniformly, `G_m ∈ H^r` with
`‖G_m‖²_{H^r} ≤ B_m → B`, then `F ∈ H^r` and `‖F‖²_{H^r} ≤ B`. -/
theorem trigSobSq_le_of_tendsto (r : ℕ) {G : ℕ → CT} {F : CT} (hG : Tendsto G atTop (𝓝 F))
    {B : ℕ → ℝ} {B₀ : ℝ} (hB : Tendsto B atTop (𝓝 B₀)) (hGm : ∀ m, MemH r ⇑(G m))
    (h : ∀ m, PeriodicGridSobolev.trigSobSq r ⇑(G m) ≤ B m) :
    MemH r ⇑F ∧ PeriodicGridSobolev.trigSobSq r ⇑F ≤ B₀ := by
  have hfin : ∀ S : Finset (Fin 3 → ℤ),
      ∑ n ∈ S, PeriodicGridSobolev.trigWeight r n * ‖mFourierCoeff ⇑F n‖ ^ 2 ≤ B₀ := by
    intro S
    have hlim : Tendsto (fun m => ∑ n ∈ S, PeriodicGridSobolev.trigWeight r n *
        ‖mFourierCoeff ⇑(G m) n‖ ^ 2) atTop
        (𝓝 (∑ n ∈ S, PeriodicGridSobolev.trigWeight r n * ‖mFourierCoeff ⇑F n‖ ^ 2)) := by
      refine tendsto_finsetSum _ fun n _ => ?_
      have hc : Tendsto (fun m => mFourierCoeff ⇑(G m) n) atTop (𝓝 (mFourierCoeff ⇑F n)) :=
        ((fcL n).continuous.tendsto F).comp hG
      exact (hc.norm.pow 2).const_mul _
    refine le_of_tendsto_of_tendsto' hlim hB fun m => ?_
    refine le_trans ?_ (h m)
    exact (hGm m).sum_le_tsum S fun n _ =>
      mul_nonneg (PeriodicGridSobolev.Sampling.trigWeight_nonneg _ _) (sq_nonneg _)
  have hnn : ∀ n, 0 ≤ PeriodicGridSobolev.trigWeight r n * ‖mFourierCoeff ⇑F n‖ ^ 2 := fun n =>
    mul_nonneg (PeriodicGridSobolev.Sampling.trigWeight_nonneg _ _) (sq_nonneg _)
  have hs : MemH r ⇑F := summable_of_sum_le hnn hfin
  exact ⟨hs, tsum_le_of_sum_le' (by simpa using hfin ∅) hfin⟩

theorem sn_le_of_tendsto (r : ℕ) {G : ℕ → CT} {F : CT} (hG : Tendsto G atTop (𝓝 F))
    {b : ℕ → ℝ} {b₀ : ℝ} (hb : Tendsto b atTop (𝓝 b₀)) (hb0 : ∀ m, 0 ≤ b m)
    (hGm : ∀ m, MemH r ⇑(G m)) (h : ∀ m, sn r ⇑(G m) ≤ b m) : MemH r ⇑F ∧ sn r ⇑F ≤ b₀ := by
  have hb₀ : 0 ≤ b₀ := ge_of_tendsto' hb hb0
  obtain ⟨h1, h2⟩ := trigSobSq_le_of_tendsto r hG (hb.pow 2) hGm fun m => by
    rw [← sn_sq]; exact pow_le_pow_left₀ (sn_nonneg _ _) (h m) 2
  refine ⟨h1, ?_⟩
  unfold sn
  rw [← Real.sqrt_sq hb₀]
  exact Real.sqrt_le_sqrt h2

theorem norm_cmp_sub_le (F G : C(T3, MetricRec)) (μ ν : Fin 4) :
    ‖cmp F μ ν - cmp G μ ν‖ ≤ ‖F - G‖ := by
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun y => ?_
  simp only [ContinuousMap.sub_apply, cmp_apply]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have h1 : |F y μ ν - G y μ ν| ≤ ‖(F - G) y‖ := by
    have := norm_le_pi_norm ((F - G) y μ) ν
    have := norm_le_pi_norm ((F - G) y) μ
    simp only [ContinuousMap.sub_apply, Pi.sub_apply, Real.norm_eq_abs] at *
    linarith
  exact h1.trans ((F - G).norm_coe_le_norm y)

theorem tendsto_cmp {F : ℕ → C(T3, MetricRec)} {F₀ : C(T3, MetricRec)}
    (h : Tendsto F atTop (𝓝 F₀)) (μ ν : Fin 4) :
    Tendsto (fun m => cmp (F m) μ ν) atTop (𝓝 (cmp F₀ μ ν)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  exact squeeze_zero (fun _ => norm_nonneg _) (fun m => norm_cmp_sub_le _ _ μ ν) h

/-- The sup distance of two symmetric record fields is controlled by the `H²` norms of the
differences of their upper components. -/
theorem norm_sub_le_of_upper (F G : C(T3, MetricRec)) (hF : ∀ y μ ν, F y μ ν = F y ν μ)
    (hG : ∀ y μ ν, G y μ ν = G y ν μ) {B : ℝ}
    (h : ∀ κ : Upper, MemH 2 ⇑(cmp F κ.1.1 κ.1.2 - cmp G κ.1.1 κ.1.2) ∧
      sn 2 ⇑(cmp F κ.1.1 κ.1.2 - cmp G κ.1.1 κ.1.2) ≤ B) :
    ‖F - G‖ ≤ Real.sqrt cEmb * B := by
  have hB : 0 ≤ B := (sn_nonneg _ _).trans (h ⟨(0, 0), le_rfl⟩).2
  refine (ContinuousMap.norm_le _ (by positivity)).mpr fun y => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun μ => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun ν => ?_
  set κ := upperOf μ ν
  have e : (F - G) y μ ν = Complex.re ((cmp F κ.1.1 κ.1.2 - cmp G κ.1.1 κ.1.2) y) := by
    simp only [ContinuousMap.sub_apply, cmp_apply, Pi.sub_apply, κ, upperOf]
    split_ifs with hμν
    · simp
    · rw [hF y μ ν, hG y μ ν]; simp
  rw [e, Real.norm_eq_abs]
  refine (Complex.abs_re_le_norm _).trans ?_
  exact (norm_apply_le_sn_two _ (h κ).1 y).trans
    (mul_le_mul_of_nonneg_left (h κ).2 (Real.sqrt_nonneg _))

/-- Uniform Cauchy criterion with an explicit rate, and the rate of the limit. -/
theorem exists_limit_of_rate {F : ℕ → C(T3, MetricRec)} (hF : ∀ m y μ ν, F m y μ ν = F m y ν μ)
    (r : ℕ) (hr : 2 ≤ r) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ n m (κ : Upper), MemH r ⇑(cmp (F n) κ.1.1 κ.1.2 - cmp (F m) κ.1.1 κ.1.2) ∧
      sn r ⇑(cmp (F n) κ.1.1 κ.1.2 - cmp (F m) κ.1.1 κ.1.2) ≤
        c * (((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹)) :
    ∃ F₀ : C(T3, MetricRec), Tendsto F atTop (𝓝 F₀) ∧ (∀ y μ ν, F₀ y μ ν = F₀ y ν μ) ∧
      ∀ n (κ : Upper), MemH r ⇑(cmp (F n) κ.1.1 κ.1.2 - cmp F₀ κ.1.1 κ.1.2) ∧
        sn r ⇑(cmp (F n) κ.1.1 κ.1.2 - cmp F₀ κ.1.1 κ.1.2) ≤ c * ((n : ℝ) + 1)⁻¹ := by
  have hdist : ∀ n m N, N ≤ n → N ≤ m →
      dist (F n) (F m) ≤ Real.sqrt cEmb * (c * (2 * ((N : ℝ) + 1)⁻¹)) := by
    intro n m N hn hm
    rw [dist_eq_norm]
    refine (norm_sub_le_of_upper _ _ (hF n) (hF m) fun κ => ?_)
    obtain ⟨h1, h2⟩ := h n m κ
    refine ⟨memH_mono hr h1, (sn_mono' hr h1).trans (h2.trans ?_)⟩
    refine mul_le_mul_of_nonneg_left ?_ hc
    have a1 : ((n : ℝ) + 1)⁻¹ ≤ ((N : ℝ) + 1)⁻¹ := by gcongr
    have a2 : ((m : ℝ) + 1)⁻¹ ≤ ((N : ℝ) + 1)⁻¹ := by gcongr
    linarith
  have hb : Tendsto (fun N : ℕ => Real.sqrt cEmb * (c * (2 * ((N : ℝ) + 1)⁻¹))) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 : ℝ)
    simp only [one_div, mul_zero] at this
    simpa using (this.const_mul c).const_mul (Real.sqrt cEmb)
  have hcs : CauchySeq F := cauchySeq_of_le_tendsto_0 _ hdist hb
  obtain ⟨F₀, hF₀⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨F₀, hF₀, fun y μ ν => ?_, fun n κ => ?_⟩
  · have hc : ∀ a b : Fin 4, Continuous fun G : C(T3, MetricRec) => G y a b := fun a b =>
      (continuous_apply b).comp ((continuous_apply a).comp (continuous_eval_const y))
    have h1 : Tendsto (fun m => F m y μ ν) atTop (𝓝 (F₀ y μ ν)) :=
      (hc μ ν).continuousAt.tendsto.comp hF₀
    have h2 : Tendsto (fun m => F m y ν μ) atTop (𝓝 (F₀ y ν μ)) :=
      (hc ν μ).continuousAt.tendsto.comp hF₀
    simp only [hF _ y μ ν] at h1
    exact tendsto_nhds_unique h1 h2
  · have hG : Tendsto (fun m => cmp (F n) κ.1.1 κ.1.2 - cmp (F m) κ.1.1 κ.1.2) atTop
        (𝓝 (cmp (F n) κ.1.1 κ.1.2 - cmp F₀ κ.1.1 κ.1.2)) :=
      tendsto_const_nhds.sub (tendsto_cmp hF₀ _ _)
    have hb' : Tendsto (fun m : ℕ => c * (((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹)) atTop
        (𝓝 (c * ((n : ℝ) + 1)⁻¹)) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simp only [one_div] at this
      simpa using (tendsto_const_nhds (x := ((n : ℝ) + 1)⁻¹)).add this |>.const_mul c
    exact sn_le_of_tendsto r hG hb' (fun m => by positivity) (fun m => (h n m κ).1)
      (fun m => (h n m κ).2)

theorem cmp_interpRec_symRec {N : ℕ} [NeZero N] (u : Grid N → MetricRec) (κ : Upper) :
    cmp (interpRec (symRec u)) κ.1.1 κ.1.2 = cmp (interpRec u) κ.1.1 κ.1.2 := by
  ext y; simp [interpRec, cmp_reField, comp_symRec_eq, upperOf_upper]

theorem interpRec_symRec_symm {N : ℕ} [NeZero N] (u : Grid N → MetricRec) (y : T3) (μ ν : Fin 4) :
    interpRec (symRec u) y μ ν = interpRec (symRec u) y ν μ :=
  interpRec_symm (isSymRec_symRec u) y μ ν

/-- **Whole-sequence convergence of the interpolated writer solutions, with rate**
(`thm:supp-open-einstein`, convergence half; the metric rate `eq:supp-open-metric-rate` for the
interpolants).  For `s ≥ 5` there are mesh-independent `δ, K, C` such that: if, for every mesh
`h = 1/(n+1)`, `(q_n, v_n)` solves the open writer on `[0, T]` from the samples of the same
symmetric continuum data `(Q₀, V₀) ∈ H^{s+1} × H^s` with `‖(Q₀, V₀)‖_top ≤ ε ≤ δ`, staying in the top
ball of size `ε`, then there are continuous symmetric record fields `Q, V, A` with `Q(0) = Q₀`,
`V(0) = V₀` such that, for every `t ∈ [0, T]`, the whole sequence of real interpolants
`𝓘_h q_n(t)`, `𝓘_h v_n(t)` and `𝓘_h ∂ₜv_n(t)` converges uniformly on `𝕋³` to `Q(t)`, `V(t)`, `A(t)`, and
`‖𝓘_h q_n - Q‖_{H^{s-1}} + ‖𝓘_h v_n - V‖_{H^{s-2}} + ‖𝓘_h ∂ₜv_n - A‖_{H^{s-3}} ≤ C e^{Kt}(1 + t) h ε`
(each upper component). -/
theorem writer_continuum_limit (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∃ C ≥ 0, ∀ (T : ℝ) (q v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec)
      (Q₀ V₀ : C(T3, MetricRec)) (ε : ℝ),
      (∀ n, IsWriterSolution T (q n) (v n)) →
      (∀ n, q n 0 = sampleRec (n + 1) ⇑Q₀) → (∀ n, v n 0 = sampleRec (n + 1) ⇑V₀) →
      (∀ y μ ν, Q₀ y μ ν = Q₀ y ν μ) → (∀ y μ ν, V₀ y μ ν = V₀ y ν μ) →
      (∀ k, MemH (s + 1) ⇑(ccoord bM Q₀ k)) → (∀ k, MemH s ⇑(ccoord bM V₀ k)) →
      contTop s Q₀ V₀ ≤ ε → (∀ n, ∀ t ∈ Set.Icc 0 T, Xnorm s (q n t) (v n t) ≤ ε) → ε ≤ δ →
      ∃ Q V A : ℝ → C(T3, MetricRec), Q 0 = Q₀ ∧ V 0 = V₀ ∧ ∀ t ∈ Set.Icc 0 T,
        Tendsto (fun n => interpRec (q n t)) atTop (𝓝 (Q t)) ∧
        Tendsto (fun n => interpRec (v n t)) atTop (𝓝 (V t)) ∧
        Tendsto (fun n => interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t)))) atTop
          (𝓝 (A t)) ∧
        (∀ y μ ν, Q t y μ ν = Q t y ν μ) ∧ (∀ y μ ν, V t y μ ν = V t y ν μ) ∧
        (∀ y μ ν, A t y μ ν = A t y ν μ) ∧
        ∀ n (κ : Upper),
          (MemH (s - 1) ⇑(cmp (interpRec (q n t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2) ∧
          sn (s - 1) ⇑(cmp (interpRec (q n t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2) ≤
            C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹) ∧
          (MemH (s - 2) ⇑(cmp (interpRec (v n t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2) ∧
          sn (s - 2) ⇑(cmp (interpRec (v n t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2) ≤
            C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹) ∧
          (MemH (s - 3) ⇑(cmp (interpRec (harmonicWriterAcceleration (q n t) (v n t))) κ.1.1 κ.1.2 -
            cmp (A t) κ.1.1 κ.1.2) ∧
          sn (s - 3) ⇑(cmp (interpRec (harmonicWriterAcceleration (q n t) (v n t))) κ.1.1 κ.1.2 -
            cmp (A t) κ.1.1 κ.1.2) ≤ C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by
  obtain ⟨δ, hδ, K, hK, C, hC, hcau⟩ := interp_cauchy s hs
  obtain ⟨Ca, hCa, hal⟩ := sn_alias_le 2 (by norm_num)
  refine ⟨δ, hδ, K, hK, C, hC, fun T q v Q₀ V₀ ε hsol hq0 hv0 hQs hVs hQ hV hX0 hXq hεδ => ?_⟩
  set Q : ℝ → C(T3, MetricRec) := fun t => limUnder atTop fun n => interpRec (q n t)
  set V : ℝ → C(T3, MetricRec) := fun t => limUnder atTop fun n => interpRec (v n t)
  set A : ℝ → C(T3, MetricRec) := fun t =>
    limUnder atTop fun n => interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t)))
  have hε0 : 0 ≤ ε := (contTop_nonneg _ _ _).trans hX0
  -- the Cauchy rates
  have hrate : ∀ t ∈ Set.Icc 0 T, ∀ n m (κ : Upper),
      (sn (s - 1) ⇑(cmp (interpRec (q n t)) κ.1.1 κ.1.2 - cmp (interpRec (q m t)) κ.1.1 κ.1.2) ≤
        C * Real.exp (K * t) * (1 + t) * ε * (((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹)) ∧
      (sn (s - 2) ⇑(cmp (interpRec (v n t)) κ.1.1 κ.1.2 - cmp (interpRec (v m t)) κ.1.1 κ.1.2) ≤
        C * Real.exp (K * t) * (1 + t) * ε * (((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹)) ∧
      (sn (s - 3) ⇑(cmp (interpRec (harmonicWriterAcceleration (q n t) (v n t))) κ.1.1 κ.1.2 -
        cmp (interpRec (harmonicWriterAcceleration (q m t) (v m t))) κ.1.1 κ.1.2) ≤
        C * Real.exp (K * t) * (1 + t) * ε * (((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹)) := by
    intro t ht n m κ
    have h := hcau (n + 1) (m + 1) T (q n) (v n) (q m) (v m) Q₀ V₀ ε (hsol n) (hsol m) (hq0 n)
      (hv0 n) (hq0 m) (hv0 m) hQ hV hX0 (hXq n) (hXq m) hεδ t ht κ
    refine ⟨h.1.trans (le_of_eq ?_), h.2.1.trans (le_of_eq ?_), h.2.2.trans (le_of_eq ?_)⟩ <;>
      push_cast <;> ring
  have hc0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ C * Real.exp (K * t) * (1 + t) * ε := fun t ht => by
    have := ht.1; positivity
  have hmem : ∀ (r : ℕ) {M M' : ℕ} [NeZero M] [NeZero M'] (u : Grid M → MetricRec)
      (u' : Grid M' → MetricRec) (κ : Upper),
      MemH r ⇑(cmp (interpRec u) κ.1.1 κ.1.2 - cmp (interpRec u') κ.1.1 κ.1.2) := fun r _ _ _ _ u u' κ =>
    memH_sub (memH_cmp_reField r (fun μ ν => cx (comp u μ ν)) _ _).1
      (memH_cmp_reField r (fun μ ν => cx (comp u' μ ν)) _ _).1
  -- the three limits
  have hlimQ : ∀ t ∈ Set.Icc 0 T, Tendsto (fun n => interpRec (q n t)) atTop (𝓝 (Q t)) ∧
      (∀ y μ ν, Q t y μ ν = Q t y ν μ) ∧ ∀ n (κ : Upper),
        MemH (s - 1) ⇑(cmp (interpRec (q n t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2) ∧
        sn (s - 1) ⇑(cmp (interpRec (q n t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2) ≤
          C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ := by
    intro t ht
    obtain ⟨F₀, hF₀, hsym, hr⟩ := exists_limit_of_rate (F := fun n => interpRec (q n t))
      (fun n y μ ν => interpRec_symm (hsol n t ht).1 y μ ν) (s - 1) (by omega) _ (hc0 t ht)
      (fun n m κ => ⟨hmem _ _ _ κ, (hrate t ht n m κ).1⟩)
    have e : Q t = F₀ := tendsto_nhds_unique (tendsto_nhds_limUnder ⟨F₀, hF₀⟩) hF₀
    rw [e]
    exact ⟨hF₀, hsym, fun n κ => hr n κ⟩
  have hlimV : ∀ t ∈ Set.Icc 0 T, Tendsto (fun n => interpRec (v n t)) atTop (𝓝 (V t)) ∧
      (∀ y μ ν, V t y μ ν = V t y ν μ) ∧ ∀ n (κ : Upper),
        MemH (s - 2) ⇑(cmp (interpRec (v n t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2) ∧
        sn (s - 2) ⇑(cmp (interpRec (v n t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2) ≤
          C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ := by
    intro t ht
    obtain ⟨F₀, hF₀, hsym, hr⟩ := exists_limit_of_rate (F := fun n => interpRec (v n t))
      (fun n y μ ν => interpRec_symm (hsol n t ht).2.1 y μ ν) (s - 2) (by omega) _ (hc0 t ht)
      (fun n m κ => ⟨hmem _ _ _ κ, (hrate t ht n m κ).2.1⟩)
    have e : V t = F₀ := tendsto_nhds_unique (tendsto_nhds_limUnder ⟨F₀, hF₀⟩) hF₀
    rw [e]
    exact ⟨hF₀, hsym, fun n κ => hr n κ⟩
  have hlimA : ∀ t ∈ Set.Icc 0 T, Tendsto (fun n =>
      interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t)))) atTop (𝓝 (A t)) ∧
      (∀ y μ ν, A t y μ ν = A t y ν μ) ∧ ∀ n (κ : Upper),
        MemH (s - 3) ⇑(cmp (interpRec (harmonicWriterAcceleration (q n t) (v n t))) κ.1.1 κ.1.2 -
          cmp (A t) κ.1.1 κ.1.2) ∧
        sn (s - 3) ⇑(cmp (interpRec (harmonicWriterAcceleration (q n t) (v n t))) κ.1.1 κ.1.2 -
          cmp (A t) κ.1.1 κ.1.2) ≤ C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ := by
    intro t ht
    obtain ⟨F₀, hF₀, hsym, hr⟩ := exists_limit_of_rate
      (F := fun n => interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t))))
      (fun n y μ ν => interpRec_symRec_symm _ y μ ν) (s - 3) (by omega) _ (hc0 t ht)
      (fun n m κ => by
        rw [cmp_interpRec_symRec, cmp_interpRec_symRec]
        exact ⟨hmem _ _ _ κ, (hrate t ht n m κ).2.2⟩)
    have e : A t = F₀ := tendsto_nhds_unique (tendsto_nhds_limUnder ⟨F₀, hF₀⟩) hF₀
    rw [e]
    refine ⟨hF₀, hsym, fun n κ => ?_⟩
    have := hr n κ
    rwa [cmp_interpRec_symRec] at this
  -- initial data
  have hT : ∀ t ∈ Set.Icc 0 T, 0 ≤ T := fun t ht => ht.1.trans ht.2
  have hinit : ∀ (F₀ : C(T3, MetricRec)), (∀ y μ ν, F₀ y μ ν = F₀ y ν μ) →
      (∀ k, MemH 3 ⇑(ccoord bM F₀ k)) →
      Tendsto (fun n => interpRec (sampleRec (n + 1) ⇑F₀)) atTop (𝓝 F₀) := by
    intro F₀ hFs hFm
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ n : ℕ, ‖interpRec (sampleRec (n + 1) ⇑F₀) - F₀‖ ≤
        Real.sqrt cEmb * (Ca * ((n : ℝ) + 1)⁻¹ * ccoordSum 3 bM F₀) := by
      intro n
      have hsy : IsSymRec (sampleRec (n + 1) ⇑F₀) := fun x a b => hFs _ a b
      refine norm_sub_le_of_upper (interpRec (sampleRec (n + 1) ⇑F₀)) F₀
        (fun y μ ν => interpRec_symm hsy y μ ν) hFs fun κ => ?_
      obtain ⟨h1, h2⟩ := hal (n + 1) F₀ κ.1.1 κ.1.2 (memH_cmp hFm κ.1.1 κ.1.2)
      refine ⟨h1, h2.trans ?_⟩
      push_cast
      exact mul_le_mul_of_nonneg_left (sn_cmp_le_ccoordSum _ _ _ _) (by positivity)
    refine squeeze_zero (fun _ => norm_nonneg _) hbound ?_
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simp only [one_div] at this
    simpa using ((this.const_mul Ca).mul_const (ccoordSum 3 bM F₀)).const_mul (Real.sqrt cEmb)
  refine ⟨Q, V, A, ?_, ?_, fun t ht => ⟨(hlimQ t ht).1, (hlimV t ht).1, (hlimA t ht).1,
    (hlimQ t ht).2.1, (hlimV t ht).2.1, (hlimA t ht).2.1, fun n κ =>
      ⟨(hlimQ t ht).2.2 n κ, (hlimV t ht).2.2 n κ, (hlimA t ht).2.2 n κ⟩⟩⟩
  · have h1 : Tendsto (fun n => interpRec (q n 0)) atTop (𝓝 Q₀) := by
      simp only [hq0]
      exact hinit Q₀ hQs fun k => memH_mono (by omega) (hQ k)
    exact tendsto_nhds_unique (tendsto_nhds_limUnder ⟨Q₀, h1⟩) h1
  · have h1 : Tendsto (fun n => interpRec (v n 0)) atTop (𝓝 V₀) := by
      simp only [hv0]
      exact hinit V₀ hVs fun k => memH_mono (by omega) (hV k)
    exact tendsto_nhds_unique (tendsto_nhds_limUnder ⟨V₀, h1⟩) h1

/-! ### Uniqueness of the limit within the continuum solution class -/

/-- **Every continuum solution with the same data is the limit of the interpolated writer
solutions** (uniqueness half of `thm:supp-open-einstein`): for `s ≥ 5` there is `δ > 0` such
that if `(q_n, v_n)` are open writer solutions on `[0, T]` started from the samples of `(Q₀, V₀)`
and staying in the grid top ball `δ`, and `(Q', V', …)` is a continuum solution of the harmonic
normal row on `[0, T]` (`IsContSolution`) with `Q'(0) = Q₀`, `V'(0) = V₀` in the continuum top ball
`ε ≤ δ`, then for every `t ∈ [0, T]`, `𝓘_h q_n(t) → Q'(t)` and `𝓘_h v_n(t) → V'(t)` uniformly on
`𝕋³`.  In particular any two such continuum solutions coincide on `[0, T]`, and they coincide with
the limit of `writer_continuum_limit`. -/
theorem contSolution_eq_limit (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∀ (T : ℝ) (q v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec)
      (Q' V' W' : ℝ → C(T3, MetricRec)) (Qd' Vd' : ℝ → Fin 3 → C(T3, MetricRec))
      (Qdd' : ℝ → Fin 3 → Fin 3 → C(T3, MetricRec)) (ε : ℝ),
      (∀ n, IsWriterSolution T (q n) (v n)) →
      (∀ n, q n 0 = sampleRec (n + 1) ⇑(Q' 0)) → (∀ n, v n 0 = sampleRec (n + 1) ⇑(V' 0)) →
      (∀ n, ∀ t ∈ Set.Icc 0 T, Xnorm s (q n t) (v n t) ≤ δ) →
      IsContSolution s T Q' V' W' Qd' Vd' Qdd' → (∀ t ∈ Set.Icc 0 T, contTop s (Q' t) (V' t) ≤ ε) →
      ε ≤ δ → ∀ t ∈ Set.Icc 0 T,
        Tendsto (fun n => interpRec (q n t)) atTop (𝓝 (Q' t)) ∧
        Tendsto (fun n => interpRec (v n t)) atTop (𝓝 (V' t)) := by
  obtain ⟨δ, hδ, K, hK, C, hC, hcmp⟩ := continuum_comparison s hs
  obtain ⟨Ca1, hCa1, hal1⟩ := sn_alias_le (s - 1) (by omega)
  obtain ⟨Ca2, hCa2, hal2⟩ := sn_alias_le (s - 2) (by omega)
  refine ⟨δ, hδ, fun T q v Q' V' W' Qd' Vd' Qdd' ε hsol hq0 hv0 hXq hcs hXQ hεδ t ht => ?_⟩
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hε0 : 0 ≤ ε := (contTop_nonneg _ _ _).trans (hXQ 0 ⟨le_rfl, hT⟩)
  -- the sampled comparison along the sequence
  have hD : ∀ n : ℕ, Xnorm (s - 2) (q n t - sampleRec (n + 1) ⇑(Q' t))
      (v n t - sampleRec (n + 1) ⇑(V' t)) ≤
      C * Real.exp (K * t) * ((1 + t) * ((((n + 1 : ℕ) : ℝ))⁻¹ * ε)) := by
    intro n
    have h := (hcmp (n + 1) T (q n) (v n) Q' V' W' Qd' Vd' Qdd' ε (hsol n) (hXq n) hcs hXQ hεδ t ht).1
    have e0 : Xnorm (s - 2) (q n 0 - sampleRec (n + 1) ⇑(Q' 0))
        (v n 0 - sampleRec (n + 1) ⇑(V' 0)) = 0 := by
      rw [hq0 n, hv0 n, sub_self, sub_self]
      unfold Xnorm Xsq
      have : ∀ κ : Upper, cx (comp (0 : Grid (n + 1) → MetricRec) κ.1.1 κ.1.2) = 0 := fun κ => by
        funext x; simp [comp, cx]
      simp only [this]
      simp [PeriodicGridSobolev.sobSq, PeriodicGridSobolev.gridNormSq]
    rw [e0, zero_add] at h
    exact h
  have hb : Tendsto (fun n : ℕ => C * Real.exp (K * t) * ((1 + t) * ((((n + 1 : ℕ) : ℝ))⁻¹ * ε)))
      atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simp only [one_div] at this
    have h2 := ((this.mul_const ε).const_mul (1 + t)).const_mul (C * Real.exp (K * t))
    simp only [zero_mul, mul_zero] at h2
    refine h2.congr fun n => ?_
    push_cast; ring
  have hb2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * ε) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simp only [one_div] at this
    simpa using this.mul_const ε
  have hQs := hcs.symQ t ht
  have hVs := hcs.symV t ht
  have hQm := hcs.regQ t ht
  have hVm := hcs.regV t ht
  have hQX : ∀ κ : Upper, sn (s - 1 + 1) ⇑(cmp (Q' t) κ.1.1 κ.1.2) ≤ ε := fun κ => by
    refine (sn_mono' (by omega) (memH_cmp hQm κ.1.1 κ.1.2)).trans ?_
    exact (sn_cmp_le_ccoordSum _ _ _ _).trans ((le_add_of_nonneg_right
      (ccoordSum_nonneg _ _ _)).trans (hXQ t ht))
  have hVX : ∀ κ : Upper, sn (s - 2 + 1) ⇑(cmp (V' t) κ.1.1 κ.1.2) ≤ ε := fun κ => by
    refine (sn_mono' (by omega) (memH_cmp hVm κ.1.1 κ.1.2)).trans ?_
    exact (sn_cmp_le_ccoordSum _ _ _ _).trans ((le_add_of_nonneg_left
      (ccoordSum_nonneg _ _ _)).trans (hXQ t ht))
  refine ⟨?_, ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ n : ℕ, ‖interpRec (q n t) - Q' t‖ ≤ Real.sqrt cEmb *
        (Real.sqrt (pc (s - 1)) * (C * Real.exp (K * t) * ((1 + t) * ((((n + 1 : ℕ) : ℝ))⁻¹ * ε))) +
          Ca1 * (((n : ℝ) + 1)⁻¹ * ε)) := by
      intro n
      refine norm_sub_le_of_upper _ _ (fun y μ ν => interpRec_symm (hsol n t ht).1 y μ ν)
        hQs fun κ => ?_
      have e : cmp (interpRec (q n t)) κ.1.1 κ.1.2 - cmp (Q' t) κ.1.1 κ.1.2 =
          cmp (interpRec (q n t - sampleRec (n + 1) ⇑(Q' t))) κ.1.1 κ.1.2 +
            (cmp (interpRec (sampleRec (n + 1) ⇑(Q' t))) κ.1.1 κ.1.2 - cmp (Q' t) κ.1.1 κ.1.2) := by
        rw [interpRec_sub, cmp_sub]; abel
      rw [e]
      obtain ⟨hm1, hs1⟩ := memH_cmp_reField (s - 1)
        (fun μ ν => cx (comp (q n t - sampleRec (n + 1) ⇑(Q' t)) μ ν)) κ.1.1 κ.1.2
      obtain ⟨hm2, hs2⟩ := hal1 (n + 1) (Q' t) κ.1.1 κ.1.2 (memH_mono (by omega) (memH_cmp hQm κ.1.1 κ.1.2))
      refine ⟨memH_mono (by omega) (memH_add hm1 hm2), (sn_mono' (by omega) (memH_add hm1 hm2)).trans
        ((sn_add_le' hm1 hm2).trans (add_le_add ?_ ?_))⟩
      · refine hs1.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
        refine (sobNorm_q_le (s - 2) (isSymRec_sub (hsol n t ht).1 (isSymRec_sampleRec hQs))
          (v n t - sampleRec (n + 1) ⇑(V' t)) _ _ (by omega)).trans (hD n)
      · refine hs2.trans ?_
        push_cast
        calc Ca1 * ((n : ℝ) + 1)⁻¹ * sn (s - 1 + 1) ⇑(cmp (Q' t) κ.1.1 κ.1.2)
            ≤ Ca1 * ((n : ℝ) + 1)⁻¹ * ε := by gcongr; exact hQX κ
          _ = Ca1 * (((n : ℝ) + 1)⁻¹ * ε) := by ring
    refine squeeze_zero (fun _ => norm_nonneg _) hbound ?_
    simpa using ((hb.const_mul (Real.sqrt (pc (s - 1)))).add (hb2.const_mul Ca1)).const_mul
      (Real.sqrt cEmb)
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ n : ℕ, ‖interpRec (v n t) - V' t‖ ≤ Real.sqrt cEmb *
        (Real.sqrt (pc (s - 2)) * (C * Real.exp (K * t) * ((1 + t) * ((((n + 1 : ℕ) : ℝ))⁻¹ * ε))) +
          Ca2 * (((n : ℝ) + 1)⁻¹ * ε)) := by
      intro n
      refine norm_sub_le_of_upper _ _ (fun y μ ν => interpRec_symm (hsol n t ht).2.1 y μ ν)
        hVs fun κ => ?_
      have e : cmp (interpRec (v n t)) κ.1.1 κ.1.2 - cmp (V' t) κ.1.1 κ.1.2 =
          cmp (interpRec (v n t - sampleRec (n + 1) ⇑(V' t))) κ.1.1 κ.1.2 +
            (cmp (interpRec (sampleRec (n + 1) ⇑(V' t))) κ.1.1 κ.1.2 - cmp (V' t) κ.1.1 κ.1.2) := by
        rw [interpRec_sub, cmp_sub]; abel
      rw [e]
      obtain ⟨hm1, hs1⟩ := memH_cmp_reField (s - 2)
        (fun μ ν => cx (comp (v n t - sampleRec (n + 1) ⇑(V' t)) μ ν)) κ.1.1 κ.1.2
      obtain ⟨hm2, hs2⟩ := hal2 (n + 1) (V' t) κ.1.1 κ.1.2 (memH_mono (by omega) (memH_cmp hVm κ.1.1 κ.1.2))
      refine ⟨memH_mono (by omega) (memH_add hm1 hm2), (sn_mono' (by omega) (memH_add hm1 hm2)).trans
        ((sn_add_le' hm1 hm2).trans (add_le_add ?_ ?_))⟩
      · refine hs1.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
        refine (sobNorm_v_le (s - 2) (q n t - sampleRec (n + 1) ⇑(Q' t))
          (isSymRec_sub (hsol n t ht).2.1 (isSymRec_sampleRec hVs)) _ _ le_rfl).trans (hD n)
      · refine hs2.trans ?_
        push_cast
        calc Ca2 * ((n : ℝ) + 1)⁻¹ * sn (s - 2 + 1) ⇑(cmp (V' t) κ.1.1 κ.1.2)
            ≤ Ca2 * ((n : ℝ) + 1)⁻¹ * ε := by gcongr; exact hVX κ
          _ = Ca2 * (((n : ℝ) + 1)⁻¹ * ε) := by ring
    refine squeeze_zero (fun _ => norm_nonneg _) hbound ?_
    simpa using ((hb.const_mul (Real.sqrt (pc (s - 2)))).add (hb2.const_mul Ca2)).const_mul
      (Real.sqrt cEmb)

/-! ### Limits of derivatives and of the normal row -/

theorem IsLineDeriv.sub' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {i : Fin 3}
    {F F' G G' : T3 → E} (hF : IsLineDeriv i F F') (hG : IsLineDeriv i G G') :
    IsLineDeriv i (fun y => F y - G y) (fun y => F' y - G' y) := fun x => (hF x).sub (hG x)

theorem reField_symm {N : ℕ} [NeZero N] {w : Fin 4 → Fin 4 → Grid N → ℂ}
    (hw : ∀ μ ν, w μ ν = w ν μ) (y : T3) (μ ν : Fin 4) : reField w y μ ν = reField w y ν μ := by
  simp only [reField_apply, hw μ ν]

theorem interpD_symm {N : ℕ} [NeZero N] {u : Grid N → MetricRec} (hu : IsSymRec u) (i : Fin 3)
    (y : T3) (μ ν : Fin 4) : interpD u i y μ ν = interpD u i y ν μ := by
  have e : comp u μ ν = comp u ν μ := funext fun x => hu x μ ν
  simp only [interpD, reField_apply, e]

theorem interpDD_symm {N : ℕ} [NeZero N] {u : Grid N → MetricRec} (hu : IsSymRec u) (i j : Fin 3)
    (y : T3) (μ ν : Fin 4) : interpDD u i j y μ ν = interpDD u i j y ν μ := by
  have e : comp u μ ν = comp u ν μ := funext fun x => hu x μ ν
  simp only [interpDD, reField_apply, e]

/-- **Uniform limits of classical derivatives are classical derivatives.** -/
theorem isLineDeriv_of_tendsto {i : Fin 3} {F F' : ℕ → C(T3, MetricRec)} {G G' : C(T3, MetricRec)}
    (hd : ∀ n, IsLineDeriv i ⇑(F n) ⇑(F' n)) (hF : Tendsto F atTop (𝓝 G))
    (hF' : Tendsto F' atTop (𝓝 G')) : IsLineDeriv i ⇑G ⇑G' := by
  intro x
  have hunif : TendstoUniformly (fun n (τ : ℝ) => F' n (x + lineShift i τ))
      (fun τ => G' (x + lineShift i τ)) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have := (Metric.tendsto_nhds.mp hF') ε hε
    filter_upwards [this] with n hn τ
    rw [dist_comm]
    exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist _) hn
  have hpt : ∀ τ : ℝ, Tendsto (fun n => F n (x + lineShift i τ)) atTop
      (𝓝 (G (x + lineShift i τ))) := fun τ =>
    ((continuous_eval_const (x + lineShift i τ)).tendsto G).comp hF
  have h := hasDerivAt_of_tendstoUniformly hunif
    (Eventually.of_forall fun n τ => (hd n).hasDerivAt x τ) hpt 0
  simpa [lineShift_zero] using h

open HarmonicDefect in
/-- The harmonic first-jet source is analytic in the site jet at every invertible record. -/
theorem analyticAt_source_jet_of_det (μ ν : Fin 4) (w₀ : JetSpace)
    (hdet : (Matrix.of (minkowski + w₀.1)).det ≠ 0) :
    AnalyticAt ℝ (fun w : JetSpace => harmonicSource (minkowski + w.1) w.2 μ ν) w₀ := by
  have hg : AnalyticAt ℝ (fun w : JetSpace => minkowski + w.1) w₀ := by fun_prop
  have hinv : AnalyticAt ℝ (fun w : JetSpace => recInv (minkowski + w.1)) w₀ := by
    refine AnalyticAt.pi fun i => AnalyticAt.pi fun j => ?_
    exact (analyticAt_inv_entry _ hdet i j).comp_of_eq hg rfl
  have hjet : AnalyticAt ℝ (fun w : JetSpace => metricJet w.2) w₀ := by
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
  have := (hpoly _).comp (hg.prod (hinv.prod hjet))
  simp only [harmonicSource]
  simp only [Function.comp_def] at this
  exact analyticAt_const.mul this

theorem continuousAt_finsetSum' {X ι : Type*} [TopologicalSpace X] (s : Finset ι)
    {f : ι → X → ℝ} {z : X} (h : ∀ i ∈ s, ContinuousAt (f i) z) :
    ContinuousAt (fun x => ∑ i ∈ s, f i x) z :=
  tendsto_finsetSum s h

/-- The normal row as a function of the whole pointwise jet. -/
def rowJet (z : MetricRec × MetricRec × MetricRec × (Fin 3 → MetricRec) × (Fin 3 → MetricRec) ×
    (Fin 3 → Fin 3 → MetricRec)) : MetricRec :=
  normalRow z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2

/-- **The normal row is continuous at every invertible record.** -/
theorem continuousAt_rowJet (z : MetricRec × MetricRec × MetricRec × (Fin 3 → MetricRec) ×
    (Fin 3 → MetricRec) × (Fin 3 → Fin 3 → MetricRec))
    (hdet : (Matrix.of (minkowski + z.1)).det ≠ 0) : ContinuousAt rowJet z := by
  have hg : ContinuousAt (fun z : MetricRec × MetricRec × MetricRec × (Fin 3 → MetricRec) ×
      (Fin 3 → MetricRec) × (Fin 3 → Fin 3 → MetricRec) => minkowski + z.1) z := by fun_prop
  have hcoef : ∀ A : MetricRec → ℝ, AnalyticOnNhd ℝ A detSet →
      ContinuousAt (fun z : MetricRec × MetricRec × MetricRec × (Fin 3 → MetricRec) ×
        (Fin 3 → MetricRec) × (Fin 3 → Fin 3 → MetricRec) => A (minkowski + z.1)) z := by
    intro A hA
    exact ContinuousAt.comp (g := A) ((hA _ hdet).continuousAt) hg
  have hA : AnalyticOnNhd ℝ harmA detSet := fun g hg' => by
    unfold harmA; exact (analyticAt_inv_entry g hg' 0 0).neg
  have hsrc : ∀ μ ν, ContinuousAt (fun z : MetricRec × MetricRec × MetricRec × (Fin 3 → MetricRec) ×
      (Fin 3 → MetricRec) × (Fin 3 → Fin 3 → MetricRec) =>
        (fun w : JetSpace => harmonicSource (minkowski + w.1) w.2 μ ν)
          ((z.1, z.2.1, z.2.2.2.1) : JetSpace)) z := by
    intro μ ν
    have h := (analyticAt_source_jet_of_det μ ν (z.1, z.2.1, z.2.2.2.1) hdet).continuousAt
    have hp : ContinuousAt (fun z : MetricRec × MetricRec × MetricRec × (Fin 3 → MetricRec) ×
        (Fin 3 → MetricRec) × (Fin 3 → Fin 3 → MetricRec) =>
          ((z.1, z.2.1, z.2.2.2.1) : JetSpace)) z := by fun_prop
    exact ContinuousAt.comp_of_eq (f := fun z : MetricRec × MetricRec × MetricRec ×
      (Fin 3 → MetricRec) × (Fin 3 → MetricRec) × (Fin 3 → Fin 3 → MetricRec) =>
        ((z.1, z.2.1, z.2.2.2.1) : JetSpace)) h hp rfl
  refine continuousAt_pi.2 fun μ => continuousAt_pi.2 fun ν => ?_
  have e : (fun z : MetricRec × MetricRec × MetricRec × (Fin 3 → MetricRec) ×
      (Fin 3 → MetricRec) × (Fin 3 → Fin 3 → MetricRec) => rowJet z μ ν) = fun z =>
      harmA (minkowski + z.1) * z.2.2.1 μ ν +
        2 * ∑ i, harmB i (minkowski + z.1) * z.2.2.2.2.1 i μ ν -
        ∑ i, ∑ j, harmC i j (minkowski + z.1) * z.2.2.2.2.2 i j μ ν -
        harmonicSource (minkowski + z.1) (z.2.1, z.2.2.2.1) μ ν := by
    funext z
    simp only [rowJet, normalRow, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply]
  rw [e]
  refine ((((hcoef _ hA).mul (by fun_prop)).add (continuousAt_const.mul
    (continuousAt_finsetSum' _ fun i _ => (hcoef _ (analyticOnNhd_harmB i)).mul (by fun_prop)))).sub
    (continuousAt_finsetSum' _ fun i _ => continuousAt_finsetSum' _ fun j _ =>
      (hcoef _ (analyticOnNhd_harmC i j)).mul (by fun_prop))).sub (hsrc μ ν)

/-! ### The limit solves the harmonic reduced equation -/

/-- Cauchy rates of the interpolant derivative fields, one order below the fields. -/
theorem deriv_cauchy {M M' : ℕ} [NeZero M] [NeZero M'] {r : ℕ} (u : Grid M → MetricRec)
    (u' : Grid M' → MetricRec) (i : Fin 3) (κ : Upper)
    {w : Fin 4 → Fin 4 → Grid M → ℂ} {w' : Fin 4 → Fin 4 → Grid M' → ℂ} :
    MemH (r + 1) ⇑(cmp (reField w) κ.1.1 κ.1.2 - cmp (reField w') κ.1.1 κ.1.2) →
    MemH r ⇑(cmp (reField fun μ ν => PeriodicGridSobolev.Sampling.specD i (w μ ν)) κ.1.1 κ.1.2 -
        cmp (reField fun μ ν => PeriodicGridSobolev.Sampling.specD i (w' μ ν)) κ.1.1 κ.1.2) ∧
      sn r ⇑(cmp (reField fun μ ν => PeriodicGridSobolev.Sampling.specD i (w μ ν)) κ.1.1 κ.1.2 -
        cmp (reField fun μ ν => PeriodicGridSobolev.Sampling.specD i (w' μ ν)) κ.1.1 κ.1.2) ≤
      sn (r + 1) ⇑(cmp (reField w) κ.1.1 κ.1.2 - cmp (reField w') κ.1.1 κ.1.2) := by
  intro hm
  refine memH_of_isLineDeriv (i := i) ?_ hm
  have h1 := isLineDeriv_cmp (isLineDeriv_reField i w) κ.1.1 κ.1.2
  have h2 := isLineDeriv_cmp (isLineDeriv_reField i w') κ.1.1 κ.1.2
  exact IsLineDeriv.sub' h1 h2

/-- **The limit of the interpolated writer solutions is a classical solution of the harmonic
reduced equation** (`thm:supp-open-einstein`, identification of the limit; ten-component form).
Under the hypotheses of `writer_continuum_limit` (with a possibly smaller `δ`), the limit fields
`Q, V, A` (`Q(0) = Q₀`, `V(0) = V₀`) admit classical spatial derivative fields `Qd, Vd, Qdd`
(`IsContJet`), satisfy `∂ₜQ = V`, `∂ₜV = A` at every interior time, and the ten upper components of
the harmonic normal row `eq:main-harmonic-normal-row` vanish identically on `[0, T] × 𝕋³`. -/
theorem writer_limit_solves (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ K₁ ≥ 0, ∃ C₁ ≥ 0, ∃ K₂ ≥ 0, ∃ C₂ ≥ 0, ∀ (T : ℝ)
      (q v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec) (Q₀ V₀ : C(T3, MetricRec)) (ε : ℝ),
      (∀ n, IsWriterSolution T (q n) (v n)) →
      (∀ n, q n 0 = sampleRec (n + 1) ⇑Q₀) → (∀ n, v n 0 = sampleRec (n + 1) ⇑V₀) →
      (∀ y μ ν, Q₀ y μ ν = Q₀ y ν μ) → (∀ y μ ν, V₀ y μ ν = V₀ y ν μ) →
      (∀ k, MemH (s + 1) ⇑(ccoord bM Q₀ k)) → (∀ k, MemH s ⇑(ccoord bM V₀ k)) →
      contTop s Q₀ V₀ ≤ ε → (∀ n, ∀ t ∈ Set.Icc 0 T, Xnorm s (q n t) (v n t) ≤ ε) → ε ≤ δ →
      ∃ (Q V A : ℝ → C(T3, MetricRec)) (Qd Vd : ℝ → Fin 3 → C(T3, MetricRec))
        (Qdd : ℝ → Fin 3 → Fin 3 → C(T3, MetricRec)), Q 0 = Q₀ ∧ V 0 = V₀ ∧
        ∀ t ∈ Set.Icc 0 T,
          Tendsto (fun n => interpRec (q n t)) atTop (𝓝 (Q t)) ∧
          Tendsto (fun n => interpRec (v n t)) atTop (𝓝 (V t)) ∧
          IsContJet (Q t) (V t) (Qd t) (Vd t) (Qdd t) ∧
          (∀ y (κ : Upper), normalRow (Q t y) (V t y) (A t y) (fun i => Qd t i y)
            (fun i => Vd t i y) (fun i j => Qdd t i j y) κ.1.1 κ.1.2 = 0) ∧
          (t ∈ Set.Ioo 0 T → ∀ y, HasDerivAt (fun τ => Q τ y) (V t y) t ∧
            HasDerivAt (fun τ => V τ y) (A t y) t) ∧
          Tendsto (fun n => interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t)))) atTop
            (𝓝 (A t)) ∧
          (∀ i, Tendsto (fun n => interpD (q n t) i) atTop (𝓝 (Qd t i))) ∧
          (∀ i, Tendsto (fun n => interpD (v n t) i) atTop (𝓝 (Vd t i))) ∧
          (∀ i j, Tendsto (fun n => interpDD (q n t) i j) atTop (𝓝 (Qdd t i j))) ∧
          (∀ n (κ : Upper),
            (MemH (s - 1) ⇑(cmp (interpRec (q n t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2) ∧
            sn (s - 1) ⇑(cmp (interpRec (q n t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2) ≤
              C₁ * Real.exp (K₁ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹) ∧
            (MemH (s - 2) ⇑(cmp (interpRec (v n t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2) ∧
            sn (s - 2) ⇑(cmp (interpRec (v n t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2) ≤
              C₁ * Real.exp (K₁ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹) ∧
            (MemH (s - 3) ⇑(cmp (interpRec (harmonicWriterAcceleration (q n t) (v n t))) κ.1.1 κ.1.2 -
              cmp (A t) κ.1.1 κ.1.2) ∧
            sn (s - 3) ⇑(cmp (interpRec (harmonicWriterAcceleration (q n t) (v n t))) κ.1.1 κ.1.2 -
              cmp (A t) κ.1.1 κ.1.2) ≤ C₁ * Real.exp (K₁ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹)) ∧
          (∀ n (κ : Upper) i,
            MemH (s - 2) ⇑(cmp (interpD (q n t) i) κ.1.1 κ.1.2 - cmp (Qd t i) κ.1.1 κ.1.2) ∧
            sn (s - 2) ⇑(cmp (interpD (q n t) i) κ.1.1 κ.1.2 - cmp (Qd t i) κ.1.1 κ.1.2) ≤
              C₂ * Real.exp (K₂ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹) ∧
          (∀ n (κ : Upper) i,
            MemH (s - 3) ⇑(cmp (interpD (v n t) i) κ.1.1 κ.1.2 - cmp (Vd t i) κ.1.1 κ.1.2) ∧
            sn (s - 3) ⇑(cmp (interpD (v n t) i) κ.1.1 κ.1.2 - cmp (Vd t i) κ.1.1 κ.1.2) ≤
              C₂ * Real.exp (K₂ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹) ∧
          (∀ n (κ : Upper) i j,
            MemH (s - 3) ⇑(cmp (interpDD (q n t) i j) κ.1.1 κ.1.2 - cmp (Qdd t i j) κ.1.1 κ.1.2) ∧
            sn (s - 3) ⇑(cmp (interpDD (q n t) i j) κ.1.1 κ.1.2 - cmp (Qdd t i j) κ.1.1 κ.1.2) ≤
              C₂ * Real.exp (K₂ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by
  obtain ⟨δL, hδL, KL, hKL, CL, hCL, hlim⟩ := writer_continuum_limit s hs
  obtain ⟨δc, hδc, Kc, hKc, Cc, hCc, hcau⟩ := interp_cauchy s hs
  obtain ⟨δR, hδR, CR, hCR, hsmall⟩ := interp_row_small s hs
  obtain ⟨r₀, hr₀, hdet⟩ := exists_det_chart
  set B : ℝ := 1 + ∑ j, ‖bM j‖
  have hB : ∀ j, ‖bM j‖ ≤ B := fun j => by
    have := single_le_sum (f := fun j => ‖bM j‖) (fun _ _ => norm_nonneg _) (mem_univ j)
    linarith
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ∑ j, ‖bM j‖ := sum_nonneg fun _ _ => norm_nonneg _
    linarith
  set Cq : ℝ := B * (Real.sqrt cEmb * (16 * Real.sqrt (pc 2)))
  have hCq : 0 ≤ Cq := by positivity
  refine ⟨min (min δL δc) (min δR (r₀ / (2 * (Cq + 1)))), by positivity, KL, hKL, CL, hCL, Kc, hKc,
    Cc, hCc, fun T q v Q₀ V₀ ε hsol hq0 hv0 hQs hVs hQ hV hX0 hXq hεδ => ?_⟩
  have hεL : ε ≤ δL := hεδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεc : ε ≤ δc := hεδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεR : ε ≤ δR := hεδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεr : ε ≤ r₀ / (2 * (Cq + 1)) := hεδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε0 : 0 ≤ ε := (contTop_nonneg _ _ _).trans hX0
  obtain ⟨Q, V, A, hQ0, hV0, hL⟩ := hlim T q v Q₀ V₀ ε hsol hq0 hv0 hQs hVs hQ hV hX0 hXq hεL
  -- Cauchy rates
  have hrate : ∀ t ∈ Set.Icc 0 T, ∀ n m (κ : Upper),
      sn (s - 1) ⇑(cmp (interpRec (q n t)) κ.1.1 κ.1.2 - cmp (interpRec (q m t)) κ.1.1 κ.1.2) ≤
        Cc * Real.exp (Kc * t) * (1 + t) * ε * (((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹) ∧
      sn (s - 2) ⇑(cmp (interpRec (v n t)) κ.1.1 κ.1.2 - cmp (interpRec (v m t)) κ.1.1 κ.1.2) ≤
        Cc * Real.exp (Kc * t) * (1 + t) * ε * (((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹) := by
    intro t ht n m κ
    have h := hcau (n + 1) (m + 1) T (q n) (v n) (q m) (v m) Q₀ V₀ ε (hsol n) (hsol m) (hq0 n)
      (hv0 n) (hq0 m) (hv0 m) hQ hV hX0 (hXq n) (hXq m) hεc t ht κ
    refine ⟨h.1.trans (le_of_eq ?_), h.2.1.trans (le_of_eq ?_)⟩ <;> push_cast <;> ring
  have hc0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ Cc * Real.exp (Kc * t) * (1 + t) * ε := fun t ht => by
    have := ht.1; positivity
  have hmem : ∀ (r : ℕ) {M M' : ℕ} [NeZero M] [NeZero M'] (w : Fin 4 → Fin 4 → Grid M → ℂ)
      (w' : Fin 4 → Fin 4 → Grid M' → ℂ) (κ : Upper),
      MemH r ⇑(cmp (reField w) κ.1.1 κ.1.2 - cmp (reField w') κ.1.1 κ.1.2) :=
    fun r _ _ _ _ w w' κ => memH_sub (memH_cmp_reField r w _ _).1 (memH_cmp_reField r w' _ _).1
  -- the derivative limits, as `limUnder`
  set Qd : ℝ → Fin 3 → C(T3, MetricRec) := fun t i => limUnder atTop fun n => interpD (q n t) i
  set Vd : ℝ → Fin 3 → C(T3, MetricRec) := fun t i => limUnder atTop fun n => interpD (v n t) i
  set Qdd : ℝ → Fin 3 → Fin 3 → C(T3, MetricRec) := fun t i j =>
    limUnder atTop fun n => interpDD (q n t) i j
  have hs1 : s - 2 + 1 = s - 1 := by omega
  have hs2 : s - 3 + 1 = s - 2 := by omega
  -- first derivatives of `q`
  have hQdL : ∀ t ∈ Set.Icc 0 T, ∀ i, Tendsto (fun n => interpD (q n t) i) atTop (𝓝 (Qd t i)) ∧
      (∀ n m (κ : Upper), MemH (s - 2) ⇑(cmp (interpD (q n t) i) κ.1.1 κ.1.2 -
        cmp (interpD (q m t) i) κ.1.1 κ.1.2) ∧
      sn (s - 2) ⇑(cmp (interpD (q n t) i) κ.1.1 κ.1.2 - cmp (interpD (q m t) i) κ.1.1 κ.1.2) ≤
        Cc * Real.exp (Kc * t) * (1 + t) * ε * (((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹)) ∧
      ∀ n (κ : Upper),
        MemH (s - 2) ⇑(cmp (interpD (q n t) i) κ.1.1 κ.1.2 - cmp (Qd t i) κ.1.1 κ.1.2) ∧
        sn (s - 2) ⇑(cmp (interpD (q n t) i) κ.1.1 κ.1.2 - cmp (Qd t i) κ.1.1 κ.1.2) ≤
          Cc * Real.exp (Kc * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ := by
    intro t ht i
    have hdc : ∀ n m (κ : Upper), MemH (s - 2) ⇑(cmp (interpD (q n t) i) κ.1.1 κ.1.2 -
        cmp (interpD (q m t) i) κ.1.1 κ.1.2) ∧
        sn (s - 2) ⇑(cmp (interpD (q n t) i) κ.1.1 κ.1.2 - cmp (interpD (q m t) i) κ.1.1 κ.1.2) ≤
          Cc * Real.exp (Kc * t) * (1 + t) * ε * (((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹) := by
      intro n m κ
      have h := deriv_cauchy (r := s - 2) (q n t) (q m t) i κ
        (w := fun μ ν => cx (comp (q n t) μ ν)) (w' := fun μ ν => cx (comp (q m t) μ ν))
        (by rw [hs1]; exact hmem _ _ _ κ)
      refine ⟨h.1, h.2.trans ?_⟩
      rw [hs1]
      exact (hrate t ht n m κ).1
    obtain ⟨F₀, hF₀, -, hr⟩ := exists_limit_of_rate (F := fun n => interpD (q n t) i)
      (fun n y μ ν => interpD_symm (hsol n t ht).1 i y μ ν) (s - 2) (by omega) _ (hc0 t ht) hdc
    have e : Qd t i = F₀ := tendsto_nhds_unique (tendsto_nhds_limUnder ⟨F₀, hF₀⟩) hF₀
    rw [e]
    exact ⟨hF₀, hdc, hr⟩
  -- second derivatives of `q`
  have hQddL : ∀ t ∈ Set.Icc 0 T, ∀ i j,
      Tendsto (fun n => interpDD (q n t) i j) atTop (𝓝 (Qdd t i j)) ∧
      ∀ n (κ : Upper),
        MemH (s - 3) ⇑(cmp (interpDD (q n t) i j) κ.1.1 κ.1.2 - cmp (Qdd t i j) κ.1.1 κ.1.2) ∧
        sn (s - 3) ⇑(cmp (interpDD (q n t) i j) κ.1.1 κ.1.2 - cmp (Qdd t i j) κ.1.1 κ.1.2) ≤
          Cc * Real.exp (Kc * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ := by
    intro t ht i j
    have hdc : ∀ n m (κ : Upper), MemH (s - 3) ⇑(cmp (interpDD (q n t) i j) κ.1.1 κ.1.2 -
        cmp (interpDD (q m t) i j) κ.1.1 κ.1.2) ∧
        sn (s - 3) ⇑(cmp (interpDD (q n t) i j) κ.1.1 κ.1.2 - cmp (interpDD (q m t) i j) κ.1.1 κ.1.2) ≤
          Cc * Real.exp (Kc * t) * (1 + t) * ε * (((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹) := by
      intro n m κ
      have h := deriv_cauchy (r := s - 3) (q n t) (q m t) i κ
        (w := fun μ ν => PeriodicGridSobolev.Sampling.specD j (cx (comp (q n t) μ ν)))
        (w' := fun μ ν => PeriodicGridSobolev.Sampling.specD j (cx (comp (q m t) μ ν)))
        (by rw [hs2]; exact ((hQdL t ht j).2.1 n m κ).1)
      refine ⟨h.1, h.2.trans ?_⟩
      rw [hs2]
      exact ((hQdL t ht j).2.1 n m κ).2
    obtain ⟨F₀, hF₀, -, hr⟩ := exists_limit_of_rate (F := fun n => interpDD (q n t) i j)
      (fun n y μ ν => interpDD_symm (hsol n t ht).1 i j y μ ν) (s - 3) (by omega) _ (hc0 t ht) hdc
    have e : Qdd t i j = F₀ := tendsto_nhds_unique (tendsto_nhds_limUnder ⟨F₀, hF₀⟩) hF₀
    rw [e]
    exact ⟨hF₀, hr⟩
  -- first derivatives of `v`
  have hVdL : ∀ t ∈ Set.Icc 0 T, ∀ i,
      Tendsto (fun n => interpD (v n t) i) atTop (𝓝 (Vd t i)) ∧
      ∀ n (κ : Upper),
        MemH (s - 3) ⇑(cmp (interpD (v n t) i) κ.1.1 κ.1.2 - cmp (Vd t i) κ.1.1 κ.1.2) ∧
        sn (s - 3) ⇑(cmp (interpD (v n t) i) κ.1.1 κ.1.2 - cmp (Vd t i) κ.1.1 κ.1.2) ≤
          Cc * Real.exp (Kc * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ := by
    intro t ht i
    have hdc : ∀ n m (κ : Upper), MemH (s - 3) ⇑(cmp (interpD (v n t) i) κ.1.1 κ.1.2 -
        cmp (interpD (v m t) i) κ.1.1 κ.1.2) ∧
        sn (s - 3) ⇑(cmp (interpD (v n t) i) κ.1.1 κ.1.2 - cmp (interpD (v m t) i) κ.1.1 κ.1.2) ≤
          Cc * Real.exp (Kc * t) * (1 + t) * ε * (((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹) := by
      intro n m κ
      have h := deriv_cauchy (r := s - 3) (v n t) (v m t) i κ
        (w := fun μ ν => cx (comp (v n t) μ ν)) (w' := fun μ ν => cx (comp (v m t) μ ν))
        (by rw [hs2]; exact hmem _ _ _ κ)
      refine ⟨h.1, h.2.trans ?_⟩
      rw [hs2]
      exact (hrate t ht n m κ).2
    obtain ⟨F₀, hF₀, -, hr⟩ := exists_limit_of_rate (F := fun n => interpD (v n t) i)
      (fun n y μ ν => interpD_symm (hsol n t ht).2.1 i y μ ν) (s - 3) (by omega) _ (hc0 t ht) hdc
    have e : Vd t i = F₀ := tendsto_nhds_unique (tendsto_nhds_limUnder ⟨F₀, hF₀⟩) hF₀
    rw [e]
    exact ⟨hF₀, hr⟩
  refine ⟨Q, V, A, Qd, Vd, Qdd, hQ0, hV0, fun t ht => ?_⟩
  obtain ⟨hQt, hVt, hAt, hQsym, hVsym, hAsym, hrt⟩ := hL t ht
  have hjet : IsContJet (Q t) (V t) (Qd t) (Vd t) (Qdd t) :=
    ⟨fun i => isLineDeriv_of_tendsto (fun n => isLineDeriv_reField i _) hQt (hQdL t ht i).1,
     fun i j => isLineDeriv_of_tendsto (fun n => isLineDeriv_reField i _) (hQdL t ht j).1
       (hQddL t ht i j).1,
     fun i => isLineDeriv_of_tendsto (fun n => isLineDeriv_reField i _) hVt (hVdL t ht i).1⟩
  refine ⟨hQt, hVt, hjet, fun y κ => ?_, fun htI y => ?_, hAt, fun i => (hQdL t ht i).1,
    fun i => (hVdL t ht i).1, fun i j => (hQddL t ht i j).1, hrt, fun n κ i => (hQdL t ht i).2.2 n κ,
    fun n κ i => (hVdL t ht i).2 n κ, fun n κ i j => (hQddL t ht i j).2 n κ⟩
  · -- the row
    -- the limit record is in the chart
    have hQy : ‖Q t y‖ ≤ Cq * ε := by
      have hn : ∀ n, ‖interpRec (q n t) y‖ ≤ Cq * ε := by
        intro n
        refine (norm_le_ccoordSum 2 le_rfl bM hB (interpRec (q n t))
          (fun k => (memH_interpRec _ _ k).1) y).trans ?_
        have h1 := ccoordSum_interpRec_le 2 s (hsol n t ht).1 (v n t) (by omega)
        have h2 : 16 * Real.sqrt (pc 2) * Xnorm s (q n t) (v n t) ≤
            16 * Real.sqrt (pc 2) * ε := by gcongr; exact hXq n t ht
        simp only [Cq]
        have h3 : Real.sqrt cEmb * ccoordSum 2 bM (interpRec (q n t)) ≤
            Real.sqrt cEmb * (16 * Real.sqrt (pc 2) * ε) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (Real.sqrt_nonneg _)
        calc B * (Real.sqrt cEmb * ccoordSum 2 bM (interpRec (q n t)))
            ≤ B * (Real.sqrt cEmb * (16 * Real.sqrt (pc 2) * ε)) := by gcongr
          _ = B * (Real.sqrt cEmb * (16 * Real.sqrt (pc 2))) * ε := by ring
      have hc : Tendsto (fun n => ‖interpRec (q n t) y‖) atTop (𝓝 ‖Q t y‖) :=
        (((continuous_eval_const y).tendsto (Q t)).comp hQt).norm
      exact le_of_tendsto' hc hn
    have hdety : (Matrix.of (minkowski + Q t y)).det ≠ 0 := by
      refine (hdet _ ?_).1
      rw [add_sub_cancel_left]
      refine lt_of_le_of_lt hQy ?_
      have hpos : 0 < 2 * (Cq + 1) := by positivity
      rw [le_div_iff₀ hpos] at hεr
      nlinarith
    -- the jets converge
    set J : ℕ → MetricRec × MetricRec × MetricRec × (Fin 3 → MetricRec) × (Fin 3 → MetricRec) ×
        (Fin 3 → Fin 3 → MetricRec) := fun n =>
      (interpRec (q n t) y, interpRec (v n t) y,
        interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t))) y,
        fun i => interpD (q n t) i y, fun i => interpD (v n t) i y,
        fun i j => interpDD (q n t) i j y)
    have hev : ∀ {F : ℕ → C(T3, MetricRec)} {G : C(T3, MetricRec)}, Tendsto F atTop (𝓝 G) →
        Tendsto (fun n => F n y) atTop (𝓝 (G y)) := fun h =>
      ((continuous_eval_const y).tendsto _).comp h
    have hJ : Tendsto J atTop (𝓝 (Q t y, V t y, A t y, fun i => Qd t i y, fun i => Vd t i y,
        fun i j => Qdd t i j y)) := by
      refine (hev hQt).prodMk_nhds ((hev hVt).prodMk_nhds ((hev hAt).prodMk_nhds
        ((tendsto_pi_nhds.2 fun i => hev (hQdL t ht i).1).prodMk_nhds
          ((tendsto_pi_nhds.2 fun i => hev (hVdL t ht i).1).prodMk_nhds
            (tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hev (hQddL t ht i j).1)))))
    have hrowc := ((continuousAt_rowJet (Q t y, V t y, A t y, fun i => Qd t i y,
      fun i => Vd t i y, fun i j => Qdd t i j y) hdety).tendsto.comp hJ)
    have hcomp : Tendsto (fun n => rowJet (J n) κ.1.1 κ.1.2) atTop
        (𝓝 (rowJet (Q t y, V t y, A t y, fun i => Qd t i y, fun i => Vd t i y,
          fun i j => Qdd t i j y) κ.1.1 κ.1.2)) :=
      ((continuous_apply κ.1.2).tendsto _).comp (((continuous_apply κ.1.1).tendsto _).comp hrowc)
    -- the rows of the interpolants are `O(h)`
    have hsmallrow : ∀ n : ℕ, |rowJet (J n) κ.1.1 κ.1.2| ≤
        Real.sqrt cEmb * (CR * ((n : ℝ) + 1)⁻¹ * ε) := by
      intro n
      obtain ⟨R, hR, hRm, hRs⟩ := hsmall (n + 1) (q n t) (v n t) (hsol n t ht).1 (hsol n t ht).2.1
        ((hXq n t ht).trans hεR) κ
      have h1 : (R y : ℂ) = ((rowJet (J n) κ.1.1 κ.1.2 : ℝ) : ℂ) := by
        rw [hR]; rfl
      have h2 := norm_apply_le_sn (s - 2) (by omega) R hRm y
      rw [h1, Complex.norm_real, Real.norm_eq_abs] at h2
      refine h2.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
      refine hRs.trans ?_
      have := hXq n t ht
      push_cast
      calc CR * ((n : ℝ) + 1)⁻¹ * Xnorm s (q n t) (v n t) ≤ CR * ((n : ℝ) + 1)⁻¹ * ε := by gcongr
        _ = CR * ((n : ℝ) + 1)⁻¹ * ε := rfl
    have hzero : Tendsto (fun n => rowJet (J n) κ.1.1 κ.1.2) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      refine squeeze_zero (fun _ => abs_nonneg _) hsmallrow ?_
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simp only [one_div] at this
      simpa using ((this.const_mul CR).mul_const ε).const_mul (Real.sqrt cEmb)
    exact tendsto_nhds_unique hcomp hzero
  · -- time derivatives in the interior
    have hTpos : 0 ≤ T := le_of_lt (htI.1.trans htI.2)
    set Bt : ℝ := CL * Real.exp (KL * T) * (1 + T) * ε
    have hrateT : ∀ τ ∈ Set.Icc 0 T, ∀ n : ℕ, CL * Real.exp (KL * τ) * (1 + τ) * ε * ((n : ℝ) + 1)⁻¹ ≤
        Bt * ((n : ℝ) + 1)⁻¹ := by
      intro τ hτ n
      have h1 : Real.exp (KL * τ) ≤ Real.exp (KL * T) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ.2 hKL)
      have h2 : (1 + τ) ≤ (1 + T) := by linarith [hτ.2]
      have hn : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
      simp only [Bt]
      have := hτ.1
      gcongr
    have hunif : ∀ {F : ℝ → ℕ → C(T3, MetricRec)} {G : ℝ → C(T3, MetricRec)} (r : ℕ), 2 ≤ r →
        (∀ τ ∈ Set.Icc 0 T, ∀ n y μ ν, F τ n y μ ν = F τ n y ν μ) →
        (∀ τ ∈ Set.Icc 0 T, ∀ y μ ν, G τ y μ ν = G τ y ν μ) →
        (∀ τ ∈ Set.Icc 0 T, ∀ n (κ : Upper),
          MemH r ⇑(cmp (F τ n) κ.1.1 κ.1.2 - cmp (G τ) κ.1.1 κ.1.2) ∧
          sn r ⇑(cmp (F τ n) κ.1.1 κ.1.2 - cmp (G τ) κ.1.1 κ.1.2) ≤
            CL * Real.exp (KL * τ) * (1 + τ) * ε * ((n : ℝ) + 1)⁻¹) →
        TendstoUniformlyOn (fun n τ => F τ n y) (fun τ => G τ y) atTop (Set.Ioo 0 T) := by
      intro F G r hr hFs hGs hFr
      rw [Metric.tendstoUniformlyOn_iff]
      intro η hη
      have hlimit : Tendsto (fun n : ℕ => Real.sqrt cEmb * (Bt * ((n : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simp only [one_div] at this
        simpa using (this.const_mul Bt).const_mul (Real.sqrt cEmb)
      filter_upwards [(Metric.tendsto_nhds.mp hlimit) η hη] with n hn τ hτ
      have hτ' : τ ∈ Set.Icc 0 T := Set.Ioo_subset_Icc_self hτ
      rw [dist_comm, dist_eq_norm]
      have hsup := norm_sub_le_of_upper (F τ n) (G τ) (hFs τ hτ' n) (hGs τ hτ') (B := Bt * ((n : ℝ) + 1)⁻¹)
        fun κ => ⟨memH_mono hr (hFr τ hτ' n κ).1, (sn_mono' hr (hFr τ hτ' n κ).1).trans
          ((hFr τ hτ' n κ).2.trans (hrateT τ hτ' n))⟩
      have h1 : ‖F τ n y - G τ y‖ ≤ ‖F τ n - G τ‖ := by
        rw [← ContinuousMap.sub_apply]; exact (F τ n - G τ).norm_coe_le_norm y
      have h2 : Real.sqrt cEmb * (Bt * ((n : ℝ) + 1)⁻¹) < η := by
        rw [Real.dist_eq, sub_zero] at hn
        exact lt_of_le_of_lt (le_abs_self _) hn
      linarith
    constructor
    · refine hasDerivAt_of_tendstoUniformlyOn (f := fun n τ => interpRec (q n τ) y) isOpen_Ioo
        (hunif (F := fun τ n => interpRec (v n τ)) (G := V) (s - 2) (by omega)
          (fun τ hτ n => interpRec_symm (hsol n τ hτ).2.1) (fun τ hτ => (hL τ hτ).2.2.2.2.1)
          (fun τ hτ n κ => ((hL τ hτ).2.2.2.2.2.2 n κ).2.1))
        (Eventually.of_forall fun n τ hτ =>
          hasDerivAt_interpRec ((hsol n τ (Set.Ioo_subset_Icc_self hτ)).2.2.1) y)
        (fun τ hτ => ((continuous_eval_const y).tendsto _).comp
          (hL τ (Set.Ioo_subset_Icc_self hτ)).1) htI
    · refine hasDerivAt_of_tendstoUniformlyOn (f := fun n τ => interpRec (v n τ) y) isOpen_Ioo
        (hunif (F := fun τ n => interpRec (symRec (harmonicWriterAcceleration (q n τ) (v n τ))))
          (G := A) (s - 3) (by omega)
          (fun τ hτ n => interpRec_symRec_symm _) (fun τ hτ => (hL τ hτ).2.2.2.2.2.1)
          (fun τ hτ n κ => by
            rw [cmp_interpRec_symRec]; exact ((hL τ hτ).2.2.2.2.2.2 n κ).2.2))
        (Eventually.of_forall fun n τ hτ => ?_)
        (fun τ hτ => ((continuous_eval_const y).tendsto _).comp
          (hL τ (Set.Ioo_subset_Icc_self hτ)).2.1) htI
      have hτ' := Set.Ioo_subset_Icc_self hτ
      have h := hasDerivAt_interpRec_symRec (u := v n)
        (u' := harmonicWriterAcceleration (q n τ) (v n τ)) (t := τ) (hsol n τ hτ').2.2.2 y
      refine h.congr_of_eventuallyEq ?_
      have hnhds : Set.Ioo 0 T ∈ 𝓝 τ := isOpen_Ioo.mem_nhds hτ
      filter_upwards [hnhds] with σ hσ
      rw [symRec_of_isSymRec (hsol n σ (Set.Ioo_subset_Icc_self hσ)).2.1]

/-! ### The curvature of the limit and the curvature rate -/

/-- The pointwise space-time 2-jet `(q, v, w, ∂q, ∂v, ∂²q)` of `g = η + q`
(`v = ∂ₜq`, `w = ∂ₜ²q`). -/
abbrev PJet := MetricRec × MetricRec × MetricRec × (Fin 3 → MetricRec) × (Fin 3 → MetricRec) ×
  (Fin 3 → Fin 3 → MetricRec)

/-- `∂_d g_{ej}`: `∂₀ g = v`, `∂_{i+1} g = ∂ᵢ q`. -/
def dgOf (z : PJet) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  Fin.cons (α := fun _ => Fin 4 → Fin 4 → ℝ) z.2.1 z.2.2.2.1

/-- `∂_d ∂_k g_{ej}`: `∂₀∂₀ g = w`, `∂₀∂_{i+1} g = ∂_{i+1}∂₀ g = ∂ᵢ v`, `∂_{i+1}∂_{j+1} g = ∂ᵢ∂ⱼ q`. -/
def ddgOf (z : PJet) : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  Fin.cons (α := fun _ => Fin 4 → Fin 4 → Fin 4 → ℝ)
    (Fin.cons (α := fun _ => Fin 4 → Fin 4 → ℝ) z.2.2.1 z.2.2.2.2.1)
    (fun i => Fin.cons (α := fun _ => Fin 4 → Fin 4 → ℝ) (z.2.2.2.2.1 i) (z.2.2.2.2.2 i))

/-- `∂_d g^{ce} = -Σ g^{cf} ∂_d g_{fk} g^{ke}`. -/
def dInvOf (ginv : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun d c e => -∑ f, ∑ k, ginv c f * dg d f k * ginv k e

/-- `∂_d Γ^c_{ij}` from the 2-jet (product rule applied to `christoffel`). -/
def dChrOf (ginv : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (ddg : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun d c i j => (1 / 2) * ∑ e, (dInvOf ginv dg d c e * (dg i e j + dg j e i - dg e i j) +
    ginv c e * (ddg d i e j + ddg d j e i - ddg d e i j))

/-- The coordinate Riemann tensor `R^a_{bcd}` (`CoordinateCurvature.riemann`) of the space-time
metric `g = η + q` with the 2-jet `z` (`Γ = christoffel g⁻¹ ∂g`, `∂Γ = dChrOf`, the inverse taken at
matrix type). -/
def riemOf (z : PJet) : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  riemann (christoffel (recInv (minkowski + z.1)) (dgOf z))
    (dChrOf (recInv (minkowski + z.1)) (dgOf z) (ddgOf z))

theorem analyticAt_riemOf (a b c d : Fin 4) (z₀ : PJet)
    (hdet : (Matrix.of (minkowski + z₀.1)).det ≠ 0) :
    AnalyticAt ℝ (fun z : PJet => riemOf z a b c d) z₀ := by
  have hg : AnalyticAt ℝ (fun z : PJet => minkowski + z.1) z₀ := by fun_prop
  have hinv : AnalyticAt ℝ (fun z : PJet => recInv (minkowski + z.1)) z₀ := by
    refine AnalyticAt.pi fun i => AnalyticAt.pi fun j => ?_
    exact (analyticAt_inv_entry _ hdet i j).comp_of_eq hg rfl
  have hdg : AnalyticAt ℝ (fun z : PJet => dgOf z) z₀ := by
    refine AnalyticAt.pi fun α => ?_
    refine Fin.cases ?_ (fun i => ?_) α
    · simp only [dgOf, Fin.cons_zero]; fun_prop
    · simp only [dgOf, Fin.cons_succ]; fun_prop
  have hddg : AnalyticAt ℝ (fun z : PJet => ddgOf z) z₀ := by
    refine AnalyticAt.pi fun α => ?_
    refine Fin.cases ?_ (fun i => ?_) α
    · refine AnalyticAt.pi fun β => ?_
      refine Fin.cases ?_ (fun j => ?_) β
      · simp only [ddgOf, Fin.cons_zero]; fun_prop
      · simp only [ddgOf, Fin.cons_zero, Fin.cons_succ]; fun_prop
    · refine AnalyticAt.pi fun β => ?_
      refine Fin.cases ?_ (fun j => ?_) β
      · simp only [ddgOf, Fin.cons_succ, Fin.cons_zero]; fun_prop
      · simp only [ddgOf, Fin.cons_succ]; fun_prop
  have hpoly : ∀ J : (Fin 4 → Fin 4 → ℝ) × (Fin 4 → Fin 4 → Fin 4 → ℝ) ×
      (Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ), AnalyticAt ℝ (fun J : (Fin 4 → Fin 4 → ℝ) ×
        (Fin 4 → Fin 4 → Fin 4 → ℝ) × (Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) =>
        riemann (christoffel J.1 J.2.1) (dChrOf J.1 J.2.1 J.2.2) a b c d) J := by
    intro J
    simp only [riemann, christoffel, dChrOf, dInvOf]
    fun_prop
  have := (hpoly _).comp (hinv.prod (hdg.prod hddg))
  simpa [riemOf, Function.comp_def] using this

/-- A basis of the pointwise jet space. -/
def bPJ : Module.Basis ((Σ _ : Fin 4, Fin 4) ⊕ ((Σ _ : Fin 4, Fin 4) ⊕ ((Σ _ : Fin 4, Fin 4) ⊕
    ((Σ _ : Fin 3, Σ _ : Fin 4, Fin 4) ⊕ ((Σ _ : Fin 3, Σ _ : Fin 4, Fin 4) ⊕
      (Σ _ : Fin 3, Σ _ : Fin 3, Σ _ : Fin 4, Fin 4)))))) ℝ PJet :=
  bM.prod (bM.prod (bM.prod ((Pi.basis fun _ : Fin 3 => bM).prod ((Pi.basis fun _ : Fin 3 => bM).prod
    (Pi.basis fun _ : Fin 3 => Pi.basis fun _ : Fin 3 => bM)))))

/-- The jet field `y ↦ (Q, V, W, ∂Q, ∂V, ∂²Q)(y)`. -/
def pjetField (Q V W : C(T3, MetricRec)) (Qd Vd : Fin 3 → C(T3, MetricRec))
    (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) : C(T3, PJet) :=
  ⟨fun y => (Q y, V y, W y, fun i => Qd i y, fun i => Vd i y, fun i j => Qdd i j y), by
    refine Q.continuous.prodMk (V.continuous.prodMk (W.continuous.prodMk
      ((continuous_pi fun i => (Qd i).continuous).prodMk ((continuous_pi fun i => (Vd i).continuous).prodMk
        (continuous_pi fun i => continuous_pi fun j => (Qdd i j).continuous)))))⟩

theorem pjetField_sub (Q V W Q' V' W' : C(T3, MetricRec)) (Qd Vd Qd' Vd' : Fin 3 → C(T3, MetricRec))
    (Qdd Qdd' : Fin 3 → Fin 3 → C(T3, MetricRec)) :
    pjetField Q V W Qd Vd Qdd - pjetField Q' V' W' Qd' Vd' Qdd' =
      pjetField (Q - Q') (V - V') (W - W') (Qd - Qd') (Vd - Vd') (Qdd - Qdd') := by
  ext y <;> simp [pjetField]

theorem ccoordSum_pjetField (r : ℕ) (Q V W : C(T3, MetricRec)) (Qd Vd : Fin 3 → C(T3, MetricRec))
    (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) :
    ccoordSum r bPJ (pjetField Q V W Qd Vd Qdd) =
      ccoordSum r bM Q + ccoordSum r bM V + ccoordSum r bM W + ∑ i, ccoordSum r bM (Qd i) +
        ∑ i, ccoordSum r bM (Vd i) + ∑ i, ∑ j, ccoordSum r bM (Qdd i j) := by
  unfold ccoordSum
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma]
  have e1 : ∀ k, ccoord bPJ (pjetField Q V W Qd Vd Qdd) (Sum.inl k) = ccoord bM Q k := by
    intro k; ext y; simp [ccoord_apply, bPJ, Module.Basis.prod_repr_inl, pjetField]
  have e2 : ∀ k, ccoord bPJ (pjetField Q V W Qd Vd Qdd) (Sum.inr (Sum.inl k)) = ccoord bM V k := by
    intro k; ext y; simp [ccoord_apply, bPJ, Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
      pjetField]
  have e3 : ∀ k, ccoord bPJ (pjetField Q V W Qd Vd Qdd) (Sum.inr (Sum.inr (Sum.inl k))) =
      ccoord bM W k := by
    intro k; ext y; simp [ccoord_apply, bPJ, Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
      pjetField]
  have e4 : ∀ i k, ccoord bPJ (pjetField Q V W Qd Vd Qdd)
      (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k⟩)))) = ccoord bM (Qd i) k := by
    intro i k; ext y; simp [ccoord_apply, bPJ, Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
      Pi.basis_repr, pjetField]
  have e5 : ∀ i k, ccoord bPJ (pjetField Q V W Qd Vd Qdd)
      (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k⟩))))) = ccoord bM (Vd i) k := by
    intro i k; ext y; simp [ccoord_apply, bPJ, Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
      Pi.basis_repr, pjetField]
  have e6 : ∀ i j k, ccoord bPJ (pjetField Q V W Qd Vd Qdd)
      (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨i, ⟨j, k⟩⟩))))) = ccoord bM (Qdd i j) k := by
    intro i j k; ext y; simp [ccoord_apply, bPJ, Module.Basis.prod_repr_inr, Pi.basis_repr, pjetField]
  simp only [e1, e2, e3, e4, e5, e6]
  ring

/-- For symmetric record fields, the coordinate size of a difference is controlled by its upper
components. -/
theorem ccoordSum_sub_le_of_upper (r : ℕ) (F G : C(T3, MetricRec)) (hF : ∀ y μ ν, F y μ ν = F y ν μ)
    (hG : ∀ y μ ν, G y μ ν = G y ν μ) {B : ℝ}
    (h : ∀ κ : Upper, MemH r ⇑(cmp F κ.1.1 κ.1.2 - cmp G κ.1.1 κ.1.2) ∧
      sn r ⇑(cmp F κ.1.1 κ.1.2 - cmp G κ.1.1 κ.1.2) ≤ B) :
    (∀ k, MemH r ⇑(ccoord bM (F - G) k)) ∧ ccoordSum r bM (F - G) ≤ 16 * B := by
  have hup : ∀ k : Σ _ : Fin 4, Fin 4, ccoord bM (F - G) k =
      cmp F (upperOf k.1 k.2).1.1 (upperOf k.1 k.2).1.2 -
        cmp G (upperOf k.1 k.2).1.1 (upperOf k.1 k.2).1.2 := by
    intro k
    rw [ccoord_bM, cmp_sub]
    ext y
    simp only [ContinuousMap.sub_apply, cmp_apply, upperOf]
    split_ifs
    · rfl
    · rw [hF y k.1 k.2, hG y k.1 k.2]
  refine ⟨fun k => by rw [hup]; exact (h _).1, ?_⟩
  unfold ccoordSum
  calc ∑ k, sn r ⇑(ccoord bM (F - G) k) ≤ ∑ _k : Σ _ : Fin 4, Fin 4, B :=
        sum_le_sum fun k _ => by rw [hup]; exact (h _).2
    _ = 16 * B := by simp

/-- `F = G - (G - F)`: membership of a limit from an approximant and a difference. -/
theorem memH_of_sub {r : ℕ} {F G : CT} (hG : MemH r ⇑G) (hGF : MemH r ⇑(G - F)) : MemH r ⇑F := by
  have := memH_sub hG hGF
  simpa using this

theorem memH_pjetField {r : ℕ} {Q V W : C(T3, MetricRec)} {Qd Vd : Fin 3 → C(T3, MetricRec)}
    {Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)} (hQ : ∀ k, MemH r ⇑(ccoord bM Q k))
    (hV : ∀ k, MemH r ⇑(ccoord bM V k)) (hW : ∀ k, MemH r ⇑(ccoord bM W k))
    (hQd : ∀ i k, MemH r ⇑(ccoord bM (Qd i) k)) (hVd : ∀ i k, MemH r ⇑(ccoord bM (Vd i) k))
    (hQdd : ∀ i j k, MemH r ⇑(ccoord bM (Qdd i j) k)) :
    ∀ j, MemH r ⇑(ccoord bPJ (pjetField Q V W Qd Vd Qdd) j) := by
  rintro (k | k | k | ⟨i, k⟩ | ⟨i, k⟩ | ⟨i, j, k⟩)
  · have e : ccoord bPJ (pjetField Q V W Qd Vd Qdd) (Sum.inl k) = ccoord bM Q k := by
      ext y; simp [ccoord_apply, bPJ, Module.Basis.prod_repr_inl, pjetField]
    rw [e]; exact hQ k
  · have e : ccoord bPJ (pjetField Q V W Qd Vd Qdd) (Sum.inr (Sum.inl k)) = ccoord bM V k := by
      ext y; simp [ccoord_apply, bPJ, Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
        pjetField]
    rw [e]; exact hV k
  · have e : ccoord bPJ (pjetField Q V W Qd Vd Qdd) (Sum.inr (Sum.inr (Sum.inl k))) =
        ccoord bM W k := by
      ext y; simp [ccoord_apply, bPJ, Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
        pjetField]
    rw [e]; exact hW k
  · have e : ccoord bPJ (pjetField Q V W Qd Vd Qdd)
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k⟩)))) = ccoord bM (Qd i) k := by
      ext y; simp [ccoord_apply, bPJ, Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
        Pi.basis_repr, pjetField]
    rw [e]; exact hQd i k
  · have e : ccoord bPJ (pjetField Q V W Qd Vd Qdd)
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k⟩))))) = ccoord bM (Vd i) k := by
      ext y; simp [ccoord_apply, bPJ, Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
        Pi.basis_repr, pjetField]
    rw [e]; exact hVd i k
  · have e : ccoord bPJ (pjetField Q V W Qd Vd Qdd)
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨i, ⟨j, k⟩⟩))))) = ccoord bM (Qdd i j) k := by
      ext y; simp [ccoord_apply, bPJ, Module.Basis.prod_repr_inr, Pi.basis_repr, pjetField]
    rw [e]; exact hQdd i j k

theorem symm_of_tendsto {F : ℕ → C(T3, MetricRec)} {G : C(T3, MetricRec)}
    (hF : ∀ n y μ ν, F n y μ ν = F n y ν μ) (h : Tendsto F atTop (𝓝 G)) (y : T3) (μ ν : Fin 4) :
    G y μ ν = G y ν μ := by
  have hc : ∀ a b : Fin 4, Continuous fun H : C(T3, MetricRec) => H y a b := fun a b =>
    (continuous_apply b).comp ((continuous_apply a).comp (continuous_eval_const y))
  have h1 : Tendsto (fun n => F n y μ ν) atTop (𝓝 (G y μ ν)) := (hc μ ν).continuousAt.tendsto.comp h
  have h2 : Tendsto (fun n => F n y ν μ) atTop (𝓝 (G y ν μ)) := (hc ν μ).continuousAt.tendsto.comp h
  simp only [hF _ y μ ν] at h1
  exact tendsto_nhds_unique h1 h2

theorem memH_ccoord_of_upper {r : ℕ} {F : C(T3, MetricRec)} (hF : ∀ y μ ν, F y μ ν = F y ν μ)
    (h : ∀ κ : Upper, MemH r ⇑(cmp F κ.1.1 κ.1.2)) : ∀ k, MemH r ⇑(ccoord bM F k) := by
  intro k
  rw [ccoord_bM]
  have e : cmp F k.1 k.2 = cmp F (upperOf k.1 k.2).1.1 (upperOf k.1 k.2).1.2 := by
    ext y
    simp only [cmp_apply, upperOf]
    split_ifs
    · rfl
    · rw [hF y k.1 k.2]
  rw [e]; exact h _

/-- **`thm:supp-open-einstein` without the vacuum clause**: the conclusions of
`writer_limit_solves` (whole-sequence convergence of the interpolated writer solutions, the limit is
a classical solution of the ten-component harmonic reduced equation, the metric rate
`eq:supp-open-metric-rate`) together with the **curvature rate** `eq:supp-open-curvature-rate`:
for every time `t ∈ [0, T]` and every mesh, the coordinate Riemann tensor of the interpolant 2-jet
(`g_h = η + 𝓘_h q`, `∂ₜg_h = 𝓘_h v`, `∂ₜ²g_h = 𝓘_h ∂ₜv`, spatial derivatives of the interpolants)
differs from the Riemann tensor of the 2-jet of the limit by at most `C e^{Kt}(1 + t) h ε` in
`H^{s-3}` (every component). -/
theorem writer_limit_curvature_rate (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∃ C ≥ 0, ∀ (T : ℝ) (q v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec)
      (Q₀ V₀ : C(T3, MetricRec)) (ε : ℝ),
      (∀ n, IsWriterSolution T (q n) (v n)) →
      (∀ n, q n 0 = sampleRec (n + 1) ⇑Q₀) → (∀ n, v n 0 = sampleRec (n + 1) ⇑V₀) →
      (∀ y μ ν, Q₀ y μ ν = Q₀ y ν μ) → (∀ y μ ν, V₀ y μ ν = V₀ y ν μ) →
      (∀ k, MemH (s + 1) ⇑(ccoord bM Q₀ k)) → (∀ k, MemH s ⇑(ccoord bM V₀ k)) →
      contTop s Q₀ V₀ ≤ ε → (∀ n, ∀ t ∈ Set.Icc 0 T, Xnorm s (q n t) (v n t) ≤ ε) → ε ≤ δ →
      ∃ (Q V A : ℝ → C(T3, MetricRec)) (Qd Vd : ℝ → Fin 3 → C(T3, MetricRec))
        (Qdd : ℝ → Fin 3 → Fin 3 → C(T3, MetricRec)), Q 0 = Q₀ ∧ V 0 = V₀ ∧
        ∀ t ∈ Set.Icc 0 T,
          Tendsto (fun n => interpRec (q n t)) atTop (𝓝 (Q t)) ∧
          Tendsto (fun n => interpRec (v n t)) atTop (𝓝 (V t)) ∧
          IsContJet (Q t) (V t) (Qd t) (Vd t) (Qdd t) ∧
          (∀ y (κ : Upper), normalRow (Q t y) (V t y) (A t y) (fun i => Qd t i y)
            (fun i => Vd t i y) (fun i j => Qdd t i j y) κ.1.1 κ.1.2 = 0) ∧
          (t ∈ Set.Ioo 0 T → ∀ y, HasDerivAt (fun τ => Q τ y) (V t y) t ∧
            HasDerivAt (fun τ => V τ y) (A t y) t) ∧
          (∀ n (κ : Upper),
            sn (s - 1) ⇑(cmp (interpRec (q n t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2) ≤
              C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ ∧
            sn (s - 2) ⇑(cmp (interpRec (v n t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2) ≤
              C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ ∧
            sn (s - 3) ⇑(cmp (interpRec (harmonicWriterAcceleration (q n t) (v n t))) κ.1.1 κ.1.2 -
              cmp (A t) κ.1.1 κ.1.2) ≤ C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹) ∧
          ∀ n (a b c d : Fin 4), ∃ F : CT,
            (∀ y, F y = ((riemOf (pjetField (interpRec (q n t)) (interpRec (v n t))
                (interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t))))
                (interpD (q n t)) (interpD (v n t)) (interpDD (q n t)) y) a b c d -
              riemOf (pjetField (Q t) (V t) (A t) (Qd t) (Vd t) (Qdd t) y) a b c d : ℝ) : ℂ)) ∧
            MemH (s - 3) ⇑F ∧ sn (s - 3) ⇑F ≤ C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ := by
  obtain ⟨δW, hδW, K₁, hK₁, C₁, hC₁, K₂, hK₂, C₂, hC₂, hW⟩ := writer_limit_solves s hs
  obtain ⟨δA, hδA, KA, hKA, hacc⟩ := accel_bound s (by omega)
  -- the Lipschitz Moser estimate for the Riemann map, uniform over the indices
  have hR : ∀ e : Fin 4 × Fin 4 × Fin 4 × Fin 4, ∃ δ > 0, ∃ C ≥ 0, ∀ P P' : C(T3, PJet),
      (∀ j, MemH (s - 3) ⇑(ccoord bPJ P j)) → (∀ j, MemH (s - 3) ⇑(ccoord bPJ P' j)) →
      ccoordSum (s - 3) bPJ P ≤ δ → ccoordSum (s - 3) bPJ P' ≤ δ →
      ∃ F : CT, (∀ y, F y = ((riemOf (P y) e.1 e.2.1 e.2.2.1 e.2.2.2 -
        riemOf (P' y) e.1 e.2.1 e.2.2.1 e.2.2.2 : ℝ) : ℂ)) ∧ MemH (s - 3) ⇑F ∧
        sn (s - 3) ⇑F ≤ C * ccoordSum (s - 3) bPJ (P - P') := by
    intro e
    have hdet0 : (Matrix.of (minkowski + (0 : PJet).1)).det ≠ 0 := by
      simpa using det_minkowski_ne
    obtain ⟨p, R, hp⟩ := analyticAt_riemOf e.1 e.2.1 e.2.2.1 e.2.2.2 0 hdet0
    obtain ⟨δ, hδ, C, hC, hm⟩ := cont_moser_lipschitz (s - 3) (by omega) bPJ hp
    refine ⟨δ, hδ, C, hC, fun P P' hP hP' h1 h2 => ?_⟩
    obtain ⟨F, hF, hFm, hFs⟩ := hm P P' hP hP' h1 h2
    exact ⟨F, fun y => by rw [hF y]; simp, hFm, hFs⟩
  choose δR hδR CR hCR hRm using hR
  set δR0 : ℝ := (univ : Finset (Fin 4 × Fin 4 × Fin 4 × Fin 4)).inf' univ_nonempty δR
  have hδR0 : 0 < δR0 := by rw [Finset.lt_inf'_iff]; intro e _; exact hδR e
  have hδR0le : ∀ e, δR0 ≤ δR e := fun e => Finset.inf'_le _ (mem_univ e)
  set CR0 : ℝ := ∑ e, CR e
  have hCR0 : ∀ e, CR e ≤ CR0 := fun e =>
    single_le_sum (f := CR) (fun e _ => hCR e) (mem_univ e)
  have hCR0n : 0 ≤ CR0 := sum_nonneg fun e _ => hCR e
  clear_value δR0 CR0
  -- sizes
  set r := s - 3 with hrdef
  set S : ℝ := 16 * (Real.sqrt (pc r) * (2 + KA) + 6 * Real.sqrt (pc (r + 1)) + 9 * Real.sqrt (pc (r + 2)))
  have hS : 0 ≤ S := by
    simp only [S]
    exact mul_nonneg (by norm_num) (add_nonneg (add_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (by linarith)) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
  set δ : ℝ := min (min δW δA) (δR0 / (S + 1))
  have hδ : 0 < δ := lt_min (lt_min hδW hδA) (div_pos hδR0 (by linarith))
  set K : ℝ := K₁ + K₂
  set C : ℝ := C₁ + C₂ + CR0 * 16 * (3 * C₁ + 15 * C₂)
  have hKnn : 0 ≤ K := add_nonneg hK₁ hK₂
  have hCnn : 0 ≤ C := add_nonneg (add_nonneg hC₁ hC₂)
    (mul_nonneg (mul_nonneg hCR0n (by norm_num)) (by linarith))
  refine ⟨δ, hδ, K, hKnn, C, hCnn,
    fun T q v Q₀ V₀ ε hsol hq0 hv0 hQs hVs hQ hV hX0 hXq hεδ => ?_⟩
  have hε0 : 0 ≤ ε := (contTop_nonneg _ _ _).trans hX0
  obtain ⟨Q, V, A, Qd, Vd, Qdd, hQ0, hV0, hP⟩ := hW T q v Q₀ V₀ ε hsol hq0 hv0 hQs hVs hQ hV hX0 hXq
    (hεδ.trans ((min_le_left _ _).trans (min_le_left _ _)))
  refine ⟨Q, V, A, Qd, Vd, Qdd, hQ0, hV0, fun t ht => ?_⟩
  obtain ⟨hQt, hVt, hjet, hrow, hder, hAt, hQdt, hVdt, hQddt, hr1, hrQd, hrVd, hrQdd⟩ := hP t ht
  have hexp1 : Real.exp (K₁ * t) ≤ Real.exp (K * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by simp [K]; linarith) ht.1)
  have hexp2 : Real.exp (K₂ * t) ≤ Real.exp (K * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by simp [K]; linarith) ht.1)
  have hfac0 : ∀ n : ℕ, 0 ≤ (1 + t) * ε * ((n : ℝ) + 1)⁻¹ := fun n =>
    mul_nonneg (mul_nonneg (by linarith [ht.1]) hε0)
      (inv_nonneg.mpr (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
  -- symmetries
  have hsq : ∀ n, IsSymRec (q n t) := fun n => (hsol n t ht).1
  have hsv : ∀ n, IsSymRec (v n t) := fun n => (hsol n t ht).2.1
  have hQsym := symm_of_tendsto (fun n y μ ν => interpRec_symm (hsq n) y μ ν) hQt
  have hVsym := symm_of_tendsto (fun n y μ ν => interpRec_symm (hsv n) y μ ν) hVt
  have hAsym := symm_of_tendsto (fun n y μ ν => interpRec_symRec_symm _ y μ ν) hAt
  have hQdsym := fun i => symm_of_tendsto (fun n y μ ν => interpD_symm (hsq n) i y μ ν) (hQdt i)
  have hVdsym := fun i => symm_of_tendsto (fun n y μ ν => interpD_symm (hsv n) i y μ ν) (hVdt i)
  have hQddsym := fun i j => symm_of_tendsto (fun n y μ ν => interpDD_symm (hsq n) i j y μ ν)
    (hQddt i j)
  -- the jet fields
  set Jn : ℕ → C(T3, PJet) := fun n => pjetField (interpRec (q n t)) (interpRec (v n t))
    (interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t))))
    (interpD (q n t)) (interpD (v n t)) (interpDD (q n t))
  set J : C(T3, PJet) := pjetField (Q t) (V t) (A t) (Qd t) (Vd t) (Qdd t)
  -- derivative-slot bounds for interpolants
  have hderQ : ∀ n i (k : Σ _ : Fin 4, Fin 4) (r' : ℕ), MemH r' ⇑(ccoord bM (interpD (q n t) i) k) ∧
      sn r' ⇑(ccoord bM (interpD (q n t) i) k) ≤ sn (r' + 1) ⇑(ccoord bM (interpRec (q n t)) k) := by
    intro n i k r'
    rw [ccoord_bM, ccoord_bM]
    exact memH_of_isLineDeriv (isLineDeriv_cmp (isLineDeriv_reField i _) k.1 k.2)
      (memH_cmp_reField _ _ _ _).1
  have hderV : ∀ n i (k : Σ _ : Fin 4, Fin 4) (r' : ℕ), MemH r' ⇑(ccoord bM (interpD (v n t) i) k) ∧
      sn r' ⇑(ccoord bM (interpD (v n t) i) k) ≤ sn (r' + 1) ⇑(ccoord bM (interpRec (v n t)) k) := by
    intro n i k r'
    rw [ccoord_bM, ccoord_bM]
    exact memH_of_isLineDeriv (isLineDeriv_cmp (isLineDeriv_reField i _) k.1 k.2)
      (memH_cmp_reField _ _ _ _).1
  have hderQQ : ∀ n i j (k : Σ _ : Fin 4, Fin 4) (r' : ℕ),
      MemH r' ⇑(ccoord bM (interpDD (q n t) i j) k) ∧
      sn r' ⇑(ccoord bM (interpDD (q n t) i j) k) ≤ sn (r' + 1) ⇑(ccoord bM (interpD (q n t) j) k) := by
    intro n i j k r'
    rw [ccoord_bM, ccoord_bM]
    exact memH_of_isLineDeriv (isLineDeriv_cmp (isLineDeriv_reField i _) k.1 k.2)
      (memH_cmp_reField _ _ _ _).1
  have hsum16 : ∀ (f : (Σ _ : Fin 4, Fin 4) → ℝ) (B : ℝ), (∀ k, f k ≤ B) → ∑ k, f k ≤ 16 * B :=
    fun f B h => (sum_le_sum fun k _ => h k).trans (by simp)
  have hJnS : ∀ n, ccoordSum r bPJ (Jn n) ≤ S * ε := by
    intro n
    have X := hXq n t ht
    have hX0' := Xnorm_nonneg s (q n t) (v n t)
    simp only [Jn]
    rw [ccoordSum_pjetField]
    have b1 := ccoordSum_interpRec_le r s (hsq n) (v n t) (by omega)
    have b2 := ccoordSum_interpRec_v_le r s (q n t) (hsv n) (by omega)
    have b3 : ccoordSum r bM (interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t)))) ≤
        16 * (Real.sqrt (pc r) * (KA * Xnorm s (q n t) (v n t))) := by
      unfold ccoordSum
      refine hsum16 _ _ fun k => (memH_interpRec r _ k).2.trans
        (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
      rw [comp_symRec_eq]
      exact (PeriodicGridSobolev.Moser.sobNorm_mono (by omega) _).trans
        (hacc (n + 1) (q n t) (v n t) (hsq n) (hsv n)
          ((hXq n t ht).trans (hεδ.trans ((min_le_left _ _).trans (min_le_right _ _)))) _ _)
    have b4 : ∀ i, ccoordSum r bM (interpD (q n t) i) ≤
        16 * Real.sqrt (pc (r + 1)) * Xnorm s (q n t) (v n t) := fun i =>
      (sum_le_sum fun k _ => (hderQ n i k r).2).trans
        (ccoordSum_interpRec_le (r + 1) s (hsq n) (v n t) (by omega))
    have b5 : ∀ i, ccoordSum r bM (interpD (v n t) i) ≤
        16 * Real.sqrt (pc (r + 1)) * Xnorm s (q n t) (v n t) := fun i =>
      (sum_le_sum fun k _ => (hderV n i k r).2).trans
        (ccoordSum_interpRec_v_le (r + 1) s (q n t) (hsv n) (by omega))
    have b6 : ∀ i j, ccoordSum r bM (interpDD (q n t) i j) ≤
        16 * Real.sqrt (pc (r + 2)) * Xnorm s (q n t) (v n t) := fun i j =>
      (sum_le_sum fun k _ => (hderQQ n i j k r).2).trans
        ((sum_le_sum fun k _ => (hderQ n j k (r + 1)).2).trans
          (ccoordSum_interpRec_le (r + 2) s (hsq n) (v n t) (by omega)))
    have s4 : ∑ i, ccoordSum r bM (interpD (q n t) i) ≤
        3 * (16 * Real.sqrt (pc (r + 1)) * Xnorm s (q n t) (v n t)) :=
      (sum_le_sum fun i _ => b4 i).trans (by simp)
    have s5 : ∑ i, ccoordSum r bM (interpD (v n t) i) ≤
        3 * (16 * Real.sqrt (pc (r + 1)) * Xnorm s (q n t) (v n t)) :=
      (sum_le_sum fun i _ => b5 i).trans (by simp)
    have s6 : ∑ i, ∑ j, ccoordSum r bM (interpDD (q n t) i j) ≤
        9 * (16 * Real.sqrt (pc (r + 2)) * Xnorm s (q n t) (v n t)) :=
      (sum_le_sum fun i _ => sum_le_sum fun j _ => b6 i j).trans (by simp; ring_nf; rfl)
    have hSX : (16 * Real.sqrt (pc r) * Xnorm s (q n t) (v n t)) +
        (16 * Real.sqrt (pc r) * Xnorm s (q n t) (v n t)) +
        16 * (Real.sqrt (pc r) * (KA * Xnorm s (q n t) (v n t))) +
        3 * (16 * Real.sqrt (pc (r + 1)) * Xnorm s (q n t) (v n t)) +
        3 * (16 * Real.sqrt (pc (r + 1)) * Xnorm s (q n t) (v n t)) +
        9 * (16 * Real.sqrt (pc (r + 2)) * Xnorm s (q n t) (v n t)) = S * Xnorm s (q n t) (v n t) := by
      simp only [S]; ring
    have := mul_le_mul_of_nonneg_left X hS
    linarith
  -- the rates of each slot (upper components)
  set ρ₁ : ℕ → ℝ := fun n => C₁ * Real.exp (K₁ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹
  set ρ₂ : ℕ → ℝ := fun n => C₂ * Real.exp (K₂ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹
  have hρ₁ : ∀ n, 0 ≤ ρ₁ n := fun n => by
    have e : ρ₁ n = (C₁ * Real.exp (K₁ * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by
      simp only [ρ₁]; ring
    rw [e]; exact mul_nonneg (mul_nonneg hC₁ (Real.exp_pos _).le) (hfac0 n)
  have hρ₂ : ∀ n, 0 ≤ ρ₂ n := fun n => by
    have e : ρ₂ n = (C₂ * Real.exp (K₂ * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by
      simp only [ρ₂]; ring
    rw [e]; exact mul_nonneg (mul_nonneg hC₂ (Real.exp_pos _).le) (hfac0 n)
  have hdiff : ∀ n, (∀ j, MemH r ⇑(ccoord bPJ (Jn n - J) j)) ∧
      ccoordSum r bPJ (Jn n - J) ≤ 16 * (3 * ρ₁ n + 15 * ρ₂ n) := by
    intro n
    have eJ : Jn n - J = pjetField (interpRec (q n t) - Q t) (interpRec (v n t) - V t)
        (interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t))) - A t)
        (interpD (q n t) - Qd t) (interpD (v n t) - Vd t) (interpDD (q n t) - Qdd t) :=
      pjetField_sub _ _ _ _ _ _ _ _ _ _ _ _
    obtain ⟨m1, c1⟩ := ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpRec_symm (hsq n) y μ ν)
      hQsym (B := ρ₁ n) fun κ => ⟨memH_mono (by omega) (hr1 n κ).1.1,
        (sn_mono' (by omega) (hr1 n κ).1.1).trans (hr1 n κ).1.2⟩
    obtain ⟨m2, c2⟩ := ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpRec_symm (hsv n) y μ ν)
      hVsym (B := ρ₁ n) fun κ => ⟨memH_mono (by omega) (hr1 n κ).2.1.1,
        (sn_mono' (by omega) (hr1 n κ).2.1.1).trans (hr1 n κ).2.1.2⟩
    obtain ⟨m3, c3⟩ := ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpRec_symRec_symm _ y μ ν)
      hAsym (B := ρ₁ n) fun κ => by
        rw [cmp_interpRec_symRec (N := n + 1)]; exact (hr1 n κ).2.2
    have m4 := fun i => ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpD_symm (hsq n) i y μ ν)
      (hQdsym i) (B := ρ₂ n) fun κ => ⟨memH_mono (by omega) (hrQd n κ i).1,
        (sn_mono' (by omega) (hrQd n κ i).1).trans (hrQd n κ i).2⟩
    have m5 := fun i => ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpD_symm (hsv n) i y μ ν)
      (hVdsym i) (B := ρ₂ n) fun κ => hrVd n κ i
    have m6 := fun i j => ccoordSum_sub_le_of_upper r _ _
      (fun y μ ν => interpDD_symm (hsq n) i j y μ ν) (hQddsym i j) (B := ρ₂ n) fun κ => hrQdd n κ i j
    rw [eJ]
    refine ⟨memH_pjetField m1 m2 m3 (fun i => (m4 i).1) (fun i => (m5 i).1)
      (fun i j => (m6 i j).1), ?_⟩
    rw [ccoordSum_pjetField]
    have s4 : ∑ i, ccoordSum r bM ((interpD (q n t) - Qd t) i) ≤ 3 * (16 * ρ₂ n) :=
      (sum_le_sum fun i _ => (m4 i).2).trans (by simp)
    have s5 : ∑ i, ccoordSum r bM ((interpD (v n t) - Vd t) i) ≤ 3 * (16 * ρ₂ n) :=
      (sum_le_sum fun i _ => (m5 i).2).trans (by simp)
    have s6 : ∑ i, ∑ j, ccoordSum r bM ((interpDD (q n t) - Qdd t) i j) ≤ 9 * (16 * ρ₂ n) :=
      (sum_le_sum fun i _ => sum_le_sum fun j _ => (m6 i j).2).trans (by simp; ring_nf; rfl)
    linarith
  -- membership and size of the limit jet
  have hJnm : ∀ n j, MemH r ⇑(ccoord bPJ (Jn n) j) := by
    intro n
    refine memH_pjetField (fun k => (memH_interpRec r _ k).1) (fun k => (memH_interpRec r _ k).1)
      (fun k => (memH_interpRec r _ k).1) (fun i k => (hderQ n i k r).1) (fun i k => (hderV n i k r).1)
      (fun i j k => (hderQQ n i j k r).1)
  have hJm : ∀ j, MemH r ⇑(ccoord bPJ J j) := by
    intro j
    have h1 := hJnm 0 j
    have h2 := (hdiff 0).1 j
    have e : ccoord bPJ (Jn 0 - J) j = ccoord bPJ (Jn 0) j - ccoord bPJ J j := ccoord_sub _ _ _ _
    rw [e] at h2
    exact memH_of_sub h1 h2
  have hJS : ccoordSum r bPJ J ≤ S * ε := by
    have hle : ∀ n, ccoordSum r bPJ J ≤ S * ε + 16 * (3 * ρ₁ n + 15 * ρ₂ n) := by
      intro n
      unfold ccoordSum
      have hk : ∀ j, sn r ⇑(ccoord bPJ J j) ≤ sn r ⇑(ccoord bPJ (Jn n) j) +
          sn r ⇑(ccoord bPJ (Jn n - J) j) := by
        intro j
        have e : ccoord bPJ J j = ccoord bPJ (Jn n) j - ccoord bPJ (Jn n - J) j := by
          rw [ccoord_sub]; abel
        rw [e]
        exact sn_sub_le' (hJnm n j) ((hdiff n).1 j)
      calc ∑ j, sn r ⇑(ccoord bPJ J j)
          ≤ ∑ j, (sn r ⇑(ccoord bPJ (Jn n) j) + sn r ⇑(ccoord bPJ (Jn n - J) j)) :=
            sum_le_sum fun j _ => hk j
        _ = ccoordSum r bPJ (Jn n) + ccoordSum r bPJ (Jn n - J) := by
            rw [sum_add_distrib]; rfl
        _ ≤ S * ε + 16 * (3 * ρ₁ n + 15 * ρ₂ n) := add_le_add (hJnS n) (hdiff n).2
    have hlim : Tendsto (fun n : ℕ => S * ε + 16 * (3 * ρ₁ n + 15 * ρ₂ n)) atTop (𝓝 (S * ε)) := by
      have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simp only [one_div] at h0
      have h1 : Tendsto ρ₁ atTop (𝓝 0) := by
        simpa using h0.const_mul (C₁ * Real.exp (K₁ * t) * (1 + t) * ε)
      have h2 : Tendsto ρ₂ atTop (𝓝 0) := by
        simpa using h0.const_mul (C₂ * Real.exp (K₂ * t) * (1 + t) * ε)
      simpa using tendsto_const_nhds.add (((h1.const_mul 3).add (h2.const_mul 15)).const_mul 16)
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hle
  have hSδ : S * ε ≤ δR0 := by
    have h1 : ε ≤ δR0 / (S + 1) := hεδ.trans (min_le_right _ _)
    rw [le_div_iff₀ (by linarith)] at h1
    nlinarith
  refine ⟨hQt, hVt, hjet, hrow, hder, fun n κ => ⟨?_, ?_, ?_⟩, fun n a b c d => ?_⟩
  · exact (hr1 n κ).1.2.trans (by
      have e1 : C₁ * Real.exp (K₁ * t) ≤ C * Real.exp (K * t) := by
        have : C₁ ≤ C := by
          simp only [C]
          have := mul_nonneg (mul_nonneg hCR0n (by norm_num : (0:ℝ) ≤ 16))
            (by linarith : (0:ℝ) ≤ 3 * C₁ + 15 * C₂)
          linarith
        exact mul_le_mul this hexp1 (Real.exp_pos _).le hCnn
      calc C₁ * Real.exp (K₁ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹
          = (C₁ * Real.exp (K₁ * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by ring
        _ ≤ (C * Real.exp (K * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_right e1 (hfac0 n)
        _ = _ := by ring)
  · exact (hr1 n κ).2.1.2.trans (by
      have e1 : C₁ * Real.exp (K₁ * t) ≤ C * Real.exp (K * t) := by
        have : C₁ ≤ C := by
          simp only [C]
          have := mul_nonneg (mul_nonneg hCR0n (by norm_num : (0:ℝ) ≤ 16))
            (by linarith : (0:ℝ) ≤ 3 * C₁ + 15 * C₂)
          linarith
        exact mul_le_mul this hexp1 (Real.exp_pos _).le hCnn
      calc C₁ * Real.exp (K₁ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹
          = (C₁ * Real.exp (K₁ * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by ring
        _ ≤ (C * Real.exp (K * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_right e1 (hfac0 n)
        _ = _ := by ring)
  · exact (hr1 n κ).2.2.2.trans (by
      have e1 : C₁ * Real.exp (K₁ * t) ≤ C * Real.exp (K * t) := by
        have : C₁ ≤ C := by
          simp only [C]
          have := mul_nonneg (mul_nonneg hCR0n (by norm_num : (0:ℝ) ≤ 16))
            (by linarith : (0:ℝ) ≤ 3 * C₁ + 15 * C₂)
          linarith
        exact mul_le_mul this hexp1 (Real.exp_pos _).le hCnn
      calc C₁ * Real.exp (K₁ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹
          = (C₁ * Real.exp (K₁ * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by ring
        _ ≤ (C * Real.exp (K * t)) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_right e1 (hfac0 n)
        _ = _ := by ring)
  · -- the curvature rate
    set e : Fin 4 × Fin 4 × Fin 4 × Fin 4 := (a, b, c, d)
    obtain ⟨F, hF, hFm, hFs⟩ := hRm e (Jn n) J (hJnm n) hJm ((hJnS n).trans (hSδ.trans (hδR0le e)))
      (hJS.trans (hSδ.trans (hδR0le e)))
    refine ⟨F, fun y => hF y, hFm, hFs.trans ?_⟩
    have h1 : CR e * ccoordSum r bPJ (Jn n - J) ≤ CR0 * (16 * (3 * ρ₁ n + 15 * ρ₂ n)) :=
      mul_le_mul (hCR0 e) (hdiff n).2 (ccoordSum_nonneg _ _ _) hCR0n
    refine h1.trans ?_
    have h2 : ρ₁ n ≤ C₁ * Real.exp (K * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by
      simp only [ρ₁]
      calc C₁ * Real.exp (K₁ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹
          = C₁ * Real.exp (K₁ * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by ring
        _ ≤ C₁ * Real.exp (K * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp1 hC₁) (hfac0 n)
    have h3 : ρ₂ n ≤ C₂ * Real.exp (K * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by
      simp only [ρ₂]
      calc C₂ * Real.exp (K₂ * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹
          = C₂ * Real.exp (K₂ * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) := by ring
        _ ≤ C₂ * Real.exp (K * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp2 hC₂) (hfac0 n)
    have hE := hfac0 n
    have hex := (Real.exp_pos (K * t)).le
    set Z := Real.exp (K * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹)
    have hZ : 0 ≤ Z := mul_nonneg hex hE
    have h4 : CR0 * (16 * (3 * ρ₁ n + 15 * ρ₂ n)) ≤ CR0 * 16 * (3 * C₁ + 15 * C₂) * Z := by
      have h5 : 3 * ρ₁ n + 15 * ρ₂ n ≤ (3 * C₁ + 15 * C₂) * Z := by
        have e1 : C₁ * Real.exp (K * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) = C₁ * Z := by
          simp only [Z]; ring
        have e2 : C₂ * Real.exp (K * t) * ((1 + t) * ε * ((n : ℝ) + 1)⁻¹) = C₂ * Z := by
          simp only [Z]; ring
        rw [e1] at h2; rw [e2] at h3
        nlinarith
      have := mul_le_mul_of_nonneg_left h5 (mul_nonneg hCR0n (by norm_num) : (0 : ℝ) ≤ CR0 * 16)
      linarith
    refine h4.trans ?_
    have h6 : CR0 * 16 * (3 * C₁ + 15 * C₂) ≤ C := by
      simp only [C]; linarith
    calc CR0 * 16 * (3 * C₁ + 15 * C₂) * Z ≤ C * Z := mul_le_mul_of_nonneg_right h6 hZ
      _ = C * Real.exp (K * t) * (1 + t) * ε * ((n : ℝ) + 1)⁻¹ := by simp only [Z]; ring

/-! ### Non-vacuity -/

theorem isWriterSolution_zero (N : ℕ) [NeZero N] (T : ℝ) :
    IsWriterSolution T (fun _ => (0 : Grid N → MetricRec)) (fun _ => 0) := by
  intro t _
  refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun x => hasDerivAt_const _ _, fun x κ => ?_⟩
  rw [harmonicWriterAcceleration_zero]
  simpa using hasDerivAt_const t (0 : ℝ)

theorem Xnorm_zero' (N : ℕ) [NeZero N] (s : ℕ) : Xnorm s (0 : Grid N → MetricRec) 0 = 0 := by
  have : Xsq s (0 : Grid N → MetricRec) 0 = 0 := by
    unfold Xsq
    refine sum_eq_zero fun κ _ => ?_
    have e : cx (comp (0 : Grid N → MetricRec) κ.1.1 κ.1.2) = 0 := by funext x; simp [comp, cx]
    rw [e]
    simp [PeriodicGridSobolev.sobSq, PeriodicGridSobolev.gridNormSq]
  rw [Xnorm, this, Real.sqrt_zero]

theorem contTop_zero (s : ℕ) : contTop s (0 : C(T3, MetricRec)) 0 = 0 := by
  simp [contTop, ccoordSum, ccoord_zero, sn, PeriodicGridSobolev.trigSobSq, mFourierCoeff_zero']

/-- Non-vacuity of `writer_limit_solves` (and of `writer_continuum_limit`, `interp_cauchy`): the flat
writer histories on every mesh, started from the flat continuum data, satisfy all hypotheses. -/
example (s : ℕ) (hs : 5 ≤ s) : True := by
  obtain ⟨δ, hδ, K₁, hK₁, C₁, hC₁, K₂, hK₂, C₂, hC₂, h⟩ := writer_limit_solves s hs
  have := h 1 (fun _ _ => 0) (fun _ _ => 0) 0 0 0 (fun n => isWriterSolution_zero (n + 1) 1)
    (fun n => rfl) (fun n => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun k => by rw [ccoord_zero]; exact memH_zero _) (fun k => by rw [ccoord_zero]; exact memH_zero _)
    (by rw [contTop_zero]) (fun n t _ => by rw [Xnorm_zero']) hδ.le
  trivial

/-- Non-vacuity of `contSolution_eq_limit`: flat writer histories and the flat continuum solution. -/
example (s : ℕ) (hs : 5 ≤ s) : True := by
  obtain ⟨δ, hδ, h⟩ := contSolution_eq_limit s hs
  have := h 1 (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
    (fun _ _ => 0) (fun _ _ _ => 0) 0 (fun n => isWriterSolution_zero (n + 1) 1) (fun n => rfl)
    (fun n => rfl) (fun n t _ => by rw [Xnorm_zero']; exact hδ.le) (isContSolution_flat s 1)
    (fun t _ => by rw [contTop_zero]) hδ.le
  trivial

/-- Non-vacuity of `writer_limit_curvature_rate` (flat data on every mesh). -/
example (s : ℕ) (hs : 5 ≤ s) : True := by
  obtain ⟨δ, hδ, K, hK, C, hC, h⟩ := writer_limit_curvature_rate s hs
  have := h 1 (fun _ _ => 0) (fun _ _ => 0) 0 0 0 (fun n => isWriterSolution_zero (n + 1) 1)
    (fun n => rfl) (fun n => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun k => by rw [ccoord_zero]; exact memH_zero _) (fun k => by rw [ccoord_zero]; exact memH_zero _)
    (by rw [contTop_zero]) (fun n t _ => by rw [Xnorm_zero']) hδ.le
  trivial

end

end RenewalGeometry.OpenWriterContinuum
