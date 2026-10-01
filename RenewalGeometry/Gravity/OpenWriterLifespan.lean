/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.ODECutoffContinuation
import RenewalGeometry.Gravity.OpenWriterEnergyEstimate

/-!
# Common nonlinear lifespan of the open writer (`cor:supp-open-lifespan`, first clause)

For each cutoff `h = 1/N` the open writer `eq:main-open-writer` is an autonomous ODE on the
finite-dimensional space of ten-component records `X = (q, v)`.  We prove existence, uniqueness
and the uniform bound `eq:main-open-uniform-time` on a common time `T_s`, independent of `N`:

* `writerField`: the vector field `(q, v) ↦ (v, a⁻¹[…])` on `4 × 4` record arrays, evaluated on
  the symmetrized record (`symRec`), so that it depends only on the ten upper components;
* `analyticAt_compensatorMap_of_det`, `analyticAt_accel`: the writer acceleration is real-analytic
  in the whole record at every record with `det(η + q(x)) ≠ 0` and `a(η + q(x)) ≠ 0`;
* `exists_lipschitz_writerField`: for each `N`, the field is Lipschitz and bounded on a fixed
  sup-norm neighbourhood of the flat record (compactness + `ContDiffOn.exists_lipschitzOnWith`);
* `energy_upper`: the upper half `𝓔_{s,h} ≤ 8 ‖X‖²_{X^s_h}` of the energy equivalence;
* `apriori_bound`: from `thm:supp-open-energy` (`open_energy_inequality`) and a scalar comparison,
  every solution staying in the chart on `[0, t]`, `t ≤ T_s`, satisfies
  `‖X(t)‖_{X^s_h} ≤ C_s ‖X(0)‖_{X^s_h}`;
* `open_writer_lifespan` (**`cor:supp-open-lifespan`, first clause; `(O1)` of
  `thm:main-open-3plus1`**): there are `ε_s, T_s, C_s > 0`, independent of `N`, such that every
  symmetric initial record with `‖X(0)‖_{X^s_h} ≤ ε_s` has a solution on `[0, T_s]` with
  `sup_t ‖X(t)‖_{X^s_h} ≤ C_s ‖X(0)‖_{X^s_h}`, and it is unique.

Existence uses the first-exit argument of `Analysis/ODECutoffContinuation.lean` (cut-off field,
Picard–Lindelöf, continuous induction); symmetry of the solution is preserved by uniqueness.
-/

open Set Metric Filter Topology Finset
open scoped NNReal BigOperators

namespace RenewalGeometry.OpenWriterLifespan

open RootParityConnector OpenWriterGridBridge OpenWriterChart OpenWriterEnergy HarmonicWriter
  OpenWriterEnergyEstimate HarmonicDefect

noncomputable section

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-- The state space of the writer: pairs `(q, v)` of record arrays. -/
abbrev State (N : ℕ) := (Grid N → MetricRec) × (Grid N → MetricRec)

/-! ### Symmetrization -/

theorem upperOf_upper (κ : Upper) : upperOf κ.1.1 κ.1.2 = κ := by
  unfold upperOf
  rw [dif_pos κ.2]

theorem upperOf_comm (μ ν : Fin 4) : upperOf μ ν = upperOf ν μ := by
  unfold upperOf
  by_cases h1 : μ ≤ ν <;> by_cases h2 : ν ≤ μ
  · have : μ = ν := le_antisymm h1 h2
    subst this; rfl
  · rw [dif_pos h1, dif_neg h2]
  · rw [dif_neg h1, dif_pos h2]
  · exact absurd (le_of_lt (not_le.mp h1)) h2

/-- The symmetrized record: every entry replaced by its upper representative. -/
def symRec (u : Grid N → MetricRec) : Grid N → MetricRec :=
  fun x μ ν => u x (upperOf μ ν).1.1 (upperOf μ ν).1.2

theorem isSymRec_symRec (u : Grid N → MetricRec) : IsSymRec (symRec u) := by
  intro x μ ν
  simp only [symRec, upperOf_comm μ ν]

theorem symRec_upper (u : Grid N → MetricRec) (x : Grid N) (κ : Upper) :
    symRec u x κ.1.1 κ.1.2 = u x κ.1.1 κ.1.2 := by
  simp only [symRec, upperOf_upper]

theorem symRec_of_isSymRec {u : Grid N → MetricRec} (hu : IsSymRec u) : symRec u = u := by
  funext x μ ν
  exact congrFun (comp_upperOf hu μ ν) x

theorem symRec_symRec (u : Grid N → MetricRec) : symRec (symRec u) = symRec u :=
  symRec_of_isSymRec (isSymRec_symRec u)

theorem comp_symRec (u : Grid N → MetricRec) (κ : Upper) :
    comp (symRec u) κ.1.1 κ.1.2 = comp u κ.1.1 κ.1.2 := by
  funext x; exact symRec_upper u x κ

theorem Xsq_symRec (s : ℕ) (q v : Grid N → MetricRec) :
    Xsq s (symRec q) (symRec v) = Xsq s q v := by
  unfold Xsq
  simp only [comp_symRec]

theorem Xnorm_symRec (s : ℕ) (q v : Grid N → MetricRec) :
    Xnorm s (symRec q) (symRec v) = Xnorm s q v := by
  unfold Xnorm; rw [Xsq_symRec]

/-- The symmetrization of states, a continuous linear map. -/
def symL : State N →L[ℝ] State N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => (symRec y.1, symRec y.2)
      map_add' := fun y z => rfl
      map_smul' := fun c y => rfl }

theorem symL_apply (y : State N) : symL y = (symRec y.1, symRec y.2) := rfl

theorem symL_symL (y : State N) : symL (symL y) = symL y := by
  simp only [symL_apply, symRec_symRec]

/-! ### The writer vector field -/

/-- The writer acceleration, component formula (`eq:main-open-writer`):
`v_t = a⁻¹ [Σ D_i⁻(c^{ij} D_j⁺ q) - 𝖪_b v + 𝖦_h(q, v)]`. -/
theorem accel_apply (q v : Grid N → MetricRec) (x : Grid N) (μ ν : Fin 4) :
    harmonicWriterAcceleration q v x μ ν = (aArr q x)⁻¹ *
      (divArr (cArr q) (comp q μ ν) x - skewArr (bArr q) (comp v μ ν) x +
        comp (Garr q v) μ ν x) := by
  have e1 : comp (harmonicWriterAcceleration q v) μ ν x = (aArr q x)⁻¹ *
      writerRhs harmC harmB harmonicSource (fun i j g w => fderiv ℝ (harmC i j) g w)
        (fun i g w => fderiv ℝ (harmB i) g w) minkowski (N : ℝ)⁻¹ (e N) q v x μ ν := by
    simp [comp, harmonicWriterAcceleration, openWriterAcceleration, writerAcceleration, aArr]
  have h1 : divergenceFlux harmC minkowski (N : ℝ)⁻¹ (e N) q x μ ν =
      divArr (cArr q) (comp q μ ν) x := by
    simp only [divergenceFlux, divArr, Finset.sum_apply]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [bwd, fwd, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, OpenWriterEnergy.Dm_apply,
      OpenWriterEnergy.Dp_apply, cArr, comp, inv_inv]
  have h2 : skewTransport harmB minkowski (N : ℝ)⁻¹ (e N) q v x μ ν =
      skewArr (bArr q) (comp v μ ν) x := by
    simp only [skewTransport, skewArr, Finset.sum_apply, Pi.add_apply]
    refine sum_congr rfl fun i _ => ?_
    simp only [ctr, fwd, bwd, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul,
      OpenWriterEnergy.D0_apply, OpenWriterEnergy.Dm_apply, OpenWriterEnergy.Dp_apply, bArr,
      comp, inv_inv]
    ring
  have h3 : compensator harmonicSource (fun i j g w => fderiv ℝ (harmC i j) g w)
      (fun i g w => fderiv ℝ (harmB i) g w) minkowski (N : ℝ)⁻¹ (e N) q v x μ ν =
      comp (Garr q v) μ ν x := by
    rw [compensator_eq]; rfl
  have e2 : harmonicWriterAcceleration q v x μ ν = comp (harmonicWriterAcceleration q v) μ ν x :=
    rfl
  rw [e2, e1]
  congr 1

/-- **The writer vector field** on states: `(q, v) ↦ (v, v_t)`, evaluated on the symmetrized
record.  On symmetric records it is the open writer `eq:main-open-writer`. -/
def writerField (y : State N) : State N :=
  (symRec y.2, symRec (harmonicWriterAcceleration (symRec y.1) (symRec y.2)))

/-- The field on symmetrized states (the analytic part). -/
def writerFieldCore (y : State N) : State N :=
  (y.2, symRec (harmonicWriterAcceleration y.1 y.2))

theorem writerField_eq_core (y : State N) : writerField y = writerFieldCore (symL y) := rfl

theorem writerField_symL (y : State N) : writerField (symL y) = writerField y := by
  simp only [writerField, symL_apply, symRec_symRec]

theorem symL_writerField (y : State N) : symL (writerField y) = writerField y := by
  simp only [writerField, symL_apply, symRec_symRec]

/-! ### Analyticity of the field -/

/-- The compensator components are analytic at every site jet `w₀` with `det(η + w₀.1) ≠ 0`. -/
theorem analyticAt_compensatorMap_of_det (μ ν : Fin 4) (w₀ : JetSpace)
    (hdet : (Matrix.of (minkowski + w₀.1)).det ≠ 0) :
    AnalyticAt ℝ (fun w : JetSpace => compensatorMap w μ ν) w₀ := by
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
  have hF : AnalyticAt ℝ (fun w : JetSpace => harmonicSource (minkowski + w.1) w.2 μ ν) w₀ := by
    have := (hpoly _).comp (hg.prod (hinv.prod hjet))
    simp only [harmonicSource]
    simp only [Function.comp_def] at this
    exact analyticAt_const.mul this
  have hev : ∀ (A : MetricRec → ℝ), AnalyticAt ℝ A (minkowski + w₀.1) →
      ∀ (L : JetSpace → MetricRec), AnalyticAt ℝ L w₀ →
      AnalyticAt ℝ (fun w : JetSpace => fderiv ℝ A (minkowski + w.1) (L w)) w₀ := by
    intro A hA L hL
    have hD : AnalyticAt ℝ (fun w : JetSpace => fderiv ℝ A (minkowski + w.1)) w₀ :=
      hA.fderiv.comp_of_eq hg rfl
    exact ((ContinuousLinearMap.id ℝ (MetricRec →L[ℝ] ℝ)).analyticAt_bilinear _).comp
      (hD.prod hL)
  have hCa : ∀ i j, AnalyticAt ℝ (harmC i j) (minkowski + w₀.1) := fun i j =>
    analyticAt_inv_entry _ hdet i.succ j.succ
  have hBa : ∀ i, AnalyticAt ℝ (harmB i) (minkowski + w₀.1) := fun i =>
    (analyticAt_inv_entry _ hdet 0 i.succ).neg
  have hC : ∀ i j, AnalyticAt ℝ (fun w : JetSpace =>
      fderiv ℝ (harmC i j) (minkowski + w.1) (w.2.2 i) * w.2.2 j μ ν) w₀ := fun i j =>
    (hev _ (hCa i j) (fun w => w.2.2 i) (by fun_prop)).mul (by fun_prop)
  have hB : ∀ i, AnalyticAt ℝ (fun w : JetSpace =>
      fderiv ℝ (harmB i) (minkowski + w.1) (w.2.2 i) * w.2.1 μ ν) w₀ := fun i =>
    (hev _ (hBa i) (fun w => w.2.2 i) (by fun_prop)).mul (by fun_prop)
  have e : (fun w : JetSpace => compensatorMap w μ ν) = fun w =>
      harmonicSource (minkowski + w.1) w.2 μ ν
      - ∑ i, ∑ j, fderiv ℝ (harmC i j) (minkowski + w.1) (w.2.2 i) * w.2.2 j μ ν
      + ∑ i, fderiv ℝ (harmB i) (minkowski + w.1) (w.2.2 i) * w.2.1 μ ν := by
    funext w; exact compensatorMap_apply w μ ν
  rw [e]
  refine (hF.sub ?_).add ?_
  · exact Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j _ => hC i j
  · exact Finset.analyticAt_fun_sum _ fun i _ => hB i

/-- **The writer acceleration is analytic in the record** at every state whose metric
`g = η + q` has `det g(x) ≠ 0` and `a(g(x)) ≠ 0` at every site. -/
theorem analyticAt_accel (y₀ : State N)
    (hdet : ∀ z, (Matrix.of (minkowski + y₀.1 z)).det ≠ 0)
    (ha : ∀ z, harmA (minkowski + y₀.1 z) ≠ 0) (x : Grid N) (μ ν : Fin 4) :
    AnalyticAt ℝ (fun y : State N => harmonicWriterAcceleration y.1 y.2 x μ ν) y₀ := by
  have hgz : ∀ z, AnalyticAt ℝ (fun y : State N => minkowski + y.1 z) y₀ := fun z => by fun_prop
  have hA : ∀ z, AnalyticAt ℝ (fun y : State N => aArr y.1 z) y₀ := fun z =>
    ((analyticAt_inv_entry _ (hdet z) 0 0).neg).comp_of_eq (hgz z) rfl
  have hC : ∀ z i j, AnalyticAt ℝ (fun y : State N => cArr y.1 i j z) y₀ := fun z i j =>
    (analyticAt_inv_entry _ (hdet z) i.succ j.succ).comp_of_eq (hgz z) rfl
  have hB : ∀ z i, AnalyticAt ℝ (fun y : State N => bArr y.1 i z) y₀ := fun z i =>
    ((analyticAt_inv_entry _ (hdet z) 0 i.succ).neg).comp_of_eq (hgz z) rfl
  have hJ : AnalyticAt ℝ (fun y : State N => jetArr y.1 y.2 x) y₀ := by
    simp only [jetArr, fwd]
    exact AnalyticAt.prod (by fun_prop) (AnalyticAt.prod (by fun_prop)
      (AnalyticAt.pi fun i => by fun_prop))
  have hG : AnalyticAt ℝ (fun y : State N => comp (Garr y.1 y.2) μ ν x) y₀ :=
    (analyticAt_compensatorMap_of_det μ ν _ (by simpa [jetArr] using hdet x)).comp_of_eq hJ rfl
  have hD : AnalyticAt ℝ (fun y : State N => divArr (cArr y.1) (comp y.1 μ ν) x) y₀ := by
    simp only [divArr, OpenWriterEnergy.Dm_apply, OpenWriterEnergy.Dp_apply, comp]
    fun_prop
  have hS : AnalyticAt ℝ (fun y : State N => skewArr (bArr y.1) (comp y.2 μ ν) x) y₀ := by
    simp only [skewArr, OpenWriterEnergy.D0_apply, OpenWriterEnergy.Dm_apply,
      OpenWriterEnergy.Dp_apply, comp]
    fun_prop
  have e : (fun y : State N => harmonicWriterAcceleration y.1 y.2 x μ ν) = fun y =>
      (aArr y.1 x)⁻¹ * (divArr (cArr y.1) (comp y.1 μ ν) x - skewArr (bArr y.1) (comp y.2 μ ν) x +
        comp (Garr y.1 y.2) μ ν x) := by
    funext y; exact accel_apply y.1 y.2 x μ ν
  rw [e]
  exact ((hA x).inv (ha x)).mul ((hD.sub hS).add hG)

/-- Near Minkowski the metric is invertible and `a = -g^{00} ≠ 0`. -/
theorem exists_det_chart : ∃ r₀ > 0, ∀ g : MetricRec, ‖g - minkowski‖ < r₀ →
    (Matrix.of g).det ≠ 0 ∧ harmA g ≠ 0 := by
  have h1 : ∀ᶠ g in 𝓝 minkowski, (Matrix.of g).det ≠ 0 :=
    (analyticAt_det minkowski).continuousAt.eventually_ne det_minkowski_ne
  have h2 : ∀ᶠ g in 𝓝 minkowski, harmA g ≠ 0 :=
    analyticAt_harmA.continuousAt.eventually_ne (by rw [harm_minkowski.1]; norm_num)
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.mp (h1.and h2)
  exact ⟨r, hr, fun g hg => h (by rw [dist_eq_norm]; exact hg)⟩

/-- **Lipschitz bound of the writer field** on a mesh-dependent but fixed-radius sup-norm region:
for `2ρ < r₀` the field is Lipschitz and bounded on `{‖symL y‖ ≤ 2ρ}`. -/
theorem exists_lipschitz_writerField {r₀ : ℝ}
    (hr₀ : ∀ g : MetricRec, ‖g - minkowski‖ < r₀ → (Matrix.of g).det ≠ 0 ∧ harmA g ≠ 0)
    {ρ : ℝ} (hρ : 2 * ρ < r₀) (N : ℕ) [NeZero N] :
    ∃ L M : ℝ≥0, LipschitzOnWith L (writerField (N := N)) {y | ‖symL y‖ ≤ 2 * ρ} ∧
      ∀ y : State N, ‖symL y‖ ≤ 2 * ρ → ‖writerField y‖ ≤ M := by
  set B : Set (State N) := closedBall 0 (2 * ρ)
  have hanal : ∀ w ∈ B, AnalyticAt ℝ (writerFieldCore (N := N)) w := by
    intro w hw
    have hw' : ‖w‖ ≤ 2 * ρ := mem_closedBall_zero_iff.mp hw
    have hz : ∀ z, ‖(minkowski + w.1 z) - minkowski‖ < r₀ := fun z => by
      rw [add_sub_cancel_left]
      exact lt_of_le_of_lt ((norm_le_pi_norm w.1 z).trans ((norm_fst_le w).trans hw')) hρ
    refine AnalyticAt.prod (by fun_prop) (AnalyticAt.pi fun x => AnalyticAt.pi fun μ =>
      AnalyticAt.pi fun ν => ?_)
    exact analyticAt_accel w (fun z => (hr₀ _ (hz z)).1) (fun z => (hr₀ _ (hz z)).2) x _ _
  have hcd : ContDiffOn ℝ 1 (writerFieldCore (N := N)) B := fun w hw =>
    (hanal w hw).contDiffAt.contDiffWithinAt
  obtain ⟨K, hK⟩ := hcd.exists_lipschitzOnWith (by norm_num) (convex_closedBall _ _)
    (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : State N) (2 * ρ)).exists_bound_of_continuousOn
    hcd.continuousOn
  refine ⟨K * ‖(symL : State N →L[ℝ] State N)‖₊, Real.toNNReal C, ?_, fun y hy => ?_⟩
  · have hmaps : MapsTo (symL : State N →L[ℝ] State N) {y | ‖symL y‖ ≤ 2 * ρ} B :=
      fun y hy => mem_closedBall_zero_iff.mpr hy
    have e : (writerField (N := N)) = writerFieldCore ∘ (symL : State N →L[ℝ] State N) :=
      funext writerField_eq_core
    rw [e]
    exact hK.comp (symL : State N →L[ℝ] State N).lipschitz.lipschitzOnWith hmaps
  · rw [writerField_eq_core]
    exact (hC _ (mem_closedBall_zero_iff.mpr hy)).trans (Real.le_coe_toNNReal C)


/-! ### Uniform sup bounds, continuity of the norm -/

/-- The uniform Sobolev constant `L = (1 + Σ‖e_k‖) √K · 16` of the pointwise bound. -/
def supConst : ℝ := (1 + ∑ j, ‖bM j‖) * Real.sqrt PeriodicGridSobolev.Kprod * 16

theorem supConst_nonneg : 0 ≤ supConst := by
  unfold supConst
  have : 0 ≤ ∑ j, ‖bM j‖ := sum_nonneg fun _ _ => norm_nonneg _
  positivity

theorem norm_bM_le (j : Σ _ : Fin 4, Fin 4) : ‖bM j‖ ≤ 1 + ∑ j, ‖bM j‖ := by
  have := single_le_sum (f := fun j => ‖bM j‖) (fun _ _ => norm_nonneg _) (mem_univ j)
  linarith

/-- **Uniform pointwise bound of a symmetric position record**: `‖q(x)‖ ≤ L ‖X‖_{X^s_h}`. -/
theorem norm_q_le (s : ℕ) (hs : 1 ≤ s) {q : Grid N → MetricRec} (hq : IsSymRec q)
    (v : Grid N → MetricRec) (x : Grid N) : ‖q x‖ ≤ supConst * Xnorm s q v := by
  have h1 := PeriodicGridSobolev.Moser.norm_le_coordSum bM norm_bM_le q x
  have h2 := coordSum_bM_q_le s hq v (r := 2) (by omega)
  have hB : 0 ≤ 1 + ∑ j, ‖bM j‖ := by
    have : 0 ≤ ∑ j, ‖bM j‖ := sum_nonneg fun _ _ => norm_nonneg _
    linarith
  calc ‖q x‖ ≤ (1 + ∑ j, ‖bM j‖) * (Real.sqrt PeriodicGridSobolev.Kprod *
        PeriodicGridSobolev.Moser.coordSum 2 bM q) := h1
    _ ≤ (1 + ∑ j, ‖bM j‖) * (Real.sqrt PeriodicGridSobolev.Kprod * (16 * Xnorm s q v)) := by
        gcongr
    _ = supConst * Xnorm s q v := by unfold supConst; ring

/-- **Uniform pointwise bound of a symmetric velocity record**. -/
theorem norm_v_le (s : ℕ) (hs : 2 ≤ s) (q : Grid N → MetricRec) {v : Grid N → MetricRec}
    (hv : IsSymRec v) (x : Grid N) : ‖v x‖ ≤ supConst * Xnorm s q v := by
  have h1 := PeriodicGridSobolev.Moser.norm_le_coordSum bM norm_bM_le v x
  have h2 := coordSum_bM_v_le s q hv (r := 2) hs
  have hB : 0 ≤ 1 + ∑ j, ‖bM j‖ := by
    have : 0 ≤ ∑ j, ‖bM j‖ := sum_nonneg fun _ _ => norm_nonneg _
    linarith
  calc ‖v x‖ ≤ (1 + ∑ j, ‖bM j‖) * (Real.sqrt PeriodicGridSobolev.Kprod *
        PeriodicGridSobolev.Moser.coordSum 2 bM v) := h1
    _ ≤ (1 + ∑ j, ‖bM j‖) * (Real.sqrt PeriodicGridSobolev.Kprod * (16 * Xnorm s q v)) := by
        gcongr
    _ = supConst * Xnorm s q v := by unfold supConst; ring

/-- The symmetrized state is bounded in sup norm by the energy norm. -/
theorem norm_symL_le (s : ℕ) (hs : 2 ≤ s) (y : State N) :
    ‖symL y‖ ≤ supConst * Xnorm s y.1 y.2 := by
  have hX : 0 ≤ supConst * Xnorm s y.1 y.2 := mul_nonneg supConst_nonneg (Xnorm_nonneg _ _ _)
  rw [symL_apply, Prod.norm_def]
  refine max_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg hX).2 fun x => ?_
    rw [← Xnorm_symRec]
    exact norm_q_le s (by omega) (isSymRec_symRec _) _ x
  · refine (pi_norm_le_iff_of_nonneg hX).2 fun x => ?_
    rw [← Xnorm_symRec]
    exact norm_v_le s hs _ (isSymRec_symRec _) x

/-- The energy norm is continuous on states. -/
theorem continuous_XnormS (s : ℕ) : Continuous fun y : State N => Xnorm s y.1 y.2 := by
  have hc : ∀ (r : ℕ) (f : State N → Grid N → MetricRec), Continuous f → ∀ μ ν : Fin 4,
      Continuous fun y => PeriodicGridSobolev.sobSq r (cx (comp (f y) μ ν)) := by
    intro r f hf μ ν
    have h1 : Continuous fun y => cx (comp (f y) μ ν) :=
      continuous_pi fun x => Complex.continuous_ofReal.comp
        ((continuous_apply ν).comp ((continuous_apply μ).comp ((continuous_apply x).comp hf)))
    simp_rw [← PeriodicGridSobolev.sobNorm_sq]
    exact ((PeriodicGridSobolev.Moser.continuous_sobNorm r).comp h1).pow 2
  unfold Xnorm Xsq
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun κ _ =>
    (hc _ _ continuous_fst _ _).add (hc _ _ continuous_snd _ _))

/-- The energy norm along a history is continuous wherever the ten upper components are. -/
theorem continuousWithinAt_Xnorm (s : ℕ) {q v : ℝ → Grid N → MetricRec} {S : Set ℝ} {t : ℝ}
    (hq : ∀ x (κ : Upper), ContinuousWithinAt (fun τ => q τ x κ.1.1 κ.1.2) S t)
    (hv : ∀ x (κ : Upper), ContinuousWithinAt (fun τ => v τ x κ.1.1 κ.1.2) S t) :
    ContinuousWithinAt (fun τ => Xnorm s (q τ) (v τ)) S t := by
  have e : (fun τ => Xnorm s (q τ) (v τ)) =
      (fun y : State N => Xnorm s y.1 y.2) ∘ fun τ => (symRec (q τ), symRec (v τ)) := by
    funext τ; simp [Xnorm_symRec]
  rw [e]
  refine (continuous_XnormS s).continuousAt.comp_continuousWithinAt
    (ContinuousWithinAt.prodMk ?_ ?_)
  · exact continuousWithinAt_pi.2 fun x => continuousWithinAt_pi.2 fun μ =>
      continuousWithinAt_pi.2 fun ν => hq x (upperOf μ ν)
  · exact continuousWithinAt_pi.2 fun x => continuousWithinAt_pi.2 fun μ =>
      continuousWithinAt_pi.2 fun ν => hv x (upperOf μ ν)

/-! ### The upper energy bound -/

theorem sum_Dp_Dα_sq_le (s : ℕ) (u : PeriodicGridSobolev.Grid N → ℂ) :
    ∑ α ∈ PeriodicGridSobolev.multiIndices s, ∑ i,
      PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dp i (PeriodicGridSobolev.Dα α u)) ≤
      3 * PeriodicGridSobolev.sobSq (s + 1) u := by
  open PeriodicGridSobolev PeriodicGridSobolev.CommutedRow in
  rw [Finset.sum_comm]
  have hi : ∀ i : Fin 3, ∑ α ∈ multiIndices s, gridNormSq (Dp i (Dα α u)) ≤
      sobSq (s + 1) u := by
    intro i
    have e : ∀ α : Fin 3 → ℕ, Dp i (Dα α u) = Dα (α + Pi.single i 1) u := by
      intro α
      rw [Dp_eq_Dα, ← Dα_add, add_comm]
    simp_rw [e]
    rw [← Finset.sum_image (f := fun β => gridNormSq (Dα β u)) (g := fun α => α + Pi.single i 1)
      (fun a _ b _ h => add_right_cancel h)]
    unfold sobSq
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => gridNormSq_nonneg _)
    intro β hβ
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hβ
    rw [mem_multiIndices] at hα ⊢
    rw [deg_add, deg_single_one]; omega
  calc _ ≤ ∑ _i : Fin 3, PeriodicGridSobolev.sobSq (s + 1) u := sum_le_sum fun i _ => hi i
    _ = 3 * PeriodicGridSobolev.sobSq (s + 1) u := by simp

/-- **Upper half of the energy equivalence**: on the chart, `𝓔_{s,h} ≤ 8 ‖X‖²_{X^s_h}`,
uniformly in the mesh. -/
theorem energy_upper (s : ℕ) (hs : 3 ≤ s) :
    ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (q v : Grid N → MetricRec), IsSymRec q → IsSymRec v →
      Xnorm s q v ≤ δ → shiftedEnergy s q v ≤ 8 * Xsq s q v := by
  obtain ⟨ε, hε, M, hM, hchart⟩ := exists_chart
  have hL := supConst_nonneg
  refine ⟨ε / (2 * (supConst + 1)), by positivity, fun N _ q v hq hv hX => ?_⟩
  have hqy : ∀ y, ‖q y‖ < ε := by
    intro y
    have h1 := norm_q_le s (by omega) hq v y
    have h2 : supConst * Xnorm s q v ≤ supConst * (ε / (2 * (supConst + 1))) :=
      mul_le_mul_of_nonneg_left hX hL
    have h3 : supConst * (ε / (2 * (supConst + 1))) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hch : ∀ y, _ := fun y => hchart (minkowski + q y) (by rw [add_sub_cancel_left]; exact hqy y)
  have ha : ∀ y, aArr q y ≤ 3 / 2 := fun y => by
    have := (hch y).1.2.2; simp only [aArr]; rw [abs_le] at this; linarith
  have hc : ∀ y i j, |cArr q i j y| ≤ 19 / 18 := fun y i j => by
    have h := ((hch y).2 i j).2.2
    have : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    calc |cArr q i j y| = |(harmC i j (minkowski + q y) - (if i = j then 1 else 0)) +
          (if i = j then 1 else 0)| := by simp [cArr]
      _ ≤ 1 / 18 + 1 := (abs_add_le _ _).trans (add_le_add h this)
      _ = 19 / 18 := by norm_num
  -- per-level bound
  have hlev : ∀ α ∈ PeriodicGridSobolev.multiIndices s,
      energy (SαR α (aArr q)) (fun i j => SαR α (cArr q i j))
        (fun κ : Upper => DαR α (comp q κ.1.1 κ.1.2))
        (fun κ : Upper => DαR α (comp v κ.1.1 κ.1.2))
      ≤ 2 * ∑ κ : Upper, (PeriodicGridSobolev.gridNormSq
          (PeriodicGridSobolev.Dα α (cx (comp v κ.1.1 κ.1.2))) +
        ∑ i, PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dp i
          (PeriodicGridSobolev.Dα α (cx (comp q κ.1.1 κ.1.2)))) +
        PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dα α (cx (comp q κ.1.1 κ.1.2)))) := by
    intro α _
    unfold energy
    have hpt : ∀ (κ : Upper) x,
        DαR α (comp v κ.1.1 κ.1.2) x * (SαR α (aArr q) x * DαR α (comp v κ.1.1 κ.1.2) x) +
          ∑ i, ∑ j, OpenWriterEnergy.Dp i (DαR α (comp q κ.1.1 κ.1.2)) x *
            (SαR α (cArr q i j) x * OpenWriterEnergy.Dp j (DαR α (comp q κ.1.1 κ.1.2)) x) +
          DαR α (comp q κ.1.1 κ.1.2) x ^ 2 ≤
        4 * (DαR α (comp v κ.1.1 κ.1.2) x ^ 2 +
          ∑ i, OpenWriterEnergy.Dp i (DαR α (comp q κ.1.1 κ.1.2)) x ^ 2 +
          DαR α (comp q κ.1.1 κ.1.2) x ^ 2) := by
      intro κ x
      have h1 : DαR α (comp v κ.1.1 κ.1.2) x *
          (SαR α (aArr q) x * DαR α (comp v κ.1.1 κ.1.2) x) ≤
          3 / 2 * DαR α (comp v κ.1.1 κ.1.2) x ^ 2 := by
        have := ha (x + svec α)
        have e : SαR α (aArr q) x = aArr q (x + svec α) := rfl
        rw [e]; nlinarith [sq_nonneg (DαR α (comp v κ.1.1 κ.1.2) x)]
      have h2 := quad_upper (fun i => OpenWriterEnergy.Dp i (DαR α (comp q κ.1.1 κ.1.2)) x)
        (fun i j => SαR α (cArr q i j) x) (19 / 18) (fun i j => hc (x + svec α) i j)
      have h3 : 0 ≤ ∑ i, OpenWriterEnergy.Dp i (DαR α (comp q κ.1.1 κ.1.2)) x ^ 2 :=
        sum_nonneg fun _ _ => sq_nonneg _
      have h4 := sq_nonneg (DαR α (comp v κ.1.1 κ.1.2) x)
      have h5 := sq_nonneg (DαR α (comp q κ.1.1 κ.1.2) x)
      linarith
    have hN : (0 : ℝ) ≤ ((N : ℝ) ^ 3)⁻¹ := by positivity
    calc ((N : ℝ) ^ 3)⁻¹ * (1 / 2) * ∑ κ : Upper, ∑ x, _
        ≤ ((N : ℝ) ^ 3)⁻¹ * (1 / 2) * ∑ κ : Upper, ∑ x,
          4 * (DαR α (comp v κ.1.1 κ.1.2) x ^ 2 +
            ∑ i, OpenWriterEnergy.Dp i (DαR α (comp q κ.1.1 κ.1.2)) x ^ 2 +
            DαR α (comp q κ.1.1 κ.1.2) x ^ 2) := by
          gcongr with κ _ x _
          exact hpt κ x
      _ = 2 * ∑ κ : Upper, (((N : ℝ) ^ 3)⁻¹ * ∑ x, DαR α (comp v κ.1.1 κ.1.2) x ^ 2 +
          ∑ i, ((N : ℝ) ^ 3)⁻¹ * ∑ x, OpenWriterEnergy.Dp i (DαR α (comp q κ.1.1 κ.1.2)) x ^ 2 +
          ((N : ℝ) ^ 3)⁻¹ * ∑ x, DαR α (comp q κ.1.1 κ.1.2) x ^ 2) := by
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun κ _ => ?_
          simp only [← mul_sum, sum_add_distrib, mul_add]
          rw [sum_comm (s := univ) (t := univ) (f := fun x i =>
            OpenWriterEnergy.Dp i (DαR α (comp q κ.1.1 κ.1.2)) x ^ 2)]
          simp only [mul_sum]
          ring
      _ = _ := by
          refine congrArg _ (sum_congr rfl fun κ _ => ?_)
          rw [← gridNormSq_cx, ← gridNormSq_cx, cx_DαR, cx_DαR]
          congr 1
          congr 1
          refine sum_congr rfl fun i _ => ?_
          rw [← gridNormSq_cx, cx_Dp, cx_DαR]
  calc shiftedEnergy s q v ≤ ∑ α ∈ PeriodicGridSobolev.multiIndices s,
        2 * ∑ κ : Upper, (PeriodicGridSobolev.gridNormSq
          (PeriodicGridSobolev.Dα α (cx (comp v κ.1.1 κ.1.2))) +
        ∑ i, PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dp i
          (PeriodicGridSobolev.Dα α (cx (comp q κ.1.1 κ.1.2)))) +
        PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dα α (cx (comp q κ.1.1 κ.1.2)))) :=
        sum_le_sum hlev
    _ = 2 * ∑ κ : Upper, (PeriodicGridSobolev.sobSq s (cx (comp v κ.1.1 κ.1.2)) +
        ∑ α ∈ PeriodicGridSobolev.multiIndices s, ∑ i, PeriodicGridSobolev.gridNormSq
          (PeriodicGridSobolev.Dp i (PeriodicGridSobolev.Dα α (cx (comp q κ.1.1 κ.1.2)))) +
        PeriodicGridSobolev.sobSq s (cx (comp q κ.1.1 κ.1.2))) := by
        rw [← mul_sum, sum_comm]
        congr 1
        refine sum_congr rfl fun κ _ => ?_
        simp only [sum_add_distrib, PeriodicGridSobolev.sobSq]
    _ ≤ 2 * ∑ κ : Upper, (PeriodicGridSobolev.sobSq s (cx (comp v κ.1.1 κ.1.2)) +
        3 * PeriodicGridSobolev.sobSq (s + 1) (cx (comp q κ.1.1 κ.1.2)) +
        PeriodicGridSobolev.sobSq (s + 1) (cx (comp q κ.1.1 κ.1.2))) := by
        gcongr with κ _
        · exact sum_Dp_Dα_sq_le s _
        · exact PeriodicGridSobolev.sobSq_mono (by omega) _
    _ ≤ 8 * Xsq s q v := by
        unfold Xsq
        rw [mul_sum, mul_sum]
        refine sum_le_sum fun κ _ => ?_
        have := PeriodicGridSobolev.sobSq_nonneg s (cx (comp v κ.1.1 κ.1.2))
        have := PeriodicGridSobolev.sobSq_nonneg (s + 1) (cx (comp q κ.1.1 κ.1.2))
        linarith

/-! ### The a priori bound on a common time -/

/-- A record history `t ↦ (q(t), v(t))` **solves the open writer on `[0, T]`** (ten-component
form): at every `t ∈ [0, T]` the records are symmetric, `q_t = v` and the ten upper components
of `v` have time derivative the writer acceleration (two-sided derivatives). -/
def IsWriterSolution (T : ℝ) (q v : ℝ → Grid N → MetricRec) : Prop :=
  ∀ t ∈ Icc 0 T, IsSymRec (q t) ∧ IsSymRec (v t) ∧
    (∀ x, HasDerivAt (fun τ => q τ x) (v t x) t) ∧
    (∀ x (κ : Upper), HasDerivAt (fun τ => v τ x κ.1.1 κ.1.2)
      (harmonicWriterAcceleration (q t) (v t) x κ.1.1 κ.1.2) t)

/-- **A priori bound on a common time** (scalar comparison for `eq:supp-open-energy-inequality`).
There are `b, T > 0` and `C ≥ 1`, independent of the mesh, such that every writer solution on
`[0, t]`, `t ≤ T`, which stays in the chart `‖X‖_{X^s_h} ≤ b`, satisfies
`‖X(t)‖_{X^s_h} ≤ C ‖X(0)‖_{X^s_h}`. -/
theorem apriori_bound (s : ℕ) (hs : 3 ≤ s) :
    ∃ b > 0, ∃ T > 0, ∃ C ≥ 1, ∀ (N : ℕ) [NeZero N] (q v : ℝ → Grid N → MetricRec) (t : ℝ),
      0 ≤ t → t ≤ T → IsWriterSolution t q v → (∀ τ ∈ Icc 0 t, Xnorm s (q τ) (v τ) ≤ b) →
      Xnorm s (q t) (v t) ≤ C * Xnorm s (q 0) (v 0) := by
  obtain ⟨δE, hδE, CE, hCE, hE⟩ := open_energy_inequality s hs
  obtain ⟨δU, hδU, hU⟩ := energy_upper s hs
  set b : ℝ := min (min δE δU) (1 / 4)
  have hb : 0 < b := by positivity
  set T : ℝ := 1 / (2 * CE + 1)
  have hT : 0 < T := by positivity
  set C : ℝ := Real.sqrt (32 * Real.exp 1)
  have hC1 : 1 ≤ C := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    refine Real.sqrt_le_sqrt ?_
    have := Real.add_one_le_exp 1
    linarith
  refine ⟨b, hb, T, hT, C, hC1, fun N _ q v t ht0 htT hsol hX => ?_⟩
  set E : ℝ → ℝ := fun τ => shiftedEnergy s (q τ) (v τ)
  have hbE : b ≤ δE := (min_le_left _ _).trans (min_le_left _ _)
  have hbU : b ≤ δU := (min_le_left _ _).trans (min_le_right _ _)
  have hb4 : b ≤ 1 / 4 := min_le_right _ _
  -- pointwise facts on `[0, t]`
  have hpt : ∀ τ ∈ Icc 0 t, ∃ r, HasDerivAt E r τ ∧ Xsq s (q τ) (v τ) / 4 ≤ E τ ∧
      E τ ≤ 8 * Xsq s (q τ) (v τ) ∧ r ≤ 2 * CE * E τ := by
    intro τ hτ
    obtain ⟨hqs, hvs, hq, hv⟩ := hsol τ hτ
    have hXτ := hX τ hτ
    obtain ⟨hd, hlow, hrate⟩ := hE N q v τ hqs hvs hq hv (hXτ.trans hbE)
    have hup := hU N (q τ) (v τ) hqs hvs (hXτ.trans hbU)
    refine ⟨_, hd, hlow, hup, ?_⟩
    have hE0 : 0 ≤ E τ := le_trans (by have := Xsq_nonneg s (q τ) (v τ); linarith) hlow
    have hE1 : E τ ≤ 1 := by
      have h1 : Xsq s (q τ) (v τ) = Xnorm s (q τ) (v τ) ^ 2 := (Xnorm_sq _ _ _).symm
      have h2 : Xnorm s (q τ) (v τ) ^ 2 ≤ (1 / 4) ^ 2 :=
        pow_le_pow_left₀ (Xnorm_nonneg _ _ _) (hXτ.trans hb4) 2
      show shiftedEnergy s (q τ) (v τ) ≤ 1
      nlinarith
    have hsq : E τ ^ ((3 : ℝ) / 2) ≤ E τ := by
      rw [rpow_three_halves hE0]
      have : Real.sqrt (E τ) ≤ 1 := Real.sqrt_le_one.mpr hE1
      nlinarith
    have : CE * E τ ^ ((3 : ℝ) / 2) ≤ CE * E τ := mul_le_mul_of_nonneg_left hsq hCE
    show energyRate s (q τ) (v τ) ≤ 2 * CE * E τ
    linarith
  choose! r hr using hpt
  -- `φ = E e^{-2CE τ}` is antitone
  set φ : ℝ → ℝ := fun τ => E τ * Real.exp (-(2 * CE) * τ)
  have hφd : ∀ τ ∈ Icc 0 t, HasDerivAt φ (r τ * Real.exp (-(2 * CE) * τ) +
      E τ * (Real.exp (-(2 * CE) * τ) * (-(2 * CE)))) τ := by
    intro τ hτ
    have h1 := (hr τ hτ).1
    have h2 : HasDerivAt (fun σ => Real.exp (-(2 * CE) * σ))
        (Real.exp (-(2 * CE) * τ) * (-(2 * CE))) τ := by
      have := ((hasDerivAt_id τ).const_mul (-(2 * CE))).exp
      simpa using this
    exact h1.mul h2
  have hanti : AntitoneOn φ (Icc 0 t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t) ?_ ?_ ?_
    · exact fun τ hτ => (hφd τ hτ).continuousAt.continuousWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      exact (hφd τ (Ioo_subset_Icc_self hτ)).differentiableAt.differentiableWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      rw [(hφd τ (Ioo_subset_Icc_self hτ)).deriv]
      have hrτ := (hr τ (Ioo_subset_Icc_self hτ)).2.2.2
      have hex := Real.exp_pos (-(2 * CE) * τ)
      nlinarith
  have h0mem : (0 : ℝ) ∈ Icc 0 t := ⟨le_rfl, ht0⟩
  have htmem : t ∈ Icc 0 t := ⟨ht0, le_rfl⟩
  have hφ := hanti h0mem htmem ht0
  simp only [φ, mul_zero, Real.exp_zero, mul_one] at hφ
  -- `E(t) ≤ e E(0)`
  have hexp : Real.exp (2 * CE * t) ≤ Real.exp 1 := by
    refine Real.exp_le_exp.mpr ?_
    have : 2 * CE * t ≤ 2 * CE * T := mul_le_mul_of_nonneg_left htT (by positivity)
    have hT1 : 2 * CE * T ≤ 1 := by
      simp only [T]; rw [mul_one_div, div_le_one (by positivity)]; linarith
    linarith
  have hEt : E t ≤ E 0 * Real.exp 1 := by
    have h1 : E t = E t * Real.exp (-(2 * CE) * t) * Real.exp (2 * CE * t) := by
      rw [mul_assoc, ← Real.exp_add]; simp
    have hE0 : 0 ≤ E 0 := le_trans (by have := Xsq_nonneg s (q 0) (v 0); linarith)
      (hr 0 h0mem).2.1
    rw [h1]
    calc E t * Real.exp (-(2 * CE) * t) * Real.exp (2 * CE * t)
        ≤ E 0 * Real.exp (2 * CE * t) :=
          mul_le_mul_of_nonneg_right hφ (Real.exp_pos _).le
      _ ≤ E 0 * Real.exp 1 := mul_le_mul_of_nonneg_left hexp hE0
  -- conclude
  have hXt : Xsq s (q t) (v t) ≤ 32 * Real.exp 1 * Xsq s (q 0) (v 0) := by
    have h1 := (hr t htmem).2.1
    have h2 := (hr 0 h0mem).2.2.1
    have he := Real.exp_pos 1
    nlinarith
  rw [Xnorm, Xnorm, show C = Real.sqrt (32 * Real.exp 1) from rfl, ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt hXt

/-! ### Symmetry and solutions of the field -/

/-- **Symmetry is preserved** (by uniqueness): a solution of the field starting from a symmetric
state and staying in the Lipschitz region is symmetric. -/
theorem symL_eq_of_field_solution {L : ℝ≥0} {ρ t : ℝ}
    (hL : LipschitzOnWith L (writerField (N := N)) {y | ‖symL y‖ ≤ 2 * ρ})
    (y : ℝ → State N) (hy : ∀ τ ∈ Icc 0 t, HasDerivAt y (writerField (y τ)) τ)
    (hreg : ∀ τ ∈ Icc 0 t, ‖symL (y τ)‖ ≤ 2 * ρ) (h0 : symL (y 0) = y 0) :
    ∀ τ ∈ Icc 0 t, symL (y τ) = y τ := by
  have hz : ∀ τ ∈ Icc 0 t, HasDerivAt (fun σ => symL (y σ)) (writerField (symL (y τ))) τ := by
    intro τ hτ
    have := (symL : State N →L[ℝ] State N).hasFDerivAt.comp_hasDerivAt τ (hy τ hτ)
    rw [writerField_symL, ← symL_writerField]
    exact this
  have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ => writerField (N := N))
    (s := fun _ => {y | ‖symL y‖ ≤ 2 * ρ}) (K := L) (a := 0) (b := t)
    (f := fun σ => symL (y σ)) (g := y) (fun _ _ => hL)
    (fun τ hτ => (hz τ hτ).continuousAt.continuousWithinAt)
    (fun τ hτ => (hz τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt)
    (fun τ hτ => by
      show ‖symL (symL (y τ))‖ ≤ 2 * ρ
      rw [symL_symL]; exact hreg τ (Ico_subset_Icc_self hτ))
    (fun τ hτ => (hy τ hτ).continuousAt.continuousWithinAt)
    (fun τ hτ => (hy τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt)
    (fun τ hτ => hreg τ (Ico_subset_Icc_self hτ)) h0
  exact fun τ hτ => heq hτ

theorem fst_eq_of_symL {y : State N} (h : symL y = y) : symRec y.1 = y.1 := by
  have := congrArg Prod.fst h; simpa [symL_apply] using this

theorem snd_eq_of_symL {y : State N} (h : symL y = y) : symRec y.2 = y.2 := by
  have := congrArg Prod.snd h; simpa [symL_apply] using this

/-- A symmetric solution of the field is a solution of the open writer. -/
theorem isWriterSolution_of_field {T : ℝ} (y : ℝ → State N)
    (hy : ∀ τ ∈ Icc 0 T, HasDerivAt y (writerField (y τ)) τ)
    (hsym : ∀ τ ∈ Icc 0 T, symL (y τ) = y τ) :
    IsWriterSolution T (fun τ => (y τ).1) (fun τ => (y τ).2) := by
  intro τ hτ
  have h1 := fst_eq_of_symL (hsym τ hτ)
  have h2 := snd_eq_of_symL (hsym τ hτ)
  have hfst : HasDerivAt (fun σ => (y σ).1) (writerField (y τ)).1 τ :=
    (ContinuousLinearMap.fst ℝ (Grid N → MetricRec) (Grid N → MetricRec)).hasFDerivAt.comp_hasDerivAt τ (hy τ hτ)
  have hsnd : HasDerivAt (fun σ => (y σ).2) (writerField (y τ)).2 τ :=
    (ContinuousLinearMap.snd ℝ (Grid N → MetricRec) (Grid N → MetricRec)).hasFDerivAt.comp_hasDerivAt τ (hy τ hτ)
  refine ⟨show IsSymRec (y τ).1 by rw [← h1]; exact isSymRec_symRec _,
    show IsSymRec (y τ).2 by rw [← h2]; exact isSymRec_symRec _,
    fun x => ?_, fun x κ => ?_⟩
  · have := hasDerivAt_pi.1 hfst x
    simp only [writerField, h2] at this
    exact this
  · have := hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_pi.1 hsnd x) κ.1.1) κ.1.2
    simp only [writerField, h1, h2, symRec_upper] at this
    exact this

/-- A writer solution, viewed as a state history, solves the field to the right of each time
of `[0, T)`. -/
theorem hasDerivWithinAt_field_of_writer {T : ℝ} {q v : ℝ → Grid N → MetricRec}
    (hsol : IsWriterSolution T q v) {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun τ => ((q τ, v τ) : State N)) (writerField (q t, v t)) (Ici t) t := by
  obtain ⟨hqs, hvs, hq, hv⟩ := hsol t (Ico_subset_Icc_self ht)
  have e : writerField ((q t, v t) : State N) =
      (v t, symRec (harmonicWriterAcceleration (q t) (v t))) := by
    simp only [writerField, symRec_of_isSymRec hqs, symRec_of_isSymRec hvs]
  rw [e]
  refine HasDerivWithinAt.prodMk ?_ ?_
  · exact (hasDerivAt_pi.2 fun x => hq x).hasDerivWithinAt
  · refine hasDerivWithinAt_pi.2 fun x => hasDerivWithinAt_pi.2 fun μ =>
      hasDerivWithinAt_pi.2 fun ν => ?_
    have h1 := (hv x (upperOf μ ν)).hasDerivWithinAt (s := Ici t)
    refine h1.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [Ico_mem_nhdsGE ht.2] with σ hσ
      have hσs := (hsol σ ⟨ht.1.trans hσ.1, hσ.2.le⟩).2.1
      exact (congrFun (comp_upperOf hσs μ ν) x).symm
    · exact (congrFun (comp_upperOf hvs μ ν) x).symm

/-- A writer solution is continuous on `[0, T]` as a state history. -/
theorem continuousOn_of_writer {T : ℝ} {q v : ℝ → Grid N → MetricRec}
    (hsol : IsWriterSolution T q v) :
    ContinuousOn (fun τ => ((q τ, v τ) : State N)) (Icc 0 T) := by
  intro t ht
  obtain ⟨-, hvs, hq, hv⟩ := hsol t ht
  refine ContinuousWithinAt.prodMk ?_ ?_
  · exact (hasDerivAt_pi.2 fun x => hq x).continuousAt.continuousWithinAt
  · refine continuousWithinAt_pi.2 fun x => continuousWithinAt_pi.2 fun μ =>
      continuousWithinAt_pi.2 fun ν => ?_
    refine (hv x (upperOf μ ν)).continuousAt.continuousWithinAt.congr (fun σ hσ => ?_) ?_
    · exact (congrFun (comp_upperOf (hsol σ hσ).2.1 μ ν) x).symm
    · exact (congrFun (comp_upperOf hvs μ ν) x).symm

/-! ### The common lifespan -/

/-- **`cor:supp-open-lifespan`, first clause (common nonlinear time); `(O1)` of
`thm:main-open-3plus1`.**  For every `s ≥ 3` (the manuscript takes `s ≥ 11`) there are
`ε_s, T_s > 0` and `C_s ≥ 0`, independent of the mesh `h = 1/N`, such that for every `N` and every
real ten-component (symmetric) initial record `X(0) = (q₀, v₀)` with `‖X(0)‖_{X^s_h} ≤ ε_s`:
* there is a solution of the open writer `eq:main-open-writer` on `[0, T_s]` with
  `sup_{t ≤ T_s} ‖X(t)‖_{X^s_h} ≤ C_s ‖X(0)‖_{X^s_h}` (`eq:main-open-uniform-time`);
* any two solutions on `[0, T_s]` with this initial record coincide on `[0, T_s]`.
No symmetry beyond the ten-component structure, Fourier restriction or `N`-dependent amplitude is
imposed. -/
theorem open_writer_lifespan (s : ℕ) (hs : 3 ≤ s) :
    ∃ ε > 0, ∃ T > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (q₀ v₀ : Grid N → MetricRec),
      IsSymRec q₀ → IsSymRec v₀ → Xnorm s q₀ v₀ ≤ ε →
      (∃ q v : ℝ → Grid N → MetricRec, q 0 = q₀ ∧ v 0 = v₀ ∧ IsWriterSolution T q v ∧
        ∀ t ∈ Icc 0 T, Xnorm s (q t) (v t) ≤ C * Xnorm s q₀ v₀) ∧
      ∀ q v q' v' : ℝ → Grid N → MetricRec, q 0 = q₀ → v 0 = v₀ → q' 0 = q₀ → v' 0 = v₀ →
        IsWriterSolution T q v → IsWriterSolution T q' v' →
        ∀ t ∈ Icc 0 T, q t = q' t ∧ v t = v' t := by
  obtain ⟨b, hb, T, hT, C, hC1, hap⟩ := apriori_bound s hs
  obtain ⟨r₀, hr₀, hchart⟩ := exists_det_chart
  set ρ : ℝ := r₀ / 4
  have hρ : 0 < ρ := by positivity
  have hρr : 2 * ρ < r₀ := by simp only [ρ]; linarith
  have hS := supConst_nonneg
  set b' : ℝ := min b (ρ / (supConst + 1))
  have hb' : 0 < b' := by positivity
  have hb'b : b' ≤ b := min_le_left _ _
  set a : ℝ := b' / 2
  have ha : 0 < a := by positivity
  have hab : a < b' := by simp only [a]; linarith
  set ε : ℝ := a / C
  have hε : 0 < ε := by positivity
  have hεa : ε ≤ a := div_le_self ha.le hC1
  have hCε : C * ε = a := by simp only [ε]; field_simp
  refine ⟨ε, hε, T, hT, C, by linarith, fun N _ q₀ v₀ hq₀ hv₀ hX₀ => ?_⟩
  obtain ⟨L, M, hL, hM⟩ := exists_lipschitz_writerField hchart hρr N
  have hregion : ∀ y : State N, Xnorm s y.1 y.2 ≤ b' → ‖symL y‖ ≤ ρ := by
    intro y hy
    refine (norm_symL_le s (by omega) y).trans ?_
    have h1 : b' ≤ ρ / (supConst + 1) := min_le_right _ _
    calc supConst * Xnorm s y.1 y.2 ≤ supConst * (ρ / (supConst + 1)) :=
          mul_le_mul_of_nonneg_left (hy.trans h1) hS
      _ ≤ ρ := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  set x₀ : State N := (q₀, v₀)
  have hsym₀ : symL x₀ = x₀ := by
    simp only [x₀, symL_apply, symRec_of_isSymRec hq₀, symRec_of_isSymRec hv₀]
  -- the a priori bound for solutions of the field
  have hfield : ∀ y : ℝ → State N, y 0 = x₀ → ∀ t ∈ Icc 0 T,
      (∀ τ ∈ Icc 0 t, HasDerivAt y (writerField (y τ)) τ ∧ Xnorm s (y τ).1 (y τ).2 ≤ b') →
      (∀ τ ∈ Icc 0 t, symL (y τ) = y τ) ∧ Xnorm s (y t).1 (y t).2 ≤ C * Xnorm s q₀ v₀ := by
    intro y hy0 t ht hpre
    have hsy := symL_eq_of_field_solution hL y (fun τ hτ => (hpre τ hτ).1)
      (fun τ hτ => by have := hregion _ (hpre τ hτ).2; linarith) (by rw [hy0]; exact hsym₀)
    refine ⟨hsy, ?_⟩
    have hws := isWriterSolution_of_field y (fun τ hτ => (hpre τ hτ).1) hsy
    have := hap N (fun τ => (y τ).1) (fun τ => (y τ).2) t ht.1 ht.2 hws
      (fun τ hτ => (hpre τ hτ).2.trans hb'b)
    simpa [hy0, x₀] using this
  constructor
  · -- existence
    obtain ⟨y, hy0, hy⟩ := ODECutoff.exists_solution_of_apriori (writerField (N := N))
      (fun y => ‖symL y‖) (fun y => Xnorm s y.1 y.2) (KΦ := 1 * ‖(symL : State N →L[ℝ] State N)‖₊)
      hρ (lipschitzWith_one_norm.comp (symL : State N →L[ℝ] State N).lipschitz) hL hM
      (continuous_XnormS s) hab hregion hT.le x₀ (hX₀.trans hεa)
      (fun y hy0 t ht hpre => ((hfield y hy0 t ht hpre).2).trans (by
        rw [← hCε]; exact mul_le_mul_of_nonneg_left hX₀ (by linarith)))
    have hpre : ∀ t ∈ Icc 0 T, ∀ τ ∈ Icc 0 t,
        HasDerivAt y (writerField (y τ)) τ ∧ Xnorm s (y τ).1 (y τ).2 ≤ b' := fun t ht τ hτ =>
      ⟨(hy τ ⟨hτ.1, hτ.2.trans ht.2⟩).1, (hy τ ⟨hτ.1, hτ.2.trans ht.2⟩).2.trans hab.le⟩
    have hsy := (hfield y hy0 T ⟨hT.le, le_rfl⟩ (hpre T ⟨hT.le, le_rfl⟩)).1
    refine ⟨fun τ => (y τ).1, fun τ => (y τ).2, by simp [hy0, x₀], by simp [hy0, x₀],
      isWriterSolution_of_field y (fun τ hτ => (hy τ hτ).1) hsy, fun t ht => ?_⟩
    exact (hfield y hy0 t ht (hpre t ht)).2
  · -- uniqueness
    intro q v q' v' hq0 hv0 hq0' hv0' hsol hsol'
    have hstay : ∀ q v : ℝ → Grid N → MetricRec, q 0 = q₀ → v 0 = v₀ → IsWriterSolution T q v →
        ∀ t ∈ Icc 0 T, Xnorm s (q t) (v t) ≤ a := by
      intro q v hq0 hv0 hsol
      have hcont : ContinuousOn (fun τ => Xnorm s (q τ) (v τ)) (Icc 0 T) := by
        intro t ht
        obtain ⟨-, -, hq, hv⟩ := hsol t ht
        exact continuousWithinAt_Xnorm s
          (fun x κ => (hasDerivAt_pi.1 (hasDerivAt_pi.1 (hq x) κ.1.1) κ.1.2).continuousAt
            |>.continuousWithinAt)
          (fun x κ => (hv x κ).continuousAt.continuousWithinAt)
      refine ODECutoff.firstExit_le hcont hab (by rw [hq0, hv0]; exact hX₀.trans hεa)
        fun t ht hbt => ?_
      have hws : IsWriterSolution t q v := fun τ hτ => hsol τ ⟨hτ.1, hτ.2.trans ht.2⟩
      have := hap N q v t ht.1 ht.2 hws fun τ hτ => (hbt τ hτ).trans hb'b
      rw [hq0, hv0] at this
      refine this.trans ?_
      rw [← hCε]; exact mul_le_mul_of_nonneg_left hX₀ (by linarith)
    have hs1 := hstay q v hq0 hv0 hsol
    have hs2 := hstay q' v' hq0' hv0' hsol'
    have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ => writerField (N := N))
      (s := fun _ => {y | ‖symL y‖ ≤ 2 * ρ}) (K := L) (a := 0) (b := T)
      (f := fun τ => ((q τ, v τ) : State N)) (g := fun τ => ((q' τ, v' τ) : State N))
      (fun _ _ => hL) (continuousOn_of_writer hsol)
      (fun t ht => hasDerivWithinAt_field_of_writer hsol ht)
      (fun t ht => by
        have := hregion ((q t, v t) : State N) ((hs1 t (Ico_subset_Icc_self ht)).trans hab.le)
        show ‖symL ((q t, v t) : State N)‖ ≤ 2 * ρ
        linarith)
      (continuousOn_of_writer hsol')
      (fun t ht => hasDerivWithinAt_field_of_writer hsol' ht)
      (fun t ht => by
        have := hregion ((q' t, v' t) : State N) ((hs2 t (Ico_subset_Icc_self ht)).trans hab.le)
        show ‖symL ((q' t, v' t) : State N)‖ ≤ 2 * ρ
        linarith)
      (by simp only [hq0, hv0, hq0', hv0'])
    intro t ht
    have := heq ht
    simp only [Prod.mk.injEq] at this
    exact this

/-- Non-vacuity: the flat initial record lies in the small-data ball of `open_writer_lifespan`
for every `N`. -/
example (s : ℕ) (hs : 3 ≤ s) : True := by
  obtain ⟨ε, hε, T, hT, C, hC, h⟩ := open_writer_lifespan s hs
  have hX : Xnorm s (0 : Grid 5 → MetricRec) 0 ≤ ε := by
    have : Xsq s (0 : Grid 5 → MetricRec) 0 = 0 := by
      unfold Xsq
      refine sum_eq_zero fun κ _ => ?_
      have e : cx (comp (0 : Grid 5 → MetricRec) κ.1.1 κ.1.2) = 0 := by funext x; simp [comp, cx]
      rw [e]
      simp [PeriodicGridSobolev.sobSq, PeriodicGridSobolev.gridNormSq]
    rw [Xnorm, this, Real.sqrt_zero]; exact hε.le
  have hsym : IsSymRec (0 : Grid 5 → MetricRec) := fun _ _ _ => rfl
  obtain ⟨⟨q, v, -, -, -, -⟩, -⟩ := h 5 0 0 hsym hsym hX
  trivial
end

end RenewalGeometry.OpenWriterLifespan
