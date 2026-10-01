/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterDifferenceEstimate

/-!
# The open law family `B` of local differential writers (`thm:supp-law-stability`)

The law family `eq:supp-law-family` (= `eq:main-open-law-family`) adds to the open writer the
fixed-radius fourth-order stencil `-h² B Λ_h² q`, `Λ_h = -Σ_i D_i⁻ D_i⁺`, with a constant symmetric
`10 × 10` coefficient `B` of operator norm at most `b₀`:
`q_t = v`, `a(g) v_t = Σ D_i⁻(c^{ij} D_j⁺ q) - 𝖪_b v + 𝖦_h(q, v) - h² B Λ_h² q`.

* Generic first-exit lifespan (`lifespan_core`): for any acceleration map on ten-component
  records which is analytic on a fixed sup-norm ball and satisfies an a priori bound on a
  common time, solutions exist, are unique and obey the bound (used for the open writer and
  for every member of the law family);
* `lapR`, `sobNorm_Dm_mesh`, `law_domination`: the discrete Laplacian, the inverse-mesh bound
  `h ‖D_i^± w‖_{r,h} ≤ 2 ‖w‖_{r,h}`, and `h² ‖Λ_h w‖² ≤ 12 Σ_i ‖D_i⁺ w‖²`
  (`eq:supp-law-domination`), `h² ‖Λ_h² q‖_{r,h} ≤ 36 ‖q‖_{r+2,h}`;
* `lawEnergy` (`eq:supp-law-energy`), the cancellation identity
  `-h² ⟨v_α, B Λ_h² q_α⟩ = -(d/dt)(h²/2)⟨Λ_h q_α, B Λ_h q_α⟩`, the positivity margin and the
  energy inequality `law_energy_inequality` (`eq:supp-law-energy-bound`);
* `law_lifespan` (`eq:supp-law-lifespan`) and `law_forced_energy` (`eq:supp-law-forced`):
  **`thm:supp-law-stability`**.
-/

open Set Metric Filter Topology Finset MeasureTheory
open scoped NNReal BigOperators

namespace RenewalGeometry.OpenWriterLifespan

open RootParityConnector OpenWriterGridBridge OpenWriterChart OpenWriterEnergy HarmonicWriter
  OpenWriterEnergyEstimate

noncomputable section

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-! ### Generic first-exit lifespan for ten-component accelerations -/

/-- The vector field of an acceleration map, evaluated on the symmetrized state. -/
def accField (Acc : (Grid N → MetricRec) → (Grid N → MetricRec) → Grid N → MetricRec)
    (y : State N) : State N :=
  (symRec y.2, symRec (Acc (symRec y.1) (symRec y.2)))

theorem accField_symL (Acc : (Grid N → MetricRec) → (Grid N → MetricRec) → Grid N → MetricRec)
    (y : State N) : accField Acc (symL y) = accField Acc y := by
  simp only [accField, symL_apply, symRec_symRec]

theorem symL_accField (Acc : (Grid N → MetricRec) → (Grid N → MetricRec) → Grid N → MetricRec)
    (y : State N) : symL (accField Acc y) = accField Acc y := by
  simp only [accField, symL_apply, symRec_symRec]

/-- A record history solves `q_t = v`, `v_t = Acc(q, v)` (ten upper components, symmetric records,
two-sided derivatives) on `[0, T]`. -/
def IsAccSolution (Acc : (Grid N → MetricRec) → (Grid N → MetricRec) → Grid N → MetricRec)
    (T : ℝ) (q v : ℝ → Grid N → MetricRec) : Prop :=
  ∀ t ∈ Icc 0 T, IsSymRec (q t) ∧ IsSymRec (v t) ∧
    (∀ x, HasDerivAt (fun τ => q τ x) (v t x) t) ∧
    (∀ x (κ : Upper), HasDerivAt (fun τ => v τ x κ.1.1 κ.1.2) (Acc (q t) (v t) x κ.1.1 κ.1.2) t)

theorem isWriterSolution_iff (T : ℝ) (q v : ℝ → Grid N → MetricRec) :
    IsWriterSolution T q v ↔ IsAccSolution harmonicWriterAcceleration T q v := Iff.rfl

/-- Lipschitz bound of an analytic acceleration field on the symmetrized sup-ball. -/
theorem exists_lipschitz_accField
    (Acc : (Grid N → MetricRec) → (Grid N → MetricRec) → Grid N → MetricRec) {r₀ ρ : ℝ}
    (hAn : ∀ y : State N, ‖y‖ < r₀ → ∀ x μ ν,
      AnalyticAt ℝ (fun y : State N => Acc y.1 y.2 x μ ν) y) (hρ : 2 * ρ < r₀) :
    ∃ L M : ℝ≥0, LipschitzOnWith L (accField Acc) {y | ‖symL y‖ ≤ 2 * ρ} ∧
      ∀ y : State N, ‖symL y‖ ≤ 2 * ρ → ‖accField Acc y‖ ≤ M := by
  set core : State N → State N := fun y => (y.2, symRec (Acc y.1 y.2))
  have hcore : accField Acc = core ∘ (symL : State N →L[ℝ] State N) := rfl
  set B : Set (State N) := closedBall 0 (2 * ρ)
  have hanal : ∀ w ∈ B, AnalyticAt ℝ core w := by
    intro w hw
    have hw' : ‖w‖ < r₀ := lt_of_le_of_lt (mem_closedBall_zero_iff.mp hw) hρ
    refine AnalyticAt.prod (by fun_prop) (AnalyticAt.pi fun x => AnalyticAt.pi fun μ =>
      AnalyticAt.pi fun ν => ?_)
    exact hAn w hw' x _ _
  have hcd : ContDiffOn ℝ 1 core B := fun w hw => (hanal w hw).contDiffAt.contDiffWithinAt
  obtain ⟨K, hK⟩ := hcd.exists_lipschitzOnWith (by norm_num) (convex_closedBall _ _)
    (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : State N) (2 * ρ)).exists_bound_of_continuousOn
    hcd.continuousOn
  refine ⟨K * ‖(symL : State N →L[ℝ] State N)‖₊, Real.toNNReal C, ?_, fun y hy => ?_⟩
  · have hmaps : MapsTo (symL : State N →L[ℝ] State N) {y | ‖symL y‖ ≤ 2 * ρ} B :=
      fun y hy => mem_closedBall_zero_iff.mpr hy
    rw [hcore]
    exact hK.comp (symL : State N →L[ℝ] State N).lipschitz.lipschitzOnWith hmaps
  · rw [hcore]
    exact (hC _ (mem_closedBall_zero_iff.mpr hy)).trans (Real.le_coe_toNNReal C)

theorem symL_eq_of_acc_solution
    (Acc : (Grid N → MetricRec) → (Grid N → MetricRec) → Grid N → MetricRec) {L : ℝ≥0} {ρ t : ℝ}
    (hL : LipschitzOnWith L (accField Acc) {y | ‖symL y‖ ≤ 2 * ρ})
    (y : ℝ → State N) (hy : ∀ τ ∈ Icc 0 t, HasDerivAt y (accField Acc (y τ)) τ)
    (hreg : ∀ τ ∈ Icc 0 t, ‖symL (y τ)‖ ≤ 2 * ρ) (h0 : symL (y 0) = y 0) :
    ∀ τ ∈ Icc 0 t, symL (y τ) = y τ := by
  have hz : ∀ τ ∈ Icc 0 t, HasDerivAt (fun σ => symL (y σ)) (accField Acc (symL (y τ))) τ := by
    intro τ hτ
    have := (symL : State N →L[ℝ] State N).hasFDerivAt.comp_hasDerivAt τ (hy τ hτ)
    rw [accField_symL, ← symL_accField]
    exact this
  have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ => accField Acc)
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

theorem isAccSolution_of_field
    (Acc : (Grid N → MetricRec) → (Grid N → MetricRec) → Grid N → MetricRec) {T : ℝ}
    (y : ℝ → State N) (hy : ∀ τ ∈ Icc 0 T, HasDerivAt y (accField Acc (y τ)) τ)
    (hsym : ∀ τ ∈ Icc 0 T, symL (y τ) = y τ) :
    IsAccSolution Acc T (fun τ => (y τ).1) (fun τ => (y τ).2) := by
  intro τ hτ
  have h1 := fst_eq_of_symL (hsym τ hτ)
  have h2 := snd_eq_of_symL (hsym τ hτ)
  have hfst : HasDerivAt (fun σ => (y σ).1) (accField Acc (y τ)).1 τ :=
    (ContinuousLinearMap.fst ℝ (Grid N → MetricRec) (Grid N → MetricRec)).hasFDerivAt.comp_hasDerivAt
      τ (hy τ hτ)
  have hsnd : HasDerivAt (fun σ => (y σ).2) (accField Acc (y τ)).2 τ :=
    (ContinuousLinearMap.snd ℝ (Grid N → MetricRec) (Grid N → MetricRec)).hasFDerivAt.comp_hasDerivAt
      τ (hy τ hτ)
  refine ⟨show IsSymRec (y τ).1 by rw [← h1]; exact isSymRec_symRec _,
    show IsSymRec (y τ).2 by rw [← h2]; exact isSymRec_symRec _, fun x => ?_, fun x κ => ?_⟩
  · have := hasDerivAt_pi.1 hfst x
    simp only [accField, h2] at this
    exact this
  · have := hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_pi.1 hsnd x) κ.1.1) κ.1.2
    simp only [accField, h1, h2, symRec_upper] at this
    exact this

theorem hasDerivWithinAt_field_of_acc
    (Acc : (Grid N → MetricRec) → (Grid N → MetricRec) → Grid N → MetricRec) {T : ℝ}
    {q v : ℝ → Grid N → MetricRec} (hsol : IsAccSolution Acc T q v) {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun τ => ((q τ, v τ) : State N)) (accField Acc (q t, v t)) (Ici t) t := by
  obtain ⟨hqs, hvs, hq, hv⟩ := hsol t (Ico_subset_Icc_self ht)
  have e : accField Acc ((q t, v t) : State N) = (v t, symRec (Acc (q t) (v t))) := by
    simp only [accField, symRec_of_isSymRec hqs, symRec_of_isSymRec hvs]
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

theorem continuousOn_of_acc
    (Acc : (Grid N → MetricRec) → (Grid N → MetricRec) → Grid N → MetricRec) {T : ℝ}
    {q v : ℝ → Grid N → MetricRec} (hsol : IsAccSolution Acc T q v) :
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

/-- **Generic common lifespan** (first-exit argument, one mesh).  Let `Acc` be analytic on the
sup-ball of radius `r₀` and suppose the a priori bound: every solution on `[0, t]`, `t ≤ T`,
staying in `‖X‖_{X^s_h} ≤ b` satisfies `‖X(t)‖ ≤ C ‖X(0)‖` (`C ≥ 1`), where
`L_sup b ≤ r₀/4`.  Then every symmetric initial record with `‖X(0)‖ ≤ b/(2C)` has a solution on
`[0, T]` obeying `‖X(t)‖ ≤ C ‖X(0)‖`, and it is unique. -/
theorem lifespan_core (s : ℕ) (hs : 3 ≤ s)
    (Acc : (Grid N → MetricRec) → (Grid N → MetricRec) → Grid N → MetricRec) {r₀ b T C : ℝ}
    (hr₀ : 0 < r₀) (hb : 0 < b) (hT : 0 < T) (hC1 : 1 ≤ C) (hbr : supConst * b ≤ r₀ / 4)
    (hAn : ∀ y : State N, ‖y‖ < r₀ → ∀ x μ ν,
      AnalyticAt ℝ (fun y : State N => Acc y.1 y.2 x μ ν) y)
    (hap : ∀ (q v : ℝ → Grid N → MetricRec) (t : ℝ), 0 ≤ t → t ≤ T → IsAccSolution Acc t q v →
      (∀ τ ∈ Icc 0 t, Xnorm s (q τ) (v τ) ≤ b) → Xnorm s (q t) (v t) ≤ C * Xnorm s (q 0) (v 0))
    (q₀ v₀ : Grid N → MetricRec) (hq₀ : IsSymRec q₀) (hv₀ : IsSymRec v₀)
    (hX₀ : Xnorm s q₀ v₀ ≤ b / 2 / C) :
    (∃ q v : ℝ → Grid N → MetricRec, q 0 = q₀ ∧ v 0 = v₀ ∧ IsAccSolution Acc T q v ∧
      ∀ t ∈ Icc 0 T, Xnorm s (q t) (v t) ≤ C * Xnorm s q₀ v₀) ∧
    ∀ q v q' v' : ℝ → Grid N → MetricRec, q 0 = q₀ → v 0 = v₀ → q' 0 = q₀ → v' 0 = v₀ →
      IsAccSolution Acc T q v → IsAccSolution Acc T q' v' →
      ∀ t ∈ Icc 0 T, q t = q' t ∧ v t = v' t := by
  set ρ : ℝ := r₀ / 4
  have hρ : 0 < ρ := by positivity
  have hρr : 2 * ρ < r₀ := by simp only [ρ]; linarith
  set a : ℝ := b / 2
  have ha : 0 < a := by positivity
  have hab : a < b := by simp only [a]; linarith
  set ε : ℝ := a / C
  have hεa : ε ≤ a := div_le_self ha.le hC1
  have hCε : C * ε = a := by simp only [ε]; field_simp
  obtain ⟨L, M, hL, hM⟩ := exists_lipschitz_accField Acc hAn hρr
  have hS := supConst_nonneg
  have hregion : ∀ y : State N, Xnorm s y.1 y.2 ≤ b → ‖symL y‖ ≤ ρ := fun y hy =>
    (norm_symL_le s (by omega) y).trans ((mul_le_mul_of_nonneg_left hy hS).trans hbr)
  set x₀ : State N := (q₀, v₀)
  have hsym₀ : symL x₀ = x₀ := by
    simp only [x₀, symL_apply, symRec_of_isSymRec hq₀, symRec_of_isSymRec hv₀]
  have hbound : C * Xnorm s q₀ v₀ ≤ a := by
    rw [← hCε]; exact mul_le_mul_of_nonneg_left hX₀ (by linarith)
  have hfield : ∀ y : ℝ → State N, y 0 = x₀ → ∀ t ∈ Icc 0 T,
      (∀ τ ∈ Icc 0 t, HasDerivAt y (accField Acc (y τ)) τ ∧ Xnorm s (y τ).1 (y τ).2 ≤ b) →
      (∀ τ ∈ Icc 0 t, symL (y τ) = y τ) ∧ Xnorm s (y t).1 (y t).2 ≤ C * Xnorm s q₀ v₀ := by
    intro y hy0 t ht hpre
    have hsy := symL_eq_of_acc_solution Acc hL y (fun τ hτ => (hpre τ hτ).1)
      (fun τ hτ => by have := hregion _ (hpre τ hτ).2; linarith) (by rw [hy0]; exact hsym₀)
    refine ⟨hsy, ?_⟩
    have hws := isAccSolution_of_field Acc y (fun τ hτ => (hpre τ hτ).1) hsy
    have := hap (fun τ => (y τ).1) (fun τ => (y τ).2) t ht.1 ht.2 hws
      (fun τ hτ => (hpre τ hτ).2)
    simpa [hy0, x₀] using this
  constructor
  · obtain ⟨y, hy0, hy⟩ := ODECutoff.exists_solution_of_apriori (accField Acc)
      (fun y => ‖symL y‖) (fun y => Xnorm s y.1 y.2) (KΦ := 1 * ‖(symL : State N →L[ℝ] State N)‖₊)
      hρ (lipschitzWith_one_norm.comp (symL : State N →L[ℝ] State N).lipschitz) hL hM
      (continuous_XnormS s) hab hregion hT.le x₀ (hX₀.trans hεa)
      (fun y hy0 t ht hpre => ((hfield y hy0 t ht hpre).2).trans hbound)
    have hpre : ∀ t ∈ Icc 0 T, ∀ τ ∈ Icc 0 t,
        HasDerivAt y (accField Acc (y τ)) τ ∧ Xnorm s (y τ).1 (y τ).2 ≤ b := fun t ht τ hτ =>
      ⟨(hy τ ⟨hτ.1, hτ.2.trans ht.2⟩).1, (hy τ ⟨hτ.1, hτ.2.trans ht.2⟩).2.trans hab.le⟩
    have hsy := (hfield y hy0 T ⟨hT.le, le_rfl⟩ (hpre T ⟨hT.le, le_rfl⟩)).1
    refine ⟨fun τ => (y τ).1, fun τ => (y τ).2, by simp [hy0, x₀], by simp [hy0, x₀],
      isAccSolution_of_field Acc y (fun τ hτ => (hy τ hτ).1) hsy, fun t ht => ?_⟩
    exact (hfield y hy0 t ht (hpre t ht)).2
  · intro q v q' v' hq0 hv0 hq0' hv0' hsol hsol'
    have hstay : ∀ q v : ℝ → Grid N → MetricRec, q 0 = q₀ → v 0 = v₀ → IsAccSolution Acc T q v →
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
      have hws : IsAccSolution Acc t q v := fun τ hτ => hsol τ ⟨hτ.1, hτ.2.trans ht.2⟩
      have := hap q v t ht.1 ht.2 hws hbt
      rw [hq0, hv0] at this
      exact this.trans hbound
    have hs1 := hstay q v hq0 hv0 hsol
    have hs2 := hstay q' v' hq0' hv0' hsol'
    have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ => accField Acc)
      (s := fun _ => {y | ‖symL y‖ ≤ 2 * ρ}) (K := L) (a := 0) (b := T)
      (f := fun τ => ((q τ, v τ) : State N)) (g := fun τ => ((q' τ, v' τ) : State N))
      (fun _ _ => hL) (continuousOn_of_acc Acc hsol)
      (fun t ht => hasDerivWithinAt_field_of_acc Acc hsol ht)
      (fun t ht => by
        have := hregion ((q t, v t) : State N) ((hs1 t (Ico_subset_Icc_self ht)).trans hab.le)
        show ‖symL ((q t, v t) : State N)‖ ≤ 2 * ρ
        linarith)
      (continuousOn_of_acc Acc hsol')
      (fun t ht => hasDerivWithinAt_field_of_acc Acc hsol' ht)
      (fun t ht => by
        have := hregion ((q' t, v' t) : State N) ((hs2 t (Ico_subset_Icc_self ht)).trans hab.le)
        show ‖symL ((q' t, v' t) : State N)‖ ≤ 2 * ρ
        linarith)
      (by simp only [hq0, hv0, hq0', hv0'])
    intro t ht
    have := heq ht
    simp only [Prod.mk.injEq] at this
    exact this


/-! ### The discrete Laplacian and the mesh multiplier bounds -/

/-- The discrete Laplacian `Λ_h = -Σ_i D_i⁻ D_i⁺` on real arrays (`eq:supp-law-laplacian`). -/
def lapR (u : Grid N → ℝ) : Grid N → ℝ :=
  -∑ i, OpenWriterEnergy.Dm i (OpenWriterEnergy.Dp i u)

/-- The discrete Laplacian on complex arrays. -/
def lapC (w : PeriodicGridSobolev.Grid N → ℂ) : PeriodicGridSobolev.Grid N → ℂ :=
  -∑ i, PeriodicGridSobolev.Dm i (PeriodicGridSobolev.Dp i w)

theorem cx_lapR (u : Grid N → ℝ) : cx (lapR u) = lapC (cx u) := by
  unfold lapR lapC
  rw [cx_neg, cx_sum]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [cx_Dm, cx_Dp]

theorem Dα_lapC (α : Fin 3 → ℕ) (w : PeriodicGridSobolev.Grid N → ℂ) :
    PeriodicGridSobolev.Dα α (lapC w) = lapC (PeriodicGridSobolev.Dα α w) := by
  simp only [lapC, map_neg, map_sum, PeriodicGridSobolev.CommutedRow.Dα_Dm,
    PeriodicGridSobolev.CommutedRow.Dα_Dp]

theorem DαR_lapR (α : Fin 3 → ℕ) (u : Grid N → ℝ) : DαR α (lapR u) = lapR (DαR α u) := by
  apply cx_injective
  rw [cx_DαR, cx_lapR, cx_lapR, cx_DαR, Dα_lapC]

theorem gridNorm_Sinv (i : Fin 3) (w : PeriodicGridSobolev.Grid N → ℂ) :
    PeriodicGridSobolev.gridNorm (PeriodicGridSobolev.Sinv i w) = PeriodicGridSobolev.gridNorm w := by
  unfold PeriodicGridSobolev.gridNorm
  rw [PeriodicGridSobolev.gridNormSq_of_unimodular (PeriodicGridSobolev.isMult_Sinv i)
    (fun k => by rw [Complex.norm_conj, PeriodicGridSobolev.norm_chi])]

theorem gridNorm_S (i : Fin 3) (w : PeriodicGridSobolev.Grid N → ℂ) :
    PeriodicGridSobolev.gridNorm (PeriodicGridSobolev.S i w) = PeriodicGridSobolev.gridNorm w := by
  unfold PeriodicGridSobolev.gridNorm
  rw [PeriodicGridSobolev.gridNormSq_of_unimodular (PeriodicGridSobolev.isMult_S i)
    (fun k => PeriodicGridSobolev.norm_chi i k)]

/-- **Inverse-mesh bound** `h ‖D_i⁻ w‖_h ≤ 2 ‖w‖_h`. -/
theorem gridNorm_Dm_le (i : Fin 3) (w : PeriodicGridSobolev.Grid N → ℂ) :
    PeriodicGridSobolev.gridNorm (PeriodicGridSobolev.Dm i w) ≤
      2 * N * PeriodicGridSobolev.gridNorm w := by
  have e : PeriodicGridSobolev.Dm i w = (N : ℂ) • (w - PeriodicGridSobolev.Sinv i w) := by
    simp [PeriodicGridSobolev.Dm]
  rw [e, PeriodicGridSobolev.gridNorm_smul, Complex.norm_natCast]
  have h1 := PeriodicGridSobolev.gridNorm_sub_le w (PeriodicGridSobolev.Sinv i w)
  rw [gridNorm_Sinv] at h1
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-- **Inverse-mesh bound** `h ‖D_i⁺ w‖_h ≤ 2 ‖w‖_h`. -/
theorem gridNorm_Dp_le (i : Fin 3) (w : PeriodicGridSobolev.Grid N → ℂ) :
    PeriodicGridSobolev.gridNorm (PeriodicGridSobolev.Dp i w) ≤
      2 * N * PeriodicGridSobolev.gridNorm w := by
  have e : PeriodicGridSobolev.Dp i w = (N : ℂ) • (PeriodicGridSobolev.S i w - w) := by
    simp [PeriodicGridSobolev.Dp]
  rw [e, PeriodicGridSobolev.gridNorm_smul, Complex.norm_natCast]
  have h1 := PeriodicGridSobolev.gridNorm_sub_le (PeriodicGridSobolev.S i w) w
  rw [gridNorm_S] at h1
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

theorem sobNorm_mesh_of_comm {T : Module.End ℂ (PeriodicGridSobolev.Grid N → ℂ)} (r : ℕ)
    (hcomm : ∀ α (w : PeriodicGridSobolev.Grid N → ℂ),
      PeriodicGridSobolev.Dα α (T w) = T (PeriodicGridSobolev.Dα α w))
    (hT : ∀ w, PeriodicGridSobolev.gridNorm (T w) ≤ 2 * N * PeriodicGridSobolev.gridNorm w)
    (w : PeriodicGridSobolev.Grid N → ℂ) :
    PeriodicGridSobolev.sobNorm r (T w) ≤ 2 * N * PeriodicGridSobolev.sobNorm r w := by
  have hN : (0 : ℝ) ≤ 2 * N := by positivity
  have hsq : PeriodicGridSobolev.sobSq r (T w) ≤ (2 * N) ^ 2 * PeriodicGridSobolev.sobSq r w := by
    unfold PeriodicGridSobolev.sobSq
    rw [mul_sum]
    refine sum_le_sum fun α _ => ?_
    rw [hcomm, ← PeriodicGridSobolev.gridNorm_sq, ← PeriodicGridSobolev.gridNorm_sq, ← mul_pow]
    exact pow_le_pow_left₀ (PeriodicGridSobolev.gridNorm_nonneg _) (hT _) 2
  unfold PeriodicGridSobolev.sobNorm
  rw [← Real.sqrt_sq hN, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt hsq

/-- `h ‖D_i⁻ w‖_{r,h} ≤ 2 ‖w‖_{r,h}`. -/
theorem sobNorm_Dm_mesh (r : ℕ) (i : Fin 3) (w : PeriodicGridSobolev.Grid N → ℂ) :
    PeriodicGridSobolev.sobNorm r (PeriodicGridSobolev.Dm i w) ≤
      2 * N * PeriodicGridSobolev.sobNorm r w :=
  sobNorm_mesh_of_comm r (fun α w => PeriodicGridSobolev.CommutedRow.Dα_Dm α i w)
    (gridNorm_Dm_le i) w

/-- `h ‖D_i⁺ w‖_{r,h} ≤ 2 ‖w‖_{r,h}`. -/
theorem sobNorm_Dp_mesh (r : ℕ) (i : Fin 3) (w : PeriodicGridSobolev.Grid N → ℂ) :
    PeriodicGridSobolev.sobNorm r (PeriodicGridSobolev.Dp i w) ≤
      2 * N * PeriodicGridSobolev.sobNorm r w :=
  sobNorm_mesh_of_comm r (fun α w => PeriodicGridSobolev.CommutedRow.Dα_Dp α i w)
    (gridNorm_Dp_le i) w

theorem lapC_lapC (w : PeriodicGridSobolev.Grid N → ℂ) :
    lapC (lapC w) = ∑ i, ∑ j, PeriodicGridSobolev.Dm i (PeriodicGridSobolev.Dp i
      (PeriodicGridSobolev.Dm j (PeriodicGridSobolev.Dp j w))) := by
  simp only [lapC, map_neg, map_sum, neg_neg, sum_neg_distrib]

/-- **`h² ‖Λ_h² w‖_{r,h} ≤ 36 ‖w‖_{r+2,h}`** (`eq:supp-law-orders`, first estimate): two of the
four differences are paid by the mesh, two by the Sobolev order. -/
theorem sobNorm_lap2_le (r : ℕ) (w : PeriodicGridSobolev.Grid N → ℂ) :
    ((N : ℝ) ^ 2)⁻¹ * PeriodicGridSobolev.sobNorm r (lapC (lapC w)) ≤
      36 * PeriodicGridSobolev.sobNorm (r + 2) w := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hij : ∀ i j, PeriodicGridSobolev.sobNorm r (PeriodicGridSobolev.Dm i
      (PeriodicGridSobolev.Dp i (PeriodicGridSobolev.Dm j (PeriodicGridSobolev.Dp j w)))) ≤
      4 * (N : ℝ) ^ 2 * PeriodicGridSobolev.sobNorm (r + 2) w := by
    intro i j
    have h1 := sobNorm_Dm_mesh r i (PeriodicGridSobolev.Dp i (PeriodicGridSobolev.Dm j
      (PeriodicGridSobolev.Dp j w)))
    have h2 := sobNorm_Dp_mesh r i (PeriodicGridSobolev.Dm j (PeriodicGridSobolev.Dp j w))
    have h3 := PeriodicGridSobolev.CommutedRow.sobNorm_Dm_le r j (PeriodicGridSobolev.Dp j w)
    have h4 := PeriodicGridSobolev.CommutedRow.sobNorm_Dp_le (r + 1) j w
    have h0 : (0 : ℝ) ≤ 2 * N := by positivity
    calc _ ≤ 2 * N * PeriodicGridSobolev.sobNorm r (PeriodicGridSobolev.Dp i
          (PeriodicGridSobolev.Dm j (PeriodicGridSobolev.Dp j w))) := h1
      _ ≤ 2 * N * (2 * N * PeriodicGridSobolev.sobNorm r
          (PeriodicGridSobolev.Dm j (PeriodicGridSobolev.Dp j w))) :=
          mul_le_mul_of_nonneg_left h2 h0
      _ ≤ 2 * N * (2 * N * PeriodicGridSobolev.sobNorm (r + 2) w) := by
          gcongr
          exact h3.trans h4
      _ = 4 * (N : ℝ) ^ 2 * PeriodicGridSobolev.sobNorm (r + 2) w := by ring
  rw [lapC_lapC]
  have hsum : PeriodicGridSobolev.sobNorm r (∑ i, ∑ j, PeriodicGridSobolev.Dm i
      (PeriodicGridSobolev.Dp i (PeriodicGridSobolev.Dm j (PeriodicGridSobolev.Dp j w)))) ≤
      9 * (4 * (N : ℝ) ^ 2 * PeriodicGridSobolev.sobNorm (r + 2) w) := by
    refine (PeriodicGridSobolev.Moser.sobNorm_sum_le _ _ _).trans ?_
    calc _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, 4 * (N : ℝ) ^ 2 * PeriodicGridSobolev.sobNorm (r + 2) w :=
          sum_le_sum fun i _ => (PeriodicGridSobolev.Moser.sobNorm_sum_le _ _ _).trans
            (sum_le_sum fun j _ => hij i j)
      _ = _ := by simp; ring
  calc ((N : ℝ) ^ 2)⁻¹ * _ ≤ ((N : ℝ) ^ 2)⁻¹ *
        (9 * (4 * (N : ℝ) ^ 2 * PeriodicGridSobolev.sobNorm (r + 2) w)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 36 * PeriodicGridSobolev.sobNorm (r + 2) w := by field_simp; ring

/-- **`eq:supp-law-domination`**: `h² ‖Λ_h w‖_h² ≤ 12 Σ_i ‖D_i⁺ w‖_h²`. -/
theorem law_domination (w : PeriodicGridSobolev.Grid N → ℂ) :
    ((N : ℝ) ^ 2)⁻¹ * PeriodicGridSobolev.gridNorm (lapC w) ^ 2 ≤
      12 * ∑ i, PeriodicGridSobolev.gridNorm (PeriodicGridSobolev.Dp i w) ^ 2 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have h1 : PeriodicGridSobolev.gridNorm (lapC w) ≤
      ∑ i, 2 * N * PeriodicGridSobolev.gridNorm (PeriodicGridSobolev.Dp i w) := by
    unfold lapC
    rw [PeriodicGridSobolev.gridNorm_neg]
    exact (PeriodicGridSobolev.gridNorm_sum_le _ _).trans
      (sum_le_sum fun i _ => gridNorm_Dm_le i _)
  have h0 := PeriodicGridSobolev.gridNorm_nonneg (lapC w)
  set a : Fin 3 → ℝ := fun i => PeriodicGridSobolev.gridNorm (PeriodicGridSobolev.Dp i w)
  have ha : ∀ i, 0 ≤ a i := fun i => PeriodicGridSobolev.gridNorm_nonneg _
  have h2 : PeriodicGridSobolev.gridNorm (lapC w) ^ 2 ≤ (2 * N) ^ 2 * (∑ i, a i) ^ 2 := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ h0 ?_ 2
    calc _ ≤ ∑ i, 2 * N * a i := h1
      _ = 2 * N * ∑ i, a i := by rw [mul_sum]
  have h3 : (∑ i, a i) ^ 2 ≤ 3 * ∑ i, a i ^ 2 := by
    simp only [Fin.sum_univ_three]
    nlinarith [sq_nonneg (a 0 - a 1), sq_nonneg (a 1 - a 2), sq_nonneg (a 0 - a 2)]
  calc ((N : ℝ) ^ 2)⁻¹ * PeriodicGridSobolev.gridNorm (lapC w) ^ 2 ≤
        ((N : ℝ) ^ 2)⁻¹ * ((2 * N) ^ 2 * (3 * ∑ i, a i ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (h2.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 12 * ∑ i, a i ^ 2 := by field_simp; ring

/-! ### Coefficient marks and the law family -/

/-- **A coefficient mark of the closed ball `ℬ̄`**: `B = Bᵀ ∈ ℝ^{10 × 10}` with operator norm at
most `b`, i.e. `|ξᵀ B η| ≤ b |ξ| |η|` for all `ξ, η` (`eq:supp-law-ball`). -/
def IsMark (b : ℝ) (B : Upper → Upper → ℝ) : Prop :=
  (∀ k l, B k l = B l k) ∧ ∀ ξ η : Upper → ℝ,
    |∑ k, ∑ l, ξ k * B k l * η l| ≤ b * Real.sqrt (∑ k, ξ k ^ 2) * Real.sqrt (∑ k, η k ^ 2)

theorem IsMark.entry_le {b : ℝ} {B : Upper → Upper → ℝ} (hB : IsMark b B) (k l : Upper) :
    |B k l| ≤ b := by
  have h := hB.2 (Pi.single k 1) (Pi.single l 1)
  have e1 : ∑ k', ∑ l', (Pi.single k 1 : Upper → ℝ) k' * B k' l' * (Pi.single l 1 : Upper → ℝ) l' =
      B k l := by
    simp [Pi.single_apply]
  have e2 : ∀ m : Upper, ∑ k', (Pi.single m 1 : Upper → ℝ) k' ^ 2 = 1 := by
    intro m; simp [Pi.single_apply]
  rw [e1, e2, e2, Real.sqrt_one, mul_one, mul_one] at h
  exact h

theorem IsMark.quad_le {b : ℝ} {B : Upper → Upper → ℝ} (hB : IsMark b B) (ξ : Upper → ℝ) :
    |∑ k, ∑ l, ξ k * B k l * ξ l| ≤ b * ∑ k, ξ k ^ 2 := by
  have h := hB.2 ξ ξ
  rwa [mul_assoc, Real.mul_self_sqrt (sum_nonneg fun _ _ => sq_nonneg _)] at h

theorem IsMark.nonneg {b : ℝ} {B : Upper → Upper → ℝ} (hB : IsMark b B) : 0 ≤ b := by
  have := hB.entry_le (upperOf 0 0) (upperOf 0 0)
  exact (abs_nonneg _).trans this

/-- Marks of a smaller ball are marks of a larger one: the results below, stated for
`‖B‖_op ≤ 1/48`, cover every closed ball `‖B‖_op ≤ b₀` with `b₀ ≤ 1/48`. -/
theorem IsMark.mono {b b' : ℝ} {B : Upper → Upper → ℝ} (hB : IsMark b B) (hbb : b ≤ b') :
    IsMark b' B := by
  refine ⟨hB.1, fun ξ η => (hB.2 ξ η).trans ?_⟩
  have h1 := Real.sqrt_nonneg (∑ k, ξ k ^ 2)
  have h2 := Real.sqrt_nonneg (∑ k, η k ^ 2)
  have := mul_nonneg h1 h2
  nlinarith

/-- The stencil `h² B Λ_h² q` as a record array (`B` acts on the ten upper components). -/
def bTerm (B : Upper → Upper → ℝ) (q : Grid N → MetricRec) : Grid N → MetricRec :=
  fun x μ ν => ((N : ℝ) ^ 2)⁻¹ * ∑ l : Upper, B (upperOf μ ν) l * lapR (lapR (comp q l.1.1 l.1.2)) x

/-- The added force `-a⁻¹ h² B Λ_h² q` of the law family. -/
def lawForce (B : Upper → Upper → ℝ) (q : Grid N → MetricRec) : Grid N → MetricRec :=
  fun x μ ν => -((aArr q x)⁻¹ * bTerm B q x μ ν)

/-- **The law-family acceleration** `eq:supp-law-family`:
`v_t = a⁻¹[Σ D_i⁻(c^{ij} D_j⁺ q) - 𝖪_b v + 𝖦_h(q, v) - h² B Λ_h² q]`. -/
def lawAccel (B : Upper → Upper → ℝ) (q v : Grid N → MetricRec) : Grid N → MetricRec :=
  harmonicWriterAcceleration q v + lawForce B q

/-- The added quadratic energy `(h²/2) Σ_{|α| ≤ s} ⟨Λ_h q_α, B Λ_h q_α⟩_h`. -/
def lawExtra (B : Upper → Upper → ℝ) (s : ℕ) (q : Grid N → MetricRec) : ℝ :=
  ((N : ℝ) ^ 2)⁻¹ / 2 * ∑ α ∈ PeriodicGridSobolev.multiIndices s, ∑ k : Upper, ∑ l : Upper,
    B k l * (((N : ℝ) ^ 3)⁻¹ * ∑ x, lapR (DαR α (comp q k.1.1 k.1.2)) x *
      lapR (DαR α (comp q l.1.1 l.1.2)) x)

/-- **The law energy** `𝓔^B_{s,h}` of `eq:supp-law-energy`. -/
def lawEnergy (B : Upper → Upper → ℝ) (s : ℕ) (q v : Grid N → MetricRec) : ℝ :=
  shiftedEnergy s q v + lawExtra B s q

/-! ### Linearity, self-adjointness and the cancellation identity -/

theorem lapC_add (a b : PeriodicGridSobolev.Grid N → ℂ) : lapC (a + b) = lapC a + lapC b := by
  simp only [lapC, map_add, sum_add_distrib, neg_add]

theorem lapC_smul (c : ℂ) (a : PeriodicGridSobolev.Grid N → ℂ) : lapC (c • a) = c • lapC a := by
  simp only [lapC, map_smul, ← smul_sum, smul_neg]

/-- `Λ_h` as a linear map of real arrays. -/
def lapRLin : (Grid N → ℝ) →ₗ[ℝ] (Grid N → ℝ) where
  toFun := lapR
  map_add' u w := by
    apply cx_injective
    rw [cx_add, cx_lapR, cx_lapR, cx_lapR, cx_add, lapC_add]
  map_smul' c u := by
    apply cx_injective
    rw [RingHom.id_apply, cx_smul, cx_lapR, cx_lapR, cx_smul, lapC_smul]

theorem hasDerivAt_lapR {U : ℝ → Grid N → ℝ} {U' : Grid N → ℝ} {t : ℝ}
    (hU : ∀ y, HasDerivAt (fun τ => U τ y) (U' y) t) (x : Grid N) :
    HasDerivAt (fun τ => lapR (U τ) x) (lapR U' x) t := by
  have h : HasDerivAt U U' t := hasDerivAt_pi.2 hU
  have := (LinearMap.toContinuousLinearMap (lapRLin (N := N))).hasFDerivAt.comp_hasDerivAt t h
  exact hasDerivAt_pi.1 this x

theorem lapR_apply (u : Grid N → ℝ) (x : Grid N) :
    lapR u x = -∑ i, OpenWriterEnergy.Dm i (OpenWriterEnergy.Dp i u) x := by
  simp [lapR, Finset.sum_apply]

/-- **`Λ_h` is self-adjoint**: `⟨u, Λ_h w⟩_h = ⟨Λ_h u, w⟩_h`. -/
theorem sum_mul_lapR (u w : Grid N → ℝ) : ∑ x, u x * lapR w x = ∑ x, lapR u x * w x := by
  have key : ∀ u w : Grid N → ℝ, ∑ x, u x * lapR w x =
      ∑ i, ∑ x, OpenWriterEnergy.Dp i u x * OpenWriterEnergy.Dp i w x := by
    intro u w
    simp only [lapR_apply, mul_neg, mul_sum, sum_neg_distrib]
    rw [sum_comm, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_mul_Dm, neg_neg]
  rw [key, show ∑ x, lapR u x * w x = ∑ x, w x * lapR u x from
    sum_congr rfl fun x _ => mul_comm _ _, key]
  exact sum_congr rfl fun i _ => sum_congr rfl fun x _ => mul_comm _ _

/-! ### The commutator of the mass coefficient -/

/-- The shifted commutator `𝒞_α(f, w) = D^α(f w) - (S^α f) D^α w` on real arrays. -/
def commR (α : Fin 3 → ℕ) (f w : Grid N → ℝ) : Grid N → ℝ :=
  fun x => DαR α (fun y => f y * w y) x - SαR α f x * DαR α w x

theorem cx_commR (α : Fin 3 → ℕ) (f w : Grid N → ℝ) :
    cx (commR α f w) = PeriodicGridSobolev.commutator α (cx f) (cx w) := by
  have e : commR α f w = DαR α (fun y => f y * w y) - fun x => SαR α f x * DαR α w x := rfl
  rw [e, cx_sub, cx_DαR, cx_fun_mul, cx_fun_mul, cx_SαR, cx_DαR]
  rfl

theorem DαR_neg (α : Fin 3 → ℕ) (u : Grid N → ℝ) : DαR α (-u) = -DαR α u := by
  funext x
  simp only [← DαRL_apply, map_neg, Pi.neg_apply]

theorem DαR_bTerm (α : Fin 3 → ℕ) (B : Upper → Upper → ℝ) (q : Grid N → MetricRec) (k : Upper) :
    DαR α (comp (bTerm B q) k.1.1 k.1.2) = fun x => ((N : ℝ) ^ 2)⁻¹ *
      ∑ l : Upper, B k l * lapR (lapR (DαR α (comp q l.1.1 l.1.2))) x := by
  funext x
  have e : comp (bTerm B q) k.1.1 k.1.2 = ∑ l : Upper, (((N : ℝ) ^ 2)⁻¹ * B k l) •
      lapR (lapR (comp q l.1.1 l.1.2)) := by
    funext y
    simp only [comp, bTerm, upperOf_upper, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sum]
    exact sum_congr rfl fun l _ => by ring
  rw [e, ← DαRL_apply, map_sum, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [map_smul, smul_eq_mul, DαRL_apply, DαR_lapR, DαR_lapR]
  ring

/-- The commutator term of the law energy identity. -/
def commTerm (B : Upper → Upper → ℝ) (s : ℕ) (q v : Grid N → MetricRec) : ℝ :=
  ∑ α ∈ PeriodicGridSobolev.multiIndices s, ∑ k : Upper, ((N : ℝ) ^ 3)⁻¹ * ∑ x,
    DαR α (comp v k.1.1 k.1.2) x * (SαR α (aArr q) x *
      commR α (fun y => (aArr q y)⁻¹) (comp (bTerm B q) k.1.1 k.1.2) x)


/-- The rate of the added energy, `Σ_α ⟨v_α, h² B Λ_h² q_α⟩_h`. -/
def lawExtraRate (B : Upper → Upper → ℝ) (s : ℕ) (q v : Grid N → MetricRec) : ℝ :=
  ∑ α ∈ PeriodicGridSobolev.multiIndices s, ∑ k : Upper, ((N : ℝ) ^ 3)⁻¹ * ∑ x,
    DαR α (comp v k.1.1 k.1.2) x * DαR α (comp (bTerm B q) k.1.1 k.1.2) x

theorem hasDerivAt_lawExtra (B : Upper → Upper → ℝ) (hB : ∀ k l, B k l = B l k) (s : ℕ)
    (q v : ℝ → Grid N → MetricRec) (t : ℝ) (hq : ∀ x, HasDerivAt (fun τ => q τ x) (v t x) t) :
    HasDerivAt (fun τ => lawExtra B s (q τ)) (lawExtraRate B s (q t) (v t)) t := by
  have hcomp : ∀ (κ : Upper) α x, HasDerivAt (fun τ => lapR (DαR α (comp (q τ) κ.1.1 κ.1.2)) x)
      (lapR (DαR α (comp (v t) κ.1.1 κ.1.2)) x) t := by
    intro κ α x
    refine hasDerivAt_lapR (U := fun τ => DαR α (comp (q τ) κ.1.1 κ.1.2)) (fun y => ?_) x
    exact hasDerivAt_DαR (fun z => hasDerivAt_pi.1 (hasDerivAt_pi.1 (hq z) κ.1.1) κ.1.2) α y
  set L : (Fin 3 → ℕ) → Upper → (Grid N → MetricRec) → Grid N → ℝ :=
    fun α k u => lapR (DαR α (comp u k.1.1 k.1.2))
  set c : ℝ := ((N : ℝ) ^ 3)⁻¹
  have hraw : HasDerivAt (fun τ => lawExtra B s (q τ))
      (((N : ℝ) ^ 2)⁻¹ / 2 * ∑ α ∈ PeriodicGridSobolev.multiIndices s, ∑ k : Upper, ∑ l : Upper,
        B k l * (c * ∑ x, (L α k (v t) x * L α l (q t) x +
          L α k (q t) x * L α l (v t) x))) t := by
    unfold lawExtra
    refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun α _ => HasDerivAt.fun_sum fun k _ =>
      HasDerivAt.fun_sum fun l _ => HasDerivAt.const_mul _ (HasDerivAt.const_mul _
        (HasDerivAt.fun_sum fun x _ => ?_)))
    exact (hcomp k α x).mul (hcomp l α x)
  refine hraw.congr_deriv ?_
  unfold lawExtraRate
  rw [mul_sum]
  refine sum_congr rfl fun α _ => ?_
  have hself : ∀ k l : Upper, ∑ x, L α k (v t) x * L α l (q t) x =
      ∑ x, DαR α (comp (v t) k.1.1 k.1.2) x * lapR (lapR (DαR α (comp (q t) l.1.1 l.1.2))) x := by
    intro k l
    simp only [L]
    rw [← sum_mul_lapR]
  have hswap : ∑ k : Upper, ∑ l : Upper, B k l * (c * ∑ x, L α k (q t) x * L α l (v t) x) =
      ∑ k : Upper, ∑ l : Upper, B k l * (c * ∑ x, L α k (v t) x * L α l (q t) x) := by
    rw [sum_comm]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    rw [hB l k]
    congr 2
    exact sum_congr rfl fun x _ => mul_comm _ _
  have hα : ∑ k : Upper, ∑ l : Upper, B k l * (c * ∑ x, (L α k (v t) x * L α l (q t) x +
      L α k (q t) x * L α l (v t) x)) =
      2 * ∑ k : Upper, ∑ l : Upper, B k l * (c * ∑ x, DαR α (comp (v t) k.1.1 k.1.2) x *
        lapR (lapR (DαR α (comp (q t) l.1.1 l.1.2))) x) := by
    simp only [sum_add_distrib, mul_add]
    rw [hswap]
    simp only [hself]
    ring
  rw [hα]
  have hR : ∑ k : Upper, c * ∑ x, DαR α (comp (v t) k.1.1 k.1.2) x *
      DαR α (comp (bTerm B (q t)) k.1.1 k.1.2) x =
      ((N : ℝ) ^ 2)⁻¹ * ∑ k : Upper, ∑ l : Upper, B k l * (c * ∑ x,
        DαR α (comp (v t) k.1.1 k.1.2) x * lapR (lapR (DαR α (comp (q t) l.1.1 l.1.2))) x) := by
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [DαR_bTerm]
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun l _ => sum_congr rfl fun x _ => ?_
    ring
  rw [hR]
  ring

/-- **The cancellation**: the forcing contribution of the law term is `-Σ_α ⟨v_α, h² B Λ_h² q_α⟩`
(minus the time derivative of the added energy) up to the commutator of `a⁻¹`. -/
theorem forcingTerm_lawForce (B : Upper → Upper → ℝ) (s : ℕ) (q v : Grid N → MetricRec)
    (ha : ∀ x, aArr q x ≠ 0) :
    forcingTerm s q v (lawForce B q) = -lawExtraRate B s q v - commTerm B s q v := by
  unfold forcingTerm lawExtraRate commTerm
  rw [← sum_neg_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun α _ => ?_
  rw [← sum_neg_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  have hpt : ∀ x, SαR α (aArr q) x * DαR α (comp (lawForce B q) k.1.1 k.1.2) x =
      -DαR α (comp (bTerm B q) k.1.1 k.1.2) x -
      SαR α (aArr q) x * commR α (fun y => (aArr q y)⁻¹) (comp (bTerm B q) k.1.1 k.1.2) x := by
    intro x
    have e1 : comp (lawForce B q) k.1.1 k.1.2 =
        -(fun y => (aArr q y)⁻¹ * comp (bTerm B q) k.1.1 k.1.2 y) := by
      funext y; simp [comp, lawForce]
    rw [e1, DαR_neg]
    have e2 : DαR α (fun y => (aArr q y)⁻¹ * comp (bTerm B q) k.1.1 k.1.2 y) x =
        SαR α (fun y => (aArr q y)⁻¹) x * DαR α (comp (bTerm B q) k.1.1 k.1.2) x +
          commR α (fun y => (aArr q y)⁻¹) (comp (bTerm B q) k.1.1 k.1.2) x := by
      simp only [commR]; ring
    have e3 : SαR α (aArr q) x * SαR α (fun y => (aArr q y)⁻¹) x = 1 := by
      simp only [SαR]; exact mul_inv_cancel₀ (ha _)
    rw [Pi.neg_apply, e2, mul_neg, mul_add, ← mul_assoc, e3, one_mul]
    ring
  rw [← mul_neg, ← mul_sub, ← sum_neg_distrib, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [hpt]
  ring
/-- **The law energy identity**: along a law-family history,
`d𝓔^B/dt = (unforced rate) - Σ_α ⟨v_α, a_α 𝒞_α(a⁻¹, h² B Λ_h² q)⟩_h`; the fourth-order term
cancels at principal order. -/
theorem hasDerivAt_lawEnergy (B : Upper → Upper → ℝ) (hB : ∀ k l, B k l = B l k) (s : ℕ)
    (q v : ℝ → Grid N → MetricRec) (t : ℝ) (hsym : IsSymRec (q t))
    (hq : ∀ x, HasDerivAt (fun τ => q τ x) (v t x) t)
    (hv : ∀ x (κ : Upper), HasDerivAt (fun τ => v τ x κ.1.1 κ.1.2)
      (lawAccel B (q t) (v t) x κ.1.1 κ.1.2) t)
    (hdA : ∀ x, DifferentiableAt ℝ harmA (minkowski + q t x))
    (hdC : ∀ x i j, DifferentiableAt ℝ (harmC i j) (minkowski + q t x))
    (ha : ∀ x, aArr (q t) x ≠ 0) :
    HasDerivAt (fun τ => lawEnergy B s (q τ) (v τ))
      (energyRate s (q t) (v t) - commTerm B s (q t) (v t)) t := by
  have h1 := hasDerivAt_shiftedEnergy_forced s q v (fun τ => lawForce B (q τ)) t hsym hq
    (fun x κ => by simpa [lawAccel] using hv x κ) hdA hdC
  have h2 := hasDerivAt_lawExtra B hB s q v t hq
  refine (h1.add h2).congr_deriv ?_
  rw [forcedRate_eq, forcingTerm_lawForce B s (q t) (v t) ha]
  ring

/-! ### Energy equivalence with the positivity margin -/

/-- The per-level quantity `‖V_α‖² + Σ_i ‖D_i⁺ Q_α‖² + ‖Q_α‖²`. -/
def levelG (α : Fin 3 → ℕ) (Q V : Grid N → MetricRec) (κ : Upper) : ℝ :=
  PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dα α (cx (comp V κ.1.1 κ.1.2))) +
    ∑ i, PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dp i
      (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2)))) +
    PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2)))

theorem levelG_eq (α : Fin 3 → ℕ) (Q V : Grid N → MetricRec) (κ : Upper) :
    ((N : ℝ) ^ 3)⁻¹ * ∑ x, (DαR α (comp V κ.1.1 κ.1.2) x ^ 2 +
      ∑ i, OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x ^ 2 +
      DαR α (comp Q κ.1.1 κ.1.2) x ^ 2) = levelG α Q V κ := by
  have hv' : PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dα α (cx (comp V κ.1.1 κ.1.2))) =
      ((N : ℝ) ^ 3)⁻¹ * ∑ x, DαR α (comp V κ.1.1 κ.1.2) x ^ 2 := by
    rw [← cx_DαR, gridNormSq_cx]
  have hq' : PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2))) =
      ((N : ℝ) ^ 3)⁻¹ * ∑ x, DαR α (comp Q κ.1.1 κ.1.2) x ^ 2 := by
    rw [← cx_DαR, gridNormSq_cx]
  have hd' : ∀ i, PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dp i
      (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2)))) =
      ((N : ℝ) ^ 3)⁻¹ * ∑ x, OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x ^ 2 := by
    intro i; rw [← cx_DαR, ← cx_Dp, gridNormSq_cx]
  simp only [levelG, hv', hq', hd']
  rw [sum_add_distrib, sum_add_distrib, sum_comm (s := univ) (t := univ) (f := fun x i =>
    OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x ^ 2), mul_add, mul_add,
    Finset.mul_sum (s := univ) (f := fun i => ∑ x,
      OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x ^ 2)]

theorem levelG_nonneg (α : Fin 3 → ℕ) (Q V : Grid N → MetricRec) (κ : Upper) :
    0 ≤ levelG α Q V κ := by
  unfold levelG
  have := PeriodicGridSobolev.gridNormSq_nonneg
    (PeriodicGridSobolev.Dα α (cx (comp V κ.1.1 κ.1.2)))
  have := PeriodicGridSobolev.gridNormSq_nonneg
    (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2)))
  have : 0 ≤ ∑ i, PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dp i
      (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2)))) :=
    sum_nonneg fun _ _ => PeriodicGridSobolev.gridNormSq_nonneg _
  linarith

/-- The per-level lower bound `𝓔_α ≥ ¼ Σ_κ G_{α,κ}` on the chart. -/
theorem energy_level_lower (α : Fin 3 → ℕ) (a : Grid N → ℝ) (c : Fin 3 → Fin 3 → Grid N → ℝ)
    (ha : ∀ x, 1 / 2 ≤ a x ∧ a x ≤ 3 / 2)
    (hc : ∀ x i j, |c i j x - (if i = j then 1 else 0)| ≤ 1 / 18) (Q V : Grid N → MetricRec) :
    (1 / 4) * ∑ κ : Upper, levelG α Q V κ ≤
      energy (SαR α a) (fun i j => SαR α (c i j)) (fun κ : Upper => DαR α (comp Q κ.1.1 κ.1.2))
        (fun κ : Upper => DαR α (comp V κ.1.1 κ.1.2)) := by
  unfold energy
  have hN : (0 : ℝ) ≤ ((N : ℝ) ^ 3)⁻¹ := by positivity
  have hpt : ∀ (κ : Upper) x,
      (1 / 2) * (DαR α (comp V κ.1.1 κ.1.2) x ^ 2 +
        ∑ i, OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x ^ 2 +
        DαR α (comp Q κ.1.1 κ.1.2) x ^ 2) ≤
      DαR α (comp V κ.1.1 κ.1.2) x * (SαR α a x * DαR α (comp V κ.1.1 κ.1.2) x) +
        ∑ i, ∑ j, OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x *
          (SαR α (c i j) x * OpenWriterEnergy.Dp j (DαR α (comp Q κ.1.1 κ.1.2)) x) +
        DαR α (comp Q κ.1.1 κ.1.2) x ^ 2 := by
    intro κ x
    have e : SαR α a x = a (x + svec α) := rfl
    have ha1 := (ha (x + svec α)).1
    have hv2 := sq_nonneg (DαR α (comp V κ.1.1 κ.1.2) x)
    have hlo := quad_lower (fun i => OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x)
      (fun i j => SαR α (c i j) x) (fun i j => hc (x + svec α) i j)
    rw [e]
    nlinarith
  calc (1 / 4) * ∑ κ : Upper, levelG α Q V κ = ((N : ℝ) ^ 3)⁻¹ * (1 / 2) * ∑ κ : Upper, ∑ x,
        (1 / 2) * (DαR α (comp V κ.1.1 κ.1.2) x ^ 2 +
          ∑ i, OpenWriterEnergy.Dp i (DαR α (comp Q κ.1.1 κ.1.2)) x ^ 2 +
          DαR α (comp Q κ.1.1 κ.1.2) x ^ 2) := by
        rw [← sum_congr rfl fun κ _ => levelG_eq α Q V κ, mul_sum, mul_sum]
        refine sum_congr rfl fun κ _ => ?_
        rw [← mul_sum]; ring
    _ ≤ _ := by
        gcongr with κ _ x _
        exact hpt κ x

/-- `‖(Q, V)‖²_{X^r_h} ≤ Σ_{|α| ≤ r} Σ_κ G_{α,κ}` (counting lemma). -/
theorem Xsq_le_sum_levelG (r : ℕ) (Q V : Grid N → MetricRec) :
    Xsq r Q V ≤ ∑ α ∈ PeriodicGridSobolev.multiIndices r, ∑ κ : Upper, levelG α Q V κ := by
  rw [sum_comm]
  unfold Xsq
  refine sum_le_sum fun κ _ => ?_
  have hcnt := PeriodicGridSobolev.CommutedRow.sobSq_succ_le_shifted r (cx (comp Q κ.1.1 κ.1.2))
  have e1 : ∑ α ∈ PeriodicGridSobolev.multiIndices r, levelG α Q V κ =
      PeriodicGridSobolev.sobSq r (cx (comp V κ.1.1 κ.1.2)) +
      ∑ α ∈ PeriodicGridSobolev.multiIndices r,
        (PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2))) +
        ∑ i, PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dp i
          (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2))))) := by
    simp only [levelG, sum_add_distrib, PeriodicGridSobolev.sobSq]
    ring
  rw [e1]
  linarith

/-- The gradient part of the levels: `Σ_α Σ_κ Σ_i ‖D_i⁺ Q_α‖² ≤ 3 ‖(Q, V)‖²_{X^r_h}`. -/
theorem sum_grad_le (r : ℕ) (Q V : Grid N → MetricRec) :
    ∑ α ∈ PeriodicGridSobolev.multiIndices r, ∑ κ : Upper, ∑ i,
      PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dp i
        (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2)))) ≤ 3 * Xsq r Q V := by
  rw [sum_comm]
  unfold Xsq
  rw [mul_sum]
  refine sum_le_sum fun κ _ => ?_
  have := sum_Dp_Dα_sq_le r (cx (comp Q κ.1.1 κ.1.2))
  have := PeriodicGridSobolev.sobSq_nonneg r (cx (comp V κ.1.1 κ.1.2))
  linarith

/-- The added energy at one level is dominated by the gradient part:
`|(h²/2) ⟨Λ_h Q_α, B Λ_h Q_α⟩| ≤ 6 b Σ_κ Σ_i ‖D_i⁺ Q_{α,κ}‖²` (`lem:supp-law-multiplier` and the
operator-norm bound). -/
theorem abs_lawExtra_level_le {b : ℝ} {B : Upper → Upper → ℝ} (hB : IsMark b B) (α : Fin 3 → ℕ)
    (q : Grid N → MetricRec) :
    |((N : ℝ) ^ 2)⁻¹ / 2 * ∑ k : Upper, ∑ l : Upper, B k l * (((N : ℝ) ^ 3)⁻¹ *
      ∑ x, lapR (DαR α (comp q k.1.1 k.1.2)) x * lapR (DαR α (comp q l.1.1 l.1.2)) x)| ≤
      6 * b * ∑ κ : Upper, ∑ i, PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dp i
        (PeriodicGridSobolev.Dα α (cx (comp q κ.1.1 κ.1.2)))) := by
  have hb := hB.nonneg
  set L : Upper → Grid N → ℝ := fun k => lapR (DαR α (comp q k.1.1 k.1.2))
  have hN3 : (0 : ℝ) ≤ ((N : ℝ) ^ 3)⁻¹ := by positivity
  have hN2 : (0 : ℝ) ≤ ((N : ℝ) ^ 2)⁻¹ := by positivity
  have e1 : ∑ k : Upper, ∑ l : Upper, B k l * (((N : ℝ) ^ 3)⁻¹ * ∑ x, L k x * L l x) =
      ((N : ℝ) ^ 3)⁻¹ * ∑ x, ∑ k : Upper, ∑ l : Upper, L k x * B k l * L l x := by
    calc ∑ k : Upper, ∑ l : Upper, B k l * (((N : ℝ) ^ 3)⁻¹ * ∑ x, L k x * L l x)
        = ∑ k : Upper, ∑ l : Upper, ∑ x, ((N : ℝ) ^ 3)⁻¹ * (L k x * B k l * L l x) := by
          simp only [mul_sum]
          exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => sum_congr rfl fun x _ => by ring
      _ = ∑ k : Upper, ∑ x, ∑ l : Upper, ((N : ℝ) ^ 3)⁻¹ * (L k x * B k l * L l x) :=
          sum_congr rfl fun k _ => sum_comm
      _ = ∑ x, ∑ k : Upper, ∑ l : Upper, ((N : ℝ) ^ 3)⁻¹ * (L k x * B k l * L l x) := sum_comm
      _ = _ := by simp only [mul_sum]
  have h1 : |∑ k : Upper, ∑ l : Upper, B k l * (((N : ℝ) ^ 3)⁻¹ * ∑ x, L k x * L l x)| ≤
      b * ∑ k : Upper, PeriodicGridSobolev.gridNormSq (cx (L k)) := by
    rw [e1, abs_mul, abs_of_nonneg hN3]
    refine (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hN3).trans ?_
    have h2 : ∀ x, |∑ k : Upper, ∑ l : Upper, L k x * B k l * L l x| ≤
        b * ∑ k : Upper, L k x ^ 2 := fun x => hB.quad_le (fun k => L k x)
    calc ((N : ℝ) ^ 3)⁻¹ * ∑ x, |∑ k : Upper, ∑ l : Upper, L k x * B k l * L l x| ≤
          ((N : ℝ) ^ 3)⁻¹ * ∑ x, b * ∑ k : Upper, L k x ^ 2 :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => h2 x) hN3
      _ = b * ∑ k : Upper, PeriodicGridSobolev.gridNormSq (cx (L k)) := by
          rw [show ∑ k : Upper, PeriodicGridSobolev.gridNormSq (cx (L k)) =
            ∑ k : Upper, ((N : ℝ) ^ 3)⁻¹ * ∑ x, L k x ^ 2 from
            sum_congr rfl fun k _ => gridNormSq_cx _]
          simp only [mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun k _ => sum_congr rfl fun x _ => by ring
  have h3 : ∀ k : Upper, ((N : ℝ) ^ 2)⁻¹ * PeriodicGridSobolev.gridNormSq (cx (L k)) ≤
      12 * ∑ i, PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dp i
        (PeriodicGridSobolev.Dα α (cx (comp q k.1.1 k.1.2)))) := by
    intro k
    have := law_domination (PeriodicGridSobolev.Dα α (cx (comp q k.1.1 k.1.2)))
    simp only [PeriodicGridSobolev.gridNorm_sq] at this
    simp only [L]
    rwa [cx_lapR, cx_DαR]
  rw [abs_mul, abs_of_nonneg (by positivity)]
  calc ((N : ℝ) ^ 2)⁻¹ / 2 * |∑ k : Upper, ∑ l : Upper, B k l *
        (((N : ℝ) ^ 3)⁻¹ * ∑ x, L k x * L l x)| ≤
        ((N : ℝ) ^ 2)⁻¹ / 2 * (b * ∑ k : Upper, PeriodicGridSobolev.gridNormSq (cx (L k))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = b / 2 * ∑ k : Upper, ((N : ℝ) ^ 2)⁻¹ * PeriodicGridSobolev.gridNormSq (cx (L k)) := by
        simp only [mul_sum]; exact sum_congr rfl fun k _ => by ring
    _ ≤ b / 2 * ∑ k : Upper, 12 * ∑ i, PeriodicGridSobolev.gridNormSq (PeriodicGridSobolev.Dp i
          (PeriodicGridSobolev.Dα α (cx (comp q k.1.1 k.1.2)))) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => h3 k) (by positivity)
    _ = _ := by rw [← mul_sum]; ring

theorem lawExtra_eq_sum (B : Upper → Upper → ℝ) (s : ℕ) (q : Grid N → MetricRec) :
    lawExtra B s q = ∑ α ∈ PeriodicGridSobolev.multiIndices s, ((N : ℝ) ^ 2)⁻¹ / 2 *
      ∑ k : Upper, ∑ l : Upper, B k l * (((N : ℝ) ^ 3)⁻¹ *
        ∑ x, lapR (DαR α (comp q k.1.1 k.1.2)) x * lapR (DαR α (comp q l.1.1 l.1.2)) x) := by
  unfold lawExtra; rw [mul_sum]

/-- **Energy equivalence for the law family** (`eq:supp-law-energy-bound`, first half): on the
pointwise chart and for every mark with `‖B‖_op ≤ b ≤ 1/48` (the margin `b₀ < c_*/24` with the
certified coercivity `c_* = 1/2` of the chart), `⅛ ‖X‖² ≤ 𝓔^B ≤ 9 ‖X‖²`. -/
theorem lawEnergy_bounds (s : ℕ) {b : ℝ} {B : Upper → Upper → ℝ} (hB : IsMark b B)
    (hb : b ≤ 1 / 48) (q v : Grid N → MetricRec) (ha : ∀ x, 1 / 2 ≤ aArr q x ∧ aArr q x ≤ 3 / 2)
    (hc : ∀ x i j, |cArr q i j x - (if i = j then 1 else 0)| ≤ 1 / 18) :
    Xsq s q v / 8 ≤ lawEnergy B s q v ∧ lawEnergy B s q v ≤ 9 * Xsq s q v := by
  have hb0 := hB.nonneg
  set Dg : (Fin 3 → ℕ) → ℝ := fun α => ∑ κ : Upper, ∑ i, PeriodicGridSobolev.gridNormSq
    (PeriodicGridSobolev.Dp i (PeriodicGridSobolev.Dα α (cx (comp q κ.1.1 κ.1.2))))
  have hDgG : ∀ α, Dg α ≤ ∑ κ : Upper, levelG α q v κ := by
    intro α
    refine sum_le_sum fun κ _ => ?_
    unfold levelG
    have := PeriodicGridSobolev.gridNormSq_nonneg
      (PeriodicGridSobolev.Dα α (cx (comp v κ.1.1 κ.1.2)))
    have := PeriodicGridSobolev.gridNormSq_nonneg
      (PeriodicGridSobolev.Dα α (cx (comp q κ.1.1 κ.1.2)))
    linarith
  have hext := fun α => abs_lawExtra_level_le hB α q
  unfold lawEnergy
  rw [shiftedEnergy_eq_genEnergy, lawExtra_eq_sum]
  unfold genEnergy
  rw [← sum_add_distrib]
  constructor
  · calc Xsq s q v / 8 ≤ ∑ α ∈ PeriodicGridSobolev.multiIndices s,
          (1 / 8) * ∑ κ : Upper, levelG α q v κ := by
          rw [← mul_sum, div_eq_mul_inv, mul_comm]
          have := Xsq_le_sum_levelG s q v
          linarith
      _ ≤ _ := by
          refine sum_le_sum fun α _ => ?_
          have h1 := energy_level_lower α (aArr q) (cArr q) ha hc q v
          have h2 := neg_abs_le (((N : ℝ) ^ 2)⁻¹ / 2 * ∑ k : Upper, ∑ l : Upper, B k l *
            (((N : ℝ) ^ 3)⁻¹ * ∑ x, lapR (DαR α (comp q k.1.1 k.1.2)) x *
              lapR (DαR α (comp q l.1.1 l.1.2)) x))
          have h3 := hext α
          have h4 := hDgG α
          have h5 : 6 * b * Dg α ≤ 1 / 8 * ∑ κ : Upper, levelG α q v κ := by
            have : 0 ≤ Dg α := sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
              PeriodicGridSobolev.gridNormSq_nonneg _
            nlinarith
          simp only [Dg] at h4 h5
          linarith
  · have hup := (genEnergy_bounds s (aArr q) (cArr q) ha hc q v).2
    have hgr := sum_grad_le s q v
    calc _ ≤ ∑ α ∈ PeriodicGridSobolev.multiIndices s, (energy (SαR α (aArr q))
          (fun i j => SαR α (cArr q i j)) (fun κ : Upper => DαR α (comp q κ.1.1 κ.1.2))
          (fun κ : Upper => DαR α (comp v κ.1.1 κ.1.2)) + 6 * b * Dg α) :=
          sum_le_sum fun α _ => add_le_add le_rfl ((le_abs_self _).trans (hext α))
      _ = genEnergy s (aArr q) (cArr q) q v + 6 * b *
          ∑ α ∈ PeriodicGridSobolev.multiIndices s, Dg α := by
          rw [sum_add_distrib, ← mul_sum]; rfl
      _ ≤ 8 * Xsq s q v + 6 * b * (3 * Xsq s q v) := by
          gcongr
      _ ≤ 9 * Xsq s q v := by
          have := Xsq_nonneg s q v
          nlinarith

/-! ### The commutator bound -/

theorem cx_comp_bTerm (B : Upper → Upper → ℝ) (q : Grid N → MetricRec) (k : Upper) :
    cx (comp (bTerm B q) k.1.1 k.1.2) = ∑ l : Upper, ((((N : ℝ) ^ 2)⁻¹ * B k l : ℝ) : ℂ) •
      lapC (lapC (cx (comp q l.1.1 l.1.2))) := by
  have e : comp (bTerm B q) k.1.1 k.1.2 = ∑ l : Upper, (((N : ℝ) ^ 2)⁻¹ * B k l) •
      lapR (lapR (comp q l.1.1 l.1.2)) := by
    funext y
    simp only [comp, bTerm, upperOf_upper, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sum]
    exact sum_congr rfl fun l _ => by ring
  rw [e, cx_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [cx_smul, cx_lapR, cx_lapR]

/-- The force `h² B Λ_h² q` of a mark is bounded in `H^{s-1}_h` by `360 b ‖q‖_{s+1}`. -/
theorem sobNorm_bTerm_le (s : ℕ) (hs : 1 ≤ s) {b : ℝ} {B : Upper → Upper → ℝ} (hB : IsMark b B)
    {q : Grid N → MetricRec} (hq : IsSymRec q) (v : Grid N → MetricRec) (k : Upper) :
    PeriodicGridSobolev.sobNorm (s - 1) (cx (comp (bTerm B q) k.1.1 k.1.2)) ≤
      576 * b * Xnorm s q v := by
  have hb := hB.nonneg
  rw [cx_comp_bTerm]
  refine (PeriodicGridSobolev.Moser.sobNorm_sum_le _ _ _).trans ?_
  have hl : ∀ l : Upper, PeriodicGridSobolev.sobNorm (s - 1)
      (((((N : ℝ) ^ 2)⁻¹ * B k l : ℝ) : ℂ) • lapC (lapC (cx (comp q l.1.1 l.1.2)))) ≤
      36 * b * Xnorm s q v := by
    intro l
    rw [PeriodicGridSobolev.Moser.sobNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((N : ℝ) ^ 2)⁻¹)]
    have h1 := sobNorm_lap2_le (s - 1) (cx (comp q l.1.1 l.1.2))
    rw [show s - 1 + 2 = s + 1 by omega] at h1
    have h2 := sobNorm_q_le s hq v l.1.1 l.1.2 le_rfl
    have h3 := hB.entry_le k l
    have h4 := PeriodicGridSobolev.Moser.sobNorm_nonneg (s - 1) (lapC (lapC (cx (comp q l.1.1 l.1.2))))
    have hX := Xnorm_nonneg s q v
    calc ((N : ℝ) ^ 2)⁻¹ * |B k l| * PeriodicGridSobolev.sobNorm (s - 1)
          (lapC (lapC (cx (comp q l.1.1 l.1.2)))) =
          |B k l| * (((N : ℝ) ^ 2)⁻¹ * PeriodicGridSobolev.sobNorm (s - 1)
            (lapC (lapC (cx (comp q l.1.1 l.1.2))))) := by ring
      _ ≤ b * (36 * Xnorm s q v) := by
          refine mul_le_mul h3 (h1.trans ?_) (by positivity) hb
          linarith
      _ = 36 * b * Xnorm s q v := by ring
  calc _ ≤ ∑ _l : Upper, 36 * b * Xnorm s q v := sum_le_sum fun l _ => hl l
    _ = (Fintype.card Upper : ℝ) * (36 * b * Xnorm s q v) := by simp
    _ ≤ 576 * b * Xnorm s q v := by
        have hc : (Fintype.card Upper : ℝ) ≤ 16 := by
          have h1 : Fintype.card Upper ≤ Fintype.card (Fin 4 × Fin 4) := Fintype.card_subtype_le _
          have h2 : Fintype.card (Fin 4 × Fin 4) = 16 := by simp
          exact_mod_cast h1.trans h2.le
        have := Xnorm_nonneg s q v
        have h3 : 0 ≤ 36 * b * Xnorm s q v := by positivity
        calc (Fintype.card Upper : ℝ) * (36 * b * Xnorm s q v) ≤ 16 * (36 * b * Xnorm s q v) :=
              mul_le_mul_of_nonneg_right hc h3
          _ = 576 * b * Xnorm s q v := by ring

/-- **The commutator term is cubic**: `|Σ_α ⟨v_α, a_α 𝒞_α(a⁻¹, h² B Λ_h² q)⟩| ≤ K ‖X‖³` on the
chart, uniformly in the mesh and the mark. -/
theorem abs_commTerm_le (s : ℕ) (hs : 3 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (N : ℕ) [NeZero N] (q v : Grid N → MetricRec) (b : ℝ)
      (B : Upper → Upper → ℝ), IsMark b B → b ≤ 1 / 48 → IsSymRec q → IsSymRec v →
      Xnorm s q v ≤ δ → |commTerm B s q v| ≤ K * Xnorm s q v ^ 3 := by
  obtain ⟨δ0, hδ0, K₁, hK₁, hpc⟩ := pointwise_chart s hs
  obtain ⟨δ2, hδ2, C2, hC2, hm2⟩ := moser_coefficients s (by omega)
  obtain ⟨Cc, hCc, hcalc⟩ := PeriodicGridSobolev.uniform_sobolev_calculus s hs
  set cM : ℝ := ((PeriodicGridSobolev.multiIndices s).card : ℝ)
  set cU : ℝ := (Fintype.card Upper : ℝ)
  refine ⟨min δ0 (δ2 / 16), by positivity, cM * cU * (3 / 2 * (Cc * (C2 * 16) * 12)),
    by positivity, fun N _ q v b B hB hb hq hv hX => ?_⟩
  have hb0 := hB.nonneg
  set X := Xnorm s q v
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  obtain ⟨ha, -, -, -, -, -⟩ := hpc N q v hq hv (hX.trans (min_le_left _ _))
  have ha' : ∀ y, |aArr q y| ≤ 3 / 2 := fun y => by
    rw [abs_le]; constructor <;> linarith [(ha y).1, (ha y).2]
  have hcs : PeriodicGridSobolev.Moser.coordSum s bM q ≤ 16 * X :=
    coordSum_bM_q_le s hq v (by omega)
  have hM2 := hm2 N q (hcs.trans (by linarith [hX.trans (min_le_right _ _)]))
  have hainv : PeriodicGridSobolev.sobNorm s
      (cx (fun x => (aArr q x)⁻¹) - fun _ => (1 : ℂ)) ≤ C2 * 16 * X := by
    refine hM2.2.1.trans ?_
    calc C2 * PeriodicGridSobolev.Moser.coordSum s bM q ≤ C2 * (16 * X) :=
          mul_le_mul_of_nonneg_left hcs hC2
      _ = C2 * 16 * X := by ring
  obtain ⟨-, hcomm⟩ := hcalc N
  have hper : ∀ α ∈ PeriodicGridSobolev.multiIndices s, ∀ k : Upper,
      |((N : ℝ) ^ 3)⁻¹ * ∑ x, DαR α (comp v k.1.1 k.1.2) x * (SαR α (aArr q) x *
        commR α (fun y => (aArr q y)⁻¹) (comp (bTerm B q) k.1.1 k.1.2) x)| ≤
      3 / 2 * (Cc * (C2 * 16) * 12) * X ^ 3 := by
    intro α hα k
    have hdeg := PeriodicGridSobolev.mem_multiIndices.mp hα
    refine (abs_inner_le _ _).trans ?_
    have h1 : PeriodicGridSobolev.gridNorm (cx (DαR α (comp v k.1.1 k.1.2))) ≤ X :=
      (gridNorm_cx_DαR_le hdeg _).trans (sobNorm_v_le s q hv _ _ le_rfl)
    have h2 : PeriodicGridSobolev.gridNorm (cx (fun x => SαR α (aArr q) x *
        commR α (fun y => (aArr q y)⁻¹) (comp (bTerm B q) k.1.1 k.1.2) x)) ≤
        3 / 2 * PeriodicGridSobolev.gridNorm
          (cx (commR α (fun y => (aArr q y)⁻¹) (comp (bTerm B q) k.1.1 k.1.2))) :=
      gridNorm_cx_mul_le (by norm_num) (fun x => ha' (x + svec α))
    have h3 : PeriodicGridSobolev.gridNorm
        (cx (commR α (fun y => (aArr q y)⁻¹) (comp (bTerm B q) k.1.1 k.1.2))) ≤
        Cc * (C2 * 16 * X) * (12 * X) := by
      rw [cx_commR]
      refine ((hcomm α hdeg _ _ 1 0).1).trans ?_
      have hw := sobNorm_bTerm_le s (by omega) hB hq v k
      have hw' : PeriodicGridSobolev.sobNorm (s - 1) (cx (comp (bTerm B q) k.1.1 k.1.2)) ≤
          12 * X := hw.trans (by nlinarith)
      gcongr
      · exact PeriodicGridSobolev.Moser.sobNorm_nonneg _ _
    calc PeriodicGridSobolev.gridNorm (cx (DαR α (comp v k.1.1 k.1.2))) *
          PeriodicGridSobolev.gridNorm (cx (fun x => SαR α (aArr q) x *
            commR α (fun y => (aArr q y)⁻¹) (comp (bTerm B q) k.1.1 k.1.2) x))
        ≤ X * (3 / 2 * (Cc * (C2 * 16 * X) * (12 * X))) := by
          refine mul_le_mul h1 (h2.trans ?_) (PeriodicGridSobolev.gridNorm_nonneg _) hX0
          exact mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = 3 / 2 * (Cc * (C2 * 16) * 12) * X ^ 3 := by ring
  unfold commTerm
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _α ∈ PeriodicGridSobolev.multiIndices s, ∑ _k : Upper,
        3 / 2 * (Cc * (C2 * 16) * 12) * X ^ 3 :=
        sum_le_sum fun α hα => (abs_sum_le_sum_abs _ _).trans
          (sum_le_sum fun k _ => hper α hα k)
    _ = cM * cU * (3 / 2 * (Cc * (C2 * 16) * 12)) * X ^ 3 := by
        simp only [sum_const, card_univ, nsmul_eq_mul, cM, cU]; ring

/-! ### Analyticity of the law vector field -/

theorem lapR_add (u w : Grid N → ℝ) : lapR (u + w) = lapR u + lapR w := lapRLin.map_add u w

theorem lapR_smul (c : ℝ) (u : Grid N → ℝ) : lapR (c • u) = c • lapR u := lapRLin.map_smul c u

/-- `y ↦ (Λ_h² q_l)(x)` as a continuous linear functional of the state. -/
def lap2L (l : Upper) (x : Grid N) : State N →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => lapR (lapR (comp y.1 l.1.1 l.1.2)) x
      map_add' := fun y z => by
        have e : comp (y + z).1 l.1.1 l.1.2 = comp y.1 l.1.1 l.1.2 + comp z.1 l.1.1 l.1.2 := rfl
        rw [e, lapR_add, lapR_add]; rfl
      map_smul' := fun c y => by
        have e : comp (c • y).1 l.1.1 l.1.2 = c • comp y.1 l.1.1 l.1.2 := rfl
        rw [e, lapR_smul, lapR_smul]; rfl }

theorem analyticAt_lawAccel (B : Upper → Upper → ℝ) (y₀ : State N)
    (hdet : ∀ z, (Matrix.of (minkowski + y₀.1 z)).det ≠ 0)
    (ha : ∀ z, harmA (minkowski + y₀.1 z) ≠ 0) (x : Grid N) (μ ν : Fin 4) :
    AnalyticAt ℝ (fun y : State N => lawAccel B y.1 y.2 x μ ν) y₀ := by
  have hA := analyticAt_accel y₀ hdet ha x μ ν
  have hgz : AnalyticAt ℝ (fun y : State N => minkowski + y.1 x) y₀ := by fun_prop
  have hainv : AnalyticAt ℝ (fun y : State N => (aArr y.1 x)⁻¹) y₀ :=
    (((analyticAt_inv_entry _ (hdet x) 0 0).neg).comp_of_eq hgz rfl).inv (ha x)
  have hb : AnalyticAt ℝ (fun y : State N => bTerm B y.1 x μ ν) y₀ := by
    have : (fun y : State N => bTerm B y.1 x μ ν) = fun y => ((N : ℝ) ^ 2)⁻¹ *
        ∑ l : Upper, B (upperOf μ ν) l * lap2L l x y := rfl
    rw [this]
    exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun l _ =>
      analyticAt_const.mul ((lap2L l x).analyticAt y₀))
  have e : (fun y : State N => lawAccel B y.1 y.2 x μ ν) = fun y =>
      harmonicWriterAcceleration y.1 y.2 x μ ν + -((aArr y.1 x)⁻¹ * bTerm B y.1 x μ ν) := rfl
  rw [e]
  exact hA.add (hainv.mul hb).neg

/-! ### The law energy inequality, the common lifespan and the forced estimate -/

/-- **`eq:supp-law-energy-bound`** (`thm:supp-law-stability`, energy part).  For `s ≥ 3` (the
manuscript takes `s ≥ 11`) there are a chart radius `δ > 0` and `C ≥ 0`, independent of the mesh
and uniform over all marks `B = Bᵀ` with `‖B‖_op ≤ 1/48` (`b₀ < c_*/24` with the certified
coercivity `c_* = 1/2` of the chart), such that along every law-family history
(`q_t = v`, `v_t = V_{B,h}(q, v)` on the ten components, symmetric records) in the chart at `t`:
`⅛ ‖X‖² ≤ 𝓔^B ≤ 9 ‖X‖²` and `(𝓔^B)' ≤ C 𝓔^B + C (𝓔^B)^{3/2}`. -/
theorem law_energy_inequality (s : ℕ) (hs : 3 ≤ s) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ) (q v : ℝ → Grid N → MetricRec)
      (t : ℝ), IsMark (1 / 48) B → IsSymRec (q t) → IsSymRec (v t) →
      (∀ x, HasDerivAt (fun τ => q τ x) (v t x) t) →
      (∀ x (κ : Upper), HasDerivAt (fun τ => v τ x κ.1.1 κ.1.2)
        (lawAccel B (q t) (v t) x κ.1.1 κ.1.2) t) →
      Xnorm s (q t) (v t) ≤ δ →
      HasDerivAt (fun τ => lawEnergy B s (q τ) (v τ))
        (energyRate s (q t) (v t) - commTerm B s (q t) (v t)) t ∧
      Xsq s (q t) (v t) / 8 ≤ lawEnergy B s (q t) (v t) ∧
      lawEnergy B s (q t) (v t) ≤ 9 * Xsq s (q t) (v t) ∧
      energyRate s (q t) (v t) - commTerm B s (q t) (v t) ≤
        C * lawEnergy B s (q t) (v t) + C * lawEnergy B s (q t) (v t) ^ ((3 : ℝ) / 2) := by
  obtain ⟨δ1, hδ1, K, hK, hstat⟩ := static_bounds s hs
  obtain ⟨δ0, hδ0, K₁, hK₁, hpc⟩ := pointwise_chart s hs
  obtain ⟨δc, hδc, Kc, hKc, hcomm⟩ := abs_commTerm_le s hs
  refine ⟨min δ1 (min δ0 δc), by positivity, 8 * K + 27 * (K + Kc), by positivity,
    fun N _ B q v t hB hqs hvs hq hv hX => ?_⟩
  obtain ⟨hdA, hdC, -, hrate⟩ := hstat N (q t) (v t) hqs hvs (hX.trans (min_le_left _ _))
  obtain ⟨ha, hc, -, -, -, -⟩ := hpc N (q t) (v t) hqs hvs
    (hX.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have ha0 : ∀ x, aArr (q t) x ≠ 0 := fun x => by have := (ha x).1; positivity
  have hd := hasDerivAt_lawEnergy B hB.1 s q v t hqs hq hv hdA hdC ha0
  obtain ⟨hlow, hup⟩ := lawEnergy_bounds s hB le_rfl (q t) (v t) ha hc
  have hct := hcomm N (q t) (v t) (1 / 48) B hB le_rfl hqs hvs
    (hX.trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨hd, hlow, hup, ?_⟩
  set E := lawEnergy B s (q t) (v t)
  set X := Xnorm s (q t) (v t)
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  have hXsq : Xsq s (q t) (v t) = X ^ 2 := (Xnorm_sq _ _ _).symm
  have hE0 : 0 ≤ E := le_trans (by rw [hXsq]; positivity) hlow
  have hX2 : X ^ 2 ≤ 8 * E := by rw [← hXsq]; linarith
  have hXs : X ≤ 3 * Real.sqrt E := by
    have hs3 : (3 * Real.sqrt E) ^ 2 = 9 * E := by rw [mul_pow, Real.sq_sqrt hE0]; norm_num
    nlinarith [Real.sqrt_nonneg E]
  have hX3 : X ^ 3 ≤ 27 * (E * Real.sqrt E) := by
    have h1 : X ^ 3 ≤ (3 * Real.sqrt E) ^ 3 := pow_le_pow_left₀ hX0 hXs 3
    have h2 : (3 * Real.sqrt E) ^ 3 = 27 * (Real.sqrt E ^ 2 * Real.sqrt E) := by ring
    rw [Real.sq_sqrt hE0] at h2
    linarith
  rw [rpow_three_halves hE0]
  rw [hXsq] at hrate
  have h1 : K * X ^ 2 ≤ K * (8 * E) := mul_le_mul_of_nonneg_left hX2 hK
  have h2 : (K + Kc) * X ^ 3 ≤ (K + Kc) * (27 * (E * Real.sqrt E)) :=
    mul_le_mul_of_nonneg_left hX3 (by positivity)
  have h3 := neg_abs_le (commTerm B s (q t) (v t))
  have hsE : 0 ≤ E * Real.sqrt E := mul_nonneg hE0 (Real.sqrt_nonneg _)
  nlinarith

/-- **A priori bound for the law family on a common time.** -/
theorem law_apriori (s : ℕ) (hs : 3 ≤ s) :
    ∃ b > 0, ∃ T > 0, ∃ C ≥ 1, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ)
      (q v : ℝ → Grid N → MetricRec) (t : ℝ), IsMark (1 / 48) B → 0 ≤ t → t ≤ T →
      IsAccSolution (lawAccel B) t q v → (∀ τ ∈ Icc 0 t, Xnorm s (q τ) (v τ) ≤ b) →
      Xnorm s (q t) (v t) ≤ C * Xnorm s (q 0) (v 0) := by
  obtain ⟨δE, hδE, CE, hCE, hE⟩ := law_energy_inequality s hs
  set b : ℝ := min δE (1 / 3)
  have hb : 0 < b := by positivity
  set T : ℝ := 1 / (2 * CE + 1)
  have hT : 0 < T := by positivity
  set C : ℝ := Real.sqrt (72 * Real.exp 1)
  have hC1 : 1 ≤ C := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    refine Real.sqrt_le_sqrt ?_
    have := Real.add_one_le_exp 1
    linarith
  refine ⟨b, hb, T, hT, C, hC1, fun N _ B q v t hB ht0 htT hsol hX => ?_⟩
  set E : ℝ → ℝ := fun τ => lawEnergy B s (q τ) (v τ)
  have hpt : ∀ τ ∈ Icc 0 t, ∃ r, HasDerivAt E r τ ∧ Xsq s (q τ) (v τ) / 8 ≤ E τ ∧
      E τ ≤ 9 * Xsq s (q τ) (v τ) ∧ r ≤ 2 * CE * E τ := by
    intro τ hτ
    obtain ⟨hqs, hvs, hq, hv⟩ := hsol τ hτ
    have hXτ := hX τ hτ
    obtain ⟨hd, hlow, hup, hrate⟩ := hE N B q v τ hB hqs hvs hq hv (hXτ.trans (min_le_left _ _))
    refine ⟨_, hd, hlow, hup, ?_⟩
    have hE0 : 0 ≤ E τ := le_trans (by have := Xsq_nonneg s (q τ) (v τ); linarith) hlow
    have hE1 : E τ ≤ 1 := by
      have h1 : Xsq s (q τ) (v τ) = Xnorm s (q τ) (v τ) ^ 2 := (Xnorm_sq _ _ _).symm
      have h2 : Xnorm s (q τ) (v τ) ^ 2 ≤ (1 / 3) ^ 2 :=
        pow_le_pow_left₀ (Xnorm_nonneg _ _ _) (hXτ.trans (min_le_right _ _)) 2
      show lawEnergy B s (q τ) (v τ) ≤ 1
      nlinarith
    have hsq : E τ ^ ((3 : ℝ) / 2) ≤ E τ := by
      rw [rpow_three_halves hE0]
      have : Real.sqrt (E τ) ≤ 1 := Real.sqrt_le_one.mpr hE1
      nlinarith
    have : CE * E τ ^ ((3 : ℝ) / 2) ≤ CE * E τ := mul_le_mul_of_nonneg_left hsq hCE
    show energyRate s (q τ) (v τ) - commTerm B s (q τ) (v τ) ≤ 2 * CE * E τ
    linarith
  choose! r hr using hpt
  set φ : ℝ → ℝ := fun τ => E τ * Real.exp (-(2 * CE) * τ)
  have hφd : ∀ τ ∈ Icc 0 t, HasDerivAt φ (r τ * Real.exp (-(2 * CE) * τ) +
      E τ * (Real.exp (-(2 * CE) * τ) * (-(2 * CE)))) τ := by
    intro τ hτ
    have h2 : HasDerivAt (fun σ => Real.exp (-(2 * CE) * σ))
        (Real.exp (-(2 * CE) * τ) * (-(2 * CE))) τ := by
      have := ((hasDerivAt_id τ).const_mul (-(2 * CE))).exp
      simpa using this
    exact (hr τ hτ).1.mul h2
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
  have hXt : Xsq s (q t) (v t) ≤ 72 * Real.exp 1 * Xsq s (q 0) (v 0) := by
    have h1 := (hr t htmem).2.1
    have h2 := (hr 0 h0mem).2.2.1
    have he := Real.exp_pos 1
    nlinarith
  rw [Xnorm, Xnorm, show C = Real.sqrt (72 * Real.exp 1) from rfl, ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt hXt

/-- **`eq:supp-law-lifespan`** (`thm:supp-law-stability`, lifespan part).  There are
`ε_s, T_s > 0` and `C_s ≥ 0`, independent of the mesh and of the mark `B` (`B = Bᵀ`,
`‖B‖_op ≤ 1/48`), such that every symmetric initial record with `‖X(0)‖_{X^s_h} ≤ ε_s` has a
unique solution of the law-family writer `eq:supp-law-family` on `[0, T_s]`, and
`sup_{t ≤ T_s} ‖X(t)‖_{X^s_h} ≤ C_s ‖X(0)‖_{X^s_h}`. -/
theorem law_lifespan (s : ℕ) (hs : 3 ≤ s) :
    ∃ ε > 0, ∃ T > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ),
      IsMark (1 / 48) B → ∀ (q₀ v₀ : Grid N → MetricRec), IsSymRec q₀ → IsSymRec v₀ →
      Xnorm s q₀ v₀ ≤ ε →
      (∃ q v : ℝ → Grid N → MetricRec, q 0 = q₀ ∧ v 0 = v₀ ∧ IsAccSolution (lawAccel B) T q v ∧
        ∀ t ∈ Icc 0 T, Xnorm s (q t) (v t) ≤ C * Xnorm s q₀ v₀) ∧
      ∀ q v q' v' : ℝ → Grid N → MetricRec, q 0 = q₀ → v 0 = v₀ → q' 0 = q₀ → v' 0 = v₀ →
        IsAccSolution (lawAccel B) T q v → IsAccSolution (lawAccel B) T q' v' →
        ∀ t ∈ Icc 0 T, q t = q' t ∧ v t = v' t := by
  obtain ⟨b, hb, T, hT, C, hC1, hap⟩ := law_apriori s hs
  obtain ⟨r₀, hr₀, hchart⟩ := exists_det_chart
  have hS := supConst_nonneg
  set b' : ℝ := min b (r₀ / (4 * (supConst + 1)))
  have hb' : 0 < b' := by positivity
  have hbr : supConst * b' ≤ r₀ / 4 := by
    have h1 : b' ≤ r₀ / (4 * (supConst + 1)) := min_le_right _ _
    calc supConst * b' ≤ supConst * (r₀ / (4 * (supConst + 1))) :=
          mul_le_mul_of_nonneg_left h1 hS
      _ ≤ r₀ / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  refine ⟨b' / 2 / C, by positivity, T, hT, C, by linarith, fun N _ B hB q₀ v₀ hq₀ hv₀ hX₀ => ?_⟩
  have hAn : ∀ y : State N, ‖y‖ < r₀ → ∀ x μ ν,
      AnalyticAt ℝ (fun y : State N => lawAccel B y.1 y.2 x μ ν) y := by
    intro y hy x μ ν
    have hz : ∀ z, ‖(minkowski + y.1 z) - minkowski‖ < r₀ := fun z => by
      rw [add_sub_cancel_left]
      exact lt_of_le_of_lt ((norm_le_pi_norm y.1 z).trans (norm_fst_le y)) hy
    exact analyticAt_lawAccel B y (fun z => (hchart _ (hz z)).1) (fun z => (hchart _ (hz z)).2)
      x μ ν
  exact lifespan_core s hs (lawAccel B) hr₀ hb' hT hC1 hbr hAn
    (fun q v t ht0 htT hsol hX => hap N B q v t hB ht0 htT hsol
      fun τ hτ => (hX τ hτ).trans (min_le_left _ _)) q₀ v₀ hq₀ hv₀ hX₀

theorem forcingTerm_add (s : ℕ) (q v f g : Grid N → MetricRec) :
    forcingTerm s q v (f + g) = forcingTerm s q v f + forcingTerm s q v g := by
  unfold forcingTerm
  rw [← sum_add_distrib]
  refine sum_congr rfl fun α _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun κ _ => ?_
  rw [← mul_add, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  have e : comp (f + g) κ.1.1 κ.1.2 = comp f κ.1.1 κ.1.2 + comp g κ.1.1 κ.1.2 := rfl
  rw [e, DαR_add, Pi.add_apply]
  ring

/-- **`eq:supp-law-forced`** (`thm:supp-law-stability`, forced part).  With an additional
acceleration defect `f` (`v_t = V_{B,h}(q, v) + f`), on the same chart and uniformly in the mesh
and the mark: `d𝓔^B/dt ≤ 2 (𝓔^B)^{1/2} (C (𝓔^B)^{1/2} + C 𝓔^B + C ‖f‖_{s,h})` and, where
`𝓔^B > 0`, `((𝓔^B)^{1/2})' ≤ C (𝓔^B)^{1/2} + C 𝓔^B + C ‖f‖_{s,h}`. -/
theorem law_forced_energy (s : ℕ) (hs : 3 ≤ s) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ)
      (q v f : ℝ → Grid N → MetricRec) (t : ℝ), IsMark (1 / 48) B →
      IsSymRec (q t) → IsSymRec (v t) →
      (∀ x, HasDerivAt (fun τ => q τ x) (v t x) t) →
      (∀ x (κ : Upper), HasDerivAt (fun τ => v τ x κ.1.1 κ.1.2)
        (lawAccel B (q t) (v t) x κ.1.1 κ.1.2 + f t x κ.1.1 κ.1.2) t) →
      Xnorm s (q t) (v t) ≤ δ →
      ∃ r, HasDerivAt (fun τ => lawEnergy B s (q τ) (v τ)) r t ∧
        Xsq s (q t) (v t) / 8 ≤ lawEnergy B s (q t) (v t) ∧
        r ≤ 2 * Real.sqrt (lawEnergy B s (q t) (v t)) *
          (C * Real.sqrt (lawEnergy B s (q t) (v t)) + C * lawEnergy B s (q t) (v t) +
            C * Fnorm s (f t)) ∧
        (0 < lawEnergy B s (q t) (v t) →
          HasDerivAt (fun τ => Real.sqrt (lawEnergy B s (q τ) (v τ)))
            (r / (2 * Real.sqrt (lawEnergy B s (q t) (v t)))) t ∧
          r / (2 * Real.sqrt (lawEnergy B s (q t) (v t))) ≤
            C * Real.sqrt (lawEnergy B s (q t) (v t)) + C * lawEnergy B s (q t) (v t) +
              C * Fnorm s (f t)) := by
  obtain ⟨δ1, hδ1, K, hK, hstat⟩ := static_bounds s hs
  obtain ⟨δ0, hδ0, K₁, hK₁, hpc⟩ := pointwise_chart s hs
  obtain ⟨δc, hδc, Kc, hKc, hcomm⟩ := abs_commTerm_le s hs
  set cM : ℝ := ((PeriodicGridSobolev.multiIndices s).card : ℝ)
  set cU : ℝ := (Fintype.card Upper : ℝ)
  set C : ℝ := 4 * K + 14 * (K + Kc) + 3 * cM * cU
  refine ⟨min δ1 (min δ0 δc), by positivity, C, by positivity,
    fun N _ B q v f t hB hqs hvs hq hv hX => ?_⟩
  obtain ⟨hdA, hdC, -, hrate⟩ := hstat N (q t) (v t) hqs hvs (hX.trans (min_le_left _ _))
  obtain ⟨ha, hc, -, -, -, -⟩ := hpc N (q t) (v t) hqs hvs
    (hX.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have ha0 : ∀ x, aArr (q t) x ≠ 0 := fun x => by have := (ha x).1; positivity
  have ha' : ∀ y, |aArr (q t) y| ≤ 3 / 2 := fun y => by
    rw [abs_le]; constructor <;> linarith [(ha y).1, (ha y).2]
  -- the exact derivative
  have h1 := hasDerivAt_shiftedEnergy_forced s q v (fun τ => lawForce B (q τ) + f τ) t hqs hq
    (fun x κ => by
      have := hv x κ
      simp only [lawAccel, Pi.add_apply] at this ⊢
      rw [← add_assoc]; exact this) hdA hdC
  have h2 := hasDerivAt_lawExtra B hB.1 s q v t hq
  set rr := energyRate s (q t) (v t) - commTerm B s (q t) (v t) + forcingTerm s (q t) (v t) (f t)
  have hd : HasDerivAt (fun τ => lawEnergy B s (q τ) (v τ)) rr t := by
    refine (h1.add h2).congr_deriv ?_
    rw [forcedRate_eq, forcingTerm_add, forcingTerm_lawForce B s (q t) (v t) ha0]
    simp only [rr]; ring
  refine ⟨rr, hd, ?_⟩
  obtain ⟨hlow, hup⟩ := lawEnergy_bounds s hB le_rfl (q t) (v t) ha hc
  have hct := hcomm N (q t) (v t) (1 / 48) B hB le_rfl hqs hvs
    (hX.trans ((min_le_right _ _).trans (min_le_right _ _)))
  set E := lawEnergy B s (q t) (v t)
  set X := Xnorm s (q t) (v t)
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  have hXsq : Xsq s (q t) (v t) = X ^ 2 := (Xnorm_sq _ _ _).symm
  have hE0 : 0 ≤ E := le_trans (by rw [hXsq]; positivity) hlow
  have hsE := Real.sqrt_nonneg E
  have hsq : Real.sqrt E * Real.sqrt E = E := Real.mul_self_sqrt hE0
  have hX2 : X ^ 2 ≤ 8 * E := by rw [← hXsq]; linarith
  have hXs : X ≤ 3 * Real.sqrt E := by nlinarith
  -- the forcing term
  have hF : forcingTerm s (q t) (v t) (f t) ≤ 3 / 2 * cM * cU * X * Fnorm s (f t) := by
    unfold forcingTerm
    have hper : ∀ α ∈ PeriodicGridSobolev.multiIndices s, ∀ κ : Upper,
        ((N : ℝ) ^ 3)⁻¹ * ∑ x, DαR α (comp (v t) κ.1.1 κ.1.2) x *
          (SαR α (aArr (q t)) x * DαR α (comp (f t) κ.1.1 κ.1.2) x) ≤
        X * (3 / 2 * Fnorm s (f t)) := by
      intro α hα κ
      have hdeg := PeriodicGridSobolev.mem_multiIndices.mp hα
      refine (le_abs_self _).trans ((abs_inner_le _ _).trans ?_)
      refine mul_le_mul ?_ ?_ (PeriodicGridSobolev.gridNorm_nonneg _) hX0
      · exact (gridNorm_cx_DαR_le hdeg _).trans (sobNorm_v_le s (q t) hvs _ _ le_rfl)
      · refine (gridNorm_cx_mul_le (by norm_num) (fun x => ha' (x + svec α))).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact (gridNorm_cx_DαR_le hdeg _).trans (sobNorm_le_Fnorm s (f t) κ)
    calc _ ≤ ∑ _α ∈ PeriodicGridSobolev.multiIndices s, ∑ _κ : Upper,
          X * (3 / 2 * Fnorm s (f t)) := sum_le_sum fun α hα => sum_le_sum fun κ _ => hper α hα κ
      _ = 3 / 2 * cM * cU * X * Fnorm s (f t) := by
          simp only [sum_const, card_univ, nsmul_eq_mul, cM, cU]; ring
  have hFn := Fnorm_nonneg s (f t)
  have hmain : rr ≤ 2 * Real.sqrt E * (C * Real.sqrt E + C * E + C * Fnorm s (f t)) := by
    rw [hXsq] at hrate
    have k1 : K * X ^ 2 ≤ K * (8 * E) := mul_le_mul_of_nonneg_left hX2 hK
    have hX3 : X ^ 3 ≤ 27 * (E * Real.sqrt E) := by
      have h3 : X ^ 3 ≤ (3 * Real.sqrt E) ^ 3 := pow_le_pow_left₀ hX0 hXs 3
      have h4 : (3 * Real.sqrt E) ^ 3 = 27 * ((Real.sqrt E * Real.sqrt E) * Real.sqrt E) := by
        ring
      rw [hsq] at h4
      linarith
    have k2 : (K + Kc) * X ^ 3 ≤ (K + Kc) * (27 * (E * Real.sqrt E)) :=
      mul_le_mul_of_nonneg_left hX3 (by positivity)
    have k3 := neg_abs_le (commTerm B s (q t) (v t))
    have k4 : 3 / 2 * cM * cU * X * Fnorm s (f t) ≤
        3 / 2 * cM * cU * (3 * Real.sqrt E) * Fnorm s (f t) := by
      have : 0 ≤ 3 / 2 * cM * cU := by positivity
      gcongr
    have hexp : 2 * Real.sqrt E * (C * Real.sqrt E + C * E + C * Fnorm s (f t)) =
        2 * C * E + 2 * C * (E * Real.sqrt E) + 2 * C * (Real.sqrt E * Fnorm s (f t)) := by
      linear_combination (2 * C) * hsq
    rw [hexp]
    have hcMU : 0 ≤ cM * cU := by positivity
    have hEs : 0 ≤ E * Real.sqrt E := mul_nonneg hE0 hsE
    have hsF : 0 ≤ Real.sqrt E * Fnorm s (f t) := mul_nonneg hsE hFn
    have hC1 : 8 * K ≤ 2 * C := by simp only [C]; nlinarith
    have hC2 : 27 * (K + Kc) ≤ 2 * C := by simp only [C]; nlinarith
    have hC3 : 9 / 2 * (cM * cU) ≤ 2 * C := by simp only [C]; nlinarith
    simp only [rr]
    nlinarith
  refine ⟨hlow, hmain, fun hpos => ⟨?_, ?_⟩⟩
  · have hh := (Real.hasDerivAt_sqrt hpos.ne').comp t hd
    refine hh.congr_deriv ?_
    rw [one_div, inv_mul_eq_div]
  · have hsqpos : 0 < Real.sqrt E := Real.sqrt_pos.mpr hpos
    rw [div_le_iff₀ (by positivity)]
    linarith [hmain]

/-- Non-vacuity of the law family: the zero mark is admissible and the flat record is a global
solution of every member of the family; the scalar mark `B = I/48` is admissible as well. -/
example : IsMark (1 / 48) (fun _ _ => (0 : ℝ)) ∧
    IsMark (1 / 48) (fun k l => if k = l then (1 / 48 : ℝ) else 0) := by
  refine ⟨⟨fun _ _ => rfl, fun ξ η => ?_⟩, ⟨fun k l => ?_, fun ξ η => ?_⟩⟩
  · simp only [mul_zero, zero_mul, sum_const_zero, abs_zero]
    positivity
  · by_cases h : k = l
    · subst h; rfl
    · simp [h, Ne.symm h]
  · have e : ∑ k, ∑ l, ξ k * (if k = l then (1 / 48 : ℝ) else 0) * η l =
        1 / 48 * ∑ k, ξ k * η k := by
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      simp only [mul_ite, mul_zero, ite_mul, zero_mul, sum_ite_eq, Finset.mem_univ, ite_true]
      ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 48), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact (abs_sum_le_sum_abs _ _).trans (by
      have := Real.sum_mul_le_sqrt_mul_sqrt univ (fun k => |ξ k|) (fun k => |η k|)
      simp only [sq_abs, abs_mul] at this ⊢
      exact this)

/-- Non-vacuity of `law_lifespan`: the zero mark and the flat initial record satisfy its
hypotheses for every mesh. -/
example (s : ℕ) (hs : 3 ≤ s) : True := by
  obtain ⟨ε, hε, T, hT, C, hC, h⟩ := law_lifespan s hs
  have hX : Xnorm s (0 : Grid 5 → MetricRec) 0 ≤ ε := by
    have : Xsq s (0 : Grid 5 → MetricRec) 0 = 0 := by
      unfold Xsq
      refine sum_eq_zero fun κ _ => ?_
      have e : cx (comp (0 : Grid 5 → MetricRec) κ.1.1 κ.1.2) = 0 := by funext x; simp [comp, cx]
      rw [e]
      simp [PeriodicGridSobolev.sobSq, PeriodicGridSobolev.gridNormSq]
    rw [Xnorm, this, Real.sqrt_zero]; exact hε.le
  have hB : IsMark (1 / 48) (fun _ _ => (0 : ℝ)) := ⟨fun _ _ => rfl, fun ξ η => by
    simp only [mul_zero, zero_mul, sum_const_zero, abs_zero]; positivity⟩
  have hsym : IsSymRec (0 : Grid 5 → MetricRec) := fun _ _ _ => rfl
  obtain ⟨⟨q, v, -, -, -, -⟩, -⟩ := h 5 _ hB 0 0 hsym hsym hX
  trivial
end

end RenewalGeometry.OpenWriterLifespan
