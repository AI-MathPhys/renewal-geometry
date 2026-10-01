/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterLawDifference
import RenewalGeometry.Analysis.TimeSobolevSupBound
import RenewalGeometry.Analysis.PiecewisePolynomialJetGluing

/-!
# Chronological words of the law family and the stopped physical cost
  (`lem:supp-law-cost-control`)

Fix a mark `B` of the closed ball (`B = Bᵀ`, `‖B‖_op ≤ 1/48`) and `T > 0`.  A **chronological
word** (`LawWord`, `LawWord.IsChronological`) is a partition of `[0, T]` into cells
`I_j = [t_j, t_{j+1}]`, `c₋ h² ≤ t_{j+1} - t_j ≤ c₊ h²`, carrying finite physical polynomial
metric segments (letters, symmetric record coefficients) with shared endpoint value, velocity,
acceleration and jerk records, plus an optional grammar/execution failure index.  The glued
record path `Q = W.path 0` has two-sided derivatives `Q' = W.path 1`, `Q'' = W.path 2`,
`Q''' = W.path 3` (`PiecewisePolynomialJetGluing`).

* `LawWord.residual`: the actual acceleration defect `f = Q'' - V_{B,h}(Q, Q')`
  (`eq:supp-law-residual`);
* `LawWord.guardTime`: the first exit time of the record from the guard chart
  `‖(Q, Q')‖_{X^s_h} < ρ`; `LawWord.stopTime`: the guard time, or the failure node;
* `LawWord.cost`: the stopped physical cost
  `C_h = ε⁻² ∫_0^{t_stop} (‖f‖²_{s,h} + ‖∂_t f‖²_{s-3,h}) dt + 𝟙_{failure}` (`eq:main-law-cost`,
  summed over the cells);
* `lawCostInner`, `hasDerivAt_lawCostInner_self`, `abs_lawCostInner_le`: the bilinear form of `‖·‖²_{r,h}` and
  `|(d/dt) ‖f‖²_{r,h}| ≤ 2 ‖f‖_{r,h} ‖∂_t f‖_{r,h}`;
* `law_cost_control` (**`lem:supp-law-cost-control`**).
-/

open Set Metric Filter Topology Finset MeasureTheory
open scoped NNReal BigOperators

namespace RenewalGeometry.OpenWriterLifespan

open RootParityConnector OpenWriterGridBridge OpenWriterChart OpenWriterEnergy HarmonicWriter
  OpenWriterEnergyEstimate

noncomputable section

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-! ### The bilinear form of the record Sobolev norm -/

/-- The bilinear form `⟨f, g⟩_{r,h} = Σ_κ Σ_{|α| ≤ r} ⟨D^α f_κ, D^α g_κ⟩_h` of `‖·‖²_{r,h}`. -/
def lawCostInner (r : ℕ) (f g : Grid N → MetricRec) : ℝ :=
  ∑ κ : Upper, ∑ α ∈ PeriodicGridSobolev.multiIndices r, ((N : ℝ) ^ 3)⁻¹ *
    ∑ x, DαR α (comp f κ.1.1 κ.1.2) x * DαR α (comp g κ.1.1 κ.1.2) x

theorem lawCost_Fnorm_sq_eq (r : ℕ) (f : Grid N → MetricRec) : Fnorm r f ^ 2 = lawCostInner r f f := by
  unfold Fnorm lawCostInner
  rw [Real.sq_sqrt (sum_nonneg fun _ _ => PeriodicGridSobolev.sobSq_nonneg _ _)]
  refine sum_congr rfl fun κ _ => ?_
  unfold PeriodicGridSobolev.sobSq
  refine sum_congr rfl fun α _ => ?_
  rw [← cx_DαR, gridNormSq_cx]
  congr 1
  exact sum_congr rfl fun x _ => by ring

theorem abs_lawCostInner_le (r : ℕ) (f g : Grid N → MetricRec) :
    |lawCostInner r f g| ≤ Fnorm r f * Fnorm r g := by
  set a : Upper → (Fin 3 → ℕ) → ℝ := fun κ α =>
    PeriodicGridSobolev.gridNorm (cx (DαR α (comp f κ.1.1 κ.1.2)))
  set b : Upper → (Fin 3 → ℕ) → ℝ := fun κ α =>
    PeriodicGridSobolev.gridNorm (cx (DαR α (comp g κ.1.1 κ.1.2)))
  have h1 : |lawCostInner r f g| ≤ ∑ κ : Upper, ∑ α ∈ PeriodicGridSobolev.multiIndices r,
      a κ α * b κ α :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun κ _ => (abs_sum_le_sum_abs _ _).trans
      (sum_le_sum fun α _ => abs_inner_le _ _))
  have hsq : ∀ (u : Grid N → MetricRec) (κ : Upper),
      ∑ α ∈ PeriodicGridSobolev.multiIndices r,
        PeriodicGridSobolev.gridNorm (cx (DαR α (comp u κ.1.1 κ.1.2))) ^ 2 =
      PeriodicGridSobolev.sobSq r (cx (comp u κ.1.1 κ.1.2)) := by
    intro u κ
    unfold PeriodicGridSobolev.sobSq
    refine sum_congr rfl fun α _ => ?_
    rw [PeriodicGridSobolev.gridNorm_sq, cx_DαR]
  have h2 : ∀ κ : Upper, ∑ α ∈ PeriodicGridSobolev.multiIndices r, a κ α * b κ α ≤
      PeriodicGridSobolev.sobNorm r (cx (comp f κ.1.1 κ.1.2)) *
        PeriodicGridSobolev.sobNorm r (cx (comp g κ.1.1 κ.1.2)) := by
    intro κ
    refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans (le_of_eq ?_)
    simp only [a, b]
    rw [hsq f κ, hsq g κ]
    rfl
  have h3 : ∑ κ : Upper, PeriodicGridSobolev.sobNorm r (cx (comp f κ.1.1 κ.1.2)) *
      PeriodicGridSobolev.sobNorm r (cx (comp g κ.1.1 κ.1.2)) ≤ Fnorm r f * Fnorm r g := by
    refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans (le_of_eq ?_)
    simp only [PeriodicGridSobolev.sobNorm_sq]
    rfl
  exact h1.trans ((sum_le_sum fun κ _ => h2 κ).trans h3)

theorem hasDerivAt_lawCostInner_self (r : ℕ) {f : ℝ → Grid N → MetricRec} {f' : Grid N → MetricRec}
    {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun τ => lawCostInner r (f τ) (f τ)) (2 * lawCostInner r (f t) f') t := by
  have hc : ∀ (κ : Upper) α x, HasDerivAt (fun τ => DαR α (comp (f τ) κ.1.1 κ.1.2) x)
      (DαR α (comp f' κ.1.1 κ.1.2) x) t := by
    intro κ α x
    refine hasDerivAt_DαR (u := fun τ => comp (f τ) κ.1.1 κ.1.2) (fun y => ?_) α x
    exact hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_pi.1 hf y) κ.1.1) κ.1.2
  unfold lawCostInner
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset Upper)) fun κ _ =>
    HasDerivAt.fun_sum (u := PeriodicGridSobolev.multiIndices r) fun α _ =>
      HasDerivAt.const_mul (((N : ℝ) ^ 3)⁻¹) (HasDerivAt.fun_sum (u := Finset.univ) fun x _ =>
        (hc κ α x).mul (hc κ α x))
  refine h.congr_deriv ?_
  rw [mul_sum]
  refine sum_congr rfl fun κ _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun α _ => ?_
  rw [mul_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  ring

/-- `|(d/dt) ‖f‖²_{r,h}| ≤ 2 ‖f‖_{r,h} ‖∂_t f‖_{r,h}`. -/
theorem lawCost_hasDerivAt_Fnorm_sq (r : ℕ) {f : ℝ → Grid N → MetricRec} {f' : Grid N → MetricRec}
    {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun τ => Fnorm r (f τ) ^ 2) (2 * lawCostInner r (f t) f') t ∧
      |2 * lawCostInner r (f t) f'| ≤ 2 * Real.sqrt (Fnorm r (f t) ^ 2) * Fnorm r f' := by
  refine ⟨?_, ?_⟩
  · have e : (fun τ => Fnorm r (f τ) ^ 2) = fun τ => lawCostInner r (f τ) (f τ) := by
      funext τ; exact lawCost_Fnorm_sq_eq r (f τ)
    rw [e]; exact hasDerivAt_lawCostInner_self r hf
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), Real.sqrt_sq (Fnorm_nonneg _ _),
      mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_lawCostInner_le r _ _) (by norm_num)

/-! ### Chronological words -/

/-- **A chronological word** of the law family on the cutoff-`N` grid: `J` cells with nodes
`node 0 < node 1 < ⋯` (cell `j` is `[node j, node (j + 1)]`), letters given by the coefficients of
polynomial metric segments of degree `≤ deg` in the local time `t - node j`, and an optional index
of a grammar or execution failure (which terminates the word). -/
structure LawWord (N : ℕ) where
  /-- number of cells (letters) -/
  J : ℕ
  /-- degree bound of the polynomial letters -/
  deg : ℕ
  /-- the cell endpoints `t_j` -/
  node : ℕ → ℝ
  /-- the coefficients of letter `j`: `Q_j(t) = Σ_i (t - t_j)^i • letter j i` -/
  letter : ℕ → Fin (deg + 1) → (Grid N → MetricRec)
  /-- the cell of a grammar or execution failure, if any -/
  fail : Option ℕ

namespace LawWord

/-- The `k`-th time derivative of the glued record path of the word (`k = 0`: the record `Q`). -/
def path (W : LawWord N) (k : ℕ) : ℝ → Grid N → MetricRec :=
  SplineGluing.splinePath W.node W.J W.letter k

/-- **Chronological word on `[0, T]` at mesh `h`**: `J ≥ 1` cells partitioning `[0, T]`
(`node 0 = 0`, `node J = T`, strictly increasing nodes), cell durations
`c₋ h² ≤ τ_j ≤ c₊ h²`, letters with shared endpoint value, velocity, acceleration and jerk
records (`JetsMatch … 3`), physical (symmetric) metric records, and a failure index (if any)
inside the word. -/
def IsChronological (W : LawWord N) (h cm cp T : ℝ) : Prop :=
  0 < W.J ∧ W.node 0 = 0 ∧ W.node W.J = T ∧ StrictMono W.node ∧
    (∀ j < W.J, cm * h ^ 2 ≤ W.node (j + 1) - W.node j ∧ W.node (j + 1) - W.node j ≤ cp * h ^ 2) ∧
    SplineGluing.JetsMatch W.node W.J W.letter 3 ∧
    (∀ j i, IsSymRec (W.letter j i)) ∧
    (∀ j, W.fail = some j → j < W.J)

/-- **The actual acceleration defect** `f = Q'' - V_{B,h}(Q, Q')` (`eq:supp-law-residual`). -/
def residual (W : LawWord N) (B : Upper → Upper → ℝ) (t : ℝ) : Grid N → MetricRec :=
  W.path 2 t - lawAccel B (W.path 0 t) (W.path 1 t)

/-- The top record norm `‖(Q, Q')(t)‖_{X^s_h}` along the word. -/
def recNorm (W : LawWord N) (s : ℕ) (t : ℝ) : ℝ := Xnorm s (W.path 0 t) (W.path 1 t)

open Classical in
/-- **The guard time**: the first time in `[0, T]` at which the record reaches the guard radius
`ρ` (`‖(Q, Q')‖_{X^s_h} ≥ ρ`), or `T` if the guard is never hit. -/
def guardTime (W : LawWord N) (s : ℕ) (ρ T : ℝ) : ℝ :=
  if ∃ t ∈ Icc 0 T, ρ ≤ W.recNorm s t then sInf {t | t ∈ Icc 0 T ∧ ρ ≤ W.recNorm s t} else T

/-- The stopping time of the word: the guard time, or the failure node if earlier. -/
def stopTime (W : LawWord N) (s : ℕ) (ρ T : ℝ) : ℝ :=
  match W.fail with
  | none => W.guardTime s ρ T
  | some j => min (W.guardTime s ρ T) (W.node j)

/-- The cost density `‖f‖²_{s,h} + ‖∂_t f‖²_{s-3,h}`. -/
def costDensity (W : LawWord N) (B : Upper → Upper → ℝ) (s : ℕ) (t : ℝ) : ℝ :=
  Fnorm s (W.residual B t) ^ 2 + Fnorm (s - 3) (deriv (W.residual B) t) ^ 2

/-- **The stopped physical cost** (`eq:main-law-cost`, summed over the cells):
`C_h = ε⁻² ∫_0^{t_stop} (‖f‖²_{s,h} + ‖∂_t f‖²_{s-3,h}) dt`, plus one for a grammar or execution
failure. -/
def cost (W : LawWord N) (B : Upper → Upper → ℝ) (s : ℕ) (ρ ε T : ℝ) : ℝ :=
  (ε ^ 2)⁻¹ * (∫ t in (0)..(W.stopTime s ρ T), W.costDensity B s t) +
    (if W.fail.isSome then 1 else 0)

/-! ### Regularity of the glued word -/

theorem isSymRec_path (W : LawWord N) (hW : ∀ j i, IsSymRec (W.letter j i)) (k : ℕ) (t : ℝ) :
    IsSymRec (W.path k t) := by
  intro x μ ν
  simp only [path, SplineGluing.splinePath, TwoPointHermite.polyCurveDeriv, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  exact sum_congr rfl fun i _ => by rw [hW _ i x μ ν]

theorem hasDerivAt_path {W : LawWord N} (ht : StrictMono W.node)
    (hm : SplineGluing.JetsMatch W.node W.J W.letter 3) {k : ℕ} (hk : k ≤ 2) (t : ℝ) :
    HasDerivAt (W.path k) (W.path (k + 1) t) t :=
  SplineGluing.hasDerivAt_splinePath ht hm (by omega) t

theorem continuous_path {W : LawWord N} (ht : StrictMono W.node)
    (hm : SplineGluing.JetsMatch W.node W.J W.letter 3) {k : ℕ} (hk : k ≤ 3) :
    Continuous (W.path k) :=
  SplineGluing.continuous_splinePath ht hm hk

theorem contDiff_path {W : LawWord N} (ht : StrictMono W.node)
    (hm : SplineGluing.JetsMatch W.node W.J W.letter 3) {k : ℕ} (hk : k ≤ 2) :
    ContDiff ℝ 1 (W.path k) := by
  refine contDiff_one_iff_deriv.2 ⟨fun t => (hasDerivAt_path ht hm hk t).differentiableAt, ?_⟩
  have e : deriv (W.path k) = W.path (k + 1) := funext fun t => (hasDerivAt_path ht hm hk t).deriv
  rw [e]
  exact continuous_path ht hm (by omega)

theorem continuous_recNorm {W : LawWord N} (ht : StrictMono W.node)
    (hm : SplineGluing.JetsMatch W.node W.J W.letter 3) (s : ℕ) :
    Continuous (W.recNorm s) := by
  have h := (continuous_XnormS (N := N) s).comp ((continuous_path ht hm (k := 0) (by norm_num)).prodMk
    (continuous_path ht hm (k := 1) (by norm_num)))
  exact h

end LawWord

/-- **The defect is `C¹` on the analytic chart**: there is a radius `ρc > 0`, independent of the
mesh, the mark and the word, such that the residual of a word is `C¹` at every time where the
record is in `‖(Q, Q')‖_{X^s_h} < ρc`. -/
theorem residual_contDiffAt (s : ℕ) (hs : 1 ≤ s) :
    ∃ ρc > 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ) (W : LawWord N),
      StrictMono W.node → SplineGluing.JetsMatch W.node W.J W.letter 3 →
      (∀ j i, IsSymRec (W.letter j i)) → ∀ t, W.recNorm s t < ρc →
      ContDiffAt ℝ 1 (W.residual B) t := by
  obtain ⟨r₀, hr₀, hchart⟩ := exists_det_chart
  have hS := supConst_nonneg
  have hS1 : 0 < supConst + 1 := by linarith
  refine ⟨r₀ / (supConst + 1), div_pos hr₀ hS1, fun N _ B W ht hm hsym t hX => ?_⟩
  set y : ℝ → State N := fun τ => (W.path 0 τ, W.path 1 τ)
  have hy : ContDiff ℝ 1 y :=
    (LawWord.contDiff_path ht hm (k := 0) (by norm_num)).prodMk
      (LawWord.contDiff_path ht hm (k := 1) (by norm_num))
  have hz : ∀ z, ‖(minkowski + (y t).1 z) - minkowski‖ < r₀ := by
    intro z
    rw [add_sub_cancel_left]
    have h1 := norm_q_le s hs (LawWord.isSymRec_path W hsym 0 t) (W.path 1 t) z
    have h2 : supConst * W.recNorm s t ≤ supConst * (r₀ / (supConst + 1)) :=
      mul_le_mul_of_nonneg_left hX.le hS
    have h3 : supConst * (r₀ / (supConst + 1)) < r₀ := by
      rw [mul_div_assoc', div_lt_iff₀ hS1]
      nlinarith
    exact lt_of_le_of_lt h1 (h2.trans_lt h3)
  have hG3 : ∀ x μ ν, AnalyticAt ℝ (fun y : State N => lawAccel B y.1 y.2 x μ ν) (y t) :=
    fun x μ ν => analyticAt_lawAccel B (y t) (fun z => (hchart _ (hz z)).1)
      (fun z => (hchart _ (hz z)).2) x μ ν
  have hG : AnalyticAt ℝ (fun y : State N => lawAccel B y.1 y.2) (y t) := by
    have h := AnalyticAt.pi (𝕜 := ℝ) (e := y t) fun x => AnalyticAt.pi (𝕜 := ℝ) (e := y t)
      fun μ => AnalyticAt.pi (𝕜 := ℝ) (e := y t) fun ν => hG3 x μ ν
    exact h
  have hGy : ContDiffAt ℝ 1 ((fun y : State N => lawAccel B y.1 y.2) ∘ y) t :=
    (hG.contDiffAt (n := 1)).comp t hy.contDiffAt
  have h2 : ContDiffAt ℝ 1 (W.path 2) t := (LawWord.contDiff_path ht hm (le_refl 2)).contDiffAt
  have e : W.residual B = fun τ => W.path 2 τ - ((fun y : State N => lawAccel B y.1 y.2) ∘ y) τ :=
    rfl
  rw [e]
  exact h2.sub hGy

theorem lawCost_Xnorm_zero (r : ℕ) : Xnorm r (0 : Grid N → MetricRec) 0 = 0 := by
  have : Xsq r (0 : Grid N → MetricRec) 0 = 0 := by
    unfold Xsq
    refine sum_eq_zero fun κ _ => ?_
    have e : cx (comp (0 : Grid N → MetricRec) κ.1.1 κ.1.2) = 0 := by funext x; simp [comp, cx]
    rw [e]
    simp [PeriodicGridSobolev.sobSq, PeriodicGridSobolev.gridNormSq]
  rw [Xnorm, this, Real.sqrt_zero]

theorem LawWord.guardTime_nonneg (W : LawWord N) (s : ℕ) (ρ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ W.guardTime s ρ T := by
  unfold LawWord.guardTime
  split_ifs with h
  · obtain ⟨t, ht, hρ⟩ := h
    exact le_csInf ⟨t, ht, hρ⟩ fun τ hτ => hτ.1.1
  · exact hT

theorem LawWord.costDensity_nonneg (W : LawWord N) (B : Upper → Upper → ℝ) (s : ℕ) (t : ℝ) :
    0 ≤ W.costDensity B s t :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

set_option maxHeartbeats 4000000 in
-- the proof assembles the energy, difference, Sobolev and guard arguments in one statement
/-- **`lem:supp-law-cost-control`: a stopped physical cost controls the whole word.**  Let
`s ≥ 5` (the manuscript takes `s ≥ 11`).  There are `ε₀, T₀ > 0` and a guard radius `ρ > 0`
(the common-energy margin), independent of the mesh, the mark and the word, such that for every
`T ∈ (0, T₀]` there is `C ≥ 0` with the following property.  Let `B = Bᵀ`, `‖B‖_op ≤ 1/48`, let
`W` be a chronological word on `[0, T]` at mesh `h = 1/N` whose initial record has
`‖(Q, Q')(0)‖_{X^s_h} ≤ ε ≤ ε₀`, and let `0 ≤ d ≤ 1/2` with stopped cost `C_h ≤ d²`.  Then

* no failure and no guard exit occur;
* `‖f‖_{L²_t H^s_h} + ‖∂_t f‖_{L²_t H^{s-3}_h} ≤ 2 ε d` (`eq:supp-law-cost-force`);
* the exact unforced `B`-history `(q_B, v_B)` with the same initial record exists (and is unique)
  on `[0, T₀]`, and for `t ∈ [0, T]`
  `‖(Q - q_B, Q' - q_B')(t)‖_{X^{s-1}_h} + ‖Q''(t) - q_B''(t)‖_{s-3,h} ≤ C ε d`
  (`eq:supp-law-cost-shadow`; `‖(·,·)‖_{X^{s-1}_h}` controls `‖Q - q_B‖_{s,h}` and
  `‖Q' - q_B'‖_{s-1,h}`, and `q_B'' = V_{B,h}(q_B, q_B')`). -/
theorem law_cost_control (s : ℕ) (hs : 5 ≤ s) :
    ∃ ε₀ > 0, ∃ T₀ > 0, ∃ ρ > 0, ∀ T, 0 < T → T ≤ T₀ → ∃ C ≥ 0,
      ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ), IsMark (1 / 48) B →
      ∀ (W : LawWord N) (cm cp : ℝ), W.IsChronological (N : ℝ)⁻¹ cm cp T →
      ∀ ε, 0 < ε → ε ≤ ε₀ → W.recNorm s 0 ≤ ε →
      ∀ d, 0 ≤ d → d ≤ 1 / 2 → W.cost B s ρ ε T ≤ d ^ 2 →
        W.fail = none ∧ (∀ t ∈ Icc 0 T, W.recNorm s t < ρ) ∧
        Real.sqrt (∫ t in (0)..T, Fnorm s (W.residual B t) ^ 2) +
          Real.sqrt (∫ t in (0)..T, Fnorm (s - 3) (deriv (W.residual B) t) ^ 2) ≤ 2 * ε * d ∧
        ∃ q v : ℝ → Grid N → MetricRec, q 0 = W.path 0 0 ∧ v 0 = W.path 1 0 ∧
          IsAccSolution (lawAccel B) T₀ q v ∧
          (∀ q' v' : ℝ → Grid N → MetricRec, q' 0 = W.path 0 0 → v' 0 = W.path 1 0 →
            IsAccSolution (lawAccel B) T₀ q' v' → ∀ t ∈ Icc 0 T₀, q' t = q t ∧ v' t = v t) ∧
          ∀ t ∈ Icc 0 T, Xnorm (s - 1) (W.path 0 t - q t) (W.path 1 t - v t) +
            Fnorm (s - 3) (W.path 2 t - lawAccel B (q t) (v t)) ≤ C * ε * d := by
  obtain ⟨δF, hδF, CF, hCF, hF⟩ := law_forced_energy s (by omega)
  obtain ⟨δ0, hδ0, K₁, hK₁, hpc⟩ := pointwise_chart s (by omega)
  obtain ⟨δD, hδD, KD, hKD, hD⟩ := law_difference s (s - 1) (by omega) (by omega)
  obtain ⟨δA, hδA, KA, hKA, hA⟩ := lawAccel_diff_bound s (s - 2) (by omega) (by omega)
  obtain ⟨εL, hεL, TL, hTL, CL, hCL, hL⟩ := law_lifespan s (by omega)
  obtain ⟨ρc, hρc, hres⟩ := residual_contDiffAt s (by omega)
  set ρ : ℝ := min (min δF δ0) (min (min δD δA) (min 1 (ρc / 2)))
  have hρ : 0 < ρ := by positivity
  have hρF : ρ ≤ δF := (min_le_left _ _).trans (min_le_left _ _)
  have hρ0 : ρ ≤ δ0 := (min_le_left _ _).trans (min_le_right _ _)
  have hρD : ρ ≤ δD := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hρA : ρ ≤ δA := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hρ1 : ρ ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρc' : ρ ≤ ρc / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set K : ℝ := 8 * CF
  have hK : 0 ≤ K := by positivity
  set A₀ : ℝ := 3 * Real.exp (K * TL) * (3 + K * (1 + TL) / 2)
  have hA₀9 : 9 ≤ A₀ := by
    have h1 : 1 ≤ Real.exp (K * TL) := Real.one_le_exp (by positivity)
    have h2 : 0 ≤ K * (1 + TL) / 2 := by positivity
    simp only [A₀]; nlinarith
  have hA₀ : 0 < A₀ := by linarith
  set ε₀ : ℝ := min εL (min (ρ / (CL + 1)) (ρ / (2 * A₀)))
  have hε₀ : 0 < ε₀ := by positivity
  refine ⟨ε₀, hε₀, TL, hTL, ρ, hρ, fun T hT hTT => ?_⟩
  set C1 : ℝ := 3 * Real.exp (KD * T) * KD * (1 + T) / 2
  have hC1 : 0 ≤ C1 := by positivity
  set C2 : ℝ := Real.sqrt (T⁻¹ + 1) + 1
  have hC2 : 0 ≤ C2 := by positivity
  refine ⟨C1 + 16 * (KA * C1 + C2), by positivity,
    fun N _ B hB W cm cp hW ε hε hεε hX0 d hd hd2 hcost => ?_⟩
  obtain ⟨hJ, hnode0, hnodeJ, ht, hdur, hm, hsym, hfailJ⟩ := hW
  have hεL' : ε ≤ εL := hεε.trans (min_le_left _ _)
  have hερ : ε ≤ ρ / (CL + 1) := hεε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεA : ε ≤ ρ / (2 * A₀) := hεε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hA₀ε : A₀ * ε ≤ ρ / 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * A₀)] at hεA
    linarith
  set φ : ℝ → ℝ := W.recNorm s
  have hφc : Continuous φ := LawWord.continuous_recNorm ht hm s
  have hφ0 : φ 0 ≤ ρ / 2 := by
    have : ε ≤ A₀ * ε := by nlinarith
    exact hX0.trans (this.trans hA₀ε)
  set f : ℝ → Grid N → MetricRec := W.residual B
  have hsym0 : ∀ τ, IsSymRec (W.path 0 τ) := LawWord.isSymRec_path W hsym 0
  have hsym1 : ∀ τ, IsSymRec (W.path 1 τ) := LawWord.isSymRec_path W hsym 1
  -- regularity on the open set `U = {φ < 2ρ}`
  set U : Set ℝ := {τ | φ τ < 2 * ρ}
  have hUo : IsOpen U := isOpen_lt hφc continuous_const
  have hreg : ∀ τ ∈ U, ContDiffAt ℝ 1 f τ := fun τ hτ =>
    hres N B W ht hm hsym τ (lt_of_lt_of_le hτ (by linarith))
  have hfU : ContDiffOn ℝ 1 f U := fun τ hτ => (hreg τ hτ).contDiffWithinAt
  have hf'c : ContinuousOn (deriv f) U := hfU.continuousOn_deriv_of_isOpen hUo le_rfl
  have hfc : ContinuousOn f U := hfU.continuousOn
  have hfd : ∀ τ ∈ U, HasDerivAt f (deriv f τ) τ := fun τ hτ =>
    ((hreg τ hτ).differentiableAt (by norm_num)).hasDerivAt
  -- the forced law history
  have hq : ∀ τ x, HasDerivAt (fun σ => W.path 0 σ x) (W.path 1 τ x) τ := fun τ x =>
    hasDerivAt_pi.1 (LawWord.hasDerivAt_path ht hm (k := 0) (by norm_num) τ) x
  have hv : ∀ τ x (κ : Upper), HasDerivAt (fun σ => W.path 1 σ x κ.1.1 κ.1.2)
      (lawAccel B (W.path 0 τ) (W.path 1 τ) x κ.1.1 κ.1.2 + f τ x κ.1.1 κ.1.2) τ := by
    intro τ x κ
    have h := hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_pi.1
      (LawWord.hasDerivAt_path ht hm (k := 1) (by norm_num) τ) x) κ.1.1) κ.1.2
    refine h.congr_deriv ?_
    simp only [f, LawWord.residual, Pi.sub_apply]
    ring
  -- continuity of the cost densities on sub-intervals of `U`
  have hcont : ∀ τ₁ : ℝ, (∀ τ ∈ Set.Icc 0 τ₁, φ τ < 2 * ρ) →
      ContinuousOn (fun τ => Fnorm s (f τ)) (Set.Icc 0 τ₁) ∧
      ContinuousOn (fun τ => Fnorm (s - 3) (deriv f τ)) (Set.Icc 0 τ₁) := by
    intro τ₁ hU
    have hsub : Set.Icc 0 τ₁ ⊆ U := fun τ hτ => hU τ hτ
    exact ⟨(continuous_Fnorm s).comp_continuousOn (hfc.mono hsub),
      (continuous_Fnorm (s - 3)).comp_continuousOn (hf'c.mono hsub)⟩
  -- the energy step: no exit before `τ₁`
  have key : ∀ τ₁ ∈ Icc 0 T, (∀ τ ∈ Icc 0 τ₁, φ τ < 2 * ρ) →
      (∫ τ in (0)..τ₁, Fnorm s (f τ) ^ 2) ≤ (ε * d) ^ 2 → ∀ t ∈ Icc 0 τ₁, φ t ≤ ρ / 2 := by
    intro τ₁ hτ₁ hU hI
    obtain ⟨hgc, -⟩ := hcont τ₁ hU
    have hg2i : IntervalIntegrable (fun τ => Fnorm s (f τ) ^ 2) volume 0 τ₁ :=
      (hgc.pow 2).intervalIntegrable_of_Icc hτ₁.1
    refine ODECutoff.firstExit_le hφc.continuousOn (show ρ / 2 < ρ by linarith) hφ0 ?_
    intro t htt hle
    set E : ℝ → ℝ := fun τ => lawEnergy B s (W.path 0 τ) (W.path 1 τ)
    have hstep : ∀ τ ∈ Icc 0 t, ∃ e', HasDerivAt E e' τ ∧
        e' ≤ K * E τ + K * Real.sqrt (E τ) * Fnorm s (f τ) := by
      intro τ hτ
      have hφτ : φ τ ≤ ρ := hle τ hτ
      obtain ⟨r, hr, hlow, hrb, -⟩ := hF N B (W.path 0) (W.path 1) f τ hB (hsym0 τ) (hsym1 τ)
        (hq τ) (hv τ) (hφτ.trans hρF)
      obtain ⟨ha, hc, -⟩ := hpc N (W.path 0 τ) (W.path 1 τ) (hsym0 τ) (hsym1 τ)
        (hφτ.trans hρ0)
      have hup := (lawEnergy_bounds s hB le_rfl (W.path 0 τ) (W.path 1 τ) ha hc).2
      have hXsq : Xsq s (W.path 0 τ) (W.path 1 τ) = φ τ ^ 2 := (Xnorm_sq _ _ _).symm
      have hφ0' : 0 ≤ φ τ := Xnorm_nonneg _ _ _
      have hE0 : 0 ≤ E τ := le_trans (by rw [hXsq]; positivity) hlow
      have hE9 : E τ ≤ 9 := by
        have : φ τ ^ 2 ≤ 1 := by nlinarith
        simp only [E]; rw [hXsq] at hup; linarith
      have hsE : Real.sqrt (E τ) ≤ 3 := by
        rw [show (3 : ℝ) = Real.sqrt 9 by
          rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt hE9
      have hss : Real.sqrt (E τ) * Real.sqrt (E τ) = E τ := Real.mul_self_sqrt hE0
      have hsE0 := Real.sqrt_nonneg (E τ)
      have hg0 := Fnorm_nonneg s (f τ)
      refine ⟨r, hr, ?_⟩
      have h1 : E τ * Real.sqrt (E τ) ≤ 3 * E τ := by nlinarith
      have h2 : 0 ≤ CF * (Real.sqrt (E τ) * Fnorm s (f τ)) := by positivity
      have hexp : 2 * Real.sqrt (E τ) * (CF * Real.sqrt (E τ) + CF * E τ + CF * Fnorm s (f τ)) =
          2 * CF * E τ + 2 * CF * (E τ * Real.sqrt (E τ)) +
            2 * CF * (Real.sqrt (E τ) * Fnorm s (f τ)) := by
        linear_combination (2 * CF) * hss
      have hrb' := hrb
      simp only [E] at hrb' ⊢
      rw [hexp] at hrb'
      have h3 : 2 * CF * (E τ * Real.sqrt (E τ)) ≤ 2 * CF * (3 * E τ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      simp only [E] at h3 h2
      simp only [K]
      nlinarith
    have hE0 : ∀ τ ∈ Icc 0 t, 0 ≤ E τ := by
      intro τ hτ
      obtain ⟨r, -, hlow, -⟩ := hF N B (W.path 0) (W.path 1) f τ hB (hsym0 τ) (hsym1 τ)
        (hq τ) (hv τ) ((hle τ hτ).trans hρF)
      exact le_trans (by have := Xsq_nonneg s (W.path 0 τ) (W.path 1 τ); linarith) hlow
    have htT : t ∈ Icc 0 τ₁ := htt
    have hgr := ODECutoff.sqrt_le_of_forced_deriv hK hstep hE0
      (hgc.mono (Icc_subset_Icc le_rfl htT.2)) (fun τ _ => Fnorm_nonneg _ _) t ⟨htT.1, le_rfl⟩
    -- the integral of the force
    have hIt : (∫ τ in (0)..t, Fnorm s (f τ) ^ 2) ≤ (ε * d) ^ 2 := by
      refine le_trans ?_ hI
      exact intervalIntegral.integral_mono_interval le_rfl htT.1 htT.2
        (ae_of_all _ fun τ => sq_nonneg _) hg2i
    have hint := TimeSobolev.integral_le_of_integral_sq_le htT.1
      (hgc.mono (Icc_subset_Icc le_rfl htT.2)) (by positivity) hIt
    -- the energy at the initial and final times
    have h0mem : (0 : ℝ) ∈ Icc 0 t := ⟨le_rfl, htT.1⟩
    have hE0b : Real.sqrt (E 0) ≤ 3 * φ 0 := by
      obtain ⟨ha, hc, -⟩ := hpc N (W.path 0 0) (W.path 1 0) (hsym0 0) (hsym1 0)
        ((hle 0 h0mem).trans hρ0)
      have hup := (lawEnergy_bounds s hB le_rfl (W.path 0 0) (W.path 1 0) ha hc).2
      have hXsq : Xsq s (W.path 0 0) (W.path 1 0) = φ 0 ^ 2 := (Xnorm_sq _ _ _).symm
      have hφ0' : 0 ≤ φ 0 := Xnorm_nonneg _ _ _
      rw [Real.sqrt_le_left (by positivity)]
      simp only [E]; rw [hXsq] at hup; nlinarith
    have hφt : φ t ≤ 3 * Real.sqrt (E t) := by
      have htm : t ∈ Icc 0 t := ⟨htT.1, le_rfl⟩
      obtain ⟨r, -, hlow, -⟩ := hF N B (W.path 0) (W.path 1) f t hB (hsym0 t) (hsym1 t)
        (hq t) (hv t) ((hle t htm).trans hρF)
      have hXsq : Xsq s (W.path 0 t) (W.path 1 t) = φ t ^ 2 := (Xnorm_sq _ _ _).symm
      rw [hXsq] at hlow
      have hEt := hE0 t htm
      have hs3 : (3 * Real.sqrt (E t)) ^ 2 = 9 * E t := by
        rw [mul_pow, Real.sq_sqrt hEt]; norm_num
      have hφ0' : 0 ≤ φ t := Xnorm_nonneg _ _ _
      nlinarith [Real.sqrt_nonneg (E t)]
    have htTL : t ≤ TL := htT.2.trans (hτ₁.2.trans hTT)
    have hexp : Real.exp (K * t) ≤ Real.exp (K * TL) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htTL hK)
    have hεd : ε * d * (1 + t) / 2 ≤ ε * (1 + TL) / 2 := by
      have : d * (1 + t) ≤ 1 * (1 + TL) := mul_le_mul (by linarith) (by linarith)
        (by linarith [htT.1]) (by norm_num)
      nlinarith
    have hint0 : 0 ≤ ∫ τ in (0)..t, Fnorm s (f τ) :=
      intervalIntegral.integral_nonneg htT.1 fun τ _ => Fnorm_nonneg _ _
    calc φ t ≤ 3 * Real.sqrt (E t) := hφt
      _ ≤ 3 * (Real.exp (K * t) * (Real.sqrt (E 0) + K * ∫ τ in (0)..t, Fnorm s (f τ))) := by
          gcongr
      _ ≤ 3 * (Real.exp (K * TL) * (3 * ε + K * (ε * (1 + TL) / 2))) := by
          gcongr
          · exact hE0b.trans (by linarith [hX0])
          · exact hint.trans hεd
      _ = A₀ * ε := by simp only [A₀]; ring
      _ ≤ ρ / 2 := hA₀ε
  -- the cost: no failure
  have hstop0 : ∀ j, W.fail = some j → 0 ≤ W.stopTime s ρ T := by
    intro j hj
    simp only [LawWord.stopTime, hj]
    refine le_min (W.guardTime_nonneg s ρ hT.le) ?_
    rw [← hnode0]; exact ht.monotone (Nat.zero_le j)
  have hfail : W.fail = none := by
    rcases hW' : W.fail with _ | j
    · rfl
    · exfalso
      have hc := hcost
      simp only [LawWord.cost, hW', Option.isSome_some, ite_true] at hc
      have hI0 : 0 ≤ ∫ t in (0)..(W.stopTime s ρ T), W.costDensity B s t :=
        intervalIntegral.integral_nonneg (hstop0 j hW') fun t _ => W.costDensity_nonneg B s t
      have : 0 ≤ (ε ^ 2)⁻¹ * ∫ t in (0)..(W.stopTime s ρ T), W.costDensity B s t := by positivity
      nlinarith
  have hcostG : (∫ t in (0)..(W.guardTime s ρ T), W.costDensity B s t) ≤ (ε * d) ^ 2 := by
    have hc := hcost
    simp only [LawWord.cost, LawWord.stopTime, hfail, Option.isSome_none] at hc
    simp only [Bool.false_eq_true, ite_false, add_zero] at hc
    rw [inv_mul_le_iff₀ (by positivity)] at hc
    linarith
  -- integral comparisons on sub-intervals of `U`
  have hsplit : ∀ τ₁ : ℝ, 0 ≤ τ₁ → (∀ τ ∈ Set.Icc 0 τ₁, φ τ < 2 * ρ) →
      (∫ t in (0)..τ₁, W.costDensity B s t) =
        (∫ t in (0)..τ₁, Fnorm s (f t) ^ 2) + ∫ t in (0)..τ₁, Fnorm (s - 3) (deriv f t) ^ 2 := by
    intro τ₁ hτ₁ hU
    obtain ⟨h1, h2⟩ := hcont τ₁ hU
    exact intervalIntegral.integral_add ((h1.pow 2).intervalIntegrable_of_Icc hτ₁)
      ((h2.pow 2).intervalIntegrable_of_Icc hτ₁)
  have hnonneg : ∀ τ₁ : ℝ, 0 ≤ τ₁ → 0 ≤ (∫ t in (0)..τ₁, Fnorm s (f t) ^ 2) ∧
      0 ≤ ∫ t in (0)..τ₁, Fnorm (s - 3) (deriv f t) ^ 2 := fun τ₁ hτ₁ =>
    ⟨intervalIntegral.integral_nonneg hτ₁ fun _ _ => sq_nonneg _,
      intervalIntegral.integral_nonneg hτ₁ fun _ _ => sq_nonneg _⟩
  -- no guard exit
  have hnoexit : ∀ t ∈ Icc 0 T, φ t < ρ := by
    by_contra hex
    push Not at hex
    have hex' : ∃ t ∈ Icc 0 T, ρ ≤ W.recNorm s t := hex
    set S : Set ℝ := {t | t ∈ Icc 0 T ∧ ρ ≤ W.recNorm s t}
    have hSne : S.Nonempty := by obtain ⟨t, ht, h⟩ := hex'; exact ⟨t, ht, h⟩
    have hScl : IsClosed S := isClosed_Icc.inter (isClosed_le continuous_const hφc)
    have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
    have hG : W.guardTime s ρ T = sInf S := by
      rw [LawWord.guardTime, if_pos hex']
    set τg := sInf S
    have hτgS : τg ∈ S := hScl.csInf_mem hSne hSbdd
    have hbefore : ∀ τ ∈ Ico 0 τg, φ τ < ρ := by
      intro τ hτ
      by_contra h
      push Not at h
      have : τ ∈ S := ⟨⟨hτ.1, hτ.2.le.trans hτgS.1.2⟩, h⟩
      exact absurd (csInf_le hSbdd this) (not_le.mpr hτ.2)
    have hτgpos : 0 < τg := by
      rcases hτgS.1.1.lt_or_eq with h | h
      · exact h
      · exfalso
        have h2 : ρ ≤ φ τg := hτgS.2
        rw [← h] at h2
        linarith
    have hτgle : φ τg ≤ ρ := by
      have hlim : Tendsto φ (𝓝[<] τg) (𝓝 (φ τg)) :=
        hφc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      refine le_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsLT hτgpos] with τ hτ
      exact (hbefore τ ⟨hτ.1.le, hτ.2⟩).le
    have hU : ∀ τ ∈ Icc 0 τg, φ τ < 2 * ρ := by
      intro τ hτ
      rcases hτ.2.lt_or_eq with h | h
      · linarith [hbefore τ ⟨hτ.1, h⟩]
      · rw [h]; linarith
    have hI : (∫ τ in (0)..τg, Fnorm s (f τ) ^ 2) ≤ (ε * d) ^ 2 := by
      have := hsplit τg hτgS.1.1 hU
      have h2 := (hnonneg τg hτgS.1.1).2
      rw [hG] at hcostG
      linarith
    have := key τg hτgS.1 hU hI τg ⟨hτgS.1.1, le_rfl⟩
    have h2 : ρ ≤ φ τg := hτgS.2
    linarith
  have hGT : W.guardTime s ρ T = T := by
    have : ¬∃ t ∈ Icc 0 T, ρ ≤ W.recNorm s t := by
      push Not
      exact hnoexit
    simp only [LawWord.guardTime, if_neg this]
  rw [hGT] at hcostG
  have hUT : ∀ τ ∈ Icc 0 T, φ τ < 2 * ρ := fun τ hτ => by linarith [hnoexit τ hτ]
  have hsplitT := hsplit T hT.le hUT
  obtain ⟨hn1, hn2⟩ := hnonneg T hT.le
  have hI1 : (∫ t in (0)..T, Fnorm s (f t) ^ 2) ≤ (ε * d) ^ 2 := by linarith
  have hI2 : (∫ t in (0)..T, Fnorm (s - 3) (deriv f t) ^ 2) ≤ (ε * d) ^ 2 := by linarith
  have hεd0 : 0 ≤ ε * d := by positivity
  have hsq1 : Real.sqrt (∫ t in (0)..T, Fnorm s (f t) ^ 2) ≤ ε * d := by
    rw [Real.sqrt_le_left hεd0]; exact hI1
  have hsq2 : Real.sqrt (∫ t in (0)..T, Fnorm (s - 3) (deriv f t) ^ 2) ≤ ε * d := by
    rw [Real.sqrt_le_left hεd0]; exact hI2
  obtain ⟨hgcT, hbcT⟩ := hcont T hUT
  -- the exact unforced history
  obtain ⟨⟨q, v, hq0, hv0, hsol, hbd⟩, huniq⟩ := hL N B hB (W.path 0 0) (W.path 1 0) (hsym0 0)
    (hsym1 0) (hX0.trans hεL')
  have hqρ : ∀ t ∈ Icc 0 TL, Xnorm s (q t) (v t) ≤ ρ := by
    intro t ht'
    refine (hbd t ht').trans ?_
    have h1 : CL * Xnorm s (W.path 0 0) (W.path 1 0) ≤ CL * ε := mul_le_mul_of_nonneg_left hX0 hCL
    have h2 : CL * ε ≤ ρ := by
      rw [le_div_iff₀ (by positivity)] at hερ
      nlinarith
    linarith
  refine ⟨hfail, hnoexit, by linarith, q, v, hq0, hv0, hsol,
    fun q' v' hq' hv' hsol' t ht' => huniq q' v' q v hq' hv' hq0 hv0 hsol' hsol t ht', ?_⟩
  -- the shadow estimate
  intro t ht'
  have htTL : ∀ τ ∈ Icc 0 T, τ ∈ Icc 0 TL := fun τ hτ => ⟨hτ.1, hτ.2.trans hTT⟩
  have hpair : IsLawForcedPair B s δD T (W.path 0) q (W.path 1) v f (fun _ => 0) := by
    intro τ hτ
    obtain ⟨hqs, hvs, hqd, hvd⟩ := hsol τ (htTL τ hτ)
    refine ⟨hsym0 τ, hsym1 τ, hqs, hvs, hq τ, hqd, hv τ, fun x κ => ?_,
      ((hnoexit τ hτ).le.trans hρD), (hqρ τ (htTL τ hτ)).trans hρD⟩
    refine (hvd x κ).congr_deriv ?_
    simp
  have hfcT : ContinuousOn f (Icc 0 T) := hfc.mono fun τ hτ => hUT τ hτ
  have hdiff := hD N B T (W.path 0) q (W.path 1) v f (fun _ => 0) hB hpair hfcT
    continuousOn_const t ht'
  have hinit : Xnorm (s - 1) (W.path 0 0 - q 0) (W.path 1 0 - v 0) = 0 := by
    rw [hq0, hv0, sub_self, sub_self, lawCost_Xnorm_zero]
  -- the integral of the force on `[0, t]`
  have hIt : (∫ τ in (0)..t, Fnorm s (f τ) ^ 2) ≤ (ε * d) ^ 2 := by
    refine le_trans ?_ hI1
    exact intervalIntegral.integral_mono_interval le_rfl ht'.1 ht'.2
      (ae_of_all _ fun τ => sq_nonneg _) ((hgcT.pow 2).intervalIntegrable_of_Icc hT.le)
  have hint := TimeSobolev.integral_le_of_integral_sq_le ht'.1
    (hgcT.mono (Icc_subset_Icc le_rfl ht'.2)) hεd0 hIt
  have hint' : (∫ τ in (0)..t, Fnorm (s - 1) (f τ - (fun _ => (0 : Grid N → MetricRec)) τ)) ≤
      ∫ τ in (0)..t, Fnorm s (f τ) := by
    refine intervalIntegral.integral_mono_on ht'.1 ?_ ?_ fun τ _ => ?_
    · refine ContinuousOn.intervalIntegrable_of_Icc ht'.1 ?_
      have : (fun τ => Fnorm (s - 1) (f τ - (fun _ => (0 : Grid N → MetricRec)) τ)) =
          fun τ => Fnorm (s - 1) (f τ) := by funext τ; simp
      rw [this]
      exact (continuous_Fnorm (s - 1)).comp_continuousOn
        (hfc.mono fun τ hτ => hUT τ ⟨hτ.1, hτ.2.trans ht'.2⟩)
    · exact (hgcT.mono (Icc_subset_Icc le_rfl ht'.2)).intervalIntegrable_of_Icc ht'.1
    · simp only [sub_zero]; exact lawDiff_Fnorm_mono (by omega) _
  have hX1 : Xnorm (s - 1) (W.path 0 t - q t) (W.path 1 t - v t) ≤ C1 * ε * d := by
    rw [hinit, mul_zero, zero_add] at hdiff
    refine hdiff.trans ?_
    have hexp : Real.exp (KD * t) ≤ Real.exp (KD * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht'.2 hKD)
    have h3 : ε * d * (1 + t) / 2 ≤ ε * d * (1 + T) / 2 := by
      have := mul_le_mul_of_nonneg_left (show 1 + t ≤ 1 + T by linarith [ht'.2]) hεd0
      linarith
    have h4 : (∫ τ in (0)..t, Fnorm (s - 1) (f τ - (fun _ => (0 : Grid N → MetricRec)) τ)) ≤
        ε * d * (1 + T) / 2 := hint'.trans (hint.trans h3)
    calc 3 * Real.exp (KD * t) * (KD * ∫ τ in (0)..t,
          Fnorm (s - 1) (f τ - (fun _ => (0 : Grid N → MetricRec)) τ)) ≤
          3 * Real.exp (KD * T) * (KD * (ε * d * (1 + T) / 2)) := by
          have hI0 : 0 ≤ ∫ τ in (0)..t,
              Fnorm (s - 1) (f τ - (fun _ => (0 : Grid N → MetricRec)) τ) :=
            intervalIntegral.integral_nonneg ht'.1 fun τ _ => Fnorm_nonneg _ _
          have := mul_nonneg hKD hI0
          gcongr
      _ = C1 * ε * d := by simp only [C1]; ring
  -- the pointwise force bound (one-dimensional Sobolev in time)
  have hsob := TimeSobolev.sqrt_sup_le_of_abs_deriv_le hT
    (φ := fun τ => Fnorm (s - 3) (f τ) ^ 2)
    (φ' := fun τ => 2 * lawCostInner (s - 3) (f τ) (deriv f τ))
    (b := fun τ => Fnorm (s - 3) (deriv f τ))
    (fun τ hτ => (lawCost_hasDerivAt_Fnorm_sq (s - 3) (hfd τ (hUT τ hτ))).1)
    (fun τ _ => sq_nonneg _)
    (fun τ hτ => (lawCost_hasDerivAt_Fnorm_sq (s - 3) (hfd τ (hUT τ hτ))).2) hbcT t ht'
  have hI3 : (∫ τ in (0)..T, Fnorm (s - 3) (f τ) ^ 2) ≤ (ε * d) ^ 2 := by
    refine le_trans ?_ hI1
    refine intervalIntegral.integral_mono_on hT.le ?_ ?_ fun τ _ => ?_
    · exact (((continuous_Fnorm (s - 3)).comp_continuousOn hfcT).pow 2).intervalIntegrable_of_Icc
        hT.le
    · exact (hgcT.pow 2).intervalIntegrable_of_Icc hT.le
    · exact pow_le_pow_left₀ (Fnorm_nonneg _ _) (lawDiff_Fnorm_mono (by omega) _) 2
  have hft : Fnorm (s - 3) (f t) ≤ C2 * (ε * d) := by
    rw [Real.sqrt_sq (Fnorm_nonneg _ _)] at hsob
    refine hsob.trans ?_
    have h1 : Real.sqrt (∫ τ in (0)..T, Fnorm (s - 3) (f τ) ^ 2) ≤ ε * d := by
      rw [Real.sqrt_le_left hεd0]; exact hI3
    have h2 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (T⁻¹ + 1))
    simp only [C2]
    linarith
  -- the acceleration difference
  have hacc : Fnorm (s - 3) (W.path 2 t - lawAccel B (q t) (v t)) ≤
      16 * (KA * (C1 * ε * d) + C2 * (ε * d)) := by
    have hM : 0 ≤ KA * (C1 * ε * d) + C2 * (ε * d) := by positivity
    refine lawDiff_Fnorm_le_of_comp_le (s - 3) _ hM fun κ => ?_
    have e : W.path 2 t - lawAccel B (q t) (v t) =
        (lawAccel B (W.path 0 t) (W.path 1 t) - lawAccel B (q t) (v t)) + f t := by
      simp only [f, LawWord.residual]; abel
    rw [e, cx_comp_add]
    refine (PeriodicGridSobolev.Moser.sobNorm_add_le _ _ _).trans (add_le_add ?_ ?_)
    · obtain ⟨hqs, hvs, -, -⟩ := hsol t (htTL t ht')
      have h1 := hA N B (W.path 0 t) (q t) (W.path 1 t) (v t) hB (hsym0 t) hqs (hsym1 t) hvs
        ((hnoexit t ht').le.trans hρA) ((hqρ t (htTL t ht')).trans hρA) κ
      rw [show s - 2 - 1 = s - 3 by omega] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hKA)
      exact (lawDiff_Xnorm_mono (by omega) _ _).trans hX1
    · exact (sobNorm_le_Fnorm _ _ κ).trans hft
  calc Xnorm (s - 1) (W.path 0 t - q t) (W.path 1 t - v t) +
        Fnorm (s - 3) (W.path 2 t - lawAccel B (q t) (v t)) ≤
        C1 * ε * d + 16 * (KA * (C1 * ε * d) + C2 * (ε * d)) := add_le_add hX1 hacc
    _ = (C1 + 16 * (KA * C1 + C2)) * ε * d := by ring

/-! ### Non-vacuity -/

theorem lawWord_lawAccel_zero (B : Upper → Upper → ℝ) :
    lawAccel B (0 : Grid N → MetricRec) 0 = 0 := by
  have hb : bTerm B (0 : Grid N → MetricRec) = 0 := by
    have hl : lapR (lapR (0 : Grid N → ℝ)) = 0 := by
      rw [show (0 : Grid N → ℝ) = (0 : ℝ) • (0 : Grid N → ℝ) by simp, lapR_smul, lapR_smul]
      simp
    funext x μ ν
    have e : ∀ l : Upper, comp (0 : Grid N → MetricRec) l.1.1 l.1.2 = 0 := fun l => by
      funext y; rfl
    simp [bTerm, e, hl]
  funext x μ ν
  simp only [lawAccel, lawForce, hb, Pi.add_apply, Pi.zero_apply, mul_zero, neg_zero, add_zero]
  rw [harmonicWriterAcceleration_zero]
  rfl

theorem isMark_zero_lawWord : IsMark (1 / 48) (fun _ _ : Upper => (0 : ℝ)) :=
  ⟨fun _ _ => rfl, fun ξ η => by simp only [mul_zero, zero_mul, sum_const_zero, abs_zero]; positivity⟩

/-- The one-letter flat word on `[0, T]`: a single cell, the zero polynomial letter, no failure. -/
def LawWord.flat (N : ℕ) (T : ℝ) : LawWord N where
  J := 1
  deg := 0
  node := fun j => (j : ℝ) * T
  letter := fun _ _ => 0
  fail := none

theorem LawWord.flat_path (T : ℝ) (k : ℕ) (t : ℝ) : (LawWord.flat N T).path k t = 0 := by
  simp [LawWord.path, SplineGluing.splinePath, TwoPointHermite.polyCurveDeriv, LawWord.flat]

theorem LawWord.flat_isChronological {T : ℝ} (hT : 0 < T) :
    (LawWord.flat N T).IsChronological (N : ℝ)⁻¹ 0 (T * (N : ℝ) ^ 2) T := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  refine ⟨by simp [LawWord.flat], by simp [LawWord.flat], by simp [LawWord.flat], ?_, ?_, ?_, ?_, ?_⟩
  · exact strictMono_nat_of_lt_succ fun n => by
      simp only [LawWord.flat]; push_cast; nlinarith
  · intro j hj
    have hj0 : j = 0 := by simp [LawWord.flat] at hj; omega
    subst hj0
    simp only [LawWord.flat]
    push_cast
    constructor
    · nlinarith
    · field_simp; linarith
  · intro j hj
    simp [LawWord.flat] at hj
  · intro j i x μ ν; rfl
  · intro j hj; simp [LawWord.flat] at hj

theorem LawWord.flat_cost (B : Upper → Upper → ℝ) (s : ℕ) (ρ ε T : ℝ) :
    (LawWord.flat N T).cost B s ρ ε T = 0 := by
  have hres : (LawWord.flat N T).residual B = fun _ => 0 := by
    funext t
    simp only [LawWord.residual, LawWord.flat_path, lawWord_lawAccel_zero, sub_zero]
  have hdens : ∀ t, (LawWord.flat N T).costDensity B s t = 0 := by
    intro t
    simp only [LawWord.costDensity, hres, deriv_const', lawDiff_Fnorm_zero]
    norm_num
  simp only [LawWord.cost, hdens, intervalIntegral.integral_zero, mul_zero, zero_add]
  simp [LawWord.flat]

/-- Non-vacuity of `law_cost_control`: the flat one-letter word with the zero mark, initial
record `0`, cost `0` and `d = 0` satisfies all its hypotheses on `[0, T₀]` for every mesh. -/
example (s : ℕ) (hs : 5 ≤ s) : True := by
  obtain ⟨ε₀, hε₀, T₀, hT₀, ρ, hρ, h⟩ := law_cost_control s hs
  obtain ⟨C, hC, h2⟩ := h T₀ hT₀ le_rfl
  have hX : (LawWord.flat 5 T₀).recNorm s 0 ≤ ε₀ := by
    simp only [LawWord.recNorm, LawWord.flat_path, lawCost_Xnorm_zero]; exact hε₀.le
  have := h2 5 (fun _ _ => 0) isMark_zero_lawWord (LawWord.flat 5 T₀) 0 (T₀ * (5 : ℝ) ^ 2)
    (by exact_mod_cast LawWord.flat_isChronological (N := 5) hT₀) ε₀ hε₀ le_rfl hX 0 le_rfl
    (by norm_num) (by rw [LawWord.flat_cost]; norm_num)
  trivial

end

end RenewalGeometry.OpenWriterLifespan
