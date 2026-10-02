/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterContinuumLimit
import RenewalGeometry.Gravity.HarmonicGaugePropagation

/-!
# Third-order regularity of the limit of the open writer and its vacuum clause
  (`thm:supp-open-einstein`, `eq:supp-open-vacuum`; emergent-spacetime manuscript)

* `derivRec u α` — the classical spatial derivative `∂^α` of the real trigonometric interpolant
  `𝓘_h u` (spectral derivatives on the grid); `derivRec_cauchy` (one Sobolev order per derivative),
  `derivRec_comm` (derivatives commute), `hasDerivAt_derivRec_time` (time derivatives commute with
  interpolation and spectral differentiation).
-/

open Finset Filter Topology UnitAddTorus ComplexConjugate
open scoped BigOperators Real

namespace RenewalGeometry.OpenWriterLimitRegularity

open TorusSobolevTransfer OpenWriterLifespan OpenWriterEnergyEstimate OpenWriterChart
  OpenWriterEnergy OpenWriterGridBridge RootParityConnector PeriodicGridSobolev.Composition
  HarmonicWriter OpenWriterContinuum

noncomputable section

set_option linter.unusedSectionVars false

attribute [local irreducible] harmonicSource harmA harmB harmC

/-! ### Spectral derivatives of interpolants -/

section Deriv

variable {N : ℕ} [NeZero N]

/-- Iterated spectral derivative `∂^α` of a complex grid function. -/
def specDL (α : List (Fin 3)) (w : Grid N → ℂ) : Grid N → ℂ := α.foldr (fun i w => PeriodicGridSobolev.Sampling.specD i w) w

@[simp] theorem specDL_nil (w : Grid N → ℂ) : specDL [] w = w := rfl
@[simp] theorem specDL_cons (i : Fin 3) (α : List (Fin 3)) (w : Grid N → ℂ) :
    specDL (i :: α) w = PeriodicGridSobolev.Sampling.specD i (specDL α w) := rfl

/-- **Spectral derivatives commute.** -/
theorem specD_comm (i j : Fin 3) (w : Grid N → ℂ) :
    PeriodicGridSobolev.Sampling.specD i (PeriodicGridSobolev.Sampling.specD j w) =
      PeriodicGridSobolev.Sampling.specD j (PeriodicGridSobolev.Sampling.specD i w) := by
  funext x
  simp only [PeriodicGridSobolev.Sampling.specD, PeriodicGridSobolev.Sampling.dft_specD]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The classical derivative `∂^α 𝓘_h u` of the real interpolant of a grid record. -/
def derivRec (u : Grid N → MetricRec) (α : List (Fin 3)) : C(T3, MetricRec) :=
  reField fun μ ν => specDL α (cx (comp u μ ν))

theorem derivRec_nil (u : Grid N → MetricRec) : derivRec u [] = interpRec u := rfl

theorem isLineDeriv_derivRec (u : Grid N → MetricRec) (i : Fin 3) (α : List (Fin 3)) :
    IsLineDeriv i ⇑(derivRec u α) ⇑(derivRec u (i :: α)) :=
  isLineDeriv_reField i _

theorem derivRec_comm (u : Grid N → MetricRec) (i j : Fin 3) (α : List (Fin 3)) :
    derivRec u (i :: j :: α) = derivRec u (j :: i :: α) := by
  simp only [derivRec, specDL_cons, specD_comm]

theorem derivRec_symm {u : Grid N → MetricRec} (hu : IsSymRec u) (α : List (Fin 3)) (y : T3)
    (μ ν : Fin 4) : derivRec u α y μ ν = derivRec u α y ν μ := by
  have e : comp u μ ν = comp u ν μ := funext fun x => hu x μ ν
  simp only [derivRec, reField_apply, e]

/-- One Sobolev order per spectral derivative. -/
theorem derivRec_cauchy {M M' : ℕ} [NeZero M] [NeZero M'] (u : Grid M → MetricRec)
    (u' : Grid M' → MetricRec) (κ : Upper) :
    ∀ (α : List (Fin 3)) (r : ℕ),
      MemH (r + α.length) ⇑(cmp (derivRec u []) κ.1.1 κ.1.2 - cmp (derivRec u' []) κ.1.1 κ.1.2) →
      MemH r ⇑(cmp (derivRec u α) κ.1.1 κ.1.2 - cmp (derivRec u' α) κ.1.1 κ.1.2) ∧
      sn r ⇑(cmp (derivRec u α) κ.1.1 κ.1.2 - cmp (derivRec u' α) κ.1.1 κ.1.2) ≤
        sn (r + α.length) ⇑(cmp (derivRec u []) κ.1.1 κ.1.2 - cmp (derivRec u' []) κ.1.1 κ.1.2)
  | [], r, h => ⟨h, le_rfl⟩
  | i :: α, r, h => by
    have ih := derivRec_cauchy u u' κ α (r + 1) (by
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using h)
    have hd := deriv_cauchy (r := r) u u' i κ (w := fun μ ν => specDL α (cx (comp u μ ν)))
      (w' := fun μ ν => specDL α (cx (comp u' μ ν))) ih.1
    refine ⟨hd.1, hd.2.trans (ih.2.trans (le_of_eq ?_))⟩
    simp only [List.length_cons, Nat.add_assoc, Nat.add_comm 1]

/-- Time derivatives commute with spectral differentiation. -/
theorem hasDerivAt_specD {w : ℝ → Grid N → ℂ} {w' : Grid N → ℂ} {t : ℝ}
    (hw : ∀ z, HasDerivAt (fun τ => w τ z) (w' z) t) (i : Fin 3) (x : Grid N) :
    HasDerivAt (fun τ => PeriodicGridSobolev.Sampling.specD i (w τ) x)
      (PeriodicGridSobolev.Sampling.specD i w' x) t := by
  simp only [PeriodicGridSobolev.Sampling.specD, LatticeTorusPlancherel.dft, smul_eq_mul]
  refine HasDerivAt.fun_sum fun k _ => ?_
  refine HasDerivAt.const_mul _ (HasDerivAt.const_mul _ (HasDerivAt.const_mul _ ?_))
  exact HasDerivAt.fun_sum fun z _ => (hw z).const_mul _

theorem hasDerivAt_specDL {w : ℝ → Grid N → ℂ} {w' : Grid N → ℂ} {t : ℝ}
    (hw : ∀ z, HasDerivAt (fun τ => w τ z) (w' z) t) :
    ∀ (α : List (Fin 3)) (x : Grid N), HasDerivAt (fun τ => specDL α (w τ) x) (specDL α w' x) t
  | [], x => hw x
  | i :: α, x => hasDerivAt_specD (fun z => hasDerivAt_specDL hw α z) i x

/-- **Time derivatives commute with `∂^α 𝓘_h`.** -/
theorem hasDerivAt_derivRec_time {u : ℝ → Grid N → MetricRec} {u' : Grid N → MetricRec} {t : ℝ}
    (hu : ∀ x, HasDerivAt (fun τ => u τ x) (u' x) t) (α : List (Fin 3)) (y : T3) :
    HasDerivAt (fun τ => derivRec (u τ) α y) (derivRec u' α y) t := by
  refine hasDerivAt_reField_time (w := fun τ μ ν => specDL α (cx (comp (u τ) μ ν)))
    (fun μ ν x => ?_) y
  refine hasDerivAt_specDL (w := fun τ => cx (comp (u τ) μ ν)) (fun z => ?_) α x
  have h := hasDerivAt_pi.mp (hasDerivAt_pi.mp (hu z) μ) ν
  exact h.ofReal_comp

end Deriv


/-! ### Uniform limits of families of interpolant fields -/

section Family

/-- The pointwise-in-time limit of a family of record fields. -/
def limF (F : ℕ → ℝ → C(T3, MetricRec)) (t : ℝ) : C(T3, MetricRec) :=
  limUnder atTop fun n => F n t

variable {T c : ℝ} {F : ℕ → ℝ → C(T3, MetricRec)}

/-- The Cauchy-rate hypothesis of a family on `[0, T]` at Sobolev order `r`. -/
def FamRate (F : ℕ → ℝ → C(T3, MetricRec)) (T c : ℝ) (r : ℕ) : Prop :=
  (∀ t ∈ Set.Icc 0 T, ∀ n y μ ν, F n t y μ ν = F n t y ν μ) ∧
  ∀ t ∈ Set.Icc 0 T, ∀ n m (κ : Upper),
    MemH r ⇑(cmp (F n t) κ.1.1 κ.1.2 - cmp (F m t) κ.1.1 κ.1.2) ∧
    sn r ⇑(cmp (F n t) κ.1.1 κ.1.2 - cmp (F m t) κ.1.1 κ.1.2) ≤ c * (((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹)

theorem FamRate.limit {r : ℕ} (h : FamRate F T c r) (hr : 2 ≤ r) (hc : 0 ≤ c) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) :
    Tendsto (fun n => F n t) atTop (𝓝 (limF F t)) ∧ (∀ y μ ν, limF F t y μ ν = limF F t y ν μ) ∧
      ∀ n, ‖F n t - limF F t‖ ≤ Real.sqrt cEmb * (c * ((n : ℝ) + 1)⁻¹) := by
  obtain ⟨F₀, hF₀, hsym, hr0⟩ := exists_limit_of_rate (F := fun n => F n t) (h.1 t ht) r hr c hc
    (h.2 t ht)
  have e : limF F t = F₀ := tendsto_nhds_unique (tendsto_nhds_limUnder ⟨F₀, hF₀⟩) hF₀
  rw [e]
  refine ⟨hF₀, hsym, fun n => ?_⟩
  refine norm_sub_le_of_upper _ _ (h.1 t ht n) hsym fun κ => ?_
  exact ⟨memH_mono hr (hr0 n κ).1, (sn_mono' hr (hr0 n κ).1).trans (hr0 n κ).2⟩

theorem tendsto_bound_zero (B : ℝ) :
    Tendsto (fun n : ℕ => Real.sqrt cEmb * (B * ((n : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
  have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  simp only [one_div] at this
  simpa using (this.const_mul B).const_mul (Real.sqrt cEmb)

/-- Uniform convergence on the slab. -/
theorem FamRate.tendstoUniformlyOn {r : ℕ} (h : FamRate F T c r) (hr : 2 ≤ r) (hc : 0 ≤ c) :
    TendstoUniformlyOn (fun n (p : ℝ × T3) => F n p.1 p.2) (fun p => limF F p.1 p.2) atTop
      (Set.Icc 0 T ×ˢ Set.univ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [(Metric.tendsto_nhds.mp (tendsto_bound_zero c)) η hη] with n hn p hp
  rw [dist_comm, dist_eq_norm]
  have h1 : ‖F n p.1 p.2 - limF F p.1 p.2‖ ≤ ‖F n p.1 - limF F p.1‖ := by
    rw [← ContinuousMap.sub_apply]; exact (F n p.1 - limF F p.1).norm_coe_le_norm p.2
  have h2 := (h.limit hr hc hp.1).2.2 n
  rw [Real.dist_eq, sub_zero] at hn
  have := lt_of_le_of_lt (le_abs_self _) hn
  linarith

theorem FamRate.continuousOn {r : ℕ} (h : FamRate F T c r) (hr : 2 ≤ r) (hc : 0 ≤ c)
    (hF : ∀ n, ContinuousOn (fun p : ℝ × T3 => F n p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × T3 => limF F p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) :=
  (h.tendstoUniformlyOn hr hc).continuousOn (Frequently.of_forall hF)

theorem FamRate.isLineDeriv {r r' : ℕ} {F' : ℕ → ℝ → C(T3, MetricRec)} (h : FamRate F T c r)
    (hr : 2 ≤ r) (h' : FamRate F' T c r') (hr' : 2 ≤ r') (hc : 0 ≤ c) {i : Fin 3}
    (hd : ∀ t ∈ Set.Icc 0 T, ∀ n, IsLineDeriv i ⇑(F n t) ⇑(F' n t)) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    IsLineDeriv i ⇑(limF F t) ⇑(limF F' t) :=
  isLineDeriv_of_tendsto (hd t ht) (h.limit hr hc ht).1 (h'.limit hr' hc ht).1

theorem FamRate.hasDerivAt {r r' : ℕ} {F' : ℕ → ℝ → C(T3, MetricRec)} (h : FamRate F T c r)
    (hr : 2 ≤ r) (h' : FamRate F' T c r') (hr' : 2 ≤ r') (hc : 0 ≤ c)
    (hd : ∀ t ∈ Set.Ioo 0 T, ∀ n y, HasDerivAt (fun τ => F n τ y) (F' n t y) t) {t : ℝ}
    (ht : t ∈ Set.Ioo 0 T) (y : T3) :
    HasDerivAt (fun τ => limF F τ y) (limF F' t y) t := by
  have hunif : TendstoUniformlyOn (fun n τ => F' n τ y) (fun τ => limF F' τ y) atTop
      (Set.Ioo 0 T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    have hU := (Metric.tendstoUniformlyOn_iff.mp (h'.tendstoUniformlyOn hr' hc)) η hη
    filter_upwards [hU] with n hn τ hτ
    exact hn (τ, y) ⟨Set.Ioo_subset_Icc_self hτ, Set.mem_univ _⟩
  refine hasDerivAt_of_tendstoUniformlyOn (f := fun n τ => F n τ y) isOpen_Ioo hunif
    (Eventually.of_forall fun n τ hτ => hd τ hτ n y) (fun τ hτ => ?_) ht
  exact ((continuous_eval_const y).tendsto _).comp (h.limit hr hc (Set.Ioo_subset_Icc_self hτ)).1

end Family


/-! ### Joint continuity of interpolated histories -/

section JointCont

variable {N : ℕ} [NeZero N]

theorem continuous_specDL (x : Grid N) :
    ∀ α : List (Fin 3), Continuous fun w : Grid N → ℂ => specDL α w x
  | [] => continuous_apply x
  | i :: α => by
    simp only [specDL_cons, PeriodicGridSobolev.Sampling.specD, LatticeTorusPlancherel.dft,
      smul_eq_mul]
    refine continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_const.mul
      (continuous_const.mul (continuous_finsetSum _ fun z _ => continuous_const.mul ?_)))
    have := continuous_specDL z α
    exact this

theorem derivRec_apply_eq (u : Grid N → MetricRec) (α : List (Fin 3)) (y : T3) (μ ν : Fin 4) :
    derivRec u α y μ ν = (∑ x, specDL α (cx (comp u μ ν)) x *
      PeriodicGridSobolev.interp (fun z => if z = x then (1 : ℂ) else 0) y).re := by
  simp only [derivRec, reField_apply]
  rw [interp_apply_eq_sum]

/-- `(u, y) ↦ ∂^α 𝓘_h u (y)` is jointly continuous. -/
theorem continuous_derivRec (α : List (Fin 3)) :
    Continuous fun z : (Grid N → MetricRec) × T3 => derivRec z.1 α z.2 := by
  refine continuous_pi fun μ => continuous_pi fun ν => ?_
  simp only [derivRec_apply_eq]
  refine Complex.continuous_re.comp (continuous_finsetSum _ fun x _ => ?_)
  refine Continuous.mul ?_ ((PeriodicGridSobolev.interp _).continuous.comp continuous_snd)
  have h1 : Continuous fun u : Grid N → MetricRec => cx (comp u μ ν) :=
    continuous_pi fun z => Complex.continuous_ofReal.comp
      ((continuous_apply ν).comp ((continuous_apply μ).comp (continuous_apply z)))
  exact ((continuous_specDL x α).comp h1).comp continuous_fst

theorem continuousOn_derivRec {T : ℝ} {u : ℝ → Grid N → MetricRec}
    (hu : ContinuousOn u (Set.Icc 0 T)) (α : List (Fin 3)) :
    ContinuousOn (fun p : ℝ × T3 => derivRec (u p.1) α p.2) (Set.Icc 0 T ×ˢ Set.univ) := by
  intro p hp
  have h1 : ContinuousWithinAt (fun p : ℝ × T3 => ((u p.1, p.2) : (Grid N → MetricRec) × T3))
      (Set.Icc 0 T ×ˢ Set.univ) p :=
    ((hu p.1 (Set.mem_prod.1 hp).1).comp continuousWithinAt_fst
      (fun q hq => (Set.mem_prod.1 hq).1)).prodMk continuousWithinAt_snd
  have hc : Continuous fun z : (Grid N → MetricRec) × T3 => derivRec z.1 α z.2 :=
    continuous_derivRec α
  have h3 : ContinuousWithinAt ((fun z : (Grid N → MetricRec) × T3 => derivRec z.1 α z.2) ∘
      (fun p : ℝ × T3 => ((u p.1, p.2) : (Grid N → MetricRec) × T3))) (Set.Icc 0 T ×ˢ Set.univ) p :=
    hc.continuousAt.comp_continuousWithinAt h1
  exact h3

end JointCont

/-! ### The acceleration as an analytic function of the jet -/

/-- The spatial-and-velocity jet `(q, v, ∂q, ∂v, ∂∂q)`. -/
abbrev RJet := MetricRec × MetricRec × (Fin 3 → MetricRec) × (Fin 3 → MetricRec) ×
  (Fin 3 → Fin 3 → MetricRec)

/-- The acceleration solving the normal row:
`Φ = a⁻¹(c^{ij}∂ᵢ∂ⱼq - 2bⁱ∂ᵢv + F(g, (v, ∂q)))`, `g = η + q` (componentwise). -/
def rowAcc (z : RJet) : MetricRec := fun μ ν =>
  (harmA (minkowski + z.1))⁻¹ * (∑ i, ∑ j, harmC i j (minkowski + z.1) * z.2.2.2.2 i j μ ν -
    2 * ∑ i, harmB i (minkowski + z.1) * z.2.2.2.1 i μ ν +
    harmonicSource (minkowski + z.1) (z.2.1, z.2.2.1) μ ν)

theorem normalRow_eq_zero_iff (q v w : MetricRec) (qd vd : Fin 3 → MetricRec)
    (qdd : Fin 3 → Fin 3 → MetricRec) (ha : harmA (minkowski + q) ≠ 0) :
    normalRow q v w qd vd qdd = 0 ↔ w = rowAcc (q, v, qd, vd, qdd) := by
  constructor
  · intro h
    funext μ ν
    have h1 := congrFun (congrFun h μ) ν
    simp only [normalRow, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply, Pi.zero_apply] at h1
    simp only [rowAcc]
    field_simp
    linarith
  · intro h
    funext μ ν
    simp only [h, rowAcc, normalRow, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply, Pi.zero_apply]
    field_simp
    ring

/-- The chart where the row can be solved. -/
def rowChart : Set RJet :=
  {z | (Matrix.of (minkowski + z.1)).det ≠ 0 ∧ harmA (minkowski + z.1) ≠ 0}

theorem isOpen_rowChart : IsOpen rowChart := by
  have hg : Continuous fun z : RJet => minkowski + z.1 := by fun_prop
  have hdet : Continuous fun z : RJet => (Matrix.of (minkowski + z.1)).det :=
    continuous_iff_continuousAt.2 fun z => ContinuousAt.comp
      (g := fun g : MetricRec => (Matrix.of g).det) (analyticAt_det _).continuousAt hg.continuousAt
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  have hAa : AnalyticAt ℝ harmA (minkowski + z.1) := by
    unfold harmA; exact (analyticAt_inv_entry _ hz.1 0 0).neg
  have hA : ContinuousAt (fun z : RJet => harmA (minkowski + z.1)) z :=
    ContinuousAt.comp (g := harmA) (f := fun z : RJet => minkowski + z.1) hAa.continuousAt
      hg.continuousAt
  exact ((hdet.continuousAt.eventually_ne hz.1).and (hA.eventually_ne hz.2))

theorem analyticOnNhd_rowAcc : AnalyticOnNhd ℝ rowAcc rowChart := by
  intro z hz
  have hg : AnalyticAt ℝ (fun z : RJet => minkowski + z.1) z := by fun_prop
  have hcoef : ∀ A : MetricRec → ℝ, AnalyticOnNhd ℝ A detSet →
      AnalyticAt ℝ (fun z : RJet => A (minkowski + z.1)) z := fun A hA =>
    (hA _ hz.1).comp_of_eq hg rfl
  have hAa : AnalyticOnNhd ℝ harmA detSet := fun g hg' => by
    unfold harmA; exact (analyticAt_inv_entry g hg' 0 0).neg
  have hinv : AnalyticAt ℝ (fun z : RJet => (harmA (minkowski + z.1))⁻¹) z :=
    (hcoef _ hAa).inv hz.2
  refine AnalyticAt.pi fun μ => AnalyticAt.pi fun ν => ?_
  have hsrc : AnalyticAt ℝ (fun z : RJet => harmonicSource (minkowski + z.1) (z.2.1, z.2.2.1) μ ν) z := by
    have h := analyticAt_source_jet_of_det μ ν ((z.1, z.2.1, z.2.2.1) : JetSpace) hz.1
    have hp : AnalyticAt ℝ (fun z : RJet => ((z.1, z.2.1, z.2.2.1) : JetSpace)) z := by fun_prop
    exact h.comp_of_eq hp rfl
  have h1 : AnalyticAt ℝ (fun z : RJet => ∑ i, ∑ j, harmC i j (minkowski + z.1) * z.2.2.2.2 i j μ ν) z :=
    Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j _ =>
      (hcoef _ (analyticOnNhd_harmC i j)).mul (by fun_prop)
  have h2 : AnalyticAt ℝ (fun z : RJet => 2 * ∑ i, harmB i (minkowski + z.1) * z.2.2.2.1 i μ ν) z :=
    analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun i _ =>
      (hcoef _ (analyticOnNhd_harmB i)).mul (by fun_prop))
  exact hinv.mul ((h1.sub h2).add hsrc)


/-! ### Auxiliary facts for the writer histories -/

section Aux

variable {N : ℕ} [NeZero N]

theorem derivRec_comm_inner (u : Grid N → MetricRec) (i j k : Fin 3) :
    derivRec u [i, j, k] = derivRec u [i, k, j] := by
  simp only [derivRec, specDL_cons, specDL_nil, specD_comm j k]

theorem derivRec_symRec {u : Grid N → MetricRec} (hu : IsSymRec u) (α : List (Fin 3)) :
    derivRec (symRec u) α = derivRec u α := by
  rw [symRec_of_isSymRec hu]

/-- The time derivative of a symmetrized history from its upper components. -/
theorem hasDerivAt_symRec {u : ℝ → Grid N → MetricRec} {u' : Grid N → MetricRec} {t : ℝ}
    (hu : ∀ x (κ : Upper), HasDerivAt (fun τ => u τ x κ.1.1 κ.1.2) (u' x κ.1.1 κ.1.2) t) (x : Grid N) :
    HasDerivAt (fun τ => symRec (u τ) x) (symRec u' x) t :=
  hasDerivAt_pi.2 fun μ => hasDerivAt_pi.2 fun ν => hu x (upperOf μ ν)

theorem hasDerivAt_symRec_full {u : ℝ → Grid N → MetricRec} {u' : Grid N → MetricRec} {t : ℝ}
    (hu : ∀ x, HasDerivAt (fun τ => u τ x) (u' x) t) (x : Grid N) :
    HasDerivAt (fun τ => symRec (u τ) x) (symRec u' x) t :=
  hasDerivAt_symRec (fun x κ => hasDerivAt_pi.mp (hasDerivAt_pi.mp (hu x) κ.1.1) κ.1.2) x

end Aux

theorem minkowski_inv : (Matrix.of minkowski)⁻¹ = Matrix.of minkowski := by
  rw [minkowski_eq_diagonal]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst h; by_cases h0 : i = 0 <;> simp [Matrix.diagonal, h0]
  · simp [Matrix.diagonal, h]

/-- A neighbourhood of Minkowski where the chart and the bound `|g^{μν} - η^{μν}| ≤ 1/10` hold. -/
theorem exists_inv_chart : ∃ r₁ > 0, ∀ g : MetricRec, ‖g - minkowski‖ < r₁ →
    (Matrix.of g).det ≠ 0 ∧ harmA g ≠ 0 ∧ ∀ μ ν, |(Matrix.of g)⁻¹ μ ν - minkowski μ ν| ≤ 1 / 10 := by
  obtain ⟨r₀, hr₀, hchart⟩ := exists_det_chart
  have hev : ∀ μ ν, ∀ᶠ g in 𝓝 minkowski, |(Matrix.of g)⁻¹ μ ν - minkowski μ ν| < 1 / 10 := by
    intro μ ν
    have hc := (analyticAt_inv_entry minkowski det_minkowski_ne μ ν).continuousAt
    have h0 : (Matrix.of minkowski)⁻¹ μ ν = minkowski μ ν := by rw [minkowski_inv]; rfl
    have := hc.tendsto
    rw [h0] at this
    have hm := (Metric.tendsto_nhds.mp this) (1 / 10) (by norm_num)
    filter_upwards [hm] with g hg
    rwa [Real.dist_eq] at hg
  have hall : ∀ᶠ g in 𝓝 minkowski, ∀ μ ν, |(Matrix.of g)⁻¹ μ ν - minkowski μ ν| < 1 / 10 :=
    eventually_all.2 fun μ => eventually_all.2 fun ν => hev μ ν
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨min r r₀, lt_min hr hr₀, fun g hg => ?_⟩
  have hg1 : ‖g - minkowski‖ < r := lt_of_lt_of_le hg (min_le_left _ _)
  have hg2 : ‖g - minkowski‖ < r₀ := lt_of_lt_of_le hg (min_le_right _ _)
  obtain ⟨hd, ha⟩ := hchart g hg2
  refine ⟨hd, ha, fun μ ν => (hball (by rwa [dist_eq_norm]) μ ν).le⟩


/-! ### The limit fields of the writer -/

section Limit

/-- Rates of the interpolant derivative families from the rate of the interpolants. -/
theorem famRate_of_base {u : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec} {T c : ℝ} {r₀ : ℕ}
    (hsym : ∀ n t, IsSymRec (u n t))
    (hb : ∀ t ∈ Set.Icc 0 T, ∀ n m (κ : Upper),
      sn r₀ ⇑(cmp (interpRec (u n t)) κ.1.1 κ.1.2 - cmp (interpRec (u m t)) κ.1.1 κ.1.2) ≤
        c * (((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹))
    (α : List (Fin 3)) (hα : α.length ≤ r₀) :
    FamRate (fun n t => derivRec (u n t) α) T c (r₀ - α.length) := by
  refine ⟨fun t _ n y μ ν => derivRec_symm (hsym n t) α y μ ν, fun t ht n m κ => ?_⟩
  have hm : MemH (r₀ - α.length + α.length)
      ⇑(cmp (derivRec (u n t) []) κ.1.1 κ.1.2 - cmp (derivRec (u m t) []) κ.1.1 κ.1.2) :=
    memH_sub (memH_cmp_reField _ _ _ _).1 (memH_cmp_reField _ _ _ _).1
  have h := derivRec_cauchy (u n t) (u m t) κ α (r₀ - α.length) hm
  refine ⟨h.1, h.2.trans ?_⟩
  rw [Nat.sub_add_cancel hα]
  exact hb t ht n m κ

variable (q v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec)

/-- The interpolant derivative families of the position, velocity and acceleration. -/
def famQ (α : List (Fin 3)) : ℕ → ℝ → C(T3, MetricRec) := fun n t => derivRec (symRec (q n t)) α
def famV (α : List (Fin 3)) : ℕ → ℝ → C(T3, MetricRec) := fun n t => derivRec (symRec (v n t)) α
def famA (α : List (Fin 3)) : ℕ → ℝ → C(T3, MetricRec) := fun n t =>
  derivRec (symRec (harmonicWriterAcceleration (q n t) (v n t))) α

/-- The limit jet `(Q, V, ∂Q, ∂V, ∂∂Q)` and its time derivative `(V, A, ∂V, ∂A, ∂∂V)`. -/
def limJet (t : ℝ) (x : T3) : RJet :=
  (limF (famQ q []) t x, limF (famV v []) t x, fun i => limF (famQ q [i]) t x,
    fun i => limF (famV v [i]) t x, fun i j => limF (famQ q [i, j]) t x)

def limJet' (t : ℝ) (x : T3) : RJet :=
  (limF (famV v []) t x, limF (famA q v []) t x, fun i => limF (famV v [i]) t x,
    fun i => limF (famA q v [i]) t x, fun i j => limF (famV v [i, j]) t x)

/-- `∂ₜ³Q = DΦ(jet)[∂ₜ jet]` with `Φ = rowAcc`. -/
def limAt (t : ℝ) (x : T3) : MetricRec := fderiv ℝ rowAcc (limJet q v t x) (limJet' q v t x)

/-- **The limit of the writer as a `C³` field** (time clamped to `[0, T]`). -/
def limField (T : ℝ) : HarmonicGaugePropagation.C3Field where
  Q t := limF (famQ q []) (HarmonicGaugePropagation.clampT T t)
  V t := limF (famV v []) (HarmonicGaugePropagation.clampT T t)
  A t := limF (famA q v []) (HarmonicGaugePropagation.clampT T t)
  At t x := fun μ ν => (limAt q v (HarmonicGaugePropagation.clampT T t) x μ ν +
    limAt q v (HarmonicGaugePropagation.clampT T t) x ν μ) / 2
  Qd t i := limF (famQ q [i]) (HarmonicGaugePropagation.clampT T t)
  Vd t i := limF (famV v [i]) (HarmonicGaugePropagation.clampT T t)
  Ad t i := limF (famA q v [i]) (HarmonicGaugePropagation.clampT T t)
  Qdd t i j := limF (famQ q [i, j]) (HarmonicGaugePropagation.clampT T t)
  Vdd t i j := limF (famV v [i, j]) (HarmonicGaugePropagation.clampT T t)
  Qddd t i j k := limF (famQ q [i, j, k]) (HarmonicGaugePropagation.clampT T t)

end Limit

section ClampLemmas

open HarmonicGaugePropagation

variable {T : ℝ}

theorem contOn_clamp {G : ℝ → C(T3, MetricRec)}
    (hG : ContinuousOn (fun p : ℝ × T3 => G p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × T3 => G (clampT T p.1) p.2) (Set.Icc 0 T ×ˢ Set.univ) :=
  hG.congr fun p hp => by simp only [clampT_of_mem (Set.mem_prod.1 hp).1]

theorem hasDerivAt_clamp {G : ℝ → C(T3, MetricRec)} {y : T3} {w : MetricRec} {t : ℝ}
    (ht : t ∈ Set.Ioo 0 T) (hG : HasDerivAt (fun τ => G τ y) w t) :
    HasDerivAt (fun τ => G (clampT T τ) y) w t :=
  hG.congr_of_eventuallyEq ((eventually_clampT ht).mono fun s hs => by simp only [hs])

end ClampLemmas


/-! ### The limit is a classical `C³` solution of the reduced equation -/

section Main

open HarmonicGaugePropagation

/-- The hypotheses on the writer histories shared by the limit theorems. -/
def WriterData (s : ℕ) (T : ℝ) (q v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec)
    (Q₀ V₀ : C(T3, MetricRec)) (ε : ℝ) : Prop :=
  (∀ n, IsWriterSolution T (q n) (v n)) ∧
  (∀ n, q n 0 = sampleRec (n + 1) ⇑Q₀) ∧ (∀ n, v n 0 = sampleRec (n + 1) ⇑V₀) ∧
  (∀ y μ ν, Q₀ y μ ν = Q₀ y ν μ) ∧ (∀ y μ ν, V₀ y μ ν = V₀ y ν μ) ∧
  (∀ k, MemH (s + 1) ⇑(ccoord bM Q₀ k)) ∧ (∀ k, MemH s ⇑(ccoord bM V₀ k)) ∧
  contTop s Q₀ V₀ ≤ ε ∧ (∀ n, ∀ t ∈ Set.Icc 0 T, Xnorm s (q n t) (v n t) ≤ ε)

/-- **Rates of all interpolant derivative families** up to third order (`s ≥ 6`). -/
theorem writer_family_rates (s : ℕ) (hs : 6 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∃ C ≥ 0, ∀ (T : ℝ) (q v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec)
      (Q₀ V₀ : C(T3, MetricRec)) (ε : ℝ), WriterData s T q v Q₀ V₀ ε → ε ≤ δ →
      ∀ α : List (Fin 3), α.length ≤ 3 →
        FamRate (famQ q α) T (C * Real.exp (K * T) * (1 + T) * ε) (s - 1 - α.length) ∧
        (α.length ≤ 2 → FamRate (famV v α) T (C * Real.exp (K * T) * (1 + T) * ε)
          (s - 2 - α.length)) ∧
        (α.length ≤ 1 → FamRate (famA q v α) T (C * Real.exp (K * T) * (1 + T) * ε)
          (s - 3 - α.length)) := by
  obtain ⟨δ, hδ, K, hK, C, hC, hcau⟩ := interp_cauchy s (by omega)
  refine ⟨δ, hδ, K, hK, C, hC, fun T q v Q₀ V₀ ε hW hεδ α hα => ?_⟩
  obtain ⟨hsol, hq0, hv0, hQs, hVs, hQ, hV, hX0, hXq⟩ := hW
  have hε0 : 0 ≤ ε := (contTop_nonneg _ _ _).trans hX0
  have hbound : ∀ t ∈ Set.Icc 0 T, ∀ n m : ℕ,
      C * Real.exp (K * t) * ((1 + t) * ((((n + 1 : ℕ) : ℝ)⁻¹ + ((m + 1 : ℕ) : ℝ)⁻¹) * ε)) ≤
        C * Real.exp (K * T) * (1 + T) * ε * (((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹) := by
    intro t ht n m
    have h1 : Real.exp (K * t) ≤ Real.exp (K * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK)
    have h2 : 1 + t ≤ 1 + T := by linarith [ht.2]
    have e : (((n + 1 : ℕ) : ℝ)⁻¹ + ((m + 1 : ℕ) : ℝ)⁻¹) = ((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹ := by
      push_cast; ring
    rw [e]
    have hp : 0 ≤ (((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹) * ε := by positivity
    have := ht.1
    calc C * Real.exp (K * t) * ((1 + t) * ((((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹) * ε))
        ≤ C * Real.exp (K * T) * ((1 + T) * ((((n : ℝ) + 1)⁻¹ + ((m : ℝ) + 1)⁻¹) * ε)) := by
          gcongr
      _ = _ := by ring
  have hcauT : ∀ t ∈ Set.Icc 0 T, ∀ n m (κ : Upper), _ := fun t ht n m κ =>
    hcau (n + 1) (m + 1) T (q n) (v n) (q m) (v m) Q₀ V₀ ε (hsol n) (hsol m) (hq0 n) (hv0 n)
      (hq0 m) (hv0 m) hQ hV hX0 (hXq n) (hXq m) hεδ t ht κ
  refine ⟨?_, fun h2 => ?_, fun h1 => ?_⟩
  · refine famRate_of_base (u := fun n t => symRec (q n t)) (fun n t => isSymRec_symRec _)
      (fun t ht n m κ => ?_) α (by omega)
    rw [cmp_interpRec_symRec, cmp_interpRec_symRec]
    exact (hcauT t ht n m κ).1.trans (hbound t ht n m)
  · refine famRate_of_base (u := fun n t => symRec (v n t)) (fun n t => isSymRec_symRec _)
      (fun t ht n m κ => ?_) α (by omega)
    rw [cmp_interpRec_symRec, cmp_interpRec_symRec]
    exact (hcauT t ht n m κ).2.1.trans (hbound t ht n m)
  · refine famRate_of_base (u := fun n t => symRec (harmonicWriterAcceleration (q n t) (v n t)))
      (fun n t => isSymRec_symRec _) (fun t ht n m κ => ?_) α (by omega)
    rw [cmp_interpRec_symRec, cmp_interpRec_symRec]
    exact (hcauT t ht n m κ).2.2.trans (hbound t ht n m)

end Main


section Main2

open HarmonicGaugePropagation

variable {s : ℕ} {T : ℝ} {q v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec} {c : ℝ}

theorem continuousOn_symRec_q (hsol : ∀ n, IsWriterSolution T (q n) (v n)) (n : ℕ) :
    ContinuousOn (fun t => symRec (q n t)) (Set.Icc 0 T) := fun t ht =>
  (continuousAt_pi.2 fun x =>
    (hasDerivAt_symRec_full ((hsol n t ht).2.2.1) x).continuousAt).continuousWithinAt

theorem continuousOn_symRec_v (hsol : ∀ n, IsWriterSolution T (q n) (v n)) (n : ℕ) :
    ContinuousOn (fun t => symRec (v n t)) (Set.Icc 0 T) := fun t ht =>
  (continuousAt_pi.2 fun x =>
    (hasDerivAt_symRec ((hsol n t ht).2.2.2) x).continuousAt).continuousWithinAt

theorem famQ_deriv (hsol : ∀ n, IsWriterSolution T (q n) (v n)) (α : List (Fin 3)) :
    ∀ t ∈ Set.Ioo 0 T, ∀ n y, HasDerivAt (fun τ => famQ q α n τ y) (famV v α n t y) t :=
  fun t ht n y => hasDerivAt_derivRec_time
    (hasDerivAt_symRec_full ((hsol n t (Set.Ioo_subset_Icc_self ht)).2.2.1)) α y

theorem famV_deriv (hsol : ∀ n, IsWriterSolution T (q n) (v n)) (α : List (Fin 3)) :
    ∀ t ∈ Set.Ioo 0 T, ∀ n y, HasDerivAt (fun τ => famV v α n τ y) (famA q v α n t y) t :=
  fun t ht n y => hasDerivAt_derivRec_time
    (hasDerivAt_symRec ((hsol n t (Set.Ioo_subset_Icc_self ht)).2.2.2)) α y

theorem famQ_line (α : List (Fin 3)) (i : Fin 3) :
    ∀ t ∈ Set.Icc 0 T, ∀ n, IsLineDeriv i ⇑(famQ q α n t) ⇑(famQ q (i :: α) n t) :=
  fun _ _ n => isLineDeriv_derivRec _ i α

theorem famV_line (α : List (Fin 3)) (i : Fin 3) :
    ∀ t ∈ Set.Icc 0 T, ∀ n, IsLineDeriv i ⇑(famV v α n t) ⇑(famV v (i :: α) n t) :=
  fun _ _ n => isLineDeriv_derivRec _ i α

theorem famA_line (α : List (Fin 3)) (i : Fin 3) :
    ∀ t ∈ Set.Icc 0 T, ∀ n, IsLineDeriv i ⇑(famA q v α n t) ⇑(famA q v (i :: α) n t) :=
  fun _ _ n => isLineDeriv_derivRec _ i α

theorem famQ_comm (i j : Fin 3) (α : List (Fin 3)) : famQ q (i :: j :: α) = famQ q (j :: i :: α) := by
  funext n t; exact derivRec_comm _ i j α

theorem famV_comm (i j : Fin 3) (α : List (Fin 3)) : famV v (i :: j :: α) = famV v (j :: i :: α) := by
  funext n t; exact derivRec_comm _ i j α

theorem famQ_comm_inner (i j k : Fin 3) : famQ q [i, j, k] = famQ q [i, k, j] := by
  funext n t; exact derivRec_comm_inner _ i j k

end Main2


section Main3

open HarmonicGaugePropagation

set_option maxHeartbeats 4000000 in
/-- **The limit of the open writer is a classical `C³` solution of the harmonic reduced equation**
on `[0, T] × 𝕋³` in the small chart (`s ≥ 6`): `limField` satisfies `C3Field.Hyp`, and the
interpolants of `q`, `v`, `∂ₜv` converge uniformly to its fields. -/
theorem writer_limit_hyp (s : ℕ) (hs : 6 ≤ s) :
    ∃ δ > 0, ∀ (T : ℝ) (q v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec)
      (Q₀ V₀ : C(T3, MetricRec)) (ε : ℝ), WriterData s T q v Q₀ V₀ ε → ε ≤ δ → 0 ≤ T →
      (limField q v T).Hyp T ∧ ∀ t ∈ Set.Icc 0 T,
        Tendsto (fun n => interpRec (q n t)) atTop (𝓝 (limF (famQ q []) t)) ∧
        Tendsto (fun n => interpRec (v n t)) atTop (𝓝 (limF (famV v []) t)) ∧
        Tendsto (fun n => interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t)))) atTop
          (𝓝 (limF (famA q v []) t)) := by
  obtain ⟨δR, hδR, KR, hKR, CR, hCR, hrates⟩ := writer_family_rates s hs
  obtain ⟨δS, hδS, _, _, _, _, _, _, _, _, hsolves⟩ := writer_limit_solves s (by omega)
  obtain ⟨ρ, hρ, hacc⟩ := continuousOn_accel_history s (by omega)
  obtain ⟨r₁, hr₁, hinv⟩ := exists_inv_chart
  set B : ℝ := 1 + ∑ j, ‖bM j‖
  have hB : ∀ j, ‖bM j‖ ≤ B := fun j => by
    have := single_le_sum (f := fun j => ‖bM j‖) (fun _ _ => norm_nonneg _) (mem_univ j)
    linarith
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ∑ j, ‖bM j‖ := sum_nonneg fun _ _ => norm_nonneg _
    linarith
  set Cq : ℝ := B * (Real.sqrt cEmb * (16 * Real.sqrt (pc 2)))
  have hCq : 0 ≤ Cq := by positivity
  refine ⟨min (min δR δS) (min ρ (r₁ / (2 * (Cq + 1)))), by positivity,
    fun T q v Q₀ V₀ ε hW hεδ hT => ?_⟩
  have hεR : ε ≤ δR := hεδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεS : ε ≤ δS := hεδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hερ : ε ≤ ρ := hεδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεr : ε ≤ r₁ / (2 * (Cq + 1)) := hεδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hsol, hq0, hv0, hQs, hVs, hQ, hV, hX0, hXq⟩ := hW
  have hε0 : 0 ≤ ε := (contTop_nonneg _ _ _).trans hX0
  set c := CR * Real.exp (KR * T) * (1 + T) * ε
  have hc : 0 ≤ c := by positivity
  have hR := hrates T q v Q₀ V₀ ε ⟨hsol, hq0, hv0, hQs, hVs, hQ, hV, hX0, hXq⟩ hεR
  -- the families and their rates
  have RQ : ∀ α : List (Fin 3), α.length ≤ 3 → FamRate (famQ q α) T c (s - 1 - α.length) :=
    fun α hα => (hR α hα).1
  have RV : ∀ α : List (Fin 3), α.length ≤ 2 → FamRate (famV v α) T c (s - 2 - α.length) :=
    fun α hα => (hR α (by omega)).2.1 hα
  have RA : ∀ α : List (Fin 3), α.length ≤ 1 → FamRate (famA q v α) T c (s - 3 - α.length) :=
    fun α hα => (hR α (by omega)).2.2 hα
  have rQ : ∀ α : List (Fin 3), α.length ≤ 3 → 2 ≤ s - 1 - α.length := fun α hα => by omega
  have rV : ∀ α : List (Fin 3), α.length ≤ 2 → 2 ≤ s - 2 - α.length := fun α hα => by omega
  have rA : ∀ α : List (Fin 3), α.length ≤ 1 → 2 ≤ s - 3 - α.length := fun α hα => by omega
  -- continuity of the interpolant families on the slab
  have hca : ∀ n, ContinuousOn (fun t => symRec (harmonicWriterAcceleration (q n t) (v n t)))
      (Set.Icc 0 T) := by
    intro n
    have h1 := hacc (n + 1) T (fun t => symRec (q n t)) (fun t => symRec (v n t))
      (fun t ht => continuousAt_pi.2 fun x =>
        (hasDerivAt_symRec_full ((hsol n t ht).2.2.1) x).continuousAt)
      (fun t ht => ?_) (fun t _ => isSymRec_symRec _)
      (fun t ht => by rw [Xnorm_symRec]; exact (hXq n t ht).trans hερ)
    · refine (continuous_symRec.comp_continuousOn h1).congr fun t ht => ?_
      simp only [Function.comp_apply, symRec_of_isSymRec (hsol n t ht).1,
        symRec_of_isSymRec (hsol n t ht).2.1]
    · exact (continuousAt_pi.2 fun x =>
        (hasDerivAt_symRec ((hsol n t ht).2.2.2) x).continuousAt)
  have CQ : ∀ α n, ContinuousOn (fun p : ℝ × T3 => famQ q α n p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) :=
    fun α n => continuousOn_derivRec (continuousOn_symRec_q hsol n) α
  have CV : ∀ α n, ContinuousOn (fun p : ℝ × T3 => famV v α n p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) :=
    fun α n => continuousOn_derivRec (continuousOn_symRec_v hsol n) α
  have CA : ∀ α n, ContinuousOn (fun p : ℝ × T3 => famA q v α n p.1 p.2)
      (Set.Icc 0 T ×ˢ Set.univ) := fun α n => continuousOn_derivRec (hca n) α
  -- identification with the plain interpolants
  have eQ : ∀ t ∈ Set.Icc 0 T, ∀ α n, famQ q α n t = derivRec (q n t) α := fun t ht α n =>
    derivRec_symRec (hsol n t ht).1 α
  have eV : ∀ t ∈ Set.Icc 0 T, ∀ α n, famV v α n t = derivRec (v n t) α := fun t ht α n =>
    derivRec_symRec (hsol n t ht).2.1 α
  have LQ : ∀ α : List (Fin 3), α.length ≤ 3 → ∀ t ∈ Set.Icc 0 T,
      Tendsto (fun n => derivRec (q n t) α) atTop (𝓝 (limF (famQ q α) t)) := fun α hα t ht =>
    ((RQ α hα).limit (rQ α hα) hc ht).1.congr fun n => eQ t ht α n
  have LV : ∀ α : List (Fin 3), α.length ≤ 2 → ∀ t ∈ Set.Icc 0 T,
      Tendsto (fun n => derivRec (v n t) α) atTop (𝓝 (limF (famV v α) t)) := fun α hα t ht =>
    ((RV α hα).limit (rV α hα) hc ht).1.congr fun n => eV t ht α n
  have LA : ∀ t ∈ Set.Icc 0 T, Tendsto (fun n => interpRec (symRec
      (harmonicWriterAcceleration (q n t) (v n t)))) atTop (𝓝 (limF (famA q v []) t)) :=
    fun t ht => ((RA [] (by simp)).limit (rA [] (by simp)) hc ht).1
  -- the row of the limit, from `writer_limit_solves`
  have hS := hsolves T q v Q₀ V₀ ε hsol hq0 hv0 hQs hVs hQ hV hX0 hXq hεS
  obtain ⟨Q', V', A', Qd', Vd', Qdd', -, -, hS'⟩ := hS
  have hrowU : ∀ t ∈ Set.Icc 0 T, ∀ y (κ : Upper), normalRow (limF (famQ q []) t y)
      (limF (famV v []) t y) (limF (famA q v []) t y) (fun i => limF (famQ q [i]) t y)
      (fun i => limF (famV v [i]) t y) (fun i j => limF (famQ q [i, j]) t y) κ.1.1 κ.1.2 = 0 := by
    intro t ht y κ
    obtain ⟨hTQ, hTV, -, hrow, -, hTA, hTQd, hTVd, hTQdd, -⟩ := hS' t ht
    have e1 : Q' t = limF (famQ q []) t := tendsto_nhds_unique hTQ (LQ [] (by simp) t ht)
    have e2 : V' t = limF (famV v []) t := tendsto_nhds_unique hTV (LV [] (by simp) t ht)
    have e3 : A' t = limF (famA q v []) t := tendsto_nhds_unique hTA (LA t ht)
    have e4 : ∀ i, Qd' t i = limF (famQ q [i]) t := fun i =>
      tendsto_nhds_unique (hTQd i) (LQ [i] (by simp) t ht)
    have e5 : ∀ i, Vd' t i = limF (famV v [i]) t := fun i =>
      tendsto_nhds_unique (hTVd i) (LV [i] (by simp) t ht)
    have e6 : ∀ i j, Qdd' t i j = limF (famQ q [i, j]) t := fun i j =>
      tendsto_nhds_unique (hTQdd i j) (LQ [i, j] (by simp) t ht)
    have := hrow y κ
    simp only [e1, e2, e3, e4, e5, e6] at this
    exact this
  -- limits: continuity and symmetry
  have cQ : ∀ α : List (Fin 3), α.length ≤ 3 →
      ContinuousOn (fun p : ℝ × T3 => limF (famQ q α) p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) :=
    fun α hα => (RQ α hα).continuousOn (rQ α hα) hc (CQ α)
  have cV : ∀ α : List (Fin 3), α.length ≤ 2 →
      ContinuousOn (fun p : ℝ × T3 => limF (famV v α) p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) :=
    fun α hα => (RV α hα).continuousOn (rV α hα) hc (CV α)
  have cA : ∀ α : List (Fin 3), α.length ≤ 1 →
      ContinuousOn (fun p : ℝ × T3 => limF (famA q v α) p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) :=
    fun α hα => (RA α hα).continuousOn (rA α hα) hc (CA α)
  have sQ : ∀ α : List (Fin 3), α.length ≤ 3 → ∀ t ∈ Set.Icc 0 T, ∀ y μ ν,
      limF (famQ q α) t y μ ν = limF (famQ q α) t y ν μ :=
    fun α hα t ht => ((RQ α hα).limit (rQ α hα) hc ht).2.1
  have sV : ∀ α : List (Fin 3), α.length ≤ 2 → ∀ t ∈ Set.Icc 0 T, ∀ y μ ν,
      limF (famV v α) t y μ ν = limF (famV v α) t y ν μ :=
    fun α hα t ht => ((RV α hα).limit (rV α hα) hc ht).2.1
  have sA : ∀ α : List (Fin 3), α.length ≤ 1 → ∀ t ∈ Set.Icc 0 T, ∀ y μ ν,
      limF (famA q v α) t y μ ν = limF (famA q v α) t y ν μ :=
    fun α hα t ht => ((RA α hα).limit (rA α hα) hc ht).2.1
  -- the chart
  have hQy : ∀ t ∈ Set.Icc 0 T, ∀ y, ‖limF (famQ q []) t y‖ ≤ Cq * ε := by
    intro t ht y
    have hn : ∀ n, ‖interpRec (q n t) y‖ ≤ Cq * ε := by
      intro n
      refine (norm_le_ccoordSum 2 le_rfl bM hB (interpRec (q n t))
        (fun k => (memH_interpRec _ _ k).1) y).trans ?_
      have h1 := ccoordSum_interpRec_le 2 s (hsol n t ht).1 (v n t) (by omega)
      have h2 : 16 * Real.sqrt (pc 2) * Xnorm s (q n t) (v n t) ≤
          16 * Real.sqrt (pc 2) * ε := by gcongr; exact hXq n t ht
      have h3 : Real.sqrt cEmb * ccoordSum 2 bM (interpRec (q n t)) ≤
          Real.sqrt cEmb * (16 * Real.sqrt (pc 2) * ε) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (Real.sqrt_nonneg _)
      calc B * (Real.sqrt cEmb * ccoordSum 2 bM (interpRec (q n t)))
          ≤ B * (Real.sqrt cEmb * (16 * Real.sqrt (pc 2) * ε)) := by gcongr
        _ = Cq * ε := by ring
    have hcv : Tendsto (fun n => ‖interpRec (q n t) y‖) atTop (𝓝 ‖limF (famQ q []) t y‖) :=
      (((continuous_eval_const y).tendsto _).comp (LQ [] (by simp) t ht)).norm
    exact le_of_tendsto' hcv hn
  have hchart : ∀ t ∈ Set.Icc 0 T, ∀ y,
      (Matrix.of (minkowski + limF (famQ q []) t y)).det ≠ 0 ∧
      harmA (minkowski + limF (famQ q []) t y) ≠ 0 ∧
      ∀ μ ν, |(Matrix.of (minkowski + limF (famQ q []) t y))⁻¹ μ ν - minkowski μ ν| ≤ 1 / 10 := by
    intro t ht y
    refine hinv _ ?_
    rw [add_sub_cancel_left]
    refine lt_of_le_of_lt (hQy t ht y) ?_
    have hpos : 0 < 2 * (Cq + 1) := by positivity
    rw [le_div_iff₀ hpos] at hεr
    nlinarith
  -- the row, all components
  have hrowAll : ∀ t ∈ Set.Icc 0 T, ∀ y, normalRow (limF (famQ q []) t y)
      (limF (famV v []) t y) (limF (famA q v []) t y) (fun i => limF (famQ q [i]) t y)
      (fun i => limF (famV v [i]) t y) (fun i j => limF (famQ q [i, j]) t y) = 0 := by
    intro t ht y
    funext μ ν
    rcases le_total μ ν with h | h
    · exact hrowU t ht y ⟨(μ, ν), h⟩
    · rw [normalRow_symm _ _ _ _ _ _ (sQ [] (by simp) t ht y) (hchart t ht y).1
        (sV [] (by simp) t ht y) (fun i => sQ [i] (by simp) t ht y) (sA [] (by simp) t ht y)
        (fun i => sV [i] (by simp) t ht y) (fun i j => sQ [i, j] (by simp) t ht y)
        (fun i j => by simp only [famQ_comm i j []])]
      exact hrowU t ht y ⟨(ν, μ), h⟩
  have hAeq : ∀ t ∈ Set.Icc 0 T, ∀ y, limF (famA q v []) t y = rowAcc (limJet q v t y) :=
    fun t ht y => (normalRow_eq_zero_iff _ _ _ _ _ _ (hchart t ht y).2.1).1 (hrowAll t ht y)
  have hmem : ∀ t ∈ Set.Icc 0 T, ∀ y, limJet q v t y ∈ rowChart :=
    fun t ht y => ⟨(hchart t ht y).1, (hchart t ht y).2.1⟩
  -- time derivatives of the limit families
  have dQ : ∀ α : List (Fin 3), α.length ≤ 2 → ∀ t ∈ Set.Ioo 0 T, ∀ y,
      HasDerivAt (fun τ => limF (famQ q α) τ y) (limF (famV v α) t y) t :=
    fun α hα t ht y => (RQ α (by omega)).hasDerivAt (rQ α (by omega)) (RV α hα) (rV α hα) hc
      (famQ_deriv hsol α) ht y
  have dV : ∀ α : List (Fin 3), α.length ≤ 1 → ∀ t ∈ Set.Ioo 0 T, ∀ y,
      HasDerivAt (fun τ => limF (famV v α) τ y) (limF (famA q v α) t y) t :=
    fun α hα t ht y => (RV α (by omega)).hasDerivAt (rV α (by omega)) (RA α hα) (rA α hα) hc
      (famV_deriv hsol α) ht y
  have hjet : ∀ t ∈ Set.Ioo 0 T, ∀ y,
      HasDerivAt (fun τ => limJet q v τ y) (limJet' q v t y) t := by
    intro t ht y
    refine (dQ [] (by simp) t ht y).prodMk ((dV [] (by simp) t ht y).prodMk
      ((hasDerivAt_pi.2 fun i => dQ [i] (by simp) t ht y).prodMk
      ((hasDerivAt_pi.2 fun i => dV [i] (by simp) t ht y).prodMk
      (hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => dQ [i, j] (by simp) t ht y))))
  have dA : ∀ t ∈ Set.Ioo 0 T, ∀ y,
      HasDerivAt (fun τ => limF (famA q v []) τ y) (limAt q v t y) t := by
    intro t ht y
    have h1 := ((analyticOnNhd_rowAcc _ (hmem t (Set.Ioo_subset_Icc_self ht) y)).differentiableAt
      |>.hasFDerivAt).comp_hasDerivAt t (hjet t ht y)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    exact hAeq τ (Set.Ioo_subset_Icc_self hτ) y
  have hAtsym : ∀ t ∈ Set.Ioo 0 T, ∀ y μ ν, limAt q v t y μ ν = limAt q v t y ν μ := by
    intro t ht y μ ν
    have h1 := hasDerivAt_pi.mp (hasDerivAt_pi.mp (dA t ht y) μ) ν
    have h2 := hasDerivAt_pi.mp (hasDerivAt_pi.mp (dA t ht y) ν) μ
    refine h1.unique (h2.congr_of_eventuallyEq ?_)
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    exact (sA [] (by simp) τ (Set.Ioo_subset_Icc_self hτ) y μ ν)
  -- continuity of the third time derivative
  have cJ : ContinuousOn (fun p : ℝ × T3 => limJet q v p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) :=
    (cQ [] (by simp)).prodMk ((cV [] (by simp)).prodMk ((continuousOn_pi.2 fun i => cQ [i] (by simp)).prodMk
      ((continuousOn_pi.2 fun i => cV [i] (by simp)).prodMk
      (continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => cQ [i, j] (by simp)))))
  have cJ' : ContinuousOn (fun p : ℝ × T3 => limJet' q v p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) :=
    (cV [] (by simp)).prodMk ((cA [] (by simp)).prodMk ((continuousOn_pi.2 fun i => cV [i] (by simp)).prodMk
      ((continuousOn_pi.2 fun i => cA [i] (by simp)).prodMk
      (continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => cV [i, j] (by simp)))))
  have cAt : ContinuousOn (fun p : ℝ × T3 => limAt q v p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) := by
    have hD : ContinuousOn (fderiv ℝ rowAcc) rowChart := analyticOnNhd_rowAcc.fderiv.continuousOn
    have h1 : ContinuousOn (fun p : ℝ × T3 => fderiv ℝ rowAcc (limJet q v p.1 p.2))
        (Set.Icc 0 T ×ˢ Set.univ) :=
      hD.comp cJ fun p hp => hmem p.1 (Set.mem_prod.1 hp).1 p.2
    exact h1.clm_apply cJ'
  have cAtS : ContinuousOn (fun p : ℝ × T3 => (limField q v T).At p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) := by
    have h1 : ContinuousOn (fun p : ℝ × T3 => limAt q v (clampT T p.1) p.2) (Set.Icc 0 T ×ˢ Set.univ) :=
      cAt.congr fun p hp => by simp only [clampT_of_mem (Set.mem_prod.1 hp).1]
    refine continuousOn_pi.2 fun μ => continuousOn_pi.2 fun ν => ?_
    exact (((continuousOn_pi.1 ((continuousOn_pi.1 h1) μ)) ν).add
      ((continuousOn_pi.1 ((continuousOn_pi.1 h1) ν)) μ)).div_const 2
  have cl := fun {t : ℝ} (ht : t ∈ Set.Icc 0 T) => clampT_of_mem ht
  have clo := fun {t : ℝ} (ht : t ∈ Set.Ioo 0 T) => clampT_of_mem (Set.Ioo_subset_Icc_self ht)
  have cm := clampT_mem hT
  refine ⟨{ cQ := contOn_clamp (cQ [] (by simp))
            cV := contOn_clamp (cV [] (by simp))
            cA := contOn_clamp (cA [] (by simp))
            cAt := cAtS
            cQd := fun i => contOn_clamp (cQ [i] (by simp))
            cVd := fun i => contOn_clamp (cV [i] (by simp))
            cAd := fun i => contOn_clamp (cA [i] (by simp))
            cQdd := fun i j => contOn_clamp (cQ [i, j] (by simp))
            cVdd := fun i j => contOn_clamp (cV [i, j] (by simp))
            cQddd := fun i j k => contOn_clamp (cQ [i, j, k] (by simp))
            sQ := fun t x μ ν => sQ [] (by simp) _ (cm t) x μ ν
            sV := fun t x μ ν => sV [] (by simp) _ (cm t) x μ ν
            sA := fun t x μ ν => sA [] (by simp) _ (cm t) x μ ν
            sAt := fun t x μ ν => by simp only [limField]; ring
            sQd := fun t i x μ ν => sQ [i] (by simp) _ (cm t) x μ ν
            sVd := fun t i x μ ν => sV [i] (by simp) _ (cm t) x μ ν
            sAd := fun t i x μ ν => sA [i] (by simp) _ (cm t) x μ ν
            sQdd := fun t i j x μ ν => sQ [i, j] (by simp) _ (cm t) x μ ν
            sVdd := fun t i j x μ ν => sV [i, j] (by simp) _ (cm t) x μ ν
            sQddd := fun t i j k x μ ν => sQ [i, j, k] (by simp) _ (cm t) x μ ν
            iQdd := fun t i j => by simp only [limField, famQ_comm i j []]
            iVdd := fun t i j => by simp only [limField, famV_comm i j []]
            iQddd1 := fun t i j k => by simp only [limField, famQ_comm i j [k]]
            iQddd2 := fun t i j k => by simp only [limField, famQ_comm_inner i j k]
            tQ := fun t ht x => by
              have := hasDerivAt_clamp ht (dQ [] (by simp) t ht x)
              simpa only [limField, clo ht] using this
            tV := fun t ht x => by
              have := hasDerivAt_clamp ht (dV [] (by simp) t ht x)
              simpa only [limField, clo ht] using this
            tA := fun t ht x => by
              have := hasDerivAt_clamp ht (dA t ht x)
              refine this.congr_deriv ?_
              funext μ ν
              simp only [limField, clo ht, hAtsym t ht x ν μ]
              ring
            tQd := fun t ht i x => by
              have := hasDerivAt_clamp ht (dQ [i] (by simp) t ht x)
              simpa only [limField, clo ht] using this
            tVd := fun t ht i x => by
              have := hasDerivAt_clamp ht (dV [i] (by simp) t ht x)
              simpa only [limField, clo ht] using this
            tQdd := fun t ht i j x => by
              have := hasDerivAt_clamp ht (dQ [i, j] (by simp) t ht x)
              simpa only [limField, clo ht] using this
            xQ := fun t ht i => by
              show IsLineDeriv i ⇑(limF (famQ q []) (clampT T t)) ⇑(limF (famQ q [i]) (clampT T t))
              rw [cl ht]
              exact (RQ [] (by simp)).isLineDeriv (rQ [] (by simp)) (RQ [i] (by simp))
                (rQ [i] (by simp)) hc (famQ_line [] i) ht
            xV := fun t ht i => by
              show IsLineDeriv i ⇑(limF (famV v []) (clampT T t)) ⇑(limF (famV v [i]) (clampT T t))
              rw [cl ht]
              exact (RV [] (by simp)).isLineDeriv (rV [] (by simp)) (RV [i] (by simp))
                (rV [i] (by simp)) hc (famV_line [] i) ht
            xA := fun t ht i => by
              show IsLineDeriv i ⇑(limF (famA q v []) (clampT T t))
                ⇑(limF (famA q v [i]) (clampT T t))
              rw [cl ht]
              exact (RA [] (by simp)).isLineDeriv (rA [] (by simp)) (RA [i] (by simp))
                (rA [i] (by simp)) hc (famA_line [] i) ht
            xQd := fun t ht i j => by
              show IsLineDeriv i ⇑(limF (famQ q [j]) (clampT T t))
                ⇑(limF (famQ q [i, j]) (clampT T t))
              rw [cl ht]
              exact (RQ [j] (by simp)).isLineDeriv (rQ [j] (by simp)) (RQ [i, j] (by simp))
                (rQ [i, j] (by simp)) hc (famQ_line [j] i) ht
            xVd := fun t ht i j => by
              show IsLineDeriv i ⇑(limF (famV v [j]) (clampT T t))
                ⇑(limF (famV v [i, j]) (clampT T t))
              rw [cl ht]
              exact (RV [j] (by simp)).isLineDeriv (rV [j] (by simp)) (RV [i, j] (by simp))
                (rV [i, j] (by simp)) hc (famV_line [j] i) ht
            xQdd := fun t ht i j k => by
              show IsLineDeriv i ⇑(limF (famQ q [j, k]) (clampT T t))
                ⇑(limF (famQ q [i, j, k]) (clampT T t))
              rw [cl ht]
              exact (RQ [j, k] (by simp)).isLineDeriv (rQ [j, k] (by simp))
                (RQ [i, j, k] (by simp)) (rQ [i, j, k] (by simp)) hc (famQ_line [j, k] i) ht
            chart := fun t ht x μ ν => by
              simp only [limField, cl ht]
              exact (hchart t ht x).2.2 μ ν
            row := fun t ht x μ ν => by
              simp only [limField, cl ht]
              exact congrFun (congrFun (hrowAll t ht x) μ) ν },
    fun t ht => ⟨LQ [] (by simp) t ht, LV [] (by simp) t ht, LA t ht⟩⟩

end Main3

end

end RenewalGeometry.OpenWriterLimitRegularity
