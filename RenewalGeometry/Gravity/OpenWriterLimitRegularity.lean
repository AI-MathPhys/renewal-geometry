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

set_option maxHeartbeats 1000000 in
theorem continuousOn_derivRec {T : ℝ} {u : ℝ → Grid N → MetricRec}
    (hu : ContinuousOn u (Set.Icc 0 T)) (α : List (Fin 3)) :
    ContinuousOn (fun p : ℝ × T3 => derivRec (u p.1) α p.2) (Set.Icc 0 T ×ˢ Set.univ) := by
  intro p hp
  have h1 : ContinuousWithinAt (fun p : ℝ × T3 => ((u p.1, p.2) : (Grid N → MetricRec) × T3))
      (Set.Icc 0 T ×ˢ Set.univ) p :=
    ((hu p.1 (Set.mem_prod.1 hp).1).comp continuousWithinAt_fst
      (fun q hq => (Set.mem_prod.1 hq).1)).prodMk continuousWithinAt_snd
  exact (continuous_derivRec (N := N) α).continuousAt.comp_continuousWithinAt h1

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
  have hA : ContinuousAt (fun z : RJet => harmA (minkowski + z.1)) z :=
    ContinuousAt.comp (g := fun g : MetricRec => -((Matrix.of g)⁻¹ 0 0))
      ((analyticAt_inv_entry _ hz.1 0 0).neg.continuousAt) hg.continuousAt
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
