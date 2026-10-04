/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMReducedExtraction

/-!
# Reduced Einstein–Standard-Model variational closure (`thm:reduced-closure`)

Rendering as in `EinsteinSMCompactnessCertificates.lean` and `EinsteinSMGravityFirstOrder.lean`:
`M = (0,T) × 𝕋³` lifted to `ℝ⁴`, trivialised bundles, compact charts rendered as chart boxes;
the regulator sequence is `RegulatorSequence` (`def:regulator`) with reconstructions
`reg.fields n = R_h(z_h^d)`, banks `reg.bank n`, consistency defect `c_h(K)` and stationarity
defect `ε_h(K)`.

**Slab exhaustion.**  A test region `K ⋐ M` has its time support in the open interval of a slab
box `(t₀,t₁) × (0,1)³` (`CylRegion.exists_slab_Ioo`), which carries the whole first variation of
every test in `𝒱_K` (spatial periodicity).  The slabs `slabExh T m = (T/(m+3), T - T/(m+3)) ×
(0,1)³` exhaust these; reduced action convergence "on every compact chart" of the conclusion is
rendered as reduced convergence on **every slab box** `(t₀,t₁) × (0,1)³`, `0 < t₀ < t₁ < T`
(every compact region of `M` is covered by such a slab up to the spatial periods).

Contents:

* `ReducedConvergence.mono` (restriction to a sub-box), `ReducedConvergence.congr_ae` (a.e.
  modification of the limit), `ReducedConvergence.unique` (limits agree a.e.),
  `ReducedConvergence.comp` (subsequences), `ReducedConvergence.of_tail`;
* `exists_diagonal_reducedConvergence`: the diagonal argument over the slab exhaustion `slabExh`
  with one limit, patched from the slab limits (`patch_ae`);
* `ReducedConvergence.higgs_strong`: strong `H¹ ∩ L⁴` Higgs convergence in the reduced class;
* `limit_eq_zero_of_defects`: the residual bound `eq:reduced-residual-bound`;
* `einsteinDistribution`, `stressDistribution`: the distributions of `eq:reduced-Einstein-limit`
  (`app:palatini`, `eq:stress-definition`) on metric tests;
* **`reduced_closure`** (`thm:reduced-closure`);
* non-vacuity: the flat regulator is consistent and stationary (`flatRegulator_consistent`,
  `flatRegulator_stationary`) and satisfies every hypothesis of `reduced_closure`.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM

open SobolevOpen (pd box IsTest MemW12)

/-! ### Generic congruence and uniqueness facts -/

section Generic

variable {T : ℝ}

/-- Integrals over `ℝ⁴` of integrands that agree off `Ω` and a.e. on `Ω` coincide. -/
theorem integral_congr_on {Ω : Set E4} (hΩ : MeasurableSet Ω) {F G : E4 → ℂ}
    (h0 : ∀ x ∉ Ω, F x = G x) (h : ∀ᵐ x ∂(volume.restrict Ω), F x = G x) :
    ∫ x, F x = ∫ x, G x := by
  refine integral_congr_ae ?_
  have h' := (ae_restrict_iff' hΩ).mp h
  filter_upwards [h'] with x hx
  by_cases hxΩ : x ∈ Ω
  · exact hx hxΩ
  · exact h0 x hxΩ

theorem test_eq_zero_off {Ω : Set E4} {φ : E4 → ℝ} (hφ : IsTest Ω φ) {x : E4} (hx : x ∉ Ω) :
    φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (hφ.subset h)

theorem test_pd_eq_zero_off {Ω : Set E4} {φ : E4 → ℝ} (hφ : IsTest Ω φ) (i : Fin 4) {x : E4}
    (hx : x ∉ Ω) : pd φ i x = 0 := test_eq_zero_off (hφ.pd i) hx

/-- `W^{1,2}` membership is invariant under a.e. modification on the box. -/
theorem memW12_congr_ae_box (Q : ChartBox T) {u u' : E4 → ℂ} {g g' : Fin 4 → E4 → ℂ}
    (h : MemW12 Q.set u g) (hu : u =ᵐ[Q.μ] u') (hg : ∀ i, g i =ᵐ[Q.μ] g' i) :
    MemW12 Q.set u' g' := by
  refine ⟨h.memLp.ae_eq hu, fun i => (h.memLp_grad i).ae_eq (hg i), fun i φ hφ => ?_⟩
  have e1 : ∫ x, ((pd φ i x : ℝ) : ℂ) * u' x = ∫ x, ((pd φ i x : ℝ) : ℂ) * u x :=
    integral_congr_on Q.isOpen.measurableSet (fun x hx => by simp [test_pd_eq_zero_off hφ i hx])
      (hu.mono fun x hx => by rw [hx])
  have e2 : ∫ x, ((φ x : ℝ) : ℂ) * g' i x = ∫ x, ((φ x : ℝ) : ℂ) * g i x :=
    integral_congr_on Q.isOpen.measurableSet (fun x hx => by simp [test_eq_zero_off hφ hx])
      ((hg i).mono fun x hx => by rw [hx])
  rw [e1, e2]
  exact h.weak i φ hφ

/-- `W^{1,2}` membership restricts to sub-boxes. -/
theorem memW12_mono_box {Q Q' : ChartBox T} (hQ : Q.set ⊆ Q'.set) {u : E4 → ℂ}
    {g : Fin 4 → E4 → ℂ} (h : MemW12 Q'.set u g) : MemW12 Q.set u g :=
  ⟨h.memLp.mono_measure (Measure.restrict_mono hQ le_rfl), fun i =>
    (h.memLp_grad i).mono_measure (Measure.restrict_mono hQ le_rfl), fun i φ hφ =>
    h.weak i φ (hφ.mono hQ)⟩

variable {ι' : Type} [Fintype ι']

omit [Fintype ι'] in
theorem ae_comp_of_ae {Q : ChartBox T} {u u' : E4 → ι' → ℂ} (h : u =ᵐ[Q.μ] u') (c : ι') :
    (fun x => u x c) =ᵐ[Q.μ] fun x => u' x c :=
  h.mono fun x hx => by simp only [hx]

theorem MemH1.congr_ae {Q : ChartBox T} {u u' : E4 → ι' → ℂ} {g g' : E4 → Fin 4 → ι' → ℂ}
    (h : MemH1 Q u g) (hu : u =ᵐ[Q.μ] u') (hg : g =ᵐ[Q.μ] g') : MemH1 Q u' g' := fun c =>
  memW12_congr_ae_box Q (h c) (ae_comp_of_ae hu c) fun i => hg.mono fun x hx => by simp only [hx]

theorem MemH1.mono_box {Q Q' : ChartBox T} (hQ : Q.set ⊆ Q'.set) {u : E4 → ι' → ℂ}
    {g : E4 → Fin 4 → ι' → ℂ} (h : MemH1 Q' u g) : MemH1 Q u g := fun c => memW12_mono_box hQ (h c)

theorem eLpNorm_box_mono {F : Type*} [NormedAddCommGroup F] {Q Q' : ChartBox T}
    (hQ : Q.set ⊆ Q'.set) (f : E4 → F) (p : ℝ≥0∞) : eLpNorm f p Q.μ ≤ eLpNorm f p Q'.μ :=
  eLpNorm_mono_measure f (Measure.restrict_mono hQ le_rfl)

theorem LpTendsto.mono_box {F : Type*} [NormedAddCommGroup F] {Q Q' : ChartBox T}
    (hQ : Q.set ⊆ Q'.set) {p : ℝ≥0∞} {u : ℕ → E4 → F} {u₀ : E4 → F}
    (h : LpTendsto p Q'.μ u u₀) : LpTendsto p Q.μ u u₀ :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => zero_le)
    fun n => eLpNorm_box_mono hQ _ p

theorem LpTendsto.congr_lim {F : Type*} [NormedAddCommGroup F] {μ : Measure E4} {p : ℝ≥0∞}
    {u : ℕ → E4 → F} {u₀ u₀' : E4 → F} (h : LpTendsto p μ u u₀) (he : u₀ =ᵐ[μ] u₀') :
    LpTendsto p μ u u₀' :=
  h.congr fun n => eLpNorm_congr_ae (f := u n - u₀) (g := u n - u₀') (he.mono fun x hx => by
    simp only [Pi.sub_apply, hx])

theorem H1Tendsto.mono_box {Q Q' : ChartBox T} (hQ : Q.set ⊆ Q'.set) {u : ℕ → E4 → ι' → ℂ}
    {g : ℕ → E4 → Fin 4 → ι' → ℂ} {u₀ : E4 → ι' → ℂ} {g₀ : E4 → Fin 4 → ι' → ℂ}
    (h : H1Tendsto Q' u g u₀ g₀) : H1Tendsto Q u g u₀ g₀ :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => zero_le)
    fun n => add_le_add (eLpNorm_box_mono hQ _ 2) (eLpNorm_box_mono hQ _ 2)

theorem H1Tendsto.congr_lim {Q : ChartBox T} {u : ℕ → E4 → ι' → ℂ}
    {g : ℕ → E4 → Fin 4 → ι' → ℂ} {u₀ u₀' : E4 → ι' → ℂ} {g₀ g₀' : E4 → Fin 4 → ι' → ℂ}
    (h : H1Tendsto Q u g u₀ g₀) (hu : u₀ =ᵐ[Q.μ] u₀') (hg : g₀ =ᵐ[Q.μ] g₀') :
    H1Tendsto Q u g u₀' g₀' :=
  h.congr fun n => by
    unfold h1Norm
    rw [eLpNorm_congr_ae (f := u n - u₀) (g := u n - u₀') (hu.mono fun x hx => by
        simp only [Pi.sub_apply, hx]),
      eLpNorm_congr_ae (f := g n - g₀) (g := g n - g₀') (hg.mono fun x hx => by
        simp only [Pi.sub_apply, hx])]

theorem WeakH1Tendsto.mono_box {Q Q' : ChartBox T} (hQ : Q.set ⊆ Q'.set)
    {u : ℕ → E4 → ι' → ℂ} {g : ℕ → E4 → Fin 4 → ι' → ℂ} {u₀ : E4 → ι' → ℂ}
    {g₀ : E4 → Fin 4 → ι' → ℂ} (h : WeakH1Tendsto Q' u g u₀ g₀) : WeakH1Tendsto Q u g u₀ g₀ := by
  obtain ⟨h1, h2, ⟨B, hBt, hB⟩, h4, h5⟩ := h
  exact ⟨fun n => (h1 n).mono_box hQ, h2.mono_box hQ, ⟨B, hBt, fun n =>
    (add_le_add (eLpNorm_box_mono hQ _ 2) (eLpNorm_box_mono hQ _ 2)).trans (hB n)⟩,
    fun φ hφ c => h4 φ (hφ.mono hQ) c, fun φ hφ i c => h5 φ (hφ.mono hQ) i c⟩

theorem WeakH1Tendsto.congr_lim {Q : ChartBox T} {u : ℕ → E4 → ι' → ℂ}
    {g : ℕ → E4 → Fin 4 → ι' → ℂ} {u₀ u₀' : E4 → ι' → ℂ} {g₀ g₀' : E4 → Fin 4 → ι' → ℂ}
    (h : WeakH1Tendsto Q u g u₀ g₀) (hu : u₀ =ᵐ[Q.μ] u₀') (hg : g₀ =ᵐ[Q.μ] g₀') :
    WeakH1Tendsto Q u g u₀' g₀' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2.congr_ae hu hg, h3, fun φ hφ c => ?_, fun φ hφ i c => ?_⟩
  · have e : ∫ x, ((φ x : ℝ) : ℂ) * u₀' x c = ∫ x, ((φ x : ℝ) : ℂ) * u₀ x c :=
      integral_congr_on Q.isOpen.measurableSet (fun x hx => by simp [test_eq_zero_off hφ hx])
        (hu.mono fun x hx => by rw [hx])
    rw [e]; exact h4 φ hφ c
  · have e : ∫ x, ((φ x : ℝ) : ℂ) * g₀' x i c = ∫ x, ((φ x : ℝ) : ℂ) * g₀ x i c :=
      integral_congr_on Q.isOpen.measurableSet (fun x hx => by simp [test_eq_zero_off hφ hx])
        (hg.mono fun x hx => by rw [hx])
    rw [e]; exact h5 φ hφ i c

/-- Two `L^p` limits of one sequence agree a.e. -/
theorem ae_eq_of_tendsto_two {F : Type*} [NormedAddCommGroup F] {μ : Measure E4} {p : ℝ≥0∞}
    (hp : 1 ≤ p) {u : ℕ → E4 → F} {a b : E4 → F} (hu : ∀ n, AEStronglyMeasurable (u n) μ)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (h1 : Tendsto (fun n => eLpNorm (u n - a) p μ) atTop (𝓝 0))
    (h2 : Tendsto (fun n => eLpNorm (u n - b) p μ) atTop (𝓝 0)) : a =ᵐ[μ] b := by
  have hle : ∀ n, eLpNorm (a - b) p μ ≤ eLpNorm (u n - b) p μ + eLpNorm (u n - a) p μ := by
    intro n
    have e : a - b = (u n - b) - (u n - a) := by abel
    rw [e]
    exact eLpNorm_sub_le ((hu n).sub hb) ((hu n).sub ha) hp
  have h0 : eLpNorm (a - b) p μ = 0 := by
    have := ge_of_tendsto' (by simpa using h2.add h1) hle
    exact le_antisymm this zero_le
  have := (eLpNorm_eq_zero_iff (ha.sub hb) (by positivity)).mp h0
  filter_upwards [this] with x hx
  exact sub_eq_zero.mp hx

/-- Test pairings determine `L²(Q)` functions a.e. on `Q`. -/
theorem ae_eq_of_pairings (Q : ChartBox T) {v w : E4 → ℂ} (hv : MemLp v 2 Q.μ)
    (hw : MemLp w 2 Q.μ) (h : ∀ φ : E4 → ℝ, IsTest Q.set φ →
      ∫ x, ((φ x : ℝ) : ℂ) * v x = ∫ x, ((φ x : ℝ) : ℂ) * w x) : v =ᵐ[Q.μ] w :=
  (ae_restrict_iff' Q.isOpen.measurableSet).mpr
    (SobolevOpen.ae_eq_of_integral_test Q.isOpen (SobolevOpen.locallyIntegrableOn_of_memLp hv)
      (SobolevOpen.locallyIntegrableOn_of_memLp hw) h)

theorem ae_eq_of_comp {Q : ChartBox T} {u u' : E4 → ι' → ℂ}
    (h : ∀ c, (fun x => u x c) =ᵐ[Q.μ] fun x => u' x c) : u =ᵐ[Q.μ] u' := by
  have := ae_all_iff.mpr h
  filter_upwards [this] with x hx
  exact funext hx

/-- Weak `H¹` limits of one sequence agree a.e. (values and gradients). -/
theorem WeakH1Tendsto.unique {Q : ChartBox T} {u : ℕ → E4 → ι' → ℂ}
    {g : ℕ → E4 → Fin 4 → ι' → ℂ} {u₀ u₀' : E4 → ι' → ℂ} {g₀ g₀' : E4 → Fin 4 → ι' → ℂ}
    (h : WeakH1Tendsto Q u g u₀ g₀) (h' : WeakH1Tendsto Q u g u₀' g₀') :
    u₀ =ᵐ[Q.μ] u₀' ∧ g₀ =ᵐ[Q.μ] g₀' := by
  refine ⟨ae_eq_of_comp fun c => ae_eq_of_pairings Q (h.2.1 c).memLp (h'.2.1 c).memLp
    fun φ hφ => tendsto_nhds_unique (h.2.2.2.1 φ hφ c) (h'.2.2.2.1 φ hφ c), ?_⟩
  have hc : ∀ i c, (fun x => g₀ x i c) =ᵐ[Q.μ] fun x => g₀' x i c := fun i c =>
    ae_eq_of_pairings Q ((h.2.1 c).memLp_grad i) ((h'.2.1 c).memLp_grad i)
      fun φ hφ => tendsto_nhds_unique (h.2.2.2.2 φ hφ i c) (h'.2.2.2.2 φ hφ i c)
  have := ae_all_iff.mpr fun i => ae_all_iff.mpr (hc i)
  filter_upwards [this] with x hx
  exact funext fun i => funext fun c => hx i c

end Generic

/-! ### Reduced convergence: restriction, modification, uniqueness, subsequences -/

section ReducedOps

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {Ysec : Type} [Fintype Ysec]

/-- Two limit-field tuples agree a.e. on a chart box (all ten components). -/
structure LimitFields.AEEqOn (Q : ChartBox T) (L L' : LimitFields C) : Prop where
  e : L.e =ᵐ[Q.μ] L'.e
  de : L.de =ᵐ[Q.μ] L'.de
  A : L.A =ᵐ[Q.μ] L'.A
  F : L.F =ᵐ[Q.μ] L'.F
  H : L.H =ᵐ[Q.μ] L'.H
  K : L.K =ᵐ[Q.μ] L'.K
  Ψ : L.Ψ =ᵐ[Q.μ] L'.Ψ
  dΨ : L.dΨ =ᵐ[Q.μ] L'.dΨ
  Ψb : L.Ψb =ᵐ[Q.μ] L'.Ψb
  dΨb : L.dΨb =ᵐ[Q.μ] L'.dΨb

theorem coframeC_ae {Q : ChartBox T} {e e' : E4 → CoframeFibre} (h : e =ᵐ[Q.μ] e') :
    coframeC e =ᵐ[Q.μ] coframeC e' := h.mono fun x hx => by
  show (fun p : Fin 4 × Fin 4 => (e x p.1 p.2 : ℂ)) = fun p => (e' x p.1 p.2 : ℂ)
  rw [hx]

theorem spinorC_ae {Q : ChartBox T} {Ψ Ψ' : E4 → SpinorFibre C} (h : Ψ =ᵐ[Q.μ] Ψ') :
    spinorC Ψ =ᵐ[Q.μ] spinorC Ψ' := h.mono fun x hx => by
  show (fun p : Fin 4 × C => Ψ x p.1 p.2) = fun p => Ψ' x p.1 p.2
  rw [hx]

/-- **Reduced convergence is invariant under a.e. modification of the limit on the chart.** -/
theorem ReducedConvergence.congr_ae {Q : ChartBox T} {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} {L L' : LimitFields C} {θ₀ : CoefficientBank Ysec}
    (h : ReducedConvergence Q z θ L θ₀) (hL : LimitFields.AEEqOn Q L L') :
    ReducedConvergence Q z θ L' θ₀ := by
  obtain ⟨Ke, hKe, hKn, hKL⟩ := h.coframe_chart
  have hAμ : ∀ μ, (fun x => L.A x μ) =ᵐ[Q.μ] fun x => L'.A x μ := fun μ =>
    hL.A.mono fun x hx => by simp only [hx]
  refine
    { coframe_chart := ⟨Ke, hKe, hKn, (hKL.and hL.e).mono fun x hx => hx.2 ▸ hx.1⟩
      coframe_mem := h.coframe_mem.congr_ae (coframeC_ae hL.e) hL.de
      coframe_tendsto := h.coframe_tendsto.congr_lim (coframeC_ae hL.e) hL.de
      conn_lie := (h.conn_lie.and hL.A).mono fun x hx => hx.2 ▸ hx.1
      conn_mem := h.conn_mem.ae_eq hL.A
      conn_tendsto := h.conn_tendsto.congr_lim hL.A
      curv_mem := h.curv_mem.ae_eq hL.F
      curv_weak := fun μ ν i j φ hφ => ?_
      curv_tendsto := h.curv_tendsto.congr_lim hL.F
      higgs_mem := h.higgs_mem.ae_eq hL.H
      higgs_tendsto := h.higgs_tendsto.congr_lim hL.H
      covgrad_mem := h.covgrad_mem.ae_eq hL.K
      covgrad_weak := fun μ c φ hφ => ?_
      covgrad_tendsto := h.covgrad_tendsto.congr_lim hL.K
      spinor_weak := h.spinor_weak.congr_lim (spinorC_ae hL.Ψ) hL.dΨ
      cospinor_weak := h.cospinor_weak.congr_lim (spinorC_ae hL.Ψb) hL.dΨb
      bank_compact := h.bank_compact
      bank_tendsto := h.bank_tendsto }
  · have e1 : ∫ x, ((φ x : ℝ) : ℂ) * (L'.F x μ ν i j - comm (L'.A x μ) (L'.A x ν) i j) =
        ∫ x, ((φ x : ℝ) : ℂ) * (L.F x μ ν i j - comm (L.A x μ) (L.A x ν) i j) :=
      integral_congr_on Q.isOpen.measurableSet (fun x hx => by simp [test_eq_zero_off hφ hx])
        ((hL.F.and hL.A).mono fun x hx => by rw [hx.1, hx.2])
    have e2 : ∫ x, (((pd φ μ x : ℝ) : ℂ) * L'.A x ν i j - ((pd φ ν x : ℝ) : ℂ) * L'.A x μ i j) =
        ∫ x, (((pd φ μ x : ℝ) : ℂ) * L.A x ν i j - ((pd φ ν x : ℝ) : ℂ) * L.A x μ i j) :=
      integral_congr_on Q.isOpen.measurableSet
        (fun x hx => by simp [test_pd_eq_zero_off hφ μ hx, test_pd_eq_zero_off hφ ν hx])
        (hL.A.mono fun x hx => by rw [hx])
    rw [e1, e2]; exact h.curv_weak μ ν i j φ hφ
  · have e1 : ∫ x, ((φ x : ℝ) : ℂ) * (L'.K x μ c - higgsAct (L'.A x μ) (L'.H x) c) =
        ∫ x, ((φ x : ℝ) : ℂ) * (L.K x μ c - higgsAct (L.A x μ) (L.H x) c) :=
      integral_congr_on Q.isOpen.measurableSet (fun x hx => by simp [test_eq_zero_off hφ hx])
        ((hL.K.and (hL.A.and hL.H)).mono fun x hx => by rw [hx.1, hx.2.1, hx.2.2])
    have e2 : ∫ x, ((pd φ μ x : ℝ) : ℂ) * L'.H x c = ∫ x, ((pd φ μ x : ℝ) : ℂ) * L.H x c :=
      integral_congr_on Q.isOpen.measurableSet (fun x hx => by simp [test_pd_eq_zero_off hφ μ hx])
        (hL.H.mono fun x hx => by rw [hx])
    rw [e1, e2]; exact h.covgrad_weak μ c φ hφ

/-- **Reduced convergence restricts to sub-boxes.** -/
theorem ReducedConvergence.mono {Q Q' : ChartBox T} (hQ : Q.set ⊆ Q'.set)
    {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C}
    {θ₀ : CoefficientBank Ysec} (h : ReducedConvergence Q' z θ L θ₀) :
    ReducedConvergence Q z θ L θ₀ := by
  obtain ⟨Ke, hKe, hKn, hKL⟩ := h.coframe_chart
  have hae : ∀ {P : E4 → Prop}, (∀ᵐ x ∂Q'.μ, P x) → ∀ᵐ x ∂Q.μ, P x := fun hP =>
    ae_restrict_of_ae_restrict_of_subset hQ hP
  exact
    { coframe_chart := ⟨Ke, hKe, fun n => hae (hKn n), hae hKL⟩
      coframe_mem := h.coframe_mem.mono_box hQ
      coframe_tendsto := h.coframe_tendsto.mono_box hQ
      conn_lie := hae h.conn_lie
      conn_mem := h.conn_mem.mono_measure (Measure.restrict_mono hQ le_rfl)
      conn_tendsto := h.conn_tendsto.mono_box hQ
      curv_mem := h.curv_mem.mono_measure (Measure.restrict_mono hQ le_rfl)
      curv_weak := fun μ ν i j φ hφ => h.curv_weak μ ν i j φ (hφ.mono hQ)
      curv_tendsto := h.curv_tendsto.mono_box hQ
      higgs_mem := h.higgs_mem.mono_measure (Measure.restrict_mono hQ le_rfl)
      higgs_tendsto := h.higgs_tendsto.mono_box hQ
      covgrad_mem := h.covgrad_mem.mono_measure (Measure.restrict_mono hQ le_rfl)
      covgrad_weak := fun μ c φ hφ => h.covgrad_weak μ c φ (hφ.mono hQ)
      covgrad_tendsto := h.covgrad_tendsto.mono_box hQ
      spinor_weak := h.spinor_weak.mono_box hQ
      cospinor_weak := h.cospinor_weak.mono_box hQ
      bank_compact := h.bank_compact
      bank_tendsto := h.bank_tendsto }

/-- **Reduced convergence passes to subsequences.** -/
theorem ReducedConvergence.comp {Q : ChartBox T} {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C} {θ₀ : CoefficientBank Ysec}
    (h : ReducedConvergence Q z θ L θ₀) {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) :
    ReducedConvergence Q (fun k => z (ψ k)) (fun k => θ (ψ k)) L θ₀ := by
  obtain ⟨Ke, hKe, hKn, hKL⟩ := h.coframe_chart
  obtain ⟨P, hP, hθP⟩ := h.bank_compact
  exact
    { coframe_chart := ⟨Ke, hKe, fun k => hKn _, hKL⟩
      coframe_mem := h.coframe_mem
      coframe_tendsto := h.coframe_tendsto.comp hψ
      conn_lie := h.conn_lie
      conn_mem := h.conn_mem
      conn_tendsto := h.conn_tendsto.comp hψ
      curv_mem := h.curv_mem
      curv_weak := h.curv_weak
      curv_tendsto := h.curv_tendsto.comp hψ
      higgs_mem := h.higgs_mem
      higgs_tendsto := h.higgs_tendsto.comp hψ
      covgrad_mem := h.covgrad_mem
      covgrad_weak := h.covgrad_weak
      covgrad_tendsto := h.covgrad_tendsto.comp hψ
      spinor_weak := h.spinor_weak.comp hψ
      cospinor_weak := h.cospinor_weak.comp hψ
      bank_compact := ⟨P, hP, fun k => hθP _⟩
      bank_tendsto := h.bank_tendsto.comp hψ }

/-- Replace the limiting bank by another limit of the same banks. -/
theorem ReducedConvergence.with_bank {Q : ChartBox T} {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C} {θ₀ θ₁ : CoefficientBank Ysec}
    (h : ReducedConvergence Q z θ L θ₀) (hθ : BankTendsto θ θ₁) :
    ReducedConvergence Q z θ L θ₁ :=
  { h with bank_tendsto := hθ }

/-- **Limits in the reduced topology are unique a.e.** on the chart. -/
theorem ReducedConvergence.unique {Q : ChartBox T} {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} {L L' : LimitFields C} {θ₀ θ₀' : CoefficientBank Ysec}
    (h : ReducedConvergence Q z θ L θ₀) (h' : ReducedConvergence Q z θ L' θ₀') :
    LimitFields.AEEqOn Q L L' := by
  have hcl := Q.isCompact_closure
  have hsub := Q.closure_subset_cylSlab
  have hm : ∀ {F : Type} [NormedAddCommGroup F] {f : E4 → F} (p : ℝ≥0∞),
      ContinuousOn f (cylSlab T) → MemLp f p Q.μ := fun p hf =>
    memLp_of_continuousOn_closure Q.isOpen hcl (hf.mono hsub) p
  have hcf : ∀ n, MemH1 Q (coframeC (z n).z.e) (coframeGrad (z n).z.e) := fun n =>
    memH1_coframe_of_smooth Q hcl hsub (z n).smooth_e
  -- coframes and their gradients, componentwise
  have hval : Tendsto (fun n => eLpNorm (coframeC (z n).z.e - coframeC L.e) 2 Q.μ) atTop
      (𝓝 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        h.coframe_tendsto (fun n => zero_le) fun n => le_self_add
  have hval' : Tendsto (fun n => eLpNorm (coframeC (z n).z.e - coframeC L'.e) 2 Q.μ) atTop
      (𝓝 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        h'.coframe_tendsto (fun n => zero_le) fun n => le_self_add
  have hgr : Tendsto (fun n => eLpNorm (coframeGrad (z n).z.e - L.de) 2 Q.μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h.coframe_tendsto
      (fun n => zero_le) fun n => le_add_self
  have hgr' : Tendsto (fun n => eLpNorm (coframeGrad (z n).z.e - L'.de) 2 Q.μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h'.coframe_tendsto
      (fun n => zero_le) fun n => le_add_self
  have hC : coframeC L.e =ᵐ[Q.μ] coframeC L'.e := ae_eq_of_comp fun p =>
    ae_eq_of_tendsto_two (p := 2) (by norm_num) (fun n => (hcf n p).memLp.1)
      (h.coframe_mem p).memLp.1 (h'.coframe_mem p).memLp.1
      (tendsto_eLpNorm_apply hval p) (tendsto_eLpNorm_apply hval' p)
  have hD : L.de =ᵐ[Q.μ] L'.de := by
    have hc : ∀ i (p : Fin 4 × Fin 4), (fun x => L.de x i p) =ᵐ[Q.μ] fun x => L'.de x i p :=
      fun i p => ae_eq_of_tendsto_two (p := 2) (by norm_num)
        (fun n => ((hcf n p).memLp_grad i).1) ((h.coframe_mem p).memLp_grad i).1
        ((h'.coframe_mem p).memLp_grad i).1
        (tendsto_eLpNorm_apply (u := fun n x => coframeGrad (z n).z.e x i)
          (tendsto_eLpNorm_apply hgr i) p)
        (tendsto_eLpNorm_apply (u := fun n x => coframeGrad (z n).z.e x i)
          (tendsto_eLpNorm_apply hgr' i) p)
    have := ae_all_iff.mpr fun i => ae_all_iff.mpr (hc i)
    filter_upwards [this] with x hx
    exact funext fun i => funext fun p => hx i p
  have hE : L.e =ᵐ[Q.μ] L'.e := hC.mono fun x hx => by
    funext a μ
    have := congrFun hx (a, μ)
    simpa [coframeC] using this
  have hΨ := h.spinor_weak.unique h'.spinor_weak
  have hΨb := h.cospinor_weak.unique h'.cospinor_weak
  have hspin : ∀ {Ψ Ψ' : E4 → SpinorFibre C}, spinorC Ψ =ᵐ[Q.μ] spinorC Ψ' → Ψ =ᵐ[Q.μ] Ψ' :=
    fun h => h.mono fun x hx => by
      funext s c
      exact congrFun hx (s, c)
  exact
    { e := hE
      de := hD
      A := ae_eq_of_tendsto_two (p := 4) (by norm_num)
        (fun n => (hm 4 (z n).smooth_A.continuousOn).1) h.conn_mem.1 h'.conn_mem.1
        h.conn_tendsto h'.conn_tendsto
      F := ae_eq_of_tendsto_two (p := 2) (by norm_num)
        (fun n => (hm 2 (continuousOn_curvatureF (z n).smooth_A)).1) h.curv_mem.1 h'.curv_mem.1
        h.curv_tendsto h'.curv_tendsto
      H := ae_eq_of_tendsto_two (p := 2) (by norm_num)
        (fun n => (hm 2 (z n).smooth_H.continuousOn).1) h.higgs_mem.1 h'.higgs_mem.1
        h.higgs_tendsto h'.higgs_tendsto
      K := ae_eq_of_tendsto_two (p := 2) (by norm_num)
        (fun n => (hm 2 (continuousOn_covDerivHiggs (z n).smooth_A (z n).smooth_H)).1)
        h.covgrad_mem.1 h'.covgrad_mem.1 h.covgrad_tendsto h'.covgrad_tendsto
      Ψ := hspin hΨ.1
      dΨ := hΨ.2
      Ψb := hspin hΨb.1
      dΨb := hΨb.2 }

end ReducedOps

/-! ### Tails -/

section Tail

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {Ysec : Type} [Fintype Ysec]

theorem IsCompactCoframeSet.union {K₁ K₂ : Set CoframeFibre} (h₁ : IsCompactCoframeSet K₁)
    (h₂ : IsCompactCoframeSet K₂) : IsCompactCoframeSet (K₁ ∪ K₂) :=
  ⟨h₁.1.union h₂.1, union_subset h₁.2 h₂.2⟩

/-- **Reduced convergence from a tail**: reduced convergence of a shifted sequence, together with
the reduced certificate for the whole sequence, gives reduced convergence of the whole
sequence. -/
theorem ReducedConvergence.of_tail {Q : ChartBox T} {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C} {θ₀ : CoefficientBank Ysec} (m : ℕ)
    (h : ReducedConvergence Q (fun k => z (k + m)) (fun k => θ (k + m)) L θ₀)
    (hc : ReducedCertificate Q z θ) : ReducedConvergence Q z θ L θ₀ := by
  obtain ⟨Ke, hKe, -, hKL⟩ := h.coframe_chart
  obtain ⟨Ke', hKe', hKn'⟩ := hc.coframe_chart
  have sh : ∀ {f : ℕ → ℝ≥0∞}, Tendsto (fun k => f (k + m)) atTop (𝓝 0) →
      Tendsto f atTop (𝓝 0) := fun hf => (tendsto_add_atTop_iff_nat m).mp hf
  have shw : ∀ {u : ℕ → E4 → Fin 4 × C → ℂ} {g : ℕ → E4 → Fin 4 → Fin 4 × C → ℂ}
      {u₀ g₀}, (∀ n, MemH1 Q (u n) (g n)) → H1Bounded Q u g →
      WeakH1Tendsto Q (fun k => u (k + m)) (fun k => g (k + m)) u₀ g₀ →
      WeakH1Tendsto Q u g u₀ g₀ := fun hm hb hw =>
    ⟨hm, hw.2.1, hb, fun φ hφ c => (tendsto_add_atTop_iff_nat m).mp (hw.2.2.2.1 φ hφ c),
      fun φ hφ i c => (tendsto_add_atTop_iff_nat m).mp (hw.2.2.2.2 φ hφ i c)⟩
  exact
    { coframe_chart := ⟨Ke ∪ Ke', hKe.union hKe', fun n => (hKn' n).mono fun x hx => Or.inr hx,
        hKL.mono fun x hx => Or.inl hx⟩
      coframe_mem := h.coframe_mem
      coframe_tendsto := sh h.coframe_tendsto
      conn_lie := h.conn_lie
      conn_mem := h.conn_mem
      conn_tendsto := sh h.conn_tendsto
      curv_mem := h.curv_mem
      curv_weak := h.curv_weak
      curv_tendsto := sh h.curv_tendsto
      higgs_mem := h.higgs_mem
      higgs_tendsto := sh h.higgs_tendsto
      covgrad_mem := h.covgrad_mem
      covgrad_weak := h.covgrad_weak
      covgrad_tendsto := sh h.covgrad_tendsto
      spinor_weak := shw (fun n => memH1_spinor_of_smooth Q (z n).smooth_Ψ) hc.spinor_bounded
        h.spinor_weak
      cospinor_weak := shw (fun n => memH1_spinor_of_smooth Q (z n).smooth_Ψb)
        hc.cospinor_bounded h.cospinor_weak
      bank_compact := hc.bank_compact
      bank_tendsto := (tendsto_add_atTop_iff_nat m).mp h.bank_tendsto }

end Tail

/-! ### The slab exhaustion -/

section Exhaustion

variable {T : ℝ}

theorem slabExh_bounds (hT : 0 < T) (m : ℕ) :
    0 < T / (m + 3) ∧ T / (m + 3) < T - T / (m + 3) ∧ T - T / (m + 3) < T := by
  have h3 : (0 : ℝ) < m + 3 := by positivity
  have hpos : 0 < T / (m + 3) := div_pos hT h3
  refine ⟨hpos, ?_, by linarith⟩
  have : T / (m + 3) * 2 < T := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ h3]
    have : (2 : ℝ) < m + 3 := by have := m.cast_nonneg (α := ℝ); linarith
    nlinarith
  linarith

/-- The exhausting slabs `(T/(m+3), T - T/(m+3)) × (0,1)³`. -/
def slabExh (hT : 0 < T) (m : ℕ) : ChartBox T :=
  slabChart (T / (m + 3)) (T - T / (m + 3)) (slabExh_bounds hT m).1 (slabExh_bounds hT m).2.1
    (slabExh_bounds hT m).2.2

theorem slabChart_subset {t₀ t₁ s₀ s₁ : ℝ} {h0 : 0 < t₀} {h01 : t₀ < t₁} {h1 : t₁ < T}
    {k0 : 0 < s₀} {k01 : s₀ < s₁} {k1 : s₁ < T} (hs : s₀ ≤ t₀) (ht : t₁ ≤ s₁) :
    (slabChart t₀ t₁ h0 h01 h1 (T := T)).set ⊆ (slabChart s₀ s₁ k0 k01 k1 (T := T)).set := by
  intro x hx
  obtain ⟨hx0, hxi⟩ := mem_slabChart.mp hx
  exact mem_slabChart.mpr ⟨⟨hs.trans_lt hx0.1, hx0.2.trans_le ht⟩, hxi⟩

theorem slabExh_mono (hT : 0 < T) {m m' : ℕ} (h : m ≤ m') :
    (slabExh hT m).set ⊆ (slabExh hT m').set := by
  have h3 : (0 : ℝ) < m + 3 := by positivity
  have hle : T / (m' + 3) ≤ T / (m + 3) :=
    div_le_div_of_nonneg_left hT.le h3 (by exact_mod_cast (by omega : m + 3 ≤ m' + 3))
  exact slabChart_subset hle (by linarith)

/-- Every slab box lies in some exhausting slab. -/
theorem exists_slabExh (hT : 0 < T) {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) :
    ∃ m, (slabChart t₀ t₁ h0 h01 h1 (T := T)).set ⊆ (slabExh hT m).set := by
  have hδ : 0 < min t₀ (T - t₁) := lt_min h0 (by linarith)
  obtain ⟨m, hm⟩ := exists_nat_gt (T / min t₀ (T - t₁))
  have h3 : (0 : ℝ) < m + 3 := by positivity
  have hle : T / (m + 3) ≤ min t₀ (T - t₁) := by
    rw [div_le_iff₀ h3]
    rw [div_lt_iff₀ hδ] at hm
    nlinarith [min_le_left t₀ (T - t₁)]
  exact ⟨m, slabChart_subset (hle.trans (min_le_left _ _))
    (by linarith [min_le_right t₀ (T - t₁)])⟩

end Exhaustion

/-! ### Diagonal extraction and the patched limit -/

section Diagonal

variable {T : ℝ}

/-- A strictly increasing sequence whose tail lies in the range of a strictly increasing `F` is a
subsequence of `F` along its tail. -/
theorem exists_strictMono_of_range {F D : ℕ → ℕ} (hF : StrictMono F) (hD : StrictMono D) (m : ℕ)
    (h : ∀ k, D (k + m) ∈ range F) : ∃ χ : ℕ → ℕ, StrictMono χ ∧ ∀ k, D (k + m) = F (χ k) := by
  choose χ hχ using h
  refine ⟨χ, fun a b hab => ?_, fun k => (hχ k).symm⟩
  have : F (χ a) < F (χ b) := by rw [hχ a, hχ b]; exact hD (by omega)
  exact hF.lt_iff_lt.mp this

/-- Patching: if `f j = f m` a.e. on `Q j` for all `j ≤ m`, and `k x ≤ m` with `x ∈ Q (k x)` on
`Q m`, then `f (k x) x = f m x` a.e. on `Q m`. -/
theorem patch_ae {X : Type*} (Q : ℕ → ChartBox T) (f : ℕ → E4 → X) (k : E4 → ℕ) (m : ℕ)
    (hk : ∀ x ∈ (Q m).set, k x ≤ m ∧ x ∈ (Q (k x)).set)
    (h : ∀ j ≤ m, ∀ᵐ x ∂(Q j).μ, f j x = f m x) : ∀ᵐ x ∂(Q m).μ, f (k x) x = f m x := by
  have h' : ∀ j, ∀ᵐ x, j ≤ m → x ∈ (Q j).set → f j x = f m x := by
    intro j
    by_cases hj : j ≤ m
    · filter_upwards [(ae_restrict_iff' (Q j).isOpen.measurableSet).mp (h j hj)] with x hx _ hxj
      exact hx hxj
    · exact Eventually.of_forall fun x hj' => absurd hj' hj
  have hall := ae_all_iff.mpr h'
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem (Q m).isOpen.measurableSet] with x hx hxm
  obtain ⟨hkm, hxk⟩ := hk x hxm
  exact hx (k x) hkm hxk

variable {C : Type} [Fintype C] {left : C → Bool} {Ysec : Type} [Fintype Ysec]

/-- **Diagonal extraction over the slab exhaustion.**  If the reduced certificate holds on every
exhausting slab, every subsequence has a further subsequence and one limit `L`, `θ₀` with reduced
convergence on every exhausting slab. -/
theorem exists_diagonal_reducedConvergence (hT : 0 < T) {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} (hcert : ∀ m, ReducedCertificate (slabExh hT m) z θ)
    (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields C) (θ₀ : CoefficientBank Ysec),
      ∀ m, ReducedConvergence (slabExh hT m) (fun k => z (ns (ψ k))) (fun k => θ (ns (ψ k)))
        L θ₀ := by
  set Q := slabExh hT with hQdef
  have step : ∀ m (Φ : ℕ → ℕ), StrictMono Φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ (L : LimitFields C) (θ₀ : CoefficientBank Ysec),
        ReducedConvergence (Q m) (fun k => z (ns (Φ (ψ k)))) (fun k => θ (ns (Φ (ψ k)))) L θ₀ :=
    fun m Φ hΦ => (hcert m).exists_reducedConvergence (ns ∘ Φ) (hns.comp hΦ)
  choose ψ hψ Lc θc hRC using step
  -- the nested subsequences
  let Φ : ℕ → {f : ℕ → ℕ // StrictMono f} := fun m => Nat.rec
    ⟨ψ 0 id strictMono_id, hψ 0 id strictMono_id⟩
    (fun m F => ⟨F.1 ∘ ψ (m + 1) F.1 F.2, F.2.comp (hψ _ _ _)⟩) m
  have hΦ0 : (Φ 0).1 = ψ 0 id strictMono_id := rfl
  have hΦs : ∀ m, (Φ (m + 1)).1 = (Φ m).1 ∘ ψ (m + 1) (Φ m).1 (Φ m).2 := fun m => rfl
  -- reduced convergence along each nested subsequence
  have hRCm : ∀ m, ∃ (L : LimitFields C) (θ₀ : CoefficientBank Ysec),
      ReducedConvergence (Q m) (fun k => z (ns ((Φ m).1 k))) (fun k => θ (ns ((Φ m).1 k))) L θ₀ := by
    intro m
    cases m with
    | zero => exact ⟨_, _, hRC 0 id strictMono_id⟩
    | succ m => exact ⟨_, _, hRC (m + 1) (Φ m).1 (Φ m).2⟩
  choose Lm θm hLm using hRCm
  -- the diagonal
  set D : ℕ → ℕ := fun k => (Φ k).1 k with hD
  have hDs : StrictMono D := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    show (Φ k).1 k < (Φ (k + 1)).1 (k + 1)
    rw [hΦs k]
    exact (Φ k).2.lt_iff_lt.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self k)
      ((hψ (k + 1) (Φ k).1 (Φ k).2).id_le (k + 1)))
  have hrange : ∀ m k, m ≤ k → range (Φ k).1 ⊆ range (Φ m).1 := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih =>
      rw [hΦs k]
      exact (range_comp_subset_range _ _).trans ih
  have hRCD : ∀ m, ReducedConvergence (Q m) (fun k => z (ns (D k))) (fun k => θ (ns (D k)))
      (Lm m) (θm m) := by
    intro m
    obtain ⟨χ, hχ, hχD⟩ := exists_strictMono_of_range (Φ m).2 hDs m
      (fun k => hrange m (k + m) (by omega) ⟨k + m, rfl⟩)
    have h1 := (hLm m).comp hχ.tendsto_atTop
    have h2 : ReducedConvergence (Q m) (fun k => z (ns (D (k + m))))
        (fun k => θ (ns (D (k + m)))) (Lm m) (θm m) := by
      simpa only [hχD] using h1
    exact h2.of_tail m ((hcert m).comp (hns.comp hDs))
  -- a common bank limit
  have hRCD' : ∀ m, ReducedConvergence (Q m) (fun k => z (ns (D k))) (fun k => θ (ns (D k)))
      (Lm m) (θm 0) := fun m => (hRCD m).with_bank (hRCD 0).bank_tendsto
  -- agreement on overlaps
  have hagree : ∀ j m, j ≤ m → LimitFields.AEEqOn (Q j) (Lm j) (Lm m) := fun j m hjm =>
    (hRCD' j).unique ((hRCD' m).mono (slabExh_mono hT hjm))
  -- the patched limit
  classical
  set kf : E4 → ℕ := fun x => if h : ∃ m, x ∈ (Q m).set then Nat.find h else 0 with hkf
  have hk : ∀ m, ∀ x ∈ (Q m).set, kf x ≤ m ∧ x ∈ (Q (kf x)).set := by
    intro m x hx
    have hex : ∃ m, x ∈ (Q m).set := ⟨m, hx⟩
    simp only [hkf, dite_eq_ite, hex]
    exact ⟨Nat.find_min' hex hx, Nat.find_spec hex⟩
  let L : LimitFields C :=
    ⟨fun x => (Lm (kf x)).e x, fun x => (Lm (kf x)).de x, fun x => (Lm (kf x)).A x,
      fun x => (Lm (kf x)).F x, fun x => (Lm (kf x)).H x, fun x => (Lm (kf x)).K x,
      fun x => (Lm (kf x)).Ψ x, fun x => (Lm (kf x)).dΨ x, fun x => (Lm (kf x)).Ψb x,
      fun x => (Lm (kf x)).dΨb x⟩
  have hpatch : ∀ m, LimitFields.AEEqOn (Q m) (Lm m) L := fun m =>
    { e := (patch_ae Q (fun j => (Lm j).e) kf m (hk m) fun j hj => (hagree j m hj).e).mono fun _ hx => hx.symm
      de := (patch_ae Q (fun j => (Lm j).de) kf m (hk m) fun j hj => (hagree j m hj).de).mono fun _ hx => hx.symm
      A := (patch_ae Q (fun j => (Lm j).A) kf m (hk m) fun j hj => (hagree j m hj).A).mono fun _ hx => hx.symm
      F := (patch_ae Q (fun j => (Lm j).F) kf m (hk m) fun j hj => (hagree j m hj).F).mono fun _ hx => hx.symm
      H := (patch_ae Q (fun j => (Lm j).H) kf m (hk m) fun j hj => (hagree j m hj).H).mono fun _ hx => hx.symm
      K := (patch_ae Q (fun j => (Lm j).K) kf m (hk m) fun j hj => (hagree j m hj).K).mono fun _ hx => hx.symm
      Ψ := (patch_ae Q (fun j => (Lm j).Ψ) kf m (hk m) fun j hj => (hagree j m hj).Ψ).mono fun _ hx => hx.symm
      dΨ := (patch_ae Q (fun j => (Lm j).dΨ) kf m (hk m) fun j hj => (hagree j m hj).dΨ).mono fun _ hx => hx.symm
      Ψb := (patch_ae Q (fun j => (Lm j).Ψb) kf m (hk m) fun j hj => (hagree j m hj).Ψb).mono fun _ hx => hx.symm
      dΨb := (patch_ae Q (fun j => (Lm j).dΨb) kf m (hk m) fun j hj =>
        (hagree j m hj).dΨb).mono fun _ hx => hx.symm }
  exact ⟨D, hDs, L, θm 0, fun m => (hRCD' m).congr_ae (hpatch m)⟩

end Diagonal

/-! ### The Higgs endpoint in the reduced class: strong `H¹ ∩ L⁴` -/

section HiggsStrong

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {Ysec : Type} [Fintype Ysec]

/-- The ordinary gradient `∂H = D_AH - ρ_H(A)H` forced on the limit Higgs field. -/
def higgsLimitGrad (L : LimitFields C) : E4 → Fin 4 → HiggsFibre :=
  fun x i c => L.K x i c - higgsAct (L.A x i) (L.H x) c

/-- Strong `H¹ ∩ L⁴` convergence of the Higgs fields, with limiting gradient `D_AH - ρ_H(A)H`. -/
def HiggsH1L4Convergence (Q : ChartBox T) (z : ℕ → SmoothFields T left) (L : LimitFields C) :
    Prop :=
  MemH1 Q L.H (higgsLimitGrad L) ∧
    H1Tendsto Q (fun k => (z k).z.H) (fun k => higgsGrad (z k).z.H) L.H (higgsLimitGrad L) ∧
    MemLp L.H 4 Q.μ ∧ LpTendsto 4 Q.μ (fun k => (z k).z.H) L.H

/-- **`prop:covariant-higgs-endpoint` in the reduced class**: reduced convergence on a chart box
upgrades the Higgs convergence to strong `H¹(Q) ∩ L⁴(Q)`, with limiting ordinary gradient
`D_AH - ρ_H(A)H`. -/
theorem ReducedConvergence.higgs_strong {Q : ChartBox T} {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C} {θ₀ : CoefficientBank Ysec}
    (h : ReducedConvergence Q z θ L θ₀) : HiggsH1L4Convergence Q z L := by
  have hcl := Q.isCompact_closure
  have hsub := Q.closure_subset_cylSlab
  have hW : ∀ n c, MemW12 Q.set (fun x => (z n).z.H x c) (fun i x => pd (z n).z.H i x c) :=
    fun n c => memW12_higgs_of_smooth Q hcl hsub (z n).smooth_H c
  have hAm : ∀ n, MemLp (z n).z.A 4 Q.μ := fun n =>
    memLp_of_continuousOn_closure Q.isOpen hcl ((z n).smooth_A.continuousOn.mono hsub) 4
  have hH4 : ∀ n, MemLp (z n).z.H 4 Q.μ := fun n =>
    memLp_of_continuousOn_closure Q.isOpen hcl ((z n).smooth_H.continuousOn.mono hsub) 4
  obtain ⟨hL4m, hL4t⟩ := higgs_L4_tendsto Q hW hH4 hAm h.conn_mem h.conn_tendsto h.higgs_mem
    h.higgs_tendsto h.covgrad_mem h.covgrad_tendsto
  have hAc : ∀ n μ (c e : Fin 2), MemLp (fun x => (z n).z.A x μ (Fin.natAdd 3 c)
      (Fin.natAdd 3 e)) 4 Q.μ := fun n μ c e =>
    memLp_pi_iff.mp (memLp_pi_iff.mp (memLp_pi_iff.mp (hAm n) μ) (Fin.natAdd 3 c)) (Fin.natAdd 3 e)
  have hA₀c : ∀ μ (c e : Fin 2), MemLp (fun x => L.A x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e)) 4
      Q.μ := fun μ c e =>
    memLp_pi_iff.mp (memLp_pi_iff.mp (memLp_pi_iff.mp h.conn_mem μ) (Fin.natAdd 3 c))
      (Fin.natAdd 3 e)
  have hAlim : ∀ μ (c e : Fin 2), Tendsto (fun n => eLpNorm
      ((fun x => (z n).z.A x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e)) -
        fun x => L.A x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e)) 4 Q.μ) atTop (𝓝 0) := fun μ c e =>
    tendsto_eLpNorm_apply (u := fun n x => (z n).z.A x μ (Fin.natAdd 3 c))
      (tendsto_eLpNorm_apply (u := fun n x => (z n).z.A x μ)
        (tendsto_eLpNorm_apply h.conn_tendsto μ) (Fin.natAdd 3 c)) (Fin.natAdd 3 e)
  have hHn2 : ∀ n, MemLp (z n).z.H 2 Q.μ := fun n => memLp_pi_iff.mpr fun c => (hW n c).memLp
  obtain ⟨B, hBt, hB⟩ := exists_eLpNorm_bound (by norm_num) hHn2 h.higgs_mem h.higgs_tendsto
  have hYlim : ∀ (c : Fin 2) μ, Tendsto (fun n => eLpNorm
      (SobolevOpen.covD (fun c μ x => pd (z n).z.H μ x c)
        (fun μ c e x => (z n).z.A x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e))
        (fun c x => (z n).z.H x c) c μ - fun x => L.K x μ c) 2 Q.μ) atTop (𝓝 0) := by
    intro c μ
    have h' := tendsto_eLpNorm_apply (u := fun n x => covDerivHiggs (z n).z.A (z n).z.H x μ)
      (tendsto_eLpNorm_apply h.covgrad_tendsto μ) c
    refine h'.congr fun n => ?_
    congr 1
  obtain ⟨h1, h2, -⟩ := SobolevOpen.covariant_higgs_endpoint_box_of_L2 (ι := Fin 4) (by simp)
    Q.lt (fun n c x => (z n).z.H x c) (fun n c μ x => pd (z n).z.H μ x c)
    (fun n μ c e x => (z n).z.A x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e))
    (fun μ c e x => L.A x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e)) (fun c μ x => L.K x μ c)
    hW (fun n μ c e => hAc n μ c e) hA₀c hAlim hBt
    (fun n c => (eLpNorm_apply_le (z n).z.H c 2).trans (hB n))
    (fun c μ => memLp_pi_iff.mp (memLp_pi_iff.mp h.covgrad_mem μ) c) hYlim (fun c x => L.H x c)
    (fun c => memLp_pi_iff.mp h.higgs_mem c) (fun c => tendsto_eLpNorm_apply h.higgs_tendsto c)
  have hmem : MemH1 Q L.H (higgsLimitGrad L) := fun c => h1 c
  have hgrad : LpTendsto 2 Q.μ (fun n => higgsGrad (z n).z.H) (higgsLimitGrad L) := by
    refine tendsto_eLpNorm_of_apply (by norm_num) (fun n μ => ?_) fun μ => ?_
    · have h1' := memLp_pi_iff.mpr fun c => (hW n c).memLp_grad μ
      have h2' := memLp_pi_iff.mpr fun c => (hmem c).memLp_grad μ
      exact h1'.1.sub h2'.1
    · refine tendsto_eLpNorm_of_apply (by norm_num) (fun n c => ((hW n c).memLp_grad μ).1.sub
        ((hmem c).memLp_grad μ).1) fun c => h2 c μ
  exact ⟨hmem, by simpa [H1Tendsto, h1Norm] using h.higgs_tendsto.add hgrad, hL4m, hL4t⟩

end HiggsStrong

/-! ### Test linearity of the limit functionals -/

section Linearity

variable {T : ℝ} {C : Type} [Fintype C]

theorem pd_smul_field {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (c : ℝ) (f : E4 → F)
    (i : Fin 4) (x : E4) : pd (c • f) i x = c • pd f i x := by
  unfold pd
  rw [fderiv_const_smul_field]
  rfl

theorem testJet_smul (c : ℝ) (w : FieldTuple C) (x : E4) :
    testJet (c • w) x = c • testJet w x := by
  have e1 : (c • w).e = c • w.e := rfl
  have e2 : (c • w).A = c • w.A := rfl
  have e3 : (c • w).H = c • w.H := rfl
  have e4 : (c • w).Ψ = c • w.Ψ := rfl
  have e5 : (c • w).Ψb = c • w.Ψb := rfl
  simp only [testJet, e1, e2, e3, e4, e5, pd_smul_field]
  rfl

theorem testJet_zero (x : E4) : testJet (0 : FieldTuple C) x = 0 := by
  have := testJet_smul (0 : ℝ) (0 : FieldTuple C) x
  simpa using this

/-- A functional of the form `v ↦ ∫_Q Λ(x)(testJet v x)` vanishing on the unit ball of `𝒱_K^r`
vanishes identically. -/
theorem jet_functional_eq_zero_of_unit {left : C → Bool} {r : ℕ} {K : CylRegion T}
    {μ : Measure E4} (Λ : E4 → RJet C →L[ℝ] ℝ)
    (h : ∀ v : CrTest left r K, ‖v‖ ≤ 1 → ∫ x, Λ x (testJet v.val x) ∂μ = 0)
    (v : CrTest left r K) : ∫ x, Λ x (testJet v.val x) ∂μ = 0 := by
  by_cases hv : v = 0
  · subst hv
    simp [testJet_zero]
  · have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have h1 := h (‖v‖⁻¹ • v) (by rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hpos.ne'])
    simp only [CrTest.val_smul, testJet_smul, map_smul, smul_eq_mul, integral_const_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (inv_ne_zero hpos.ne')
    · exact h2

end Linearity

/-! ### Distributions on metric tests (`app:palatini`, `eq:stress-definition`) -/

section Distributions

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec) {r : ℕ} {K : CylRegion T}

/-- The pure metric part `(k, 0, 0, 0, 0)` of a physical test `v = (k, a, η_H, η_Ψ, η_Ψ̄)`. -/
def metricTest (v : CrTest FC.left r K) : CrTest FC.left r K :=
  (⟨FieldTuple.mk v.val.e 0 0 0 0, v.val_mem.1, IsCylTest.zero, IsCylTest.zero, IsCylTest.zero,
    IsCylTest.zero, v.val_mem.2.2.2.2.2.1, fun _ _ => smLie.zero_mem, fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl⟩ : ↥(testSubmodule FC.left K))

/-- **The gravitational distribution `(Ein(g) + Λg) dV_g` of `app:palatini`**, on the metric
test `k`: `⟨(Ein(g)+Λg)dV_g, k⟩ = 2κ D𝒮_g[k]`, the gravitational first variation being the
first-order (integrated-by-parts) representative `gravLimitVariation` evaluated on the limit jet
(`app:palatini`: "on smooth metrics the distribution is `(Ein(g)+Λg)dV_g/(2κ)`"). -/
def einsteinDistribution (θ : CoefficientBank Ysec) (Q : ChartBox T) (L : LimitFields FC.C)
    (v : CrTest FC.left r K) : ℝ :=
  2 * θ.kappa * gravLimitVariation FC θ Q L (metricTest FC v)

/-- **The matter stress distribution `T^SM dV_g`** (`eq:stress-definition`,
`D_g𝒮_SM[k] = -½ ∫ T^SM_{μν} k^{μν} dV_g`): `⟨T^SM dV_g, k⟩ = -2 D_g𝒮_SM[k]`, the complete
(Yang–Mills + Higgs + Dirac–Yukawa, spin-connection chain included) matter metric first variation
of the limit fields. -/
def stressDistribution (θ : CoefficientBank Ysec) (Q : ChartBox T) (L : LimitFields FC.C)
    (v : CrTest FC.left r K) : ℝ :=
  -2 * smLimitVariation FC θ Q L (metricTest FC v)

end Distributions

/-! ### Yukawa continuity of the fermion carrier -/

/-- The carrier's Yukawa map depends continuously on the coefficient bank (in the manuscript the
Yukawa/Majorana map is a fixed linear function of the bank's Yukawa matrices; the carrier
encoding leaves this dependence abstract, so its continuity is stated). -/
def FermionCarrier.YukawaContinuous {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec) :
    Prop :=
  ∀ (θ : ℕ → CoefficientBank Ysec) (θ₀ : CoefficientBank Ysec), BankTendsto θ θ₀ →
    Tendsto (fun n => yukL FC (θ n)) atTop (𝓝 (yukL FC θ₀)) ∧
      Tendsto (fun n => FC.yukawa (θ n) 0) atTop (𝓝 (FC.yukawa θ₀ 0))

theorem trivialCarrier_yukawaContinuous (Ysec : Type) [Fintype Ysec] :
    (trivialCarrier Ysec).YukawaContinuous := by
  intro θ θ₀ _
  have h1 : ∀ θ, yukL (trivialCarrier Ysec) θ = 0 := fun θ => by
    ext h c c'
    simp [yukL, trivialCarrier]
    rfl
  simp only [h1]
  exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩

/-! ### The Euler identities of the limit -/

section Euler

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec}

/-- Defect bounds for a single test of norm `≤ 1`. -/
theorem RegulatorSequence.defect_bounds (reg : RegulatorSequence T FC) (n : ℕ) (K : CylRegion T)
    (v : CrTest FC.left reg.r0 K) (hv : ‖v‖ ≤ 1) :
    ENNReal.ofReal |(firstVariation T FC (reg.bank n) .gravity (reg.fields n).z v.val +
        firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z v.val) -
      fderiv ℝ (reg.iface n).action (reg.config n) (reg.lift n K v)| ≤
        reg.consistencyDefect n K ∧
    ENNReal.ofReal |fderiv ℝ (reg.iface n).action (reg.config n) (reg.lift n K v)| ≤
        reg.stationarityDefect n K := by
  have hv' : testNorm reg.r0 (v : ↥(testSubmodule FC.left K)).1 ≤ 1 := hv
  have hb : ∀ b : Sector, ENNReal.ofReal |reg.finiteSectorVariation n b (reg.lift n K v) -
      firstVariation T FC (reg.bank n) b (reg.fields n).z v.val| ≤
      ⨆ (w : ↥(testSubmodule FC.left K)) (_ : testNorm reg.r0 w.1 ≤ 1),
        ENNReal.ofReal |reg.finiteSectorVariation n b (reg.lift n K w) -
          firstVariation T FC (reg.bank n) b (reg.fields n).z w.1| := fun b =>
    le_iSup₂ (f := fun (w : ↥(testSubmodule FC.left K)) (_ : testNorm reg.r0 w.1 ≤ 1) =>
      ENNReal.ofReal |reg.finiteSectorVariation n b (reg.lift n K w) -
        firstVariation T FC (reg.bank n) b (reg.fields n).z w.1|) (v : ↥(testSubmodule FC.left K))
      hv'
  refine ⟨?_, le_iSup₂ (f := fun (w : ↥(testSubmodule FC.left K))
    (_ : testNorm reg.r0 w.1 ≤ 1) => ENNReal.ofReal |fderiv ℝ (reg.iface n).action
      (reg.config n) (reg.lift n K w)|) (v : ↥(testSubmodule FC.left K)) hv'⟩
  rw [reg.fderiv_action_eq_sum]
  calc ENNReal.ofReal |(firstVariation T FC (reg.bank n) .gravity (reg.fields n).z v.val +
          firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z v.val) -
        (reg.finiteSectorVariation n .gravity (reg.lift n K v) +
          reg.finiteSectorVariation n .standardModel (reg.lift n K v))|
      ≤ ENNReal.ofReal (|reg.finiteSectorVariation n .gravity (reg.lift n K v) -
            firstVariation T FC (reg.bank n) .gravity (reg.fields n).z v.val| +
          |reg.finiteSectorVariation n .standardModel (reg.lift n K v) -
            firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z v.val|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [abs_sub_comm (reg.finiteSectorVariation n .gravity _),
          abs_sub_comm (reg.finiteSectorVariation n .standardModel _)]
        refine le_trans (le_of_eq ?_) (abs_add_le _ _)
        congr 1; ring
    _ ≤ _ := by
        rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        unfold RegulatorSequence.consistencyDefect
        have : (Finset.univ : Finset Sector) = {Sector.gravity, Sector.standardModel} := rfl
        rw [this, Finset.sum_pair (by decide)]
        exact add_le_add (hb .gravity) (hb .standardModel)

/-- **Distributional Euler identities of the limit** (the closure step of `thm:reduced-closure`,
`eq:reduced-residual-bound`): if along a subsequence the complete reconstructed first variations
converge in the dual norm of `𝒱_K^{r₀}` to a functional `ℓ`, and `c_h(K) → 0`, `ε_h(K) → 0`,
then `ℓ = 0` on the unit ball. -/
theorem limit_eq_zero_of_defects (reg : RegulatorSequence T FC) {σ : ℕ → ℕ}
    (hσ : Tendsto σ atTop atTop) (K : CylRegion T) (hcons : reg.FirstVariationConsistent)
    (hstat : reg.PhysicallyStationary) (ℓ : CrTest FC.left reg.r0 K → ℝ)
    (hconv : ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v : CrTest FC.left reg.r0 K,
      |(firstVariation T FC (reg.bank (σ k)) .gravity (reg.fields (σ k)).z v.val +
          firstVariation T FC (reg.bank (σ k)) .standardModel (reg.fields (σ k)).z v.val) -
        ℓ v| ≤ ε * ‖v‖)
    (v : CrTest FC.left reg.r0 K) (hv : ‖v‖ ≤ 1) : ℓ v = 0 := by
  refine abs_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_) (abs_nonneg _))
  have hδ3 : 0 < δ / 3 := by positivity
  have hc := ((hcons K).comp hσ).eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ3))
  have hs := ((hstat K).comp hσ).eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ3))
  obtain ⟨k, hk1, hk2, hk3⟩ := ((hconv (δ / 3) hδ3).and (hc.and hs)).exists
  obtain ⟨b1, b2⟩ := reg.defect_bounds (σ k) K v hv
  have e1 : |(firstVariation T FC (reg.bank (σ k)) .gravity (reg.fields (σ k)).z v.val +
      firstVariation T FC (reg.bank (σ k)) .standardModel (reg.fields (σ k)).z v.val) -
      fderiv ℝ (reg.iface (σ k)).action (reg.config (σ k)) (reg.lift (σ k) K v)| < δ / 3 :=
    (ENNReal.ofReal_lt_ofReal_iff hδ3).mp (b1.trans_lt hk2)
  have e2 : |fderiv ℝ (reg.iface (σ k)).action (reg.config (σ k)) (reg.lift (σ k) K v)| <
      δ / 3 := (ENNReal.ofReal_lt_ofReal_iff hδ3).mp (b2.trans_lt hk3)
  have e3 := (hk1 v).trans (mul_le_of_le_one_right hδ3.le hv)
  have := abs_sub_le (ℓ v) ((firstVariation T FC (reg.bank (σ k)) .gravity
    (reg.fields (σ k)).z v.val + firstVariation T FC (reg.bank (σ k)) .standardModel
    (reg.fields (σ k)).z v.val)) 0
  rw [abs_sub_comm] at e3
  have h4 := abs_sub_le ((firstVariation T FC (reg.bank (σ k)) .gravity (reg.fields (σ k)).z v.val +
    firstVariation T FC (reg.bank (σ k)) .standardModel (reg.fields (σ k)).z v.val))
    (fderiv ℝ (reg.iface (σ k)).action (reg.config (σ k)) (reg.lift (σ k) K v)) 0
  simp only [sub_zero] at this h4
  linarith

end Euler

/-! ### Homogeneity of the limit functionals -/

section Homogeneity

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec) {r : ℕ} {K : CylRegion T}

theorem gravLimitVariation_smul (θ : CoefficientBank Ysec) (Q : ChartBox T)
    (L : LimitFields FC.C) (c : ℝ) (v : CrTest FC.left r K) :
    gravLimitVariation FC θ Q L (c • v) = c * gravLimitVariation FC θ Q L v := by
  simp only [gravLimitVariation, CrTest.val_smul, testJet_smul, map_smul, smul_eq_mul,
    integral_const_mul]

theorem smLimitVariation_smul (θ : CoefficientBank Ysec) (Q : ChartBox T)
    (L : LimitFields FC.C) (c : ℝ) (v : CrTest FC.left r K) :
    smLimitVariation FC θ Q L (c • v) = c * smLimitVariation FC θ Q L v := by
  simp only [smLimitVariation, CrTest.val_smul, testJet_smul, map_smul, smul_eq_mul,
    integral_const_mul]

/-- A homogeneous functional on `𝒱_K^r` vanishing on the unit ball vanishes identically. -/
theorem eq_zero_of_unit_of_homogeneous {left : _} (ℓ : CrTest (C := FC.C) left r K → ℝ)
    (hhom : ∀ (c : ℝ) v, ℓ (c • v) = c * ℓ v) (h : ∀ v, ‖v‖ ≤ 1 → ℓ v = 0) (v) : ℓ v = 0 := by
  by_cases hv : v = 0
  · subst hv
    have := hhom 0 0
    simpa using this
  · have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have h1 := h (‖v‖⁻¹ • v) (by rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hpos.ne'])
    rw [hhom] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (inv_ne_zero hpos.ne')
    · exact h2

end Homogeneity

/-! ### The limiting bank is physical -/

theorem ReducedConvergence.bank_physical {T : ℝ} {C : Type} [Fintype C] {left : C → Bool}
    {Ysec : Type} [Fintype Ysec] {Q : ChartBox T} {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C} {θ₀ : CoefficientBank Ysec}
    (h : ReducedConvergence Q z θ L θ₀) : θ₀ ∈ physicalBanks := by
  obtain ⟨P, ⟨hPc, hPphys⟩, hθP⟩ := h.bank_compact
  obtain ⟨θ₁, hθ₁, heq⟩ : bankCoords θ₀ ∈ bankCoords '' P :=
    hPc.isClosed.mem_of_tendsto h.bank_tendsto
      (Eventually.of_forall fun n => mem_image_of_mem _ (hθP n))
  have hp := hPphys hθ₁
  have e : ∀ k : Fin 7, (bankCoords θ₁).1 k = (bankCoords θ₀).1 k := fun k =>
    congrFun (congrArg Prod.fst heq) k
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := e 0; simp [bankCoords] at this; rw [← this]; exact hp.1
  · have := e 2; simp [bankCoords] at this; rw [← this]; exact hp.2.1
  · have := e 3; simp [bankCoords] at this; rw [← this]; exact hp.2.2.1
  · have := e 4; simp [bankCoords] at this; rw [← this]; exact hp.2.2.2.1
  · have := e 5; simp [bankCoords] at this; rw [← this]; exact hp.2.2.2.2

/-! ### `thm:reduced-closure` -/

section Closure

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec}

/-- **`thm:reduced-closure` (reduced Einstein–Standard-Model variational closure).**  Let `reg` be
a finite-interface regulator sequence (`def:regulator`) satisfying the reduced compactness
certificate (`def:reduced-certificate`, (R1)–(R5)) on every compact chart, first-variation
consistency `c_h(K) → 0` and physical common-action stationarity `ε_h(K) → 0` for every `K`
(the manuscript's hypothesis `L_h√R_h + e_h → 0` gives `ε_h(K) → 0` by `prop:source-bound`), and
let the carrier's Yukawa map depend continuously on the bank.  Then every cutoff subsequence `ns`
has a further subsequence `ns ∘ ψ`, limit fields `z = L` and a limiting physical bank `θ₀` such
that:

1. on every slab chart `(t₀,t₁) × (0,1)³` the reconstructed fields converge in the reduced action
   topology (`ReducedConvergence`: `e_h → e` strongly in `H¹` with values of terms and limit a.e.
   in one compact nondegenerate coframe chart, `A_h → A` in `L⁴`, `F_{A_h} → F_A` in `L²`,
   `H_h → H` and `D_{A_h}H_h → D_AH` in `L²`, `Ψ_h ⇀ Ψ`, `Ψ̄_h ⇀ Ψ̄` weakly in `H¹`, banks
   convergent in the compact physical set), and moreover `H_h → H` strongly in `H¹ ∩ L⁴`;
2. the complete reconstructed first variation converges in `(𝒱_K^{r₀})^*`;
3. the limit is a **distributional solution of all Euler equations**: its complete first variation
   (first-order gravitational representative + Yang–Mills + Higgs + complete Dirac–Yukawa) vanishes
   on every test of every `𝒱_K`;
4. **`eq:reduced-Einstein-limit`**: `(Ein(g) + Λg) dV_g = κ T^SM dV_g` as distributions on metric
   tests (`einsteinDistribution = κ · stressDistribution`). -/
theorem reduced_closure (hT : 0 < T) (reg : RegulatorSequence T FC)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesReducedCertificate Q)
    (hcons : reg.FirstVariationConsistent) (hstat : reg.PhysicallyStationary)
    (hyuk : FC.YukawaContinuous) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec),
      θ₀ ∈ physicalBanks ∧
      (∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
        ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) (fun k => reg.fields (ns (ψ k)))
          (fun k => reg.bank (ns (ψ k))) L θ₀ ∧
        HiggsH1L4Convergence (slabChart t₀ t₁ h0 h01 h1) (fun k => reg.fields (ns (ψ k))) L) ∧
      (∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
        (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) → ∀ ε > (0 : ℝ), ∀ᶠ k in atTop,
          ∀ v : CrTest FC.left reg.r0 K,
            |(firstVariation T FC (reg.bank (ns (ψ k))) .gravity (reg.fields (ns (ψ k))).z v.val +
                firstVariation T FC (reg.bank (ns (ψ k))) .standardModel
                  (reg.fields (ns (ψ k))).z v.val) -
              (gravLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v +
                smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v)| ≤ ε * ‖v‖) ∧
      (∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
        (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) → ∀ v : CrTest FC.left reg.r0 K,
          gravLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v +
            smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v = 0) ∧
      (∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
        (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) → ∀ v : CrTest FC.left reg.r0 K,
          einsteinDistribution FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v =
            θ₀.kappa * stressDistribution FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v) := by
  obtain ⟨ψ, hψ, L, θ₀, hRC⟩ := exists_diagonal_reducedConvergence hT (fun m => hcert _) ns hns
  have hRCs : ∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
      ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) (fun k => reg.fields (ns (ψ k)))
        (fun k => reg.bank (ns (ψ k))) L θ₀ := fun t₀ t₁ h0 h01 h1 => by
    obtain ⟨m, hm⟩ := exists_slabExh hT h0 h01 h1
    exact (hRC m).mono hm
  have hr : 1 ≤ reg.r0 := le_trans (by norm_num) reg.four_le_r0
  have hdual : ∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
      (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) → ∀ ε > (0 : ℝ), ∀ᶠ k in atTop,
        ∀ v : CrTest FC.left reg.r0 K,
          |(firstVariation T FC (reg.bank (ns (ψ k))) .gravity (reg.fields (ns (ψ k))).z v.val +
              firstVariation T FC (reg.bank (ns (ψ k))) .standardModel
                (reg.fields (ns (ψ k))).z v.val) -
            (gravLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v +
              smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v)| ≤ ε * ‖v‖ := by
    intro K t₀ t₁ h0 h01 h1 hK ε hε
    obtain ⟨hyL, hy0⟩ := hyuk _ _ (hRCs t₀ t₁ h0 h01 h1).bank_tendsto
    exact actionVariation_dual_tendsto FC h0 h01 h1 hK hr (hRCs t₀ t₁ h0 h01 h1) hyL hy0 hε
  have heuler : ∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
      (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) → ∀ v : CrTest FC.left reg.r0 K,
        gravLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v +
          smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v = 0 := by
    intro K t₀ t₁ h0 h01 h1 hK
    refine eq_zero_of_unit_of_homogeneous FC (fun v => gravLimitVariation FC θ₀
      (slabChart t₀ t₁ h0 h01 h1) L v + smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L v)
      (fun c v => by
        simp only [gravLimitVariation_smul, smLimitVariation_smul]; ring) ?_
    intro v hv
    exact limit_eq_zero_of_defects reg (hns.comp hψ).tendsto_atTop K hcons hstat _
      (hdual K t₀ t₁ h0 h01 h1 hK) v hv
  refine ⟨ψ, hψ, L, θ₀, (hRCs _ _ (slabExh_bounds hT 0).1 (slabExh_bounds hT 0).2.1
      (slabExh_bounds hT 0).2.2).bank_physical,
    fun t₀ t₁ h0 h01 h1 => ⟨hRCs t₀ t₁ h0 h01 h1, (hRCs t₀ t₁ h0 h01 h1).higgs_strong⟩, hdual,
    heuler, fun K t₀ t₁ h0 h01 h1 hK v => ?_⟩
  have h := heuler K t₀ t₁ h0 h01 h1 hK (metricTest FC v)
  simp only [einsteinDistribution, stressDistribution]
  rw [show gravLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L (metricTest FC v) =
    -smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1) L (metricTest FC v) by linarith]
  ring

end Closure

/-! ### Non-vacuity: the flat regulator satisfies every hypothesis of `reduced_closure` -/

section FlatNonVacuity

variable {T : ℝ}

theorem redJet_flat (n : ℕ) (x : E4) :
    redJet ((flatRegulator T).fields n).z x =
      (RJet.mk flatCoframe 0 0 0 0 0 0 0 0 0 : RJet (trivialCarrier Unit).C) := by
  have hA : curvatureF (0 : E4 → ConnFibre) x = 0 := by rw [curvatureF_zero]; rfl
  have hK : covDerivHiggs (0 : E4 → ConnFibre) (0 : E4 → HiggsFibre) x = 0 := by
    rw [covDerivHiggs_zero]; rfl
  have he : (fun i => pd (fun _ : E4 => flatCoframe) i x) = 0 := funext fun i => pd_const' _ i x
  have hΨ : (fun i => pd (0 : E4 → SpinorFibre (trivialCarrier Unit).C) i x) = 0 :=
    funext fun i => pd_const' (0 : SpinorFibre (trivialCarrier Unit).C) i x
  simp only [redJet, flat_e, flat_A, flat_H, flat_Ψ, flat_Ψb, hA, hK, he, hΨ, Pi.zero_apply]

theorem gravCov_flat (R : RJet (trivialCarrier Unit).C) (he : R.de = 0) :
    gravCov (C := (trivialCarrier Unit).C) physicalBank R = 0 := by
  simp only [gravCov, gravCovF, he, map_zero, zero_apply, zero_add,
    physicalBank]
  simp

theorem smCov_flat (R : RJet (trivialCarrier Unit).C) (hA : R.A = 0) (hF : R.F = 0) (hH : R.H = 0) (hK : R.K = 0)
    (hΨ : R.Ψ = 0) (hΨb : R.Ψb = 0) (hdΨ : R.dΨ = 0) (hdΨb : R.dΨb = 0) :
    bosonCov physicalBank R + diracCov (trivialCarrier Unit) physicalBank R = 0 := by
  have hq : higgsQuad (0 : HiggsFibre) = 0 := by simp [higgsQuad]
  have hpU : pU (trivialCarrier Unit) R = 0 := by
    simp only [pU, ContinuousLinearMap.prod_apply]
    rw [show πΨb R = R.Ψb from rfl, show πΨ R = R.Ψ from rfl, hΨ, hΨb]; rfl
  have hpW : pW (trivialCarrier Unit) R = 0 := by
    simp only [pW, ContinuousLinearMap.prod_apply]
    rw [show πdΨ R = R.dΨ from rfl, show πdΨb R = R.dΨb from rfl, hdΨ, hdΨb]; rfl
  simp only [bosonCov, diracCov, hA, hF, hH, hK, hΨb, hΨ, hpU, hpW, hq, map_zero,
    zero_apply, smul_zero, Finset.sum_const_zero, add_zero, physicalBank,
    sub_zero, ContinuousLinearMap.zero_comp]
  simp

/-- The continuum first variations of the flat fields with the physical bank vanish. -/
theorem firstVariation_flat (hT : 0 < T) (b : Sector) (n : ℕ) (K : CylRegion T)
    (v : ↥(testSubmodule (trivialCarrier Unit).left K)) :
    firstVariation T (trivialCarrier Unit) ((flatRegulator T).bank n) b
      ((flatRegulator T).fields n).z v.1 = 0 := by
  obtain ⟨t₀, t₁, h0, h01, h1, hK⟩ := K.exists_slab_Ioo hT
  have hKe : IsCompact ({flatCoframe} : Set CoframeFibre) := isCompact_singleton
  have hGL : ({flatCoframe} : Set CoframeFibre) ⊆ coframeGL :=
    singleton_subset_iff.mpr (coframeChart_subset_GL flatCoframe_mem_chart)
  have hz : ∀ x ∈ closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set,
      ((flatRegulator T).fields n).z.e x ∈ ({flatCoframe} : Set CoframeFibre) := fun x _ => rfl
  set w : CrTest (trivialCarrier Unit).left 4 K := v
  cases b with
  | gravity =>
    rw [show v.1 = w.val from rfl, gravVariation_eq_cov (trivialCarrier Unit) _ h0 h01 h1 hK _ w
      hKe hGL hz]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [Pi.zero_apply, redJet_flat, flat_bank, gravCov_flat _ rfl]
    rfl
  | standardModel =>
    rw [show v.1 = w.val from rfl, smVariation_eq_cov (trivialCarrier Unit) _ h0 h01 h1
      (fun p hp => Ioo_subset_Icc_self (hK p hp)) _ w hKe hGL hz]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [Pi.zero_apply, redJet_flat, flat_bank, smCov_flat _ rfl rfl rfl rfl rfl rfl rfl rfl]
    rfl

/-- The flat regulator is first-variation consistent (`c_h(K) = 0`). -/
theorem flatRegulator_consistent (hT : 0 < T) : (flatRegulator T).FirstVariationConsistent := by
  intro K
  have : ∀ n, (flatRegulator T).consistencyDefect n K = 0 := by
    intro n
    simp only [RegulatorSequence.consistencyDefect]
    refine Finset.sum_eq_zero fun b _ => le_antisymm (iSup₂_le fun v _ => ?_) zero_le
    have h0 : (flatRegulator T).lift n K v = 0 := rfl
    rw [firstVariation_flat hT b n K v, h0]
    cases b <;> simp [RegulatorSequence.finiteSectorVariation]
  simp only [this]
  exact tendsto_const_nhds

/-- The flat regulator is physically stationary (`ε_h(K) = 0`). -/
theorem flatRegulator_stationary : (flatRegulator T).PhysicallyStationary := by
  intro K
  have : ∀ n, (flatRegulator T).stationarityDefect n K = 0 := by
    intro n
    simp only [RegulatorSequence.stationarityDefect]
    refine le_antisymm (iSup₂_le fun v _ => ?_) zero_le
    have h0 : (flatRegulator T).lift n K v = 0 := rfl
    rw [h0, map_zero, abs_zero, ENNReal.ofReal_zero]
  simp only [this]
  exact tendsto_const_nhds

/-- **Non-vacuity of `thm:reduced-closure`**: the flat regulator satisfies all hypotheses. -/
example (hT : 0 < T) (ns : ℕ → ℕ) (hns : StrictMono ns) :=
  reduced_closure hT (flatRegulator T) (fun Q => flatRegulator_reducedCertificate T Q)
    (flatRegulator_consistent hT) flatRegulator_stationary
    (trivialCarrier_yukawaContinuous Unit) ns hns

end FlatNonVacuity

end EinsteinSM
end RenewalGeometry
