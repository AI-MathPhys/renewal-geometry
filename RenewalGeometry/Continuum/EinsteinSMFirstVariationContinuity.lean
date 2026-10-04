/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMVariationFramework
import RenewalGeometry.Continuum.EinsteinSMBosonicVariation
import RenewalGeometry.Analysis.CovariantGradientCompactness

/-!
# Continuity of the bosonic first variation in the reduced action topology
  (`prop:reduced-continuity`, Yang–Mills and Higgs sectors; Einstein–Standard-Model
  action-closure manuscript)

Rendering: one slab chart box `Q = (t₀,t₁) × (0,1)³` containing the time support of the test
region `K` (any box of the fundamental domain carries the whole first variation of a test in
`𝒱_K`, `actionVariation_eq_box`); the reduced convergence `ReducedConvergence Q z θ L θ₀` of the
compactness-certificate file on this box; the norm of `(𝒱_K^r)^*` is rendered as the uniform
estimate `|ℓ_n(v) - ℓ(v)| ≤ ε ‖v‖_{C^r}` on all tests, eventually in `n`.

* `pd_congr`, `redJet_congr`, `isLocalDensity_of_redJet`: densities factoring through the reduced
  jet are local.
* `bosonDensity`: the Yang–Mills + Higgs (kinetic and potential) part of the Standard-Model
  density, `(𝓛_YM + 𝓛_H,kin - V(H)) dV_g`.
* `bosonVariation_eq_cov`: for smooth fields the complete first variation of the bosonic action
  (metric, gauge and Higgs variations) is `∫_Q bosonCov θ (redJet z)(testJet v)`.
* `memW12_of_contDiffOn`: a `C¹` function on a neighbourhood of a compact closure lies in
  `W^{1,2}` with its classical partials as weak partials (smooth fields lie in the field spaces).
* `forall_mem_of_ae_mem`: a continuous field taking values a.e. in a closed set takes values
  there everywhere on the closure of the box.
* `higgs_L4_tendsto`: `prop:covariant-higgs-endpoint` in field form: under `L⁴` connection,
  `L²` Higgs and `L²` covariant-gradient convergence, `H_h → H` in `L⁴(Q)`.
* `bosonVariation_dual_tendsto` (**`prop:reduced-continuity`, Yang–Mills + Higgs sectors**):
  under `ReducedConvergence` on the slab box, `D𝒮_{YM+H,θ_h}(z_h) → D𝒮_{YM+H,θ}(z)` in the dual
  norm of `𝒱_K^r` (`r ≥ 1`), the limit functional being the covector formula evaluated on the
  limit jet `(e, de, A, F, H, K)` (`bosonLimitVariation`).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM

open SobolevOpen (pd box IsTest MemW12)

/-! ### Locality of jet densities -/

section Locality

variable {C : Type} [Fintype C]

theorem pd_congr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E4 → F} {x : E4}
    (h : f =ᶠ[𝓝 x] g) (i : Fin 4) : pd f i x = pd g i x := by
  unfold pd; rw [h.fderiv_eq]

theorem redJet_congr {z z' : FieldTuple C} {x : E4} (he : z.e =ᶠ[𝓝 x] z'.e)
    (hA : z.A =ᶠ[𝓝 x] z'.A) (hH : z.H =ᶠ[𝓝 x] z'.H) (hΨ : z.Ψ =ᶠ[𝓝 x] z'.Ψ)
    (hΨb : z.Ψb =ᶠ[𝓝 x] z'.Ψb) : redJet z x = redJet z' x := by
  have hAμ : ∀ μ, (fun y => z.A y μ) =ᶠ[𝓝 x] (fun y => z'.A y μ) := fun μ =>
    hA.mono fun y hy => by show z.A y μ = z'.A y μ; rw [hy]
  have h1 : curvatureF z.A x = curvatureF z'.A x := by
    funext μ ν
    simp only [curvatureF, pd_congr (hAμ ν) μ, pd_congr (hAμ μ) ν, hA.eq_of_nhds]
  have h2 : covDerivHiggs z.A z.H x = covDerivHiggs z'.A z'.H x := by
    funext μ
    simp only [covDerivHiggs, pd_congr hH μ, hA.eq_of_nhds, hH.eq_of_nhds]
  simp only [redJet, h1, h2, he.eq_of_nhds, hA.eq_of_nhds, hH.eq_of_nhds, hΨ.eq_of_nhds,
    hΨb.eq_of_nhds, pd_congr he, pd_congr hΨ, pd_congr hΨb]

/-- A density which is everywhere a function of the reduced jet is local. -/
theorem isLocalDensity_of_redJet {L : FieldTuple C → E4 → ℝ} {Φ : RJet C → ℝ}
    (h : ∀ z x, L z x = Φ (redJet z x)) : IsLocalDensity L := by
  intro z z' x he hA hH hΨ hΨb
  rw [h, h, redJet_congr he hA hH hΨ hΨb]

end Locality

/-! ### The bosonic density and its first variation -/

section Bosonic

variable {C : Type} [Fintype C] {T : ℝ} {left : C → Bool}

/-- The Yang–Mills + Higgs part of the Standard-Model density,
`(𝓛_YM + 𝓛_{H,kin} - V(H)) dV_g`. -/
def bosonDensity {Y : Type} (θ : CoefficientBank Y) (z : FieldTuple C) (x : E4) : ℝ :=
  (ymDensity θ z.e z.A x + higgsKinetic z.e z.A z.H x - higgsPotential θ (z.H x)) *
    volFactor (z.e x)

/-- The Standard-Model density is the bosonic density plus the Dirac–Yukawa density. -/
theorem smDensity_eq {Ysec : Type} (FC : FermionCarrier Ysec)
    (θ : CoefficientBank Ysec) (z : FieldTuple FC.C) (x : E4) :
    smDensity FC θ z x = bosonDensity θ z x + diracDensity FC θ z x * volFactor (z.e x) := by
  simp only [smDensity, bosonDensity]; ring

theorem isLocalDensity_bosonDensity {Y : Type} (θ : CoefficientBank Y) :
    IsLocalDensity (C := C) (bosonDensity θ) :=
  isLocalDensity_of_redJet fun z x => bosonDensity_eq_bosonPt θ z x

/-- **The first variation of the bosonic action of smooth fields is the covector integral**
`D𝒮_{YM+H,θ}(z)[v] = ∫_Q bosonCov θ (redJet z) (testJet v)` (metric variation through the
symmetric coframe lift, gauge and Higgs variations). -/
theorem bosonVariation_eq_cov {Y : Type} (θ : CoefficientBank Y) {t₀ t₁ : ℝ} (h0 : 0 < t₀)
    (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁)
    {r : ℕ} (z : SmoothFields T left) (v : CrTest left r K) {Ke : Set CoframeFibre}
    (hKe : IsCompact Ke) (hKGL : Ke ⊆ coframeGL)
    (hzK : ∀ x ∈ closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, z.z.e x ∈ Ke) :
    actionVariation T (bosonDensity θ) z.z (variationDirection z.z v.val) =
      ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set,
        bosonCov θ (redJet z.z x) (testJet v.val x) :=
  actionVariation_eq_cov h0 h01 h1 hK z v hKe hKGL hzK (isLocalDensity_bosonDensity θ)
    (contDiffOn_bosonPt θ) (fun z' x _ _ _ _ _ _ => bosonDensity_eq_bosonPt θ z' x)
    (fun R hR T' => by rw [(hasFDerivAt_bosonPt θ hR).2, bosonCov_apply])

end Bosonic

/-! ### Smooth fields in the field spaces -/

section SmoothSpaces

theorem isFiniteMeasure_restrict_of_compact_closure {Ω : Set E4} (hc : IsCompact (closure Ω)) :
    IsFiniteMeasure (volume.restrict Ω) :=
  isFiniteMeasure_restrict.mpr ((measure_mono subset_closure).trans_lt hc.measure_lt_top).ne

theorem memLp_of_continuousOn_closure {F : Type*} [NormedAddCommGroup F] {Ω : Set E4}
    (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω)) {f : E4 → F} (hf : ContinuousOn f (closure Ω))
    (p : ℝ≥0∞) : MemLp f p (volume.restrict Ω) := by
  haveI := isFiniteMeasure_restrict_of_compact_closure hc
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound ((hf.mono subset_closure).aestronglyMeasurable hΩ.measurableSet) M ?_
  exact (ae_restrict_iff' hΩ.measurableSet).mpr
    (Eventually.of_forall fun x hx => hM x (subset_closure hx))

/-- **Classical functions are Sobolev**: a `C¹` function on an open neighbourhood `U` of the
compact closure of an open `Ω` lies in `W^{1,2}(Ω)`, with its classical partials as weak
partials. -/
theorem memW12_of_contDiffOn {Ω U : Set E4} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hc : IsCompact (closure Ω)) (hΩU : closure Ω ⊆ U) {u : E4 → ℂ} (hu : ContDiffOn ℝ 1 u U) :
    MemW12 Ω u (fun i => pd u i) := by
  obtain ⟨χ, hχ, hχ1, -⟩ := SobolevOpen.exists_cutoff hU hc hΩU
  set w : E4 → ℂ := fun x => ((χ x : ℝ) : ℂ) * u x with hw_def
  have hχc : ContDiff ℝ 1 fun x => ((χ x : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (hχ.smooth.of_le (by simp))
  have hw : ContDiff ℝ 1 w := by
    refine contDiff_iff_contDiffAt.mpr fun y => ?_
    by_cases hy : y ∈ U
    · exact hχc.contDiffAt.mul (hu.contDiffAt (hU.mem_nhds hy))
    · have hy' : y ∉ tsupport χ := fun h => hy (hχ.subset h)
      have h0 : χ =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp hy'
      refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [h0] with x hx
      simp [hw_def, hx]
  have hwu : ∀ x ∈ Ω, w =ᶠ[𝓝 x] u := fun x hx => by
    have := hχ1.filter_mono (nhds_le_nhdsSet (subset_closure hx))
    filter_upwards [this] with y hy
    simp [hw_def, hy]
  have hfd : ContinuousOn (fderiv ℝ u) U := hu.continuousOn_fderiv_of_isOpen hU le_rfl
  refine ⟨memLp_of_continuousOn_closure hΩ hc (hu.continuousOn.mono hΩU) 2, fun i =>
    memLp_of_continuousOn_closure hΩ hc ((hfd.mono hΩU).clm_apply continuousOn_const) 2,
    fun i φ hφ => ?_⟩
  have h := SobolevOpen.hasWeakPartial_of_contDiff Ω hw i φ hφ
  have hφ0 : ∀ x ∉ Ω, φ =ᶠ[𝓝 x] 0 := fun x hx =>
    notMem_tsupport_iff_eventuallyEq.mp fun h => hx (hφ.subset h)
  have e1 : ∀ x, ((pd φ i x : ℝ) : ℂ) * u x = ((pd φ i x : ℝ) : ℂ) * w x := by
    intro x
    by_cases hx : x ∈ Ω
    · rw [(hwu x hx).eq_of_nhds]
    · rw [pd_congr (hφ0 x hx) i]
      simp [pd]
  have e2 : ∀ x, ((φ x : ℝ) : ℂ) * pd u i x = ((φ x : ℝ) : ℂ) * pd w i x := by
    intro x
    by_cases hx : x ∈ Ω
    · rw [pd_congr (hwu x hx) i]
    · rw [(hφ0 x hx).eq_of_nhds]
      simp
  simp only [e1, e2]
  exact h

/-- A field continuous on the closure of an open set and taking values a.e. in a closed set takes
values in it everywhere on the closure. -/
theorem forall_mem_of_ae_mem {X : Type*} [TopologicalSpace X] {Ω : Set E4} (hΩ : IsOpen Ω)
    {f : E4 → X} (hf : ContinuousOn f (closure Ω)) {S : Set X} (hS : IsClosed S)
    (h : ∀ᵐ x ∂(volume.restrict Ω), f x ∈ S) : ∀ x ∈ closure Ω, f x ∈ S := by
  have hΩS : ∀ x ∈ Ω, f x ∈ S := by
    intro x hx
    by_contra hfx
    have hV : IsOpen (Ω ∩ f ⁻¹' Sᶜ) :=
      (hf.mono subset_closure).isOpen_inter_preimage hΩ hS.isOpen_compl
    have hpos : 0 < volume (Ω ∩ f ⁻¹' Sᶜ) := hV.measure_pos volume ⟨x, hx, hfx⟩
    have h' := (ae_restrict_iff' hΩ.measurableSet).mp h
    have h0 : volume (Ω ∩ f ⁻¹' Sᶜ) = 0 := by
      refine measure_mono_null (fun y hy => ?_) (ae_iff.mp h')
      exact fun hy' => hy.2 (hy' hy.1)
    exact hpos.ne' h0
  intro x hx
  have := hf.image_closure (mem_image_of_mem f hx)
  exact closure_minimal (by rintro _ ⟨y, hy, rfl⟩; exact hΩS y hy) hS this

end SmoothSpaces

/-! ### Componentwise `L^p` bookkeeping -/

section Components

variable {μ : Measure E4}

theorem eLpNorm_apply_le {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] (f : E4 → ι → F)
    (i : ι) (p : ℝ≥0∞) : eLpNorm (fun x => f x i) p μ ≤ eLpNorm f p μ :=
  eLpNorm_mono fun x => norm_le_pi_norm (f x) i

theorem eLpNorm_le_sum_apply {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] {f : E4 → ι → F}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hf : ∀ i, AEStronglyMeasurable (fun x => f x i) μ) :
    eLpNorm f p μ ≤ ∑ i, eLpNorm (fun x => f x i) p μ := by
  calc eLpNorm f p μ ≤ eLpNorm (∑ i, fun x => ‖f x i‖) p μ := by
        refine eLpNorm_mono_real fun x => ?_
        rw [Finset.sum_apply]
        exact (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)).mpr
          fun i => Finset.single_le_sum (f := fun i => ‖f x i‖) (fun i _ => norm_nonneg _)
            (Finset.mem_univ i)
    _ ≤ ∑ i, eLpNorm (fun x => ‖f x i‖) p μ :=
        eLpNorm_sum_le (fun i _ => (hf i).norm) hp
    _ = ∑ i, eLpNorm (fun x => f x i) p μ := by simp only [eLpNorm_norm]

/-- Componentwise `L^p` convergence implies `L^p` convergence of the vector. -/
theorem tendsto_eLpNorm_of_apply {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    {u : ℕ → E4 → ι → F} {u₀ : E4 → ι → F} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hm : ∀ n i, AEStronglyMeasurable (fun x => u n x i - u₀ x i) μ)
    (h : ∀ i, Tendsto (fun n => eLpNorm (fun x => u n x i - u₀ x i) p μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (u n - u₀) p μ) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => ∑ i, eLpNorm (fun x => u n x i - u₀ x i) p μ) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum (Finset.univ : Finset ι) fun i _ => h i
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun n => zero_le)
    fun n => ?_
  exact eLpNorm_le_sum_apply (f := u n - u₀) hp (hm n)

/-- Vector `L^p` convergence implies componentwise `L^p` convergence. -/
theorem tendsto_eLpNorm_apply {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    {u : ℕ → E4 → ι → F} {u₀ : E4 → ι → F} {p : ℝ≥0∞}
    (h : Tendsto (fun n => eLpNorm (u n - u₀) p μ) atTop (𝓝 0)) (i : ι) :
    Tendsto (fun n => eLpNorm (fun x => u n x i - u₀ x i) p μ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => zero_le)
    fun n => eLpNorm_apply_le (u n - u₀) i p

/-- An `L^p`-convergent sequence of `L^p` functions is uniformly bounded in `L^p`. -/
theorem exists_eLpNorm_bound {F : Type*} [NormedAddCommGroup F] {u : ℕ → E4 → F}
    {u₀ : E4 → F} {p : ℝ≥0∞} (hp : 1 ≤ p) (hu : ∀ n, MemLp (u n) p μ) (hu₀ : MemLp u₀ p μ)
    (h : Tendsto (fun n => eLpNorm (u n - u₀) p μ) atTop (𝓝 0)) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ n, eLpNorm (u n) p μ ≤ B := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually (ge_mem_nhds (zero_lt_one' ℝ≥0∞)))
  refine ⟨1 + eLpNorm u₀ p μ + ∑ n ∈ Finset.range N, eLpNorm (u n) p μ, ?_, fun n => ?_⟩
  · exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hu₀.2.ne⟩,
      ENNReal.sum_ne_top.mpr fun n _ => (hu n).2.ne⟩
  · rcases lt_or_ge n N with hn | hn
    · exact (Finset.single_le_sum (f := fun n => eLpNorm (u n) p μ) (fun _ _ => zero_le)
        (Finset.mem_range.mpr hn)).trans le_add_self
    · calc eLpNorm (u n) p μ = eLpNorm ((u n - u₀) + u₀) p μ := by rw [sub_add_cancel]
        _ ≤ eLpNorm (u n - u₀) p μ + eLpNorm u₀ p μ :=
            eLpNorm_add_le ((hu n).1.sub hu₀.1) hu₀.1 hp
        _ ≤ 1 + eLpNorm u₀ p μ := by gcongr; exact hN n hn
        _ ≤ _ := le_self_add

end Components

/-! ### `prop:covariant-higgs-endpoint` in field form -/

section HiggsEndpoint

variable {T : ℝ}

/-- **Strong `L⁴` Higgs convergence** (`prop:covariant-higgs-endpoint`, field form on a chart
box): if `H_h ∈ W^{1,2}(Q)` (classical gradients), `A_h → A` in `L⁴`, `H_h → H` in `L²` and
`D_{A_h}H_h → K` in `L²`, then `H_h → H` in `L⁴(Q)` (and `H ∈ L⁴(Q)`). -/
theorem higgs_L4_tendsto (Q : ChartBox T) {Hn : ℕ → E4 → HiggsFibre} {An : ℕ → E4 → ConnFibre}
    {H₀ : E4 → HiggsFibre} {A₀ : E4 → ConnFibre} {K₀ : E4 → Fin 4 → HiggsFibre}
    (hW : ∀ n c, MemW12 Q.set (fun x => Hn n x c) (fun i x => pd (Hn n) i x c))
    (hH4 : ∀ n, MemLp (Hn n) 4 Q.μ)
    (hA : ∀ n, MemLp (An n) 4 Q.μ) (hA₀ : MemLp A₀ 4 Q.μ) (hAt : LpTendsto 4 Q.μ An A₀)
    (hH₀ : MemLp H₀ 2 Q.μ) (hHt : LpTendsto 2 Q.μ Hn H₀)
    (hK₀ : MemLp K₀ 2 Q.μ) (hKt : LpTendsto 2 Q.μ (fun n => covDerivHiggs (An n) (Hn n)) K₀) :
    MemLp H₀ 4 Q.μ ∧ LpTendsto 4 Q.μ Hn H₀ := by
  have hAc : ∀ n μ (c e : Fin 2), MemLp (fun x => An n x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e)) 4
      Q.μ := fun n μ c e =>
    memLp_pi_iff.mp (memLp_pi_iff.mp (memLp_pi_iff.mp (hA n) μ) (Fin.natAdd 3 c)) (Fin.natAdd 3 e)
  have hA₀c : ∀ μ (c e : Fin 2), MemLp (fun x => A₀ x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e)) 4
      Q.μ := fun μ c e =>
    memLp_pi_iff.mp (memLp_pi_iff.mp (memLp_pi_iff.mp hA₀ μ) (Fin.natAdd 3 c)) (Fin.natAdd 3 e)
  have hAlim : ∀ μ (c e : Fin 2), Tendsto (fun n => eLpNorm
      ((fun x => An n x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e)) -
        fun x => A₀ x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e)) 4 Q.μ) atTop (𝓝 0) := fun μ c e =>
    tendsto_eLpNorm_apply (u := fun n x => An n x μ (Fin.natAdd 3 c))
      (tendsto_eLpNorm_apply (u := fun n x => An n x μ)
        (tendsto_eLpNorm_apply hAt μ) (Fin.natAdd 3 c)) (Fin.natAdd 3 e)
  have hHn2 : ∀ n, MemLp (Hn n) 2 Q.μ := fun n =>
    memLp_pi_iff.mpr fun c => (hW n c).memLp
  obtain ⟨B, hBt, hB⟩ := exists_eLpNorm_bound (by norm_num) hHn2 hH₀ hHt
  have hY : ∀ (c : Fin 2) μ, MemLp (fun x => K₀ x μ c) 2 Q.μ := fun c μ =>
    memLp_pi_iff.mp (memLp_pi_iff.mp hK₀ μ) c
  have hYlim : ∀ (c : Fin 2) μ, Tendsto (fun n => eLpNorm
      (SobolevOpen.covD (fun c μ x => pd (Hn n) μ x c)
        (fun μ c e x => An n x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e)) (fun c x => Hn n x c) c μ -
        fun x => K₀ x μ c) 2 Q.μ) atTop (𝓝 0) := by
    intro c μ
    have h := tendsto_eLpNorm_apply (u := fun n x => covDerivHiggs (An n) (Hn n) x μ)
      (tendsto_eLpNorm_apply hKt μ) c
    refine h.congr fun n => ?_
    congr 1
  obtain ⟨-, -, hL4⟩ := SobolevOpen.covariant_higgs_endpoint_box_of_L2 (ι := Fin 4) (by simp)
    Q.lt (fun n c x => Hn n x c) (fun n c μ x => pd (Hn n) μ x c)
    (fun n μ c e x => An n x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e))
    (fun μ c e x => A₀ x μ (Fin.natAdd 3 c) (Fin.natAdd 3 e)) (fun c μ x => K₀ x μ c)
    hW (fun n μ c e => hAc n μ c e) hA₀c hAlim hBt
    (fun n c => (eLpNorm_apply_le (Hn n) c 2).trans (hB n)) hY hYlim (fun c x => H₀ x c)
    (fun c => memLp_pi_iff.mp hH₀ c) (fun c => tendsto_eLpNorm_apply hHt c)
  have hconv : LpTendsto 4 Q.μ Hn H₀ :=
    tendsto_eLpNorm_of_apply (by norm_num)
      (fun n c => ((hW n c).memLp.1.sub (memLp_pi_iff.mp hH₀ c).1)) hL4
  refine ⟨?_, hconv⟩
  obtain ⟨n, hn⟩ := (hconv.eventually (gt_mem_nhds ENNReal.zero_lt_top)).exists
  have hd : MemLp (Hn n - H₀) 4 Q.μ := ⟨(hH4 n).1.sub hH₀.1, hn⟩
  have := (hH4 n).sub hd
  rwa [sub_sub_cancel] at this

end HiggsEndpoint

/-! ### Smooth fields on a chart box -/

section SmoothChart

variable {T : ℝ}

theorem pd_clm_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : E4 → F} {x : E4} (hf : DifferentiableAt ℝ f x) (L : F →L[ℝ] G)
    (i : Fin 4) : pd (fun y => L (f y)) i x = L (pd f i x) := by
  unfold pd
  rw [show (fun y => L (f y)) = L ∘ f from rfl, (L.hasFDerivAt.comp x hf.hasFDerivAt).fderiv]
  rfl

theorem memW12_congr_grad {Ω : Set E4} (hΩ : MeasurableSet Ω) {u : E4 → ℂ}
    {g g' : Fin 4 → E4 → ℂ} (h : MemW12 Ω u g) (hg : ∀ i, ∀ x ∈ Ω, g i x = g' i x) :
    MemW12 Ω u g' := by
  refine ⟨h.memLp, fun i => (h.memLp_grad i).ae_eq
    ((ae_restrict_iff' hΩ).mpr (Eventually.of_forall (hg i))), fun i φ hφ => ?_⟩
  rw [h.weak i φ hφ]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Ω
  · simp only [hg i x hx]
  · simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.subset h))]

/-- The entry `e ↦ (e^a_μ : ℂ)` of a coframe. -/
def coframeEntryL (a μ : Fin 4) : CoframeFibre →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) μ).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 4 → ℝ) a))

/-- **Smooth coframes lie in `H¹(Q)`** with the classical gradient packet, for a chart box whose
closure lies in the open slab. -/
theorem memH1_coframe_of_smooth (Q : ChartBox T) (hc : IsCompact (closure Q.set))
    (hQ : closure Q.set ⊆ cylSlab T) {e : E4 → CoframeFibre}
    (he : ContDiffOn ℝ ∞ e (cylSlab T)) : MemH1 Q (coframeC e) (coframeGrad e) := by
  intro c
  have hu : ContDiffOn ℝ 1 (fun x => coframeEntryL c.1 c.2 (e x)) (cylSlab T) :=
    (coframeEntryL c.1 c.2).contDiff.comp_contDiffOn (he.of_le (by simp))
  have hO := SobolevOpen.isOpen_box Q.a Q.b
  refine memW12_congr_grad hO.measurableSet
    (memW12_of_contDiffOn hO (isOpen_cylSlab T) hc hQ hu) fun i x hx => ?_
  exact pd_clm_comp (differentiableAt_of_contDiffOn_slab he (hQ (subset_closure hx)))
    (coframeEntryL c.1 c.2) i

/-- **Smooth Higgs fields lie in `W^{1,2}(Q)`** componentwise with their classical gradients. -/
theorem memW12_higgs_of_smooth (Q : ChartBox T) (hc : IsCompact (closure Q.set))
    (hQ : closure Q.set ⊆ cylSlab T) {H : E4 → HiggsFibre}
    (hH : ContDiffOn ℝ ∞ H (cylSlab T)) (c : Fin 2) :
    MemW12 Q.set (fun x => H x c) (fun i x => pd H i x c) := by
  have hu : ContDiffOn ℝ 1 (fun x => H x c) (cylSlab T) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) c).contDiff.comp_contDiffOn
      (hH.of_le (by simp))
  have hO := SobolevOpen.isOpen_box Q.a Q.b
  refine memW12_congr_grad hO.measurableSet
    (memW12_of_contDiffOn hO (isOpen_cylSlab T) hc hQ hu) fun i x hx => ?_
  exact pd_clm_comp (differentiableAt_of_contDiffOn_slab hH (hQ (subset_closure hx)))
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) c) i

end SmoothChart

/-! ### Convergence of the couplings -/

section Banks

variable {Ysec : Type}

/-- Under bank convergence inside a compact physical set, the gauge factors `g_j^{-2}`, `λ_H` and
`v_H` converge. -/
theorem bank_couplings_tendsto {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    (hP : ∃ P, IsCompactBankSet P ∧ ∀ n, θ n ∈ P) (ht : BankTendsto θ θ₀) :
    (∀ j, Tendsto (fun n => gaugeScalars (θ n) j) atTop (𝓝 (gaugeScalars θ₀ j))) ∧
      Tendsto (fun n => (θ n).lambdaH) atTop (𝓝 θ₀.lambdaH) ∧
      Tendsto (fun n => (θ n).vH) atTop (𝓝 θ₀.vH) := by
  have hc : ∀ k : Fin 7, Tendsto (fun n => (bankCoords (θ n)).1 k) atTop
      (𝓝 ((bankCoords θ₀).1 k)) := fun k =>
    (((continuous_apply k).comp continuous_fst).tendsto _).comp ht
  have h2 : Tendsto (fun n => (θ n).g1) atTop (𝓝 θ₀.g1) := by simpa [bankCoords] using hc 2
  have h3 : Tendsto (fun n => (θ n).g2) atTop (𝓝 θ₀.g2) := by simpa [bankCoords] using hc 3
  have h4 : Tendsto (fun n => (θ n).g3) atTop (𝓝 θ₀.g3) := by simpa [bankCoords] using hc 4
  have h5 : Tendsto (fun n => (θ n).lambdaH) atTop (𝓝 θ₀.lambdaH) := by
    simpa [bankCoords] using hc 5
  have h6 : Tendsto (fun n => (θ n).vH) atTop (𝓝 θ₀.vH) := by simpa [bankCoords] using hc 6
  obtain ⟨P, ⟨hPc, hPphys⟩, hθP⟩ := hP
  obtain ⟨θ₁, hθ₁, heq⟩ : bankCoords θ₀ ∈ bankCoords '' P :=
    hPc.isClosed.mem_of_tendsto ht (Eventually.of_forall fun n => mem_image_of_mem _ (hθP n))
  have hphys := hPphys hθ₁
  have e2 : θ₁.g1 = θ₀.g1 := by simpa [bankCoords] using congrArg (fun c => c.1 2) heq
  have e3 : θ₁.g2 = θ₀.g2 := by simpa [bankCoords] using congrArg (fun c => c.1 3) heq
  have e4 : θ₁.g3 = θ₀.g3 := by simpa [bankCoords] using congrArg (fun c => c.1 4) heq
  have p2 : θ₀.g1 ≠ 0 := e2 ▸ hphys.2.1.ne'
  have p3 : θ₀.g2 ≠ 0 := e3 ▸ hphys.2.2.1.ne'
  have p4 : θ₀.g3 ≠ 0 := e4 ▸ hphys.2.2.2.1.ne'
  refine ⟨fun j => ?_, h5, h6⟩
  fin_cases j
  · simpa [gaugeScalars] using (h4.pow 2).inv₀ (pow_ne_zero 2 p4)
  · simpa [gaugeScalars] using (h3.pow 2).inv₀ (pow_ne_zero 2 p3)
  · simpa [gaugeScalars] using (h2.pow 2).inv₀ (pow_ne_zero 2 p2)

end Banks

/-! ### `prop:reduced-continuity`: the Yang–Mills and Higgs sectors -/

section Assembly

variable {C : Type} [Fintype C] {T : ℝ} {left : C → Bool} {Ysec : Type} [Fintype Ysec]

/-- The reduced jet `(e, de, A, F, H, K, Ψ, dΨ, Ψ̄, dΨ̄)` of limit fields (the coframe gradient is
the real part of the weak gradient packet). -/
def limitJet (L : LimitFields C) (x : E4) : RJet C :=
  RJet.mk (L.e x) (toJet (reJet L.de x)) (L.A x) (L.F x) (L.H x) (L.K x) (L.Ψ x)
    (fun i s c => L.dΨ x i (s, c)) (L.Ψb x) (fun i s c => L.dΨb x i (s, c))

/-- The first variation of the bosonic action at limit fields, defined by the same covector
formula as for smooth fields (`bosonVariation_eq_cov`). -/
def bosonLimitVariation {Y : Type} (θ : CoefficientBank Y) (Q : ChartBox T) (L : LimitFields C)
    {r : ℕ} {K : CylRegion T} (v : CrTest left r K) : ℝ :=
  ∫ x in Q.set, bosonCov θ (limitJet L x) (testJet v.val x)

/-- **Coframe data on the slab box**: values in the compact chart set everywhere on the closed
box, smooth coframes in `H¹(Q)`, and the hypotheses `CoframeConv` (convergence in measure inside
the compact chart set) for the coframe parts of the jets. -/
theorem coframe_slab_data {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {z : ℕ → SmoothFields T left} {L : LimitFields C} {Ke : Set CoframeFibre}
    (hKe : IsCompactCoframeSet Ke)
    (hzKe : ∀ n, ∀ᵐ x ∂(slabChart t₀ t₁ h0 h01 h1 (T := T)).μ, (z n).z.e x ∈ Ke)
    (hLKe : ∀ᵐ x ∂(slabChart t₀ t₁ h0 h01 h1 (T := T)).μ, L.e x ∈ Ke)
    (hemem : MemH1 (slabChart t₀ t₁ h0 h01 h1 (T := T)) (coframeC L.e) L.de)
    (het : H1Tendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)) (fun n => coframeC (z n).z.e)
      (fun n => coframeGrad (z n).z.e) (coframeC L.e) L.de) :
    (∀ n, ∀ x ∈ closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, (z n).z.e x ∈ Ke) ∧
      (∀ n, MemH1 (slabChart t₀ t₁ h0 h01 h1 (T := T)) (coframeC (z n).z.e)
        (coframeGrad (z n).z.e)) ∧
      CoframeConv (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ Ke (fun n x => (redJet (z n).z x).e)
        (fun x => (limitJet L x).e) := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T) with hQdef
  have hO : IsOpen Q.set := SobolevOpen.isOpen_box Q.a Q.b
  have hclS : closure Q.set ⊆ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1)
  have hc : IsCompact (closure Q.set) := isCompact_closure_slabChart h0 h01 h1
  have hKGL : Ke ⊆ coframeGL := hKe.2.trans coframeChart_subset_GL
  have hmem : ∀ n, MemH1 Q (coframeC (z n).z.e) (coframeGrad (z n).z.e) := fun n =>
    memH1_coframe_of_smooth Q hc hclS (z n).smooth_e
  refine ⟨fun n => forall_mem_of_ae_mem hO ((z n).smooth_e.continuousOn.mono hclS)
    hKe.1.isClosed (hzKe n), hmem, ⟨hKe.1, hKGL, fun n => ((z n).smooth_e.continuousOn.mono
      (subset_closure.trans hclS) |>.aestronglyMeasurable hO.measurableSet).aemeasurable, hzKe,
      hLKe, coframe_tendstoInMeasure hmem hemem het⟩⟩

/-- **The bosonic covectors converge in `L¹(Q)`** under the reduced convergence on the slab
box. -/
theorem bosonCov_reduced_tendsto {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C}
    {θ₀ : CoefficientBank Ysec}
    (hRC : ReducedConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀) :
    RenewalGeometry.LpTendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ 1
      (fun n x => bosonCov (θ n) (redJet (z n).z x)) (fun x => bosonCov θ₀ (limitJet L x)) := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T) with hQdef
  have hO : IsOpen Q.set := SobolevOpen.isOpen_box Q.a Q.b
  have hclS : closure Q.set ⊆ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1)
  have hc : IsCompact (closure Q.set) := isCompact_closure_slabChart h0 h01 h1
  obtain ⟨Ke, hKe, hzKe, hLKe⟩ := hRC.coframe_chart
  obtain ⟨-, -, he⟩ := coframe_slab_data h0 h01 h1 hKe hzKe hLKe hRC.coframe_mem
    hRC.coframe_tendsto
  have hmemLp : ∀ {F : Type} [NormedAddCommGroup F] {f : E4 → F} (p : ℝ≥0∞),
      ContinuousOn f (cylSlab T) → MemLp f p Q.μ := fun p hf =>
    memLp_of_continuousOn_closure hO hc (hf.mono hclS) p
  have hF : RenewalGeometry.LpTendsto Q.μ 2 (fun n x => (redJet (z n).z x).F)
      (fun x => (limitJet L x).F) :=
    ⟨fun n => hmemLp 2 (continuousOn_curvatureF (z n).smooth_A), hRC.curv_mem,
      hRC.curv_tendsto⟩
  have hA : RenewalGeometry.LpTendsto Q.μ 4 (fun n x => (redJet (z n).z x).A)
      (fun x => (limitJet L x).A) :=
    ⟨fun n => hmemLp 4 (z n).smooth_A.continuousOn, hRC.conn_mem, hRC.conn_tendsto⟩
  have hKc : RenewalGeometry.LpTendsto Q.μ 2 (fun n x => (redJet (z n).z x).K)
      (fun x => (limitJet L x).K) :=
    ⟨fun n => hmemLp 2 (continuousOn_covDerivHiggs (z n).smooth_A (z n).smooth_H),
      hRC.covgrad_mem, hRC.covgrad_tendsto⟩
  obtain ⟨hH₀4, hH4⟩ := higgs_L4_tendsto Q
    (fun n c => memW12_higgs_of_smooth Q hc hclS (z n).smooth_H c)
    (fun n => hmemLp 4 (z n).smooth_H.continuousOn)
    (fun n => hmemLp 4 (z n).smooth_A.continuousOn) hRC.conn_mem hRC.conn_tendsto
    hRC.higgs_mem hRC.higgs_tendsto hRC.covgrad_mem hRC.covgrad_tendsto
  have hH : RenewalGeometry.LpTendsto Q.μ 4 (fun n x => (redJet (z n).z x).H)
      (fun x => (limitJet L x).H) :=
    ⟨fun n => hmemLp 4 (z n).smooth_H.continuousOn, hH₀4, hH4⟩
  obtain ⟨hs, hl, hv⟩ := bank_couplings_tendsto hRC.bank_compact hRC.bank_tendsto
  exact bosonCov_tendsto he hF hA hKc hH hs hl hv

/-- **`prop:reduced-continuity`, Yang–Mills + Higgs sectors.**  Let `Q` be the slab box
`(t₀,t₁) × (0,1)³` containing the time support of the test region `K`, and let
`z_h → z` in the reduced action topology on `Q` (`ReducedConvergence`, including bank
convergence).  Then for `r ≥ 1` the complete first variations (metric, gauge and Higgs
directions) of the Yang–Mills + Higgs action converge in the dual norm of `𝒱_K^r`:
for every `ε > 0`, eventually `|D𝒮_{YM+H,θ_h}(z_h)[v] - D𝒮_{YM+H,θ}(z)[v]| ≤ ε ‖v‖_{C^r}` for
all `v`. -/
theorem bosonVariation_dual_tendsto {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁) {r : ℕ} (hr : 1 ≤ r)
    {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec} {L : LimitFields C}
    {θ₀ : CoefficientBank Ysec}
    (hRC : ReducedConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest left r K,
      |actionVariation T (bosonDensity (θ n)) (z n).z (variationDirection (z n).z v.val) -
        bosonLimitVariation θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v| ≤ ε * ‖v‖ := by
  obtain ⟨Ke, hKe, hzKe, hLKe⟩ := hRC.coframe_chart
  obtain ⟨hcl, -, -⟩ := coframe_slab_data h0 h01 h1 hKe hzKe hLKe hRC.coframe_mem
    hRC.coframe_tendsto
  filter_upwards [dual_tendsto_of_L1 (left := left) (K := K) hr
    (bosonCov_reduced_tendsto h0 h01 h1 hRC) hε] with n hn v
  rw [bosonVariation_eq_cov (θ n) h0 h01 h1 hK (z n) v hKe.1
    (hKe.2.trans coframeChart_subset_GL) (hcl n)]
  exact hn v

end Assembly

end EinsteinSM
end RenewalGeometry
