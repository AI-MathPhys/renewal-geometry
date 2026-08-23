/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMSTQuantumTightnessExact
import NCG.Grand.SMSTFermionicPhaseTransportExact

/-!
# Reflection-positive protected Euclidean continuum alternative

Machinery and assembly for `thm:SMST-reflection-positive-continuum` on the field space `E`
(a separable metrizable Borel space) carrying a continuous Euclidean reflection `θ`.

* `fieldLaw_reflection_positive`: the field law of a reflection-positive cylinder is reflection
  positive on every positive-time field function pulling back into the cylinder algebra (the
  bridge from (Q1) on cylinders to the field space);
* `reflectionPositive_of_tendsto`: reflection positivity on a bounded continuous positive-time
  algebra passes to weak limits (the limiting Osterwalder–Schrader form is positive);
* `exists_subseq_tendsto_of_tight` (**Prokhorov**): a tight sequence of field laws has a weakly
  convergent subsequence;
* `reflection_positive_continuum`: the positive branch — a subsequence converges to a
  probability measure on the field space which is reflection positive, every uniformly
  integrable protected correlation converges along the subsequence, the limit is nontrivial
  whenever a protected observable has a uniform positive variance floor, and every uniformly
  integrable residual insertion vanishing locally uniformly has zero limiting expectation;
* `mass_escape_of_not_tight`, `soft_mode_of_not_gap`: the obstruction witnesses returned when
  tightness (Q3) or the fermionic gap (Q4) fails.
-/

open MeasureTheory Filter Topology
open NCG.QuantumCylinderInverseLimit NCG.QuantumFieldTightness NCG.QuantumFieldPassage
  NCG.FermionicPhaseTransport NCG.SMSTQuantumTightness

namespace NCG
namespace SMSTReflectionPositiveContinuum

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### Reflection positivity on the field space -/

section Field

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Reflection positivity of a measure on the field space for the positive-time family `A`:
`∫ F(θ x) F(x) dμ ≥ 0`. -/
def ReflectionPositiveField (μ : Measure E) (θ : E → E) (A : Set (E → ℝ)) : Prop :=
  ∀ F ∈ A, 0 ≤ ∫ x, F (θ x) * F x ∂μ

/-- **Bridge from cylinders**: if the cylinder weight is reflection positive for the pulled-back
functions and the field map intertwines the reflections, the field law is reflection positive. -/
theorem fieldLaw_reflection_positive {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (ι : Ω → E) (θΩ : Ω → Ω)
    {θ : E → E} (hθc : Continuous θ) (hθ : ∀ ω, ι (θΩ ω) = θ (ι ω)) (A : Set (E → ℝ))
    (hA : ∀ F ∈ A, Continuous F)
    (hRP : ∀ F ∈ A, 0 ≤ ∑ ω, μ ω * (F (ι (θΩ ω)) * F (ι ω))) :
    ReflectionPositiveField (fieldLaw μ ι) θ A := by
  intro F hF
  have hFc := hA F hF
  unfold fieldLaw
  rw [integral_map (f := fun x => F (θ x) * F x) (Measurable.of_discrete).aemeasurable
    (by fun_prop : Continuous fun x => F (θ x) * F x).aestronglyMeasurable]
  have hint : ∫ ω, F (θ (ι ω)) * F (ι ω) ∂(discrete μ)
      = ∑ ω, μ ω * (F (ι (θΩ ω)) * F (ι ω)) := by
    unfold discrete
    rw [integral_finsetSum_measure fun ω _ =>
      Integrable.smul_measure Integrable.of_finite ENNReal.ofReal_ne_top]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [integral_smul_measure, integral_dirac, hθ, ENNReal.toReal_ofReal (hμ ω), smul_eq_mul]
  rw [hint]
  exact hRP F hF

/-- A bounded continuous reflected square `x ↦ F(θ x) F(x)` as a bounded continuous function. -/
noncomputable def reflectedSquare {θ : E → E} (hθ : Continuous θ) {F : E → ℝ} (hF : Continuous F)
    {B : ℝ} (hB : ∀ x, |F x| ≤ B) : BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => F (θ x) * F x, (hF.comp hθ).mul hF⟩ (2 * B ^ 2)
    fun x y => by
      rw [Real.dist_eq]
      have hB0 : 0 ≤ B := (abs_nonneg (F x)).trans (hB x)
      have h1 : |F (θ x) * F x| ≤ B ^ 2 := by
        rw [abs_mul, sq]
        exact mul_le_mul (hB (θ x)) (hB x) (abs_nonneg (F x)) hB0
      have h2 : |F (θ y) * F y| ≤ B ^ 2 := by
        rw [abs_mul, sq]
        exact mul_le_mul (hB (θ y)) (hB y) (abs_nonneg (F y)) hB0
      calc |F (θ x) * F x - F (θ y) * F y| ≤ |F (θ x) * F x| + |F (θ y) * F y| := abs_sub _ _
        _ ≤ B ^ 2 + B ^ 2 := add_le_add h1 h2
        _ = 2 * B ^ 2 := by ring

theorem reflectedSquare_apply {θ : E → E} (hθ : Continuous θ) {F : E → ℝ} (hF : Continuous F)
    {B : ℝ} (hB : ∀ x, |F x| ≤ B) (x : E) : reflectedSquare hθ hF hB x = F (θ x) * F x := rfl

/-- **Reflection positivity passes to weak limits** for bounded continuous positive-time
functions. -/
theorem reflectionPositive_of_tendsto {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hμ : Tendsto μs atTop (𝓝 μ)) {θ : E → E} (hθ : Continuous θ) (A : Set (E → ℝ))
    (hA : ∀ F ∈ A, Continuous F ∧ ∃ B, ∀ x, |F x| ≤ B)
    (hRP : ∀ j, ReflectionPositiveField (μs j : Measure E) θ A) :
    ReflectionPositiveField (μ : Measure E) θ A := by
  intro F hF
  obtain ⟨hFc, B, hB⟩ := hA F hF
  have hconv := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hμ
    (reflectedSquare hθ hFc hB)
  simp only [reflectedSquare_apply] at hconv
  exact ge_of_tendsto' hconv fun j => hRP j F hF

end Field

/-! ### Prokhorov extraction and the positive branch -/

section Assembly

variable {E : Type*} [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E]
  [TopologicalSpace.SeparableSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Prokhorov**: a tight sequence of field laws has a weakly convergent subsequence. -/
theorem exists_subseq_tendsto_of_tight (μs : ℕ → ProbabilityMeasure E)
    (htight : IsTightMeasureSet (Set.range fun j => (μs j : Measure E))) :
    ∃ μ : ProbabilityMeasure E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  have hset : {((ν : ProbabilityMeasure E) : Measure E) | ν ∈ Set.range μs}
      = Set.range fun j => (μs j : Measure E) := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_range, exists_exists_eq_and]
  have hc : IsCompact (closure (Set.range μs)) :=
    isCompact_closure_of_isTightMeasureSet (S := Set.range μs) (hset ▸ htight)
  obtain ⟨μ, -, φ, hφ, hlim⟩ := hc.tendsto_subseq fun n => subset_closure (Set.mem_range_self n)
  exact ⟨μ, φ, hφ, hlim⟩

/-- Tightness passes to subsequences. -/
theorem isTightMeasureSet_subseq (μs : ℕ → ProbabilityMeasure E)
    (htight : IsTightMeasureSet (Set.range fun j => (μs j : Measure E))) (φ : ℕ → ℕ) :
    IsTightMeasureSet (Set.range fun k => (μs (φ k) : Measure E)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight ⊢
  intro ε hε
  obtain ⟨K, hK, hKε⟩ := htight ε hε
  exact ⟨K, hK, by rintro _ ⟨k, rfl⟩; exact hKε _ ⟨φ k, rfl⟩⟩

/-- Local uniform convergence passes to subsequences. -/
theorem tendstoUniformlyOn_subseq {F : E → ℝ} {Fs : ℕ → E → ℝ} {K : Set E}
    (h : TendstoUniformlyOn Fs F atTop K) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    TendstoUniformlyOn (fun k => Fs (φ k)) F atTop K :=
  fun u hu => hφ.tendsto_atTop.eventually (h u hu)

/-- **Reflection-positive protected Euclidean continuum (positive branch)**: under tightness
(Q3) and reflection positivity of the field laws on the positive-time algebra (Q1), a
subsequence converges weakly to a reflection-positive probability measure on the field space;
every uniformly integrable protected correlation converges along the subsequence, a uniform
positive variance floor survives (nontriviality), and uniformly integrable residual insertions
vanishing locally uniformly have zero limiting expectation. -/
theorem reflection_positive_continuum (μs : ℕ → ProbabilityMeasure E)
    (htight : IsTightMeasureSet (Set.range fun j => (μs j : Measure E)))
    {θ : E → E} (hθ : Continuous θ) (A : Set (E → ℝ))
    (hA : ∀ F ∈ A, Continuous F ∧ ∃ B, ∀ x, |F x| ≤ B)
    (hRP : ∀ j, ReflectionPositiveField (μs j : Measure E) θ A) :
    ∃ μ : ProbabilityMeasure E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) ∧
      ReflectionPositiveField (μ : Measure E) θ A ∧
      (∀ (F : E → ℝ) (Fs : ℕ → E → ℝ), Continuous F → (∀ j, Continuous (Fs j)) →
        (∀ K : Set E, IsCompact K → TendstoUniformlyOn Fs F atTop K) → ∀ (δ : ℝ), 0 < δ →
        ∀ (C : ENNReal), C ≠ ⊤ → (∀ j, ∫⁻ x, ‖Fs j x‖ₑ ^ (1 + δ) ∂(μs j : Measure E) ≤ C) →
        Tendsto (fun k => ∫ x, Fs (φ k) x ∂(μs (φ k) : Measure E)) atTop
          (𝓝 (∫ x, F x ∂(μ : Measure E)))) ∧
      (∀ (O : E → ℝ) (Os : ℕ → E → ℝ), Continuous O → (∀ j, Continuous (Os j)) →
        (∀ K : Set E, IsCompact K → TendstoUniformlyOn Os O atTop K) → ∀ (δ : ℝ), 0 < δ →
        ∀ (C : ENNReal), C ≠ ⊤ → (∀ j, ∫⁻ x, ‖Os j x‖ₑ ^ (1 + δ) ∂(μs j : Measure E) ≤ C) →
        (∀ j, ∫⁻ x, ‖Os j x ^ 2‖ₑ ^ (1 + δ) ∂(μs j : Measure E) ≤ C) → ∀ (v : ℝ),
        (∀ j, v ≤ ∫ x, Os j x ^ 2 ∂(μs j : Measure E) - (∫ x, Os j x ∂(μs j : Measure E)) ^ 2) →
        v ≤ ∫ x, O x ^ 2 ∂(μ : Measure E) - (∫ x, O x ∂(μ : Measure E)) ^ 2) ∧
      (∀ (Rs : ℕ → E → ℝ), (∀ j, Continuous (Rs j)) →
        (∀ K : Set E, IsCompact K → TendstoUniformlyOn Rs (fun _ => 0) atTop K) → ∀ (δ : ℝ),
        0 < δ → ∀ (C : ENNReal), C ≠ ⊤ →
        (∀ j, ∫⁻ x, ‖Rs j x‖ₑ ^ (1 + δ) ∂(μs j : Measure E) ≤ C) →
        Tendsto (fun k => ∫ x, Rs (φ k) x ∂(μs (φ k) : Measure E)) atTop (𝓝 0)) := by
  obtain ⟨μ, φ, hφ, hlim⟩ := exists_subseq_tendsto_of_tight μs htight
  have htight' := isTightMeasureSet_subseq μs htight φ
  refine ⟨μ, φ, hφ, hlim, ?_, ?_, ?_, ?_⟩
  · exact reflectionPositive_of_tendsto hlim hθ A hA fun k => hRP (φ k)
  · intro F Fs hF hFs hunif δ hδ C hC hmom
    exact correlation_passage hlim htight' hF (fun k => hFs (φ k))
      (fun K hK => tendstoUniformlyOn_subseq (hunif K hK) hφ) hδ hC fun k => hmom (φ k)
  · intro O Os hO hOs hunif δ hδ C hC hmom1 hmom2 v hvar
    exact limit_variance_ge hlim htight' hO (fun k => hOs (φ k))
      (fun K hK => tendstoUniformlyOn_subseq (hunif K hK) hφ) hδ hC (fun k => hmom1 (φ k))
      (fun k => hmom2 (φ k)) fun k => hvar (φ k)
  · intro Rs hRs hunif δ hδ C hC hmom
    have := correlation_passage hlim htight' continuous_const (fun k => hRs (φ k))
      (fun K hK => tendstoUniformlyOn_subseq (hunif K hK) hφ) hδ hC fun k => hmom (φ k)
    simpa using this

/-! ### Obstruction witnesses -/

/-- **Field-mass escape**: failure of tightness returns a fixed mass escaping every compact. -/
theorem mass_escape_of_not_tight (μs : ℕ → ProbabilityMeasure E)
    (h : ¬ IsTightMeasureSet (Set.range fun j => (μs j : Measure E))) :
    ∃ ε : ENNReal, 0 < ε ∧ ∀ K : Set E, IsCompact K → ∃ j, ε < (μs j : Measure E) Kᶜ := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at h
  push Not at h
  obtain ⟨ε, hε, hK⟩ := h
  refine ⟨ε, hε, fun K hKc => ?_⟩
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hK K hKc
  exact ⟨j, hj⟩

/-- **Normalized fermionic soft mode**: failure of the uniform reduced gap returns unit vectors
orthogonal to the kernels with vanishing Dirac norm. -/
theorem soft_mode_of_not_gap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : ℕ → H →ₗ[ℂ] H) (h : ¬ ∃ γ : ℝ, 0 < γ ∧ UniformReducedGap D γ) :
    VanishingReducedGap D :=
  (reduced_gap_alternative D).1.resolve_left h

/-- **Negative reflected observable**: failure of reflection positivity on the field space
returns a positive-time function of negative reflected norm. -/
theorem negative_reflected_of_not_RP (μ : Measure E) (θ : E → E) (A : Set (E → ℝ))
    (h : ¬ ReflectionPositiveField μ θ A) : ∃ F ∈ A, ∫ x, F (θ x) * F x ∂μ < 0 := by
  unfold ReflectionPositiveField at h
  push Not at h
  exact h

/-- **Gauge anomaly holonomy**: failure of scalarization of the gauge-line cocycle on an orbit
returns a stabilizer element with nontrivial phase. -/
theorem gauge_holonomy_of_not_scalarizable {G Ω A : Type*} [Group G] [MulAction G Ω] [CommGroup A]
    {a : G → Ω → A} (ha : IsCocycle a) (ω₀ : Ω) (h : ¬ ∃ b : Ω → A, IsScalarization a ω₀ b) :
    ∃ h ∈ MulAction.stabilizer G ω₀, a h ω₀ ≠ 1 := by
  rw [scalarizable_iff_stabilizer_trivial ha ω₀] at h
  push Not at h
  exact h

/-- **The reflection-positive continuum alternative**: the positive branch under (Q1) and (Q3),
together with the obstruction witnesses returned when (Q1), (Q3), (Q4) or (Q5) fail. -/
theorem reflection_positive_continuum_alternative (μs : ℕ → ProbabilityMeasure E)
    {θ : E → E} (hθ : Continuous θ) (A : Set (E → ℝ))
    (hA : ∀ F ∈ A, Continuous F ∧ ∃ B, ∀ x, |F x| ≤ B) :
    ((IsTightMeasureSet (Set.range fun j => (μs j : Measure E)) →
      (∀ j, ReflectionPositiveField (μs j : Measure E) θ A) →
      ∃ μ : ProbabilityMeasure E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) ∧
        ReflectionPositiveField (μ : Measure E) θ A) ∧
      (¬ IsTightMeasureSet (Set.range fun j => (μs j : Measure E)) →
        ∃ ε : ENNReal, 0 < ε ∧ ∀ K : Set E, IsCompact K → ∃ j, ε < (μs j : Measure E) Kᶜ) ∧
      (∀ j, ¬ ReflectionPositiveField (μs j : Measure E) θ A →
        ∃ F ∈ A, ∫ x, F (θ x) * F x ∂(μs j : Measure E) < 0)) ∧
    (∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (D : ℕ → H →ₗ[ℂ] H),
      (¬ ∃ γ : ℝ, 0 < γ ∧ UniformReducedGap D γ) → VanishingReducedGap D) ∧
    (∀ {G Ω A' : Type*} [Group G] [MulAction G Ω] [CommGroup A'] (a : G → Ω → A'),
      IsCocycle a → ∀ ω₀ : Ω, (¬ ∃ b : Ω → A', IsScalarization a ω₀ b) →
        ∃ h ∈ MulAction.stabilizer G ω₀, a h ω₀ ≠ 1) := by
  refine ⟨⟨fun htight hRP => ?_, fun h => mass_escape_of_not_tight μs h,
    fun j h => negative_reflected_of_not_RP _ θ A h⟩,
    fun D h => soft_mode_of_not_gap D h, fun a ha ω₀ h => gauge_holonomy_of_not_scalarizable ha
      ω₀ h⟩
  obtain ⟨μ, φ, hφ, hlim, hRPμ, -⟩ := reflection_positive_continuum μs htight hθ A hA hRP
  exact ⟨μ, φ, hφ, hlim, hRPμ⟩

end Assembly

end SMSTReflectionPositiveContinuum
end NCG
