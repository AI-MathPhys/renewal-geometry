/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.QuantumFieldTightnessExact
import NCG.Grand.QuantumFieldPassageExact

/-!
# Absolute tightness, correlation passage, and nontriviality (record theorem)

Exact encoding of `thm:SMST-quantum-tightness` (QRP.7–QRP.9) for the field laws
`μ̂_X = (ι_X)_* μ_X` of finite weighted cylinders mapped into a field space `E`.

* **(QRP.7)** `tail_bound` / `tight_of_expMoment`: a uniform exponential moment bound
  `sup_X ∑ μ_X(ω) e^{α 𝒱(ι_X ω)} ≤ C` with compact sublevel sets of `𝒱` gives
  `sup_X μ̂_X {𝒱 > R} ≤ C e^{-α R}` and tightness of the field laws;
* **(QRP.8)** `tight_of_screen`: on a Hilbert field space, uniformly bounded second moments and
  uniformly vanishing finite-rank screen tails give tightness;
* **(QRP.9)** `correlation_passage`: if `μ̂_{X_j} ⇒ μ`, the family is tight, continuous protected
  writers `F_j → F` locally uniformly and `sup_j ∫ |F_j|^{1+δ} dμ̂_{X_j} < ∞`, then
  `∫ F_j dμ̂_{X_j} → ∫ F dμ`;
* **(nontriviality)** `limit_variance_ge`: under the corresponding `2+δ` bounds for `O_j`, the
  limiting variance dominates `inf_j Var(O_j)`, so a positive lower bound makes the limit
  nontrivial.

The whole package is collected in `quantum_tightness`.
-/

open MeasureTheory Filter Topology
open NCG.QuantumFieldTightness NCG.QuantumFieldPassage NCG.QuantumCylinderInverseLimit

namespace NCG
namespace SMSTQuantumTightness

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

section Polish

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]

/-- **(QRP.7, tail bound)**. -/
theorem tail_bound {X : Type*} {Ω : X → Type*} [∀ x, Fintype (Ω x)] [∀ x, MeasurableSpace (Ω x)]
    [∀ x, DiscreteMeasurableSpace (Ω x)] (μ : ∀ x, Ω x → ℝ) (hμ : ∀ x ω, 0 ≤ μ x ω)
    (ι : ∀ x, Ω x → E) (V : E → ℝ) (hV : Measurable V) {α : ℝ} (hα : 0 < α) {C : ℝ}
    (hC : ∀ x, expMoment (μ x) (ι x) V α ≤ C) (x : X) (R : ℝ) :
    fieldLaw (μ x) (ι x) {e | R < V e} ≤ ENNReal.ofReal (C * Real.exp (-(α * R))) :=
  (fieldLaw_tail_le (hμ x) (ι x) V hV hα.le R).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hC x) (Real.exp_pos _).le))

/-- **(QRP.7, tightness)**. -/
theorem tight_of_expMoment {X : Type*} {Ω : X → Type*} [∀ x, Fintype (Ω x)]
    [∀ x, MeasurableSpace (Ω x)] [∀ x, DiscreteMeasurableSpace (Ω x)] (μ : ∀ x, Ω x → ℝ)
    (hμ : ∀ x ω, 0 ≤ μ x ω) (ι : ∀ x, Ω x → E) (V : E → ℝ) (hV : Measurable V)
    (hcompact : ∀ R : ℝ, IsCompact {e | V e ≤ R}) {α : ℝ} (hα : 0 < α) {C : ℝ}
    (hC : ∀ x, expMoment (μ x) (ι x) V α ≤ C) :
    IsTightMeasureSet (Set.range fun x => fieldLaw (μ x) (ι x)) :=
  isTightMeasureSet_fieldLaw μ hμ ι V hV hcompact hα hC

end Polish

/-- **(QRP.8)**: screen tightness on a Hilbert field space. -/
theorem tight_of_screen {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] {X : Type*} (ν : X → Measure H)
    [∀ x, IsProbabilityMeasure (ν x)] (P : ℕ → H →L[ℝ] H)
    (hfin : ∀ k, FiniteDimensional ℝ (LinearMap.range (P k).toLinearMap))
    (hP : ∀ k x, ‖P k x‖ ≤ ‖x‖) {A : ENNReal} (hA : A ≠ ⊤)
    (hmom : ∀ x, ∫⁻ φ, ‖φ‖ₑ ^ 2 ∂(ν x) ≤ A)
    (hscreen : Tendsto (fun k => ⨆ x, ∫⁻ φ, ‖φ - P k φ‖ₑ ^ 2 ∂(ν x)) atTop (𝓝 0)) :
    IsTightMeasureSet (Set.range ν) :=
  isTightMeasureSet_of_screen ν P hfin hP hA hmom hscreen

section Passage

variable {E : Type*} [TopologicalSpace E] [T2Space E] [MeasurableSpace E] [BorelSpace E]
  [HasOuterApproxClosed E]

/-- **(QRP.9)**: uniformly integrable passage of protected correlations. -/
theorem correlation_passage {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hμ : Tendsto μs atTop (𝓝 μ))
    (htight : IsTightMeasureSet (Set.range fun j => (μs j : Measure E)))
    {F : E → ℝ} (hF : Continuous F) {Fs : ℕ → E → ℝ} (hFs : ∀ j, Continuous (Fs j))
    (hunif : ∀ K : Set E, IsCompact K → TendstoUniformlyOn Fs F atTop K) {δ : ℝ} (hδ : 0 < δ)
    {C : ENNReal} (hC : C ≠ ⊤) (hmom : ∀ j, ∫⁻ x, ‖Fs j x‖ₑ ^ (1 + δ) ∂(μs j : Measure E) ≤ C) :
    Tendsto (fun j => ∫ x, Fs j x ∂(μs j : Measure E)) atTop
      (𝓝 (∫ x, F x ∂(μ : Measure E))) := by
  refine tendsto_integral_of_locally_uniform hμ ?_ hF hFs hunif hδ hC hmom
  intro η hη
  obtain ⟨K, hK, hKη⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 htight η hη
  exact ⟨K, hK, fun j => hKη _ ⟨j, rfl⟩⟩

/-- **(Nontriviality)**: the limiting variance dominates a uniform lower variance bound. -/
theorem limit_variance_ge {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hμ : Tendsto μs atTop (𝓝 μ))
    (htight : IsTightMeasureSet (Set.range fun j => (μs j : Measure E)))
    {O : E → ℝ} (hO : Continuous O) {Os : ℕ → E → ℝ} (hOs : ∀ j, Continuous (Os j))
    (hunif : ∀ K : Set E, IsCompact K → TendstoUniformlyOn Os O atTop K) {δ : ℝ} (hδ : 0 < δ)
    {C : ENNReal} (hC : C ≠ ⊤) (hmom1 : ∀ j, ∫⁻ x, ‖Os j x‖ₑ ^ (1 + δ) ∂(μs j : Measure E) ≤ C)
    (hmom2 : ∀ j, ∫⁻ x, ‖Os j x ^ 2‖ₑ ^ (1 + δ) ∂(μs j : Measure E) ≤ C) {v : ℝ}
    (hvar : ∀ j, v ≤ ∫ x, Os j x ^ 2 ∂(μs j : Measure E) - (∫ x, Os j x ∂(μs j : Measure E)) ^ 2) :
    v ≤ ∫ x, O x ^ 2 ∂(μ : Measure E) - (∫ x, O x ∂(μ : Measure E)) ^ 2 := by
  refine variance_limit_ge hμ ?_ hO hOs hunif hδ hC hmom1 hmom2 hvar
  intro η hη
  obtain ⟨K, hK, hKη⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 htight η hη
  exact ⟨K, hK, fun j => hKη _ ⟨j, rfl⟩⟩

end Passage

/-- **Absolute tightness, correlation passage, and nontriviality**: the record package. -/
theorem quantum_tightness {E : Type*} [TopologicalSpace E] [T2Space E] [MeasurableSpace E]
    [BorelSpace E] [HasOuterApproxClosed E] :
    (∀ {X : Type} {Ω : X → Type} [∀ x, Fintype (Ω x)] [∀ x, MeasurableSpace (Ω x)]
        [∀ x, DiscreteMeasurableSpace (Ω x)] (μ : ∀ x, Ω x → ℝ), (∀ x ω, 0 ≤ μ x ω) →
        ∀ (ι : ∀ x, Ω x → E) (V : E → ℝ), Measurable V → (∀ R : ℝ, IsCompact {e | V e ≤ R}) →
        ∀ (α : ℝ), 0 < α → ∀ (C : ℝ), (∀ x, expMoment (μ x) (ι x) V α ≤ C) →
        (∀ x R, fieldLaw (μ x) (ι x) {e | R < V e} ≤ ENNReal.ofReal (C * Real.exp (-(α * R)))) ∧
          IsTightMeasureSet (Set.range fun x => fieldLaw (μ x) (ι x))) ∧
      (∀ (μs : ℕ → ProbabilityMeasure E) (μ : ProbabilityMeasure E), Tendsto μs atTop (𝓝 μ) →
        IsTightMeasureSet (Set.range fun j => (μs j : Measure E)) →
        ∀ (F : E → ℝ), Continuous F → ∀ (Fs : ℕ → E → ℝ), (∀ j, Continuous (Fs j)) →
        (∀ K : Set E, IsCompact K → TendstoUniformlyOn Fs F atTop K) → ∀ (δ : ℝ), 0 < δ →
        ∀ (C : ENNReal), C ≠ ⊤ → (∀ j, ∫⁻ x, ‖Fs j x‖ₑ ^ (1 + δ) ∂(μs j : Measure E) ≤ C) →
        Tendsto (fun j => ∫ x, Fs j x ∂(μs j : Measure E)) atTop
          (𝓝 (∫ x, F x ∂(μ : Measure E)))) :=
  ⟨fun μ hμ ι V hV hcompact _α hα _C hC =>
      ⟨fun x R => tail_bound μ hμ ι V hV hα hC x R, tight_of_expMoment μ hμ ι V hV hcompact hα hC⟩,
    fun _μs _μ hμ htight _F hF _Fs hFs hunif _δ hδ _C hC hmom =>
      correlation_passage hμ htight hF hFs hunif hδ hC hmom⟩

end SMSTQuantumTightness
end NCG
