/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FreshStationarySamplerInvisibility

/-!
# Concrete hidden dynamical nonidentifiability witnesses

This module closes the final witness gap in
`thm:fresh-opportunity-invisibility`.  It instantiates the general fresh-table
invariance principle for every dynamical item listed in the manuscript.
-/

open Matrix

namespace NCG

/-- Type of a complete duration-resolved visible downstream table. -/
abbrev FreshVisibleTable (Omega H : Type*) := List (ℕ × Omega) → H

/-- A kernel's one-step generator in the unit-time convention. -/
def samplerGenerator {A : Type*} [Fintype A] [DecidableEq A]
    (K : Matrix A A ℝ) : Matrix A A ℝ := K - 1

/-- The number of communicating classes for the two explicit binary witnesses:
two when there are no cross transitions and one otherwise. -/
noncomputable def binaryComponentCount (K : Matrix (Fin 2) (Fin 2) ℝ) : ℕ :=
  if K 0 1 = 0 ∧ K 1 0 = 0 then 2 else 1

/-- Directed spanning-tree weights for a two-state sampler. -/
def binaryRootedTreeWeights (K : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → ℝ
  | 0 => K 1 0
  | 1 => K 0 1

/-- The exact two-state absolute spectral gap.  For a row-stochastic binary
kernel the nontrivial eigenvalue is `K 0 0 - K 1 0`. -/
def binarySamplerGap (K : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  1 - |K 0 0 - K 1 0|

theorem binary_hidden_quantities_differ :
    samplerGenerator (1 : Matrix (Fin 2) (Fin 2) ℝ) ≠
        samplerGenerator uniformBinaryReset
    ∧ binaryComponentCount (1 : Matrix (Fin 2) (Fin 2) ℝ) ≠
        binaryComponentCount uniformBinaryReset
    ∧ binaryRootedTreeWeights (1 : Matrix (Fin 2) (Fin 2) ℝ) ≠
        binaryRootedTreeWeights uniformBinaryReset
    ∧ binarySamplerGap (1 : Matrix (Fin 2) (Fin 2) ℝ) ≠
        binarySamplerGap uniformBinaryReset := by
  constructor
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    norm_num [samplerGenerator, uniformBinaryReset, Matrix.one_apply] at h01
  constructor
  · norm_num [binaryComponentCount, uniformBinaryReset, Matrix.one_apply]
  constructor
  · intro h
    have h0 := congrFun h 0
    norm_num [binaryRootedTreeWeights, uniformBinaryReset,
      Matrix.one_apply] at h0
  · norm_num [binarySamplerGap, uniformBinaryReset, Matrix.one_apply]

/-- Uniform law on three atoms. -/
noncomputable def uniformThreeLaw (_ : Fin 3) : ℝ := 1 / 3

/-- Deterministic directed three-cycle. -/
noncomputable def directedThreeCycle : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if (i.1, j.1) = (0, 1) ∨ (i.1, j.1) = (1, 2) ∨
    (i.1, j.1) = (2, 0) then 1 else 0

/-- Complete uniform three-state reset. -/
noncomputable def uniformThreeReset : Matrix (Fin 3) (Fin 3) ℝ :=
  fun _ _ => 1 / 3

/-- Detailed balance for a declared stationary law. -/
def SamplerDetailedBalance {A : Type*} [Fintype A]
    (p : A → ℝ) (K : Matrix A A ℝ) : Prop :=
  ∀ i j, p i * K i j = p j * K j i

/-- An oriented circulation coordinate. -/
def threeCycleCirculation (K : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  K 0 1 - K 1 0

theorem threeSampler_stochasticWitnesses :
    IsRowStochastic directedThreeCycle ∧
      IsRowStochastic uniformThreeReset := by
  constructor <;> constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [directedThreeCycle]
  · intro i
    fin_cases i <;> norm_num [directedThreeCycle, Fin.sum_univ_three] <;> decide
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [uniformThreeReset]
  · intro i
    fin_cases i <;> norm_num [uniformThreeReset, Fin.sum_univ_three]

theorem threeSampler_stationaryWitnesses :
    IsStationaryLaw uniformThreeLaw directedThreeCycle ∧
      IsStationaryLaw uniformThreeLaw uniformThreeReset := by
  constructor <;> intro j <;> fin_cases j <;>
    norm_num [uniformThreeLaw, directedThreeCycle, uniformThreeReset,
      Fin.sum_univ_three]

theorem threeSampler_balance_and_circulation_differ :
    SamplerDetailedBalance uniformThreeLaw directedThreeCycle ≠
      SamplerDetailedBalance uniformThreeLaw uniformThreeReset
    ∧ threeCycleCirculation directedThreeCycle ≠
      threeCycleCirculation uniformThreeReset := by
  constructor
  · have hreset : SamplerDetailedBalance uniformThreeLaw
        uniformThreeReset := by
      intro i j
      fin_cases i <;> fin_cases j <;>
        norm_num [uniformThreeLaw, uniformThreeReset]
    have hcycle : ¬ SamplerDetailedBalance uniformThreeLaw
        directedThreeCycle := by
      intro h
      have h01 := h 0 1
      norm_num [uniformThreeLaw, directedThreeCycle] at h01
    intro heq
    apply hcycle
    rw [heq]
    exact hreset
  · norm_num [threeCycleCirculation, directedThreeCycle,
      uniformThreeReset]

/-- Restricted form of the two-witness nonidentifiability principle. -/
theorem admissibleQuantity_notIdentifiable
    {Sampler Table Quantity : Type*}
    (admissible : Sampler → Prop) (observe : Sampler → Table)
    (quantity : Sampler → Quantity) (S₀ S₁ : Sampler)
    (hS₀ : admissible S₀) (hS₁ : admissible S₁)
    (hobs : observe S₀ = observe S₁)
    (hquantity : quantity S₀ ≠ quantity S₁) :
    ¬∃ reconstruct : Table → Quantity,
      ∀ S, admissible S → reconstruct (observe S) = quantity S := by
  rintro ⟨reconstruct, hreconstruct⟩
  apply hquantity
  rw [← hreconstruct S₀ hS₀, ← hreconstruct S₁ hS₁, hobs]

/-- The complete fresh downstream table identifies none of the seven hidden
items listed in the manuscript: kernel, generator, balance, circulation,
components, rooted-tree weights, or spectral gap. -/
theorem fresh_sampler_all_dynamics_not_identifiable
    {Ω₂ H₂ Ω₃ H₃ : Type*}
    [Monoid H₂] [AddCommMonoid H₂] [Module ℝ H₂]
    [Monoid H₃] [AddCommMonoid H₃] [Module ℝ H₃]
    (Φ₂ : Ω₂ → Fin 2 → H₂) (I₂ : List Ω₂ → H₂)
    (Φ₃ : Ω₃ → Fin 3 → H₃) (I₃ : List Ω₃ → H₃) :
    let admissible₂ := fun K : Matrix (Fin 2) (Fin 2) ℝ ↦
      IsRowStochastic K ∧ IsStationaryLaw uniformBinaryLaw K
    let observe₂ := fun K ↦
      freshDownstreamTable uniformBinaryLaw K Φ₂ I₂
    let admissible₃ := fun K : Matrix (Fin 3) (Fin 3) ℝ ↦
      IsRowStochastic K ∧ IsStationaryLaw uniformThreeLaw K
    let observe₃ := fun K ↦
      freshDownstreamTable uniformThreeLaw K Φ₃ I₃
    (¬∃ r : FreshVisibleTable Ω₂ H₂ → Matrix (Fin 2) (Fin 2) ℝ,
        ∀ K, admissible₂ K → r (observe₂ K) = K)
    ∧ (¬∃ r : FreshVisibleTable Ω₂ H₂ → Matrix (Fin 2) (Fin 2) ℝ,
        ∀ K, admissible₂ K → r (observe₂ K) = samplerGenerator K)
    ∧ (¬∃ r : FreshVisibleTable Ω₃ H₃ → Prop,
        ∀ K, admissible₃ K →
          r (observe₃ K) = SamplerDetailedBalance uniformThreeLaw K)
    ∧ (¬∃ r : FreshVisibleTable Ω₃ H₃ → ℝ,
        ∀ K, admissible₃ K → r (observe₃ K) = threeCycleCirculation K)
    ∧ (¬∃ r : FreshVisibleTable Ω₂ H₂ → ℕ,
        ∀ K, admissible₂ K → r (observe₂ K) = binaryComponentCount K)
    ∧ (¬∃ r : FreshVisibleTable Ω₂ H₂ → (Fin 2 → ℝ),
        ∀ K, admissible₂ K → r (observe₂ K) = binaryRootedTreeWeights K)
    ∧ (¬∃ r : FreshVisibleTable Ω₂ H₂ → ℝ,
        ∀ K, admissible₂ K → r (observe₂ K) = binarySamplerGap K) := by
  dsimp only
  obtain ⟨hstochId, hstochReset⟩ := binarySampler_stochasticWitnesses
  obtain ⟨hstatId, hstatReset⟩ := binarySampler_stationaryWitnesses
  obtain ⟨hgen, hcomp, htree, hgap⟩ := binary_hidden_quantities_differ
  obtain ⟨hstochCycle, hstochReset₃⟩ := threeSampler_stochasticWitnesses
  obtain ⟨hstatCycle, hstatReset₃⟩ := threeSampler_stationaryWitnesses
  obtain ⟨hbalance, hcirculation⟩ :=
    threeSampler_balance_and_circulation_differ
  have hobs₂ := freshDownstreamTable_samplerInvariant uniformBinaryLaw
    (1 : Matrix (Fin 2) (Fin 2) ℝ) uniformBinaryReset Φ₂
    hstatId hstatReset I₂
  have hobs₃ := freshDownstreamTable_samplerInvariant uniformThreeLaw
    directedThreeCycle uniformThreeReset Φ₃ hstatCycle hstatReset₃ I₃
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact admissibleQuantity_notIdentifiable _ _ id _ _
      ⟨hstochId, hstatId⟩ ⟨hstochReset, hstatReset⟩ hobs₂
      binaryIdentity_ne_uniformReset
  · exact admissibleQuantity_notIdentifiable _ _ samplerGenerator _ _
      ⟨hstochId, hstatId⟩ ⟨hstochReset, hstatReset⟩ hobs₂ hgen
  · exact admissibleQuantity_notIdentifiable _ _
      (SamplerDetailedBalance uniformThreeLaw) _ _
      ⟨hstochCycle, hstatCycle⟩ ⟨hstochReset₃, hstatReset₃⟩ hobs₃ hbalance
  · exact admissibleQuantity_notIdentifiable _ _ threeCycleCirculation _ _
      ⟨hstochCycle, hstatCycle⟩ ⟨hstochReset₃, hstatReset₃⟩ hobs₃ hcirculation
  · exact admissibleQuantity_notIdentifiable _ _ binaryComponentCount _ _
      ⟨hstochId, hstatId⟩ ⟨hstochReset, hstatReset⟩ hobs₂ hcomp
  · exact admissibleQuantity_notIdentifiable _ _ binaryRootedTreeWeights _ _
      ⟨hstochId, hstatId⟩ ⟨hstochReset, hstatReset⟩ hobs₂ htree
  · exact admissibleQuantity_notIdentifiable _ _ binarySamplerGap _ _
      ⟨hstochId, hstatId⟩ ⟨hstochReset, hstatReset⟩ hobs₂ hgap

end NCG
