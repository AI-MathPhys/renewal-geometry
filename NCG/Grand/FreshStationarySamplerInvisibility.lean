/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Fresh stationary sampler invisibility

This file performs the finite freshness reduction for a hidden Markov sampler.
The terminal hidden atom is summed out at every opportunity, and no hidden
coordinate is propagated to the next visible cycle.
-/

open Matrix

namespace NCG

/-- Finite row-stochastic kernels. -/
def IsRowStochastic {A : Type*} [Fintype A]
    (K : Matrix A A ℝ) : Prop :=
  (∀ i j, 0 ≤ K i j) ∧ ∀ i, ∑ j, K i j = 1

/-- A finite law is stationary for a row-stochastic convention kernel when
`pᵀK = pᵀ`.  Stochasticity itself is not needed for the algebraic reduction. -/
def IsStationaryLaw {A : Type*} [Fintype A]
    (p : A → ℝ) (K : Matrix A A ℝ) : Prop :=
  ∀ j, ∑ i, p i * K i j = p j

/-- The hidden terminal law after a duration of `t` sampler steps. -/
def hiddenTerminalLaw {A : Type*} [Fintype A] [DecidableEq A]
    (p : A → ℝ) (K : Matrix A A ℝ) (t : ℕ) (j : A) : ℝ :=
  ∑ i, p i * (K ^ t) i j

/-- A stationary source remains stationary after every admitted hidden
duration. -/
theorem stationaryLaw_matrixPower {A : Type*} [Fintype A] [DecidableEq A]
    (p : A → ℝ) (K : Matrix A A ℝ) (hstat : IsStationaryLaw p K) :
    ∀ t j, hiddenTerminalLaw p K t j = p j := by
  intro t
  induction t with
  | zero =>
      intro j
      simp [hiddenTerminalLaw, Matrix.one_apply]
  | succ t ih =>
      intro j
      change (∑ i, p i * (K ^ (t + 1)) i j) = p j
      rw [pow_succ]
      calc
        (∑ i, p i * (K ^ t * K) i j) =
            ∑ k, (∑ i, p i * (K ^ t) i k) * K k j := by
          simp only [Matrix.mul_apply, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = ∑ k, p k * K k j := by
          apply Finset.sum_congr rfl
          intro k _
          rw [show (∑ i, p i * (K ^ t) i k) =
              hiddenTerminalLaw p K t k from rfl, ih k]
        _ = p j := hstat j

/-- The visible branch obtained after a hidden duration and terminal-atom
discard. -/
def sampledVisibleBranch {A Ω H : Type*} [Fintype A] [DecidableEq A]
    [AddCommMonoid H] [Module ℝ H]
    (p : A → ℝ) (K : Matrix A A ℝ)
    (Φ : Ω → A → H) (t : ℕ) (ω : Ω) : H :=
  ∑ i, hiddenTerminalLaw p K t i • Φ ω i

/-- The branch averaged directly against the fresh source law. -/
def freshAveragedBranch {A Ω H : Type*} [Fintype A]
    [AddCommMonoid H] [Module ℝ H]
    (p : A → ℝ) (Φ : Ω → A → H) (ω : Ω) : H :=
  ∑ i, p i • Φ ω i

/-- Stationarity removes both the hidden sampler and its duration from every
single visible branch. -/
theorem sampledVisibleBranch_eq_freshAverage
    {A Ω H : Type*} [Fintype A] [DecidableEq A]
    [AddCommMonoid H] [Module ℝ H]
    (p : A → ℝ) (K : Matrix A A ℝ)
    (Φ : Ω → A → H) (hstat : IsStationaryLaw p K)
    (t : ℕ) (ω : Ω) :
    sampledVisibleBranch p K Φ t ω = freshAveragedBranch p Φ ω := by
  apply Finset.sum_congr rfl
  intro i _
  rw [stationaryLaw_matrixPower p K hstat t i]

/-- A resolved downstream word with arbitrary visible interventions.  The
intervention at a step may depend on the entire remaining visible history,
which is enough to encode an adaptive family after reversing chronology. -/
def freshAdaptiveDownstreamWord {A Ω H : Type*}
    [Fintype A] [DecidableEq A] [Monoid H]
    [AddCommMonoid H] [Module ℝ H]
    (p : A → ℝ) (K : Matrix A A ℝ) (Φ : Ω → A → H)
    (intervention : List Ω → H) : List (ℕ × Ω) → H
  | [] => 1
  | (t, ω) :: word =>
      intervention (word.map Prod.snd) * sampledVisibleBranch p K Φ t ω *
        freshAdaptiveDownstreamWord p K Φ intervention word

/-- The sampler-free word built only from the averaged visible branches. -/
def averagedAdaptiveDownstreamWord {A Ω H : Type*}
    [Fintype A] [Monoid H] [AddCommMonoid H] [Module ℝ H]
    (p : A → ℝ) (Φ : Ω → A → H)
    (intervention : List Ω → H) : List (ℕ × Ω) → H
  | [] => 1
  | (_, ω) :: word =>
      intervention (word.map Prod.snd) * freshAveragedBranch p Φ ω *
        averagedAdaptiveDownstreamWord p Φ intervention word

/-- Every resolved word and adaptive visible intervention family reduces to
composition of the averaged branches; the hidden duration at each opportunity
is absent from the result. -/
theorem freshAdaptiveDownstreamWord_eq_averaged
    {A Ω H : Type*} [Fintype A] [DecidableEq A]
    [Monoid H] [AddCommMonoid H] [Module ℝ H]
    (p : A → ℝ) (K : Matrix A A ℝ) (Φ : Ω → A → H)
    (hstat : IsStationaryLaw p K)
    (intervention : List Ω → H) :
    ∀ word,
      freshAdaptiveDownstreamWord p K Φ intervention word =
        averagedAdaptiveDownstreamWord p Φ intervention word
  | [] => rfl
  | (t, ω) :: word => by
      simp only [freshAdaptiveDownstreamWord,
        averagedAdaptiveDownstreamWord]
      rw [sampledVisibleBranch_eq_freshAverage p K Φ hstat t ω,
        freshAdaptiveDownstreamWord_eq_averaged p K Φ hstat intervention word]

/-- Any two stationary samplers with the same fresh law give the same complete
resolved/adaptive downstream word, even when their admitted durations differ
at every opportunity. -/
theorem freshAdaptiveDownstreamWord_samplerInvariant
    {A Ω H : Type*} [Fintype A] [DecidableEq A]
    [Monoid H] [AddCommMonoid H] [Module ℝ H]
    (p : A → ℝ) (K₀ K₁ : Matrix A A ℝ) (Φ : Ω → A → H)
    (hstat₀ : IsStationaryLaw p K₀) (hstat₁ : IsStationaryLaw p K₁)
    (intervention : List Ω → H)
    (word₀ word₁ : List (ℕ × Ω))
    (hvisible : word₀.map Prod.snd = word₁.map Prod.snd) :
    freshAdaptiveDownstreamWord p K₀ Φ intervention word₀ =
      freshAdaptiveDownstreamWord p K₁ Φ intervention word₁ := by
  rw [freshAdaptiveDownstreamWord_eq_averaged p K₀ Φ hstat₀,
    freshAdaptiveDownstreamWord_eq_averaged p K₁ Φ hstat₁]
  clear hstat₀ hstat₁
  induction word₀ generalizing word₁ with
  | nil =>
      cases word₁ <;> simp_all [averagedAdaptiveDownstreamWord]
  | cons head tail ih =>
      cases head with
      | mk t ω =>
        cases word₁ with
        | nil => simp at hvisible
        | cons head₁ tail₁ =>
          cases head₁ with
          | mk t₁ ω₁ =>
            simp only [List.map_cons, List.cons.injEq] at hvisible
            rcases hvisible with ⟨hω, htail⟩
            subst ω₁
            simp only [averagedAdaptiveDownstreamWord]
            rw [ih tail₁ htail, htail]

/-- Terminal Reads cannot distinguish equal downstream words. -/
theorem freshTerminalRead_invariant
    {A Ω H R : Type*} [Fintype A] [DecidableEq A]
    [Monoid H] [AddCommMonoid H] [Module ℝ H]
    (p : A → ℝ) (K : Matrix A A ℝ) (Φ : Ω → A → H)
    (hstat : IsStationaryLaw p K)
    (intervention : List Ω → H) (read : H → R)
    (word : List (ℕ × Ω)) :
    read (freshAdaptiveDownstreamWord p K Φ intervention word) =
      read (averagedAdaptiveDownstreamWord p Φ intervention word) := by
  rw [freshAdaptiveDownstreamWord_eq_averaged p K Φ hstat intervention word]

/-- The complete resolved downstream table of a hidden sampler. -/
def freshDownstreamTable {A Ω H : Type*}
    [Fintype A] [DecidableEq A] [Monoid H]
    [AddCommMonoid H] [Module ℝ H]
    (p : A → ℝ) (K : Matrix A A ℝ) (Φ : Ω → A → H)
    (intervention : List Ω → H) : List (ℕ × Ω) → H :=
  fun word => freshAdaptiveDownstreamWord p K Φ intervention word

/-- The complete table, simultaneously over all durations and visible words,
is identical for any two stationary hidden samplers with the same fresh law. -/
theorem freshDownstreamTable_samplerInvariant
    {A Ω H : Type*} [Fintype A] [DecidableEq A]
    [Monoid H] [AddCommMonoid H] [Module ℝ H]
    (p : A → ℝ) (K₀ K₁ : Matrix A A ℝ) (Φ : Ω → A → H)
    (hstat₀ : IsStationaryLaw p K₀) (hstat₁ : IsStationaryLaw p K₁)
    (intervention : List Ω → H) :
    freshDownstreamTable p K₀ Φ intervention =
      freshDownstreamTable p K₁ Φ intervention := by
  funext word
  exact freshAdaptiveDownstreamWord_samplerInvariant p K₀ K₁ Φ
    hstat₀ hstat₁ intervention word word rfl

/-- The uniform law on two hidden atoms. -/
noncomputable def uniformBinaryLaw (_ : Fin 2) : ℝ := 1 / 2

/-- A fresh uniform reset kernel. -/
noncomputable def uniformBinaryReset : Matrix (Fin 2) (Fin 2) ℝ :=
  fun _ _ => 1 / 2

/-- Both the identity sampler and the reset sampler preserve the same
full-support uniform source. -/
theorem binarySampler_stationaryWitnesses :
    IsStationaryLaw uniformBinaryLaw (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
  IsStationaryLaw uniformBinaryLaw uniformBinaryReset := by
  constructor <;> intro j <;> fin_cases j <;>
    norm_num [uniformBinaryLaw, uniformBinaryReset,
      Matrix.one_apply, Fin.sum_univ_two]

/-- The two binary witnesses are valid stochastic kernels. -/
theorem binarySampler_stochasticWitnesses :
    IsRowStochastic (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    IsRowStochastic uniformBinaryReset := by
  constructor
  · constructor
    · intro i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · intro i
      fin_cases i <;>
        simp [Matrix.one_apply]
  · constructor
    · intro i j
      norm_num [uniformBinaryReset]
    · intro i
      norm_num [uniformBinaryReset, Fin.sum_univ_two]

/-- The two stationary binary samplers are genuinely different. -/
theorem binaryIdentity_ne_uniformReset :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) ≠ uniformBinaryReset := by
  intro h
  have hij := congrArg (fun K => K 0 1) h
  norm_num [uniformBinaryReset, Matrix.one_apply] at hij

/-- Explicit non-identifiability witness: no decoder of the complete
downstream table recovers every stationary stochastic binary kernel. -/
theorem binaryKernel_notIdentifiableFromDownstreamTable
    {Ω H : Type*} [Monoid H] [AddCommMonoid H] [Module ℝ H]
    (Φ : Ω → Fin 2 → H) (intervention : List Ω → H) :
    ¬∃ reconstruct : (List (ℕ × Ω) → H) → Matrix (Fin 2) (Fin 2) ℝ,
      ∀ K, IsRowStochastic K → IsStationaryLaw uniformBinaryLaw K →
        reconstruct (freshDownstreamTable uniformBinaryLaw K Φ intervention) = K := by
  rintro ⟨reconstruct, hreconstruct⟩
  rcases binarySampler_stochasticWitnesses with ⟨hstochId, hstochReset⟩
  rcases binarySampler_stationaryWitnesses with ⟨hstatId, hstatReset⟩
  apply binaryIdentity_ne_uniformReset
  rw [← hreconstruct 1 hstochId hstatId,
    ← hreconstruct uniformBinaryReset hstochReset hstatReset,
    freshDownstreamTable_samplerInvariant uniformBinaryLaw
      1 uniformBinaryReset Φ hstatId hstatReset intervention]

/-- A hidden quantity cannot be reconstructed from an observation that agrees
on two samplers where that quantity differs.  This applies uniformly to the
kernel, generator, balance/circulation data, communicating components,
tree-weight data, and spectral gap. -/
theorem hiddenSamplerQuantity_notIdentifiable
    {Sampler Table Quantity : Type*}
    (observe : Sampler → Table) (quantity : Sampler → Quantity)
    (S₀ S₁ : Sampler) (hobs : observe S₀ = observe S₁)
    (hquantity : quantity S₀ ≠ quantity S₁) :
    ¬∃ reconstruct : Table → Quantity,
      ∀ S, reconstruct (observe S) = quantity S := by
  rintro ⟨reconstruct, hreconstruct⟩
  apply hquantity
  rw [← hreconstruct S₀, ← hreconstruct S₁, hobs]

end NCG
