/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteFutureSaturatedExperimentState

/-!
# Universal Markov retract and reset branch

Exact finite-matrix equivalences for deterministic Markov records, their
stationary conditional decoders, stationary reversals, and the stronger
within-cell reset identity.
-/

open Finset Matrix

namespace NCG
namespace UniversalMarkovRetract

/-- Fine-to-coarse deterministic record matrix. -/
def recordMatrix {U Z : Type*} [DecidableEq Z] (c : U → Z) : Matrix U Z ℝ :=
  fun u z ↦ if c u = z then 1 else 0

/-- Stationary mass of a record cell. -/
noncomputable def cellMass {U Z : Type*} [Fintype U] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (z : Z) : ℝ :=
  ∑ u, if c u = z then m u else 0

theorem cellMass_eq_pushforwardRow
    {U Z : Type*} [Fintype U] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (z : Z) :
    cellMass c m z = AcceptedActionInformationPythagoras.pushforwardRow c m z := by
  classical
  simp [cellMass, AcceptedActionInformationPythagoras.pushforwardRow,
    Finset.sum_filter]

theorem cellMass_pos {U Z : Type*} [Fintype U] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c) (m : U → ℝ)
    (hm : ∀ u, 0 < m u) (z : Z) : 0 < cellMass c m z := by
  rw [cellMass_eq_pushforwardRow]
  exact AcceptedActionInformationPythagoras.pushforwardRow_pos c m hc hm z

/-- Conditional stationary decoder from a coarse cell to its fine fibre. -/
noncomputable def stationaryDecoder
    {U Z : Type*} [Fintype U] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) : Matrix Z U ℝ :=
  fun z u ↦ if c u = z then m u / cellMass c m z else 0

/-- The deterministic record followed by its stationary decoder is the
identity on coarse rows. -/
theorem stationaryDecoder_mul_recordMatrix
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c) (m : U → ℝ)
    (hm : ∀ u, 0 < m u) :
    stationaryDecoder c m * recordMatrix c = 1 := by
  classical
  ext z z'
  by_cases hzz : z = z'
  · subst z'
    simp only [Matrix.mul_apply, stationaryDecoder, recordMatrix]
    rw [show (∑ u, (if c u = z then m u / cellMass c m z else 0) *
        (if c u = z then 1 else 0)) =
        ∑ u, if c u = z then m u / cellMass c m z else 0 by
      apply Finset.sum_congr rfl
      intro u _
      split <;> simp_all]
    rw [← Finset.sum_filter, ← Finset.sum_div]
    have hmass : ∑ u ∈ Finset.univ.filter (fun u ↦ c u = z), m u =
        cellMass c m z := by
      simp [cellMass, Finset.sum_filter]
    rw [hmass, div_self (ne_of_gt (cellMass_pos c hc m hm z))]
    simp
  · simp only [Matrix.mul_apply, stationaryDecoder, recordMatrix]
    have hsum :
        (∑ u, (if c u = z then m u / cellMass c m z else 0) *
          (if c u = z' then 1 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro u _
      by_cases huz' : c u = z'
      · have huz : c u ≠ z := by
          intro h
          exact hzz (h.symm.trans huz')
        simp [huz', huz, hzz, Ne.symm hzz]
      · simp [huz']
    rw [hsum]
    simp [Matrix.one_apply, hzz]

/-- Fine-space conditional expectation associated with the record. -/
noncomputable def conditionalExpectation
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) : Matrix U U ℝ :=
  recordMatrix c * stationaryDecoder c m

/-- Coarse update obtained by encode-update-decode. -/
noncomputable def coarseKernel
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (K : Matrix U U ℝ) : Matrix Z Z ℝ :=
  stationaryDecoder c m * K * recordMatrix c

/-- Universal retract equivalence: commutation with conditional expectation is
equivalent to the two exact intertwinings. -/
theorem commutes_iff_two_sided_intertwining
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c) (m : U → ℝ)
    (hm : ∀ u, 0 < m u) (K : Matrix U U ℝ) :
    conditionalExpectation c m * K = K * conditionalExpectation c m ↔
      K * recordMatrix c = recordMatrix c * coarseKernel c m K ∧
      stationaryDecoder c m * K = coarseKernel c m K * stationaryDecoder c m := by
  have hRC := stationaryDecoder_mul_recordMatrix c hc m hm
  let C := recordMatrix c
  let R := stationaryDecoder c m
  let E := conditionalExpectation c m
  let L := coarseKernel c m K
  have hEC : E * C = C := by
    simp only [E, conditionalExpectation, C, R]
    rw [Matrix.mul_assoc, hRC, Matrix.mul_one]
  have hRE : R * E = R := by
    simp only [E, conditionalExpectation, C, R]
    rw [← Matrix.mul_assoc, hRC, Matrix.one_mul]
  change E * K = K * E ↔ K * C = C * L ∧ R * K = L * R
  constructor
  · intro hcomm
    constructor
    · calc
        K * C = K * (E * C) := by rw [hEC]
        _ = (K * E) * C := by rw [Matrix.mul_assoc]
        _ = (E * K) * C := by rw [hcomm]
        _ = C * L := by simp [E, L, conditionalExpectation, coarseKernel,
          C, R, Matrix.mul_assoc]
    · calc
        R * K = (R * E) * K := by rw [hRE]
        _ = R * (E * K) := by rw [Matrix.mul_assoc]
        _ = R * (K * E) := by rw [hcomm]
        _ = L * R := by simp [E, L, conditionalExpectation, coarseKernel,
          C, R, Matrix.mul_assoc]
  · rintro ⟨hKC, hRK⟩
    calc
      E * K = C * (R * K) := by simp [E, conditionalExpectation, C, R,
        Matrix.mul_assoc]
      _ = C * (L * R) := by rw [hRK]
      _ = (C * L) * R := by rw [Matrix.mul_assoc]
      _ = (K * C) * R := by rw [hKC]
      _ = K * E := by simp [E, conditionalExpectation, C, R, Matrix.mul_assoc]

/-- Exact quotient dynamics for every fine row. -/
theorem fine_row_quotient_dynamics
    {U Z : Type*} [Fintype U] [Fintype Z]
    (p : Matrix Unit U ℝ) (K : Matrix U U ℝ)
    (C : Matrix U Z ℝ) (L : Matrix Z Z ℝ) (hKC : K * C = C * L) :
    (p * K) * C = (p * C) * L := by
  rw [Matrix.mul_assoc, hKC, Matrix.mul_assoc]

/-- Exact reconstructed fine dynamics for every decoded coarse row. -/
theorem decoded_row_fine_dynamics
    {U Z : Type*} [Fintype U] [Fintype Z]
    (q : Matrix Unit Z ℝ) (K : Matrix U U ℝ)
    (R : Matrix Z U ℝ) (L : Matrix Z Z ℝ) (hRK : R * K = L * R) :
    (q * R) * K = (q * L) * R := by
  rw [Matrix.mul_assoc, hRK, Matrix.mul_assoc]

/-- A faithful row is stationary for a row-stochastic update. -/
def IsStationary {U : Type*} [Fintype U]
    (m : U → ℝ) (K : Matrix U U ℝ) : Prop :=
  ∀ v, ∑ u, m u * K u v = m v

/-- Stationary reversal in row convention:
`K♯(v,u) = m(u) K(u,v) / m(v)`. -/
noncomputable def stationaryReversal {U : Type*}
    (m : U → ℝ) (K : Matrix U U ℝ) : Matrix U U ℝ :=
  fun v u ↦ m u * K u v / m v

/-- Reversal of the coarse update with respect to cell masses. -/
noncomputable def coarseReversal
    {U Z : Type*} [Fintype U] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (L : Matrix Z Z ℝ) : Matrix Z Z ℝ :=
  fun z z' ↦ cellMass c m z' * L z' z / cellMass c m z

/-- Strong lumpability through a deterministic partition, with the displayed
coarse kernel as witness. -/
def StronglyLumpable
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (K : Matrix U U ℝ) (L : Matrix Z Z ℝ) : Prop :=
  K * recordMatrix c = recordMatrix c * L

noncomputable def weightedIncomingBlock
    {U Z : Type*} [Fintype U] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (K : Matrix U U ℝ)
    (z : Z) (v : U) : ℝ :=
  ∑ u, if c u = z then m u * K u v else 0

theorem stationaryDecoder_mul_apply
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (K : Matrix U U ℝ) (z : Z) (v : U) :
    (stationaryDecoder c m * K) z v =
      weightedIncomingBlock c m K z v / cellMass c m z := by
  classical
  rw [Matrix.mul_apply]
  unfold stationaryDecoder weightedIncomingBlock
  calc
    ∑ u, (if c u = z then m u / cellMass c m z else 0) * K u v =
        ∑ u, (if c u = z then m u * K u v else 0) / cellMass c m z := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : c u = z
      · simp [h]
        ring
      · simp [h]
    _ = (∑ u, if c u = z then m u * K u v else 0) /
        cellMass c m z := by rw [Finset.sum_div]

theorem mul_stationaryDecoder_apply
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (L : Matrix Z Z ℝ) (z : Z) (v : U) :
    (L * stationaryDecoder c m) z v =
      L z (c v) * m v / cellMass c m (c v) := by
  classical
  rw [Matrix.mul_apply]
  unfold stationaryDecoder
  calc
    ∑ y, L z y * (if c v = y then m v / cellMass c m y else 0) =
        ∑ y, if c v = y then L z y * (m v / cellMass c m y) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      split <;> simp_all
    _ = L z (c v) * (m v / cellMass c m (c v)) := by simp
    _ = L z (c v) * m v / cellMass c m (c v) := by ring

theorem stationaryReversal_mul_record_apply
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (K : Matrix U U ℝ) (v : U) (z : Z) :
    (stationaryReversal m K * recordMatrix c) v z =
      weightedIncomingBlock c m K z v / m v := by
  classical
  rw [Matrix.mul_apply]
  unfold stationaryReversal recordMatrix weightedIncomingBlock
  calc
    ∑ u, (m u * K u v / m v) * (if c u = z then 1 else 0) =
        ∑ u, (if c u = z then m u * K u v else 0) / m v := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : c u = z
      · simp [h]
      · simp [h]
    _ = (∑ u, if c u = z then m u * K u v else 0) / m v := by
      rw [Finset.sum_div]

theorem record_mul_coarseReversal_apply
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (L : Matrix Z Z ℝ) (v : U) (z : Z) :
    (recordMatrix c * coarseReversal c m L) v z =
      cellMass c m z * L z (c v) / cellMass c m (c v) := by
  classical
  rw [Matrix.mul_apply]
  unfold recordMatrix coarseReversal
  calc
    ∑ y, (if c v = y then 1 else 0) *
        (cellMass c m z * L z y / cellMass c m y) =
      ∑ y, if c v = y then
        cellMass c m z * L z y / cellMass c m y else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          split <;> simp_all
    _ = cellMass c m z * L z (c v) / cellMass c m (c v) := by simp

/-- Decoder invariance is exactly forward lumpability of the stationary
reversal through the same deterministic partition. -/
theorem decoder_intertwining_iff_reversal_lumpability
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c) (m : U → ℝ)
    (hm : ∀ u, 0 < m u) (K : Matrix U U ℝ) (L : Matrix Z Z ℝ)
    (_hstationary : IsStationary m K) :
    stationaryDecoder c m * K = L * stationaryDecoder c m ↔
      StronglyLumpable c (stationaryReversal m K) (coarseReversal c m L) := by
  constructor
  · intro hRK
    unfold StronglyLumpable
    ext v z
    have hvz := congrArg (fun M : Matrix Z U ℝ ↦ M z v) hRK
    rw [stationaryDecoder_mul_apply, mul_stationaryDecoder_apply] at hvz
    rw [stationaryReversal_mul_record_apply, record_mul_coarseReversal_apply]
    field_simp [ne_of_gt (hm v), ne_of_gt (cellMass_pos c hc m hm z),
      ne_of_gt (cellMass_pos c hc m hm (c v))] at hvz ⊢
    ring_nf at hvz ⊢
    exact hvz
  · intro hrev
    unfold StronglyLumpable at hrev
    ext z v
    have hvz := congrArg (fun M : Matrix U Z ℝ ↦ M v z) hrev
    rw [stationaryReversal_mul_record_apply, record_mul_coarseReversal_apply] at hvz
    rw [stationaryDecoder_mul_apply, mul_stationaryDecoder_apply]
    field_simp [ne_of_gt (hm v), ne_of_gt (cellMass_pos c hc m hm z),
      ne_of_gt (cellMass_pos c hc m hm (c v))] at hvz ⊢
    ring_nf at hvz ⊢
    exact hvz

/-- Complete manuscript equivalence: conditional-expectation commutation,
two-sided intertwining, and simultaneous forward/reversed strong lumpability. -/
theorem markov_retract_equivalences
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c) (m : U → ℝ)
    (hm : ∀ u, 0 < m u) (K : Matrix U U ℝ)
    (hstationary : IsStationary m K) :
    conditionalExpectation c m * K = K * conditionalExpectation c m ↔
      (K * recordMatrix c = recordMatrix c * coarseKernel c m K ∧
        stationaryDecoder c m * K =
          coarseKernel c m K * stationaryDecoder c m) ∧
      (StronglyLumpable c K (coarseKernel c m K) ∧
        StronglyLumpable c (stationaryReversal m K)
          (coarseReversal c m (coarseKernel c m K))) := by
  rw [commutes_iff_two_sided_intertwining c hc m hm K]
  constructor
  · intro h
    refine ⟨h, ⟨h.1, ?_⟩⟩
    exact (decoder_intertwining_iff_reversal_lumpability
      c hc m hm K (coarseKernel c m K) hstationary).1 h.2
  · rintro ⟨h, _⟩
    exact h

/-- The displayed reset factorization is exactly double projection of the
fine update. -/
theorem reset_factorization_eq_double_projection
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (K : Matrix U U ℝ) :
    recordMatrix c * coarseKernel c m K * stationaryDecoder c m =
      conditionalExpectation c m * K * conditionalExpectation c m := by
  simp [coarseKernel, conditionalExpectation, Matrix.mul_assoc]

/-- For an idempotent conditional expectation, reset is equivalent to erasing
all within-cell motion on both the input and output side. -/
theorem double_projection_eq_iff_absorbed
    {U : Type*} [Fintype U] (E K : Matrix U U ℝ) (hE : E * E = E) :
    K = E * K * E ↔ E * K = K ∧ K * E = K := by
  constructor
  · intro hreset
    have hleftRewrite : E * K = E * (E * K * E) :=
      congrArg (fun X : Matrix U U ℝ ↦ E * X) hreset
    have hrightRewrite : K * E = (E * K * E) * E :=
      congrArg (fun X : Matrix U U ℝ ↦ X * E) hreset
    constructor
    · calc
        E * K = E * (E * K * E) := hleftRewrite
        _ = (E * E) * K * E := by simp [Matrix.mul_assoc]
        _ = E * K * E := by rw [hE]
        _ = K := hreset.symm
    · calc
        K * E = (E * K * E) * E := hrightRewrite
        _ = E * K * (E * E) := by simp [Matrix.mul_assoc]
        _ = E * K * E := by rw [hE]
        _ = K := hreset.symm
  · rintro ⟨hleft, hright⟩
    symm
    calc
      E * K * E = K * E := by rw [hleft]
      _ = K := hright

theorem conditionalExpectation_idempotent
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c) (m : U → ℝ)
    (hm : ∀ u, 0 < m u) :
    conditionalExpectation c m * conditionalExpectation c m =
      conditionalExpectation c m := by
  let C := recordMatrix c
  let R := stationaryDecoder c m
  have hRC : R * C = (1 : Matrix Z Z ℝ) :=
    stationaryDecoder_mul_recordMatrix c hc m hm
  change (C * R) * (C * R) = C * R
  calc
    (C * R) * (C * R) = C * (R * C) * R := by simp [Matrix.mul_assoc]
    _ = C * R := by rw [hRC]; simp

/-- Exact characterization of the stronger reset branch. -/
theorem reset_iff_erases_within_cell_motion
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (c : U → Z) (hc : Function.Surjective c) (m : U → ℝ)
    (hm : ∀ u, 0 < m u) (K : Matrix U U ℝ) :
    K = recordMatrix c * coarseKernel c m K * stationaryDecoder c m ↔
      conditionalExpectation c m * K = K ∧
        K * conditionalExpectation c m = K := by
  rw [reset_factorization_eq_double_projection]
  exact double_projection_eq_iff_absorbed _ _
    (conditionalExpectation_idempotent c hc m hm)

/-- Exact Markov closure need not imply reset: whenever a nontrivial
conditional expectation exists, the identity update commutes with it but
retains within-cell information. -/
theorem identity_update_markov_but_not_reset
    {U : Type*} [Fintype U] [DecidableEq U] (E : Matrix U U ℝ)
    (hE : E * E = E) (hne : E ≠ 1) :
    E * (1 : Matrix U U ℝ) = 1 * E ∧
      (1 : Matrix U U ℝ) ≠ E * 1 * E := by
  constructor
  · simp
  · simpa [hE] using Ne.symm hne

/-! ## Finite simultaneous forward/reversal partition refinement -/

/-- Total transition mass from `u` into a finite set of target states. -/
def massIntoSet {U : Type*} [Fintype U]
    (K : Matrix U U ℝ) (u : U) (S : Finset U) : ℝ :=
  ∑ v ∈ S, K u v

/-- A set is a union of blocks of the relation represented by `P`. -/
def IsBlockUnion {U : Type*} [DecidableEq U]
    (P : Finset (U × U)) (S : Finset U) : Prop :=
  ∀ ⦃u v⦄, (u, v) ∈ P → (u ∈ S ↔ v ∈ S)

/-- Simultaneous stability for a forward kernel and its reversal.  The use of
all block-unions is equivalent, on a finite partition, to equality of the
mass entering every individual block. -/
def SimultaneouslyStableOnBlocks
    {U : Type*} [Fintype U] [DecidableEq U]
    (K Krev : Matrix U U ℝ) (P : Finset (U × U)) : Prop :=
  ∀ ⦃u v⦄, (u, v) ∈ P → ∀ S : Finset U, IsBlockUnion P S →
    massIntoSet K u S = massIntoSet K v S ∧
      massIntoSet Krev u S = massIntoSet Krev v S

/-- One forward/reversal splitter step: retain precisely the pairs in the
current partition having identical forward and reversed block-mass profiles. -/
noncomputable def splitByForwardReversedBlockMasses
    {U : Type*} [Fintype U] [DecidableEq U]
    (K Krev : Matrix U U ℝ) (P : Finset (U × U)) : Finset (U × U) := by
  classical
  exact P.filter fun uv ↦ ∀ S : Finset U, IsBlockUnion P S →
    massIntoSet K uv.1 S = massIntoSet K uv.2 S ∧
      massIntoSet Krev uv.1 S = massIntoSet Krev uv.2 S

theorem splitByForwardReversedBlockMasses_subset
    {U : Type*} [Fintype U] [DecidableEq U]
    (K Krev : Matrix U U ℝ) (P : Finset (U × U)) :
    splitByForwardReversedBlockMasses K Krev P ⊆ P := by
  classical
  intro uv huv
  exact (Finset.mem_filter.1 huv).1

theorem split_eq_self_iff_stable
    {U : Type*} [Fintype U] [DecidableEq U]
    (K Krev : Matrix U U ℝ) (P : Finset (U × U)) :
    splitByForwardReversedBlockMasses K Krev P = P ↔
      SimultaneouslyStableOnBlocks K Krev P := by
  classical
  constructor
  · intro hsplit u v huv S hS
    have hmem : (u, v) ∈ splitByForwardReversedBlockMasses K Krev P := by
      rw [hsplit]
      exact huv
    exact (Finset.mem_filter.1 hmem).2 S hS
  · intro hstable
    apply Finset.Subset.antisymm
    · exact splitByForwardReversedBlockMasses_subset K Krev P
    · intro uv huv
      change uv ∈ P.filter _
      rw [Finset.mem_filter]
      exact ⟨huv, fun S hS ↦ hstable huv S hS⟩

/-- Refinement does not lose any already-stable finer partition.  This is the
key coarseness invariant: a block-union for `P` is also a block-union for
every finer relation `Q`. -/
theorem stable_refinement_subset_split
    {U : Type*} [Fintype U] [DecidableEq U]
    (K Krev : Matrix U U ℝ) (P Q : Finset (U × U))
    (hQP : Q ⊆ P) (hQ : SimultaneouslyStableOnBlocks K Krev Q) :
    Q ⊆ splitByForwardReversedBlockMasses K Krev P := by
  classical
  intro uv huv
  change uv ∈ P.filter _
  rw [Finset.mem_filter]
  refine ⟨hQP huv, ?_⟩
  intro S hSP
  apply hQ huv S
  intro u v huvQ
  exact hSP (hQP huvQ)

/-- A finite refinement result, bundled with its stability and universal
coarseness property among stable refinements of the starting partition. -/
structure StableRefinementResult
    {U : Type*} [Fintype U] [DecidableEq U]
    (K Krev : Matrix U U ℝ) (P : Finset (U × U)) where
  partition : Finset (U × U)
  refines : partition ⊆ P
  stable : SimultaneouslyStableOnBlocks K Krev partition
  coarsest : ∀ Q : Finset (U × U), Q ⊆ P →
    SimultaneouslyStableOnBlocks K Krev Q → Q ⊆ partition

/-- Finite partition refinement terminates because every nontrivial splitter
step strictly decreases the finite relation. -/
noncomputable def finiteForwardReversedRefinement
    {U : Type*} [Fintype U] [DecidableEq U]
    (K Krev : Matrix U U ℝ) (P : Finset (U × U)) :
    StableRefinementResult K Krev P := by
  classical
  let Pnext := splitByForwardReversedBlockMasses K Krev P
  by_cases hfixed : Pnext = P
  · exact
      { partition := P
        refines := Finset.Subset.rfl
        stable := (split_eq_self_iff_stable K Krev P).1 hfixed
        coarsest := fun Q hQP _ ↦ hQP }
  · have hproper : Pnext ⊂ P :=
      Finset.ssubset_iff_subset_ne.2
        ⟨splitByForwardReversedBlockMasses_subset K Krev P, hfixed⟩
    let result := finiteForwardReversedRefinement K Krev Pnext
    exact
      { partition := result.partition
        refines := result.refines.trans
          (splitByForwardReversedBlockMasses_subset K Krev P)
        stable := result.stable
        coarsest := by
          intro Q hQP hQ
          apply result.coarsest Q
          · exact stable_refinement_subset_split K Krev P Q hQP hQ
          · exact hQ }
termination_by P.card
decreasing_by
  exact Finset.card_lt_card hproper

/-- The refinement algorithm returns the unique coarsest simultaneous stable
refinement of the supplied partition. -/
theorem finiteForwardReversedRefinement_spec
    {U : Type*} [Fintype U] [DecidableEq U]
    (K Krev : Matrix U U ℝ) (P : Finset (U × U)) :
    let result := finiteForwardReversedRefinement K Krev P
    result.partition ⊆ P ∧
      SimultaneouslyStableOnBlocks K Krev result.partition ∧
      ∀ Q : Finset (U × U), Q ⊆ P →
        SimultaneouslyStableOnBlocks K Krev Q → Q ⊆ result.partition := by
  let result := finiteForwardReversedRefinement K Krev P
  exact ⟨result.refines, result.stable, result.coarsest⟩

/-- Relation-pair encoding of a deterministic starting quotient. -/
def quotientPartitionPairs
    {U Z : Type*} [Fintype U] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) : Finset (U × U) :=
  Finset.univ.filter fun uv ↦ c uv.1 = c uv.2

/-- Applied to the stationary reversal, finite block-mass refinement produces
the unique coarsest refinement of the given quotient that is simultaneously
stable for the forward and reversed updates. -/
theorem unique_coarsest_stationary_markov_refinement
    {U Z : Type*} [Fintype U] [DecidableEq U] [DecidableEq Z]
    (c : U → Z) (m : U → ℝ) (K : Matrix U U ℝ) :
    let P₀ := quotientPartitionPairs c
    let result := finiteForwardReversedRefinement K (stationaryReversal m K) P₀
    result.partition ⊆ P₀ ∧
      SimultaneouslyStableOnBlocks K (stationaryReversal m K) result.partition ∧
      ∀ Q : Finset (U × U), Q ⊆ P₀ →
        SimultaneouslyStableOnBlocks K (stationaryReversal m K) Q →
          Q ⊆ result.partition := by
  exact finiteForwardReversedRefinement_spec K (stationaryReversal m K)
    (quotientPartitionPairs c)

end UniversalMarkovRetract
end NCG
