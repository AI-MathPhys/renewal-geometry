/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PhaseSelection

/-!
# Exact finite classification of the synchronized Store phase

This module proves the classification layer of
`thm:primitive-phase-selection`.  A `PrimitivePhasePacket` separates
complete exposed operational coordinates from the three invisible choices
allowed in the manuscript: minimal-Stinespring coordinates, simultaneous
determinant-sign naming, and rank-one Kraus phases.  Operational isomorphism
is equality of the complete operational coordinates and therefore ignores
exactly those gauge fields.

The eight residual components are literal finite Hilbert--Schmidt squares.
Their common zero locus is proved to be the canonical twenty-five-cell
instrument, not merely an abstract list of zero defects.
-/

namespace NCG

open Matrix

/-- Squared real Hilbert--Schmidt norm of a finite matrix. -/
def realHSSq {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, (M i j) ^ 2

theorem realHSSq_nonneg {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) : 0 ≤ realHSSq M := by
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem realHSSq_eq_zero_iff {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) :
    realHSSq M = 0 ↔ M = 0 := by
  constructor
  · intro h
    have hi : ∀ i, ∑ j, (M i j) ^ 2 = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        fun i (_ : i ∈ Finset.univ) =>
          Finset.sum_nonneg fun _ _ => sq_nonneg (M i _)).mp h
      exact fun i => hz i (Finset.mem_univ i)
    ext i j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      fun j (_ : j ∈ Finset.univ) => sq_nonneg (M i j)).mp (hi i)
    have hs : (M i j) ^ 2 = 0 := hj j (Finset.mem_univ j)
    simpa using (sq_eq_zero_iff.mp hs)
  · rintro rfl
    simp [realHSSq]

/-- Complete gauge-invariant coordinates of the finite enriched packet.
The error matrices are the normalized coordinates of the seven declared
relation panels; `instrument` is the exposed deterministic Store--Read
table itself. -/
structure PrimitivePhaseObservable where
  oddRead : ℝ
  exhaustionError : Matrix (Fin 25) (Fin 25) ℝ
  lockingError : Matrix (Fin 25) (Fin 25) ℝ
  multiplicityError : Matrix (Fin 25) (Fin 25) ℝ
  reversalError : Matrix (Fin 25) (Fin 25) ℝ
  edgeError : Matrix (Fin 25) (Fin 25) ℝ
  covarianceError : Matrix (Fin 25) (Fin 25) ℝ
  adaptednessError : ℝ
  instrument : Matrix (Fin 25) (Fin 25) ℝ

@[ext]
theorem PrimitivePhaseObservable.ext
    {X Y : PrimitivePhaseObservable}
    (hodd : X.oddRead = Y.oddRead)
    (hexh : X.exhaustionError = Y.exhaustionError)
    (hlock : X.lockingError = Y.lockingError)
    (hmult : X.multiplicityError = Y.multiplicityError)
    (hrev : X.reversalError = Y.reversalError)
    (hedge : X.edgeError = Y.edgeError)
    (hcov : X.covarianceError = Y.covarianceError)
    (had : X.adaptednessError = Y.adaptednessError)
    (hinst : X.instrument = Y.instrument) : X = Y := by
  cases X
  cases Y
  simp_all

/-- The locked twenty-five-cell synchronized Store phase in operational
coordinates: all relation errors vanish, the retained odd Read is normalized,
and the deterministic writer is the identity table. -/
def lockedTwentyFiveObservable : PrimitivePhaseObservable where
  oddRead := 1
  exhaustionError := 0
  lockingError := 0
  multiplicityError := 0
  reversalError := 0
  edgeError := 0
  covarianceError := 0
  adaptednessError := 0
  instrument := 1

/-- Raw enriched packet.  The last three fields record precisely the
coordinate freedoms declared operationally irrelevant in the manuscript. -/
structure PrimitivePhasePacket where
  observable : PrimitivePhaseObservable
  renewalNative : Prop
  allPortsExposedOrReconstructed : Prop
  typedSupportsNonzero : Prop
  primitiveWordPanelSaturated : Prop
  stinespringCoordinate : ℕ
  determinantSignsExchanged : Bool
  krausPhaseCoordinate : Fin 25 → ℝ

/-- The hypotheses separating the downstream enriched packet from autonomous
renewal. -/
def PrimitivePhasePacket.DomainAdmissible
    (X : PrimitivePhasePacket) : Prop :=
  X.renewalNative ∧ X.allPortsExposedOrReconstructed ∧
    X.typedSupportsNonzero ∧ X.primitiveWordPanelSaturated

/-- Operational isomorphism after quotienting the allowed Stinespring,
sign-name, and rank-one Kraus-phase coordinate changes. -/
def PrimitivePhasePacket.OperationallyIsomorphic
    (X Y : PrimitivePhasePacket) : Prop :=
  X.observable = Y.observable

/-- A canonical raw representative.  Its gauge fields have no operational
meaning. -/
def lockedTwentyFivePacket : PrimitivePhasePacket where
  observable := lockedTwentyFiveObservable
  renewalNative := True
  allPortsExposedOrReconstructed := True
  typedSupportsNonzero := True
  primitiveWordPanelSaturated := True
  stinespringCoordinate := 0
  determinantSignsExchanged := false
  krausPhaseCoordinate := fun _ => 0

/-- The selected locked phase, including the independent domain assumptions. -/
def PrimitivePhasePacket.IsLockedSynchronizedStore
    (X : PrimitivePhasePacket) : Prop :=
  X.DomainAdmissible ∧ X.OperationallyIsomorphic lockedTwentyFivePacket

/-- The least nonzero singular value of the normalized rank-one odd Read
panel.  In these quotient coordinates that panel is the `1 × 1` matrix
with entry `oddRead`. -/
def primitiveOddMargin (X : PrimitivePhasePacket) : ℝ :=
  |X.observable.oddRead|

/-- The eight residual categories in the order displayed by the manuscript. -/
def primitivePhaseResidualComponent
    (X : PrimitivePhasePacket) : Fin 8 → ℝ :=
  ![realHSSq X.observable.exhaustionError,
    realHSSq X.observable.lockingError,
    realHSSq X.observable.multiplicityError,
    realHSSq X.observable.reversalError +
      (X.observable.oddRead - 1) ^ 2,
    realHSSq X.observable.edgeError,
    realHSSq X.observable.covarianceError,
    X.observable.adaptednessError ^ 2,
    realHSSq (X.observable.instrument - 1)]

/-- The boxed downstream synchronized Store-loading residual. -/
def primitivePhaseResidual (X : PrimitivePhasePacket) : ℝ :=
  ∑ i, primitivePhaseResidualComponent X i

theorem primitivePhaseResidualComponent_nonneg
    (X : PrimitivePhasePacket) (i : Fin 8) :
    0 ≤ primitivePhaseResidualComponent X i := by
  fin_cases i <;>
    simp [primitivePhaseResidualComponent, realHSSq_nonneg]
  exact add_nonneg (realHSSq_nonneg _) (sq_nonneg _)
  exact sq_nonneg _

/-- Vanishing of the full, concrete residual reconstructs every operational
coordinate of the locked twenty-five-cell phase. -/
theorem primitivePhaseResidual_zero_iff
    (X : PrimitivePhasePacket) :
    primitivePhaseResidual X = 0 ↔
      X.observable = lockedTwentyFiveObservable := by
  rw [primitivePhaseResidual,
    phase_panel_zero_iff _ (primitivePhaseResidualComponent_nonneg X)]
  constructor
  · intro h
    have h0 := h (0 : Fin 8)
    have h1 := h (1 : Fin 8)
    have h2 := h (2 : Fin 8)
    have h3 := h (3 : Fin 8)
    have h4 := h (4 : Fin 8)
    have h5 := h (5 : Fin 8)
    have h6 := h (6 : Fin 8)
    have h7 := h (7 : Fin 8)
    simp [primitivePhaseResidualComponent] at h0 h1 h2 h3 h4 h5 h6 h7
    have hrev : realHSSq X.observable.reversalError = 0 :=
      le_antisymm (by nlinarith [sq_nonneg (X.observable.oddRead - 1)])
        (realHSSq_nonneg _)
    have hodd : X.observable.oddRead = 1 := by
      have : (X.observable.oddRead - 1) ^ 2 = 0 := by
        nlinarith [realHSSq_nonneg X.observable.reversalError]
      nlinarith
    apply PrimitivePhaseObservable.ext
    · exact hodd
    · exact (realHSSq_eq_zero_iff _).mp h0
    · exact (realHSSq_eq_zero_iff _).mp h1
    · exact (realHSSq_eq_zero_iff _).mp h2
    · exact (realHSSq_eq_zero_iff _).mp hrev
    · exact (realHSSq_eq_zero_iff _).mp h4
    · exact (realHSSq_eq_zero_iff _).mp h5
    · simpa [lockedTwentyFiveObservable] using h6
    · have hw := (realHSSq_eq_zero_iff
        (X.observable.instrument - 1)).mp h7
      exact sub_eq_zero.mp hw
  · intro h
    intro i
    fin_cases i <;>
      simp [primitivePhaseResidualComponent, h, lockedTwentyFiveObservable,
        realHSSq]

/-- Exact two-directional finite domain-enriched synchronized-interface
classification. -/
theorem primitive_phase_selection_classification
    (X : PrimitivePhasePacket)
    (hrenewal : X.renewalNative)
    (hexposed : X.allPortsExposedOrReconstructed)
    (hsupport : X.typedSupportsNonzero)
    (hsaturated : X.primitiveWordPanelSaturated) :
    (0 < primitiveOddMargin X ∧ primitivePhaseResidual X = 0) ↔
      X.IsLockedSynchronizedStore := by
  constructor
  · rintro ⟨_, hzero⟩
    refine ⟨⟨hrenewal, hexposed, hsupport, hsaturated⟩, ?_⟩
    exact (primitivePhaseResidual_zero_iff X).mp hzero
  · rintro ⟨_, hiso⟩
    have hobs : X.observable = lockedTwentyFiveObservable := hiso
    constructor
    · rw [primitiveOddMargin, hobs]
      norm_num [lockedTwentyFiveObservable]
    · exact (primitivePhaseResidual_zero_iff X).mpr hobs

/-- A positive residual component is a concrete least first-failure witness. -/
theorem primitivePhase_firstFailure
    (X : PrimitivePhasePacket) (hfail : 0 < primitivePhaseResidual X) :
    ∃ i : Fin 8, 0 < primitivePhaseResidualComponent X i ∧
      ∀ j, j < i → primitivePhaseResidualComponent X j = 0 := by
  apply first_failure_witness
    (primitivePhaseResidualComponent X)
    (primitivePhaseResidualComponent_nonneg X)
  intro hall
  have : primitivePhaseResidual X = 0 := by
    simp [primitivePhaseResidual, hall]
  linarith

/-- The two kinds of extra datum named in the manuscript when a tested
coordinate is not exposed. -/
inductive PrimitivePhaseAdditionalDatum
  | contextualRead
  | environmentPOVM
  deriving DecidableEq

/-- Multiplicity and covariance are environment coordinates; the other
residual panels are decided by exposed contextual Reads. -/
def primitivePhaseRequiredDatum (i : Fin 8) :
    PrimitivePhaseAdditionalDatum :=
  if i = 2 ∨ i = 5 then
    .environmentPOVM
  else
    .contextualRead

/-- Once a coordinate is missing, supplying exactly its declared Read or
environment POVM is necessary and sufficient to make that term testable. -/
theorem primitivePhase_missingDatum_exact
    (exposed : Fin 8 → Bool) (i : Fin 8) (hi : exposed i = false)
    (d : PrimitivePhaseAdditionalDatum) :
    (exposed i = true ∨ d = primitivePhaseRequiredDatum i) ↔
      d = primitivePhaseRequiredDatum i := by
  simp [hi]

end NCG
