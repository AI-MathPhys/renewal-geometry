/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompletionConservative
import NCG.Grand.ConservativeResolvedGradingExtensions
import NCG.Grand.GrandOrder
import NCG.Grand.CutoffSupport
import NCG.Grand.RecordSurvival
import NCG.Grand.IntrinsicRegularTrace

/-!
# Conservativity of the protected operational completion

This file completes the exact finite content of
`thm:SM-completion-conservative`.  In addition to the word-level conservative
extension, it proves that the normalized two-state completion preserves every
old contextual future-null class.  It also records physical Gram transport and
the central-density criterion distinguishing a pulled-back intrinsic trace
from the old normalized regular trace.
-/

open Matrix
open scoped Kronecker

namespace NCG

/-- The future metric on the resolved two-state completion.  The factor on the
new record is the normalized trace density `I₂ / 2`. -/
noncomputable def resolvedCompletionFutureMetric {h : Type*} [Fintype h]
    [DecidableEq h] (G : Matrix h h ℂ) :
    Matrix (h × Fin 2) (h × Fin 2) ℂ :=
  G ⊗ₖ ((2 : ℂ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ))

/-- The normalized completion metric evaluates an embedded old coefficient
exactly as the old future metric does. -/
theorem resolvedCompletionFutureMetric_trace_embed
    {h : Type*} [Fintype h] [DecidableEq h]
    (G A : Matrix h h ℂ) :
    (resolvedCompletionFutureMetric G * resolvedGradingEmbed A).trace =
      (G * A).trace := by
  rw [resolvedCompletionFutureMetric, resolvedGradingEmbed,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  simp

/-- The conservative resolved-grading embedding preserves multiplication. -/
theorem resolvedGradingEmbed_mul
    {h : Type*} [Fintype h] [DecidableEq h]
    (A B : Matrix h h ℂ) :
    resolvedGradingEmbed (A * B) =
      resolvedGradingEmbed A * resolvedGradingEmbed B := by
  change (A * B) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) =
    (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      (B ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Embedding an old coefficient preserves all old two-sided contextual null
tests.  Hence the induced map on old future-null quotient classes is
well-defined and injective whenever the old Reads separate those classes. -/
theorem resolvedCompletion_preserves_oldFutureNullClasses
    {h : Type*} [Fintype h] [DecidableEq h]
    (G A : Matrix h h ℂ) :
    A ∈ nullSubmodule G ↔
      ∀ X Y : Matrix h h ℂ,
        (resolvedCompletionFutureMetric G *
          (resolvedGradingEmbed X * resolvedGradingEmbed A *
            resolvedGradingEmbed Y)).trace = 0 := by
  constructor
  · intro hA X Y
    rw [← resolvedGradingEmbed_mul X A,
      ← resolvedGradingEmbed_mul (X * A) Y]
    exact (resolvedCompletionFutureMetric_trace_embed G (X * A * Y)).trans
      (hA X Y)
  · intro hA X Y
    have h := hA X Y
    rw [← resolvedGradingEmbed_mul X A,
      ← resolvedGradingEmbed_mul (X * A) Y] at h
    exact (resolvedCompletionFutureMetric_trace_embed G (X * A * Y)).symm.trans h

/-- Isometric restriction of a future synthesis transports every old word
Gram by the exact congruence from `thm:cutoff-compatibility`. -/
theorem operationalCompletion_physicalWordGram_transport
    {wOld wNew m : Type*} [Fintype wNew] [Fintype m]
    (VNew : Matrix m wNew ℂ) (includeOld : Matrix wNew wOld ℂ) :
    (VNew * includeOld)ᴴ * (VNew * includeOld) =
      includeOldᴴ * (VNewᴴ * VNew) * includeOld :=
  cutoff_compatibility VNew includeOld

/-- A trace pairing transported by a density equals the reference pairing
for every coefficient exactly when that density is the identity.  This is the
finite nondegeneracy clause needed for intrinsic regular-trace transport. -/
theorem centralDensityTraceTransport_eq_reference_iff
    {n : Type*} [Fintype n] [DecidableEq n]
    (density : Matrix n n ℂ) :
    (∀ A : Matrix n n ℂ,
      (density * A).trace = ((1 : Matrix n n ℂ) * A).trace) ↔
      density = 1 := by
  constructor
  · intro h
    exact cutoff_quotient_transport (n := n) (r := Unit) |>.2
      density 1 h
  · rintro rfl A
    rfl

/-- Contextually certified protected records survive the quotient, while a
separately certified transient sector is annihilated by record forgetting and
has zero leakage Gram. -/
theorem protectedRecords_survive_transientRecord_forgets
    {n ρ t e : Type*} [Fintype n] [Fintype t] [DecidableEq t]
    (G : Matrix n n ℂ) (protectedRecord : ρ → Matrix n n ℂ)
    (hprotected : ∀ r, ∃ X Y : Matrix n n ℂ,
      (G * (X * protectedRecord r * Y)).trace ≠ 0)
    (C : Matrix n t ℂ) (P Q : Matrix t t ℂ) (J : Matrix t e ℂ)
    (hPQ : P + Q = 1) (hCQ : C * Q = 0) (hQJ : Q * J = J) :
    (∀ r,
      (Submodule.Quotient.mk (protectedRecord r) :
          Matrix n n ℂ ⧸ nullSubmodule G) ≠ 0)
    ∧ C = C * P
    ∧ C * J = 0
    ∧ Jᴴ * (Cᴴ * C) * J = 0 := by
  refine ⟨?_, record_sink_nullity C P Q J hPQ hCQ hQJ⟩
  intro r
  exact (record_survival G).1 (protectedRecord r) |>.2 (hprotected r)

/-- Exact finite conservativity packet for the protected score-square
completion.  The five components are respectively word recovery, unital
star-monomorphism, old future-null preservation, physical Gram transport, and
the sharp central-density criterion for intrinsic traces.  Protected-record
survival and certified transient forgetting are supplied without weakening by
`record_survival` and `record_sink_nullity`. -/
theorem protectedOperationalCompletion_conservative
    {h ι wOld wNew m : Type*}
    [Fintype h] [DecidableEq h]
    [Fintype wNew] [Fintype m]
    (K : ι → Matrix h h ℂ) (G : Matrix h h ℂ)
    (VNew : Matrix m wNew ℂ) (includeOld : Matrix wNew wOld ℂ)
    (density : Matrix h h ℂ) :
    (∀ word : List ι,
      discardResolvedGrading
          ((word.map (fun a => resolvedGradingEmbed (K a))).prod) =
        representedWord K word)
    ∧ (∀ A B : Matrix h h ℂ,
        resolvedGradingEmbed (A * B) =
          resolvedGradingEmbed A * resolvedGradingEmbed B)
    ∧ (∀ A : Matrix h h ℂ,
        A ∈ nullSubmodule G ↔
          ∀ X Y : Matrix h h ℂ,
            (resolvedCompletionFutureMetric G *
              (resolvedGradingEmbed X * resolvedGradingEmbed A *
                resolvedGradingEmbed Y)).trace = 0)
    ∧ ((VNew * includeOld)ᴴ * (VNew * includeOld) =
        includeOldᴴ * (VNewᴴ * VNew) * includeOld)
    ∧ ((∀ A : Matrix h h ℂ,
          (density * A).trace = ((1 : Matrix h h ℂ) * A).trace) ↔
        density = 1) := by
  refine ⟨conservativeResolvedGrading_word K, ?_,
    resolvedCompletion_preserves_oldFutureNullClasses G,
    operationalCompletion_physicalWordGram_transport VNew includeOld,
    centralDensityTraceTransport_eq_reference_iff density⟩
  intro A B
  exact resolvedGradingEmbed_mul A B

end NCG
