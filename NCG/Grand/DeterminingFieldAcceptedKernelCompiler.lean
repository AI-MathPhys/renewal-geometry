/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.GeneratedMinimalRecord

/-!
# Determining-field quotient and accepted-kernel compiler

This file completes `thm:determining-field-compiler`.  It uses literal
all-future signatures, so the right-congruence, descended primitive updates,
future-coordinate factorization, and unique coarsest quotient are constructive
theorems rather than assumptions.  It also gives the finite strict-round bound
and constructs the unique accepted transition kernel from resolved branch
probabilities.
-/

namespace NCG
namespace DeterminingFieldAcceptedKernelCompiler

open WordRecordMachine

/-- A certificate selecting one fresh block at each strict refinement stage
implies the sharp `|Theta|-1` bound on strict rounds. -/
theorem strictRefinementRounds_le_card_sub_one
    {N k : ℕ} (stageBlock : Fin (k + 1) → Fin N)
    (hstage : Function.Injective stageBlock) : k ≤ N - 1 := by
  have hcard : k + 1 ≤ N := by
    simpa using Fintype.card_le_of_injective stageBlock hstage
  omega

/-- A branch probability that is constant on complete-future classes descends
to the determining-field quotient. -/
noncomputable def quotientBranchProbability
    {A R D V : Type*} (M : WordRecordMachine A R D V)
    (p : R → A → ℝ)
    (hp : ∀ r s, M.futureSig r = M.futureSig s → ∀ a, p r a = p s a)
    (a : A) : MinRec M.futureSig → ℝ :=
  Quotient.lift (fun r => p r a) fun r s hrs => hp r s hrs a

@[simp] theorem quotientBranchProbability_mk
    {A R D V : Type*} (M : WordRecordMachine A R D V)
    (p : R → A → ℝ)
    (hp : ∀ r s, M.futureSig r = M.futureSig s → ∀ a, p r a = p s a)
    (r : R) (a : A) :
    quotientBranchProbability M p hp a
      (Quotient.mk (minRecSetoid M.futureSig) r) = p r a := rfl

/-- Table-native accepted transition: sum the resolved accepted branch masses
whose descended target is the requested quotient class. -/
noncomputable def acceptedDeterminingKernel
    {A R D V : Type*} [Fintype A]
    (M : WordRecordMachine A R D V)
    [DecidableEq (MinRec M.futureSig)]
    (p : R → A → ℝ)
    (hp : ∀ r s, M.futureSig r = M.futureSig s → ∀ a, p r a = p s a)
    (q q' : MinRec M.futureSig) : ℝ := by
  classical
  exact ∑ a, if M.quotientStep a q = q'
    then quotientBranchProbability M p hp a q else 0

/-- On a represented state, the compiled kernel is exactly the resolved
branch table grouped by target determining-field class. -/
theorem acceptedDeterminingKernel_mk
    {A R D V : Type*} [Fintype A]
    (M : WordRecordMachine A R D V)
    [DecidableEq (MinRec M.futureSig)]
    (p : R → A → ℝ)
    (hp : ∀ r s, M.futureSig r = M.futureSig s → ∀ a, p r a = p s a)
    (r : R) (q' : MinRec M.futureSig) :
    acceptedDeterminingKernel M p hp
        (Quotient.mk (minRecSetoid M.futureSig) r) q' =
      ∑ a, if Quotient.mk (minRecSetoid M.futureSig) (M.step a r) = q'
        then p r a else 0 := by
  simp [acceptedDeterminingKernel, quotientBranchProbability]
  rfl

/-- The grouped table is the unique accepted transition reproducing every
post-accepted determining-field class probability. -/
theorem acceptedDeterminingKernel_unique
    {A R D V : Type*} [Fintype A]
    (M : WordRecordMachine A R D V)
    [DecidableEq (MinRec M.futureSig)]
    (p : R → A → ℝ)
    (hp : ∀ r s, M.futureSig r = M.futureSig s → ∀ a, p r a = p s a)
    (K : MinRec M.futureSig → MinRec M.futureSig → ℝ)
    (hK : ∀ r q', K (Quotient.mk (minRecSetoid M.futureSig) r) q' =
      ∑ a, if Quotient.mk (minRecSetoid M.futureSig) (M.step a r) = q'
        then p r a else 0) :
    K = acceptedDeterminingKernel M p hp := by
  funext q q'
  induction q using Quotient.ind with
  | _ r =>
      rw [hK r q', acceptedDeterminingKernel_mk]

/-- Complete compiler package: literal future equality is the unique coarsest
sufficient quotient, primitive updates and every selected future descend
uniquely, strict refinement has the finite cardinal bound, and the accepted
kernel is the unique grouped branch table. -/
theorem determiningFieldAcceptedKernelCompiler
    {A R D V : Type*} [Fintype A]
    (M : WordRecordMachine A R D V)
    [DecidableEq (MinRec M.futureSig)]
    (p : R → A → ℝ)
    (hp : ∀ r s, M.futureSig r = M.futureSig s → ∀ a, p r a = p s a) :
    M.MinimalRecordExact ∧
    (∀ {N k : ℕ} (stageBlock : Fin (k + 1) → Fin N),
      Function.Injective stageBlock → k ≤ N - 1) ∧
    (∃! K : MinRec M.futureSig → MinRec M.futureSig → ℝ,
      ∀ r q', K (Quotient.mk (minRecSetoid M.futureSig) r) q' =
        ∑ a, if Quotient.mk (minRecSetoid M.futureSig) (M.step a r) = q'
          then p r a else 0) := by
  refine ⟨M.minimal_record_exact, ?_, ?_⟩
  · intro N k stageBlock hstage
    exact strictRefinementRounds_le_card_sub_one stageBlock hstage
  · refine ⟨acceptedDeterminingKernel M p hp,
      acceptedDeterminingKernel_mk M p hp, ?_⟩
    intro K hK
    exact acceptedDeterminingKernel_unique M p hp K hK

/-- Selected immediate branch probabilities are automatically constant on
determining-field classes, so the compiler needs no extra fibre-constancy
hypothesis when those probabilities are among the declared Read coordinates. -/
theorem determiningFieldAcceptedKernelCompiler_fromSelectedReads
    {A R D V : Type*} [Fintype A]
    (M : WordRecordMachine A R D V)
    [DecidableEq (MinRec M.futureSig)]
    (p : R → A → ℝ) (branchRead : A → D)
    (decode : V → ℝ)
    (hread : ∀ r a, p r a = decode (M.read (branchRead a) r)) :
    M.MinimalRecordExact ∧
    (∀ {N k : ℕ} (stageBlock : Fin (k + 1) → Fin N),
      Function.Injective stageBlock → k ≤ N - 1) ∧
    (∃! K : MinRec M.futureSig → MinRec M.futureSig → ℝ,
      ∀ r q', K (Quotient.mk (minRecSetoid M.futureSig) r) q' =
        ∑ a, if Quotient.mk (minRecSetoid M.futureSig) (M.step a r) = q'
          then p r a else 0) := by
  have hp : ∀ r s, M.futureSig r = M.futureSig s →
      ∀ a, p r a = p s a := by
    intro r s hrs a
    rw [hread r a, hread s a]
    exact congrArg decode (congrFun hrs ([], branchRead a))
  exact determiningFieldAcceptedKernelCompiler M p hp

end DeterminingFieldAcceptedKernelCompiler
end NCG
