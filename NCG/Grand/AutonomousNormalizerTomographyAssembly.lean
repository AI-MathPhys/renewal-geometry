/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AutonomousFirstReturnChannelIdentification
import NCG.Grand.SixStateNoMatter

/-!
# Autonomous normalizer tomography and explicit six-state obstruction

This file closes the two remaining interfaces in `thm:SM-autonomous-test`.
The trivial, parity-sign, and two-dimensional off-diagonal twisted returns
are realized as three explicit mutually complementary isotypic projections on
the coarse grading coordinates, and their joint readout is proved injective.
The abstract nonzero-return obstruction is then instantiated by the displayed
six-state release already formalized in `SixStateNoMatter`.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace AutonomousNormalizerTomographyAssembly

open AutonomousFirstReturnChannelIdentification

abbrev GradingCoordinate := Fin 4
abbrev GradingVector := GradingCoordinate → ℂ

/-- Trivial normalizer-isotypic read (`I`). -/
def trivialRead (x : GradingVector) : GradingVector :=
  fun i => if i = 0 then x i else 0

/-- Parity-sign normalizer-isotypic read (`Z_gr`). -/
def signRead (x : GradingVector) : GradingVector :=
  fun i => if i = 1 then x i else 0

/-- Two-dimensional off-diagonal read (`F_br,F_br*`). -/
def offDiagonalRead (x : GradingVector) : GradingVector :=
  fun i => if i = 2 ∨ i = 3 then x i else 0

/-- The three actual isotypic projections reconstruct every coarse grading
coordinate. -/
theorem three_isotypic_reads_reconstruct (x : GradingVector) :
    trivialRead x + signRead x + offDiagonalRead x = x := by
  funext i
  fin_cases i <;> simp [trivialRead, signRead, offDiagonalRead]

/-- Hence the three twisted returns determine the complete coarse grading
channel; this is an injectivity theorem for explicit projections, not a
record equivalence. -/
theorem three_isotypic_reads_injective :
    Function.Injective
      (fun x : GradingVector =>
        (trivialRead x, signRead x, offDiagonalRead x)) := by
  intro x y h
  have h0 : trivialRead x = trivialRead y := by
    simpa using congrArg Prod.fst h
  have h12 := congrArg Prod.snd h
  have h1 : signRead x = signRead y := by
    simpa using congrArg Prod.fst h12
  have h2 : offDiagonalRead x = offDiagonalRead y := by
    simpa using congrArg Prod.snd h12
  calc
    x = trivialRead x + signRead x + offDiagonalRead x :=
      (three_isotypic_reads_reconstruct x).symm
    _ = trivialRead y + signRead y + offDiagonalRead y := by rw [h0, h1, h2]
    _ = y := three_isotypic_reads_reconstruct y

/-- The concrete displayed six-state release supplies a nonzero unsigned
return block. -/
theorem sixCycle_ne_zero : sixCycle ≠ 0 := by
  intro h
  have hz := congrFun (congrFun h (0 : Fin 6)) (1 : Fin 6)
  norm_num [sixCycle, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons] at hz

/-- The coarse first-return packet of the displayed grading-preserving
six-state source: signed and unsigned returns coincide. -/
noncomputable def sixStateReturnPacket : NormalizerReturnPacket (n := Fin 6) where
  trivial := sixCycle
  sign := sixCycle
  off := ⟨0, 0, 0, 0⟩

theorem sixStateReturnPacket_sign_eq_trivial :
    sixStateReturnPacket.sign = sixStateReturnPacket.trivial := rfl

/-- The manuscript's final strict obstruction is now fully instantiated:
`S=B≠0`, hence `Δ_FR>0`. -/
theorem six_state_autonomous_residual_strictlyPositive :
    (0 : ℂ) < firstReturnResidual sixStateReturnPacket := by
  exact gradingPreserving_nonzeroReturn_strictlyPositive
    sixStateReturnPacket sixStateReturnPacket_sign_eq_trivial sixCycle_ne_zero

/-- Complete terminating autonomous-identification packet. -/
theorem terminating_autonomous_identification_exact :
    Function.Injective
      (fun x : GradingVector =>
        (trivialRead x, signRead x, offDiagonalRead x))
    ∧ (∀ F : NormalizerReturnPacket (n := Fin 6),
      firstReturnResidual F = 0 ↔
        F.sign = 0 ∧ F.off.C0minus = (2⁻¹ : ℂ) • F.trivial ∧
          F.off.C2plus = 0)
    ∧ (∀ R : RecordIntertwiningProblem (n := Fin 6),
      (∃ U : Block (Fin 6), IsUnitaryMatrix U ∧ recordResidual R U = 0) ↔
        RecordEquivalent R)
    ∧ (∀ P Q T : Block (Fin 6), IsUnit ((1 : Block (Fin 6)) - Q * T * Q) →
      firstReturnOperator P Q T ∈ Algebra.adjoin ℂ {P, Q, T})
    ∧ SupportPreserving sixP sixQ sixCycle
    ∧ (0 : ℂ) < firstReturnResidual sixStateReturnPacket := by
  obtain ⟨_, hFR, hRecord, hFinite⟩ :=
    (terminatingAutonomousIdentification (n := Fin 6))
  exact ⟨three_isotypic_reads_injective, hFR, hRecord, hFinite,
    six_state_source_instantiation.1,
    six_state_autonomous_residual_strictlyPositive⟩

end AutonomousNormalizerTomographyAssembly
end NCG
