/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact terminating conditional-Gaussian compiler

This is the finite ordered decision procedure of `thm:SMQG-compiler`.  The
packet records the nine branch tests performed after the complete precision
and physical reflection data have been assembled.  `compile` follows QG.3--10
in order and returns exactly one of the ten outputs in QG.85.  `Certifies`
records the entire first-failure path, so the main theorem proves not just
termination but exhaustive and exclusive branch certification.
-/

namespace NCG
namespace ConditionalGaussianCompiler

/-- The ten outputs in QG.85. -/
inductive Verdict where
  | positiveConditionalGaussianReflectedKernel
  | negativeOrNonHermitianOneParticleWord
  | softTailMode
  | gaussianWickFailure
  | wordRelationFailure
  | complexOrNegativeLineWeight
  | divisorOrZeroModePacket
  | pfaffianSignObstruction
  | nonQuasiFreeBosonicMixture
  | cutoffLeakageOrConcentrationWitness
  deriving DecidableEq, Repr

/-- Decidable tests at one cutoff and one fixed bosonic history. -/
structure Packet where
  hardSchurBranch : Bool
  reflectedCovariancePositiveHermitian : Bool
  lineWeightRealNonnegative : Bool
  gaussianWickOccurrencePass : Bool
  physicalWordRelationsPass : Bool
  awayFromDivisor : Bool
  pfaffianSignTransportPass : Bool
  bosonicMixtureQuasiFree : Bool
  cutoffTransportUniformlyIntegrable : Bool
  deriving DecidableEq, Repr

/-- The ordered QG.3--10 compiler. -/
def compile (p : Packet) : Verdict :=
  if !p.hardSchurBranch then
    .softTailMode
  else if !p.reflectedCovariancePositiveHermitian then
    .negativeOrNonHermitianOneParticleWord
  else if !p.lineWeightRealNonnegative then
    .complexOrNegativeLineWeight
  else if !p.gaussianWickOccurrencePass then
    .gaussianWickFailure
  else if !p.physicalWordRelationsPass then
    .wordRelationFailure
  else if !p.awayFromDivisor then
    .divisorOrZeroModePacket
  else if !p.pfaffianSignTransportPass then
    .pfaffianSignObstruction
  else if !p.bosonicMixtureQuasiFree then
    .nonQuasiFreeBosonicMixture
  else if !p.cutoffTransportUniformlyIntegrable then
    .cutoffLeakageOrConcentrationWitness
  else
    .positiveConditionalGaussianReflectedKernel

/-- Exact first-failure evidence for every QG.85 verdict. -/
def Certifies (p : Packet) : Verdict → Prop
  | .softTailMode =>
      p.hardSchurBranch = false
  | .negativeOrNonHermitianOneParticleWord =>
      p.hardSchurBranch = true ∧
      p.reflectedCovariancePositiveHermitian = false
  | .complexOrNegativeLineWeight =>
      p.hardSchurBranch = true ∧
      p.reflectedCovariancePositiveHermitian = true ∧
      p.lineWeightRealNonnegative = false
  | .gaussianWickFailure =>
      p.hardSchurBranch = true ∧
      p.reflectedCovariancePositiveHermitian = true ∧
      p.lineWeightRealNonnegative = true ∧
      p.gaussianWickOccurrencePass = false
  | .wordRelationFailure =>
      p.hardSchurBranch = true ∧
      p.reflectedCovariancePositiveHermitian = true ∧
      p.lineWeightRealNonnegative = true ∧
      p.gaussianWickOccurrencePass = true ∧
      p.physicalWordRelationsPass = false
  | .divisorOrZeroModePacket =>
      p.hardSchurBranch = true ∧
      p.reflectedCovariancePositiveHermitian = true ∧
      p.lineWeightRealNonnegative = true ∧
      p.gaussianWickOccurrencePass = true ∧
      p.physicalWordRelationsPass = true ∧
      p.awayFromDivisor = false
  | .pfaffianSignObstruction =>
      p.hardSchurBranch = true ∧
      p.reflectedCovariancePositiveHermitian = true ∧
      p.lineWeightRealNonnegative = true ∧
      p.gaussianWickOccurrencePass = true ∧
      p.physicalWordRelationsPass = true ∧
      p.awayFromDivisor = true ∧
      p.pfaffianSignTransportPass = false
  | .nonQuasiFreeBosonicMixture =>
      p.hardSchurBranch = true ∧
      p.reflectedCovariancePositiveHermitian = true ∧
      p.lineWeightRealNonnegative = true ∧
      p.gaussianWickOccurrencePass = true ∧
      p.physicalWordRelationsPass = true ∧
      p.awayFromDivisor = true ∧
      p.pfaffianSignTransportPass = true ∧
      p.bosonicMixtureQuasiFree = false
  | .cutoffLeakageOrConcentrationWitness =>
      p.hardSchurBranch = true ∧
      p.reflectedCovariancePositiveHermitian = true ∧
      p.lineWeightRealNonnegative = true ∧
      p.gaussianWickOccurrencePass = true ∧
      p.physicalWordRelationsPass = true ∧
      p.awayFromDivisor = true ∧
      p.pfaffianSignTransportPass = true ∧
      p.bosonicMixtureQuasiFree = true ∧
      p.cutoffTransportUniformlyIntegrable = false
  | .positiveConditionalGaussianReflectedKernel =>
      p.hardSchurBranch = true ∧
      p.reflectedCovariancePositiveHermitian = true ∧
      p.lineWeightRealNonnegative = true ∧
      p.gaussianWickOccurrencePass = true ∧
      p.physicalWordRelationsPass = true ∧
      p.awayFromDivisor = true ∧
      p.pfaffianSignTransportPass = true ∧
      p.bosonicMixtureQuasiFree = true ∧
      p.cutoffTransportUniformlyIntegrable = true

/-- Each returned verdict is equivalent to its full ordered certificate. -/
theorem compile_eq_iff_certifies (p : Packet) (v : Verdict) :
    compile p = v ↔ Certifies p v := by
  unfold compile
  split
  · cases v <;> simp_all [Certifies]
  · split
    · cases v <;> simp_all [Certifies]
    · split
      · cases v <;> simp_all [Certifies]
      · split
        · cases v <;> simp_all [Certifies]
        · split
          · cases v <;> simp_all [Certifies]
          · split
            · cases v <;> simp_all [Certifies]
            · split
              · cases v <;> simp_all [Certifies]
              · split
                · cases v <;> simp_all [Certifies]
                · split
                  · cases v <;> simp_all [Certifies]
                  · cases v <;> simp_all [Certifies]

theorem compile_certified (p : Packet) : Certifies p (compile p) :=
  (compile_eq_iff_certifies p (compile p)).mp rfl

theorem compile_eq_of_certifies {p : Packet} {v : Verdict}
    (h : Certifies p v) : compile p = v :=
  (compile_eq_iff_certifies p v).mpr h

theorem certified_verdict_unique {p : Packet} {v w : Verdict}
    (hv : Certifies p v) (hw : Certifies p w) : v = w := by
  rw [← compile_eq_of_certifies hv, ← compile_eq_of_certifies hw]

/-- **Terminating conditional-Gaussian compiler.**  Every finite QG packet
has exactly one certified verdict among the ten alternatives of QG.85. -/
theorem terminating_conditional_Gaussian_compiler (p : Packet) :
    ∃! v : Verdict, Certifies p v := by
  refine ⟨compile p, compile_certified p, ?_⟩
  intro v hv
  exact certified_verdict_unique hv (compile_certified p)

end ConditionalGaussianCompiler
end NCG
