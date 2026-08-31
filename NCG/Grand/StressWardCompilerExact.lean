/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact terminating stress/Ward compiler

This file encodes `thm:SMOS-compiler` from the Gran--Tensor manuscript.  A
finite cutoff packet supplies the eleven decidable tests appearing in the
theorem, in their prescribed order.  `compile` returns one of the twelve
manuscript verdicts.  The predicate `Certifies` records the complete
first-failure certificate: every earlier test passed and the named test is the
first one that failed (or every test passed in the final branch).

The main results prove that the compiler terminates, its verdict has exactly
the advertised certificate, every certificate determines the verdict, and two
different verdicts cannot both be certified.  Thus the result is an exhaustive
and exclusive finite decision procedure rather than an unstructured list of
possible labels.
-/

namespace NCG
namespace StressWardCompiler

/-- The twelve outputs of the stress/Ward compiler, in manuscript order. -/
inductive Verdict where
  | inheritedCompositeContactDomainObstruction
  | nuisanceShortOrSourceAtlasDefect
  | sourceMinimalWardAnomalyWriter
  | contactCocycleOrTripleOccurrenceFailure
  | conservationSymmetryOrGradedLocalityWitness
  | energyDensityHamiltonianMismatch
  | unfixedAbsoluteEnergyPressureFibre
  | newTraceSource
  | scaleOccurrenceOrSchemeTransportDefect
  | gaussianOrQuasiFreeStressResponse
  | movingStressSourceWithoutLocalLimit
  | representedStressCurrentSectorWithNonzeroExcess
  deriving DecidableEq, Repr

/-- The finite collection of yes/no tests performed at one cutoff.

Each Boolean says that the corresponding manuscript test passed.  The excess
test is phrased positively: `nonzeroStressCompositeExcess = false` is the
Gaussian/quasi-free verdict. -/
structure Packet where
  inheritedCompositeReady : Bool
  nuisanceShortPhysicalAndAtlasComplete : Bool
  wardRowsPass : Bool
  contactCocycleAndTripleOccurrencePass : Bool
  quotientConservationSymmetryLocalityPass : Bool
  energyDensityMatchesHamiltonian : Bool
  absoluteEnergyPressureFibreFixed : Bool
  traceSourceInDeclaredBasis : Bool
  scaleOccurrenceAndSchemeTransportPass : Bool
  nonzeroStressCompositeExcess : Bool
  stressSourceHasLocalLimit : Bool
  deriving DecidableEq, Repr

/-- The literal ordered finite compiler from `thm:SMOS-compiler`. -/
def compile (p : Packet) : Verdict :=
  if !p.inheritedCompositeReady then
    .inheritedCompositeContactDomainObstruction
  else if !p.nuisanceShortPhysicalAndAtlasComplete then
    .nuisanceShortOrSourceAtlasDefect
  else if !p.wardRowsPass then
    .sourceMinimalWardAnomalyWriter
  else if !p.contactCocycleAndTripleOccurrencePass then
    .contactCocycleOrTripleOccurrenceFailure
  else if !p.quotientConservationSymmetryLocalityPass then
    .conservationSymmetryOrGradedLocalityWitness
  else if !p.energyDensityMatchesHamiltonian then
    .energyDensityHamiltonianMismatch
  else if !p.absoluteEnergyPressureFibreFixed then
    .unfixedAbsoluteEnergyPressureFibre
  else if !p.traceSourceInDeclaredBasis then
    .newTraceSource
  else if !p.scaleOccurrenceAndSchemeTransportPass then
    .scaleOccurrenceOrSchemeTransportDefect
  else if !p.nonzeroStressCompositeExcess then
    .gaussianOrQuasiFreeStressResponse
  else if !p.stressSourceHasLocalLimit then
    .movingStressSourceWithoutLocalLimit
  else
    .representedStressCurrentSectorWithNonzeroExcess

/-- Exact evidence associated with each possible compiler output. -/
def Certifies (p : Packet) : Verdict → Prop
  | .inheritedCompositeContactDomainObstruction =>
      p.inheritedCompositeReady = false
  | .nuisanceShortOrSourceAtlasDefect =>
      p.inheritedCompositeReady = true ∧
      p.nuisanceShortPhysicalAndAtlasComplete = false
  | .sourceMinimalWardAnomalyWriter =>
      p.inheritedCompositeReady = true ∧
      p.nuisanceShortPhysicalAndAtlasComplete = true ∧
      p.wardRowsPass = false
  | .contactCocycleOrTripleOccurrenceFailure =>
      p.inheritedCompositeReady = true ∧
      p.nuisanceShortPhysicalAndAtlasComplete = true ∧
      p.wardRowsPass = true ∧
      p.contactCocycleAndTripleOccurrencePass = false
  | .conservationSymmetryOrGradedLocalityWitness =>
      p.inheritedCompositeReady = true ∧
      p.nuisanceShortPhysicalAndAtlasComplete = true ∧
      p.wardRowsPass = true ∧
      p.contactCocycleAndTripleOccurrencePass = true ∧
      p.quotientConservationSymmetryLocalityPass = false
  | .energyDensityHamiltonianMismatch =>
      p.inheritedCompositeReady = true ∧
      p.nuisanceShortPhysicalAndAtlasComplete = true ∧
      p.wardRowsPass = true ∧
      p.contactCocycleAndTripleOccurrencePass = true ∧
      p.quotientConservationSymmetryLocalityPass = true ∧
      p.energyDensityMatchesHamiltonian = false
  | .unfixedAbsoluteEnergyPressureFibre =>
      p.inheritedCompositeReady = true ∧
      p.nuisanceShortPhysicalAndAtlasComplete = true ∧
      p.wardRowsPass = true ∧
      p.contactCocycleAndTripleOccurrencePass = true ∧
      p.quotientConservationSymmetryLocalityPass = true ∧
      p.energyDensityMatchesHamiltonian = true ∧
      p.absoluteEnergyPressureFibreFixed = false
  | .newTraceSource =>
      p.inheritedCompositeReady = true ∧
      p.nuisanceShortPhysicalAndAtlasComplete = true ∧
      p.wardRowsPass = true ∧
      p.contactCocycleAndTripleOccurrencePass = true ∧
      p.quotientConservationSymmetryLocalityPass = true ∧
      p.energyDensityMatchesHamiltonian = true ∧
      p.absoluteEnergyPressureFibreFixed = true ∧
      p.traceSourceInDeclaredBasis = false
  | .scaleOccurrenceOrSchemeTransportDefect =>
      p.inheritedCompositeReady = true ∧
      p.nuisanceShortPhysicalAndAtlasComplete = true ∧
      p.wardRowsPass = true ∧
      p.contactCocycleAndTripleOccurrencePass = true ∧
      p.quotientConservationSymmetryLocalityPass = true ∧
      p.energyDensityMatchesHamiltonian = true ∧
      p.absoluteEnergyPressureFibreFixed = true ∧
      p.traceSourceInDeclaredBasis = true ∧
      p.scaleOccurrenceAndSchemeTransportPass = false
  | .gaussianOrQuasiFreeStressResponse =>
      p.inheritedCompositeReady = true ∧
      p.nuisanceShortPhysicalAndAtlasComplete = true ∧
      p.wardRowsPass = true ∧
      p.contactCocycleAndTripleOccurrencePass = true ∧
      p.quotientConservationSymmetryLocalityPass = true ∧
      p.energyDensityMatchesHamiltonian = true ∧
      p.absoluteEnergyPressureFibreFixed = true ∧
      p.traceSourceInDeclaredBasis = true ∧
      p.scaleOccurrenceAndSchemeTransportPass = true ∧
      p.nonzeroStressCompositeExcess = false
  | .movingStressSourceWithoutLocalLimit =>
      p.inheritedCompositeReady = true ∧
      p.nuisanceShortPhysicalAndAtlasComplete = true ∧
      p.wardRowsPass = true ∧
      p.contactCocycleAndTripleOccurrencePass = true ∧
      p.quotientConservationSymmetryLocalityPass = true ∧
      p.energyDensityMatchesHamiltonian = true ∧
      p.absoluteEnergyPressureFibreFixed = true ∧
      p.traceSourceInDeclaredBasis = true ∧
      p.scaleOccurrenceAndSchemeTransportPass = true ∧
      p.nonzeroStressCompositeExcess = true ∧
      p.stressSourceHasLocalLimit = false
  | .representedStressCurrentSectorWithNonzeroExcess =>
      p.inheritedCompositeReady = true ∧
      p.nuisanceShortPhysicalAndAtlasComplete = true ∧
      p.wardRowsPass = true ∧
      p.contactCocycleAndTripleOccurrencePass = true ∧
      p.quotientConservationSymmetryLocalityPass = true ∧
      p.energyDensityMatchesHamiltonian = true ∧
      p.absoluteEnergyPressureFibreFixed = true ∧
      p.traceSourceInDeclaredBasis = true ∧
      p.scaleOccurrenceAndSchemeTransportPass = true ∧
      p.nonzeroStressCompositeExcess = true ∧
      p.stressSourceHasLocalLimit = true

/-- The compiler returns a verdict exactly when the corresponding complete
first-failure certificate holds. -/
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
                  · split
                    · cases v <;> simp_all [Certifies]
                    · split
                      · cases v <;> simp_all [Certifies]
                      · cases v <;> simp_all [Certifies]

/-- Every finite packet has a certified compiler output. -/
theorem compile_certified (p : Packet) : Certifies p (compile p) :=
  (compile_eq_iff_certifies p (compile p)).mp rfl

/-- A certificate recovers the compiler verdict. -/
theorem compile_eq_of_certifies {p : Packet} {v : Verdict}
    (h : Certifies p v) : compile p = v :=
  (compile_eq_iff_certifies p v).mpr h

/-- The twelve branches are mutually exclusive. -/
theorem certified_verdict_unique {p : Packet} {v w : Verdict}
    (hv : Certifies p v) (hw : Certifies p w) : v = w := by
  rw [← compile_eq_of_certifies hv, ← compile_eq_of_certifies hw]

/-- **Terminating stress/Ward compiler.**  On every finite cutoff packet there
is a unique one of the twelve manuscript verdicts, and it carries the exact
ordered first-failure certificate. -/
theorem terminating_stress_Ward_compiler (p : Packet) :
    ∃! v : Verdict, Certifies p v := by
  refine ⟨compile p, compile_certified p, ?_⟩
  intro v hv
  exact certified_verdict_unique hv (compile_certified p)

end StressWardCompiler
end NCG
