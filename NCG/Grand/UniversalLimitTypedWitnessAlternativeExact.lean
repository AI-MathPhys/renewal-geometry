/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.UniversalLimitAlternativeExact
import NCG.Grand.GlobalCylinderDescentCStarCompletionExact

/-!
# Typed universal limit and obstruction alternative

Unlike the earlier propositional skeleton, every negative branch below carries
an actual witness, and the nonunique-state branch derives a finite cylinder
tester separating the two global states.  The common subnet is the genuine
diagonal compactness result for countably many compact metrizable coordinates.
-/

open Filter Topology

noncomputable section

namespace NCG.UniversalLimit

universe u v w

variable {G : ℕ → Type u} [∀ m, AddCommGroup (G m)]
variable [∀ m, Module ℂ (G m)]
variable (g : ∀ m k : ℕ, m ≤ k → G m →ₗ[ℂ] G k)
variable {K : Type v} [AddCommGroup K] [Module ℂ K]

/-- The three positive analytic outcomes after all obstruction coordinates
vanish.  The nonunique case records two genuinely distinct global states; the
trivial case records an actual one-dimensional cyclic carrier. -/
inductive ControlledStateOutcome where
  | canonical (state : Module.DirectLimit G g →ₗ[ℂ] ℂ)
  | nonunique (state₁ state₂ : Module.DirectLimit G g →ₗ[ℂ] ℂ)
      (distinct : state₁ ≠ state₂)
  | trivial (state : Module.DirectLimit G g →ₗ[ℂ] ℂ)
      (cyclicVector : K) (all_scalar : ∀ x : K, ∃ c : ℂ, x = c • cyclicVector)

/-- Complete typed audit profile.  `none` means the coordinate passed; `some w`
is the finite or sequential witness retained when it failed. -/
structure TypedAuditProfile
    (CutoffWitness SourceWitness MetricWitness DomainWitness FieldWitness
      LocalityWitness MemoryWitness CoercivityWitness : Type w) where
  declared : Bool
  stateOutcome : ControlledStateOutcome g (K := K)
  cutoff : Option CutoffWitness
  source : Option SourceWitness
  metric : Option MetricWitness
  domain : Option DomainWitness
  field : Option FieldWitness
  locality : Option LocalityWitness
  memory : Option MemoryWitness
  coercivity : Option CoercivityWitness

/-- Typed realization of branches (U1)--(U12).  In (U2), `stage`, `tester`,
and `separates` are the promised finite observable. -/
inductive TypedUniversalBranch
    (CutoffWitness SourceWitness MetricWitness DomainWitness FieldWitness
      LocalityWitness MemoryWitness CoercivityWitness : Type w)
    (P : TypedAuditProfile g (K := K) CutoffWitness SourceWitness MetricWitness
      DomainWitness FieldWitness LocalityWitness MemoryWitness
      CoercivityWitness) : Type (max u v w) where
  | canonical (state : Module.DirectLimit G g →ₗ[ℂ] ℂ)
      (hstate : P.stateOutcome = ControlledStateOutcome.canonical state)
      (hcutoff : P.cutoff = none) (hsource : P.source = none)
      (hmetric : P.metric = none) (hdomain : P.domain = none)
      (hfield : P.field = none) (hlocality : P.locality = none)
      (hmemory : P.memory = none) (hcoercivity : P.coercivity = none)
  | nonunique (state₁ state₂ : Module.DirectLimit G g →ₗ[ℂ] ℂ)
      (distinct : state₁ ≠ state₂) (stage : ℕ) (tester : G stage)
      (separates : state₁ (Module.DirectLimit.of ℂ ℕ G g stage tester) ≠
        state₂ (Module.DirectLimit.of ℂ ℕ G g stage tester))
      (hstate : P.stateOutcome =
        ControlledStateOutcome.nonunique state₁ state₂ distinct)
      (hcutoff : P.cutoff = none) (hsource : P.source = none)
      (hmetric : P.metric = none) (hdomain : P.domain = none)
      (hfield : P.field = none) (hlocality : P.locality = none)
      (hmemory : P.memory = none) (hcoercivity : P.coercivity = none)
  | trivial (state : Module.DirectLimit G g →ₗ[ℂ] ℂ)
      (cyclicVector : K) (all_scalar : ∀ x : K, ∃ c : ℂ, x = c • cyclicVector)
      (hstate : P.stateOutcome =
        ControlledStateOutcome.trivial state cyclicVector all_scalar)
      (hcutoff : P.cutoff = none) (hsource : P.source = none)
      (hmetric : P.metric = none) (hdomain : P.domain = none)
      (hfield : P.field = none) (hlocality : P.locality = none)
      (hmemory : P.memory = none) (hcoercivity : P.coercivity = none)
  | cutoffIncompatible (witness : CutoffWitness) (hw : P.cutoff = some witness)
  | sourceIncomplete (witness : SourceWitness) (hw : P.source = some witness)
      (hcutoff : P.cutoff = none)
  | metricDegenerate (witness : MetricWitness) (hw : P.metric = some witness)
      (hcutoff : P.cutoff = none) (hsource : P.source = none)
  | domainUnstable (witness : DomainWitness) (hw : P.domain = some witness)
      (hcutoff : P.cutoff = none) (hsource : P.source = none)
      (hmetric : P.metric = none)
  | fieldNontight (witness : FieldWitness) (hw : P.field = some witness)
      (hcutoff : P.cutoff = none) (hsource : P.source = none)
      (hmetric : P.metric = none) (hdomain : P.domain = none)
  | nonlocal (witness : LocalityWitness) (hw : P.locality = some witness)
      (hcutoff : P.cutoff = none) (hsource : P.source = none)
      (hmetric : P.metric = none) (hdomain : P.domain = none)
      (hfield : P.field = none)
  | longMemory (witness : MemoryWitness) (hw : P.memory = some witness)
      (hcutoff : P.cutoff = none) (hsource : P.source = none)
      (hmetric : P.metric = none) (hdomain : P.domain = none)
      (hfield : P.field = none) (hlocality : P.locality = none)
  | noncoercive (witness : CoercivityWitness) (hw : P.coercivity = some witness)
      (hcutoff : P.cutoff = none) (hsource : P.source = none)
      (hmetric : P.metric = none) (hdomain : P.domain = none)
      (hfield : P.field = none) (hlocality : P.locality = none)
      (hmemory : P.memory = none)
  | undeclared (hdeclared : P.declared = false)

/-- Every complete typed profile lands in a positive branch or retains the
first concrete obstruction witness. -/
theorem classify_typed_profile
    {CutoffWitness SourceWitness MetricWitness DomainWitness FieldWitness
      LocalityWitness MemoryWitness CoercivityWitness : Type w}
    (P : TypedAuditProfile g (K := K) CutoffWitness SourceWitness MetricWitness
      DomainWitness FieldWitness LocalityWitness MemoryWitness
      CoercivityWitness) :
    Nonempty (TypedUniversalBranch (g := g) (P := P)) := by
  classical
  by_cases hdecl : P.declared = false
  · exact ⟨.undeclared hdecl⟩
  rcases hcut : P.cutoff with _ | w
  · rcases hsrc : P.source with _ | w
    · rcases hmet : P.metric with _ | w
      · rcases hdom : P.domain with _ | w
        · rcases hfield : P.field with _ | w
          · rcases hloc : P.locality with _ | w
            · rcases hmem : P.memory with _ | w
              · rcases hcoer : P.coercivity with _ | w
                · cases hstate : P.stateOutcome with
                  | canonical state =>
                      exact ⟨.canonical state hstate hcut hsrc hmet hdom hfield
                        hloc hmem hcoer⟩
                  | nonunique state₁ state₂ distinct =>
                      obtain ⟨stage, tester, separates⟩ :=
                        NCG.GlobalCylinderDescent.distinctGlobalStates_have_finite_tester
                          g distinct
                      exact ⟨.nonunique state₁ state₂ distinct stage tester separates
                        hstate hcut hsrc hmet hdom hfield hloc hmem hcoer⟩
                  | trivial state cyclicVector all_scalar =>
                      exact ⟨.trivial state cyclicVector all_scalar hstate hcut hsrc
                        hmet hdom hfield hloc hmem hcoer⟩
                · exact ⟨.noncoercive w hcoer hcut hsrc hmet hdom hfield hloc hmem⟩
              · exact ⟨.longMemory w hmem hcut hsrc hmet hdom hfield hloc⟩
            · exact ⟨.nonlocal w hloc hcut hsrc hmet hdom hfield⟩
          · exact ⟨.fieldNontight w hfield hcut hsrc hmet hdom⟩
        · exact ⟨.domainUnstable w hdom hcut hsrc hmet⟩
      · exact ⟨.metricDegenerate w hmet hcut hsrc⟩
    · exact ⟨.sourceIncomplete w hsrc hcut⟩
  · exact ⟨.cutoffIncompatible w hcut⟩

/-- **Universal Grand-Tensor limit and obstruction alternative, typed form.**
A countable compact profile has one common cofinal subsequence; its limiting
profile is then classified with a concrete witness in every failure branch. -/
theorem typed_universal_limit_alternative
    {X : ℕ → Type*} [∀ m, TopologicalSpace (X m)]
    [∀ m, CompactSpace (X m)]
    [∀ m, TopologicalSpace.PseudoMetrizableSpace (X m)]
    {CutoffWitness SourceWitness MetricWitness DomainWitness FieldWitness
      LocalityWitness MemoryWitness CoercivityWitness : Type w}
    (x : ℕ → ∀ m, X m)
    (profile : (∀ m, X m) →
      TypedAuditProfile g (K := K) CutoffWitness SourceWitness MetricWitness
        DomainWitness FieldWitness LocalityWitness MemoryWitness
        CoercivityWitness) :
    ∃ (φ : ℕ → ℕ) (lim : ∀ m, X m), StrictMono φ ∧
      (∀ m, Tendsto (fun r => x (φ r) m) atTop (𝓝 (lim m))) ∧
      Nonempty (TypedUniversalBranch (g := g) (P := profile lim)) := by
  obtain ⟨φ, lim, hφ, hlim⟩ := exists_common_profile_subsequence x
  exact ⟨φ, lim, hφ, hlim, classify_typed_profile g (profile lim)⟩

end NCG.UniversalLimit
