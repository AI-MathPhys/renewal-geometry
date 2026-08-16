/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCStarQuotientInductiveSystem

/-!
# Contextually strict AF inductive systems

This file assembles the finite-cutoff input used in `thm:AF-limit-state` of the Gran-Tensor
manuscript.  The raw finite-dimensional C-star algebras form an isometric directed system and
surject onto their separated-history quotients.  Vanishing of each contextual innovation Gram
is recorded by its exact finite-coordinate consequence: the kernel of the earlier quotient is
the pullback of the later quotient kernel.

That kernel equality both permits the raw cutoff map to descend and makes the descended map
injective.  Injective C-star homomorphisms are isometric, so the separated algebras form an AF
system.  Its completed algebraic direct limit has the C-star universal property, has dense
finite-stage image, and every compatible family of states extends uniquely with a contractive
GNS representation.
-/

open scoped CStarAlgebra ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false
namespace NCG

universe u v

variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
variable (Raw Sep : I → Type v)
variable [∀ i, CStarAlgebra (Raw i)] [∀ i, CStarAlgebra (Sep i)]
variable [∀ i, FiniteDimensional ℂ (Raw i)] [∀ i, FiniteDimensional ℂ (Sep i)]

/-- Finite-cutoff data for a contextually strict AF presentation.

The proposition `innovationGramVanishes i j hij` is the model-specific assertion that the
contextual innovation Gram for the cutoff `i ≤ j` is zero.  The last field is precisely the
finite-coordinate cutoff theorem identifying that vanishing with equality of contextual-null
kernels. -/
structure ContextuallyStrictAFFamily where
  /-- Raw cutoff inclusions. -/
  rawMap : ∀ i j, i ≤ j → Raw i →⋆ₐ[ℂ] Raw j
  /-- Raw cutoff maps are identities at equal indices. -/
  raw_map_self : ∀ i (x : Raw i), rawMap i i le_rfl x = x
  /-- Raw cutoff maps compose. -/
  raw_map_map : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) (x : Raw i),
    rawMap j k hjk (rawMap i j hij x) = rawMap i k (hij.trans hjk) x
  /-- The raw prefix-exact system is isometric. -/
  raw_norm_map : ∀ i j (hij : i ≤ j) (x : Raw i), ‖rawMap i j hij x‖ = ‖x‖
  /-- Quotient onto the separated-history algebra at a cutoff. -/
  quotient : ∀ i, Raw i →⋆ₐ[ℂ] Sep i
  /-- Each separated-history quotient map is onto. -/
  quotient_surjective : ∀ i, Function.Surjective (quotient i)
  /-- Vanishing of the contextual innovation Gram for a cutoff pair. -/
  innovationGramVanishes : ∀ (i j : I), i ≤ j → Prop
  /-- Contextual strictness: every innovation Gram in the cofinal family vanishes. -/
  all_innovationGrams_vanish : ∀ i j (hij : i ≤ j), innovationGramVanishes i j hij
  /-- The finite-coordinate cutoff criterion: innovation vanishing is exact kernel pullback. -/
  innovationGramVanishes_iff_exactKernel : ∀ i j (hij : i ≤ j),
    innovationGramVanishes i j hij ↔
      RingHom.ker (quotient i).toRingHom =
        Ideal.comap (rawMap i j hij).toRingHom
          (RingHom.ker (quotient j).toRingHom)

namespace ContextuallyStrictAFFamily

variable {Raw Sep}
variable (S : ContextuallyStrictAFFamily Raw Sep)

/-- Vanishing contextual innovation gives exact pullback of separated-history kernels. -/
theorem exactKernel (i j : I) (hij : i ≤ j) :
    RingHom.ker (S.quotient i).toRingHom =
      Ideal.comap (S.rawMap i j hij).toRingHom
        (RingHom.ker (S.quotient j).toRingHom) :=
  (S.innovationGramVanishes_iff_exactKernel i j hij).mp
    (S.all_innovationGrams_vanish i j hij)

/-- The raw cutoff map descended to separated-history quotients. -/
def separatedMap (i j : I) (hij : i ≤ j) : Sep i →⋆ₐ[ℂ] Sep j :=
  StarAlgHom.descendSurjective (S.quotient i) (S.quotient_surjective i)
    (S.quotient j) (S.rawMap i j hij) (S.exactKernel i j hij).le

@[simp]
theorem separatedMap_quotient (i j : I) (hij : i ≤ j) (x : Raw i) :
    S.separatedMap i j hij (S.quotient i x) =
      S.quotient j (S.rawMap i j hij x) :=
  StarAlgHom.descendSurjective.apply_quotient _ _ _ _ _ x

/-- Exact kernel pullback makes every separated cutoff map injective. -/
theorem separatedMap_injective (i j : I) (hij : i ≤ j) :
    Function.Injective (S.separatedMap i j hij) :=
  StarAlgHom.descendSurjective.injective _ _ _ _ _ (S.exactKernel i j hij).ge

/-- Hence every separated cutoff map is isometric. -/
theorem separatedMap_isometry (i j : I) (hij : i ≤ j) :
    Isometry (S.separatedMap i j hij) :=
  NonUnitalStarAlgHom.isometry _ (S.separatedMap_injective i j hij)

instance rawDirectedSystem :
    DirectedSystem Raw (fun i j hij ↦ S.rawMap i j hij) where
  map_self i x := S.raw_map_self i x
  map_map k j i hij hjk x := S.raw_map_map i j k hij hjk x

instance rawIsometricSystem :
    PreCStarDirectLimit.IsometricSystem S.rawMap where
  norm_map := S.raw_norm_map

instance separatedDirectedSystem :
    DirectedSystem Sep (fun i j hij ↦ S.separatedMap i j hij) where
  map_self i x := by
    obtain ⟨a, rfl⟩ := S.quotient_surjective i x
    rw [S.separatedMap_quotient, S.raw_map_self]
  map_map k j i hij hjk x := by
    obtain ⟨a, rfl⟩ := S.quotient_surjective i x
    rw [S.separatedMap_quotient, S.separatedMap_quotient,
      S.separatedMap_quotient, S.raw_map_map]

instance separatedIsometricSystem :
    PreCStarDirectLimit.IsometricSystem S.separatedMap where
  norm_map i j hij x :=
    (S.separatedMap_isometry i j hij).norm_map_of_map_zero (map_zero _) x

/-- The completed raw algebraic direct limit. -/
abbrev RawLimit := PreCStarDirectLimit.Completion S.rawMap

/-- The completed separated-history algebraic direct limit. -/
abbrev SeparatedLimit := PreCStarDirectLimit.Completion S.separatedMap

/-- The raw completion is the canonical C-star inductive limit. -/
def rawLimit_isCStarInductiveLimit :
    PreCStarDirectLimit.IsCStarInductiveLimit S.rawMap
      (PreCStarDirectLimit.completionCone S.rawMap) :=
  PreCStarDirectLimit.completionCone_isCStarInductiveLimit S.rawMap

/-- The separated-history completion is the canonical C-star inductive limit. -/
def separatedLimit_isCStarInductiveLimit :
    PreCStarDirectLimit.IsCStarInductiveLimit S.separatedMap
      (PreCStarDirectLimit.completionCone S.separatedMap) :=
  PreCStarDirectLimit.completionCone_isCStarInductiveLimit S.separatedMap

/-- Every separated finite stage embeds isometrically in the AF limit. -/
theorem separatedLimit_stage_isometry (i : I) :
    Isometry (PreCStarDirectLimit.completionOf S.separatedMap i) :=
  PreCStarDirectLimit.completionOf_isometry S.separatedMap i

/-- The union of the separated finite-stage images is dense in the AF limit. -/
theorem separatedLimit_denseRange :
    DenseRange (PreCStarDirectLimit.stageMap S.separatedMap) :=
  PreCStarDirectLimit.denseRange_stageMap S.separatedMap

/-- The complete conclusion of `thm:AF-limit-state` for a compatible separated-stage state. -/
structure AFLimitStateConclusion
    (omega : PreCStarDirectLimit.CompatibleState S.separatedMap) where
  /-- The completion has the C-star inductive-limit universal property. -/
  isInductiveLimit :
    PreCStarDirectLimit.IsCStarInductiveLimit S.separatedMap
      (PreCStarDirectLimit.completionCone S.separatedMap)
  /-- Every finite-stage map into the limit is isometric. -/
  stageIsometry : ∀ i, Isometry (PreCStarDirectLimit.completionOf S.separatedMap i)
  /-- Finite-stage observables have dense union in the limit. -/
  denseStageRange : DenseRange (PreCStarDirectLimit.stageMap S.separatedMap)
  /-- The induced state is the unique state with the prescribed finite restrictions. -/
  stateUnique : ∀ (phi : S.SeparatedLimit →ₚ[ℂ] ℂ),
    (∀ i (x : Sep i),
      phi (PreCStarDirectLimit.completionOf S.separatedMap i x) = omega.state i x) →
      phi = omega.completionPositiveLinearMap
  /-- The resulting GNS representation is bounded by the C-star norm. -/
  gnsNormBound : ∀ a : S.SeparatedLimit,
    ‖omega.completionGNSRepresentation a‖ ≤ ‖a‖

/-- Vanishing of all contextual innovation Grams produces the separated AF limit, its unique
compatible limit state, and the bounded GNS representation. -/
def afLimitState (omega : PreCStarDirectLimit.CompatibleState S.separatedMap) :
    S.AFLimitStateConclusion omega where
  isInductiveLimit := S.separatedLimit_isCStarInductiveLimit
  stageIsometry := S.separatedLimit_stage_isometry
  denseStageRange := S.separatedLimit_denseRange
  stateUnique phi hphi := omega.completionPositiveLinearMap_unique phi hphi
  gnsNormBound a := omega.norm_completionGNSRepresentation_apply_le a

end ContextuallyStrictAFFamily

end NCG
