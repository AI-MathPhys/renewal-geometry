/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PreCStarDirectLimit

/-!
# Compatible contractions on pre-C-star direct limits

This file supplies the linear-map layer needed for quasilocal dynamics. A compatible family
of contractive complex-linear maps on the stages of an isometric directed system descends to
the algebraic direct limit and extends uniquely to its C-star completion. The construction
preserves identities and composition, so pointwise local semigroup laws pass to the completed
quasilocal algebra.
-/

noncomputable section

namespace NCG.PreCStarDirectLimit

open UniformSpace UniformSpace.Completion

universe u v

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A : ι → Type v}
variable [∀ i, NormedRing (A i)] [∀ i, StarRing (A i)] [∀ i, CStarRing (A i)]
variable [∀ i, NormedAlgebra ℂ (A i)] [∀ i, StarModule ℂ (A i)]
variable (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
variable [DirectedSystem A (fun i j hij ↦ f i j hij)] [IsometricSystem f]

/-- A compatible family of contractive complex-linear endomorphisms of the stages. -/
structure CompatibleLinearContraction where
  /-- The local map at each stage. -/
  map : ∀ i, A i →L[ℂ] A i
  /-- Every local map is contractive. -/
  norm_apply_le : ∀ i (x : A i), ‖map i x‖ ≤ ‖x‖
  /-- Local maps commute with all connecting maps. -/
  compatible : ∀ i j (hij : i ≤ j) (x : A i),
    map j (f i j hij x) = f i j hij (map i x)

namespace CompatibleLinearContraction

variable (T : CompatibleLinearContraction f)
variable {f}

/-- The linear endomorphism induced on the algebraic direct limit. -/
def linearMap : AlgebraicLimit f →ₗ[ℂ] AlgebraicLimit f :=
  DirectLimit.Module.lift ℂ ι A (fun i j hij ↦ f i j hij)
    (fun i ↦ (of f i).toLinearMap.comp (T.map i).toLinearMap) fun i j hij x ↦ by
      change of f j (T.map j (f i j hij x)) = of f i (T.map i x)
      rw [T.compatible]
      exact DirectLimit.Algebra.of_f hij (T.map i x)

omit [∀ i, CStarRing (A i)] [∀ i, StarModule ℂ (A i)] [IsometricSystem f] in
@[simp]
theorem linearMap_of (i : ι) (x : A i) :
    T.linearMap (of f i x) = of f i (T.map i x) :=
  rfl

omit [∀ i, CStarRing (A i)] [∀ i, StarModule ℂ (A i)] in
/-- The induced algebraic-limit map is contractive. -/
theorem norm_linearMap_apply_le (x : AlgebraicLimit f) :
    ‖T.linearMap x‖ ≤ ‖x‖ := by
  induction x using DirectLimit.induction with
  | _ i x =>
      simpa only [← of_apply, linearMap_of, norm_of] using T.norm_apply_le i x

/-- The compatible family as a continuous linear contraction on the algebraic limit. -/
def continuousLinearMap : AlgebraicLimit f →L[ℂ] AlgebraicLimit f :=
  T.linearMap.mkContinuous 1 fun x ↦ by simpa using T.norm_linearMap_apply_le x

omit [∀ i, CStarRing (A i)] [∀ i, StarModule ℂ (A i)] in
@[simp]
theorem continuousLinearMap_apply (x : AlgebraicLimit f) :
    T.continuousLinearMap x = T.linearMap x :=
  rfl

omit [∀ i, CStarRing (A i)] [∀ i, StarModule ℂ (A i)] in
@[simp]
theorem continuousLinearMap_of (i : ι) (x : A i) :
    T.continuousLinearMap (of f i x) = of f i (T.map i x) :=
  rfl

/-- The unique continuous extension of a compatible local contraction to the completed
direct limit. -/
def completionMap : Completion f →L[ℂ] Completion f :=
  ((Completion.toComplL : AlgebraicLimit f →L[ℂ] Completion f).comp T.continuousLinearMap).extend
    (Completion.toComplL : AlgebraicLimit f →L[ℂ] Completion f)

omit [∀ i, CStarRing (A i)] [∀ i, StarModule ℂ (A i)] in
@[simp]
theorem completionMap_coe (x : AlgebraicLimit f) :
    T.completionMap (x : Completion f) = (T.continuousLinearMap x : Completion f) := by
  exact ContinuousLinearMap.extend_eq _ Completion.denseRange_coe
    Completion.coe_isometry.isUniformInducing x

omit [∀ i, StarModule ℂ (A i)] in
@[simp]
theorem completionMap_completionOf (i : ι) (x : A i) :
    T.completionMap (completionOf f i x) = completionOf f i (T.map i x) := by
  rw [completionOf_apply, completionMap_coe, continuousLinearMap_of, completionOf_apply]

/-- Contractivity survives passage to the C-star completion. -/
theorem norm_completionMap_apply_le (x : Completion f) :
    ‖T.completionMap x‖ ≤ ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le T.completionMap.continuous.norm continuous_norm
  | ih x =>
      simpa only [completionMap_coe, continuousLinearMap_apply, Completion.norm_coe] using
        T.norm_linearMap_apply_le x

omit [∀ i, StarModule ℂ (A i)] in
/-- The completed map is characterized uniquely by its values on the local stages. -/
theorem completionMap_unique (g : Completion f →L[ℂ] Completion f)
    (hg : ∀ i (x : A i), g (completionOf f i x) = completionOf f i (T.map i x)) :
    g = T.completionMap := by
  apply ContinuousLinearMap.coeFn_injective
  apply Completion.ext g.continuous T.completionMap.continuous
  intro x
  obtain ⟨i, a, rfl⟩ := DirectLimit.exists_eq_mk (fun i j hij ↦ f i j hij) x
  exact hg i a |>.trans (T.completionMap_completionOf i a).symm

/-- Composition of compatible local contractions. -/
def comp (S T : CompatibleLinearContraction f) : CompatibleLinearContraction f where
  map i := (S.map i).comp (T.map i)
  norm_apply_le i x := (S.norm_apply_le i (T.map i x)).trans (T.norm_apply_le i x)
  compatible i j hij x := by
    rw [ContinuousLinearMap.comp_apply, T.compatible, S.compatible]
    rfl

omit [IsDirectedOrder ι] [Nonempty ι] [∀ i, CStarRing (A i)]
  [∀ i, StarModule ℂ (A i)] [DirectedSystem A (fun i j hij ↦ f i j hij)]
  [IsometricSystem f] in
@[simp]
theorem comp_map_apply (S T : CompatibleLinearContraction f) (i : ι) (x : A i) :
    (S.comp T).map i x = S.map i (T.map i x) :=
  rfl

omit [∀ i, StarModule ℂ (A i)] in
/-- Completion preserves composition exactly. -/
theorem completionMap_comp (S T : CompatibleLinearContraction f) :
    (S.comp T).completionMap = S.completionMap.comp T.completionMap := by
  symm
  apply (S.comp T).completionMap_unique
  intro i x
  rw [ContinuousLinearMap.comp_apply, T.completionMap_completionOf,
    S.completionMap_completionOf]
  rfl

/-- The identity compatible local contraction. -/
def id : CompatibleLinearContraction f where
  map _ := ContinuousLinearMap.id ℂ _
  norm_apply_le _ _ := le_rfl
  compatible _ _ _ _ := rfl

omit [IsDirectedOrder ι] [Nonempty ι] [∀ i, CStarRing (A i)]
  [∀ i, StarModule ℂ (A i)] [DirectedSystem A (fun i j hij ↦ f i j hij)]
  [IsometricSystem f] in
@[simp]
theorem id_map_apply (i : ι) (x : A i) :
    (id (f := f)).map i x = x :=
  rfl

omit [∀ i, StarModule ℂ (A i)] in
/-- Completion preserves the identity map. -/
@[simp]
theorem completionMap_id :
    (id (f := f)).completionMap = ContinuousLinearMap.id ℂ (Completion f) := by
  symm
  apply (id (f := f)).completionMap_unique
  intro i x
  rfl

omit [∀ i, StarModule ℂ (A i)] in
/-- Any pointwise local semigroup law passes unchanged to the completed direct limit. -/
theorem completionMap_operation {τ : Type*} (op : τ → τ → τ)
    (U : τ → CompatibleLinearContraction f)
    (hU : ∀ s t i (x : A i),
      (U (op s t)).map i x = (U s).map i ((U t).map i x))
    (s t : τ) :
    (U (op s t)).completionMap = (U s).completionMap.comp (U t).completionMap := by
  symm
  apply (U (op s t)).completionMap_unique
  intro i x
  rw [ContinuousLinearMap.comp_apply, (U t).completionMap_completionOf,
    (U s).completionMap_completionOf, hU]

omit [∀ i, StarModule ℂ (A i)] in
/-- A local unitality law passes to the completed direct limit. -/
theorem completionMap_one (hT : ∀ i, T.map i 1 = 1) :
    T.completionMap 1 = 1 := by
  let i := Classical.arbitrary ι
  rw [← map_one (completionOf f i), T.completionMap_completionOf, hT]

end CompatibleLinearContraction

end NCG.PreCStarDirectLimit
