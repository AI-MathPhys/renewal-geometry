/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PreCStarDirectLimit

/-!
# Compatible states on normed pre-C-star direct limits

A compatible family of bounded states on the stages of an isometric pre-C-star directed system
descends to a bounded state on its algebraic direct limit.  Combining this file with
`NCG.Grand.CStarAlgebraCompletion` then extends that state to the completed C-star algebra and
makes Mathlib's GNS construction available.
-/


open scoped ComplexOrder
noncomputable section

namespace NCG.PreCStarDirectLimit

universe u v

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A : ι → Type v}
variable [∀ i, NormedRing (A i)] [∀ i, StarRing (A i)] [∀ i, CStarRing (A i)]
variable [∀ i, NormedAlgebra ℂ (A i)] [∀ i, StarModule ℂ (A i)]
variable (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
variable [DirectedSystem A (fun i j hij ↦ f i j hij)] [IsometricSystem f]

/-- A family of pre-C-star states compatible with every connecting map. -/
structure CompatibleState where
  /-- The state at each stage. -/
  state : ∀ i, NCG.PreCStarState (A i)
  /-- Compatibility with the directed system. -/
  compatible : ∀ i j (hij : i ≤ j) (x : A i), state j (f i j hij x) = state i x

namespace CompatibleState

variable (ω : CompatibleState f)
variable {f}

/-- The algebraic linear functional induced on the direct limit. -/
def linearMap : AlgebraicLimit f →ₗ[ℂ] ℂ :=
  DirectLimit.Module.lift ℂ ι A (fun i j hij ↦ f i j hij)
    (fun i ↦ (ω.state i).toContinuousLinearMap.toLinearMap) ω.compatible

omit [IsometricSystem f] in
@[simp]
theorem linearMap_of (i : ι) (x : A i) :
    ω.linearMap (of f i x) = ω.state i x :=
  rfl

/-- The induced functional is contractive. -/
theorem norm_linearMap_le (x : AlgebraicLimit f) :
    ‖ω.linearMap x‖ ≤ ‖x‖ := by
  induction x using DirectLimit.induction with
  | _ i x =>
      rw [norm_mk]
      change ‖ω.state i x‖ ≤ ‖x‖
      calc
        ‖ω.state i x‖ ≤ ‖(ω.state i).toContinuousLinearMap‖ * ‖x‖ :=
          (ω.state i).toContinuousLinearMap.le_opNorm x
        _ = ‖x‖ := by rw [(ω.state i).norm_eq_one, one_mul]

/-- The compatible family as a continuous linear functional on the algebraic direct limit. -/
def continuousLinearMap : AlgebraicLimit f →L[ℂ] ℂ :=
  ω.linearMap.mkContinuous 1 fun x ↦ by simpa using ω.norm_linearMap_le x

@[simp]
theorem continuousLinearMap_of (i : ι) (x : A i) :
    ω.continuousLinearMap (of f i x) = ω.state i x :=
  rfl

@[simp]
theorem continuousLinearMap_one : ω.continuousLinearMap 1 = 1 := by
  let i := Classical.arbitrary ι
  rw [DirectLimit.one_def i]
  exact (ω.state i).map_one

theorem continuousLinearMap_star_mul_self_nonneg (x : AlgebraicLimit f) :
    0 ≤ ω.continuousLinearMap (star x * x) := by
  induction x using DirectLimit.induction with
  | _ i x =>
      rw [DirectLimit.star_def, DirectLimit.mul_def]
      change 0 ≤ ω.state i (star x * x)
      exact (ω.state i).map_star_mul_self_nonneg x

theorem norm_continuousLinearMap_le_one : ‖ω.continuousLinearMap‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one fun x ↦ by
    simpa using ω.norm_linearMap_le x

private theorem norm_one_limit (ω : CompatibleState f) : ‖(1 : AlgebraicLimit f)‖ = 1 := by
  let i := Classical.arbitrary ι
  letI : Nontrivial (A i) :=
    ⟨⟨0, 1, fun h ↦ by
      have h' : (0 : ℂ) = 1 := by
        calc
          0 = ω.state i 0 := by simp
          _ = ω.state i 1 := congrArg (ω.state i) h
          _ = 1 := (ω.state i).map_one
      exact zero_ne_one h'⟩⟩
  rw [DirectLimit.one_def i, norm_mk, CStarRing.norm_one]

@[simp]
theorem norm_continuousLinearMap : ‖ω.continuousLinearMap‖ = 1 := by
  apply le_antisymm ω.norm_continuousLinearMap_le_one
  calc
    1 = ‖ω.continuousLinearMap 1‖ := by rw [continuousLinearMap_one, norm_one]
    _ ≤ ‖ω.continuousLinearMap‖ * ‖(1 : AlgebraicLimit f)‖ :=
      ω.continuousLinearMap.le_opNorm 1
    _ = ‖ω.continuousLinearMap‖ := by rw [norm_one_limit ω, mul_one]

/-- A compatible family of finite-stage states descends to a pre-C-star state on the
algebraic direct limit. -/
def toPreCStarState : NCG.PreCStarState (AlgebraicLimit f) where
  toContinuousLinearMap := ω.continuousLinearMap
  map_one := ω.continuousLinearMap_one
  map_star_mul_self_nonneg := ω.continuousLinearMap_star_mul_self_nonneg
  norm_eq_one := ω.norm_continuousLinearMap

@[simp]
theorem toPreCStarState_of (i : ι) (x : A i) :
    ω.toPreCStarState (of f i x) = ω.state i x :=
  rfl

/-- The completed positive linear map associated to a compatible family of stage states. -/
def completionPositiveLinearMap : Completion f →ₚ[ℂ] ℂ :=
  ω.toPreCStarState.completionPositiveLinearMap

/-- The GNS construction for the completed direct limit and the descended state. -/
abbrev CompletionGNS := ω.toPreCStarState.CompletionGNS

/-- The GNS representation of the completed direct limit. -/
def completionGNSRepresentation :
    Completion f →⋆ₐ[ℂ] (ω.CompletionGNS →L[ℂ] ω.CompletionGNS) :=
  ω.toPreCStarState.completionGNSRepresentation

end CompatibleState

end NCG.PreCStarDirectLimit
