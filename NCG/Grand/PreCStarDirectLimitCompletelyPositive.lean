/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PreCStarDirectLimitContraction
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!
# Complete positivity from a dense pre-C-star direct-limit core

This file isolates the matrix-density argument used by quasilocal UCP maps. A bounded linear
map on a completed pre-C-star direct limit is completely positive as soon as every matrix
amplification sends star squares whose entries lie in the algebraic direct-limit core to
positive elements. Density upgrades that hypothesis to arbitrary completed matrix star squares;
the spectral order then upgrades star-square positivity to positivity on the full cone.
-/

open scoped CStarAlgebra

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

namespace CompatibleLinearContraction

variable (T : CompatibleLinearContraction f)
variable {f}

/-- A matrix over the completion obtained entrywise from the algebraic direct-limit core. -/
def coreMatrix (k : ℕ) (X : Fin k → Fin k → AlgebraicLimit f) :
    CStarMatrix (Fin k) (Fin k) (Completion f) :=
  fun i j ↦ (X i j : Completion f)

/-- Algebraic-core matrices are dense among matrices over the completion. -/
private theorem denseRange_coreMatrix (k : ℕ) :
    DenseRange (coreMatrix (f := f) k) := by
  have hrow : DenseRange (fun x : Fin k → AlgebraicLimit f ↦
      fun j ↦ (x j : Completion f)) :=
    DenseRange.piMap fun _ ↦ Completion.denseRange_coe
  exact DenseRange.piMap fun _ ↦ hrow

/-- Matrix star-square positivity extends from algebraic-core entries to arbitrary entries of
the C-star completion. -/
private theorem completionMap_matrix_star_mul_self_nonneg
    (hcore : ∀ k (X : Fin k → Fin k → AlgebraicLimit f),
      0 ≤ (star (coreMatrix (f := f) k X) * coreMatrix (f := f) k X).map T.completionMap)
    (k : ℕ) (X : CStarMatrix (Fin k) (Fin k) (Completion f)) :
    0 ≤ (star X * X).map T.completionMap := by
  refine DenseRange.induction_on (denseRange_coreMatrix (f := f) k) X ?_ ?_
  · apply isClosed_le continuous_const
    have hmap : Continuous (fun M : CStarMatrix (Fin k) (Fin k) (Completion f) ↦
        M.map T.completionMap) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact T.completionMap.continuous.comp <|
        (continuous_apply j).comp (continuous_apply i)
    exact hmap.comp (continuous_star.mul continuous_id)
  · intro Y
    exact hcore k Y

set_option backward.isDefEq.respectTransparency false in
/-- A compatible completed contraction is completely positive if all matrix star squares from
the dense algebraic direct-limit core have positive image. -/
def completionCompletelyPositiveMap
    (hcore : ∀ k (X : Fin k → Fin k → AlgebraicLimit f),
      0 ≤ (star (coreMatrix (f := f) k X) * coreMatrix (f := f) k X).map T.completionMap) :
    Completion f →CP Completion f where
  toLinearMap := T.completionMap.toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    rw [StarOrderedRing.nonneg_iff] at hM
    induction hM using AddSubmonoid.closure_induction with
    | mem Y hY =>
        obtain ⟨X, rfl⟩ := hY
        exact T.completionMap_matrix_star_mul_self_nonneg hcore k X
    | zero =>
        have hz : (0 : CStarMatrix (Fin k) (Fin k) (Completion f)).map
            T.completionMap.toLinearMap = 0 := by
          ext i j
          rw [CStarMatrix.map_apply]
          simp
        rw [hz]
    | add X Y _ _ hX hY =>
        have hadd : (X + Y).map T.completionMap.toLinearMap =
            X.map T.completionMap.toLinearMap + Y.map T.completionMap.toLinearMap := by
          ext i j
          simp only [CStarMatrix.map_apply, CStarMatrix.add_apply, map_add]
        rw [hadd]
        exact add_nonneg hX hY

@[simp]
theorem completionCompletelyPositiveMap_apply
    (hcore : ∀ k (X : Fin k → Fin k → AlgebraicLimit f),
      0 ≤ (star (coreMatrix (f := f) k X) * coreMatrix (f := f) k X).map T.completionMap)
    (x : Completion f) :
    T.completionCompletelyPositiveMap hcore x = T.completionMap x :=
  rfl

/-- The completed CP map is unital whenever the compatible local contraction is unital. -/
theorem completionCompletelyPositiveMap_one
    (hcore : ∀ k (X : Fin k → Fin k → AlgebraicLimit f),
      0 ≤ (star (coreMatrix (f := f) k X) * coreMatrix (f := f) k X).map T.completionMap)
    (hT : ∀ i, T.map i 1 = 1) :
    T.completionCompletelyPositiveMap hcore 1 = 1 :=
  T.completionMap_one hT

end CompatibleLinearContraction

end NCG.PreCStarDirectLimit
