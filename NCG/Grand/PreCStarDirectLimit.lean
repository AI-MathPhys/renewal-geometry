/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CStarAlgebraCompletion
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Normed direct limits of pre-C-star algebras

Mathlib's algebraic `DirectLimit` already transports the ring, complex-algebra, and star
structures of a directed system.  This file adds the analytic structure when every connecting
map is isometric.  The resulting algebraic limit is a (usually incomplete) normed pre-C-star
algebra, and its uniform completion is consequently a genuine C-star algebra by
`NCG.Grand.CStarAlgebraCompletion`.

The construction is deliberately independent of finite dimensionality.  It applies in
particular to algebraic AF limits, but also to any directed system of normed complex star
algebras whose connecting star-algebra homomorphisms preserve the norm.

## Main definitions

* `NCG.PreCStarDirectLimit.IsometricSystem`: norm preservation for all connecting maps;
* `NCG.PreCStarDirectLimit.of`: the canonical star-algebra map from a stage;
* `NCG.PreCStarDirectLimit.ofLinearIsometry`: the same map as a linear isometry;
* `NCG.PreCStarDirectLimit.Completion`: the completed direct limit;
* `NCG.PreCStarDirectLimit.completionOf`: the canonical stage map into the completion.

The final density theorem says that the images of all stages are dense in the completed limit.
-/

open scoped ComplexOrder

noncomputable section

namespace NCG.PreCStarDirectLimit

universe u v

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A : ι → Type v}
variable [∀ i, NormedRing (A i)] [∀ i, StarRing (A i)] [∀ i, CStarRing (A i)]
variable [∀ i, NormedAlgebra ℂ (A i)] [∀ i, StarModule ℂ (A i)]

/-- A directed system of star-algebra homomorphisms is isometric when every connecting map
preserves the norm. -/
class IsometricSystem
    (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j) : Prop where
  norm_map : ∀ i j (hij : i ≤ j) (x : A i), ‖f i j hij x‖ = ‖x‖

variable (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
variable [DirectedSystem A (fun i j hij ↦ f i j hij)] [IsometricSystem f]

/-- The underlying algebraic direct limit. -/
abbrev AlgebraicLimit := DirectLimit A (fun i j hij ↦ f i j hij)

/-- The norm on the algebraic direct limit, obtained by descending the norms on its stages. -/
def limitNorm : AlgebraicLimit f → ℝ :=
  DirectLimit.lift (fun i j hij ↦ f i j hij) (fun _ x ↦ ‖x‖) fun i j hij x ↦
    (IsometricSystem.norm_map i j hij x).symm

noncomputable instance instNorm : Norm (AlgebraicLimit f) :=
  ⟨limitNorm f⟩

omit [Nonempty ι] [∀ i, CStarRing (A i)] [∀ i, StarModule ℂ (A i)] in
@[simp]
theorem norm_mk (i : ι) (x : A i) :
    ‖(⟦⟨i, x⟩⟧ : AlgebraicLimit f)‖ = ‖x‖ :=
  rfl

omit [∀ i, CStarRing (A i)] [∀ i, StarModule ℂ (A i)] in
private theorem norm_zero_limit : ‖(0 : AlgebraicLimit f)‖ = 0 := by
  let i := Classical.arbitrary ι
  rw [DirectLimit.zero_def i, norm_mk, norm_zero]

omit [∀ i, CStarRing (A i)] [∀ i, StarModule ℂ (A i)] in
private theorem norm_neg_limit (x : AlgebraicLimit f) : ‖-x‖ = ‖x‖ := by
  induction x using DirectLimit.induction with
  | _ i x => simp only [DirectLimit.neg_def, norm_mk, norm_neg]

omit [Nonempty ι] [∀ i, CStarRing (A i)] [∀ i, StarModule ℂ (A i)] in
private theorem norm_add_le_limit (x y : AlgebraicLimit f) :
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  induction x, y using DirectLimit.induction₂ with
  | _ i x y => simpa only [DirectLimit.add_def, norm_mk] using norm_add_le x y

omit [∀ i, CStarRing (A i)] [∀ i, StarModule ℂ (A i)] in
private theorem eq_zero_of_norm_eq_zero_limit {x : AlgebraicLimit f} (hx : ‖x‖ = 0) : x = 0 := by
  induction x using DirectLimit.induction with
  | _ i x =>
      rw [norm_mk] at hx
      rw [norm_eq_zero.mp hx]
      exact (DirectLimit.zero_def i).symm

noncomputable instance instMetricSpace : MetricSpace (AlgebraicLimit f) where
  dist x y := ‖-x + y‖
  dist_self x := by rw [neg_add_cancel, norm_zero_limit]
  dist_comm x y := by
    calc
      ‖-x + y‖ = ‖-(-x + y)‖ := (norm_neg_limit (f := f) (-x + y)).symm
      _ = ‖-y + x‖ := by congr 1; abel
  dist_triangle x y z := by
    rw [show -x + z = (-x + y) + (-y + z) by abel]
    exact norm_add_le_limit (f := f) _ _
  eq_of_dist_eq_zero h := by
    have hz : -_ + _ = (0 : AlgebraicLimit f) :=
      eq_zero_of_norm_eq_zero_limit (f := f) h
    exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg, add_comm] using hz)).symm

/- `DirectLimit` is a quotient and therefore also receives generic quotient topology instances.
For an isometric algebraic limit the intended analytic topology and uniformity are the ones
induced by the norm constructed above.  Give these projections priority over the unrelated
generic quotient instances. -/
noncomputable instance (priority := 2000) instTopologicalSpace :
    TopologicalSpace (AlgebraicLimit f) :=
  (inferInstance : MetricSpace (AlgebraicLimit f)).toPseudoMetricSpace.toUniformSpace
    |>.toTopologicalSpace

noncomputable instance (priority := 2000) instUniformSpace :
    UniformSpace (AlgebraicLimit f) :=
  (inferInstance : MetricSpace (AlgebraicLimit f)).toPseudoMetricSpace.toUniformSpace

noncomputable instance (priority := 2000) instBornology :
    Bornology (AlgebraicLimit f) :=
  (inferInstance : MetricSpace (AlgebraicLimit f)).toPseudoMetricSpace.toBornology

noncomputable instance instNormedRing : NormedRing (AlgebraicLimit f) where
  dist_eq _ _ := rfl
  norm_mul_le x y := by
    induction x, y using DirectLimit.induction₂ with
    | _ i x y => simpa only [DirectLimit.mul_def, norm_mk] using norm_mul_le x y

noncomputable instance instNormedAlgebra : NormedAlgebra ℂ (AlgebraicLimit f) where
  norm_smul_le r x := by
    induction x using DirectLimit.induction with
    | _ i x => simpa only [DirectLimit.smul_def, norm_mk] using norm_smul_le r x

noncomputable instance instCStarRing : CStarRing (AlgebraicLimit f) where
  norm_mul_self_le x := by
    induction x using DirectLimit.induction with
    | _ i x =>
        simpa only [DirectLimit.star_def, DirectLimit.mul_def, norm_mk]
          using CStarRing.norm_mul_self_le (x := x)

/-- The canonical star-algebra homomorphism from a stage to the algebraic direct limit. -/
def of (i : ι) : A i →⋆ₐ[ℂ] AlgebraicLimit f where
  __ := DirectLimit.Algebra.of A (fun i j hij ↦ f i j hij) i
  map_star' x := (DirectLimit.star_def i x).symm

omit [∀ i, CStarRing (A i)] [∀ i, StarModule ℂ (A i)] [IsometricSystem f] in
@[simp]
theorem of_apply (i : ι) (x : A i) :
    of f i x = (⟦⟨i, x⟩⟧ : AlgebraicLimit f) :=
  rfl

omit [∀ i, CStarRing (A i)] [∀ i, StarModule ℂ (A i)] in
@[simp]
theorem norm_of (i : ι) (x : A i) : ‖of f i x‖ = ‖x‖ :=
  rfl

omit [∀ i, CStarRing (A i)] [∀ i, StarModule ℂ (A i)] in
theorem of_isometry (i : ι) : Isometry (of f i) :=
  AddMonoidHomClass.isometry_of_norm (of f i) (norm_of f i)

/-- The canonical map from a stage, bundled as a complex linear isometry. -/
def ofLinearIsometry (i : ι) : A i →ₗᵢ[ℂ] AlgebraicLimit f where
  __ := (of f i).toLinearMap
  norm_map' := norm_of f i

omit [∀ i, CStarRing (A i)] [∀ i, StarModule ℂ (A i)] in
@[simp]
theorem ofLinearIsometry_apply (i : ι) (x : A i) :
    ofLinearIsometry f i x = of f i x :=
  rfl

/-- The completed direct limit.  This is a genuine C-star algebra by the instances in
`NCG.Grand.CStarAlgebraCompletion`. -/
abbrev Completion := UniformSpace.Completion (AlgebraicLimit f)

/-- The canonical star-algebra homomorphism from a stage into the completed direct limit. -/
def completionOf (i : ι) : A i →⋆ₐ[ℂ] Completion f where
  toFun x := (of f i x : Completion f)
  map_one' := by
    rw [map_one]
    exact UniformSpace.Completion.coe_one _
  map_mul' x y := by
    rw [map_mul]
    exact UniformSpace.Completion.coe_mul _ _
  map_zero' := by
    rw [map_zero]
    exact UniformSpace.Completion.coe_zero
  map_add' x y := by
    rw [map_add]
    exact UniformSpace.Completion.coe_add _ _
  commutes' r := by
    change ((of f i (algebraMap ℂ (A i) r) : AlgebraicLimit f) : Completion f) =
      ((algebraMap ℂ (AlgebraicLimit f) r : AlgebraicLimit f) : Completion f)
    congr 1
    exact (of f i).commutes r
  map_star' x := by
    rw [map_star]
    exact (UniformSpace.Completion.coe_star (A := AlgebraicLimit f) (of f i x)).symm

omit [∀ i, StarModule ℂ (A i)] in
@[simp]
theorem completionOf_apply (i : ι) (x : A i) :
    completionOf f i x = (of f i x : Completion f) :=
  rfl

omit [∀ i, StarModule ℂ (A i)] in
@[simp]
theorem norm_completionOf (i : ι) (x : A i) : ‖completionOf f i x‖ = ‖x‖ := by
  rw [completionOf_apply, UniformSpace.Completion.norm_coe, norm_of]

omit [∀ i, StarModule ℂ (A i)] in
theorem completionOf_isometry (i : ι) : Isometry (completionOf f i) :=
  AddMonoidHomClass.isometry_of_norm (completionOf f i) (norm_completionOf f i)

/-- All stage elements, regarded as a single map into the completed direct limit. -/
def stageMap : (Σ i, A i) → Completion f :=
  fun x ↦ completionOf f x.1 x.2

omit [∀ i, StarModule ℂ (A i)] in
/-- The union of the finite-stage images is exactly the image of the algebraic direct limit
inside its completion. -/
theorem range_stageMap :
    Set.range (stageMap f) = Set.range (fun x : AlgebraicLimit f ↦ (x : Completion f)) := by
  ext x
  constructor
  · rintro ⟨⟨i, a⟩, rfl⟩
    exact ⟨of f i a, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨i, x, rfl⟩ :=
      DirectLimit.exists_eq_mk (fun i j hij ↦ f i j hij) a
    exact ⟨⟨i, x⟩, rfl⟩

omit [∀ i, StarModule ℂ (A i)] in
/-- The images of the stages are dense in the completed direct limit. -/
theorem denseRange_stageMap : DenseRange (stageMap f) := by
  rw [DenseRange, range_stageMap]
  exact UniformSpace.Completion.denseRange_coe

end NCG.PreCStarDirectLimit
