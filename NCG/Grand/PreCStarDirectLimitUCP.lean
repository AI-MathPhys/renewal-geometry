/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PreCStarDirectLimitCompletelyPositive

/-!
# Compatible UCP maps on pre-C-star direct limits

Compatible unital completely positive contractions on complete local C-star algebras induce a
unique UCP contraction on the completed direct limit. The finite common-stage lemma below is the
bridge between local complete positivity and positivity on matrix star squares in the algebraic
direct-limit core.
-/

open scoped CStarAlgebra

noncomputable section

namespace NCG.PreCStarDirectLimit

open UniformSpace UniformSpace.Completion

universe u v

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A : ι → Type v}
variable [∀ i, CStarAlgebra (A i)] [∀ i, PartialOrder (A i)]
variable [∀ i, StarOrderedRing (A i)]
variable (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
variable [DirectedSystem A (fun i j hij ↦ f i j hij)] [IsometricSystem f]

/-- A compatible family of unital completely positive contractions on the local stages. -/
structure CompatibleUCPContraction where
  /-- The completely positive local map at each stage. -/
  map : ∀ i, A i →CP A i
  /-- The local maps are unital. -/
  map_one : ∀ i, map i 1 = 1
  /-- Contractivity is recorded explicitly, avoiding any dependence on an automatic-continuity
  theorem for UCP maps. -/
  norm_apply_le : ∀ i (x : A i), ‖map i x‖ ≤ ‖x‖
  /-- The local maps commute with every connecting embedding. -/
  compatible : ∀ i j (hij : i ≤ j) (x : A i),
    map j (f i j hij x) = f i j hij (map i x)

namespace CompatibleUCPContraction

variable (T : CompatibleUCPContraction f)
variable {f}

/-- The underlying local linear map with its evaluation function exposed definitionally. -/
private def localLinearMap (i : ι) : A i →ₗ[ℂ] A i where
  toFun := fun x ↦ T.map i x
  map_add' x y := map_add (T.map i) x y
  map_smul' c x := map_smul (T.map i) c x

omit [IsDirectedOrder ι] [Nonempty ι]
  [DirectedSystem A (fun i j hij ↦ f i j hij)] [IsometricSystem f] in
@[simp]
private theorem localLinearMap_apply (i : ι) (x : A i) :
    T.localLinearMap i x = T.map i x :=
  rfl

/-- The local CP map bundled continuously using its stated contraction bound. -/
private def localContinuousLinearMap (i : ι) : A i →L[ℂ] A i :=
  (T.localLinearMap i).mkContinuous 1 fun x ↦ by
    simpa only [one_mul, localLinearMap_apply] using T.norm_apply_le i x

/-- Forgetting positivity and unitality gives a compatible family of linear contractions. -/
def toCompatibleLinearContraction : CompatibleLinearContraction f where
  map i := T.localContinuousLinearMap i
  norm_apply_le i x := T.norm_apply_le i x
  compatible i j hij x := T.compatible i j hij x

omit [IsDirectedOrder ι] [Nonempty ι]
  [DirectedSystem A (fun i j hij ↦ f i j hij)] [IsometricSystem f] in
@[simp]
theorem toCompatibleLinearContraction_map_apply (i : ι) (x : A i) :
    T.toCompatibleLinearContraction.map i x = T.map i x :=
  rfl

omit [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)] [IsometricSystem f] in
/-- Every finite matrix over the algebraic direct limit is represented entrywise at one common
stage. -/
private theorem exists_commonStage_matrix (k : ℕ)
    (X : Fin k → Fin k → AlgebraicLimit f) :
    ∃ i, ∃ Y : Fin k → Fin k → A i, ∀ p q, X p q = of f i (Y p q) := by
  classical
  choose stage value hvalue using fun p q ↦
    DirectLimit.exists_eq_mk (fun i j hij ↦ f i j hij) (X p q)
  let stages : Finset ι := Finset.univ.image fun pq : Fin k × Fin k ↦ stage pq.1 pq.2
  obtain ⟨i, hi⟩ := Finset.exists_le stages
  have hle (p q : Fin k) : stage p q ≤ i := by
    apply hi
    change stage p q ∈ Finset.univ.image fun pq : Fin k × Fin k ↦ stage pq.1 pq.2
    exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_univ _, rfl⟩
  let Y : Fin k → Fin k → A i :=
    fun p q ↦ f (stage p q) i (hle p q) (value p q)
  refine ⟨i, Y, fun p q ↦ ?_⟩
  calc
    X p q = of f (stage p q) (value p q) := hvalue p q
    _ = of f i (Y p q) := (DirectLimit.Algebra.of_f (hle p q) (value p q)).symm


/-- Local complete positivity implies matrix star-square positivity on the algebraic core. -/
private theorem coreMatrix_star_mul_self_nonneg (k : ℕ)
    (X : Fin k → Fin k → AlgebraicLimit f) :
    0 ≤ (star (CompatibleLinearContraction.coreMatrix (f := f) k X) *
      CompatibleLinearContraction.coreMatrix (f := f) k X).map
        T.toCompatibleLinearContraction.completionMap := by
  obtain ⟨i, Y, hY⟩ := exists_commonStage_matrix (f := f) k X
  let YM : CStarMatrix (Fin k) (Fin k) (A i) := fun p q ↦ Y p q
  have hlocal : 0 ≤ (star YM * YM).map (T.map i) :=
    CompletelyPositiveMap.map_cstarMatrix_nonneg (T.map i) (star YM * YM)
      (star_mul_self_nonneg YM)
  let embCP : A i →CP Completion f :=
    CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (completionOf f i)
  have himage : 0 ≤ ((star YM * YM).map (T.map i)).map embCP :=
    CompletelyPositiveMap.map_cstarMatrix_nonneg embCP _ hlocal
  have heq :
      (star (CompatibleLinearContraction.coreMatrix (f := f) k X) *
        CompatibleLinearContraction.coreMatrix (f := f) k X).map
          T.toCompatibleLinearContraction.completionMap =
      ((star YM * YM).map (T.map i)).map embCP := by
    ext p q
    simp only [CStarMatrix.map_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply]
    simp only [CompatibleLinearContraction.coreMatrix, hY]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Completion.coe_star, ← Completion.coe_mul, ← map_star, ← map_mul]
    change T.toCompatibleLinearContraction.completionMap
        (completionOf f i (star (Y r p) * Y r q)) =
      completionOf f i (T.map i (star (Y r p) * Y r q))
    rw [CompatibleLinearContraction.completionMap_completionOf]
    rw [toCompatibleLinearContraction_map_apply]
  rw [heq]
  exact himage
/-- The completed linear contraction associated to a compatible local UCP family. -/
def completionMap : Completion f →L[ℂ] Completion f :=
  T.toCompatibleLinearContraction.completionMap

@[simp]
theorem completionMap_completionOf (i : ι) (x : A i) :
    T.completionMap (completionOf f i x) = completionOf f i (T.map i x) :=
  T.toCompatibleLinearContraction.completionMap_completionOf i x

theorem norm_completionMap_apply_le (x : Completion f) :
    ‖T.completionMap x‖ ≤ ‖x‖ :=
  T.toCompatibleLinearContraction.norm_completionMap_apply_le x

@[simp]
theorem completionMap_one : T.completionMap 1 = 1 :=
  T.toCompatibleLinearContraction.completionMap_one T.map_one

/-- The unique completed extension, bundled as a completely positive map. -/
def completionUCPMap : Completion f →CP Completion f :=
  T.toCompatibleLinearContraction.completionCompletelyPositiveMap
    T.coreMatrix_star_mul_self_nonneg

@[simp]
theorem completionUCPMap_apply (x : Completion f) :
    T.completionUCPMap x = T.completionMap x :=
  rfl

@[simp]
theorem completionUCPMap_completionOf (i : ι) (x : A i) :
    T.completionUCPMap (completionOf f i x) = completionOf f i (T.map i x) :=
  T.completionMap_completionOf i x

@[simp]
theorem completionUCPMap_one : T.completionUCPMap 1 = 1 :=
  T.completionMap_one

theorem norm_completionUCPMap_apply_le (x : Completion f) :
    ‖T.completionUCPMap x‖ ≤ ‖x‖ :=
  T.norm_completionMap_apply_le x

/-- The completed UCP map is the unique CP map with the prescribed local restrictions. -/
theorem completionUCPMap_unique (ψ : Completion f →CP Completion f)
    (hψ : ∀ i (x : A i), ψ (completionOf f i x) = completionOf f i (T.map i x)) :
    ψ = T.completionUCPMap := by
  apply DFunLike.coe_injective
  apply Completion.ext (map_continuous ψ) (map_continuous T.completionUCPMap)
  intro x
  obtain ⟨i, a, rfl⟩ := DirectLimit.exists_eq_mk (fun i j hij ↦ f i j hij) x
  exact hψ i a |>.trans (T.completionUCPMap_completionOf i a).symm

/-- Any pointwise local semigroup law passes to the completed UCP maps. -/
theorem completionUCPMap_operation {τ : Type*} (op : τ → τ → τ)
    (U : τ → CompatibleUCPContraction f)
    (hU : ∀ s t i (x : A i),
      (U (op s t)).map i x = (U s).map i ((U t).map i x))
    (s t : τ) (x : Completion f) :
    (U (op s t)).completionUCPMap x =
      (U s).completionUCPMap ((U t).completionUCPMap x) := by
  have hlocal : ∀ s t i (x : A i),
      (U (op s t)).toCompatibleLinearContraction.map i x =
        (U s).toCompatibleLinearContraction.map i
          ((U t).toCompatibleLinearContraction.map i x) := by
    intro s t i x
    simpa only [toCompatibleLinearContraction_map_apply] using hU s t i x
  have hcomp := CompatibleLinearContraction.completionMap_operation op
    (fun r ↦ (U r).toCompatibleLinearContraction) hlocal s t
  have hx := congrArg (fun L : Completion f →L[ℂ] Completion f ↦ L x) hcomp
  simpa only [completionUCPMap_apply, completionMap, ContinuousLinearMap.comp_apply] using hx

end CompatibleUCPContraction

end NCG.PreCStarDirectLimit
