/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Fubini equivalence for ℓ² with a finite Euclidean fibre

Square-summable vectors with values in a finite Euclidean space are
canonically unitarily equivalent to a finite `L²` product of scalar
square-summable sequences.  This is the coefficient-carrier swap needed to
pass between vector-valued Fourier multipliers and coordinatewise scalar
Fourier transforms.
-/

open scoped lp

noncomputable section

namespace NCG

variable {ι r : Type*} [Fintype r]

/-- Swap the infinite ℓ² index with a finite Euclidean fibre. -/
def l2EuclideanToPiL2LinearMap :
    ℓ²(ι, EuclideanSpace ℂ r) →ₗ[ℂ]
      PiLp 2 (fun _ : r ↦ ℓ²(ι, ℂ)) where
  toFun f := WithLp.toLp 2 fun a ↦
    ⟨fun i ↦ f i a,
      (lp.memℓp f).mono' fun i ↦ PiLp.norm_apply_le (f i) a⟩
  map_add' f g := by
    apply WithLp.ofLp_injective
    funext a
    apply lp.ext
    funext i
    rfl
  map_smul' c f := by
    apply WithLp.ofLp_injective
    funext a
    apply lp.ext
    funext i
    rfl

@[simp]
theorem l2EuclideanToPiL2LinearMap_apply
    (f : ℓ²(ι, EuclideanSpace ℂ r)) (a : r) (i : ι) :
    l2EuclideanToPiL2LinearMap f a i = f i a := rfl

theorem l2EuclideanToPiL2LinearMap_norm
    (f : ℓ²(ι, EuclideanSpace ℂ r)) :
    ‖l2EuclideanToPiL2LinearMap f‖ = ‖f‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [PiLp.norm_sq_eq_of_L2]
  have hsource : ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
    simpa using lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) f
  rw [hsource]
  have hcoord (a : r) :
      ‖l2EuclideanToPiL2LinearMap f a‖ ^ 2 =
        ∑' i, ‖f i a‖ ^ 2 := by
    simpa using lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num)
      (l2EuclideanToPiL2LinearMap f a)
  simp_rw [hcoord]
  have hsummable (a : r) : Summable (fun i ↦ ‖f i a‖ ^ 2) := by
    simpa using (lp.memℓp (l2EuclideanToPiL2LinearMap f a)).summable
      (by norm_num : 0 < (2 : ENNReal).toReal)
  rw [← Summable.tsum_finsetSum
    (s := Finset.univ) (fun a _ ↦ hsummable a)]
  apply tsum_congr
  intro i
  exact (PiLp.norm_sq_eq_of_L2 (fun _ : r ↦ ℂ) (f i)).symm

/-- The Fubini swap is an isometric linear embedding. -/
def l2EuclideanToPiL2LinearIsometry :
    ℓ²(ι, EuclideanSpace ℂ r) →ₗᵢ[ℂ]
      PiLp 2 (fun _ : r ↦ ℓ²(ι, ℂ)) :=
  ⟨l2EuclideanToPiL2LinearMap,
    l2EuclideanToPiL2LinearMap_norm⟩

theorem l2EuclideanToPiL2LinearIsometry_surjective :
    Function.Surjective
      (l2EuclideanToPiL2LinearIsometry (ι := ι) (r := r)) := by
  intro g
  let v : ι → EuclideanSpace ℂ r := fun i ↦
    WithLp.toLp 2 fun a ↦ g a i
  have hsummable (a : r) : Summable (fun i ↦ ‖g a i‖ ^ 2) := by
    simpa using (lp.memℓp (g a)).summable
      (by norm_num : 0 < (2 : ENNReal).toReal)
  have hsum : Summable (fun i ↦ ∑ a, ‖g a i‖ ^ 2) :=
    summable_sum fun a _ ↦ hsummable a
  have hv : Memℓp v 2 := by
    apply memℓp_gen
    convert hsum using 1
    funext i
    simpa [v] using PiLp.norm_sq_eq_of_L2 (fun _ : r ↦ ℂ) (v i)
  refine ⟨⟨v, hv⟩, ?_⟩
  apply WithLp.ofLp_injective
  funext a
  apply lp.ext
  funext i
  rfl

/-- Canonical unitary Fubini swap for a finite complex fibre. -/
def l2EuclideanToPiL2Equiv :
    ℓ²(ι, EuclideanSpace ℂ r) ≃ₗᵢ[ℂ]
      PiLp 2 (fun _ : r ↦ ℓ²(ι, ℂ)) :=
  LinearIsometryEquiv.ofSurjective l2EuclideanToPiL2LinearIsometry
    l2EuclideanToPiL2LinearIsometry_surjective

@[simp]
theorem l2EuclideanToPiL2Equiv_apply
    (f : ℓ²(ι, EuclideanSpace ℂ r)) (a : r) (i : ι) :
    l2EuclideanToPiL2Equiv f a i = f i a := rfl

end NCG
