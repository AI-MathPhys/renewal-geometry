/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealQuadraticEulerIdentity

/-!
# Extended energies of linear operators on submodule domains

An operator defined on a linear submodule determines the extended energy `‖A x‖²` on its domain
and `∞` outside.  This module supplies its exact effective domain and automatic real
two-homogeneity, the algebraic ingredients required by the quadratic Mosco converse.
-/

open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace K F]

/-- The extended squared-graph energy of a linear operator on a submodule domain. -/
def ennrealOperatorGraphEnergy
    (D : Submodule K E) (A : D →ₗ[K] F) (x : E) : ENNReal :=
  by
    classical
    exact if hx : x ∈ D then ENNReal.ofReal (‖A ⟨x, hx⟩‖ ^ 2) else ∞

@[simp] theorem ennrealOperatorGraphEnergy_ne_top_iff
    (D : Submodule K E) (A : D →ₗ[K] F) (x : E) :
    ennrealOperatorGraphEnergy D A x ≠ ∞ ↔ x ∈ D := by
  simp [ennrealOperatorGraphEnergy]

@[simp] theorem ennrealOperatorGraphEnergy_toReal
    (D : Submodule K E) (A : D →ₗ[K] F) (x : E) (hx : x ∈ D) :
    (ennrealOperatorGraphEnergy D A x).toReal = ‖A ⟨x, hx⟩‖ ^ 2 := by
  simp [ennrealOperatorGraphEnergy, hx]

@[simp] theorem ennrealOperatorGraphEnergy_zero
    (D : Submodule K E) (A : D →ₗ[K] F) :
    ennrealOperatorGraphEnergy D A 0 = 0 := by
  classical
  rw [ennrealOperatorGraphEnergy]
  split
  · change ENNReal.ofReal (‖A (0 : D)‖ ^ 2) = 0
    simp
  · rename_i hzero
    exact (hzero D.zero_mem).elim

/-- Every squared graph energy is two-homogeneous along real scalar multiples of its effective
domain. -/
theorem isENNRealTwoHomogeneous_operatorGraphEnergy
    (D : Submodule K E) (A : D →ₗ[K] F) :
    IsENNRealTwoHomogeneous (K := K) (ennrealOperatorGraphEnergy D A) := by
  constructor
  · intro r x hx
    rw [ennrealOperatorGraphEnergy_ne_top_iff] at hx ⊢
    exact D.smul_mem (((r : ℝ) : K)) hx
  · intro r x hx
    have hxD : x ∈ D := (ennrealOperatorGraphEnergy_ne_top_iff D A x).mp hx
    have hrx : (((r : ℝ) : K)) • x ∈ D := D.smul_mem (((r : ℝ) : K)) hxD
    rw [ennrealOperatorGraphEnergy_toReal D A _ hrx,
      ennrealOperatorGraphEnergy_toReal D A x hxD]
    have hsub :
        (⟨(((r : ℝ) : K)) • x, hrx⟩ : D) =
          (((r : ℝ) : K)) • (⟨x, hxD⟩ : D) := by
      rfl
    rw [hsub, map_smul, norm_smul, RCLike.norm_ofReal, mul_pow, sq_abs]


/-- The finite part of every squared linear-operator graph energy is convex on its effective
domain. -/
theorem convexOn_ennrealOperatorGraphEnergy
    [NormedSpace ℝ E] [IsScalarTower ℝ K E]
    [NormedSpace ℝ F] [IsScalarTower ℝ K F]
    (D : Submodule K E) (A : D →ₗ[K] F) :
    ConvexOn ℝ {x : E | ennrealOperatorGraphEnergy D A x ≠ ∞}
      (fun x ↦ (ennrealOperatorGraphEnergy D A x).toReal) := by
  have hdomain : {x : E | ennrealOperatorGraphEnergy D A x ≠ ∞} = (D : Set E) := by
    ext x
    exact ennrealOperatorGraphEnergy_ne_top_iff D A x
  rw [hdomain]
  constructor
  · exact (D.restrictScalars ℝ).convex
  intro x hx y hy a b ha hb hab
  have hcomb : a • x + b • y ∈ D :=
    (D.restrictScalars ℝ).convex hx hy ha hb hab
  change (ennrealOperatorGraphEnergy D A (a • x + b • y)).toReal ≤
    a * (ennrealOperatorGraphEnergy D A x).toReal +
      b * (ennrealOperatorGraphEnergy D A y).toReal
  rw [ennrealOperatorGraphEnergy_toReal D A _ hcomb,
    ennrealOperatorGraphEnergy_toReal D A x hx,
    ennrealOperatorGraphEnergy_toReal D A y hy]
  let AR : D →ₗ[ℝ] F := A.restrictScalars ℝ
  let ux : F := A ⟨x, hx⟩
  let uy : F := A ⟨y, hy⟩
  have hsub :
      (⟨a • x + b • y, hcomb⟩ : D) =
        a • (⟨x, hx⟩ : D) + b • (⟨y, hy⟩ : D) := by
    rfl
  have hAcomb :
      A ⟨a • x + b • y, hcomb⟩ = a • ux + b • uy := by
    change AR ⟨a • x + b • y, hcomb⟩ = a • ux + b • uy
    rw [hsub, map_add, map_smul, map_smul]
    rfl
  rw [hAcomb]
  have hnorm : ‖a • ux + b • uy‖ ≤ a * ‖ux‖ + b * ‖uy‖ := by
    calc
      ‖a • ux + b • uy‖ ≤ ‖a • ux‖ + ‖b • uy‖ := norm_add_le _ _
      _ = a * ‖ux‖ + b * ‖uy‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
  have hrightNonneg : 0 ≤ a * ‖ux‖ + b * ‖uy‖ :=
    add_nonneg (mul_nonneg ha (norm_nonneg _)) (mul_nonneg hb (norm_nonneg _))
  have hsquareMono :
      ‖a • ux + b • uy‖ ^ 2 ≤ (a * ‖ux‖ + b * ‖uy‖) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnorm)
      (add_nonneg (norm_nonneg (a • ux + b • uy)) hrightNonneg)]
  have hjensen :
      (a * ‖ux‖ + b * ‖uy‖) ^ 2 ≤
        a * ‖ux‖ ^ 2 + b * ‖uy‖ ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (‖ux‖ - ‖uy‖))]
  exact hsquareMono.trans hjensen
end NCG.VaryingHilbert
