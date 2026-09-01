/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite compiler for centered coordinate demands

The demand norm in a hierarchy block is a weighted coordinate maximum norm.
After diagonal rescaling its `d`-dimensional centered space has the explicit
basis `eᵢ-e_last`.  This file proves the coefficient estimate and constructs
one linear router from pointwise routes with the exact factor `d`; no
Auerbach-basis hypothesis is left implicit.
-/

open scoped BigOperators

noncomputable section

namespace NCG
namespace CenteredCoordinateRouterCompiler

def basisDemand {d : ℕ} (i : Fin d) (x : Fin (d + 1)) : ℝ :=
  if x = i.castSucc then 1 else if x = Fin.last d then -1 else 0

theorem last_ne_castSucc {d : ℕ} (i : Fin d) :
    Fin.last d ≠ i.castSucc := Ne.symm (Fin.castSucc_ne_last i)

theorem basisDemand_centered {d : ℕ} (i : Fin d) :
    ∑ x, basisDemand i x = 0 := by
  classical
  rw [Fin.sum_univ_castSucc]
  simp [basisDemand, last_ne_castSucc]

theorem basisDemand_abs_le_one {d : ℕ} (i : Fin d) :
    ∀ x, |basisDemand i x| ≤ 1 := by
  intro x
  classical
  unfold basisDemand
  split_ifs <;> norm_num

theorem centered_eq_basis_sum
    {d : ℕ} (g : Fin (d + 1) → ℝ) (hcenter : ∑ x, g x = 0) :
    g = ∑ i : Fin d, g i.castSucc • basisDemand i := by
  funext x
  classical
  cases x using Fin.lastCases with
  | last =>
      rw [Fin.sum_univ_castSucc] at hcenter
      simp [basisDemand, last_ne_castSucc]
      linarith
  | cast x =>
      simp [basisDemand]

def HasPointwiseCubeBound
    {d : ℕ} {J : Type*} [AddCommGroup J] [Module ℝ J]
    (boundary : J →ₗ[ℝ] (Fin (d + 1) → ℝ))
    (currentGauge : J → ℝ) (C : ℝ) : Prop :=
  ∀ g, (∑ x, g x = 0) → (∀ x, |g x| ≤ 1) →
    ∃ j, boundary j = g ∧ currentGauge j ≤ C

def HasLinearCubeBound
    {d : ℕ} {J : Type*} [AddCommGroup J] [Module ℝ J]
    (boundary : J →ₗ[ℝ] (Fin (d + 1) → ℝ))
    (currentGauge : J → ℝ) (C : ℝ) : Prop :=
  ∃ R : (Fin (d + 1) → ℝ) →ₗ[ℝ] J,
    (∀ g, (∑ x, g x = 0) → boundary (R g) = g) ∧
    ∀ g, (∑ x, g x = 0) → (∀ x, |g x| ≤ 1) →
      currentGauge (R g) ≤ C

theorem linear_implies_pointwise
    {d : ℕ} {J : Type*} [AddCommGroup J] [Module ℝ J]
    (boundary : J →ₗ[ℝ] (Fin (d + 1) → ℝ))
    (currentGauge : J → ℝ) (C : ℝ)
    (h : HasLinearCubeBound boundary currentGauge C) :
    HasPointwiseCubeBound boundary currentGauge C := by
  obtain ⟨R, hright, hbound⟩ := h
  intro g hg hg1
  exact ⟨R g, hright g hg, hbound g hg hg1⟩

theorem pointwise_compiles_linear
    {d : ℕ} {J : Type*} [AddCommGroup J] [Module ℝ J]
    (boundary : J →ₗ[ℝ] (Fin (d + 1) → ℝ))
    (currentGauge : J → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (htriangle : ∀ (a : Fin d → ℝ) (j : Fin d → J),
      currentGauge (∑ i, a i • j i) ≤
        ∑ i, |a i| * currentGauge (j i))
    (hpoint : HasPointwiseCubeBound boundary currentGauge C) :
    HasLinearCubeBound boundary currentGauge (d * C) := by
  choose j hjBoundary hjGauge using fun i : Fin d =>
    hpoint (basisDemand i) (basisDemand_centered i)
      (basisDemand_abs_le_one i)
  let R : (Fin (d + 1) → ℝ) →ₗ[ℝ] J :=
    { toFun := fun g => ∑ i, g i.castSucc • j i
      map_add' := by
        intro g h
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro a g
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul] }
  refine ⟨R, ?_, ?_⟩
  · intro g hg
    change boundary (∑ i, g i.castSucc • j i) = g
    rw [map_sum]
    simp_rw [map_smul, hjBoundary]
    exact (centered_eq_basis_sum g hg).symm
  · intro g _ hg
    change currentGauge (∑ i, g i.castSucc • j i) ≤ d * C
    calc
      currentGauge (∑ i, g i.castSucc • j i) ≤
          ∑ i, |g i.castSucc| * currentGauge (j i) := htriangle _ _
      _ ≤ ∑ _i : Fin d, 1 * C := by
        apply Finset.sum_le_sum
        intro i _
        calc
          |g i.castSucc| * currentGauge (j i) ≤ |g i.castSucc| * C :=
            mul_le_mul_of_nonneg_left (hjGauge i) (abs_nonneg _)
          _ ≤ 1 * C := mul_le_mul_of_nonneg_right (hg i.castSucc) hC
      _ = d * C := by simp

end CenteredCoordinateRouterCompiler
end NCG
