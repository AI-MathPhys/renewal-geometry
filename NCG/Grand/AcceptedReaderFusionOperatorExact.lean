/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exact endpoint-reader fusion pullback action

This file places the AO.17 operator `(eF)†(eF)` in the theorem and proves that its quadratic
energy, and hence its fibre infimum, is exactly the physical endpoint action.
-/

open scoped InnerProductSpace

namespace NCG

/-- Fusion from allocation coordinates `(n, α)` to the physical endpoint coordinate `n`. -/
noncomputable def endpointAllocationFusion
    {N : Type*} [Fintype N]
    (Alloc : N → Type*) [∀ n, Fintype (Alloc n)] :
    EuclideanSpace ℂ (Sigma Alloc) →ₗ[ℂ] EuclideanSpace ℂ N where
  toFun y := WithLp.toLp 2 (fun n => ∑ a : Alloc n, WithLp.ofLp y ⟨n, a⟩)
  map_add' y z := by
    ext n
    simp [Finset.sum_add_distrib]
  map_smul' c y := by
    ext n
    simp [Finset.mul_sum]

/-- The pulled-back occurrence action operator is literally `(eF)†(eF)`. -/
noncomputable def endpointFusionPullbackAction
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    (F : Y →ₗ[ℂ] X) (e : X →ₗ[ℂ] ℂ) : Y →ₗ[ℂ] Y :=
  let L := e ∘ₗ F
  L.adjoint ∘ₗ L

/-- Every representative of one fusion fibre has the same AO.17 operator energy. -/
theorem endpointFusionPullbackAction_energy
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    (F : Y →ₗ[ℂ] X) (e : X →ₗ[ℂ] ℂ)
    (x : X) (y : Y) (hy : F y = x) :
    inner ℂ y (endpointFusionPullbackAction F e y) = ((‖e x‖ : ℝ) : ℂ) ^ 2 := by
  let L : Y →ₗ[ℂ] ℂ := e ∘ₗ F
  have hinner : inner ℂ y (L.adjoint (L y)) = inner ℂ (L y) (L y) :=
    LinearMap.adjoint_inner_right L y (L y)
  change inner ℂ y (L.adjoint (L y)) = ((‖e x‖ : ℝ) : ℂ) ^ 2
  rw [hinner, inner_self_eq_norm_sq_to_K]
  simp [L, hy]

/-- The image of the concrete pulled-back operator energy on a nonempty fibre is a singleton. -/
theorem endpointFusionPullbackAction_fibreRange
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    (F : Y →ₗ[ℂ] X) (e : X →ₗ[ℂ] ℂ)
    (x : X) (y₀ : Y) (hy₀ : F y₀ = x) :
    Set.range (fun y : {y : Y // F y = x} =>
      (inner ℂ (y : Y) (endpointFusionPullbackAction F e y)).re) = {‖e x‖ ^ 2} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    have h := congrArg Complex.re
      (endpointFusionPullbackAction_energy F e x y y.property)
    calc
      _ = (((‖e x‖ : ℝ) : ℂ) ^ 2).re := h
      _ = ‖e x‖ ^ 2 := by
        rw [← Complex.ofReal_pow, Complex.ofReal_re]
  · intro hz
    have hz' : z = ‖e x‖ ^ 2 := by simpa using hz
    refine ⟨⟨y₀, hy₀⟩, ?_⟩
    have h := congrArg Complex.re
      (endpointFusionPullbackAction_energy F e x y₀ hy₀)
    have he : (inner ℂ y₀ (endpointFusionPullbackAction F e y₀)).re = ‖e x‖ ^ 2 := by
      calc
        _ = (((‖e x‖ : ℝ) : ℂ) ^ 2).re := h
        _ = ‖e x‖ ^ 2 := by
          rw [← Complex.ofReal_pow, Complex.ofReal_re]
    change (inner ℂ y₀ (endpointFusionPullbackAction F e y₀)).re = z
    exact he.trans hz'.symm
/-- **Endpoint fusion invariance of the occurrence action (`thm:accepted-reader-fusion`).**
For the actual finite allocation fusion, the fibre energy range is a singleton and its infimum
is exactly the physical endpoint action `|e x|²`. -/
theorem acceptedReaderFusion_occurrenceAction_exact
    {N : Type*} [Fintype N]
    (Alloc : N → Type*) [∀ n, Fintype (Alloc n)]
    (e : EuclideanSpace ℂ N →ₗ[ℂ] ℂ)
    (x : EuclideanSpace ℂ N)
    (y₀ : EuclideanSpace ℂ (Sigma Alloc))
    (hy₀ : endpointAllocationFusion Alloc y₀ = x) :
    let F := endpointAllocationFusion Alloc
    Set.range (fun y : {y : EuclideanSpace ℂ (Sigma Alloc) // F y = x} =>
      (inner ℂ (y : EuclideanSpace ℂ (Sigma Alloc))
        (endpointFusionPullbackAction F e y)).re) = {‖e x‖ ^ 2}
    ∧ sInf (Set.range (fun y : {y : EuclideanSpace ℂ (Sigma Alloc) // F y = x} =>
      (inner ℂ (y : EuclideanSpace ℂ (Sigma Alloc))
        (endpointFusionPullbackAction F e y)).re)) = ‖e x‖ ^ 2 := by
  dsimp only
  have hrange := endpointFusionPullbackAction_fibreRange
    (endpointAllocationFusion Alloc) e x y₀ hy₀
  refine ⟨hrange, ?_⟩
  rw [hrange]
  simp

end NCG





