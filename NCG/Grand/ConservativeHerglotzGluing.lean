/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandDelay
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Holomorphic conservative gluing of strict matrix Herglotz families

This supplies the analytic-in-the-spectral-parameter layer of
`thm:Herglotz-gluing`.  The pointwise conservation identity and strict
positivity are proved in `GrandDelay`; here they are packaged with complex
differentiability and the Schur response is shown to remain holomorphic on
the strict upper half-plane.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

-- The finite indexing hypotheses are used to construct continuous linear and
-- bilinear assembly maps in the proofs below.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace NCG

/-- The open strict upper half-plane, used as the domain of Herglotz families. -/
def strictUpperHalfPlane : Set ℂ := {z | 0 < z.im}

/-- Coordinatewise holomorphy of a finite matrix family.  In finite
dimensions this is equivalent to holomorphy for any matrix norm, while
avoiding a library-facing choice among equivalent matrix norm instances. -/
def MatrixHolomorphicOn {m n : Type*}
    (F : ℂ → Matrix m n ℂ) (s : Set ℂ) : Prop :=
  ∀ a b, DifferentiableOn ℂ (fun z ↦ F z a b) s

/-- A holomorphic block response whose full block quadratic form has strictly
positive imaginary part in the upper half-plane. -/
structure StrictHerglotzBlockFamily (e i : Type*) [Fintype e] [Fintype i]
    [DecidableEq e] [DecidableEq i] where
  A : ℂ → Matrix e e ℂ
  B : ℂ → Matrix e i ℂ
  C : ℂ → Matrix i e ℂ
  D : ℂ → Matrix i i ℂ
  holomorphic_A : DifferentiableOn ℂ A strictUpperHalfPlane
  holomorphic_B : DifferentiableOn ℂ B strictUpperHalfPlane
  holomorphic_C : DifferentiableOn ℂ C strictUpperHalfPlane
  holomorphic_D : DifferentiableOn ℂ D strictUpperHalfPlane
  strict : ∀ z ∈ strictUpperHalfPlane, ∀ (x : e → ℂ) (u : i → ℂ),
    ¬ (x = 0 ∧ u = 0) →
      0 < (dotProduct (star x) (A z *ᵥ x + B z *ᵥ u) +
        dotProduct (star u) (C z *ᵥ x + D z *ᵥ u)).im

/-- The interface block that is eliminated in conservative gluing. -/
def gluedInterfaceBlock
    {e₁ e₂ i : Type*} [Fintype e₁] [Fintype e₂] [Fintype i]
    [DecidableEq e₁] [DecidableEq e₂] [DecidableEq i]
    (F₁ : StrictHerglotzBlockFamily e₁ i)
    (F₂ : StrictHerglotzBlockFamily e₂ i) (z : ℂ) : Matrix i i ℂ :=
  F₁.D z + F₂.D z

/-- The exterior Schur response obtained by solving the common conservative
interface equation. -/
noncomputable def gluedHerglotzResponse
    {e₁ e₂ i : Type*} [Fintype e₁] [Fintype e₂] [Fintype i]
    [DecidableEq e₁] [DecidableEq e₂] [DecidableEq i]
    (F₁ : StrictHerglotzBlockFamily e₁ i)
    (F₂ : StrictHerglotzBlockFamily e₂ i) (z : ℂ) :
    Matrix (e₁ ⊕ e₂) (e₁ ⊕ e₂) ℂ :=
  Matrix.fromBlocks (F₁.A z) 0 0 (F₂.A z) -
    Matrix.fromRows (F₁.B z) (F₂.B z) *
      Ring.inverse (gluedInterfaceBlock F₁ F₂ z) *
        Matrix.fromCols (F₁.C z) (F₂.C z)

private theorem holomorphic_fromBlocks_diagonal
    {e₁ e₂ : Type*} [Fintype e₁] [Fintype e₂]
    [DecidableEq e₁] [DecidableEq e₂]
    (A₁ : ℂ → Matrix e₁ e₁ ℂ) (A₂ : ℂ → Matrix e₂ e₂ ℂ)
    (h₁ : DifferentiableOn ℂ A₁ strictUpperHalfPlane)
    (h₂ : DifferentiableOn ℂ A₂ strictUpperHalfPlane) :
    DifferentiableOn ℂ
      (fun z ↦ Matrix.fromBlocks (A₁ z) 0 0 (A₂ z))
      strictUpperHalfPlane := by
  let L : (Matrix e₁ e₁ ℂ × Matrix e₂ e₂ ℂ) →ₗ[ℂ]
      Matrix (e₁ ⊕ e₂) (e₁ ⊕ e₂) ℂ :=
    { toFun := fun P ↦ Matrix.fromBlocks P.1 0 0 P.2
      map_add' := by
        intro P R
        ext (p | p) (q | q) <;> simp
      map_smul' := by
        intro c P
        ext (p | p) (q | q) <;> simp }
  let Lc := LinearMap.toContinuousLinearMap L
  intro z hz
  exact Lc.differentiableAt.comp_differentiableWithinAt z
    ((h₁ z hz).prodMk (h₂ z hz))

private theorem holomorphic_fromRows
    {e₁ e₂ i : Type*} [Fintype e₁] [Fintype e₂] [Fintype i]
    [DecidableEq e₁] [DecidableEq e₂] [DecidableEq i]
    (B₁ : ℂ → Matrix e₁ i ℂ) (B₂ : ℂ → Matrix e₂ i ℂ)
    (h₁ : DifferentiableOn ℂ B₁ strictUpperHalfPlane)
    (h₂ : DifferentiableOn ℂ B₂ strictUpperHalfPlane) :
    DifferentiableOn ℂ (fun z ↦ Matrix.fromRows (B₁ z) (B₂ z))
      strictUpperHalfPlane := by
  let L : (Matrix e₁ i ℂ × Matrix e₂ i ℂ) →ₗ[ℂ]
      Matrix (e₁ ⊕ e₂) i ℂ :=
    { toFun := fun P ↦ Matrix.fromRows P.1 P.2
      map_add' := by
        intro P R
        ext (p | p) q <;> simp
      map_smul' := by
        intro c P
        ext (p | p) q <;> simp }
  let Lc := LinearMap.toContinuousLinearMap L
  intro z hz
  exact Lc.differentiableAt.comp_differentiableWithinAt z
    ((h₁ z hz).prodMk (h₂ z hz))

private theorem holomorphic_fromCols
    {e₁ e₂ i : Type*} [Fintype e₁] [Fintype e₂] [Fintype i]
    [DecidableEq e₁] [DecidableEq e₂] [DecidableEq i]
    (C₁ : ℂ → Matrix i e₁ ℂ) (C₂ : ℂ → Matrix i e₂ ℂ)
    (h₁ : DifferentiableOn ℂ C₁ strictUpperHalfPlane)
    (h₂ : DifferentiableOn ℂ C₂ strictUpperHalfPlane) :
    DifferentiableOn ℂ (fun z ↦ Matrix.fromCols (C₁ z) (C₂ z))
      strictUpperHalfPlane := by
  let L : (Matrix i e₁ ℂ × Matrix i e₂ ℂ) →ₗ[ℂ]
      Matrix i (e₁ ⊕ e₂) ℂ :=
    { toFun := fun P ↦ Matrix.fromCols P.1 P.2
      map_add' := by
        intro P R
        ext p (q | q) <;> simp
      map_smul' := by
        intro c P
        ext p (q | q) <;> simp }
  let Lc := LinearMap.toContinuousLinearMap L
  intro z hz
  exact Lc.differentiableAt.comp_differentiableWithinAt z
    ((h₁ z hz).prodMk (h₂ z hz))

private theorem holomorphic_matrix_mul
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (A : ℂ → Matrix m n ℂ) (B : ℂ → Matrix n p ℂ)
    (hA : DifferentiableOn ℂ A strictUpperHalfPlane)
    (hB : DifferentiableOn ℂ B strictUpperHalfPlane) :
    DifferentiableOn ℂ (fun z ↦ A z * B z) strictUpperHalfPlane := by
  let μ : Matrix m n ℂ →L[ℂ] Matrix n p ℂ →L[ℂ] Matrix m p ℂ :=
    (mulLinearMap ℂ :
      Matrix m n ℂ →ₗ[ℂ] Matrix n p ℂ →ₗ[ℂ] Matrix m p ℂ).toContinuousBilinearMap
  intro z hz
  simpa only [μ, LinearMap.toContinuousBilinearMap_apply,
    mulLinearMap_apply_apply] using
      (μ.hasFDerivWithinAt_of_bilinear
        (hA z hz).hasFDerivWithinAt
        (hB z hz).hasFDerivWithinAt).differentiableWithinAt

/-- The common interface block of two strict Herglotz families is invertible
throughout the upper half-plane. -/
theorem gluedInterfaceBlock_isUnit
    {e₁ e₂ i : Type*} [Fintype e₁] [Fintype e₂] [Fintype i]
    [DecidableEq e₁] [DecidableEq e₂] [DecidableEq i]
    (F₁ : StrictHerglotzBlockFamily e₁ i)
    (F₂ : StrictHerglotzBlockFamily e₂ i)
    {z : ℂ} (hz : z ∈ strictUpperHalfPlane) :
    IsUnit (gluedInterfaceBlock F₁ F₂ z) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact (herglotz_strict (F₁.A z) (F₁.B z) (F₁.C z) (F₁.D z)
    (F₂.A z) (F₂.B z) (F₂.C z) (F₂.D z)
    (F₁.strict z hz) (F₂.strict z hz)).2

/-- Conservative Schur gluing preserves holomorphy and strict matrix-Herglotz
positivity. -/
theorem conservative_herglotz_gluing
    {e₁ e₂ i : Type*} [Fintype e₁] [Fintype e₂] [Fintype i]
    [DecidableEq e₁] [DecidableEq e₂] [DecidableEq i]
    (F₁ : StrictHerglotzBlockFamily e₁ i)
    (F₂ : StrictHerglotzBlockFamily e₂ i) :
    MatrixHolomorphicOn (gluedHerglotzResponse F₁ F₂) strictUpperHalfPlane
    ∧ ∀ z ∈ strictUpperHalfPlane, ∀ x : e₁ ⊕ e₂ → ℂ, x ≠ 0 →
      0 < (dotProduct (star x) (gluedHerglotzResponse F₁ F₂ z *ᵥ x)).im := by
  constructor
  · have hD : DifferentiableOn ℂ (gluedInterfaceBlock F₁ F₂)
        strictUpperHalfPlane := F₁.holomorphic_D.add F₂.holomorphic_D
    have hDinv := hD.inverse fun z hz ↦ gluedInterfaceBlock_isUnit F₁ F₂ hz
    have hBD := holomorphic_matrix_mul
      (fun z ↦ Matrix.fromRows (F₁.B z) (F₂.B z))
      (fun z ↦ Ring.inverse (gluedInterfaceBlock F₁ F₂ z))
      (holomorphic_fromRows F₁.B F₂.B
        F₁.holomorphic_B F₂.holomorphic_B) hDinv
    have hBDC := holomorphic_matrix_mul
      (fun z ↦ Matrix.fromRows (F₁.B z) (F₂.B z) *
        Ring.inverse (gluedInterfaceBlock F₁ F₂ z))
      (fun z ↦ Matrix.fromCols (F₁.C z) (F₂.C z)) hBD
      (holomorphic_fromCols F₁.C F₂.C
        F₁.holomorphic_C F₂.holomorphic_C)
    change DifferentiableOn ℂ
      (fun z ↦ Matrix.fromRows (F₁.B z) (F₂.B z) *
        Ring.inverse (gluedInterfaceBlock F₁ F₂ z) *
          Matrix.fromCols (F₁.C z) (F₂.C z))
      strictUpperHalfPlane at hBDC
    have htotal := (holomorphic_fromBlocks_diagonal F₁.A F₂.A
      F₁.holomorphic_A F₂.holomorphic_A).sub hBDC
    intro a b
    let L : Matrix (e₁ ⊕ e₂) (e₁ ⊕ e₂) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun M ↦ M a b
        map_add' := by simp
        map_smul' := by simp }
    let Lc := LinearMap.toContinuousLinearMap L
    intro z hz
    exact Lc.differentiableAt.comp_differentiableWithinAt z (htotal z hz)
  · intro z hz x hx
    let x₁ : e₁ → ℂ := x ∘ Sum.inl
    let x₂ : e₂ → ℂ := x ∘ Sum.inr
    let v : i → ℂ := F₁.C z *ᵥ x₁ + F₂.C z *ᵥ x₂
    let u : i → ℂ := -((gluedInterfaceBlock F₁ F₂ z)⁻¹ *ᵥ v)
    have hunit := gluedInterfaceBlock_isUnit F₁ F₂ hz
    letI := hunit.invertible
    have hsolve : gluedInterfaceBlock F₁ F₂ z *ᵥ u + v = 0 := by
      dsimp [u]
      rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec,
        Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
      simp
    have hxsplit : x₁ ≠ 0 ∨ x₂ ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext p
      rcases p with p | p
      · exact congrFun h.1 p
      · exact congrFun h.2 p
    have hstrict := (herglotz_strict
      (F₁.A z) (F₁.B z) (F₁.C z) (F₁.D z)
      (F₂.A z) (F₂.B z) (F₂.C z) (F₂.D z)
      (F₁.strict z hz) (F₂.strict z hz)).1 x₁ x₂ u
        (by simpa [gluedInterfaceBlock, v] using hsolve) hxsplit
    convert hstrict using 1
    simp only [gluedHerglotzResponse, Matrix.sub_mulVec,
      Matrix.fromBlocks_mulVec, x₁, x₂, v, u]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.fromCols_mulVec, Matrix.fromRows_mulVec]
    simp only [Matrix.zero_mulVec, add_zero, zero_add, Matrix.mulVec_neg]
    rw [dotProduct, Fintype.sum_sum_type]
    simp only [Pi.star_apply, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply]
    simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
    simp only [Pi.add_apply, Pi.neg_apply, mul_add, mul_neg,
      Finset.sum_add_distrib, Finset.sum_neg_distrib]
    simp only [sub_eq_add_neg,
      Matrix.nonsing_inv_eq_ringInverse]
    simp only [Pi.star_apply, Function.comp_apply]

end NCG
