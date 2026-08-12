/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.AtomicResetOrderedCone
import NCG.Upstream.PrimitiveWeight
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.MetricSpace.Algebra

/-!
# The ordered cone of finite Hermitian matrices

Positive semidefinite matrices form a generating cone in the real vector space
of Hermitian matrices.  The trace is a strictly positive normalization
functional on that cone.  A positive complex-linear matrix map therefore has
a canonical real-linear Hermitian transfer operator to which the abstract
atomic-reset theorem applies.
-/

open Matrix
open scoped ComplexOrder MatrixOrder ComplexStarModule Matrix.Norms.Frobenius

namespace NCG

open Upstream.PrimitiveWeight

/-- The real vector space of finite Hermitian complex matrices. -/
abbrev HermitianMatrix (n : ℕ) :=
  selfAdjoint (Matrix (Fin n) (Fin n) ℂ)

/-- Inclusion of Hermitian matrices into all matrices, as a real-linear map. -/
def hermitianMatrixRealInclusion (n : ℕ) :
    HermitianMatrix n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := X.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Frobenius norm on Hermitian matrices, exported independently of the
scoped ambient matrix-norm instance. -/
noncomputable instance hermitianMatrixNorm (n : ℕ) :
    Norm (HermitianMatrix n) where
  norm X := ‖X.val‖

/-- Joint continuity of real scalar multiplication, inherited from the
ambient complex matrix space. -/
noncomputable instance hermitianMatrixContinuousSMul (n : ℕ) :
    ContinuousSMul ℝ (HermitianMatrix n) where
  continuous_smul := Continuous.subtype_mk (by
    change Continuous (fun p : ℝ × HermitianMatrix n =>
      (p.1 : ℂ) • p.2.val)
    fun_prop) _

/-- The Hermitian matrix space is finite-dimensional over `ℝ`. -/
noncomputable instance hermitianMatrixFiniteDimensional (n : ℕ) :
    FiniteDimensional ℝ (HermitianMatrix n) :=
  FiniteDimensional.of_injective (hermitianMatrixRealInclusion n)
    Subtype.val_injective

/-- The positive-semidefinite cone generates the Hermitian matrix space by
the spectral positive/negative-part decomposition. -/
noncomputable def hermitianPsdGeneratingCone (n : ℕ) :
    GeneratingCone (HermitianMatrix n) where
  carrier := {X | (X : Matrix (Fin n) (Fin n) ℂ).PosSemidef}
  zero_mem := Matrix.PosSemidef.zero
  add_mem := fun hX hY => hX.add hY
  smul_mem := by
    intro a ha X hX
    exact hX.smul ha
  generating := by
    intro X
    let P : HermitianMatrix n :=
      ⟨posPart X.prop, (posPart_posSemidef X.prop).1⟩
    let Q : HermitianMatrix n :=
      ⟨negPart X.prop, (negPart_posSemidef X.prop).1⟩
    refine ⟨P, posPart_posSemidef X.prop, Q,
      negPart_posSemidef X.prop, ?_⟩
    apply Subtype.ext
    exact (posPart_sub_negPart X.prop).symm

/-- Real trace on Hermitian matrices. -/
def hermitianTraceLinear (n : ℕ) : HermitianMatrix n →ₗ[ℝ] ℝ where
  toFun X := (X.val.trace).re
  map_add' := by
    intro X Y
    simp
  map_smul' := by
    intro a X
    simp

/-- The trace is strictly positive on every nonzero positive-semidefinite
Hermitian matrix. -/
noncomputable def hermitianTraceStrictFunctional (n : ℕ) :
    StrictConeFunctional (hermitianPsdGeneratingCone n) where
  toLinearMap := hermitianTraceLinear n
  nonneg := by
    intro X hX
    exact (Complex.nonneg_iff.mp hX.trace_nonneg).1
  pos := by
    intro X hX hX0
    have htrnonneg := hX.trace_nonneg
    have hre : 0 ≤ X.val.trace.re :=
      (Complex.nonneg_iff.mp htrnonneg).1
    have him : X.val.trace.im = 0 :=
      (Complex.nonneg_iff.mp htrnonneg).2.symm
    have htr0 : X.val.trace ≠ 0 := by
      intro hz
      apply hX0
      apply Subtype.ext
      exact hX.trace_eq_zero_iff.mp hz
    have hre0 : X.val.trace.re ≠ 0 := by
      intro hz
      apply htr0
      apply Complex.ext
      · simpa using hz
      · simpa using him
    exact lt_of_le_of_ne hre (Ne.symm hre0)

/-- A positive complex-linear matrix map sends every Hermitian input to a
Hermitian output. -/
theorem positiveMatrixMap_isHermitian {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hpos : ∀ X, X.PosSemidef → (R X).PosSemidef)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian) :
    (R X).IsHermitian := by
  have hP := hpos (posPart hX) (posPart_posSemidef hX)
  have hQ := hpos (negPart hX) (negPart_posSemidef hX)
  have hdecomp : R X = R (posPart hX) - R (negPart hX) := by
    rw [← map_sub, Upstream.PrimitiveWeight.posPart_sub_negPart]
  rw [hdecomp]
  exact hP.1.sub hQ.1

/-- The real-linear transfer of a positive matrix map on Hermitian matrices. -/
noncomputable def hermitianTransfer {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hpos : ∀ X, X.PosSemidef → (R X).PosSemidef) :
    HermitianMatrix n →ₗ[ℝ] HermitianMatrix m where
  toFun X := ⟨R X.val, positiveMatrixMap_isHermitian R hpos X.val X.prop⟩
  map_add' := by
    intro X Y
    apply Subtype.ext
    simp
  map_smul' := by
    intro a X
    apply Subtype.ext
    simp

theorem hermitianTransfer_apply {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hpos : ∀ X, X.PosSemidef → (R X).PosSemidef)
    (X : HermitianMatrix n) :
    (hermitianTransfer R hpos X).val = R X.val :=
  rfl

/-- Positivity of the Hermitian transfer between the two PSD cones. -/
theorem hermitianTransfer_conePositive {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hpos : ∀ X, X.PosSemidef → (R X).PosSemidef) :
    ConePositive (hermitianPsdGeneratingCone n)
      (hermitianPsdGeneratingCone m) (hermitianTransfer R hpos) := by
  intro X hX
  exact hpos X.val hX

/-- A nonzero positive complex-linear map has a nonzero Hermitian transfer,
because Hermitian matrices complex-linearly span the matrix algebra. -/
theorem hermitianTransfer_ne_zero_of_ne_zero {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hpos : ∀ X, X.PosSemidef → (R X).PosSemidef)
    (hR : R ≠ 0) : hermitianTransfer R hpos ≠ 0 := by
  intro hT
  apply hR
  apply LinearMap.ext
  intro X
  let A : HermitianMatrix n := ℜ X
  let B : HermitianMatrix n := ℑ X
  have hA0 : R A.val = 0 := by
    have h := LinearMap.congr_fun hT A
    exact congrArg Subtype.val h
  have hB0 : R B.val = 0 := by
    have h := LinearMap.congr_fun hT B
    exact congrArg Subtype.val h
  calc
    R X = R (A.val + Complex.I • B.val) := by
      congr 1
      exact (realPart_add_I_smul_imaginaryPart X).symm
    _ = R A.val + Complex.I • R B.val := by rw [map_add, map_smul]
    _ = 0 := by rw [hA0, hB0]; simp

end NCG
