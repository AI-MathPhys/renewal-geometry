/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.LinearAlgebra.Matrix.Action
import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Modules over a full complex matrix algebra

This module gives an explicit matrix-linear classification of modules over
`Matrix ι ι ℂ`.  After choosing an index `i₀`, the corner fixed by the matrix
unit `E i₀ i₀` is the multiplicity space, and every module vector decomposes
uniquely into one copy of that space for each index in `ι`.

The final equivalence `fullMatrixModuleLinearEquiv` is linear over the full
matrix algebra, not merely over `ℂ`.  It is the represented simple-block layer
needed in finite-dimensional commutant decompositions.
-/

noncomputable section

open scoped BigOperators
open scoped Matrix.Module
open Matrix

namespace NCG
namespace FullMatrixAlgebraModuleDecomposition

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard matrix unit `Eᵢⱼ`. -/
def matrixUnit (i j : ι) : Matrix ι ι ℂ := Matrix.single i j 1

@[simp] theorem matrixUnit_mul_same (i j k : ι) :
    matrixUnit i j * matrixUnit j k = matrixUnit i k := by
  simp [matrixUnit]

theorem matrixUnit_mul_of_ne (i j k l : ι) (h : j ≠ k) :
    matrixUnit i j * matrixUnit k l = 0 := by
  simpa only [matrixUnit] using
    (Matrix.single_mul_single_of_ne (1 : ℂ) i j k h (1 : ℂ) :
      Matrix.single i j (1 : ℂ) * Matrix.single k l (1 : ℂ) =
        (0 : Matrix ι ι ℂ))

theorem sum_diagonal_matrixUnit :
    ∑ i : ι, matrixUnit i i = 1 := by
  simpa [matrixUnit] using (Matrix.sum_single_one (α := ℂ) (m := ι))

theorem matrixUnit_mul_eq_sum (i₀ i : ι) (A : Matrix ι ι ℂ) :
    matrixUnit i₀ i * A = ∑ j, A i j • matrixUnit i₀ j := by
  ext a b
  by_cases ha : a = i₀
  · subst a
    simp [matrixUnit, Matrix.mul_apply, Matrix.sum_apply, Matrix.single]
  · have hia : i₀ ≠ a := Ne.symm ha
    simp [matrixUnit, Matrix.mul_apply, Matrix.sum_apply, Matrix.single, hia]

variable {M : Type*}
  [AddCommGroup M] [Module ℂ M]
  [Module (Matrix ι ι ℂ) M]
  [SMulCommClass ℂ (Matrix ι ι ℂ) M]

/-- The multiplicity space cut out by the diagonal matrix unit at `i₀`. -/
def cornerSubspace (i₀ : ι) : Submodule ℂ M where
  carrier := {x | matrixUnit i₀ i₀ • x = x}
  zero_mem' := by simp
  add_mem' hx hy := by
    change matrixUnit i₀ i₀ • (_ + _) = _ + _
    change matrixUnit i₀ i₀ • _ = _ at hx hy
    rw [smul_add, hx, hy]
  smul_mem' c x hx := by
    change matrixUnit i₀ i₀ • (c • x) = c • x
    change matrixUnit i₀ i₀ • x = x at hx
    rw [← smul_comm c (matrixUnit i₀ i₀) x, hx]

/-- Extract all matrix-unit components of a module vector. -/
def decomposeVector (i₀ : ι) (x : M) (i : ι) : cornerSubspace (M := M) i₀ :=
  ⟨matrixUnit i₀ i • x, by
    change matrixUnit i₀ i₀ • (matrixUnit i₀ i • x) =
      matrixUnit i₀ i • x
    rw [← mul_smul, matrixUnit_mul_same]⟩

def decomposeLinear (i₀ : ι) :
    M →ₗ[ℂ] (ι → cornerSubspace (M := M) i₀) where
  toFun := decomposeVector i₀
  map_add' x y := by
    ext i
    simp [decomposeVector, smul_add]
  map_smul' c x := by
    ext i
    change matrixUnit i₀ i • (c • x) = c • (matrixUnit i₀ i • x)
    exact (smul_comm c (matrixUnit i₀ i) x).symm

def assembleLinear (i₀ : ι) :
    (ι → cornerSubspace (M := M) i₀) →ₗ[ℂ] M where
  toFun v := ∑ i, matrixUnit i i₀ • (v i).1
  map_add' v w := by
    simp only [Pi.add_apply, Submodule.coe_add, smul_add,
      Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, RingHom.id_apply, Submodule.coe_smul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (smul_comm c (matrixUnit i i₀) (v i).1).symm

theorem decompose_assemble (i₀ : ι)
    (v : ι → cornerSubspace (M := M) i₀) :
    decomposeLinear i₀ (assembleLinear i₀ v) = v := by
  funext k
  apply Subtype.ext
  change matrixUnit i₀ k • (∑ i, matrixUnit i i₀ • (v i).1) = (v k).1
  rw [Finset.smul_sum, Finset.sum_eq_single k]
  · rw [← mul_smul, matrixUnit_mul_same]
    exact (v k).2
  · intro i hi hik
    rw [← mul_smul, matrixUnit_mul_of_ne i₀ k i i₀ hik.symm, zero_smul]
  · simp

theorem assemble_decompose (i₀ : ι) (x : M) :
    assembleLinear i₀ (decomposeLinear i₀ x) = x := by
  change (∑ i, matrixUnit i i₀ • (matrixUnit i₀ i • x)) = x
  simp_rw [← mul_smul, matrixUnit_mul_same]
  rw [← Finset.sum_smul, sum_diagonal_matrixUnit, one_smul]

/-- The explicit complex-linear decomposition into defining-representation copies. -/
def fullMatrixModuleEquiv (i₀ : ι) :
    (ι → cornerSubspace (M := M) i₀) ≃ₗ[ℂ] M where
  toLinearMap := assembleLinear i₀
  invFun := decomposeLinear i₀
  left_inv := decompose_assemble i₀
  right_inv := assemble_decompose i₀

variable [IsScalarTower ℂ (Matrix ι ι ℂ) M]

theorem decompose_smul (i₀ : ι) (A : Matrix ι ι ℂ) (x : M) :
    decomposeVector i₀ (A • x) = A • decomposeVector i₀ x := by
  funext i
  apply Subtype.ext
  simp only [Matrix.Module.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul, decomposeVector]
  change matrixUnit i₀ i • (A • x) =
    ∑ j, A i j • (matrixUnit i₀ j • x)
  rw [← mul_smul, matrixUnit_mul_eq_sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_assoc]

def decomposeMatrixLinear (i₀ : ι) :
    M →ₗ[Matrix ι ι ℂ] (ι → cornerSubspace (M := M) i₀) where
  toFun := decomposeVector i₀
  map_add' x y := by
    ext i
    simp [decomposeVector, smul_add]
  map_smul' A x := decompose_smul i₀ A x

theorem decomposeMatrixLinear_bijective (i₀ : ι) :
    Function.Bijective (decomposeMatrixLinear (M := M) i₀) := by
  constructor
  · intro x y h
    have h' := congrArg (assembleLinear (M := M) i₀) h
    change assembleLinear i₀ (decomposeLinear i₀ x) =
      assembleLinear i₀ (decomposeLinear i₀ y) at h'
    rw [assemble_decompose, assemble_decompose] at h'
    exact h'
  · intro v
    refine ⟨assembleLinear i₀ v, ?_⟩
    change decomposeLinear i₀ (assembleLinear i₀ v) = v
    exact decompose_assemble i₀ v

/-- Every module over a full matrix algebra is a family of copies of its
corner multiplicity space, equivariantly for the full matrix action. -/
def fullMatrixModuleLinearEquiv (i₀ : ι) :
    (ι → cornerSubspace (M := M) i₀) ≃ₗ[Matrix ι ι ℂ] M :=
  (LinearEquiv.ofBijective (decomposeMatrixLinear i₀)
    (decomposeMatrixLinear_bijective i₀)).symm

section Unitary

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [Module (Matrix ι ι ℂ) H]
  [SMulCommClass ℂ (Matrix ι ι ℂ) H]

omit [Fintype ι] in
@[simp] theorem matrixUnit_conjTranspose (i j : ι) :
    (matrixUnit i j)ᴴ = matrixUnit j i := by
  ext a b
  simp [matrixUnit, Matrix.conjTranspose_apply, Matrix.single, and_comm]

/-- The matrix-unit assembly preserves inner products whenever the matrix
action is compatible with conjugate transpose. -/
theorem inner_assemble (i₀ : ι)
    (hstar : ∀ (A : Matrix ι ι ℂ) (x y : H),
      inner ℂ (A • x) y = inner ℂ x (Matrix.conjTranspose A • y))
    (v w : PiLp 2 (fun _ : ι => cornerSubspace (M := H) i₀)) :
    inner ℂ (∑ i, matrixUnit i i₀ • (v i).1)
        (∑ j, matrixUnit j i₀ • (w j).1) =
      ∑ i, inner ℂ (v i).1 (w i).1 := by
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum]
  rw [Finset.sum_eq_single i]
  · rw [hstar, matrixUnit_conjTranspose, ← mul_smul,
      matrixUnit_mul_same]
    exact congrArg (fun z : H => inner ℂ (v i).1 z) (w i).2
  · intro j hj hji
    rw [hstar, matrixUnit_conjTranspose, ← mul_smul,
      matrixUnit_mul_of_ne i₀ i j i₀ hji.symm, zero_smul]
    simp
  · simp

/-- Matrix-unit assembly as a complex-linear isometry. -/
def assembleIsometry (i₀ : ι)
    (hstar : ∀ (A : Matrix ι ι ℂ) (x y : H),
      inner ℂ (A • x) y = inner ℂ x (Matrix.conjTranspose A • y)) :
    PiLp 2 (fun _ : ι => cornerSubspace (M := H) i₀) →ₗᵢ[ℂ] H where
  toFun v := ∑ i, matrixUnit i i₀ • (v i).1
  map_add' v w := by
    simp only [PiLp.add_apply, Submodule.coe_add, smul_add,
      Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [PiLp.smul_apply, RingHom.id_apply, Submodule.coe_smul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (smul_comm c (matrixUnit i i₀) (v i).1).symm
  norm_map' v := by
    change ‖∑ i, matrixUnit i i₀ • (v i).1‖ = ‖v‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    calc
      ‖∑ i, matrixUnit i i₀ • (v i).1‖ ^ 2 =
          RCLike.re (inner ℂ (∑ i, matrixUnit i i₀ • (v i).1)
            (∑ i, matrixUnit i i₀ • (v i).1)) := norm_sq_eq_re_inner _
      _ = RCLike.re (inner ℂ v v) := by
        rw [PiLp.inner_apply, inner_assemble i₀ hstar]
        rfl
      _ = ‖v‖ ^ 2 := (norm_sq_eq_re_inner _).symm

theorem assembleIsometry_surjective (i₀ : ι)
    (hstar : ∀ (A : Matrix ι ι ℂ) (x y : H),
      inner ℂ (A • x) y = inner ℂ x (Matrix.conjTranspose A • y)) :
    Function.Surjective (assembleIsometry i₀ hstar) := by
  intro x
  refine ⟨WithLp.toLp 2 (decomposeVector i₀ x), ?_⟩
  change assembleLinear i₀ (decomposeLinear i₀ x) = x
  exact assemble_decompose i₀ x

/-- Every star-compatible representation of a full complex matrix algebra is
unitarily a family of copies of the defining representation. The multiplicity
space is the range of one diagonal matrix unit. -/
def fullMatrixModuleUnitaryEquiv (i₀ : ι)
    (hstar : ∀ (A : Matrix ι ι ℂ) (x y : H),
      inner ℂ (A • x) y = inner ℂ x (Matrix.conjTranspose A • y)) :
    PiLp 2 (fun _ : ι => cornerSubspace (M := H) i₀) ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (assembleIsometry i₀ hstar)
    (assembleIsometry_surjective i₀ hstar)

end Unitary

end FullMatrixAlgebraModuleDecomposition
end NCG
