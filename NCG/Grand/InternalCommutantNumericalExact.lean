/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.InternalAssemblyExact
import NCG.Grand.InternalCommutantSeedExact
import NCG.Grand.WeakResetGenerationExact

/-!
# Numerical and word-filtration certificates for the active internal seed

This file supplies the three finite clauses accompanying
`thm:SM-active-internal-commutant`: the normalized weak-reset commutator norm,
the exact two-block colour-router gap, and the relative colour word-dimension
profile `5 → 7 → 9 → 9`.
-/

open Finset Matrix Complex
open scoped Kronecker

namespace NCG
namespace InternalCommutantNumerical

/-! ## The operation-native weak reset -/

/-- Canonical unit tail line. -/
noncomputable def weakTail : Fin 2 → ℂ := ![1, 0]

/-- Canonical unit head line with overlap `1/3` with `weakTail`. -/
noncomputable def weakHead : Fin 2 → ℂ :=
  ![(1 : ℂ) / 3, ((2 * Real.sqrt 2 / 3 : ℝ) : ℂ)]

noncomputable def weakProjection (v : Fin 2 → ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := Matrix.vecMulVec v (star v)

theorem weak_reset_overlap :
    ‖∑ i, star (weakTail i) * weakHead i‖ = 1 / 3 := by
  simp [weakTail, weakHead, Fin.sum_univ_two]

theorem weakTail_unit : ∑ i, Complex.normSq (weakTail i) = 1 := by
  simp [weakTail, Fin.sum_univ_two]

theorem weakHead_unit : ∑ i, Complex.normSq (weakHead i) = 1 := by
  simp [weakHead, Fin.sum_univ_two, Complex.normSq_apply]
  have hs : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

/-- The weak-reset projection commutator. -/
noncomputable def weakResetCommutator : Matrix (Fin 2) (Fin 2) ℂ :=
  weakProjection weakTail * weakProjection weakHead -
    weakProjection weakHead * weakProjection weakTail

/-- Squared Hilbert--Schmidt norm in trace convention. -/
noncomputable def hsNormSq {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ℝ := (Matrix.trace (Aᴴ * A)).re

theorem weakResetCommutator_eq :
    weakResetCommutator =
      !![0, (((2 * Real.sqrt 2 / 9 : ℝ) : ℂ));
         -(((2 * Real.sqrt 2 / 9 : ℝ) : ℂ)), 0] := by
  unfold weakResetCommutator weakProjection weakTail weakHead
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.vecMulVec_apply, Pi.star_apply]
  fin_cases i <;> fin_cases j
  all_goals simp [map_ofNat]
  all_goals ring

theorem weakResetCommutator_hsNormSq :
    hsNormSq weakResetCommutator = 16 / 81 := by
  rw [weakResetCommutator_eq]
  simp [hsNormSq, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply]
  norm_num [map_ofNat]
  have hs : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [hs]

/-- Lift the weak reset over the three-dimensional standard isotypic factor. -/
noncomputable def liftedWeakResetCommutator :
    Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ :=
  (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ weakResetCommutator

theorem liftedWeakResetCommutator_hsNormSq :
    hsNormSq liftedWeakResetCommutator = 16 / 27 := by
  change (Matrix.trace
    (((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ weakResetCommutator)ᴴ *
      (1 ⊗ₖ weakResetCommutator))).re = 16 / 27
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.trace_kronecker]
  rw [show Matrix.trace (1 : Matrix (Fin 3) (Fin 3) ℂ) = 3 by
    simp [Matrix.trace_one]]
  change (3 * Matrix.trace (weakResetCommutatorᴴ * weakResetCommutator)).re = _
  have h := weakResetCommutator_hsNormSq
  change (Matrix.trace
    (weakResetCommutatorᴴ * weakResetCommutator)).re = 16 / 81 at h
  rw [Complex.mul_re]
  norm_num
  linarith

/-! ## The two-block colour router -/

/-- Weighted two-vertex graph Laplacian of the type/private router. -/
def twoBlockLaplacian (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ω, -ω; -ω, ω]

theorem twoBlockLaplacian_constant_kernel (ω : ℝ) :
    twoBlockLaplacian ω *ᵥ ![1, 1] = 0 := by
  ext i
  fin_cases i <;>
    simp [twoBlockLaplacian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Every mean-zero two-block contrast has eigenvalue `2ω`; this is the exact
router gap asserted in the manuscript. -/
theorem twoBlockLaplacian_contrast_gap (ω a : ℝ) :
    twoBlockLaplacian ω *ᵥ ![a, -a] = (2 * ω) • ![a, -a] := by
  ext i
  fin_cases i <;>
    simp [twoBlockLaplacian, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

/-! ## Relative colour word dimensions -/

abbrev ColourMatrix := Matrix (Fin 3) (Fin 3) ℂ

/-- The full matrix-unit family. -/
def colourMatrixUnit (ij : Fin 3 × Fin 3) : ColourMatrix :=
  Matrix.single ij.1 ij.2 1

theorem colourMatrixUnit_linearIndependent :
    LinearIndependent ℂ colourMatrixUnit := by
  have h := (Matrix.stdBasis ℂ (Fin 3) (Fin 3)).linearIndependent
  rw [show colourMatrixUnit = Matrix.stdBasis ℂ (Fin 3) (Fin 3) from by
    funext ij
    exact (Matrix.stdBasis_eq_single ℂ ij.1 ij.2).symm]
  exact h

/-- Five block-diagonal units: the type scalar plus the private `M₂`. -/
def colourWordIndex0 : Fin 5 → Fin 3 × Fin 3 :=
  ![(0, 0), (1, 1), (1, 2), (2, 1), (2, 2)]

/-- Degree one adds one oriented bridge and its adjoint. -/
def colourWordIndex1 : Fin 7 → Fin 3 × Fin 3 :=
  ![(0, 0), (1, 1), (1, 2), (2, 1), (2, 2), (0, 1), (1, 0)]

def colourWords0 (i : Fin 5) : ColourMatrix :=
  colourMatrixUnit (colourWordIndex0 i)

def colourWords1 (i : Fin 7) : ColourMatrix :=
  colourMatrixUnit (colourWordIndex1 i)

def colourWordSpace0 : Submodule ℂ ColourMatrix :=
  Submodule.span ℂ (Set.range colourWords0)

def colourWordSpace1 : Submodule ℂ ColourMatrix :=
  Submodule.span ℂ (Set.range colourWords1)

def colourWordSpace2 : Submodule ℂ ColourMatrix :=
  Submodule.span ℂ (Set.range colourMatrixUnit)

def colourWordSpace3 : Submodule ℂ ColourMatrix := colourWordSpace2

theorem colourWordIndex0_injective : Function.Injective colourWordIndex0 := by
  decide

theorem colourWordIndex1_injective : Function.Injective colourWordIndex1 := by
  decide

theorem colourWords0_linearIndependent : LinearIndependent ℂ colourWords0 := by
  exact LinearIndependent.comp colourMatrixUnit_linearIndependent
    colourWordIndex0 colourWordIndex0_injective

theorem colourWords1_linearIndependent : LinearIndependent ℂ colourWords1 := by
  exact LinearIndependent.comp colourMatrixUnit_linearIndependent
    colourWordIndex1 colourWordIndex1_injective

theorem colourWordSpace0_finrank : Module.finrank ℂ colourWordSpace0 = 5 := by
  rw [colourWordSpace0, finrank_span_eq_card colourWords0_linearIndependent]
  simp

theorem colourWordSpace1_finrank : Module.finrank ℂ colourWordSpace1 = 7 := by
  rw [colourWordSpace1, finrank_span_eq_card colourWords1_linearIndependent]
  simp

theorem colourWordSpace2_finrank : Module.finrank ℂ colourWordSpace2 = 9 := by
  rw [colourWordSpace2, finrank_span_eq_card colourMatrixUnit_linearIndependent]
  simp

theorem colourWordSpace3_finrank : Module.finrank ℂ colourWordSpace3 = 9 := by
  exact colourWordSpace2_finrank

/-- Canonical oriented colour bridge. -/
def colourBridge : ColourMatrix := Matrix.single 0 1 1

theorem colourBridge_degree_one :
    colourWords1 5 = colourBridge ∧ colourWords1 6 = colourBridgeᴴ := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [colourWords1, colourWordIndex1, colourMatrixUnit, colourBridge,
      Matrix.single_apply, Matrix.conjTranspose_apply]

/-- The two missing rectangular units occur at the next relative word degree. -/
theorem colourBridge_degree_two_units :
    colourBridge * Matrix.single 1 2 1 = Matrix.single 0 2 1 ∧
    Matrix.single 2 1 1 * colourBridgeᴴ = Matrix.single 2 0 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [colourBridge, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.single_apply, Matrix.conjTranspose_apply]

/-- Exact relative word profile `5 → 7 → 9 → 9`. -/
theorem relative_colour_word_dimension_profile :
    Module.finrank ℂ colourWordSpace0 = 5 ∧
    Module.finrank ℂ colourWordSpace1 = 7 ∧
    Module.finrank ℂ colourWordSpace2 = 9 ∧
    Module.finrank ℂ colourWordSpace3 = 9 :=
  ⟨colourWordSpace0_finrank, colourWordSpace1_finrank,
    colourWordSpace2_finrank, colourWordSpace3_finrank⟩

/-- Numerical clause bundle for `thm:SM-active-internal-commutant`. -/
theorem internal_commutant_numerical_exact :
    ‖∑ i, star (weakTail i) * weakHead i‖ = 1 / 3 ∧
    hsNormSq liftedWeakResetCommutator = 16 / 27 ∧
    (∀ ω a : ℝ,
      twoBlockLaplacian ω *ᵥ ![a, -a] = (2 * ω) • ![a, -a]) ∧
    Module.finrank ℂ colourWordSpace0 = 5 ∧
    Module.finrank ℂ colourWordSpace1 = 7 ∧
    Module.finrank ℂ colourWordSpace2 = 9 ∧
    Module.finrank ℂ colourWordSpace3 = 9 := by
  exact ⟨weak_reset_overlap, liftedWeakResetCommutator_hsNormSq,
    twoBlockLaplacian_contrast_gap, colourWordSpace0_finrank,
    colourWordSpace1_finrank, colourWordSpace2_finrank,
    colourWordSpace3_finrank⟩

/-- Full exact bundle for the active internal-commutant theorem: arbitrary
positive colour corners generate the M3 corner, the supported seven-sector
assembly is exactly M3 plus M2 plus two scalar blocks, two independent
nonorthogonal weak lines generate M2, and all numerical clauses hold. -/
theorem source_minimal_internal_seed_exact :
    (∀ u : Matrix (Fin 3) (Fin 3) ℂ,
      Algebra.adjoin ℂ (InternalSeed.gens u) = ⊤ ↔
        0 < InternalSeed.omegaCol u) ∧
    (∀ u : Matrix (Fin 7) (Fin 7) ℂ,
      InternalAssembly.ColourSupported u →
      (Algebra.adjoin ℂ (InternalAssembly.gens7 u) =
          InternalAssembly.blockAlgebra ↔
        0 < InternalAssembly.omega7 u)) ∧
    (∀ t h : Fin 2 → ℂ,
      t 0 * h 1 - t 1 * h 0 ≠ 0 →
      (∑ m, star (t m) * h m) ≠ 0 →
      Algebra.adjoin ℂ
        {Matrix.vecMulVec t (star t), Matrix.vecMulVec h (star h)} = ⊤) ∧
    ‖∑ i, star (weakTail i) * weakHead i‖ = 1 / 3 ∧
    hsNormSq liftedWeakResetCommutator = 16 / 27 ∧
    (∀ ω a : ℝ,
      twoBlockLaplacian ω *ᵥ ![a, -a] = (2 * ω) • ![a, -a]) ∧
    Module.finrank ℂ colourWordSpace0 = 5 ∧
    Module.finrank ℂ colourWordSpace1 = 7 ∧
    Module.finrank ℂ colourWordSpace2 = 9 ∧
    Module.finrank ℂ colourWordSpace3 = 9 := by
  exact ⟨InternalSeed.internal_seed_dichotomy,
    InternalAssembly.assembled_dichotomy, WeakReset.two_lines_generate,
    weak_reset_overlap, liftedWeakResetCommutator_hsNormSq,
    twoBlockLaplacian_contrast_gap, colourWordSpace0_finrank,
    colourWordSpace1_finrank, colourWordSpace2_finrank,
    colourWordSpace3_finrank⟩

end InternalCommutantNumerical
end NCG
