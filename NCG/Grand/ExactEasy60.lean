/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.ArDerivedPacket
import NCG.Grand.RecordGeneration
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.AlmostPrime

/-!
# Exact EASY 60: concrete arithmetic derived histories

The generic diagonal calculus and von Mangoldt column were already proved in
`ArDerivedPacket`.  This file instantiates that calculus at the affine,
Mellin--heat, prime-depth, Liouville, and Moebius weights, and records that all
such finite matrices lie in the full record history algebra.
-/

open Matrix
open scoped ArithmeticFunction.Omega

namespace NCG

/-- Affine endpoint weight `exp(2 pi i n theta)`. -/
noncomputable def affineWeight (θ : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ))

/-- Mellin--heat endpoint weight
`n^(-sigma-i tau) exp(-t(log n)^2)`. -/
noncomputable def mellinHeatWeight (σ τ t : ℝ) (n : ℕ) : ℂ :=
  Complex.cpow (n : ℂ) (-(σ : ℂ) - Complex.I * (τ : ℂ))
    * Complex.exp (-(t : ℂ) * (Real.log n : ℂ) ^ 2)

noncomputable def affineHistory (X : ℕ) (θ : ℝ) :
    Matrix (Fin X) (Fin X) ℂ := diagFn X (affineWeight θ)

noncomputable def mellinHeatHistory (X : ℕ) (σ τ t : ℝ) :
    Matrix (Fin X) (Fin X) ℂ := diagFn X (mellinHeatWeight σ τ t)

/-- The spectral projection onto factor depth one. -/
def primeDepthProjection (X : ℕ) : Matrix (Fin X) (Fin X) ℂ :=
  diagFn X (fun n => if Ω n = 1 then 1 else 0)

/-- The diagonal prime indicator. -/
def primeProjection (X : ℕ) : Matrix (Fin X) (Fin X) ℂ :=
  diagFn X (fun n => if n.Prime then 1 else 0)

/-- Factor-parity diagonal `(-1)^Omega`. -/
def factorParityHistory (X : ℕ) : Matrix (Fin X) (Fin X) ℂ :=
  diagFn X (fun n => (((-1 : ℤ) ^ Ω n : ℤ) : ℂ))

/-- The Liouville diagonal. -/
def liouvilleHistory (X : ℕ) : Matrix (Fin X) (Fin X) ℂ :=
  diagFn X (fun n => ((ArithmeticFunction.liouville n : ℤ) : ℂ))

/-- The squarefree spectral projection. -/
def squarefreeProjection (X : ℕ) : Matrix (Fin X) (Fin X) ℂ :=
  diagFn X (fun n => if Squarefree n then 1 else 0)

/-- The Moebius diagonal. -/
def moebiusHistory (X : ℕ) : Matrix (Fin X) (Fin X) ℂ :=
  diagFn X (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))

/-- Every diagonal history acts by its defining endpoint weight. -/
theorem diagFn_mulVec_single {X : ℕ} (f : ℕ → ℂ) (i : Fin X) :
    diagFn X f *ᵥ Pi.single i 1 = f ((i : ℕ) + 1) • Pi.single i 1 := by
  funext j
  simp only [diagFn, Matrix.mulVec, dotProduct, Matrix.diagonal_apply,
    Pi.single_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single i]
  · by_cases hji : j = i
    · subst hji
      simp
    · simp [hji]
  · intro k _ hki
    simp [hki]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem affineHistory_action {X : ℕ} (θ : ℝ) (i : Fin X) :
    affineHistory X θ *ᵥ Pi.single i 1
      = affineWeight θ ((i : ℕ) + 1) • Pi.single i 1 := by
  exact diagFn_mulVec_single _ _

theorem mellinHeatHistory_action {X : ℕ} (σ τ t : ℝ) (i : Fin X) :
    mellinHeatHistory X σ τ t *ᵥ Pi.single i 1
      = mellinHeatWeight σ τ t ((i : ℕ) + 1) • Pi.single i 1 := by
  exact diagFn_mulVec_single _ _

/-- Factor depth one is exactly primality. -/
theorem primeProjection_eq_depth_one (X : ℕ) :
    primeProjection X = primeDepthProjection X := by
  ext i j
  simp only [primeProjection, primeDepthProjection, diagFn,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp [ArithmeticFunction.cardFactors_eq_one_iff_prime]
  · simp [hij]

/-- The Liouville history is the factor-parity functional calculus. -/
theorem liouvilleHistory_eq_factorParity (X : ℕ) :
    liouvilleHistory X = factorParityHistory X := by
  ext i j
  simp only [liouvilleHistory, factorParityHistory, diagFn,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl,
      ArithmeticFunction.liouville_apply (by omega)]
  · simp [hij]

/-- The Moebius history is squarefree projection times factor parity. -/
theorem moebiusHistory_eq_squarefree_mul_factorParity (X : ℕ) :
    moebiusHistory X = squarefreeProjection X * factorParityHistory X := by
  rw [moebiusHistory, squarefreeProjection, factorParityHistory,
    diagFn, diagFn, diagFn, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hsf : Squarefree ((i : ℕ) + 1)
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hsf]
    simp [hsf]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
    simp [hsf]

/-- The record shift generates the full matrix algebra, so every concrete
derived history above is internal to the record corner. -/
theorem every_matrix_mem_record_history {X : ℕ} (hX : 0 < X)
    (M : Matrix (Fin X) (Fin X) ℂ) :
    M ∈ StarAlgebra.adjoin ℂ ({recS X} : Set (Matrix (Fin X) (Fin X) ℂ)) := by
  rw [record_generation hX]
  trivial

/-- The fully twisted affine/Mellin--heat/von-Mangoldt column is the stated
endpoint expansion. -/
theorem affine_mellin_vonMangoldt_column {X : ℕ} (hX : 0 < X)
    (χ : ℕ → ℂ) (σ τ t θ : ℝ) :
    diagFn X (fun n => affineWeight θ n * χ n * mellinHeatWeight σ τ t n)
        *ᵥ ((countLog X * logZop X - logZop X * countLog X)
          *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1)
      = fun i : Fin X =>
          affineWeight θ ((i : ℕ) + 1) * χ ((i : ℕ) + 1)
            * mellinHeatWeight σ τ t ((i : ℕ) + 1)
            * (ArithmeticFunction.vonMangoldt ((i : ℕ) + 1) : ℂ) := by
  simpa only [mul_assoc] using
    (ar_derived_packet hX).2.2.2.2
      (fun n => affineWeight θ n * χ n * mellinHeatWeight σ τ t n)

end NCG
