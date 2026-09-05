/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.ChoiCriterion
import NCG.Grand.MarkedFirstReturn

/-!
# Marked first-return reconstruction

This module supplies the finite tomography, Choi-positivity, and formal-series
parts of the marked first-return theorem.  The formal-series multiplication is
kept noncommutative, as required for composition of quantum operations.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- A finite operation on a matrix algebra. -/
abbrev FiniteMatrixOperation (d : ℕ) :=
  Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ

/-- Complete branch tomography on the matrix-unit preparations and all output
entries determines a finite operation uniquely. -/
theorem matrixUnitTomography_unique {n m : ℕ}
    (Φ Ψ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ i j, Φ (Matrix.single i j 1) = Ψ (Matrix.single i j 1)) :
    Φ = Ψ := by
  apply LinearMap.ext
  intro X
  rw [Matrix.matrix_eq_sum_single X]
  simp_rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hsingle : Matrix.single i j (X i j) =
      X i j • Matrix.single i j (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hsingle, map_smul, map_smul, h i j]

/-- Equality of finite Choi matrices is exactly equality of the represented
operations; this is the Choi-coordinate form of branch tomography. -/
theorem choiMatrix_injective {n m : ℕ}
    (Φ Ψ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin m) (Fin m) ℂ)
    (h : choiMatrix Φ = choiMatrix Ψ) : Φ = Ψ := by
  apply matrixUnitTomography_unique Φ Ψ
  intro i j
  ext k l
  exact congrArg (fun C => C (i, k) (j, l)) h

/-- Composition preserves complete positivity for finite matrix operations. -/
theorem matrixCompletelyPositive_comp {a b c : ℕ}
    {Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ]
      Matrix (Fin b) (Fin b) ℂ}
    {Ψ : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ]
      Matrix (Fin c) (Fin c) ℂ}
    (hΦ : IsMatrixCompletelyPositive Φ)
    (hΨ : IsMatrixCompletelyPositive Ψ) :
    IsMatrixCompletelyPositive (Ψ.comp Φ) := by
  intro k X hX
  have hcomp : ampliate k (Ψ.comp Φ) X =
      ampliate k Ψ (ampliate k Φ X) := by
    ext ⟨p, r⟩ ⟨q, s⟩
    rfl
  rw [hcomp]
  exact hΨ k _ (hΦ k X hX)

/-- The identity matrix operation is completely positive. -/
theorem matrixCompletelyPositive_one {d : ℕ} :
    IsMatrixCompletelyPositive (1 : FiniteMatrixOperation d) := by
  intro k X hX
  have hone : ampliate k (1 : FiniteMatrixOperation d) X = X := by
    ext ⟨p, r⟩ ⟨q, s⟩
    rfl
  rwa [hone]

/-- Every iterate of a completely positive matrix operation is completely
positive. -/
theorem matrixCompletelyPositive_pow {d : ℕ}
    {Φ : FiniteMatrixOperation d} (hΦ : IsMatrixCompletelyPositive Φ) :
    ∀ n : ℕ, IsMatrixCompletelyPositive (Φ ^ n)
  | 0 => by simpa using (matrixCompletelyPositive_one (d := d))
  | n + 1 => by
      rw [pow_succ]
      exact matrixCompletelyPositive_comp hΦ
        (matrixCompletelyPositive_pow hΦ n)

/-- A finite first-return instrument consists of CP return branches and a CP
survivor branch whose Heisenberg effects sum to the identity. -/
def IsFiniteFirstReturnInstrument {d N : ℕ} {M : Type*} [Fintype M]
    (Fstar : Fin N → M → FiniteMatrixOperation d)
    (Sstar : FiniteMatrixOperation d) : Prop :=
  (∀ n m, IsMatrixCompletelyPositive (Fstar n m)) ∧
  IsMatrixCompletelyPositive Sstar ∧
  (∑ n, ∑ m, Fstar n m 1) + Sstar 1 = 1

/-- Exact finite Choi criterion for the marked first-return instrument. -/
theorem finiteFirstReturnInstrument_iff_choiPositivity {d N : ℕ}
    {M : Type*} [Fintype M]
    (Fstar : Fin N → M → FiniteMatrixOperation d)
    (Sstar : FiniteMatrixOperation d) :
    IsFiniteFirstReturnInstrument Fstar Sstar ↔
      (∀ n m, (choiMatrix (Fstar n m)).PosSemidef) ∧
      (choiMatrix Sstar).PosSemidef ∧
      (∑ n, ∑ m, Fstar n m 1) + Sstar 1 = 1 := by
  simp only [IsFiniteFirstReturnInstrument, choi_criterion]

/-- The stationary first-return branch at time `n+1`: a marked event after
exactly `n` consecutive no-return outcomes. -/
def stationaryMarkedFirstReturn {d : ℕ} {M : Type*}
    (Φnone : FiniteMatrixOperation d)
    (Φmark : M → FiniteMatrixOperation d)
    (n : ℕ) (m : M) : FiniteMatrixOperation d :=
  Φmark m * Φnone ^ n

/-- The no-return survivor through horizon `N`. -/
def stationaryMarkedSurvivor {d : ℕ}
    (Φnone : FiniteMatrixOperation d) (N : ℕ) :
    FiniteMatrixOperation d :=
  Φnone ^ N

/-- The stationary definition is the resolved word
`none^n · mark`, with composition written in Schrödinger order. -/
theorem stationaryMarkedFirstReturn_formula {d : ℕ} {M : Type*}
    (Φnone : FiniteMatrixOperation d)
    (Φmark : M → FiniteMatrixOperation d)
    (n : ℕ) (m : M) :
    stationaryMarkedFirstReturn Φnone Φmark n m =
      Φmark m * Φnone ^ n := rfl

/-- CP primitive branches give CP first-return branches for every resolved
stationary word. -/
theorem stationaryMarkedFirstReturn_completelyPositive {d : ℕ}
    {M : Type*}
    (Φnone : FiniteMatrixOperation d)
    (Φmark : M → FiniteMatrixOperation d)
    (hnone : IsMatrixCompletelyPositive Φnone)
    (hmark : ∀ m, IsMatrixCompletelyPositive (Φmark m))
    (n : ℕ) (m : M) :
    IsMatrixCompletelyPositive
      (stationaryMarkedFirstReturn Φnone Φmark n m) := by
  exact matrixCompletelyPositive_comp
    (matrixCompletelyPositive_pow hnone n) (hmark m)

/-- A CP no-return primitive gives a CP survivor at every horizon. -/
theorem stationaryMarkedSurvivor_completelyPositive {d : ℕ}
    (Φnone : FiniteMatrixOperation d)
    (hnone : IsMatrixCompletelyPositive Φnone) (N : ℕ) :
    IsMatrixCompletelyPositive (stationaryMarkedSurvivor Φnone N) :=
  matrixCompletelyPositive_pow hnone N

/-! ## Noncommutative formal renewal series -/

/-- The unit formal series, written coefficientwise so the coefficient ring
may be noncommutative. -/
def renewalSeriesUnit {R : Type*} [Zero R] [One R] (n : ℕ) : R :=
  if n = 0 then 1 else 0

/-- Noncommutative Cauchy product.  The coefficient `k = 0` is displayed
separately from the interval `1 ≤ k ≤ n`; this is definitionally the usual
sum over `0 ≤ k ≤ n`. -/
def renewalSeriesConvolution {R : Type*} [Semiring R]
    (U F : ℕ → R) (n : ℕ) : R :=
  U n * F 0 + ∑ k ∈ Finset.Icc 1 n, U (n - k) * F k

/-- Coefficient form of `U = I + U F`. -/
def HasFormalRenewalIdentity {R : Type*} [Semiring R]
    (U F : ℕ → R) : Prop :=
  ∀ n, U n = renewalSeriesUnit n + renewalSeriesConvolution U F n

/-- The coefficient recurrence from the manuscript, including the constant
terms of the two formal series. -/
def HasFirstReturnRecurrence {R : Type*} [Semiring R]
    (U F : ℕ → R) : Prop :=
  U 0 = 1 ∧ F 0 = 0 ∧
    ∀ n, 1 ≤ n →
      U n = ∑ k ∈ Finset.Icc 1 n, U (n - k) * F k

@[simp] theorem renewalSeriesUnit_zero {R : Type*} [Zero R] [One R] :
    renewalSeriesUnit (R := R) 0 = 1 := by
  simp [renewalSeriesUnit]

@[simp] theorem renewalSeriesUnit_of_ne_zero {R : Type*} [Zero R] [One R]
    {n : ℕ} (hn : n ≠ 0) : renewalSeriesUnit (R := R) n = 0 := by
  simp [renewalSeriesUnit, hn]

/-- The ordinary renewal recurrence is exactly the formal identity
`U = I + U F`. -/
theorem firstReturnRecurrence_formalIdentity {R : Type*} [Semiring R]
    {U F : ℕ → R} (h : HasFirstReturnRecurrence U F) :
    HasFormalRenewalIdentity U F := by
  rcases h with ⟨hU0, hF0, hrec⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp [renewalSeriesConvolution, hU0, hF0]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    rw [hrec n hn1]
    simp [renewalSeriesConvolution, hF0, renewalSeriesUnit, hn]

/-- Solving the renewal equation for its last summand gives the manuscript's
boxed first-return recursion. -/
theorem firstReturnRecurrence_solveCurrent {R : Type*} [Ring R]
    {U F : ℕ → R} (h : HasFirstReturnRecurrence U F)
    (n : ℕ) (hn : 1 ≤ n) :
    F n = U n -
      ∑ k ∈ Finset.Icc 1 (n - 1), U (n - k) * F k := by
  rcases h with ⟨hU0, _, hrec⟩
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hn)
  have hr := hrec (r + 1) (by simp)
  rw [Finset.sum_Icc_succ_top (show 1 ≤ r + 1 by omega)] at hr
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.sub_self,
    hU0, one_mul] at hr ⊢
  exact eq_sub_of_add_eq' hr.symm

/-- Right multiplication by the unit formal series fixes every coefficient. -/
theorem renewalSeriesConvolution_unit_right {R : Type*} [Semiring R]
    (U : ℕ → R) (n : ℕ) :
    renewalSeriesConvolution U renewalSeriesUnit n = U n := by
  simp [renewalSeriesConvolution, renewalSeriesUnit]

/-- Cauchy multiplication distributes over subtraction in the right factor. -/
theorem renewalSeriesConvolution_sub_right {R : Type*} [Ring R]
    (U V W : ℕ → R) (n : ℕ) :
    renewalSeriesConvolution U (V - W) n =
      renewalSeriesConvolution U V n - renewalSeriesConvolution U W n := by
  simp only [renewalSeriesConvolution, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]
  abel

/-- The formal identity `U = I + U F` gives the noncommutative resolvent
identity `U (I - F) = I`.  Thus `I - F` is the formal right inverse of `U`;
no convergence or commutativity hypothesis is used. -/
theorem formalRenewal_rightInverse {R : Type*} [Ring R]
    {U F : ℕ → R} (h : HasFormalRenewalIdentity U F) (n : ℕ) :
    renewalSeriesConvolution U (renewalSeriesUnit - F) n =
      renewalSeriesUnit n := by
  rw [renewalSeriesConvolution_sub_right,
    renewalSeriesConvolution_unit_right, h n]
  abel

/-- Coefficient form of `F = I - U⁻¹`, with the inverse certified by
`formalRenewal_rightInverse`. -/
theorem formalRenewal_returnSeries_eq_unit_sub_inverse {R : Type*} [Ring R]
    (F : ℕ → R) (n : ℕ) :
    F n = renewalSeriesUnit n -
      ((renewalSeriesUnit : ℕ → R) - F) n := by
  simp

end NCG
