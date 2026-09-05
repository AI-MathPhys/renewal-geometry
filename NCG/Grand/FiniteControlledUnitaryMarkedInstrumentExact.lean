/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MarkedFirstReturnReconstruction

/-!
# Finite controlled-unitary marked instruments

This file turns a finite normalized family of controlled unitaries into an
actual marked first-return instrument.  Each branch is given by one Kraus
operator.  Its Choi matrix is exhibited as a rank-one Gram matrix, so complete
positivity, finite tomography, and the support carrier are all intrinsic rather
than additional assumptions.
-/

open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace NCG

variable {d : ℕ} {M : Type*} [Fintype M]

/-- The Heisenberg operation with one Kraus operator `V`. -/
noncomputable def singleKrausHeisenberg (V : Matrix (Fin d) (Fin d) ℂ) :
    FiniteMatrixOperation d where
  toFun X := Vᴴ * X * V
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    simpa only [RingHom.id_apply]

@[simp]
theorem singleKrausHeisenberg_apply
    (V X : Matrix (Fin d) (Fin d) ℂ) :
    singleKrausHeisenberg V X = Vᴴ * X * V := rfl

/-- The Choi matrix of a one-Kraus Heisenberg operation is its rank-one
vectorized Gram matrix. -/
theorem choiMatrix_singleKrausHeisenberg
    (V : Matrix (Fin d) (Fin d) ℂ) :
    choiMatrix (singleKrausHeisenberg V) =
      vecMulVec (fun p : Fin d × Fin d => star (V p.1 p.2))
        (star fun p : Fin d × Fin d => star (V p.1 p.2)) := by
  classical
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [choiMatrix, Matrix.of_apply, singleKrausHeisenberg_apply,
    vecMulVec_apply, Pi.star_apply, star_star]
  change (Vᴴ *
      (Matrix.single i j (1 : ℂ) : Matrix (Fin d) (Fin d) ℂ) * V) k l =
    star (V i k) * V j l
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · simp [Matrix.mul_apply, Matrix.single_apply]
  · intro b _ hbj
    have hz : (Vᴴ *
        (Matrix.single i j (1 : ℂ) : Matrix (Fin d) (Fin d) ℂ)) k b = 0 :=
      Matrix.mul_single_apply_of_ne (1 : ℂ) i j k b hbj (Vᴴ)
    simp [hz]
  · simp

/-- Every one-Kraus Heisenberg operation is completely positive. -/
theorem singleKrausHeisenberg_completelyPositive
    (V : Matrix (Fin d) (Fin d) ℂ) :
    IsMatrixCompletelyPositive (singleKrausHeisenberg V) := by
  rw [choi_criterion, choiMatrix_singleKrausHeisenberg]
  exact posSemidef_vecMulVec_self_star _

/-- The effect of a one-Kraus branch is `VᴴV`. -/
@[simp]
theorem singleKrausHeisenberg_one
    (V : Matrix (Fin d) (Fin d) ℂ) :
    singleKrausHeisenberg V 1 = Vᴴ * V := by
  simp [singleKrausHeisenberg]

/-- Marked branches obtained by weighting each controlled unitary by a
complex amplitude. -/
noncomputable def controlledUnitaryMarkedBranch
    (c : M → ℂ) (U : M → Matrix (Fin d) (Fin d) ℂ) (m : M) :
    FiniteMatrixOperation d :=
  singleKrausHeisenberg (c m • U m)

theorem controlledUnitaryMarkedBranch_completelyPositive
    (c : M → ℂ) (U : M → Matrix (Fin d) (Fin d) ℂ) (m : M) :
    IsMatrixCompletelyPositive (controlledUnitaryMarkedBranch c U m) :=
  singleKrausHeisenberg_completelyPositive _

/-- A normalized amplitude family and isometric controlled operators give
effects whose sum is exactly the identity. -/
theorem controlledUnitaryMarkedBranch_effects_sum
    (c : M → ℂ) (U : M → Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ m, (U m)ᴴ * U m = 1)
    (hc : ∑ m, star (c m) * c m = 1) :
    ∑ m, controlledUnitaryMarkedBranch c U m 1 = 1 := by
  simp only [controlledUnitaryMarkedBranch, singleKrausHeisenberg_one]
  have hbranch : ∀ m, (c m • U m)ᴴ * (c m • U m) =
      (star (c m) * c m) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    intro m
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hU]
    simp [smul_smul]
  simp_rw [hbranch]
  rw [← Finset.sum_smul, hc, one_smul]

/-- The canonical equal-amplitude choice on a nonempty finite mark set. -/
noncomputable def uniformMarkAmplitude (M : Type*) [Fintype M] [Nonempty M] :
    M → ℂ :=
  fun _ => (Real.sqrt ((Fintype.card M : ℝ)⁻¹) : ℂ)

/-- Equal amplitudes on a nonempty finite mark set have total squared norm
one. -/
theorem uniformMarkAmplitude_normalized (M : Type*) [Fintype M] [Nonempty M] :
    ∑ m, star (uniformMarkAmplitude M m) * uniformMarkAmplitude M m = 1 := by
  have hcard : (0 : ℝ) < Fintype.card M := by
    exact_mod_cast Fintype.card_pos
  have hinv : 0 ≤ (Fintype.card M : ℝ)⁻¹ := (inv_pos.mpr hcard).le
  simp only [uniformMarkAmplitude, Complex.star_def, Complex.conj_ofReal,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  norm_cast
  rw [Real.mul_self_sqrt hinv]
  field_simp

/-- The zero survivor branch is completely positive. -/
theorem matrixCompletelyPositive_zero {d : ℕ} :
    IsMatrixCompletelyPositive (0 : FiniteMatrixOperation d) := by
  rw [choi_criterion]
  have hz : choiMatrix (0 : FiniteMatrixOperation d) = 0 := by
    ext p q
    rfl
  rw [hz]
  exact Matrix.PosSemidef.zero

/-- A finite normalized controlled-unitary bank is a genuine one-step marked
first-return instrument, with zero survivor. -/
theorem controlledUnitary_isFiniteFirstReturnInstrument
    (c : M → ℂ) (U : M → Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ m, (U m)ᴴ * U m = 1)
    (hc : ∑ m, star (c m) * c m = 1) :
    IsFiniteFirstReturnInstrument
      (fun _ : Fin 1 => controlledUnitaryMarkedBranch c U)
      (0 : FiniteMatrixOperation d) := by
  refine ⟨?_, matrixCompletelyPositive_zero, ?_⟩
  · intro n m
    exact controlledUnitaryMarkedBranch_completelyPositive c U m
  · simp [controlledUnitaryMarkedBranch_effects_sum c U hU hc]

/-- Every nonempty finite controlled-unitary bank therefore carries a
canonical, equally weighted marked first-return instrument. -/
theorem exists_controlledUnitary_isFiniteFirstReturnInstrument
    [Nonempty M] (U : M → Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ m, (U m)ᴴ * U m = 1) :
    ∃ c : M → ℂ,
      IsFiniteFirstReturnInstrument
        (fun _ : Fin 1 => controlledUnitaryMarkedBranch c U)
        (0 : FiniteMatrixOperation d) := by
  refine ⟨uniformMarkAmplitude M, ?_⟩
  exact controlledUnitary_isFiniteFirstReturnInstrument _ U hU
    (uniformMarkAmplitude_normalized M)

/-- The same construction, stated in the exact Choi-positive tomography form
used by finite first-return reconstruction. -/
theorem controlledUnitary_markedInstrument_choiCertificate
    (c : M → ℂ) (U : M → Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ m, (U m)ᴴ * U m = 1)
    (hc : ∑ m, star (c m) * c m = 1) :
    (∀ n m, (choiMatrix
      ((fun _ : Fin 1 => controlledUnitaryMarkedBranch c U) n m)).PosSemidef) ∧
      (choiMatrix (0 : FiniteMatrixOperation d)).PosSemidef ∧
      (∑ n : Fin 1, ∑ m,
        (fun _ : Fin 1 => controlledUnitaryMarkedBranch c U) n m 1) +
          (0 : FiniteMatrixOperation d) 1 = 1 := by
  exact (finiteFirstReturnInstrument_iff_choiPositivity _ _).mp
    (controlledUnitary_isFiniteFirstReturnInstrument c U hU hc)

end NCG
