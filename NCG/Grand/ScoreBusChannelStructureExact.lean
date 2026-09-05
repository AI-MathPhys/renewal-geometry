/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandScoreBus

/-!
# Complete channel structure of the protected score bus

This closes the clauses of `thm:SM-score-bus` beyond the already checked Pauli action: a Kraus
ampliation certificate for complete positivity, phase/deck covariance, Hilbert--Schmidt
self-adjointness, the scalar fixed algebra, the exact traceless gap, and constant branch effects.
-/

open Matrix
open scoped ComplexOrder Kronecker

namespace NCG

noncomputable def scoreBusMap (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • A + (1 / 4 : ℂ) • (clockX * A * clockX)
    + (1 / 4 : ℂ) • (clockY * A * clockY)

/-- Entrywise normal form of the score bus. -/
theorem scoreBusMap_eq_entries (A : Matrix (Fin 2) (Fin 2) ℂ) :
    scoreBusMap A =
      !![(A 0 0 + A 1 1) / 2, A 0 1 / 2;
         A 1 0 / 2, (A 0 0 + A 1 1) / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scoreBusMap, clockX, clockY, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two] <;> ring_nf <;> rw [Complex.I_sq] <;> ring
noncomputable def scoreBusPhase (z : Circle) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(z : ℂ), 0; 0, (z : ℂ)⁻¹]

/-- A Kraus-form ampliation of the score bus at an arbitrary finite ancilla. -/
noncomputable def scoreBusAmplification {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix (m × Fin 2) (m × Fin 2) ℂ) :=
  let I := (1 : Matrix m m ℂ)
  let K0 := (Real.sqrt 2 : ℂ)⁻¹ • (I ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
  let KX := (2 : ℂ)⁻¹ • (I ⊗ₖ clockX)
  let KY := (2 : ℂ)⁻¹ • (I ⊗ₖ clockY)
  K0 * A * K0ᴴ + KX * A * KXᴴ + KY * A * KYᴴ

/-- The Kraus ampliation is positive at every finite ancilla: the explicit complete-positivity
certificate. -/
theorem scoreBusAmplification_posSemidef {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix (m × Fin 2) (m × Fin 2) ℂ) (hA : A.PosSemidef) :
    (scoreBusAmplification A).PosSemidef := by
  unfold scoreBusAmplification
  exact ((hA.mul_mul_conjTranspose_same _).add
    (hA.mul_mul_conjTranspose_same _)).add
    (hA.mul_mul_conjTranspose_same _)

/-- Covariance under all protected phase rotations about the grading axis. -/
theorem scoreBus_phase_covariant (z : Circle) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    scoreBusMap (scoreBusPhase z * A * (scoreBusPhase z)ᴴ)
      = scoreBusPhase z * scoreBusMap A * (scoreBusPhase z)ᴴ := by
  have hzstar : (starRingEnd ℂ) (z : ℂ) = (z : ℂ)⁻¹ := (Circle.coe_inv_eq_conj z).symm
  rw [scoreBusMap_eq_entries, scoreBusMap_eq_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scoreBusPhase, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, hzstar] <;>
    field_simp <;> ring
/-- Deck covariance under conjugation by the grading flip `X_gr`. -/
theorem scoreBus_deck_covariant (A : Matrix (Fin 2) (Fin 2) ℂ) :
    scoreBusMap (clockX * A * clockX) = clockX * scoreBusMap A * clockX := by
  rw [scoreBusMap_eq_entries, scoreBusMap_eq_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockX, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring
/-- Tracial Hilbert--Schmidt self-adjointness. -/
theorem scoreBus_hilbertSchmidt_selfAdjoint
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    ((scoreBusMap A)ᴴ * B).trace = (Aᴴ * scoreBusMap B).trace := by
  rw [scoreBusMap_eq_entries, scoreBusMap_eq_entries]
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace_fin_two,
    Fin.sum_univ_two]
  simp only [map_inv₀, map_ofNat]
  ring
/-- The fixed algebra of the score bus consists exactly of scalar matrices. -/
theorem scoreBus_fixed_iff_scalar (A : Matrix (Fin 2) (Fin 2) ℂ) :
    scoreBusMap A = A ↔ ∃ c : ℂ, A = c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  constructor
  · intro h
    rw [scoreBusMap_eq_entries] at h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    simp at h00 h01 h10 h11
    refine ⟨A 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp
    · have hz : A 0 1 = 0 := by linear_combination -2 * h01
      simpa [Matrix.one_apply] using hz
    · have hz : A 1 0 = 0 := by linear_combination -2 * h10
      simpa [Matrix.one_apply] using hz
    · have hd : A 1 1 = A 0 0 := h11.symm.trans h00
      simpa [Matrix.one_apply] using hd
  · rintro ⟨c, rfl⟩
    rw [scoreBusMap_eq_entries]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
/-- Exact eigenvalue table on the traceless Pauli directions, hence least positive eigenvalue
`1/2` for `I - Ψ_sb`. -/
theorem scoreBus_traceless_gap_table :
    scoreBusMap clockX = (1 / 2 : ℂ) • clockX
      ∧ scoreBusMap clockY = (1 / 2 : ℂ) • clockY
      ∧ scoreBusMap clockZ = 0
      ∧ clockX ≠ 0 ∧ clockY ≠ 0 ∧ clockZ ≠ 0 := by
  obtain ⟨_, hX, hY, hZ, _⟩ := sm_score_bus (0 : Matrix (Fin 2) (Fin 2) ℂ)
  refine ⟨hX, hY, hZ, ?_, ?_, ?_⟩
  · intro h
    have q := congrFun (congrFun h 0) 1
    simp [clockX] at q
  · intro h
    have q := congrFun (congrFun h 0) 1
    simp [clockY] at q
  · intro h
    have q := congrFun (congrFun h 0) 0
    simp [clockZ] at q
/-- Every resolved unitary score-square branch `U/2` has the constant effect `I/4`. -/
theorem scoreBus_branch_effects :
    let branch (U : Matrix (Fin 2) (Fin 2) ℂ) := (2 : ℂ)⁻¹ • U
    (branch 1)ᴴ * branch 1 = (1 / 4 : ℂ) • 1
      ∧ (branch clockX)ᴴ * branch clockX = (1 / 4 : ℂ) • 1
      ∧ (branch clockY)ᴴ * branch clockY = (1 / 4 : ℂ) • 1 := by
  dsimp
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [clockX, clockY, Matrix.mul_apply, Fin.sum_univ_two, map_inv₀, map_ofNat] <;>
      ring_nf <;> rw [Complex.I_sq] <;> ring

end NCG
