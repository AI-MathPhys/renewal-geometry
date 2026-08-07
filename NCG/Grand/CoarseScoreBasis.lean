/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.ClockQuarterRoot

/-!
# A coarse pinching does not identify the fine score basis
  (`cth:coarse-score-basis`, Gran-Tensor manuscript)

* `coarse_score_basis`: the Lüders instrument `ρ ↦ P±ρP±` and
  the fair phase instrument `ρ ↦ ½U±ρU±ᴴ` with
  `U± = e^{∓iπZ/4}` have the same coarse channel
  `½(ρ + ZρZ)`, but different resolved outcome branches — the
  coarse collision does not identify a physical score bit or its
  environment basis.

Rendering disclosed: the projections and phases are rendered
through the Pauli presentation `P₊ = ½(1+Z)`,
`U₊ = (1 - iZ)/√2` (so `U₋ = U₊ᴴ`); the branch inequality is
witnessed at `ρ = 1`.
-/

open Matrix

namespace NCG

/-- The Pauli `Z`. -/
noncomputable def scoreZ : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![1, -1]

/-- The `+1` eigenprojection `P₊ = ½(1 + Z)`. -/
noncomputable def scoreP : Matrix (Fin 2) (Fin 2) ℂ :=
  (2⁻¹ : ℂ) • (1 + scoreZ)

/-- The quarter phase `U₊ = e^{-iπZ/4} = (1 - iZ)/√2`. -/
noncomputable def scoreU : Matrix (Fin 2) (Fin 2) ℂ :=
  invSqrt2 • (1 - Complex.I • scoreZ)

/-- `cth:coarse-score-basis`: equal coarse channels, distinct
resolved branches. -/
theorem coarse_score_basis :
    (∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      scoreP * ρ * scoreP
        + (1 - scoreP) * ρ * (1 - scoreP)
      = (2⁻¹ : ℂ) • (ρ + scoreZ * ρ * scoreZ))
    ∧ (∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      (2⁻¹ : ℂ) • (scoreU * ρ * scoreUᴴ)
        + (2⁻¹ : ℂ) • (scoreUᴴ * ρ * scoreU)
      = (2⁻¹ : ℂ) • (ρ + scoreZ * ρ * scoreZ))
    ∧ (∃ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      scoreP * ρ * scoreP
        ≠ (2⁻¹ : ℂ) • (scoreU * ρ * scoreUᴴ)) := by
  have husq : invSqrt2 * invSqrt2 = (2⁻¹ : ℂ) := by
    have h := invSqrt2_sq
    rwa [pow_two] at h
  have hZH : scoreZᴴ = scoreZ := by
    rw [scoreZ, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    fin_cases i <;> simp
  have hZ2 : scoreZ * scoreZ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [scoreZ, Matrix.mul_apply, Fin.sum_univ_two]
  have hUH : scoreUᴴ = invSqrt2 • (1 + Complex.I • scoreZ) := by
    rw [scoreU, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hZH, invSqrt2_star,
      Complex.star_def, Complex.conj_I, neg_smul,
      sub_neg_eq_add]
  have hQ : (1 : Matrix (Fin 2) (Fin 2) ℂ) - scoreP
      = (2⁻¹ : ℂ) • (1 - scoreZ) := by
    rw [scoreP]
    module
  refine ⟨?_, ?_, ?_⟩
  · intro ρ
    rw [hQ, scoreP]
    have hexp : ∀ (s : ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ),
        (s • A) * ρ * (s • B) = (s * s) • (A * ρ * B) := by
      intro s A B
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        smul_smul]
    rw [hexp, hexp, ← smul_add]
    have hkey : (1 + scoreZ) * ρ * (1 + scoreZ)
        + (1 - scoreZ) * ρ * (1 - scoreZ)
        = (2 : ℂ) • ρ + (2 : ℂ) • (scoreZ * ρ * scoreZ) := by
      simp only [Matrix.add_mul, Matrix.mul_add,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
        Matrix.mul_one]
      module
    rw [hkey]
    module
  · intro ρ
    rw [hUH, scoreU]
    have hexp : ∀ A B : Matrix (Fin 2) (Fin 2) ℂ,
        (invSqrt2 • A) * ρ * (invSqrt2 • B)
          = (2⁻¹ : ℂ) • (A * ρ * B) := by
      intro A B
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        smul_smul, husq]
    rw [hexp, hexp, smul_smul, smul_smul, ← smul_add]
    have hkey : (1 - Complex.I • scoreZ) * ρ
          * (1 + Complex.I • scoreZ)
        + (1 + Complex.I • scoreZ) * ρ
          * (1 - Complex.I • scoreZ)
        = (2 : ℂ) • ρ + (2 : ℂ) • (scoreZ * ρ * scoreZ) := by
      simp only [Matrix.add_mul, Matrix.mul_add,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
        Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
      match_scalars <;> (ring_nf; try simp [Complex.I_sq])
    rw [hkey]
    module
  · refine ⟨1, ?_⟩
    intro h
    have hP2 : scoreP * 1 * scoreP = scoreP := by
      rw [Matrix.mul_one, scoreP]
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [show (1 + scoreZ) * (1 + scoreZ)
          = (2 : ℂ) • (1 + scoreZ) from by
        simp only [Matrix.add_mul, Matrix.mul_add,
          Matrix.one_mul, Matrix.mul_one, hZ2]
        module]
      rw [smul_smul]
      module
    have hU1 : (2⁻¹ : ℂ) • (scoreU * 1 * scoreUᴴ)
        = (2⁻¹ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      congr 1
      rw [Matrix.mul_one, hUH, scoreU]
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, husq]
      rw [show (1 - Complex.I • scoreZ)
          * (1 + Complex.I • scoreZ)
          = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) from by
        simp only [Matrix.mul_add, Matrix.sub_mul,
          Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
          Matrix.mul_smul, hZ2]
        match_scalars <;> (ring_nf; try norm_num [Complex.I_sq])]
      rw [smul_smul]
      module
    rw [hP2, hU1] at h
    have h11 := congrArg (fun M => M 1 1) h
    simp only [scoreP, Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply_eq, scoreZ, smul_eq_mul] at h11
    rw [Matrix.diagonal_apply_eq] at h11
    simp at h11

end NCG
