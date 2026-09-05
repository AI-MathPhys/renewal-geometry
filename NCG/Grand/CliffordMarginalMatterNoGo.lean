/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.CliffordConcrete

/-!
# separate Clifford marginals do not decide matter
-/

open Matrix Kronecker

namespace NCG

open CommonOrigin

abbrev SMST4 := Fin 2 × Fin 2
abbrev SMST8 := SMST4 × Fin 2

/-- The intrinsic four-axis chirality word. -/
def smstChirality : Matrix SMST4 SMST4 ℂ :=
  gamma 0 * gamma 1 * gamma 2 * gamma 3

/-- The external Clifford packet on a carrier with multiplicity two. -/
def smstAxis (mu : Fin 4) : Matrix SMST8 SMST8 ℂ :=
  gamma mu ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- Intrinsic-chirality and multiplicity-only gradings. -/
def smstJChir : Matrix SMST8 SMST8 ℂ :=
  smstChirality ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)

def smstJSep : Matrix SMST8 SMST8 ℂ :=
  (1 : Matrix SMST4 SMST4 ℂ) ⊗ₖ pauli1

private theorem neg_kron_general {m n : Type*}
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [Matrix.kroneckerMap_apply]

private theorem kron_neg_general {m n : Type*}
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [Matrix.kroneckerMap_apply]

/-- A finite grading has equally large sign fibres when it is an
involution and an invertible involution exchanges its two signs.  On
an eight-dimensional carrier this is the algebraic `4+4` certificate. -/
def HasFourPlusFour (J : Matrix SMST8 SMST8 ℂ) : Prop :=
  J * J = 1 ∧ ∃ S : Matrix SMST8 SMST8 ℂ,
    S * S = 1 ∧ S * J = -(J * S)

/-- Correlation form of one Clifford-axis matter mass.  For Hermitian
involutions this equals `2 ‖P₋ σ P₊‖_HS² / 8`. -/
noncomputable def smstAxisMass
    (J sigma : Matrix SMST8 SMST8 ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (1 - (1 / 8 : ℂ) * Matrix.trace (J * sigma * J * sigma))

noncomputable def smstCliffordMass
    (J : Matrix SMST8 SMST8 ℂ) : ℂ :=
  (1 / 4 : ℂ) * ∑ mu : Fin 4, smstAxisMass J (smstAxis mu)

theorem smstChirality_eq :
    smstChirality = -(pauli3 ⊗ₖ pauli3) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [smstChirality, gamma, pauli1, pauli2, pauli3,
      Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Complex.I_mul_I]

theorem smstChirality_sq : smstChirality * smstChirality = 1 := by
  rw [smstChirality_eq]
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [pauli3, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kroneckerMap_apply]

theorem smstChirality_anticomm (mu : Fin 4) :
    smstChirality * gamma mu = -(gamma mu * smstChirality) := by
  rw [smstChirality_eq]
  fin_cases mu <;>
    ext ⟨i, k⟩ ⟨j, l⟩ <;>
    fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [gamma, pauli1, pauli2, pauli3, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Complex.I_mul_I]

theorem smstAxis_sq (mu : Fin 4) : smstAxis mu * smstAxis mu = 1 := by
  rw [smstAxis, ← Matrix.mul_kronecker_mul, gamma_sq,
    Matrix.one_mul, Matrix.one_kronecker_one]

theorem smstJChir_sq : smstJChir * smstJChir = 1 := by
  rw [smstJChir, ← Matrix.mul_kronecker_mul, smstChirality_sq,
    Matrix.one_mul, Matrix.one_kronecker_one]

theorem smstJSep_sq : smstJSep * smstJSep = 1 := by
  rw [smstJSep, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    pauli1_sq, Matrix.one_kronecker_one]

theorem smstJChir_anticomm (mu : Fin 4) :
    smstJChir * smstAxis mu = -(smstAxis mu * smstJChir) := by
  rw [smstJChir, smstAxis, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    smstChirality_anticomm]
  simpa using neg_kron_general (gamma mu * smstChirality)
    (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem smstJSep_comm (mu : Fin 4) :
    smstJSep * smstAxis mu = smstAxis mu * smstJSep := by
  rw [smstJSep, smstAxis, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  simp

theorem smstJChir_balanced : HasFourPlusFour smstJChir := by
  refine ⟨smstJChir_sq, smstAxis 0, smstAxis_sq 0, ?_⟩
  rw [smstJChir_anticomm]
  simp

theorem smstJSep_balanced : HasFourPlusFour smstJSep := by
  refine ⟨smstJSep_sq, ?_, ?_, ?_⟩
  · exact (gamma 0) ⊗ₖ pauli3
  · rw [← Matrix.mul_kronecker_mul, gamma_sq, pauli3_sq,
      Matrix.one_kronecker_one]
  · rw [smstJSep, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      pauli31_anticomm]
    simpa using kron_neg_general (gamma 0) (pauli1 * pauli3)

private theorem axisMass_of_anticomm
    (J sigma : Matrix SMST8 SMST8 ℂ)
    (hJ : J * J = 1) (hsigma : sigma * sigma = 1)
    (hanti : J * sigma = -(sigma * J)) :
    smstAxisMass J sigma = 1 := by
  have hanti' : sigma * J = -(J * sigma) := by
    rw [hanti]
    simp
  have hprod : J * sigma * J * sigma = -1 := by
    calc
      J * sigma * J * sigma = J * (sigma * J) * sigma := by
        simp only [Matrix.mul_assoc]
      _ = J * (-(J * sigma)) * sigma := by rw [hanti']
      _ = -((J * J) * (sigma * sigma)) := by noncomm_ring
      _ = -1 := by rw [hJ, hsigma, Matrix.one_mul]
  rw [smstAxisMass, hprod, Matrix.trace_neg, Matrix.trace_one]
  norm_num

private theorem axisMass_of_comm
    (J sigma : Matrix SMST8 SMST8 ℂ)
    (hJ : J * J = 1) (hsigma : sigma * sigma = 1)
    (hcomm : J * sigma = sigma * J) :
    smstAxisMass J sigma = 0 := by
  have hprod : J * sigma * J * sigma = 1 := by
    calc
      J * sigma * J * sigma = J * (sigma * J) * sigma := by
        simp only [Matrix.mul_assoc]
      _ = J * (J * sigma) * sigma := by rw [hcomm]
      _ = (J * J) * (sigma * sigma) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, hsigma, Matrix.one_mul]
  rw [smstAxisMass, hprod, Matrix.trace_one]
  norm_num

theorem smstJChir_axisMass (mu : Fin 4) :
    smstAxisMass smstJChir (smstAxis mu) = 1 :=
  axisMass_of_anticomm _ _ smstJChir_sq (smstAxis_sq mu)
    (smstJChir_anticomm mu)

theorem smstJSep_axisMass (mu : Fin 4) :
    smstAxisMass smstJSep (smstAxis mu) = 0 :=
  axisMass_of_comm _ _ smstJSep_sq (smstAxis_sq mu)
    (smstJSep_comm mu)

/-- `cth:SMST-Clifford-marginals`: on the same `ℂ⁴ ⊗ ℂ²`
carrier and with the same external Clifford packet, intrinsic chirality
and a multiplicity-only grading both have `4+4` sign fibres but their
Clifford matter masses are respectively one and zero. -/
theorem separate_clifford_marginals_do_not_decide_matter :
    HasFourPlusFour smstJChir ∧ HasFourPlusFour smstJSep
      ∧ smstCliffordMass smstJChir = 1
      ∧ smstCliffordMass smstJSep = 0 := by
  refine ⟨smstJChir_balanced, smstJSep_balanced, ?_, ?_⟩
  · simp [smstCliffordMass, smstJChir_axisMass]
  · simp [smstCliffordMass, smstJSep_axisMass]

end NCG
