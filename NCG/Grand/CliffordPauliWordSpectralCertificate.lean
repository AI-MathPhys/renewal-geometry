/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.CliffordConcrete

/-!
# Pauli-word spectral certificate for the Clifford commutator

The sixteen two-qubit Pauli words diagonalize the four commuting Clifford
conjugations.  This file constructs that basis explicitly, proves its
Hilbert--Schmidt orthogonality, and records the anticommutation multiplicities
which give the sharp spectral window `[4,16]` off the scalar word.
-/

open Matrix Kronecker

namespace NCG
namespace CliffordPauliWordSpectralCertificate

open CommonOrigin

noncomputable section

abbrev C4 := Fin 2 × Fin 2
abbrev WordIndex := Fin 4 × Fin 4

def pauliAt : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![1, pauli1, pauli2, pauli3]

def pauliWord (w : WordIndex) : Matrix C4 C4 ℂ :=
  pauliAt w.1 ⊗ₖ pauliAt w.2

theorem pauliWord_hermitian (w : WordIndex) :
    (pauliWord w)ᴴ = pauliWord w := by
  rcases w with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [pauliWord, pauliAt, Matrix.conjTranspose_kronecker,
      pauli1_herm, pauli2_herm, pauli3_herm]

set_option maxHeartbeats 1000000 in
theorem pauliWord_trace_product (u v : WordIndex) :
    Matrix.trace (pauliWord u * pauliWord v) =
      if u = v then 4 else 0 := by
  rcases u with ⟨a, b⟩
  rcases v with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [pauliWord, pauliAt, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, pauli1, pauli2, pauli3,
      Complex.I_mul_I]

def pauliSynthesis (c : WordIndex → ℂ) : Matrix C4 C4 ℂ :=
  ∑ w, c w • pauliWord w

def pauliCoefficient (X : Matrix C4 C4 ℂ) (w : WordIndex) : ℂ :=
  (4 : ℂ)⁻¹ * Matrix.trace (pauliWord w * X)

theorem pauliCoefficient_synthesis (c : WordIndex → ℂ) (u : WordIndex) :
    pauliCoefficient (pauliSynthesis c) u = c u := by
  classical
  unfold pauliCoefficient pauliSynthesis
  rw [Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [Matrix.mul_smul, Matrix.trace_smul,
    pauliWord_trace_product]
  simp
  ring

def pauliSynthesisLinear :
    (WordIndex → ℂ) →ₗ[ℂ] Matrix C4 C4 ℂ where
  toFun := pauliSynthesis
  map_add' c d := by
    unfold pauliSynthesis
    simp_rw [Pi.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' z c := by
    unfold pauliSynthesis
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro w _
    simp [smul_smul]

theorem pauliSynthesisLinear_injective :
    Function.Injective pauliSynthesisLinear := by
  intro c d h
  funext u
  change pauliSynthesis c = pauliSynthesis d at h
  rw [← pauliCoefficient_synthesis c u,
    ← pauliCoefficient_synthesis d u, h]

theorem pauliSynthesisLinear_surjective :
    Function.Surjective pauliSynthesisLinear := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    pauliSynthesisLinear_injective
  simp [Module.finrank_matrix, C4, WordIndex]

theorem exists_pauli_expansion (X : Matrix C4 C4 ℂ) :
    ∃! c : WordIndex → ℂ, pauliSynthesis c = X := by
  obtain ⟨c, hc⟩ := pauliSynthesisLinear_surjective X
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact pauliSynthesisLinear_injective (hd.trans hc.symm)

/-- Whether a Pauli word anticommutes with one of the four concrete gamma
axes.  The table is ordered by the two Pauli indices and then by the axis. -/
def anticommutesAxis (w : WordIndex) (μ : Fin 4) : Bool :=
  ![
    ![![false, false, false, false], ![false, false, false, true],
       ![false, false, true, false], ![false, false, true, true]],
    ![![false, true, true, true], ![false, true, true, false],
       ![false, true, false, true], ![false, true, false, false]],
    ![![true, false, true, true], ![true, false, true, false],
       ![true, false, false, true], ![true, false, false, false]],
    ![![true, true, false, false], ![true, true, false, true],
       ![true, true, true, false], ![true, true, true, true]]
  ] w.1 w.2 μ

/-- Number of axes anticommuting with a word. -/
def anticommutationCount (w : WordIndex) : ℕ :=
  ![![0, 1, 1, 2], ![3, 2, 2, 1], ![3, 2, 2, 1], ![2, 3, 3, 4]]
    w.1 w.2

theorem anticommutationCount_bounds (w : WordIndex)
    (hw : w ≠ (0, 0)) :
    1 ≤ anticommutationCount w ∧ anticommutationCount w ≤ 4 := by
  rcases w with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    simp_all [anticommutationCount]

set_option maxHeartbeats 4000000 in
theorem pauliWord_axis_relation (w : WordIndex) (μ : Fin 4) :
    if anticommutesAxis w μ then
      pauliWord w * gamma μ = -(gamma μ * pauliWord w)
    else
      pauliWord w * gamma μ = gamma μ * pauliWord w := by
  rcases w with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> fin_cases μ <;>
    ext ⟨i, k⟩ ⟨j, l⟩ <;>
    fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [anticommutesAxis, pauliWord, pauliAt, gamma,
      pauli1, pauli2, pauli3, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Complex.I_mul_I]

theorem pauliWord_rightAxis_trace_product (u v : WordIndex) (μ : Fin 4) :
    Matrix.trace ((pauliWord u * gamma μ)ᴴ * (pauliWord v * gamma μ)) =
      if u = v then 4 else 0 := by
  rw [Matrix.conjTranspose_mul, gamma_herm, pauliWord_hermitian]
  calc
    Matrix.trace ((gamma μ * pauliWord u) * (pauliWord v * gamma μ)) =
        Matrix.trace (gamma μ * (pauliWord u * pauliWord v) * gamma μ) := by
          congr 1
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((gamma μ * gamma μ) *
        (pauliWord u * pauliWord v)) := by
          rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace (pauliWord u * pauliWord v) := by
          rw [gamma_sq, Matrix.one_mul]
    _ = if u = v then 4 else 0 := pauliWord_trace_product u v

def twistedSynthesis (μ : Fin 4) (c : WordIndex → ℂ) : Matrix C4 C4 ℂ :=
  ∑ w, c w • (pauliWord w * gamma μ)

theorem twistedSynthesis_trace_square (μ : Fin 4) (c : WordIndex → ℂ) :
    Matrix.trace ((twistedSynthesis μ c)ᴴ * twistedSynthesis μ c) =
      4 * ∑ w, star (c w) * c w := by
  classical
  unfold twistedSynthesis
  rw [Matrix.conjTranspose_sum, Finset.sum_mul]
  simp_rw [Matrix.mul_sum, Matrix.trace_sum,
    Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_smul, pauliWord_rightAxis_trace_product]
  simp
  calc
    ∑ w, star (c w) * c w * 4 =
        (∑ w, star (c w) * c w) * 4 :=
      (Finset.sum_mul Finset.univ (fun w => star (c w) * c w) 4).symm
    _ = 4 * ∑ w, star (c w) * c w := mul_comm _ _

theorem pauliSynthesis_trace_square (c : WordIndex → ℂ) :
    Matrix.trace ((pauliSynthesis c)ᴴ * pauliSynthesis c) =
      4 * ∑ w, star (c w) * c w := by
  classical
  unfold pauliSynthesis
  rw [Matrix.conjTranspose_sum, Finset.sum_mul]
  simp_rw [Matrix.mul_sum, Matrix.trace_sum,
    Matrix.conjTranspose_smul,
    pauliWord_hermitian, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.trace_smul, pauliWord_trace_product]
  simp
  calc
    ∑ w, star (c w) * c w * 4 =
        (∑ w, star (c w) * c w) * 4 :=
      (Finset.sum_mul Finset.univ (fun w => star (c w) * c w) 4).symm
    _ = 4 * ∑ w, star (c w) * c w := mul_comm _ _

def axisCoefficient (μ : Fin 4) (c : WordIndex → ℂ) (w : WordIndex) : ℂ :=
  if anticommutesAxis w μ then 2 * c w else 0

theorem pauliSynthesis_commutator (μ : Fin 4) (c : WordIndex → ℂ) :
    pauliSynthesis c * gamma μ - gamma μ * pauliSynthesis c =
      twistedSynthesis μ (axisCoefficient μ c) := by
  classical
  unfold pauliSynthesis twistedSynthesis
  rw [Finset.sum_mul, Matrix.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hanti : anticommutesAxis w μ = true
  · have hrel := pauliWord_axis_relation w μ
    simp [hanti] at hrel
    rw [Matrix.smul_mul, Matrix.mul_smul, hrel]
    simp [axisCoefficient, hanti]
    module
  · have hfalse : anticommutesAxis w μ = false := Bool.eq_false_of_not_eq_true hanti
    have hrel := pauliWord_axis_relation w μ
    simp [hfalse] at hrel
    rw [Matrix.smul_mul, Matrix.mul_smul, hrel]
    simp [axisCoefficient, hfalse]

end

end CliffordPauliWordSpectralCertificate
end NCG
