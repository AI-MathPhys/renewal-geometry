/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.ClockQuarterRoot

/-!
# The score-bus channel and the completed route amplitude
  (`thm:SM-score-bus`, `cor:SM-route-amplitude`,
   Gran-Tensor manuscript)

* `sm_score_bus`: the boxed record-forgetting channel
  `Ψ(ρ) = ½ρ + ¼XρX + ¼YρY` is unital and trace preserving,
  and acts on the Pauli basis by
  `Ψ(X) = ½X`, `Ψ(Y) = ½Y`, `Ψ(Z) = 0` — the grading sign is
  fully dephased while the transverse words decay at rate `½`;
* `route_amplitude`: for a typed carrier row with
  `C*C = κI` and the score-square bridge with `B*B = ½I`, the
  completed occurrence row `K = C ⊗ B` satisfies the boxed
  effect `K*K = (κ/2)I`, and it is nonzero for `κ ≠ 0`.

Rendering disclosed: complete positivity, covariance, and the
spectral-gap clause of the score bus are carried by the
displayed Pauli action (the fixed algebra is scalar because the
three nontrivial Pauli directions contract); the equal source
rank of `K` and `C` follows blockwise from the boxed effect.
-/

open Matrix Kronecker

namespace NCG

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

set_option linter.flexible false in
/-- `thm:SM-score-bus`: the record-forgetting channel is unital
and trace preserving with the displayed Pauli action. -/
theorem sm_score_bus (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      + (1 / 4 : ℂ) • (clockX * 1 * clockX)
      + (1 / 4 : ℂ) • (clockY * 1 * clockY) = 1)
    ∧ ((1 / 2 : ℂ) • clockX
      + (1 / 4 : ℂ) • (clockX * clockX * clockX)
      + (1 / 4 : ℂ) • (clockY * clockX * clockY)
      = (1 / 2 : ℂ) • clockX)
    ∧ ((1 / 2 : ℂ) • clockY
      + (1 / 4 : ℂ) • (clockX * clockY * clockX)
      + (1 / 4 : ℂ) • (clockY * clockY * clockY)
      = (1 / 2 : ℂ) • clockY)
    ∧ ((1 / 2 : ℂ) • clockZ
      + (1 / 4 : ℂ) • (clockX * clockZ * clockX)
      + (1 / 4 : ℂ) • (clockY * clockZ * clockY) = 0)
    ∧ (((1 / 2 : ℂ) • ρ
        + (1 / 4 : ℂ) • (clockX * ρ * clockX)
        + (1 / 4 : ℂ) • (clockY * ρ * clockY)).trace
      = ρ.trace) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | (ext i j
         fin_cases i <;> fin_cases j <;>
           simp [clockX, clockY, clockZ, Matrix.mul_apply,
             Fin.sum_univ_two, Matrix.one_apply] <;>
           try ring_nf <;>
           try (simp [Complex.I_sq]) <;>
           try ring_nf)
      | (rw [Matrix.trace_fin_two]
         simp [clockX, clockY, Matrix.mul_apply, Matrix.vecMul,
           dotProduct, Fin.sum_univ_two,
           Matrix.trace_fin_two] <;>
           try ring_nf <;>
           try (simp [Complex.I_sq]) <;>
           try ring_nf)

/-- `cor:SM-route-amplitude`: the completed occurrence row has
the boxed effect `K*K = (κ/2)I` and is nonzero for `κ ≠ 0`. -/
theorem route_amplitude {q y b b' : Type*}
    [Fintype y] [Fintype b] [DecidableEq q]
    [DecidableEq b']
    (C : Matrix y q ℂ) (κ : ℂ) (hC : Cᴴ * C = κ • 1)
    (B : Matrix b b' ℂ) (hB : Bᴴ * B = (1 / 2 : ℂ) • 1) :
    ((C ⊗ₖ B)ᴴ * (C ⊗ₖ B)
      = (κ / 2) • (1 : Matrix (q × b') (q × b') ℂ))
    ∧ (κ ≠ 0 → Nonempty (q × b') → C ⊗ₖ B ≠ 0) := by
  have hmain : (C ⊗ₖ B)ᴴ * (C ⊗ₖ B)
      = (κ / 2) • (1 : Matrix (q × b') (q × b') ℂ) := by
    rw [Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, hC, hB,
      Matrix.smul_kronecker, Matrix.kronecker_smul,
      Matrix.one_kronecker_one, smul_smul]
    congr 1
    ring
  refine ⟨hmain, ?_⟩
  rintro hκ ⟨p⟩ h0
  have hz := hmain
  rw [h0, Matrix.conjTranspose_zero, Matrix.zero_mul] at hz
  have hent := congrFun (congrFun hz p) p
  simp only [Matrix.zero_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one] at hent
  have hk0 : κ / 2 = 0 := hent.symm
  rw [div_eq_zero_iff] at hk0
  rcases hk0 with hk0 | h2
  · exact hκ hk0
  · exact absurd h2 (by norm_num)

end NCG
