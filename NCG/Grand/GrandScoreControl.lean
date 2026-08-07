/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Score pulse control and the exact controlled-Z
  (`thm:canonical-score-control`, Gran-Tensor manuscript)

In the joint score–Store `Z` eigenframe (both operators
diagonal, entries `±1`):

* `scorePulse_group` / `scorePulse_zero`: the Ising pulses
  `E(θ) = exp(-iθZ_ε⊗Z_c)` form a one-parameter group — every
  `θ` is reached from the generating pulse, the algebraic form
  of "every `E(θ)` is physical";
* `scorePhase_kron_left` / `scorePhase_kron_right`: the local
  score and Store phases `e^{-itZ}` act as the two kickback
  factors on the joint frame;
* `score_control_cz`: the boxed exact gate —
  `CZ = e^{-iπ/4}·e^{iπZ_ε/4}·e^{iπZ_c/4}·e^{-iπZ_εZ_c/4}`.

Rendering disclosed: the derivation of the pulses from the
sourced pointer–score interaction and the branch-kickback
bookkeeping are the manuscript's control-model reading; the
dynamical `su(2)`-block generation clause on anticommuting
frequency supports is the separately proved predictive clock
discharge (`NCG.predictive_clock_discharge`), and the
identities above are the boxed operator content.
-/

open Matrix

set_option linter.unusedSimpArgs false
set_option linter.style.show false

namespace NCG

/-- Diagonal `Z` sign pattern. -/
def zSign : Fin 2 → ℂ := ![1, -1]

/-- The Ising score pulse `E(θ) = exp(-iθZ_ε⊗Z_c)` in the
joint eigenframe. -/
noncomputable def scorePulse (θ : ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal fun p =>
    Complex.exp (-(θ : ℂ) * Complex.I * (zSign p.1 * zSign p.2))

/-- The local phase `e^{-itZ}` in the `Z` eigenframe. -/
noncomputable def scorePhase (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun i => Complex.exp (-(t : ℂ) * Complex.I * zSign i)

/-- The controlled-`Z` gate in the joint eigenframe. -/
def czGate : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal fun p => if p.1 = 1 ∧ p.2 = 1 then -1 else 1

private lemma exp_neg_pi_I : Complex.exp (-(Real.pi * Complex.I)) = -1 := by
  rw [Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]

/-- The identity pulse. -/
theorem scorePulse_zero : scorePulse 0 = 1 := by
  rw [scorePulse]
  rw [show (Matrix.diagonal fun p : Fin 2 × Fin 2 =>
      Complex.exp (-((0 : ℝ) : ℂ) * Complex.I
        * (zSign p.1 * zSign p.2)))
      = Matrix.diagonal fun _ : Fin 2 × Fin 2 => (1 : ℂ) from by
    congr 1
    funext p
    rw [show -((0 : ℝ) : ℂ) * Complex.I
        * (zSign p.1 * zSign p.2) = 0 from by push_cast; ring]
    exact Complex.exp_zero]
  exact Matrix.diagonal_one

/-- The pulses form a one-parameter group: every `θ` is
physical from the generating pulse. -/
theorem scorePulse_group (θ₁ θ₂ : ℝ) :
    scorePulse θ₁ * scorePulse θ₂ = scorePulse (θ₁ + θ₂) := by
  rw [scorePulse, scorePulse, scorePulse,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The local score phase is the left kickback factor. -/
theorem scorePhase_kron_left (t : ℝ) :
    Matrix.kroneckerMap (· * ·) (scorePhase t)
        (1 : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.diagonal fun p : Fin 2 × Fin 2 =>
          Complex.exp (-(t : ℂ) * Complex.I * zSign p.1) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i = j <;> by_cases hab : a = b <;>
    simp [scorePhase, Matrix.kroneckerMap_apply,
      Matrix.diagonal_apply, Matrix.one_apply, hij, hab,
      Prod.ext_iff]

/-- The local Store phase is the right kickback factor. -/
theorem scorePhase_kron_right (t : ℝ) :
    Matrix.kroneckerMap (· * ·)
        (1 : Matrix (Fin 2) (Fin 2) ℂ) (scorePhase t)
      = Matrix.diagonal fun p : Fin 2 × Fin 2 =>
          Complex.exp (-(t : ℂ) * Complex.I * zSign p.2) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i = j <;> by_cases hab : a = b <;>
    simp [scorePhase, Matrix.kroneckerMap_apply,
      Matrix.diagonal_apply, Matrix.one_apply, hij, hab,
      Prod.ext_iff]

/-- `thm:canonical-score-control`, boxed display: the exact
controlled-`Z` as a scalar phase times two local quarter
phases times one Ising quarter pulse. -/
theorem score_control_cz :
    czGate = Complex.exp (-((Real.pi / 4 : ℝ) : ℂ) * Complex.I) •
      ((Matrix.diagonal fun p : Fin 2 × Fin 2 =>
          Complex.exp (-((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I
            * zSign p.1))
        * (Matrix.diagonal fun p : Fin 2 × Fin 2 =>
            Complex.exp (-((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I
              * zSign p.2))
        * scorePulse (Real.pi / 4)) := by
  rw [scorePulse, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul, czGate]
  congr 1
  funext p
  obtain ⟨i, j⟩ := p
  fin_cases i <;> fin_cases j <;>
    simp only [zSign, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
  · show (1 : ℂ) = _
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    convert Complex.exp_zero.symm using 2
    push_cast
    ring
  · show (1 : ℂ) = _
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    convert Complex.exp_zero.symm using 2
    push_cast
    ring
  · show (1 : ℂ) = _
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    convert Complex.exp_zero.symm using 2
    push_cast
    ring
  · show (-1 : ℂ) = _
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    convert exp_neg_pi_I.symm using 2
    push_cast
    ring

end NCG
