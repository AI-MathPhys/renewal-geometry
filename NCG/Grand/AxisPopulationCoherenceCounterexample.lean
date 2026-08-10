/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Axis populations do not determine qutrit coherence

This module constructs the two channel curves from
`cth:SMST-axis-populations-no-coherence`: a coherent unitary pulse and a
nonunitary random-unitary channel have the same transition probabilities on
all three distinguished axis projectors at every time.
-/

open Matrix Finset

namespace NCG

noncomputable section

/-- The involution swapping the first two qutrit axes and fixing the third. -/
def qutritSwap01 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 1]

/-- A coherent swap pulse on the first two axes, with the spectator-axis phase
fixed to one. -/
def qutritSwapPulse (t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(Real.cos t : ℂ), -(Complex.I * Real.sin t), 0;
     -(Complex.I * Real.sin t), (Real.cos t : ℂ), 0;
     0, 0, 1]

/-- Distinguished population projector of a qutrit score axis. -/
def qutritAxisProjector (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.single a a 1

/-- The coherent unitary channel. -/
def coherentSwapChannel (t : ℝ) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  qutritSwapPulse t * M * (qutritSwapPulse t)ᴴ

/-- The incoherent random-unitary channel with swap probability `sin² t`. -/
def randomSwapChannel (t : ℝ) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  (1 - Real.sin t ^ 2 : ℝ) • M
    + (Real.sin t ^ 2 : ℝ) •
      (qutritSwap01 * M * qutritSwap01ᴴ)

theorem qutritSwap01_unitary :
    qutritSwap01 * qutritSwap01ᴴ = 1
      ∧ qutritSwap01ᴴ * qutritSwap01 = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [qutritSwap01, Matrix.mul_apply, Fin.sum_univ_three]

theorem qutritSwapPulse_unitary (t : ℝ) :
    qutritSwapPulse t * (qutritSwapPulse t)ᴴ = 1
      ∧ (qutritSwapPulse t)ᴴ * qutritSwapPulse t = 1 := by
  have htrig := Real.sin_sq_add_cos_sq t
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [qutritSwapPulse, Matrix.mul_apply, Fin.sum_univ_three,
      Complex.ext_iff, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, pow_two,
      Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- Both channels have exactly the same full three-axis transition table for
every pulse time. -/
theorem axis_transition_tables_equal (t : ℝ) (a b : Fin 3) :
    coherentSwapChannel t (qutritAxisProjector a) b b
      = randomSwapChannel t (qutritAxisProjector a) b b := by
  have htrig := Real.sin_sq_add_cos_sq t
  fin_cases a <;> fin_cases b <;>
    simp [coherentSwapChannel, randomSwapChannel, qutritSwapPulse,
      qutritSwap01, qutritAxisProjector, Matrix.mul_apply,
      Fin.sum_univ_three, Complex.ext_iff, Complex.cos_ofReal_re,
      Complex.cos_ofReal_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, pow_two, Complex.mul_re,
      Complex.mul_im, Matrix.vecMul, dotProduct, Fin.isValue] <;> nlinarith

theorem randomSwapChannel_axis0 (t : ℝ) :
    randomSwapChannel t (qutritAxisProjector (0 : Fin 3))
      = !![(1 - Real.sin t ^ 2 : ℂ), 0, 0;
           0, (Real.sin t ^ 2 : ℂ), 0;
           0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [randomSwapChannel, qutritAxisProjector, qutritSwap01,
      Matrix.mul_apply, Fin.sum_univ_three, Complex.ext_iff,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, pow_two,
      Complex.mul_re, Complex.mul_im, Matrix.vecMul, dotProduct, Fin.isValue]

/-- On the open mixing branch the random channel sends a pure axis projector
to a non-idempotent matrix, so it cannot be a unitary conjugation. -/
theorem randomSwapChannel_not_unitary (t : ℝ)
    (hp0 : 0 < Real.sin t ^ 2) (hp1 : Real.sin t ^ 2 < 1) :
    ¬ ∃ V : Matrix (Fin 3) (Fin 3) ℂ,
        Vᴴ * V = 1 ∧
        ∀ M, randomSwapChannel t M = V * M * Vᴴ := by
  rintro ⟨V, hV, hchan⟩
  let P := qutritAxisProjector (0 : Fin 3)
  have hPid : P * P = P := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, qutritAxisProjector, Matrix.mul_apply, Fin.sum_univ_three]
  have hunitId : (V * P * Vᴴ) * (V * P * Vᴴ) = V * P * Vᴴ := by
    calc
      (V * P * Vᴴ) * (V * P * Vᴴ)
          = V * (P * (Vᴴ * V) * P) * Vᴴ := by noncomm_ring
      _ = V * P * Vᴴ := by
        rw [hV]
        simp only [Matrix.mul_one, Matrix.one_mul]
        rw [hPid]
  have hrandId : randomSwapChannel t P * randomSwapChannel t P
      = randomSwapChannel t P := by
    simpa [hchan P] using hunitId
  have haxis : randomSwapChannel t P
      = !![(1 - Real.sin t ^ 2 : ℂ), 0, 0;
           0, (Real.sin t ^ 2 : ℂ), 0;
           0, 0, 0] := randomSwapChannel_axis0 t
  rw [haxis] at hrandId
  have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0) hrandId
  have hre := congrArg Complex.re hentry
  simp [Matrix.mul_apply, Fin.sum_univ_three, pow_two, Complex.mul_re,
    Complex.mul_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im] at hre
  nlinarith

/-- Exact counterexample bundle: identical population data at every time, with
a genuinely nonunitary random-unitary member whenever `0 < sin² t < 1`. -/
theorem axis_populations_do_not_certify_coherence_exact :
    (∀ t a b,
      coherentSwapChannel t (qutritAxisProjector a) b b
        = randomSwapChannel t (qutritAxisProjector a) b b)
    ∧ (∀ t, 0 < Real.sin t ^ 2 → Real.sin t ^ 2 < 1 →
      ¬ ∃ V : Matrix (Fin 3) (Fin 3) ℂ,
          Vᴴ * V = 1 ∧
          ∀ M, randomSwapChannel t M = V * M * Vᴴ) := by
  exact ⟨axis_transition_tables_equal, randomSwapChannel_not_unitary⟩

end

end NCG
