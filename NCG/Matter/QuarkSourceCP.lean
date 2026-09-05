/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact quark source spectrum and CP invariant
  (`thm:quark-source-CP`, SM_emergence)

The order-complete quark source operators
`D_u = (1+i)P₂₃P₁₃ + (1-i)P₁₃P₂₃` and
`D_d = (1-i)P₂₃P₁₂ + (1+i)P₁₂P₂₃`, expressed in the rational edge-
line (Gram) coordinates of the frame `u₁₂, u₁₃, u₂₃`:

* `quark_source_hermitian` — `G·D_u` and `G·D_d` are Hermitian
  (Hermiticity of the operators with respect to the frame inner
  product with Gram matrix `G`);
* `quark_source_charpoly` — the common characteristic polynomial is
  `λ(λ² - λ/2 - 3/8)`, so
  `spec D_f = {0, (1-√7)/4, (1+√7)/4}`;
* `quark_commutator` / `quark_source_cp_invariant` — the exact CP
  data `det[D_u,D_d] = i/32` and `Tr[D_u,D_d]³ = 3i/32`.

The identification of the Gram-coordinate matrices with the
orthonormal-frame projector form is the standard change-of-basis
step (all displayed quantities are basis-invariant, and
Hermiticity transports to `G`-Hermiticity); the exact `CB/BC`
phase pairing selecting the coefficients `1 ± i` is the declared
enumeration input.
-/

namespace NCG

open Matrix

/-- `D_u` in edge-line coordinates. -/
noncomputable def quarkDu : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0;
     -(1/4) + (1/4) * Complex.I, (1/4) - (1/4) * Complex.I,
       -(1/2) + (1/2) * Complex.I;
     (1/4) + (1/4) * Complex.I, -(1/2) - (1/2) * Complex.I,
       (1/4) + (1/4) * Complex.I]

/-- `D_d` in edge-line coordinates. -/
noncomputable def quarkDd : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(1/4) + (1/4) * Complex.I, -(1/4) - (1/4) * Complex.I,
       (1/2) + (1/2) * Complex.I;
     0, 0, 0;
     (1/2) - (1/2) * Complex.I, -(1/4) + (1/4) * Complex.I,
       (1/4) - (1/4) * Complex.I]

/-- The Gram matrix of the edge-line frame. -/
noncomputable def quarkGram : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, -(1/2), 1/2;
     -(1/2), 1, -(1/2);
     1/2, -(1/2), 1]

/-- The commutator `[D_u, D_d]` in edge-line coordinates. -/
noncomputable def quarkComm : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-(1/8) - (1/4) * Complex.I, (1/8) + (1/2) * Complex.I,
       -(1/4) - (1/4) * Complex.I;
     -(1/8) + (1/2) * Complex.I, (1/8) - (1/4) * Complex.I,
       -(1/4) + (1/4) * Complex.I;
     (1/8) + (1/4) * Complex.I, (1/8) - (1/4) * Complex.I,
       (1/2) * Complex.I]

/-- The square of the commutator. -/
noncomputable def quarkCommSq : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-(9/32) - (1/32) * Complex.I, (5/32) - (1/32) * Complex.I,
       -(1/16) - (1/8) * Complex.I;
     (5/32) + (1/32) * Complex.I, -(9/32) + (1/32) * Complex.I,
       (1/16) - (1/8) * Complex.I;
     (1/32) + (3/32) * Complex.I, -(1/32) + (3/32) * Complex.I,
       -(3/16)]

set_option linter.flexible false in
/-- Hermiticity of the sources with respect to the frame inner
product: `(G·D_f)ᴴ = G·D_f`. -/
theorem quark_source_hermitian :
    (quarkGram * quarkDu)ᴴ = quarkGram * quarkDu
      ∧ (quarkGram * quarkDd)ᴴ = quarkGram * quarkDd := by
  constructor <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [quarkGram, quarkDu, quarkDd, Matrix.mul_apply,
          Matrix.conjTranspose_apply, Fin.sum_univ_three,
          Complex.ext_iff] <;>
        norm_num

set_option linter.flexible false in
/-- The common characteristic polynomial:
`det(λ·1 - D_f) = λ(λ² - λ/2 - 3/8)`, so the spectrum is
`{0, (1-√7)/4, (1+√7)/4}`. -/
theorem quark_source_charpoly (lam : ℂ) :
    (lam • (1 : Matrix (Fin 3) (Fin 3) ℂ) - quarkDu).det
        = lam * (lam ^ 2 - lam / 2 - 3 / 8)
      ∧ (lam • (1 : Matrix (Fin 3) (Fin 3) ℂ) - quarkDd).det
        = lam * (lam ^ 2 - lam / 2 - 3 / 8) := by
  constructor <;>
    · rw [Matrix.det_fin_three]
      simp [quarkDu, quarkDd]
      linear_combination (3 * lam / 16) * Complex.I_sq

set_option linter.flexible false in
/-- The commutator identity `[D_u, D_d] = quarkComm` and its
square. -/
theorem quark_commutator :
    quarkDu * quarkDd - quarkDd * quarkDu = quarkComm
      ∧ quarkComm * quarkComm = quarkCommSq := by
  constructor <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [quarkDu, quarkDd, quarkComm, quarkCommSq,
          Matrix.mul_apply, Fin.sum_univ_three,
          Complex.ext_iff] <;>
        norm_num

/-- `thm:quark-source-CP` (CP invariant): the exact rephasing data
`det[D_u,D_d] = i/32` and `Tr[D_u,D_d]³ = 3i/32`: the microscopic
CP phase is exactly `+π/2`. -/
theorem quark_source_cp_invariant :
    quarkComm.det = Complex.I / 32
      ∧ (quarkCommSq * quarkComm).trace = 3 * Complex.I / 32 := by
  constructor
  · rw [Matrix.det_fin_three]
    norm_num [quarkComm, Complex.ext_iff, Matrix.cons_val_two,
      Matrix.vecTail, Matrix.vecHead]
  · rw [Matrix.trace_fin_three]
    norm_num [quarkComm, quarkCommSq, Matrix.mul_apply,
      Fin.sum_univ_three, Complex.ext_iff, Matrix.cons_val_two,
      Matrix.vecTail, Matrix.vecHead]

end NCG
