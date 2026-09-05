/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Two phase settings reconstruct every ordered history kernel
  (`cor:canonical-two-phase-history-master`, flagship
   manuscript)

* `two_phase_polarization`: the boxed two-phase kernel identity
  `A*B = ½[(G₁ - D) - i(G_i - D)]` with marginal sum
  `D = A*A + B*B` and interference Grams
  `G_z = (A + zB)*(A + zB)` — the calibrated phase settings
  `z = 1` and `z = i` reconstruct every ordered history kernel
  `A*B` once the marginals are known, so the settings `-1, -i`
  are consistency checks, not independent premises.

Rendering disclosed: the physical production of the calibrated
amplitude `½(A + zB)` (controlled common dilation, scalar path
phase, erasure against the anchor) is the compiler record
`thm:canonical-history-compiler-master`; the reconstruction
identity itself is proved here exactly.
-/

open Matrix

namespace NCG

/-- `cor:canonical-two-phase-history-master`: the polarization
identity — phases `1` and `i` reconstruct the ordered kernel. -/
theorem two_phase_polarization {n p : Type*} [Fintype n]
    (A B : Matrix n p ℂ) :
    Aᴴ * B = (2 : ℂ)⁻¹ •
      (((A + B)ᴴ * (A + B) - (Aᴴ * A + Bᴴ * B))
        - Complex.I • ((A + Complex.I • B)ᴴ * (A + Complex.I • B)
            - (Aᴴ * A + Bᴴ * B))) := by
  have h1 : (A + B)ᴴ * (A + B) - (Aᴴ * A + Bᴴ * B)
      = Aᴴ * B + Bᴴ * A := by
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_add]
    abel
  have h2 : (A + Complex.I • B)ᴴ * (A + Complex.I • B)
      - (Aᴴ * A + Bᴴ * B)
      = Complex.I • (Aᴴ * B) + (-Complex.I) • (Bᴴ * A) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul]
    rw [Complex.star_def, Complex.conj_I]
    rw [smul_add, smul_smul]
    rw [show Complex.I * -Complex.I = (1 : ℂ) from by
      rw [mul_neg, Complex.I_mul_I, neg_neg]]
    rw [one_smul]
    abel
  rw [h1, h2, smul_add, smul_smul, smul_smul, Complex.I_mul_I]
  rw [show Complex.I * -Complex.I = 1 from by
    rw [mul_neg, Complex.I_mul_I, neg_neg]]
  rw [one_smul, neg_one_smul]
  match_scalars <;> ring

end NCG
