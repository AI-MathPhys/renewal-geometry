/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandResidueMin
import NCG.Flagship.ClockQuarterRoot

/-!
# The portfolio of other loadings
  (`thm:other-loadings`, Gran-Tensor manuscript)

* `other_loadings`: the boxed typed-compression congruence —
  every component of a joint loading is the canonical positive
  compression `𝕂^δ = I*𝕂^J I` of the joint word-Gram hierarchy
  (positivity is preserved by compression); and conversely the
  separate component tensors do **not** determine the mixed
  cross kernels: two positive joint Grams with identical
  component compressions and different cross kernels are
  displayed.

Rendering disclosed: canonicity/flatness/source-minimality of
each component hierarchy restate its defining properties under
the compression congruence and are the manuscript's
bookkeeping over the proved clauses.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

set_option linter.unusedSimpArgs false
set_option linter.unusedFintypeInType false

/-- `thm:other-loadings`: typed compressions of a positive
joint hierarchy are positive, and the components do not
determine the cross kernels. -/
theorem other_loadings {J d : Type*} [Fintype J] [Fintype d]
    (K : Matrix J J ℂ) (hK : K.PosSemidef)
    (Icl : Matrix J d ℂ) :
    (Iclᴴ * K * Icl).PosSemidef
    ∧ (∃ K1 K2 : Matrix (Fin 2) (Fin 2) ℂ,
      K1.PosSemidef ∧ K2.PosSemidef
      ∧ K1 0 0 = K2 0 0 ∧ K1 1 1 = K2 1 1
      ∧ K1 ≠ K2) := by
  refine ⟨hK.conjTranspose_mul_mul_same Icl,
    Matrix.vecMulVec ![invSqrt2, 0]
        (star (![invSqrt2, 0] : Fin 2 → ℂ))
      + Matrix.vecMulVec ![0, invSqrt2]
        (star (![0, invSqrt2] : Fin 2 → ℂ)),
    Matrix.vecMulVec ![invSqrt2, invSqrt2]
      (star (![invSqrt2, invSqrt2] : Fin 2 → ℂ)),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (vecMulVec_psd _).add (vecMulVec_psd _)
  · exact vecMulVec_psd _
  · rw [Matrix.add_apply, Matrix.vecMulVec_apply,
      Matrix.vecMulVec_apply, Matrix.vecMulVec_apply]
    simp [Pi.star_apply, invSqrt2_star]
  · rw [Matrix.add_apply, Matrix.vecMulVec_apply,
      Matrix.vecMulVec_apply, Matrix.vecMulVec_apply]
    simp [Pi.star_apply, invSqrt2_star]
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    rw [Matrix.add_apply, Matrix.vecMulVec_apply,
      Matrix.vecMulVec_apply, Matrix.vecMulVec_apply] at h01
    simp only [Pi.star_apply] at h01
    rw [show (![invSqrt2, 0] : Fin 2 → ℂ) 0 = invSqrt2
        from rfl,
      show (![invSqrt2, 0] : Fin 2 → ℂ) 1 = 0 from rfl,
      show (![0, invSqrt2] : Fin 2 → ℂ) 0 = 0 from rfl,
      show (![0, invSqrt2] : Fin 2 → ℂ) 1 = invSqrt2
        from rfl,
      show (![invSqrt2, invSqrt2] : Fin 2 → ℂ) 0 = invSqrt2
        from rfl,
      show (![invSqrt2, invSqrt2] : Fin 2 → ℂ) 1 = invSqrt2
        from rfl, invSqrt2_star, star_zero] at h01
    rw [show invSqrt2 * invSqrt2 = (2⁻¹ : ℂ) from by
      have hsq := invSqrt2_sq
      rwa [pow_two] at hsq] at h01
    simp only [mul_zero, zero_mul, add_zero, zero_add] at h01
    norm_num at h01

end NCG
