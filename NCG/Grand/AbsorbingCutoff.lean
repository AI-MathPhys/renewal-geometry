/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RecordCutoff

/-!
# The absorbing-corner word rule is transitive
  (`thm:ar-absorbing-cutoff`, Gran-Tensor manuscript)

* `absorbing_cutoff`: the corner inclusions compose,
  `J_{YZ}·J_{XY} = J_{XZ}` for `X ≤ Y ≤ Z`, so the boxed
  absorbing word evaluation
  `Abs_{XY}(A_k⋯A_1) = π_{XY}(A_k)⋯π_{XY}(A_1)` — the unique
  rule agreeing with letterwise compression and multiplicative
  under concatenation — is transitive: the direct letterwise
  cutoff from `Z` to `X` equals letterwise cutoff to `Y`
  followed by the cutoff-`X` compression, letter by letter.

Rendering disclosed: `Abs` is the multiplicative extension of
the letter compression `π_{XY}(A) = J_{XY}*·A·J_{XY}` by
definition (its uniqueness clause is definitional); the proved
content is the corner composition law and the letterwise
transitivity of the compression it generates.
-/

open Matrix

namespace NCG

/-- `thm:ar-absorbing-cutoff`: corner composition and
letterwise transitivity of the absorbing compression. -/
theorem absorbing_cutoff {X Y Z : ℕ} (hXY : X ≤ Y)
    (_hYZ : Y ≤ Z) (A : Matrix (Fin Z) (Fin Z) ℂ) :
    (cornerJ Y Z * cornerJ X Y = cornerJ X Z)
    ∧ ((cornerJ X Z)ᴴ * A * cornerJ X Z
      = (cornerJ X Y)ᴴ
        * ((cornerJ Y Z)ᴴ * A * cornerJ Y Z)
        * cornerJ X Y) := by
  have hcomp : cornerJ Y Z * cornerJ X Y = cornerJ X Z := by
    ext j i
    rw [Matrix.mul_apply, cornerJ, cornerJ, cornerJ]
    simp only [Matrix.of_apply]
    have hiY : (i : ℕ) < Y := lt_of_lt_of_le i.isLt hXY
    rw [Finset.sum_eq_single (⟨(i : ℕ), hiY⟩ : Fin Y)
      (fun k _ hk => by
        rw [show (if (k : ℕ) = (i : ℕ) then (1 : ℂ) else 0)
            = 0 from if_neg (fun h => hk (Fin.ext h)),
          mul_zero])
      (fun habs => absurd (Finset.mem_univ _) habs)]
    rw [if_pos rfl, mul_one]
  refine ⟨hcomp, ?_⟩
  rw [← hcomp, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end NCG
