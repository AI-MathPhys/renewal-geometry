/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.ExcursionInversion

/-!
# resolved-word Schur inversion

This file supplies the formal noncommutative generating-function packaging
for `thm:resolved-excursion-inversion`.  A formal series is represented by
its coefficient at every word in the free alphabet.  The recursion
`hiddenResolventApply` is coefficientwise multiplication by
`(I - D(z))^{-1} C(z)`, while `schurInverseApply` is coefficientwise left
multiplication by

`I - A(z) - B(z) (I - D(z))^{-1} C(z)`.

Thus `resolved_excursion_formal_schur_inverse` is the boxed identity

`X(z)^{-1} = I - A(z) - E(z)`,  `E(z) = B(z)(I-D(z))^{-1}C(z)`.

The coefficient theorem below also treats an arbitrary middle word, not
only a single middle letter.
-/

open Matrix

namespace NCG

variable {sigma n p : Type*} [Fintype n] [Fintype p]
  [DecidableEq n] [DecidableEq p]

/-- The identity series on the free alphabet: constant coefficient `I` and
all nonempty coefficients zero. -/
def formalWordUnit : List sigma -> Matrix n n Complex
  | [] => 1
  | _ :: _ => 0

/-- Coefficientwise action of `(I - D(z))^{-1} C(z)` on a word series `X`.
The defining recursion is the geometric-series expansion in noncommuting
letters. -/
def hiddenResolventApply (C : sigma -> Matrix p n Complex)
    (D : sigma -> Matrix p p Complex)
    (X : List sigma -> Matrix n n Complex) :
    List sigma -> Matrix p n Complex
  | [] => 0
  | a :: w => C a * X w + D a * hiddenResolventApply C D X w

/-- The coefficient series
`E(z) = B(z) (I - D(z))^{-1} C(z)`. -/
def excursionESeries (B : sigma -> Matrix n p Complex)
    (C : sigma -> Matrix p n Complex)
    (D : sigma -> Matrix p p Complex) :
    List sigma -> Matrix n n Complex
  | [] => 0
  | b :: w => B b * hiddenResolventApply C D formalWordUnit w

/-- Coefficientwise left multiplication of `X` by the Schur kernel
`I - A(z) - E(z)`. -/
def schurInverseApply (A : sigma -> Matrix n n Complex)
    (B : sigma -> Matrix n p Complex)
    (C : sigma -> Matrix p n Complex)
    (D : sigma -> Matrix p p Complex)
    (X : List sigma -> Matrix n n Complex) :
    List sigma -> Matrix n n Complex
  | [] => X []
  | b :: w => X (b :: w) - A b * X w
      - B b * hiddenResolventApply C D X w

lemma hiddenResolventApply_excursionX
    (A : sigma -> Matrix n n Complex)
    (B : sigma -> Matrix n p Complex)
    (C : sigma -> Matrix p n Complex)
    (D : sigma -> Matrix p p Complex) (w : List sigma) :
    hiddenResolventApply C D (excursionX A B C D) w
      = excursionH A B C D w := by
  induction w with
  | nil =>
      simp [hiddenResolventApply, excursionH_nil]
  | cons a w ih =>
      rw [hiddenResolventApply, ih, excursionH_cons]

/-- The full formal Schur-complement identity.  Equality is coefficientwise
over every word of the free (hence noncommutative) alphabet. -/
theorem resolved_excursion_formal_schur_inverse
    (A : sigma -> Matrix n n Complex)
    (B : sigma -> Matrix n p Complex)
    (C : sigma -> Matrix p n Complex)
    (D : sigma -> Matrix p p Complex) :
    schurInverseApply A B C D (excursionX A B C D)
      = formalWordUnit := by
  funext w
  cases w with
  | nil =>
      simp [schurInverseApply, formalWordUnit, excursionX_nil]
  | cons b w =>
      rw [schurInverseApply,
        hiddenResolventApply_excursionX A B C D w,
        excursionX_cons]
      simp [formalWordUnit]

lemma hiddenResolventApply_unit_append_singleton
    (C : sigma -> Matrix p n Complex)
    (D : sigma -> Matrix p p Complex)
    (u : List sigma) (a : sigma) :
    hiddenResolventApply C D formalWordUnit (u ++ [a])
      = (u.map D).prod * C a := by
  induction u with
  | nil =>
      simp [hiddenResolventApply, formalWordUnit]
  | cons d u ih =>
      have hunit : (formalWordUnit (u ++ [a]) : Matrix n n Complex) = 0 := by
        cases u <;> rfl
      simp only [List.cons_append, hiddenResolventApply,
        hunit, Matrix.mul_zero, zero_add, List.map_cons,
        List.prod_cons]
      rw [ih, Matrix.mul_assoc]

/-- Every coefficient of the excursion series is the corresponding
irreducible hidden excursion.  In particular, for a one-letter middle word
this is `E_[b,u,a] = B_b D_u C_a`. -/
theorem excursionESeries_coefficient
    (B : sigma -> Matrix n p Complex)
    (C : sigma -> Matrix p n Complex)
    (D : sigma -> Matrix p p Complex)
    (b a : sigma) (u : List sigma) :
    excursionESeries B C D (b :: (u ++ [a]))
      = B b * ((u.map D).prod * C a) := by
  rw [excursionESeries,
    hiddenResolventApply_unit_append_singleton C D u a]

/-- The displayed three-letter coefficient from the manuscript. -/
theorem excursionESeries_three_letter
    (B : sigma -> Matrix n p Complex)
    (C : sigma -> Matrix p n Complex)
    (D : sigma -> Matrix p p Complex)
    (b u a : sigma) :
    excursionESeries B C D [b, u, a] = B b * (D u * C a) := by
  simpa using excursionESeries_coefficient B C D b a [u]

end NCG
