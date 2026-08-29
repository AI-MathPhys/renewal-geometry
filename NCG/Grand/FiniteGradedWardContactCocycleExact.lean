/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteWardConsistencyOccurrenceExact

/-!
# Finite graded Ward contact cocycle

This file proves `thm:SMOS-Ward-contact-cocycle`: associativity and a graded
Ward--Leibniz identity force the contact cochain to satisfy the corresponding
triple-fusion cocycle identity.  It also contains the manuscript's explicit
two-idempotent counterexample showing that an independently acquired pair
contact table need not be a cocycle.
-/

namespace NCG
namespace FiniteGradedWardContactCocycle

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Curried bilinear multiplication. -/
abbrev BilinearProduct := E →ₗ[ℂ] E →ₗ[ℂ] E

/-- The graded Ward contact associator.  The scalar `sx` is the sign
`(-1)^(p |x|)` for the first homogeneous input. -/
def wardContactCocycle (mu c : BilinearProduct (E := E))
    (sx : ℂ) (x y z : E) : E :=
  mu (c x y) z + c (mu x y) z -
    sx • mu x (c y z) - c x (mu y z)

/-- Expanding the Ward identity on the two associative bracketings of a
triple product leaves exactly the graded contact-cocycle equation. -/
theorem wardContactCocycle_eq_zero
    (mu c : BilinearProduct (E := E)) (d : E →ₗ[ℂ] E)
    (sgn : E → ℂ)
    (hassoc : ∀ a b e, mu (mu a b) e = mu a (mu b e))
    (hsgn : ∀ a b, sgn (mu a b) = sgn a * sgn b)
    (hWard : ∀ a b,
      d (mu a b) = mu (d a) b + sgn a • mu a (d b) + c a b)
    (x y z : E) :
    wardContactCocycle mu c (sgn x) x y z = 0 := by
  have hbracket : d (mu (mu x y) z) = d (mu x (mu y z)) := by
    rw [hassoc]
  rw [hWard, hWard, hWard, hWard, hsgn] at hbracket
  simp only [map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_add, smul_smul] at hbracket
  simp only [hassoc] at hbracket
  let common : E :=
    mu (d x) (mu y z) +
      sgn x • mu x (mu (d y) z) +
      (sgn x * sgn y) • mu x (mu y (d z))
  have hreordered :
      common + (mu (c x y) z + c (mu x y) z) =
        common + (sgn x • mu x (c y z) + c x (mu y z)) := by
    calc
      common + (mu (c x y) z + c (mu x y) z) =
          mu (d x) (mu y z) + sgn x • mu x (mu (d y) z) +
            mu (c x y) z + (sgn x * sgn y) • mu x (mu y (d z)) +
            c (mu x y) z := by module
      _ = mu (d x) (mu y z) +
            (sgn x • mu x (mu (d y) z) +
              (sgn x * sgn y) • mu x (mu y (d z)) +
              sgn x • mu x (c y z)) + c x (mu y z) := hbracket
      _ = mu (d x) (mu y z) +
            sgn x • mu x (mu (d y) z) +
            (sgn x * sgn y) • mu x (mu y (d z)) +
            sgn x • mu x (c y z) + c x (mu y z) := by module
      _ = common + (sgn x • mu x (c y z) + c x (mu y z)) := by module
  have hcontact := add_left_cancel hreordered
  unfold wardContactCocycle
  rw [hcontact]
  module

/-! ### Explicit pair-contact counterexample -/

/-- The two minimal projections of `ℂ²`. -/
def e1 : Fin 2 → ℂ := fun i => if i = 0 then 1 else 0
def e2 : Fin 2 → ℂ := fun i => if i = 1 then 1 else 0

/-- Pointwise product on `ℂ²`. -/
def pointwiseProduct : BilinearProduct (E := Fin 2 → ℂ) where
  toFun x :=
    { toFun := fun y i => x i * y i
      map_add' := fun y z => by ext i; simp [mul_add]
      map_smul' := fun a y => by
        apply funext
        intro i
        change x i * (a * y i) = a * (x i * y i)
        ring }
  map_add' := fun x y => by
    apply LinearMap.ext
    intro z
    apply funext
    intro i
    change (x i + y i) * z i = x i * z i + y i * z i
    ring
  map_smul' := fun a x => by
    apply LinearMap.ext
    intro y
    apply funext
    intro i
    change (a * x i) * y i = a * (x i * y i)
    ring

/-- Pair contact supported only on `(e₁,e₁)`, written bilinearly as the
product of the first coordinates times `e₂`. -/
def pairContact : BilinearProduct (E := Fin 2 → ℂ) where
  toFun x :=
    { toFun := fun y => (x 0 * y 0) • e2
      map_add' := fun y z => by ext i; fin_cases i <;> simp [mul_add, e2]
      map_smul' := fun a y => by
        apply funext
        intro i
        fin_cases i <;> simp [e2] <;> ring }
  map_add' := fun x y => by
    apply LinearMap.ext
    intro z
    apply funext
    intro i
    fin_cases i <;> simp [add_mul, e2]
  map_smul' := fun a x => by
    apply LinearMap.ext
    intro y
    apply funext
    intro i
    fin_cases i <;> simp [e2] <;> ring

theorem e2_ne_zero : e2 ≠ (0 : Fin 2 → ℂ) := by
  intro h
  have := congrFun h 1
  norm_num [e2] at this

/-- The manuscript counterexample evaluates the ungraded contact associator
at `(e₁,e₁,e₂)` to the nonzero projection `e₂`. -/
theorem pairContact_not_cocycle :
    wardContactCocycle pointwiseProduct pairContact 1 e1 e1 e2 = e2 ∧
      wardContactCocycle pointwiseProduct pairContact 1 e1 e1 e2 ≠ 0 := by
  have heq : wardContactCocycle pointwiseProduct pairContact 1 e1 e1 e2 = e2 := by
    ext i
    fin_cases i <;>
      norm_num [wardContactCocycle, pointwiseProduct, pairContact, e1, e2]
  refine ⟨heq, ?_⟩
  intro hzero
  exact e2_ne_zero (heq.symm.trans hzero)

/-- Consolidated exact finite statement for `thm:SMOS-Ward-contact-cocycle`
and its advertised pair-contact separation. -/
theorem smos_Ward_contact_cocycle_exact :
    (∀ (mu c : BilinearProduct (E := E)) (d : E →ₗ[ℂ] E)
      (sgn : E → ℂ),
      (∀ a b e, mu (mu a b) e = mu a (mu b e)) →
      (∀ a b, sgn (mu a b) = sgn a * sgn b) →
      (∀ a b,
        d (mu a b) = mu (d a) b + sgn a • mu a (d b) + c a b) →
      ∀ x y z, wardContactCocycle mu c (sgn x) x y z = 0) ∧
    (wardContactCocycle pointwiseProduct pairContact 1 e1 e1 e2 = e2 ∧
      wardContactCocycle pointwiseProduct pairContact 1 e1 e1 e2 ≠ 0) :=
  ⟨fun mu c d sgn ha hs hw =>
      wardContactCocycle_eq_zero mu c d sgn ha hs hw,
    pairContact_not_cocycle⟩

end FiniteGradedWardContactCocycle
end NCG
