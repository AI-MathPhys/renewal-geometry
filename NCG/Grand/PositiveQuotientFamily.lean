/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Complete positive two-state quotient family
  (`thm:positive-renewal-quotient-family`,
  Gran-Tensor manuscript)

* `positive_renewal_quotient_family`: the anchored two-state
  no-completion family `Q(a) = [[a, 1-a],[c(a), d(a)]]` with
  the boxed formulas `d(a) = 8/15 - a`,
  `c(a) = (5a-1)(1-3a)/(15(1-a))`, `r_P(a) = 8/(15(1-a))`:
  (i) trace and determinant are family-constant
      (`tr = 8/15`, `det = 1/15`), so
      `spec Q(a) = {1/5, 1/3}` for every member;
  (ii) the first-return normalization
      `(1-a)·(1-c(a)-d(a)) = 8/15` — the numerator of the
      boxed transform `8z²/((5-z)(3-z))`;
  (iii) the boxed survivor-pencil identity
      `det(1 - z·Q(a)) = (1-z/5)(1-z/3)` for every `z`;
  (iv) positivity window: `c(a) ≥ 0` exactly on
      `1/5 ≤ a ≤ 1/3`, with the serial endpoints
      `c(1/5) = c(1/3) = 0`.

The general-cone reduction clause (any finite positive
first-return model with proper generating cone has a
two-dimensional quotient of this form) is the manuscript's
Krein–Rutman step over this explicit family.
-/

open Matrix

namespace NCG

/-- `thm:positive-renewal-quotient-family`. -/
theorem positive_renewal_quotient_family (a : ℚ)
    (ha1 : 1 / 5 ≤ a) (ha2 : a ≤ 1 / 3) :
    -- (i) constant trace and determinant
    (!![a, 1 - a;
        (5*a - 1)*(1 - 3*a)/(15*(1 - a)),
        8/15 - a] : Matrix (Fin 2) (Fin 2) ℚ).trace = 8/15
    ∧ (!![a, 1 - a;
        (5*a - 1)*(1 - 3*a)/(15*(1 - a)),
        8/15 - a] : Matrix (Fin 2) (Fin 2) ℚ).det = 1/15
    -- (ii) the first-return normalization
    ∧ (1 - a) * (1 - (5*a - 1)*(1 - 3*a)/(15*(1 - a))
        - (8/15 - a)) = 8/15
    -- (iii) the survivor-pencil identity
    ∧ (∀ z : ℚ,
        ((1 : Matrix (Fin 2) (Fin 2) ℚ)
          - z • !![a, 1 - a;
              (5*a - 1)*(1 - 3*a)/(15*(1 - a)),
              8/15 - a]).det
        = (1 - z/5) * (1 - z/3))
    -- (iv) the positivity window and serial endpoints
    ∧ 0 ≤ (5*a - 1)*(1 - 3*a)/(15*(1 - a))
    ∧ ((5*(1/5 : ℚ) - 1)*(1 - 3*(1/5))/(15*(1 - 1/5)) = 0
        ∧ (5*(1/3 : ℚ) - 1)*(1 - 3*(1/3))/(15*(1 - 1/3))
          = 0) := by
  have h1a : (1 : ℚ) - a ≠ 0 := by
    intro h
    have : a = 1 := by linarith
    rw [this] at ha2
    norm_num at ha2
  refine ⟨?_, ?_, ?_, ?_, ?_, by norm_num, by norm_num⟩
  · rw [Matrix.trace_fin_two_of]
    ring
  · rw [Matrix.det_fin_two_of]
    field_simp
    ring
  · field_simp
    ring
  · intro z
    have hentry : ((1 : Matrix (Fin 2) (Fin 2) ℚ)
        - z • !![a, 1 - a;
            (5*a - 1)*(1 - 3*a)/(15*(1 - a)),
            8/15 - a])
        = !![1 - z*a, -(z*(1 - a));
            -(z*((5*a - 1)*(1 - 3*a)/(15*(1 - a)))),
            1 - z*(8/15 - a)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hentry, Matrix.det_fin_two_of]
    field_simp
    ring
  · apply div_nonneg
    · nlinarith
    · nlinarith

end NCG
