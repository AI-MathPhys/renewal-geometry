/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Positive averaging is Riemannian

The symbol-level positivity obstruction of the manuscript
(Proposition `prop:positive-averaging`): the second-moment tensor

`G = ∑ₐ pₐ · vₐ vₐᵀ`

of real reset directions `vₐ` with positive weights `pₐ` is **positive
semidefinite** — and positive *definite* when the directions span.  In
particular `G` can never have Lorentzian signature: positive completely
positive data, averaged with positive weights, remain Riemannian.  This is
the principal-symbol shadow of the operator-level positivity obstruction
(`NCG.IsFundamentalSymmetry.eq_one_of_krein_nonneg`), and it is what makes
the signed anti-renewal datum necessary rather than decorative.

## Main results

* `NCG.posSemidef_sum_outer` — Proposition `prop:positive-averaging`,
  positive-semidefiniteness of the averaged second moment;
* `NCG.quadratic_nonneg_sum_outer` — the quadratic form of the averaged
  second moment never takes negative values, so it has no timelike
  directions.
-/

namespace NCG

open Matrix

variable {m n : ℕ}

/-- **Proposition `prop:positive-averaging`** (positive averaging is
Riemannian): the second-moment matrix `∑ₐ pₐ • vₐ vₐᵀ` of a family of real
directions `vₐ` with nonnegative weights `pₐ` is positive semidefinite. -/
theorem posSemidef_sum_outer (p : Fin m → ℝ) (hp : ∀ a, 0 ≤ p a)
    (v : Fin m → Fin n → ℝ) :
    (∑ a, p a • vecMulVec (v a) (v a)).PosSemidef :=
  Matrix.posSemidef_sum _ fun a _ =>
    Matrix.PosSemidef.smul
      (by simpa using Matrix.posSemidef_vecMulVec_self_star (v a)) (hp a)

/-- The averaged second moment has no timelike direction: its quadratic
form is nonnegative everywhere, so no linear change of frame can bring it
to a Lorentzian form (which takes both signs).  This is the "no Lorentzian
signature from positive CP data" reading of Proposition
`prop:positive-averaging`. -/
theorem quadratic_nonneg_sum_outer (p : Fin m → ℝ) (hp : ∀ a, 0 ≤ p a)
    (v : Fin m → Fin n → ℝ) (x : Fin n →₀ ℝ) :
    0 ≤ x.sum fun i xi => x.sum fun j xj =>
      xi * (∑ a, p a • vecMulVec (v a) (v a)) i j * xj := by
  simpa using (posSemidef_sum_outer p hp v).2 x

end NCG
