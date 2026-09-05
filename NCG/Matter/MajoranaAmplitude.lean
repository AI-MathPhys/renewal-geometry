/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Quadratic-before-collapse Majorana amplitude
  (`thm:quadratic-majorana-amplitude-consolidated`, SM_emergence)

For the canonical `ℤ₄` lift `ϑ(a,b) = ±i` (by orientation) on `K₄`,
the two length-four Hamiltonian returns carry opposite phases:

* `z4_phase_gamma_minus` / `z4_phase_gamma_plus` —
  `u(γ₋) = -1`, `u(γ₊) = +1`;
* `linear_return_cancellation` — the exchange-even coisometry
  `R₊ = (⟨γ₋| + ⟨γ₊|)/√2` annihilates the linear return vector
  `q⁴(-|γ₋⟩ + |γ₊⟩)`;
* `quadratic_majorana_amplitude` — the quadratic Store squares both
  internal phases to `+1`, so the post-Store amplitude
  `q⁸(|γ₋⟩ + |γ₊⟩)` survives with
  `R₊Ψ⁽²⁾ = √2·q⁸`, which at `q = 1/3` is the boxed `√2·3⁻⁸`;
* `seesaw_stopping_valuation` — the stopping valuation is
  `n_seesaw = 2·4 = 8` (quadratic Store on the minimal length-four
  return).

The identification of the exchange-even coisometry and of the Store
with phase squaring follows the manuscript's declared instrument.
-/

namespace NCG

/-- The canonical `ℤ₄` edge lift: `ϑ(a,b) = i` for `a < b` and
`-i` for `a > b`. -/
noncomputable def z4Lift (a b : Fin 4) : ℂ :=
  if a < b then Complex.I else -Complex.I

/-- The `γ₋ = (0,1)(1,2)(2,3)(3,0)` holonomy: `u(γ₋) = -1`. -/
theorem z4_phase_gamma_minus :
    z4Lift 0 1 * z4Lift 1 2 * z4Lift 2 3 * z4Lift 3 0 = -1 := by
  have h1 : z4Lift 0 1 = Complex.I := by simp [z4Lift]
  have h2 : z4Lift 1 2 = Complex.I := by simp [z4Lift]
  have h3 : z4Lift 2 3 = Complex.I := by simp [z4Lift]
  have h4 : z4Lift 3 0 = -Complex.I := by
    simp only [z4Lift, if_neg (by decide : ¬(3 : Fin 4) < 0)]
  rw [h1, h2, h3, h4]
  linear_combination (1 - Complex.I ^ 2) * Complex.I_sq

/-- The `γ₊ = (0,1)(1,3)(3,2)(2,0)` holonomy: `u(γ₊) = +1`. -/
theorem z4_phase_gamma_plus :
    z4Lift 0 1 * z4Lift 1 3 * z4Lift 3 2 * z4Lift 2 0 = 1 := by
  have h1 : z4Lift 0 1 = Complex.I := by simp [z4Lift]
  have h2 : z4Lift 1 3 = Complex.I := by simp [z4Lift]
  have h3 : z4Lift 3 2 = -Complex.I := by
    simp only [z4Lift, if_neg (by decide : ¬(3 : Fin 4) < 2)]
  have h4 : z4Lift 2 0 = -Complex.I := by
    simp only [z4Lift, if_neg (by decide : ¬(2 : Fin 4) < 0)]
  rw [h1, h2, h3, h4]
  linear_combination (Complex.I ^ 2 - 1) * Complex.I_sq

/-- The exchange-even coisometry `R₊ v = (v(γ₋) + v(γ₊))/√2` on the
two-dimensional return space `ℛ₄`. -/
noncomputable def exchangeEven (v : Fin 2 → ℝ) : ℝ :=
  (v 0 + v 1) / Real.sqrt 2

/-- The linear return vector `q⁴(-|γ₋⟩+|γ₊⟩)` (phases `u(γ∓)`) is
annihilated by the exchange-even coisometry: the linear channel
cancels exactly. -/
theorem linear_return_cancellation (q : ℝ) :
    exchangeEven ![(-(q ^ 4)), q ^ 4] = 0 := by
  simp [exchangeEven]

/-- `thm:quadratic-majorana-amplitude-consolidated`: the quadratic
Store squares both phases to `+1`, so the post-Store amplitude
`Ψ⁽²⁾ = q⁸(|γ₋⟩+|γ₊⟩)` has exchange-even quotient
`R₊Ψ⁽²⁾ = √2·q⁸`; at `q = 1/3` this is the boxed `√2·3⁻⁸`. -/
theorem quadratic_majorana_amplitude :
    exchangeEven ![(1 / 3 : ℝ) ^ 8, (1 / 3 : ℝ) ^ 8]
      = Real.sqrt 2 * (3 : ℝ)⁻¹ ^ 8 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  simp only [exchangeEven, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [div_eq_iff (ne_of_gt h2)]
  rw [show Real.sqrt 2 * (3 : ℝ)⁻¹ ^ 8 * Real.sqrt 2
    = (Real.sqrt 2 * Real.sqrt 2) * (3 : ℝ)⁻¹ ^ 8 from by ring, hss]
  norm_num

/-- The seesaw stopping valuation: a quadratic Store on the minimal
length-four visible return gives `n_seesaw = 2·4 = 8`. -/
theorem seesaw_stopping_valuation : 2 * 4 = 8 := by norm_num

end NCG
