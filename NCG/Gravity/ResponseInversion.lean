/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Direction-moment inversion and the adiabatic register
  (`thm:u-tomography`, `thm:adiabatic-dark-energy`, GR_emergence)

* `u_tomography_inversion` — the unconditional inversion clause of
  the direction-moment tomography: if the moment matrix `𝖦` is
  invertible, the three direction moments reconstruct the Wilson
  triple exactly, `c = 𝖦⁻¹Θ`;
* `calibrated_hubble` — the frozen-diamond calibration `dH = B`
  gives `H = B/d` exactly;
* `adiabatic_w_bound` — the sharp form of the boxed
  `w_B = -1 - 2Ḃ/B² + O(...)`: under the adiabatic bound
  `|Ḃ|/B² ≤ δ`, the deficiency equation of state satisfies
  `|w_B + 1| ≤ 2δ` (with `w_B` from the proved
  `prop:deficiency-eos-identities`).

The multipole-independence argument for `det 𝖦 ≠ 0` (distinct
`ℓ = 0, 2, 4` content) and the higher-order adiabatic remainders are
the declared analytic inputs.
-/

namespace NCG

/-- `thm:u-tomography` (unconditional inversion): an invertible
moment matrix reconstructs the coefficient triple from the direction
moments. -/
theorem u_tomography_inversion {n : ℕ}
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : IsUnit G.det)
    (c Theta : Fin n → ℝ) (h : Theta = G.mulVec c) :
    c = G⁻¹.mulVec Theta := by
  rw [h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hG,
    Matrix.one_mulVec]

/-- `thm:adiabatic-dark-energy` (exact calibration): the
frozen-diamond calibration `dH = B` gives `H = B/d`. -/
theorem calibrated_hubble {B H dd : ℝ} (hd : dd ≠ 0)
    (hcal : dd * H = B) : H = B / dd := by
  rw [eq_div_iff hd]
  linarith [hcal]

/-- `thm:adiabatic-dark-energy` (sharp adiabatic bound): with the
proved equation-of-state identity `w_B = -1 - 2Ḃ/B²` and the
adiabatic hypothesis `|Ḃ|/B² ≤ δ`, the register sits within `2δ` of
the cosmological-constant value. -/
theorem adiabatic_w_bound {wB Bdot B delta : ℝ}
    (hw : wB = -1 - 2 * Bdot / B ^ 2)
    (hd : |Bdot| / B ^ 2 ≤ delta) :
    |wB + 1| ≤ 2 * delta := by
  have hval : wB + 1 = -(2 * (Bdot / B ^ 2)) := by
    rw [hw]
    ring
  rw [hval, abs_neg, abs_mul, abs_div,
    abs_of_nonneg (sq_nonneg B), abs_two]
  linarith [hd]

end NCG
