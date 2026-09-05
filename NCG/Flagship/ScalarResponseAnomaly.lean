/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact scalar-response anomaly
  (`thm:scalar-response-anomaly-master`, flagship manuscript)

Directional (one-parameter) rendering of the Ward-departure
identity for `𝓡(q) = det q · c(q)`:

* `response_second_derivative`: the second derivative of the
  response `R = d·c` along the direction is
  `R'' = d''c + 2d'c' + dc''` (twice the product rule);
* `ward_departure`: the boxed anomaly identity — the departure of
  the normalized response Hessian from the pure determinant Ward
  tensor is exactly
  `R''/R - d''/d = -𝒲`,
  `𝒲 = -ℓ'' - (ℓ')² - 2θℓ'`,
  with `ℓ' = c'/c`, `ℓ'' = c''/c - (c'/c)²` (the identity
  `c⁻¹c'' = ℓ'' + (ℓ')²`) and `θ = d'/d` the determinant slope;
* `ward_vanishing`: if `Dℓ = 0` identically then the second
  derivative vanishes too, so `𝒲 = 0` — `Dℓ = 0` is sufficient
  for exact ADM balance.

Rendering disclosed: the bilinear polarization `𝒲_q(h,k)` is the
directional identity applied along `h + tk` (the manuscript's
two-direction display); the conjugacy criterion
`F(q) = U(q)F(q₀)U(q)*`, `U(q)e₀ = e^{iα(q)}e₀ ⇒ c` constant is
the displayed sufficient condition feeding `ward_vanishing`.
-/

namespace NCG

/-- Second derivative of the response `R = d·c` along the
direction: `R'' = d''c + 2d'c' + dc''`. -/
theorem response_second_derivative
    (d c d' c' : ℝ → ℝ) (dpp cpp : ℝ) (t : ℝ)
    (hd : ∀ s, HasDerivAt d (d' s) s)
    (hc : ∀ s, HasDerivAt c (c' s) s)
    (hd' : HasDerivAt d' dpp t) (hc' : HasDerivAt c' cpp t) :
    HasDerivAt (deriv fun s => d s * c s)
      (dpp * c t + 2 * (d' t * c' t) + d t * cpp) t := by
  have hR : (deriv fun s => d s * c s)
      = fun s => d' s * c s + d s * c' s := by
    funext s
    exact ((hd s).mul (hc s)).deriv
  rw [hR]
  have h2 := (hd'.mul (hc t)).add ((hd t).mul hc')
  exact h2.congr_deriv (by ring)

/-- `thm:scalar-response-anomaly-master`, boxed identity: the
departure of the normalized response Hessian from the pure
determinant Ward tensor is `-𝒲` with
`𝒲 = -ℓ'' - (ℓ')² - 2θℓ'`. -/
theorem ward_departure (dv dp dpp cv cp cpp : ℝ)
    (hd : dv ≠ 0) (hc : cv ≠ 0) :
    (dpp * cv + 2 * (dp * cp) + dv * cpp) / (dv * cv) - dpp / dv
      = -(-(cpp / cv - (cp / cv) ^ 2) - (cp / cv) ^ 2
          - 2 * (dp / dv) * (cp / cv)) := by
  field_simp
  ring

/-- `Dℓ = 0` kills the anomaly: if the log-slope vanishes
identically, its derivative vanishes too, so `𝒲 = 0`. -/
theorem ward_vanishing (c' : ℝ → ℝ) (cpp : ℝ) (t : ℝ)
    (hzero : ∀ s, c' s = 0) (hc' : HasDerivAt c' cpp t) :
    cpp = 0 := by
  have h0 : HasDerivAt (fun _ : ℝ => (0:ℝ)) cpp t := by
    have heq : c' = fun _ : ℝ => (0:ℝ) := funext hzero
    exact heq ▸ hc'
  exact h0.unique (hasDerivAt_const t 0)

end NCG
