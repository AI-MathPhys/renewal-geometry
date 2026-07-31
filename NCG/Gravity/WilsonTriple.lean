/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The worked-channel volume Wilson triple
  (`thm:triple`, GR_emergence)

The axis-averaged volume response of the isotropic compound-Poisson
channel, assembled from the declared isotropic direction averages
(`⟨R_uu⟩ = R/4`, `⟨R_uu²⟩ = (R² + 2Ric²)/24`,
`⟨4|Ric⁽³⁾|²⟩ = R²/6 + Ric²/2 + Riem²/4`) and the four-dimensional
decompositions `Ric² = S² + R²/4`,
`Riem² = Weyl² + 2S² + R²/6`:

* `worked_channel_triple` — the boxed chain
  `⟨Ψ⟩ = 7/6 R² + 13/6 Ric² - 1/4 Riem²
       = 5/3 R² + 5/3 S² - 1/4 C²`,
  so `(κ_R, κ_S, κ_C) ∝ (20, 20, -3)` on the one-parameter ray;
* `stelle_conversion` — the Stelle-basis triple
  `(c₁, c₂, c₃) = (κ_R - κ_S/4, κ_S, κ_C) = (5/4, 5/3, -1/4)
  ∝ (15, 20, -3)`.

The tensor-contraction identities producing the direction averages
from the isotropic moment formulas (checked against numerical random
curvature tensors in the manuscript) are the disclosed
tensor-algebra layer.
-/

namespace NCG

/-- `thm:triple` (assembly): the axis-averaged volume response in
both curvature bases. -/
theorem worked_channel_triple
    {R R2 Ric2 Riem2 S2 W2c PsiAvg T4Avg RuuAvg Ruu2Avg : ℝ}
    (hR2 : R2 = R ^ 2)
    (hRuu : RuuAvg = R / 4)
    (hRuu2 : Ruu2Avg = (R ^ 2 + 2 * Ric2) / 24)
    (hPsi : PsiAvg = 8 * (R ^ 2 - 4 * R * RuuAvg + 4 * Ruu2Avg)
      - T4Avg)
    (hT4 : T4Avg = 1 / 6 * R2 + 1 / 2 * Ric2 + 1 / 4 * Riem2)
    (hS : Ric2 = S2 + R2 / 4)
    (hW : Riem2 = W2c + 2 * S2 + R2 / 6) :
    PsiAvg = 7 / 6 * R2 + 13 / 6 * Ric2 - 1 / 4 * Riem2 ∧
      PsiAvg = 5 / 3 * R2 + 5 / 3 * S2 - 1 / 4 * W2c := by
  constructor
  · rw [hPsi, hRuu, hRuu2, hT4, hR2]
    ring
  · rw [hPsi, hRuu, hRuu2, hT4, hW, hS, hR2]
    ring

/-- `thm:triple` (Stelle conversion): `(c₁, c₂, c₃) =
(κ_R - κ_S/4, κ_S, κ_C) = (5/4, 5/3, -1/4) ∝ (15, 20, -3)`, and
`(κ_R, κ_S, κ_C) = (5/3, 5/3, -1/4) ∝ (20, 20, -3)`. -/
theorem stelle_conversion :
    ((5 : ℝ) / 3 - (5 / 3) / 4 = 5 / 4) ∧
      ((5 : ℝ) / 3, (5 : ℝ) / 3, -(1 : ℝ) / 4)
        = ((20 : ℝ) / 12, (20 : ℝ) / 12, -(3 : ℝ) / 12) ∧
      ((5 : ℝ) / 4, (5 : ℝ) / 3, -(1 : ℝ) / 4)
        = ((15 : ℝ) / 12, (20 : ℝ) / 12, -(3 : ℝ) / 12) := by
  norm_num

end NCG
