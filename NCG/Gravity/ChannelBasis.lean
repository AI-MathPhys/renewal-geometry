/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Four-dimensional channel basis and dynamical quotient
  (`thm:basis`, GR_emergence)

The four-dimensional identity
`Riem² = C² + 2Ric² - R²/3` converts the Euler density
`E₄ = Riem² - 4Ric² + R²` into
`E₄ = C² - 2Ric² + (2/3)R²`, equivalently
`C² = E₄ + 2Ric² - (2/3)R²`, so the four-derivative sector
`c₁R² + c₂Ric² + c₃C²` reduces modulo the topological density to the
two-parameter dynamical quotient `(α, β) = (c₁ - (2/3)c₃, c₂ + 2c₃)`:

* `euler_weyl_conversion` — both directions of the `E₄`/`C²`
  identity;
* `channel_basis_reduction` — the `(α, β, c₃)` re-expression of the
  quadratic sector;
* `dynamical_quotient_map` — the affine coefficient map and its
  invertibility (`c₁ = α + (2/3)c₃`, `c₂ = β - 2c₃`).

The Stelle classification (every parity-even quadratic curvature
scalar reduces to `Riem², Ric², R²` up to divergences) and the
topological invariance of `∫E₄` are the declared tensor-calculus
inputs; the scalar sector restrictions are bookkeeping.
-/

namespace NCG

/-- `thm:basis` (Euler–Weyl conversion): in four dimensions the
`Riem²` decomposition converts `E₄` and `C²` into each other. -/
theorem euler_weyl_conversion {Riem2 Ric2 R2 C2 E4 : ℝ}
    (hRiem : Riem2 = C2 + 2 * Ric2 - R2 / 3)
    (hE4 : E4 = Riem2 - 4 * Ric2 + R2) :
    E4 = C2 - 2 * Ric2 + 2 / 3 * R2
      ∧ C2 = E4 + 2 * Ric2 - 2 / 3 * R2 := by
  constructor
  · rw [hE4, hRiem]
    ring
  · rw [hE4, hRiem]
    ring

/-- `thm:basis` (dynamical quotient): the quadratic sector reduces to
`αR² + βRic² + c₃E₄` with `α = c₁ - (2/3)c₃`, `β = c₂ + 2c₃`. -/
theorem channel_basis_reduction {Riem2 Ric2 R2 C2 E4 : ℝ}
    (hRiem : Riem2 = C2 + 2 * Ric2 - R2 / 3)
    (hE4 : E4 = Riem2 - 4 * Ric2 + R2) (c1 c2 c3 : ℝ) :
    c1 * R2 + c2 * Ric2 + c3 * C2
      = (c1 - 2 / 3 * c3) * R2 + (c2 + 2 * c3) * Ric2 + c3 * E4 := by
  obtain ⟨_, hC2⟩ := euler_weyl_conversion hRiem hE4
  rw [hC2]
  ring

/-- `thm:basis` (coefficient map): the map
`(c₁, c₂) ↦ (α, β) = (c₁ - (2/3)c₃, c₂ + 2c₃)` is an affine
bijection at each fixed `c₃`. -/
theorem dynamical_quotient_map (c1 c2 c3 : ℝ) :
    (c1 - 2 / 3 * c3) + 2 / 3 * c3 = c1
      ∧ (c2 + 2 * c3) - 2 * c3 = c2 := by
  constructor <;> ring

end NCG
