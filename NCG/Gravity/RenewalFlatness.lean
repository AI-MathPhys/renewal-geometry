/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Renewal flatness (exact)

Exact formalization of `thm:renewal-flatness`: on the
four-dimensional pure-deficiency branch with the
curvature-locked memory
`ℳ = 16πG·ε²(6c₁+2c₂)·u(2H²-u)`, the spatial-curvature
constraint factorizes as `u·[1-Φ(u)] = 0` with
`Φ(u) = 16πG·ε²(6c₁+2c₂)(2H²-u)`, and:

* `renewal_flatness_factorization`: the constraint
  `u = Φ(u)·u` is **equivalent** to the boxed factorization
  `u·(1-Φ(u)) = 0` (exact ring identity);
* `renewal_flatness_unique`: if `|Φ| < 1` on the validity
  window then `u = 0` is the unique controlled solution —
  the algebraic alternative `Φ = 1` is excluded;
* `renewal_flatness_stable`: with a nonzero remainder `r`
  (`u·(1-Φ(u)) = r`, `|r| ≤ R₀₀`), the stable bound
  `|u| ≤ (1-supΦ)⁻¹·R₀₀` holds;
* `renewal_flatness_discrete`: exact discreteness of the
  spatial curvature (`u = k/a²`, `k ∈ ℤ`) recovers `k = 0`
  whenever the stable bound is below `1/a²`.

The locked-memory constraint itself (the coefficient
combination `6c₁+2c₂` with `c₃` dropping and
`c₄(∇λ)² = 0`) is the framework input from
`def:effective-action` on the constant-rate branch
(disclosed); the factorization, uniqueness, stability, and
discreteness chain — the theorem's conclusions — are derived.
-/

namespace NCG
namespace Gravity

/-- **The boxed factorization**: the memory-locked constraint
`u = Φ(u)·u` holds iff `u·(1-Φ(u)) = 0`, with
`Φ(u) = C·(2H²-u)`. -/
theorem renewal_flatness_factorization (C H u : ℝ) :
    u = C * (2 * H ^ 2 - u) * u
      ↔ u * (1 - C * (2 * H ^ 2 - u)) = 0 := by
  constructor
  · intro h
    have := h
    nlinarith [h]
  · intro h
    nlinarith [h]

/-- **Uniqueness of the flat solution**: if the Wilson
combination satisfies `|Φ(u)| < 1` throughout the validity
window, then `u = 0` is the unique controlled solution of the
factorized constraint. -/
theorem renewal_flatness_unique (C H u : ℝ)
    (hΦ : |C * (2 * H ^ 2 - u)| < 1)
    (hcon : u * (1 - C * (2 * H ^ 2 - u)) = 0) :
    u = 0 := by
  rcases mul_eq_zero.mp hcon with h | h
  · exact h
  · exfalso
    have h1 : C * (2 * H ^ 2 - u) = 1 := by linarith
    rw [h1] at hΦ
    simp at hΦ

/-- **The stable bound**: with remainder `r = u·(1-Φ(u))`
bounded by `R₀₀` and `|Φ(u)| ≤ s < 1`, the curvature obeys
`|u| ≤ (1-s)⁻¹·R₀₀`. -/
theorem renewal_flatness_stable (Φu u r R₀₀ s : ℝ)
    (hΦ : |Φu| ≤ s) (hs : s < 1)
    (hcon : u * (1 - Φu) = r) (hr : |r| ≤ R₀₀) :
    |u| ≤ (1 - s)⁻¹ * R₀₀ := by
  have hs0 : 0 ≤ s := (abs_nonneg Φu).trans hΦ
  have hpos : 0 < 1 - s := by linarith
  have hlow : 1 - s ≤ |1 - Φu| := by
    have h1 := abs_le.mp hΦ
    rw [abs_of_pos (by linarith : (0:ℝ) < 1 - Φu)]
    linarith
  have hprod : |u| * (1 - s) ≤ |r| := by
    calc |u| * (1 - s) ≤ |u| * |1 - Φu| :=
          mul_le_mul_of_nonneg_left hlow (abs_nonneg u)
      _ = |u * (1 - Φu)| := (abs_mul u (1 - Φu)).symm
      _ = |r| := by rw [hcon]
  calc |u| ≤ R₀₀ / (1 - s) := by
        rw [le_div_iff₀ hpos]
        calc |u| * (1 - s) ≤ |r| := hprod
          _ ≤ R₀₀ := hr
    _ = (1 - s)⁻¹ * R₀₀ := by ring

/-- **Discreteness recovers exact flatness**: with `u = k/a²`
for integer `k` and the stable bound below `1/a²`, necessarily
`k = 0`. -/
theorem renewal_flatness_discrete (k : ℤ) (a B : ℝ)
    (ha : 0 < a)
    (hbound : |(k : ℝ)| / a ^ 2 ≤ B) (hB : B < 1 / a ^ 2) :
    k = 0 := by
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have habs : |(k : ℝ)| < 1 := by
    have h1 : |(k : ℝ)| / a ^ 2 < 1 / a ^ 2 :=
      lt_of_le_of_lt hbound hB
    rw [div_lt_div_iff_of_pos_right ha2] at h1
    exact h1
  have hk : (|k| : ℤ) < 1 := by
    exact_mod_cast (by rwa [← Int.cast_abs] at habs :
      ((|k| : ℤ) : ℝ) < 1)
  have hknn : (0 : ℤ) ≤ |k| := abs_nonneg k
  have hk0 : |k| = 0 := by omega
  exact abs_eq_zero.mp hk0

end Gravity
end NCG
