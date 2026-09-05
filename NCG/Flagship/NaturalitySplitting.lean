/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Common-action naturality, Legendre reciprocity, and splitting
  (`thm:naturality-splitting`, flagship manuscript)

* `homogeneous_descendant`: (i) — a fixed homogeneous operation
  of degree `p` applied to the common class `χ·a₀` produces
  coefficient `χ^p` on every normalized descendant;
* `legendre_reciprocity`: (ii) — for the quadratic Lagrangian
  `L_χ(q,v) = (χ/2)bv² - χV`, completing the square gives the
  exact identity
  `pv - L_χ = (1/(2χ))(p²/b) + χV - (χb/2)(v - p/(χb))²`,
  so the supremum over `v` is attained at `v* = p/(χb)` with
  value `H_χ = (1/(2χ))(p²/b) + χV` — reciprocal coefficients
  `a = χ⁻¹`, `b = χ` with `ab = 1`;
* `loading_trichotomy`: (iii) — the loading difference satisfies
  exactly one of `D = 0`, `D = δI ≠ 0`, `D ∉ ℝI`.

Rendering disclosed: the nondegenerate-bilinear-form version of
(ii) is the same completing-square identity with `B⁻¹`; the
finite source polynomial discriminator `Δ_D(p)` in the third case
of (iii) is the manuscript's separate construction on the minimal
action-cyclic space.
-/

namespace NCG

/-- (i) Homogeneous descendants of the common class carry `χ^p`. -/
theorem homogeneous_descendant {A : Type*} [SMul ℝ A]
    (ℓ : A → ℝ) (pdeg : ℕ) (a0 : A) (χ : ℝ)
    (hhom : ∀ (t : ℝ) (x : A), ℓ (t • x) = t ^ pdeg * ℓ x)
    (hnorm : ℓ a0 = 1) :
    ℓ (χ • a0) = χ ^ pdeg := by
  rw [hhom, hnorm, mul_one]

/-- (ii) Legendre reciprocity by completing the square: the
supremum of `pv - L_χ(q,v)` is attained at `v* = p/(χb)` with
value `(1/(2χ))(p²/b) + χV`, so `a = χ⁻¹`, `b = χ`, `ab = 1`. -/
theorem legendre_reciprocity (χ b V pmom : ℝ) (hχ : 0 < χ)
    (hb : 0 < b) :
    (∀ v : ℝ, pmom * v - (χ / 2 * b * v ^ 2 - χ * V)
      ≤ 1 / (2 * χ) * (pmom ^ 2 / b) + χ * V)
    ∧ pmom * (pmom / (χ * b))
        - (χ / 2 * b * (pmom / (χ * b)) ^ 2 - χ * V)
      = 1 / (2 * χ) * (pmom ^ 2 / b) + χ * V
    ∧ χ⁻¹ * χ = 1 := by
  refine ⟨fun v => ?_, ?_, inv_mul_cancel₀ hχ.ne'⟩
  · have hkey : pmom * v - (χ / 2 * b * v ^ 2 - χ * V)
        = 1 / (2 * χ) * (pmom ^ 2 / b) + χ * V
          - χ * b / 2 * (v - pmom / (χ * b)) ^ 2 := by
      field_simp
      ring
    rw [hkey]
    nlinarith [sq_nonneg (v - pmom / (χ * b)),
      mul_pos hχ hb]
  · field_simp
    ring

/-- (iii) The loading-difference trichotomy: exactly one of
`D = 0`, `D = δ•1 ≠ 0`, or `D` is not a scalar. -/
theorem loading_trichotomy {n : Type*}
    [DecidableEq n] [Nonempty n] (D : Matrix n n ℝ) :
    D = 0 ∨ (∃ δ : ℝ, δ ≠ 0 ∧ D = δ • (1 : Matrix n n ℝ))
      ∨ ¬∃ δ : ℝ, D = δ • (1 : Matrix n n ℝ) := by
  by_cases h0 : D = 0
  · exact Or.inl h0
  by_cases hsc : ∃ δ : ℝ, D = δ • (1 : Matrix n n ℝ)
  · obtain ⟨δ, hδ⟩ := hsc
    refine Or.inr (Or.inl ⟨δ, ?_, hδ⟩)
    intro hδ0
    rw [hδ0, zero_smul] at hδ
    exact h0 hδ
  · exact Or.inr (Or.inr hsc)

end NCG
