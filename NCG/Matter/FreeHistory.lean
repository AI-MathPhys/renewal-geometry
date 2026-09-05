/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The isometric free-history ladder
  (`thm:free-history-isometry`, SM_emergence)

* `appendHistory` / `appendAdjoint` — appending one port outcome
  with its Kraus amplitude, and its adjoint;
* `append_adjoint_spec` — the adjoint identity
  `⟨ε ψ, φ⟩ = ⟨ψ, ε* φ⟩`;
* `append_isometry` — `ε* ε = I`: since the squared amplitudes of
  all children of a history sum to one, appending one recorded
  outcome is an isometry;
* `append_inner` — hence `⟨ε ψ, ε φ⟩ = ⟨ψ, φ⟩`;
* `weyl_quadratic` / `weyl_continued_fraction` — the free half-line
  Weyl function `U(z) = (z - √(z²-4))/2` satisfies
  `U² - zU + 1 = 0`, i.e. `U = (z - U)⁻¹` (the continued-fraction
  fixed point), for either square-root branch `w² = z² - 4`;
* `catalan_generating_quadratic` — the return-moment generating
  function `C(s) = Σ catalan(n)·sⁿ` satisfies `C = 1 + s·C²`, the
  first-return decomposition of the free chain's Catalan moments.

The identification of the full compressed resolvent
`L*(z-T)⁻¹L = U(z)·L*L` for wandering carrier vectors (the
spectral theory of the half-line Jacobi chain) is the declared
operator-theoretic layer and is not formalized here.
-/

namespace NCG

open Matrix

variable {H O : Type*} [Fintype H] [Fintype O]

private theorem star_mul_self_normSq' (z : ℂ) :
    star z * z = (Complex.normSq z : ℂ) := by
  rw [show (star z : ℂ) = (starRingEnd ℂ) z from rfl,
    mul_comm ((starRingEnd ℂ) z) z]
  exact Complex.mul_conj z

/-- Appending one port outcome with its Kraus amplitude: a state on
histories of length `n` is sent to a state on histories of length
`n + 1` (encoded as parent–outcome pairs). -/
noncomputable def appendHistory (amp : H → O → ℂ) (ψ : H → ℂ) :
    H × O → ℂ := fun p => amp p.1 p.2 * ψ p.1

/-- The adjoint of `appendHistory`: sum out the last recorded
outcome against the conjugate amplitude. -/
noncomputable def appendAdjoint (amp : H → O → ℂ)
    (φ : H × O → ℂ) : H → ℂ :=
  fun h => ∑ o, star (amp h o) * φ (h, o)

/-- `appendAdjoint` is the adjoint of `appendHistory`:
`⟨ε ψ, φ⟩ = ⟨ψ, ε* φ⟩`. -/
theorem append_adjoint_spec (amp : H → O → ℂ) (ψ : H → ℂ)
    (φ : H × O → ℂ) :
    ∑ p : H × O, star (appendHistory amp ψ p) * φ p
      = ∑ h, star (ψ h) * appendAdjoint amp φ h := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  simp only [appendHistory, appendAdjoint, star_mul']
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  ring

omit [Fintype H] in
/-- `thm:free-history-isometry` (ladder isometry): when the squared
child amplitudes at every history sum to one, `ε* ε = I`. -/
theorem append_isometry (amp : H → O → ℂ)
    (hamp : ∀ h, ∑ o, Complex.normSq (amp h o) = 1) (ψ : H → ℂ) :
    appendAdjoint amp (appendHistory amp ψ) = ψ := by
  funext h
  simp only [appendAdjoint, appendHistory]
  have hsum : ∑ o, star (amp h o) * (amp h o * ψ h)
      = (∑ o, (Complex.normSq (amp h o) : ℂ)) * ψ h := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro o _
    rw [← star_mul_self_normSq' (amp h o)]
    ring
  rw [hsum]
  have hone : (∑ o, (Complex.normSq (amp h o) : ℂ)) = 1 := by
    rw [← Complex.ofReal_sum, hamp h, Complex.ofReal_one]
  rw [hone, one_mul]

/-- Isometry of inner products: `⟨ε ψ, ε φ⟩ = ⟨ψ, φ⟩`. -/
theorem append_inner (amp : H → O → ℂ)
    (hamp : ∀ h, ∑ o, Complex.normSq (amp h o) = 1)
    (ψ φ : H → ℂ) :
    ∑ p : H × O, star (appendHistory amp ψ p)
        * appendHistory amp φ p
      = ∑ h, star (ψ h) * φ h := by
  rw [append_adjoint_spec amp ψ (appendHistory amp φ)]
  apply Finset.sum_congr rfl
  intro h _
  rw [append_isometry amp hamp φ]

/-- The free half-line Weyl function satisfies the quadratic
equation `U² - zU + 1 = 0`, for either branch `w² = z² - 4` of the
square root in `U = (z - w)/2`. -/
theorem weyl_quadratic (z w : ℂ) (hw : w ^ 2 = z ^ 2 - 4) :
    ((z - w) / 2) ^ 2 - z * ((z - w) / 2) + 1 = 0 := by
  linear_combination (1 / 4 : ℂ) * hw

/-- The continued-fraction fixed point: a root of `u² - zu + 1 = 0`
with `z - u ≠ 0` satisfies `u = (z - u)⁻¹`. -/
theorem weyl_continued_fraction (z u : ℂ)
    (hu : u ^ 2 - z * u + 1 = 0) (hne : z - u ≠ 0) :
    u = (z - u)⁻¹ := by
  have hmul : u * (z - u) = 1 := by linear_combination -hu
  field_simp
  linear_combination hmul

/-- First-return decomposition of the free chain's return moments:
the Catalan generating function satisfies `C = 1 + X·C²`. -/
theorem catalan_generating_quadratic :
    (PowerSeries.mk fun n => (catalan n : ℝ))
      = 1 + PowerSeries.X
        * (PowerSeries.mk fun n => (catalan n : ℝ)) ^ 2 := by
  ext n
  cases n with
  | zero => simp [PowerSeries.coeff_mk]
  | succ n =>
      rw [map_add, PowerSeries.coeff_mk, sq,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [PowerSeries.coeff_mk]
      rw [show ((PowerSeries.coeff (n + 1))
          (1 : PowerSeries ℝ) : ℝ) = 0 from by
        rw [PowerSeries.coeff_one]
        simp]
      rw [zero_add, catalan_succ]
      push_cast
      rw [← Fin.sum_univ_eq_sum_range]

end NCG
