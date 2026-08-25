/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The determinant–incidence retraction

Machinery for `thm:SM-active-determinant-incidence` (SM.0s–SM.0t) in explicit
up-incidence coordinates: the determinant line `𝒟 = (det C ⊗ det W₂)*` is a scalar
line, an up-incidence shadow is a coefficient array `T a i j p` (colour argument
`a`, two weak arguments `i j`, and the `Λ²C*` pair label `p` identified with its
complementary colour index), and the determinant seed embedding is

`(Θ_τ) a i j p = τ · s a · ε i j · δ_{a p}`

with `s` the colour complement sign and `ε` the weak Levi-Civita symbol.

* `alternation_retracts` (SM.0s): the normalized complete alternation `𝔄` recovers
  the seed, `𝔄(Θ_τ) = τ`;
* `theta_norm` (SM.0s): `‖Θ_τ‖² = 6‖τ‖²` — the boxed Hilbert–Schmidt weight;
* `theta_of_alternating`: `Θ ∘ 𝔄` is the identity on the fully alternating line,
  so `Θ` and `𝔄` restrict to inverse isomorphisms;
* `mdet_pos_iff` (SM.0t): `m_det(T) = ‖𝔄T‖²` is positive exactly when a nonzero
  determinant seed occurs, and the seed is reconstructed as `τ = 𝔄T`.
-/

open Finset

namespace NCG
namespace DetIncidence

/-- The weak Levi-Civita symbol on `Fin 2`. -/
def eps2 : Fin 2 → Fin 2 → ℂ := ![![0, 1], ![-1, 0]]

/-- The colour complement sign `s a = ε(a, pair a)`. -/
def csign : Fin 3 → ℂ := ![1, -1, 1]

/-- An up-incidence shadow: colour argument, two weak arguments, pair label. -/
def Shadow : Type := Fin 3 → Fin 2 → Fin 2 → Fin 3 → ℂ

/-- The determinant seed embedding `Θ`. -/
def theta (τ : ℂ) : Shadow :=
  fun a i j p => τ * csign a * eps2 i j * (if a = p then 1 else 0)

/-- The normalized complete alternation `𝔄`. -/
noncomputable def alt (T : Shadow) : ℂ :=
  (6 : ℂ)⁻¹ * ∑ a : Fin 3, ∑ i : Fin 2, ∑ j : Fin 2,
    csign a * eps2 i j * T a i j a

/-- The determinant occurrence weight `m_det` (SM.0t). -/
noncomputable def mdet (T : Shadow) : ℝ := Complex.normSq (alt T)

/-- The squared Hilbert–Schmidt weight of a shadow. -/
noncomputable def shadowNormSq (T : Shadow) : ℝ :=
  ∑ a : Fin 3, ∑ i : Fin 2, ∑ j : Fin 2, ∑ p : Fin 3,
    Complex.normSq (T a i j p)

/-- **SM.0s, retraction**: the alternation recovers the determinant seed. -/
theorem alternation_retracts (τ : ℂ) : alt (theta τ) = τ := by
  rw [alt]
  rw [show (∑ a : Fin 3, ∑ i : Fin 2, ∑ j : Fin 2,
      csign a * eps2 i j * theta τ a i j a) = 6 * τ from ?_]
  · field_simp
  · simp only [theta]
    rw [Fin.sum_univ_three]
    simp only [Fin.sum_univ_two]
    simp only [csign, eps2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (![(1 : ℂ), -1, 1]) 2 = 1 from rfl]
    simp only [if_true]
    ring

/-- **SM.0s, the boxed Hilbert–Schmidt weight**: `‖Θ_τ‖² = 6‖τ‖²`. -/
theorem theta_norm (τ : ℂ) : shadowNormSq (theta τ) = 6 * Complex.normSq τ := by
  rw [shadowNormSq]
  simp only [theta, csign, eps2, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [Complex.normSq_mul, Complex.normSq_zero, Complex.normSq_one,
    Complex.normSq_neg]
  simp only [eq_false (show ¬((0 : Fin 3) = 2) by decide),
    eq_false (show ¬((1 : Fin 3) = 2) by decide),
    eq_false (show ¬((2 : Fin 3) = 0) by decide),
    eq_false (show ¬((2 : Fin 3) = 1) by decide), if_false,
    show (![(1 : ℂ), -1, 1]) 2 = 1 from rfl]
  norm_num [Complex.normSq_mul]
  ring

/-- The fully alternating property of an up-incidence shadow. -/
def FullyAlternating (T : Shadow) : Prop :=
  ∃ τ : ℂ, T = theta τ

/-- **SM.0s, inverse isomorphisms**: `Θ ∘ 𝔄` is the identity on the fully
alternating line. -/
theorem theta_of_alternating {T : Shadow} (hT : FullyAlternating T) :
    theta (alt T) = T := by
  obtain ⟨τ, rfl⟩ := hT
  rw [alternation_retracts]

/-- **SM.0t**: the determinant occurrence weight is positive exactly when a
nonzero determinant seed occurs, and the seed is reconstructed as `τ = 𝔄T`. -/
theorem mdet_pos_iff {T : Shadow} (hT : FullyAlternating T) :
    0 < mdet T ↔ ∃ τ : ℂ, τ ≠ 0 ∧ T = theta τ := by
  constructor
  · intro hpos
    refine ⟨alt T, ?_, (theta_of_alternating hT).symm⟩
    intro hc
    rw [mdet, hc, Complex.normSq_zero] at hpos
    exact lt_irrefl 0 hpos
  · rintro ⟨τ, hτ, rfl⟩
    rw [mdet, alternation_retracts]
    exact Complex.normSq_pos.mpr hτ

end DetIncidence
end NCG
