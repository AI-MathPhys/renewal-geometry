/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Lorentz.KreinClifford
import RenewalGeometry.Lorentz.AnchorClifford

/-!
# The Lorentzian principal square
  (`cor:supp-lorentzian-square`, emergent-spacetime manuscript)

With a coframe `E_h E_hᵀ = g_h⁻¹`, lapse `N_h` and shift `β_h`, the principal
symbol `eq:dirac-symbol-main`

  `σ_h(ξ) = γ⁰ N_h⁻¹(ξ₀ − β_h·ξ) + γᵃ (E_h)ₐⁱ ξᵢ`

squares to the scalar `eq:dirac-square-main`

  `σ_h(ξ)² = [ −N_h⁻²(ξ₀ − β_h·ξ)² + g_h^{ij} ξᵢ ξⱼ ] · 1`.

* `RenewalGeometry.signed_symbol_square` — the abstract square for any
  Lorentzian Clifford generators (`(γ⁰)² = −1`, `(γᵃ)² = 1`, mutually
  anticommuting);
* `RenewalGeometry.lorentzian_symbol_square` — the lapse/shift/coframe
  substitution yielding `eq:dirac-square-main` verbatim;
* `RenewalGeometry.anchor_lorentzian_symbol_square` — the same for the
  concrete depth-two anchor generators `γ⁰ = −iX_A⊗I`, `γ¹ = Z_A⊗Z_B`,
  `γ² = Z_A⊗Y_B`, `γ³ = Y_A⊗I` of `AnchorClifford.lean`;
* `RenewalGeometry.lorentzCharForm_inertia` — for `g_h ≻ 0` and `N_h > 0` the
  characteristic quadratic form is brought by the invertible substitution
  `ξ₀ = N η₀ + β·η`, `ξ = η` to the Sylvester block form `−η₀² + ηᵀ g⁻¹ η`
  (one negative line, `g⁻¹ ≻ 0` on the three spatial directions): inertia
  `(1, 3)` in the convention `(−, +, +, +)`. -/

open Matrix

namespace RenewalGeometry

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- **Abstract Lorentzian symbol square**: for generators with `(γ⁰)² = −1`,
`γ⁰γᵃ = −γᵃγ⁰` and `{γᵃ, γᵇ} = 2δᵃᵇ`,
`(ξ₀γ⁰ + Σ aᵢγᵢ)² = (−ξ₀² + Σ aᵢ²)·1` (`cor:supp-lorentzian-square`). -/
theorem signed_symbol_square {d : ℕ} (γ0 : A) (γ : Fin d → A)
    (hq : γ0 * γ0 = (-1 : ℝ) • 1)
    (hanti : ∀ i, γ0 * γ i = -(γ i * γ0))
    (hcliff : ∀ i j, γ i * γ j + γ j * γ i
      = (if i = j then (2 : ℝ) else 0) • 1)
    (ξ0 : ℝ) (a : Fin d → ℝ) :
    (ξ0 • γ0 + ∑ i, a i • γ i) * (ξ0 • γ0 + ∑ i, a i • γ i)
      = (-1 * ξ0 ^ 2 + ∑ i, a i ^ 2) • 1 := by
  have hcross : γ0 * (∑ i, a i • γ i) + (∑ i, a i • γ i) * γ0 = 0 := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add, hanti i]
    simp
  have hS := clifford_square γ hcliff a
  rw [add_mul, mul_add, mul_add]
  rw [smul_mul_smul_comm, hq, smul_smul]
  rw [smul_mul_assoc, mul_smul_comm, hS]
  have hcross' : ξ0 • (γ0 * ∑ i, a i • γ i)
      + ξ0 • ((∑ i, a i • γ i) * γ0) = 0 := by
    rw [← smul_add, hcross, smul_zero]
  calc (ξ0 * ξ0 * -1) • (1 : A)
        + ξ0 • (γ0 * ∑ i, a i • γ i)
        + (ξ0 • ((∑ i, a i • γ i) * γ0)
          + (∑ i, a i ^ 2) • 1)
      = (ξ0 * ξ0 * -1) • (1 : A) + (∑ i, a i ^ 2) • 1
        + (ξ0 • (γ0 * ∑ i, a i • γ i)
          + ξ0 • ((∑ i, a i • γ i) * γ0)) := by abel
    _ = (-1 * ξ0 ^ 2 + ∑ i, a i ^ 2) • 1 := by
        rw [hcross', add_zero, ← add_smul]
        congr 1
        ring

/-- The coframe contraction: with `E Eᵀ = g⁻¹` and `aₐ = Σᵢ Eᵢₐ ξᵢ`,
`Σₐ aₐ² = g^{ij} ξᵢ ξⱼ` (`cor:supp-lorentzian-square`, spatial square). -/
theorem coframe_square {d m : ℕ} (E : Matrix (Fin d) (Fin m) ℝ)
    (ginv : Matrix (Fin d) (Fin d) ℝ) (hE : E * Eᵀ = ginv) (ξ : Fin d → ℝ) :
    ∑ a, (∑ i, E i a * ξ i) ^ 2 = ξ ⬝ᵥ (ginv *ᵥ ξ) := by
  rw [← hE, ← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.vecMul, sq]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Corollary `cor:supp-lorentzian-square`, `eq:dirac-square-main`**: with
`E Eᵀ = g⁻¹`, the principal symbol
`σ(ξ) = γ⁰ N⁻¹(ξ₀ − β·ξ) + γᵃ Eᵢₐ ξᵢ` squares to
`[ −N⁻²(ξ₀ − β·ξ)² + g^{ij} ξᵢ ξⱼ ] · 1`. -/
theorem lorentzian_symbol_square {d m : ℕ} (γ0 : A) (γ : Fin m → A)
    (hq : γ0 * γ0 = (-1 : ℝ) • 1)
    (hanti : ∀ i, γ0 * γ i = -(γ i * γ0))
    (hcliff : ∀ i j, γ i * γ j + γ j * γ i
      = (if i = j then (2 : ℝ) else 0) • 1)
    (N : ℝ) (β ξ : Fin d → ℝ) (ξ0 : ℝ)
    (E : Matrix (Fin d) (Fin m) ℝ) (ginv : Matrix (Fin d) (Fin d) ℝ)
    (hE : E * Eᵀ = ginv) :
    ((N⁻¹ * (ξ0 - β ⬝ᵥ ξ)) • γ0 + ∑ a, (∑ i, E i a * ξ i) • γ a)
      * ((N⁻¹ * (ξ0 - β ⬝ᵥ ξ)) • γ0 + ∑ a, (∑ i, E i a * ξ i) • γ a)
      = (-(N⁻¹ * (ξ0 - β ⬝ᵥ ξ)) ^ 2 + ξ ⬝ᵥ (ginv *ᵥ ξ)) • 1 := by
  rw [signed_symbol_square γ0 γ hq hanti hcliff, coframe_square E ginv hE ξ]
  congr 1
  ring

section Anchor

/-- `gammaDir 0 = γ¹`. -/
lemma gammaDir_zero : gammaDir 0 = gamma1 := rfl

/-- `gammaDir 1 = γ²`. -/
lemma gammaDir_one : gammaDir 1 = gamma2 := rfl

/-- `gammaDir 2 = γ³`. -/
lemma gammaDir_two : gammaDir 2 = gamma3 := rfl

/-- `(γ⁰)² = −1` in scalar-multiple form. -/
lemma gamma0_sq_smul :
    gamma0 * gamma0
      = (-1 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  rw [gamma0_sq, neg_smul, one_smul]

/-- `γ⁰` anticommutes with every spatial generator. -/
lemma gamma0_anticomm (i : Fin 3) :
    gamma0 * gammaDir i = -(gammaDir i * gamma0) := by
  rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2) i
    with rfl | rfl | rfl
  · rw [gammaDir_zero]
    exact eq_neg_of_add_eq_zero_left gamma_anti_01
  · rw [gammaDir_one]
    exact eq_neg_of_add_eq_zero_left gamma_anti_02
  · rw [gammaDir_two]
    exact eq_neg_of_add_eq_zero_left gamma_anti_03

/-- Each spatial anchor generator squares to the identity. -/
lemma gammaDir_sq (i : Fin 3) : gammaDir i * gammaDir i = 1 := by
  rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2) i
    with rfl | rfl | rfl
  · rw [gammaDir_zero]; exact gamma1_sq
  · rw [gammaDir_one]; exact gamma2_sq
  · rw [gammaDir_two]; exact gamma3_sq

/-- Distinct spatial anchor generators anticommute. -/
lemma gammaDir_anticomm (i j : Fin 3) (h : i ≠ j) :
    gammaDir i * gammaDir j + gammaDir j * gammaDir i = 0 := by
  rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2) i
    with rfl | rfl | rfl <;>
  rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2) j
    with rfl | rfl | rfl <;>
  first
  | exact absurd rfl h
  | (rw [gammaDir_zero, gammaDir_one]
     first
     | exact gamma_anti_12
     | (rw [add_comm]; exact gamma_anti_12))
  | (rw [gammaDir_zero, gammaDir_two]
     first
     | exact gamma_anti_13
     | (rw [add_comm]; exact gamma_anti_13))
  | (rw [gammaDir_one, gammaDir_two]
     first
     | exact gamma_anti_23
     | (rw [add_comm]; exact gamma_anti_23))

/-- The spatial anchor generators satisfy the Euclidean Clifford relations
`{γᵃ, γᵇ} = 2δᵃᵇ`. -/
lemma gammaDir_cliff (i j : Fin 3) :
    gammaDir i * gammaDir j + gammaDir j * gammaDir i
      = (if i = j then (2 : ℝ) else 0)
        • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, gammaDir_sq, two_smul]
  · rw [if_neg h, zero_smul]
    exact gammaDir_anticomm i j h

/-- **Corollary `cor:supp-lorentzian-square`** for the concrete depth-two
anchor generators `eq:clifford-main`: the principal symbol
`eq:dirac-symbol-main` squares to `eq:dirac-square-main`. -/
theorem anchor_lorentzian_symbol_square (N : ℝ) (β ξ : Fin 3 → ℝ) (ξ0 : ℝ)
    (E ginv : Matrix (Fin 3) (Fin 3) ℝ) (hE : E * Eᵀ = ginv) :
    ((N⁻¹ * (ξ0 - β ⬝ᵥ ξ)) • gamma0
        + ∑ a, (∑ i, E i a * ξ i) • gammaDir a)
      * ((N⁻¹ * (ξ0 - β ⬝ᵥ ξ)) • gamma0
        + ∑ a, (∑ i, E i a * ξ i) • gammaDir a)
      = (-(N⁻¹ * (ξ0 - β ⬝ᵥ ξ)) ^ 2 + ξ ⬝ᵥ (ginv *ᵥ ξ))
        • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :=
  lorentzian_symbol_square gamma0 gammaDir gamma0_sq_smul gamma0_anticomm
    gammaDir_cliff N β ξ ξ0 E ginv hE

end Anchor

section Inertia

/-- The characteristic quadratic form of the principal symbol,
`Q(ξ₀, ξ) = −N⁻²(ξ₀ − β·ξ)² + ξᵀ g⁻¹ ξ` (`eq:dirac-square-main`). -/
noncomputable def lorentzCharForm {d : ℕ} (N : ℝ) (β : Fin d → ℝ)
    (ginv : Matrix (Fin d) (Fin d) ℝ) (ξ0 : ℝ) (ξ : Fin d → ℝ) : ℝ :=
  -(N⁻¹ * (ξ0 - β ⬝ᵥ ξ)) ^ 2 + ξ ⬝ᵥ (ginv *ᵥ ξ)

/-- **Corollary `cor:supp-lorentzian-square`, inertia clause**: for
`g⁻¹ ≻ 0` and `N > 0` the characteristic form has inertia `(1, d)` in the
convention `(−, +, …, +)`: the invertible substitution
`ξ₀ = N η₀ + β·η`, `ξ = η` (with inverse `η₀ = N⁻¹(ξ₀ − β·ξ)`) brings it to
the Sylvester block form `−η₀² + ηᵀ g⁻¹ η`; the time line `(1, 0)` is
negative and the form is positive definite on the `d`-dimensional graph
subspace `{(β·ξ, ξ)}`. -/
theorem lorentzCharForm_inertia {d : ℕ} (N : ℝ) (hN : 0 < N)
    (β : Fin d → ℝ) (ginv : Matrix (Fin d) (Fin d) ℝ)
    (hg : ∀ ξ : Fin d → ℝ, ξ ≠ 0 → 0 < ξ ⬝ᵥ (ginv *ᵥ ξ)) :
    -- Sylvester block form after the invertible substitution
    (∀ (η0 : ℝ) (η : Fin d → ℝ),
        lorentzCharForm N β ginv (N * η0 + β ⬝ᵥ η) η
          = -η0 ^ 2 + η ⬝ᵥ (ginv *ᵥ η))
    -- the substitution is invertible
    ∧ (∀ (ξ0 : ℝ) (ξ : Fin d → ℝ),
        N * (N⁻¹ * (ξ0 - β ⬝ᵥ ξ)) + β ⬝ᵥ ξ = ξ0)
    -- one negative (time) direction …
    ∧ lorentzCharForm N β ginv 1 0 < 0
    -- … and positive definiteness on the spatial graph subspace
    ∧ (∀ ξ : Fin d → ℝ, ξ ≠ 0 → 0 < lorentzCharForm N β ginv (β ⬝ᵥ ξ) ξ) := by
  have hNne : N ≠ 0 := ne_of_gt hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro η0 η
    unfold lorentzCharForm
    rw [add_sub_cancel_right, inv_mul_cancel_left₀ hNne]
  · intro ξ0 ξ
    rw [mul_inv_cancel_left₀ hNne, sub_add_cancel]
  · unfold lorentzCharForm
    simp only [dotProduct_zero, Matrix.mulVec_zero, sub_zero, mul_one,
      add_zero]
    have : 0 < N⁻¹ ^ 2 := by positivity
    linarith
  · intro ξ hξ
    unfold lorentzCharForm
    rw [sub_self, mul_zero]
    have := hg ξ hξ
    linarith

end Inertia

end RenewalGeometry
