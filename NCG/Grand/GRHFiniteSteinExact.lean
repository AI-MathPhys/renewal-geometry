/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite Stein criterion for the reconstructed zero shift

Exact encoding of `cor:GRH-finite-Stein` (GRH.23–GRH.24) together with the
node criterion (GRH.21) of `thm:GRH-finite-zero-tomography`.

* `node_unimodular_iff` (GRH.21): for `ζ_ρ = e^{τ(ρ - 1/2)}`, `τ > 0`,
  `|ζ_ρ| = 1 ⇔ Re ρ = 1/2`;
* the reconstructed shift on the visible recurrence carrier is the matrix
  `S = V · diag(ζ) · V⁻¹` diagonalized by the zero eigenframe `V`; its
  spectrum is the node set (GRH.23, `shift_mulVec_eigen`);
* `stein_of_unimodular`: unimodular nodes give the positive invariant metric
  `G = V⁻¹^* V⁻¹ ≻ 0` with `S^* G S = G`;
* `unimodular_of_stein`: a positive Stein solution forces every eigenvalue
  to have modulus one; hence (GRH.24)
  `Re ρ = 1/2 for all nodes ⇔ ∃ G ≻ 0, S^* G S = G` (`finite_stein_iff`);
* `invariant_metric_diagonal`: for distinct unimodular nodes every invariant
  metric is diagonal in the zero eigenframe (`V^* G V` is diagonal), so its
  condition number is controlled by the eigenframe, not by critical-line
  location alone.

Scope: the shift is taken in diagonalized form `S = V diag(ζ) V⁻¹` (the
manuscript's companion shift with distinct nodes is diagonalizable, with `V`
the Vandermonde eigenframe).
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace GRHFiniteStein

/-- **(GRH.21)**: `|e^{τ(ρ - 1/2)}| = 1 ⇔ Re ρ = 1/2` for `τ > 0`. -/
theorem node_unimodular_iff (τ : ℝ) (hτ : 0 < τ) (ρ : ℂ) :
    ‖Complex.exp ((τ : ℂ) * (ρ - 1 / 2))‖ = 1 ↔ ρ.re = 1 / 2 := by
  rw [Complex.norm_exp, Real.exp_eq_one_iff]
  have : ((τ : ℂ) * (ρ - 1 / 2)).re = τ * (ρ.re - 1 / 2) := by
    simp [Complex.mul_re]
  rw [this]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hτ.ne'
    · linarith
  · intro h
    rw [h]; ring

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The reconstructed shift in the zero eigenframe: `S = V diag(ζ) V⁻¹`. -/
noncomputable def shift (V : Matrix n n ℂ) (ζ : n → ℂ) : Matrix n n ℂ :=
  V * diagonal ζ * V⁻¹

/-- **(GRH.23)**: the columns of `V` are eigenvectors of the shift with the
nodes as eigenvalues. -/
theorem shift_mulVec_eigen (V : Matrix n n ℂ) (hV : IsUnit V.det) (ζ : n → ℂ) (j : n) :
    shift V ζ *ᵥ (V *ᵥ Pi.single j 1) = ζ j • (V *ᵥ Pi.single j 1) := by
  calc shift V ζ *ᵥ (V *ᵥ Pi.single j 1) = V *ᵥ (diagonal ζ *ᵥ Pi.single j 1) := by
        unfold shift
        rw [mulVec_mulVec, Matrix.mul_assoc (V * diagonal ζ), nonsing_inv_mul V hV,
          Matrix.mul_one, ← mulVec_mulVec]
    _ = V *ᵥ (ζ j • Pi.single j 1) := by
        rw [diagonal_mulVec_single, ← Pi.single_smul, smul_eq_mul]
    _ = ζ j • (V *ᵥ Pi.single j 1) := mulVec_smul _ _ _

theorem shift_mul_frame (V : Matrix n n ℂ) (hV : IsUnit V.det) (ζ : n → ℂ) :
    shift V ζ * V = V * diagonal ζ := by
  unfold shift
  rw [Matrix.mul_assoc, nonsing_inv_mul V hV, Matrix.mul_one]

/-- **Stein solution from unimodular nodes**: `G = V⁻¹^* V⁻¹ ≻ 0` satisfies
`S^* G S = G`. -/
theorem stein_of_unimodular (V : Matrix n n ℂ) (hV : IsUnit V.det) (ζ : n → ℂ)
    (hζ : ∀ i, ‖ζ i‖ = 1) :
    (V⁻¹ᴴ * V⁻¹).PosDef ∧ (shift V ζ)ᴴ * (V⁻¹ᴴ * V⁻¹) * shift V ζ = V⁻¹ᴴ * V⁻¹ := by
  have hinv : V⁻¹ * V = 1 := nonsing_inv_mul V hV
  have hinvH : Vᴴ * V⁻¹ᴴ = 1 := by rw [← conjTranspose_mul, hinv, conjTranspose_one]
  have hdiag : diagonal (star ζ) * diagonal ζ = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', hζ i]
    norm_num
  constructor
  · -- `V⁻¹` is injective on vectors
    have hunit : IsUnit V⁻¹ := (isUnit_nonsing_inv_iff).mpr ((isUnit_iff_isUnit_det V).mpr hV)
    exact PosDef.conjTranspose_mul_self V⁻¹ (mulVec_injective_iff_isUnit.mpr hunit)
  · unfold shift
    rw [conjTranspose_mul, conjTranspose_mul, diagonal_conjTranspose]
    have hinvH' : ∀ X : Matrix n n ℂ, Vᴴ * (V⁻¹ᴴ * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hinvH, Matrix.one_mul]
    have hinv' : ∀ X : Matrix n n ℂ, V⁻¹ * (V * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [hinvH', hinv', ← Matrix.mul_assoc (diagonal (star ζ)), hdiag, Matrix.one_mul]

omit [DecidableEq n] in
/-- **Unimodularity from a positive Stein solution**: every eigenvalue of `S`
has modulus one. -/
theorem unimodular_of_stein (S G : Matrix n n ℂ) (hG : G.PosDef) (hstein : Sᴴ * G * S = G)
    {ζ : ℂ} {x : n → ℂ} (hx : x ≠ 0) (heig : S *ᵥ x = ζ • x) : ‖ζ‖ = 1 := by
  have hq : 0 < star x ⬝ᵥ (G *ᵥ x) := hG.dotProduct_mulVec_pos hx
  have hquad : star x ⬝ᵥ (G *ᵥ x) = (star ζ * ζ) * (star x ⬝ᵥ (G *ᵥ x)) := by
    calc star x ⬝ᵥ (G *ᵥ x) = star x ⬝ᵥ ((Sᴴ * G * S) *ᵥ x) := by rw [hstein]
      _ = star (S *ᵥ x) ⬝ᵥ (G *ᵥ (S *ᵥ x)) := by
          rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]
      _ = (star ζ * ζ) * (star x ⬝ᵥ (G *ᵥ x)) := by
          rw [heig, star_smul, smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul,
            smul_eq_mul]
          ring
  have hne : star x ⬝ᵥ (G *ᵥ x) ≠ 0 := hq.ne'
  have h1 : star ζ * ζ = 1 := by
    have := hquad
    field_simp at this
    linear_combination -this
  rw [Complex.star_def, Complex.conj_mul'] at h1
  have h2 : (‖ζ‖ ^ 2 : ℝ) = 1 := by exact_mod_cast h1
  nlinarith [norm_nonneg ζ, sq_nonneg (‖ζ‖ - 1)]

/-- **(GRH.24)** for the diagonalized shift: all nodes unimodular ⇔ a positive
invariant Stein metric exists. -/
theorem finite_stein_iff (V : Matrix n n ℂ) (hV : IsUnit V.det) (ζ : n → ℂ) :
    (∀ i, ‖ζ i‖ = 1) ↔ ∃ G : Matrix n n ℂ, G.PosDef ∧ (shift V ζ)ᴴ * G * shift V ζ = G := by
  constructor
  · intro hζ
    exact ⟨_, stein_of_unimodular V hV ζ hζ⟩
  · rintro ⟨G, hG, hstein⟩ i
    have hcol : V *ᵥ Pi.single i 1 ≠ 0 := by
      intro h0
      have hinj : Function.Injective V.mulVec :=
        mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det V).mpr hV)
      have : Pi.single i (1 : ℂ) = 0 := hinj (by rw [h0, mulVec_zero])
      have := congrFun this i
      simp at this
    exact unimodular_of_stein (shift V ζ) G hG hstein hcol (shift_mulVec_eigen V hV ζ i)

/-- **Invariant metrics are diagonal in the eigenframe** when the nodes are
distinct and unimodular. -/
theorem invariant_metric_diagonal (V : Matrix n n ℂ) (hV : IsUnit V.det) (ζ : n → ℂ)
    (hζ : ∀ i, ‖ζ i‖ = 1) (hdist : Function.Injective ζ) (G : Matrix n n ℂ)
    (hstein : (shift V ζ)ᴴ * G * shift V ζ = G) :
    ∀ i j, i ≠ j → (Vᴴ * G * V) i j = 0 := by
  -- conjugate the Stein equation into the eigenframe
  have hkey : diagonal (star ζ) * (Vᴴ * G * V) * diagonal ζ = Vᴴ * G * V := by
    have h1 : (shift V ζ * V)ᴴ * G * (shift V ζ * V) = Vᴴ * G * V := by
      rw [conjTranspose_mul]
      calc Vᴴ * (shift V ζ)ᴴ * G * (shift V ζ * V)
          = Vᴴ * ((shift V ζ)ᴴ * G * shift V ζ) * V := by simp only [Matrix.mul_assoc]
        _ = Vᴴ * G * V := by rw [hstein]
    rw [shift_mul_frame V hV ζ, conjTranspose_mul, diagonal_conjTranspose] at h1
    calc diagonal (star ζ) * (Vᴴ * G * V) * diagonal ζ
        = diagonal (star ζ) * Vᴴ * G * (V * diagonal ζ) := by simp only [Matrix.mul_assoc]
      _ = Vᴴ * G * V := h1
  intro i j hij
  have hentry := congrFun (congrFun hkey i) j
  rw [mul_diagonal, diagonal_mul] at hentry
  -- `star ζ_i · g · ζ_j = g` forces `g = 0` unless `star ζ_i ζ_j = 1`
  by_contra hne
  have hprod : star (ζ i) * ζ j = 1 := by
    have : (star (ζ i) * ζ j - 1) * (Vᴴ * G * V) i j = 0 := by
      rw [Pi.star_apply] at hentry
      linear_combination hentry
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hne
  -- multiply by `ζ_i` and use `ζ_i star ζ_i = 1`
  have hii : ζ i * star (ζ i) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', hζ i]
    norm_num
  have hji : ζ j = ζ i := by
    calc ζ j = (ζ i * star (ζ i)) * ζ j := by rw [hii, one_mul]
      _ = ζ i * (star (ζ i) * ζ j) := by ring
      _ = ζ i := by rw [hprod, mul_one]
  exact hij (hdist hji).symm

end GRHFiniteStein
end NCG
