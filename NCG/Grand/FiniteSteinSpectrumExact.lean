/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GRHFiniteSteinExact

/-!
# Exact spectrum of the finite reconstructed zero shift

This supplies the converse direction implicit in GRH.23: the eigenvalues of
the reconstructed diagonalizable shift are exactly its reconstructed nodes.
Together with the existing positive Stein equivalence and invariant-metric
diagonal theorem, this completes `cor:GRH-finite-Stein`.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace GRHFiniteStein

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A scalar is an eigenvalue of the reconstructed shift exactly when it is
one of the reconstructed nodes. -/
theorem shift_eigenvalue_iff_node (V : Matrix n n ℂ)
    (hV : IsUnit V.det) (zeta : n → ℂ) (lam : ℂ) :
    (∃ x : n → ℂ, x ≠ 0 ∧ shift V zeta *ᵥ x = lam • x)
      ↔ ∃ i, zeta i = lam := by
  have hVunit : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).mpr hV
  have hVinj : Function.Injective V.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hVunit
  constructor
  · rintro ⟨x, hx, heig⟩
    let y : n → ℂ := V⁻¹ *ᵥ x
    have hxy : V *ᵥ y = x := by
      calc
        V *ᵥ y = (V * V⁻¹) *ᵥ x := by
          dsimp [y]
          exact Matrix.mulVec_mulVec x V V⁻¹
        _ = x := by rw [Matrix.mul_nonsing_inv V hV, Matrix.one_mulVec]
    have hy : Matrix.diagonal zeta *ᵥ y = lam • y := by
      apply hVinj
      calc
        V *ᵥ (Matrix.diagonal zeta *ᵥ y)
            = (V * Matrix.diagonal zeta) *ᵥ y :=
                Matrix.mulVec_mulVec y V (Matrix.diagonal zeta)
        _ = (shift V zeta * V) *ᵥ y := by rw [shift_mul_frame V hV zeta]
        _ = shift V zeta *ᵥ (V *ᵥ y) :=
              (Matrix.mulVec_mulVec y (shift V zeta) V).symm
        _ = shift V zeta *ᵥ x := by rw [hxy]
        _ = lam • x := heig
        _ = lam • (V *ᵥ y) := by rw [hxy]
        _ = V *ᵥ (lam • y) := (Matrix.mulVec_smul V lam y).symm
    have hyne : y ≠ 0 := by
      intro hzero
      apply hx
      rw [← hxy, hzero, Matrix.mulVec_zero]
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hyne (funext h)
    refine ⟨i, ?_⟩
    have hentry := congrFun hy i
    simp [Matrix.mulVec, Matrix.diagonal, dotProduct] at hentry
    exact hentry.resolve_right hi
  · rintro ⟨i, rfl⟩
    refine ⟨V *ᵥ Pi.single i 1, ?_, shift_mulVec_eigen V hV zeta i⟩
    intro hzero
    have hzeroSingle : Pi.single i (1 : ℂ) = 0 :=
      hVinj (by simpa using hzero)
    have := congrFun hzeroSingle i
    simp at this

/-- GRH.23--GRH.24 assembled: exact node spectrum and the positive Stein
criterion, with diagonal invariant metrics for distinct nodes. -/
theorem finite_stein_spectrum_exact (V : Matrix n n ℂ)
    (hV : IsUnit V.det) (zeta : n → ℂ)
    (hdist : Function.Injective zeta) :
    (∀ lam, (∃ x : n → ℂ, x ≠ 0 ∧ shift V zeta *ᵥ x = lam • x)
        ↔ ∃ i, zeta i = lam)
      ∧ ((∀ i, ‖zeta i‖ = 1) ↔
        ∃ G : Matrix n n ℂ, G.PosDef ∧
          (shift V zeta)ᴴ * G * shift V zeta = G)
      ∧ (∀ G : Matrix n n ℂ, G.PosDef →
        (shift V zeta)ᴴ * G * shift V zeta = G →
        ∀ i j, i ≠ j → (Vᴴ * G * V) i j = 0) := by
  refine ⟨shift_eigenvalue_iff_node V hV zeta,
    finite_stein_iff V hV zeta, ?_⟩
  intro G hG hstein
  have hnodes : ∀ i, ‖zeta i‖ = 1 :=
    (finite_stein_iff V hV zeta).mpr ⟨G, hG, hstein⟩
  exact invariant_metric_diagonal V hV zeta hnodes hdist G hstein

end GRHFiniteStein
end NCG