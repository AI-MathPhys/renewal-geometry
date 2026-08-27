/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTAffineFourier
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Affine Fourier expansion on a concrete finite abelian dual

This file instantiates the abstract character interface with Mathlib's complete
basis of complex-valued additive characters of a finite abelian group.
-/

open Finset

attribute [local instance] Classical.propDecidable

namespace NCG
namespace AffineFiniteAbelianFourierExact

/-- Fourier coefficient in the manuscript's unnormalised convention. -/
noncomputable def finiteFourierCoefficient
    {G : Type} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (χ : AddChar G ℂ) : ℂ :=
  (Fintype.card G : ℂ) * (AddChar.complexBasis G).repr f χ

/-- The complete finite character basis supplies the precise inversion
normalisation used by the affine relation formula. -/
theorem finiteFourier_inversion
    {G : Type} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (y : G) :
    f y = (Fintype.card G : ℂ)⁻¹ *
      ∑ χ : AddChar G ℂ, finiteFourierCoefficient f χ * χ y := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  symm
  calc
    (Fintype.card G : ℂ)⁻¹ *
        ∑ χ : AddChar G ℂ, finiteFourierCoefficient f χ * χ y =
      ∑ χ : AddChar G ℂ,
        (AddChar.complexBasis G).repr f χ * χ y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      simp only [finiteFourierCoefficient, ← mul_assoc,
        inv_mul_cancel₀ hcard, one_mul]
    _ = f y := by
      have h := congrFun ((AddChar.complexBasis G).sum_repr f) y
      simpa [AddChar.complexBasis_apply, Fintype.sum_apply,
        Pi.smul_apply, smul_eq_mul] using h

/-- Concrete form of the affine Fourier relation with
`X = AddChar G ℂ`; no abstract character-system or inversion hypothesis
remains. -/
theorem finiteAbelian_affine_fourier
    {G : Type} [AddCommGroup G] [Fintype G]
    {t d : ℕ}
    (L : Fin t → ((Fin d → G) →+ G)) (b : Fin t → G)
    (f : Fin t → G → ℂ) :
    (∀ χ : Fin t → AddChar G ℂ,
      (¬ ∀ x : Fin d → G, ∏ i, χ i (L i x) = 1) →
      ∑ x : Fin d → G, ∏ i, χ i (L i x) = 0) ∧
    ((Fintype.card (Fin d → G) : ℂ))⁻¹ *
        ∑ x : Fin d → G, ∏ i, f i (L i x + b i) =
      ((Fintype.card G : ℂ) ^ t)⁻¹ *
        ∑ χ ∈ Finset.univ.filter
          (fun χ : Fin t → AddChar G ℂ =>
            ∀ x : Fin d → G, ∏ i, χ i (L i x) = 1),
          ∏ i, finiteFourierCoefficient (f i) (χ i) * χ i (b i) := by
  exact gt_affine_fourier
    (fun χ : AddChar G ℂ => fun x => χ x)
    finiteFourierCoefficient L b f
    (fun χ a a' => χ.map_add_eq_mul a a')
    finiteFourier_inversion

end AffineFiniteAbelianFourierExact
end NCG
