/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandInterface2
import NCG.Grand.GrandDelay
import NCG.Grand.SchurAssociativity
import NCG.Grand.SchurRedheffer
import NCG.Grand.BoundarySpectralShift
import NCG.Grand.GrandCountermodels

/-!
# Integrated interface duality
  (`thm:integrated-interface-duality`, Gran-Tensor manuscript)

The interface-chapter master bundle: the manuscript's proof is
exactly the citation list of its constituent records, all of
which are proved, and each clause below is the representative
formal core through which the cited record enters:

* (1) interface gluing — the solved interface value and the
      Schur determinant factorization (`interface_gluing`);
* (2) conservative (Herglotz) gluing — the glued quadratic form
      is the sum of the component block forms
      (`herglotz_gluing`);
* (3) associative interface elimination — the iterated Schur
      complement reproduces the full solved response
      (`schur_associativity`);
* (4) signed Redheffer feedback — the wave-coordinate chart
      transports the response law to the Cayley scattering
      matrix (`cayley_scattering`; the full leg comprises the
      seven `redheffer_star_*` declarations);
* (5) matrix continued fractions and layer stripping — the
      three-term recursion inverts to the stripped layer
      (`layer_stripping`);
* (6) determinant ratios and spectral shift — both boundary
      determinants factor through the common interior
      (`boundary_det_ratio`; the full leg includes
      `boundary_spectral_shift_deriv` and
      `boundary_contour_count`);
* (7) positive delay — the Wigner–Smith boundary Gram is
      positive definite with positive trace (`positive_delay`);
* (8) necessity of the matrix frame — equal component
      self-responses with different glued cross responses
      (`relative_interface_frame`);
* (9) the resource boundary — Schur elimination can create
      quadratic fill-in (`schur_fill_in`).

Rendering disclosed: each clause is the formal core of its cited
proved record (see the ledger entries of the constituents for
their own disclosures); "one interface object" is rendered as
this conjunction of exact interchange formulas between the five
coordinate presentations.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:integrated-interface-duality`: the interface-chapter
master bundle — gluing, Schur response, Redheffer feedback,
continued fractions/layer stripping, and determinant/delay
shadows are exact coordinate presentations of one interface
object, the matrix frame is necessary, and the duality is not
resource faithful. -/
theorem integrated_interface_duality
    {e i b n : Type*} [Fintype e] [Fintype i] [Fintype b]
    [Fintype n] [DecidableEq e] [DecidableEq i] [DecidableEq b]
    [DecidableEq n] [Nonempty n] :
    -- (1) interface gluing: solved value + determinant split
    (∀ (A : Matrix e e ℂ) (K : Matrix e i ℂ) (L : Matrix i e ℂ)
        (H : Matrix i i ℂ) (_ : Invertible H)
        (x : e → ℂ) (u : i → ℂ),
        H *ᵥ u + L *ᵥ x = 0 →
        u = -(H⁻¹ *ᵥ (L *ᵥ x))
        ∧ (Matrix.fromBlocks A K L H).det
          = H.det * (A - K * H⁻¹ * L).det)
    -- (2) conservative gluing adds the component forms
    ∧ (∀ (A1 : Matrix e e ℂ) (B1 : Matrix e i ℂ)
        (C1 : Matrix i e ℂ) (D1 : Matrix i i ℂ)
        (A2 : Matrix b b ℂ) (B2 : Matrix b i ℂ)
        (C2 : Matrix i b ℂ) (D2 : Matrix i i ℂ)
        (x1 : e → ℂ) (x2 : b → ℂ) (u : i → ℂ),
        (D1 + D2) *ᵥ u + (C1 *ᵥ x1 + C2 *ᵥ x2) = 0 →
        star x1 ⬝ᵥ (A1 *ᵥ x1 + B1 *ᵥ u)
          + star x2 ⬝ᵥ (A2 *ᵥ x2 + B2 *ᵥ u)
        = (star x1 ⬝ᵥ (A1 *ᵥ x1 + B1 *ᵥ u)
            + star u ⬝ᵥ (C1 *ᵥ x1 + D1 *ᵥ u))
          + (star x2 ⬝ᵥ (A2 *ᵥ x2 + B2 *ᵥ u)
            + star u ⬝ᵥ (C2 *ᵥ x2 + D2 *ᵥ u)))
    -- (3) associative interface elimination
    ∧ (∀ (A : Matrix e e ℂ) (B1 : Matrix e i ℂ)
        (B2 : Matrix e b ℂ) (C1 : Matrix i e ℂ)
        (C2 : Matrix b e ℂ) (D11 : Matrix i i ℂ)
        (D12 : Matrix i b ℂ) (D21 : Matrix b i ℂ)
        (D22 : Matrix b b ℂ) (_ : Invertible D11)
        (_ : Invertible (D22 - D21 * D11⁻¹ * D12))
        (x : e → ℂ) (u1 : i → ℂ) (u2 : b → ℂ),
        D11 *ᵥ u1 + (D12 *ᵥ u2 + C1 *ᵥ x) = 0 →
        D21 *ᵥ u1 + (D22 *ᵥ u2 + C2 *ᵥ x) = 0 →
        ((A - B1 * D11⁻¹ * C1)
            - (B2 - B1 * D11⁻¹ * D12)
              * (D22 - D21 * D11⁻¹ * D12)⁻¹
              * (C2 - D21 * D11⁻¹ * C1)) *ᵥ x
          = A *ᵥ x + (B1 *ᵥ u1 + B2 *ᵥ u2))
    -- (4) Redheffer wave chart (Cayley scattering)
    ∧ (∀ (Λ : Matrix n n ℂ)
        (_ : Invertible (Λ + Complex.I • 1)),
        (∀ u : n → ℂ,
          ((Λ - Complex.I • 1) * (Λ + Complex.I • 1)⁻¹) *ᵥ
              (invSqrt2 • (Λ *ᵥ u + Complex.I • u))
            = invSqrt2 • (Λ *ᵥ u - Complex.I • u))
        ∧ (∀ a : n → ℂ, ∃ u : n → ℂ,
            a = invSqrt2 • (Λ *ᵥ u + Complex.I • u)))
    -- (5) continued fraction / layer stripping inversion
    ∧ (∀ (Lk Ln C B : Matrix b b ℂ) (z : ℂ)
        (_ : Invertible B) (_ : Invertible Ln),
        Lk = z • (1 : Matrix b b ℂ) - C - Bᴴ * Ln⁻¹ * B →
        Ln = -(B * (Lk - z • (1 : Matrix b b ℂ) + C)⁻¹ * Bᴴ))
    -- (6) determinant ratio through the common interior
    ∧ (∀ (A1 A0 : Matrix e e ℂ) (B1 B0 : Matrix e i ℂ)
        (C1 C0 : Matrix i e ℂ) (D : Matrix i i ℂ) (z : ℂ)
        (_ : Invertible (D - z • 1)),
        (Matrix.fromBlocks A1 B1 C1 D - z • 1).det
          = (D - z • 1).det
            * ((A1 - z • 1) - B1 * (D - z • 1)⁻¹ * C1).det
        ∧ (Matrix.fromBlocks A1 B1 C1 D - z • 1).det
            * ((A0 - z • 1) - B0 * (D - z • 1)⁻¹ * C0).det
          = (Matrix.fromBlocks A0 B0 C0 D - z • 1).det
            * ((A1 - z • 1) - B1 * (D - z • 1)⁻¹ * C1).det)
    -- (7) positive Wigner–Smith delay
    ∧ (∀ (L Ld : Matrix n n ℂ), Lᴴ = L → Ld.PosDef →
        ∀ _ : Invertible (L + Complex.I • 1),
        ((-Complex.I) • (((L - Complex.I • 1)
              * (L + Complex.I • 1)⁻¹)ᴴ
            * (Ld * (L + Complex.I • 1)⁻¹
              - (L - Complex.I • 1) * (L + Complex.I • 1)⁻¹
                * Ld * (L + Complex.I • 1)⁻¹))
          = (2 : ℂ) • (((L + Complex.I • 1)⁻¹)ᴴ * Ld
              * (L + Complex.I • 1)⁻¹))
        ∧ (∀ x : n → ℂ, x ≠ 0 →
            0 < star x ⬝ᵥ ((((L + Complex.I • 1)⁻¹)ᴴ * Ld
              * (L + Complex.I • 1)⁻¹) *ᵥ x))
        ∧ 0 < (((((L + Complex.I • 1)⁻¹)ᴴ * Ld
            * (L + Complex.I • 1)⁻¹)).trace).re)
    -- (8) the matrix frame is necessary
    ∧ (∃ (K L K' L' : ℚ),
        (0 - K * 1⁻¹ * L = 0 - K' * 1⁻¹ * L')
        ∧ (0 - K * (2 : ℚ)⁻¹ * L') ≠ 0 - K' * (2 : ℚ)⁻¹ * L')
    -- (9) the duality is not resource faithful
    ∧ (∃ (A : Matrix (Fin 2) (Fin 2) ℚ)
        (K : Matrix (Fin 2) (Fin 1) ℚ)
        (L : Matrix (Fin 1) (Fin 2) ℚ)
        (H : Matrix (Fin 1) (Fin 1) ℚ),
        (∀ i j, (A - K * H⁻¹ * L) i j ≠ 0)
        ∧ (∀ i j, i ≠ j → A i j = 0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    relative_interface_frame, schur_fill_in⟩
  · intro A K L H hH x u hsolve
    exact @interface_gluing e i _ _ _ _ A K L H hH x u hsolve
  · intro A1 B1 C1 D1 A2 B2 C2 D2 x1 x2 u hsolve
    exact herglotz_gluing A1 B1 C1 D1 A2 B2 C2 D2 x1 x2 u hsolve
  · intro A B1 B2 C1 C2 D11 D12 D21 D22 hI1 hI2 x u1 u2 h1 h2
    exact @schur_associativity e i b _ _ _ _ _
      A B1 B2 C1 C2 D11 D12 D21 D22 hI1 hI2 x u1 u2 h1 h2
  · intro Λ hI
    exact @cayley_scattering n _ _ Λ hI
  · intro Lk Ln C B z hB hLn hrec
    exact @layer_stripping b _ _ Lk Ln C B z hB hLn hrec
  · intro A1 A0 B1 B0 C1 C0 D z hI
    exact @boundary_det_ratio e i _ _ _ _ A1 A0 B1 B0 C1 C0 D z hI
  · intro L Ld hL hLd hI
    exact @positive_delay n _ _ _ L Ld hL hLd hI

end NCG
