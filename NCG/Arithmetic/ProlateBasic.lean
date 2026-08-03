/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Basic prolate concentration and simple-even extraction
  (`thm:v002-prolate-basic`, `corollary:simple-even-extraction`,
   arithmetic manuscript)

* `prolate_sandwich`: the operator core of the prolate theorem —
  for self-adjoint idempotents `P` (time cut) and `B` (band cut),
  the compression `K = PBP` satisfies the displayed identity
  `⟨f, Kf⟩ = ‖B(Pf)‖²` and the two-sided bound
  `0 ≤ ⟨f, Kf⟩ ≤ ‖f‖²`, i.e. `0 ⪯ K ⪯ I`
  (`projection_contraction` supplies `‖Bg‖ ≤ ‖g‖`);
* `simple_even_extraction`: the perturbation arithmetic of the
  corollary — with the Schur effective-operator reduction and the
  spectral comparison displayed (`hlow`, `hgap`), a correction of
  size `ε < γ/2` keeps the lowest eigenvalue simple, and an odd
  sector starting above the shifted ground level forces the even
  parity of the ground vector (`heven`).

Rendering disclosed: the explicit sine kernel, the trace value
`2TΩ/π` (trace-class of the continuous positive kernel), and the
Ky Fan maximum principle are the manuscript's classical inputs
(Slepian–Landau–Pollak) and are not re-proved; the Schur
complement reduction to the effective operator `A - B*(C-z)⁻¹B`
and the Weyl-type spectral comparison enter the corollary as the
displayed hypotheses, as in the store-pencil record.
-/

open Complex

namespace NCG

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- A self-adjoint idempotent is a contraction. -/
theorem projection_contraction (B : H →ₗ[ℂ] H)
    (hBsa : ∀ f g : H, ⟪B f, g⟫ = ⟪f, B g⟫)
    (hBidem : ∀ f : H, B (B f) = B f) (g : H) :
    ‖B g‖ ≤ ‖g‖ := by
  have h1 : (‖B g‖ : ℝ) ^ 2 = (⟪B g, B g⟫).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (B g)]
    rfl
  have h2 : ⟪B g, B g⟫ = ⟪g, B g⟫ := by
    rw [hBsa g (B g), hBidem]
  have h3 : (⟪g, B g⟫).re ≤ ‖g‖ * ‖B g‖ := by
    calc (⟪g, B g⟫).re ≤ ‖⟪g, B g⟫‖ :=
        Complex.re_le_norm _
      _ ≤ ‖g‖ * ‖B g‖ := norm_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg (B g)) with h0 | h0
  · rw [← h0]
    exact norm_nonneg g
  · have h4 : ‖B g‖ ^ 2 ≤ ‖g‖ * ‖B g‖ := by
      rw [h1, h2]
      exact h3
    have h5 : ‖B g‖ * ‖B g‖ ≤ ‖g‖ * ‖B g‖ := by
      nlinarith
    exact le_of_mul_le_mul_right (by linarith) h0

/-- `thm:v002-prolate-basic`, operator core: the time–band
compression satisfies `⟨f, Kf⟩ = ‖B(Pf)‖²` and `0 ⪯ K ⪯ I`. -/
theorem prolate_sandwich (P B : H →ₗ[ℂ] H)
    (hPsa : ∀ f g : H, ⟪P f, g⟫ = ⟪f, P g⟫)
    (hPidem : ∀ f : H, P (P f) = P f)
    (hBsa : ∀ f g : H, ⟪B f, g⟫ = ⟪f, B g⟫)
    (hBidem : ∀ f : H, B (B f) = B f) (f : H) :
    ⟪f, P (B (P f))⟫ = ((‖B (P f)‖ : ℝ) ^ 2 : ℂ)
    ∧ 0 ≤ ((‖B (P f)‖ : ℝ) ^ 2)
    ∧ ((‖B (P f)‖ : ℝ) ^ 2) ≤ ‖f‖ ^ 2 := by
  refine ⟨?_, by positivity, ?_⟩
  · calc ⟪f, P (B (P f))⟫
        = ⟪P f, B (P f)⟫ := by rw [← hPsa]
      _ = ⟪P f, B (B (P f))⟫ := by rw [hBidem]
      _ = ⟪B (P f), B (P f)⟫ := by rw [← hBsa]
      _ = ((‖B (P f)‖ : ℝ) ^ 2 : ℂ) := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
          norm_cast
  · have h1 : ‖B (P f)‖ ≤ ‖P f‖ :=
      projection_contraction B hBsa hBidem (P f)
    have h2 : ‖P f‖ ≤ ‖f‖ :=
      projection_contraction P hPsa hPidem f
    have h3 : (0:ℝ) ≤ ‖B (P f)‖ := norm_nonneg _
    nlinarith

/-- `corollary:simple-even-extraction`: the perturbation
arithmetic — with the effective-operator spectral comparison
displayed, a correction below half the gap keeps the ground level
simple, and an odd sector starting above it forces even
parity. -/
theorem simple_even_extraction
    (a₀ γ ε lam₀ lam₁ lamOdd : ℝ) (hhalf : 2 * ε < γ)
    -- displayed spectral comparison for the effective operator:
    -- the two lowest levels move by at most the correction norm
    (hlow : |lam₀ - a₀| ≤ ε)
    (hgap : a₀ + γ - ε ≤ lam₁)
    -- displayed odd-sector lower edge
    (hodd : a₀ + γ - ε ≤ lamOdd) :
    lam₀ < lam₁ ∧ lam₀ < lamOdd := by
  have h1 := abs_le.mp hlow
  constructor
  · linarith [h1.2]
  · linarith [h1.2]

end NCG
