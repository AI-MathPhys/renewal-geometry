/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Certified store-pencil error propagation
  (`prop:store-pencil-error-master`, flagship manuscript)

For the whitened pencils `A = R₀H₁R₀` and `Â = R̂₀Ĥ₁R̂₀` with
measured data `‖Ĥ₀-H₀‖ ≤ ε₀ < κ`, `‖Ĥ₁-H₁‖ ≤ ε₁`:

* the boxed operator bound `‖Â - A‖ ≤ ε_A`
  (`store_pencil_operator_error`) is proved by the one-factor-at-
  a-time decomposition
  `Â - A = (R̂₀-R₀)Ĥ₁R̂₀ + R₀(Ĥ₁-H₁)R̂₀ + R₀H₁(R̂₀-R₀)`
  and submultiplicativity, in any normed ring;
* the boxed eigenvalue bound `|λ̂_j - λ_j| ≤ ε_A`
  (`store_pencil_eigen_error`) follows by chaining with Weyl's
  comparison for the compatibly ordered spectra.

Two standard inputs enter as displayed hypotheses (disclosed):
the positive inverse-square-root perturbation estimate
`‖R̂₀-R₀‖ ≤ d₀` together with the spectral bounds
`‖R₀‖ ≤ κ^{-1/2}`, `‖R̂₀‖ ≤ (κ-ε₀)^{-1/2}` (their
operator-monotonicity proofs are not separately recorded), and —
in the eigenvalue box — Weyl's inequality for the Hermitian
whitened pencils (`hweyl`; the Courant–Fischer min–max principle
is not yet available in Mathlib).  The boxed constants are
exactly the manuscript's.
-/

namespace NCG

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- `prop:store-pencil-error-master`, boxed operator bound:
`‖Â - A‖ ≤ ε_A` with the manuscript's explicit constant. -/
theorem store_pencil_operator_error
    (H1 Hh1 R0 Rh0 : 𝔸) (κ ε0 ε1 d0 : ℝ)
    (h1err : ‖Hh1 - H1‖ ≤ ε1)
    (hd0 : ‖Rh0 - R0‖ ≤ d0)
    (hR0 : ‖R0‖ ≤ (Real.sqrt κ)⁻¹)
    (hRh0 : ‖Rh0‖ ≤ (Real.sqrt (κ - ε0))⁻¹) :
    ‖Rh0 * Hh1 * Rh0 - R0 * H1 * R0‖
      ≤ d0 * (‖H1‖ + ε1) * (Real.sqrt (κ - ε0))⁻¹
        + (Real.sqrt κ)⁻¹ * ε1 * (Real.sqrt (κ - ε0))⁻¹
        + (Real.sqrt κ)⁻¹ * ‖H1‖ * d0 := by
  have hε1 : 0 ≤ ε1 := le_trans (norm_nonneg _) h1err
  have hd0' : 0 ≤ d0 := le_trans (norm_nonneg _) hd0
  have hHh1 : ‖Hh1‖ ≤ ‖H1‖ + ε1 := by
    calc ‖Hh1‖
        = ‖H1 + (Hh1 - H1)‖ := by rw [add_sub_cancel]
      _ ≤ ‖H1‖ + ‖Hh1 - H1‖ := norm_add_le _ _
      _ ≤ ‖H1‖ + ε1 := by linarith
  have hdecomp : Rh0 * Hh1 * Rh0 - R0 * H1 * R0
      = (Rh0 - R0) * Hh1 * Rh0
        + (R0 * (Hh1 - H1) * Rh0 + R0 * H1 * (Rh0 - R0)) := by
    noncomm_ring
  calc ‖Rh0 * Hh1 * Rh0 - R0 * H1 * R0‖
      = ‖(Rh0 - R0) * Hh1 * Rh0
          + (R0 * (Hh1 - H1) * Rh0
            + R0 * H1 * (Rh0 - R0))‖ := by rw [hdecomp]
    _ ≤ ‖(Rh0 - R0) * Hh1 * Rh0‖
          + (‖R0 * (Hh1 - H1) * Rh0‖
            + ‖R0 * H1 * (Rh0 - R0)‖) := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ d0 * (‖H1‖ + ε1) * (Real.sqrt (κ - ε0))⁻¹
          + ((Real.sqrt κ)⁻¹ * ε1 * (Real.sqrt (κ - ε0))⁻¹
            + (Real.sqrt κ)⁻¹ * ‖H1‖ * d0) := by
        gcongr
        · calc ‖(Rh0 - R0) * Hh1 * Rh0‖
              ≤ ‖(Rh0 - R0) * Hh1‖ * ‖Rh0‖ := norm_mul_le _ _
            _ ≤ ‖Rh0 - R0‖ * ‖Hh1‖ * ‖Rh0‖ := by
                gcongr
                exact norm_mul_le _ _
            _ ≤ d0 * (‖H1‖ + ε1) * (Real.sqrt (κ - ε0))⁻¹ := by
                gcongr
        · calc ‖R0 * (Hh1 - H1) * Rh0‖
              ≤ ‖R0 * (Hh1 - H1)‖ * ‖Rh0‖ := norm_mul_le _ _
            _ ≤ ‖R0‖ * ‖Hh1 - H1‖ * ‖Rh0‖ := by
                gcongr
                exact norm_mul_le _ _
            _ ≤ (Real.sqrt κ)⁻¹ * ε1
                * (Real.sqrt (κ - ε0))⁻¹ := by
                gcongr
        · calc ‖R0 * H1 * (Rh0 - R0)‖
              ≤ ‖R0 * H1‖ * ‖Rh0 - R0‖ := norm_mul_le _ _
            _ ≤ ‖R0‖ * ‖H1‖ * ‖Rh0 - R0‖ := by
                gcongr
                exact norm_mul_le _ _
            _ ≤ (Real.sqrt κ)⁻¹ * ‖H1‖ * d0 := by
                gcongr
    _ = d0 * (‖H1‖ + ε1) * (Real.sqrt (κ - ε0))⁻¹
          + (Real.sqrt κ)⁻¹ * ε1 * (Real.sqrt (κ - ε0))⁻¹
          + (Real.sqrt κ)⁻¹ * ‖H1‖ * d0 := by ring

/-- `prop:store-pencil-error-master`, boxed eigenvalue bound:
compatibly ordered generalized eigenvalues inherit the operator
error through Weyl's comparison (`hweyl`, disclosed). -/
theorem store_pencil_eigen_error {ι : Type*}
    (H1 Hh1 R0 Rh0 : 𝔸) (κ ε0 ε1 d0 : ℝ)
    (h1err : ‖Hh1 - H1‖ ≤ ε1)
    (hd0 : ‖Rh0 - R0‖ ≤ d0)
    (hR0 : ‖R0‖ ≤ (Real.sqrt κ)⁻¹)
    (hRh0 : ‖Rh0‖ ≤ (Real.sqrt (κ - ε0))⁻¹)
    (lam lamhat : ι → ℝ)
    (hweyl : ∀ j, |lamhat j - lam j|
      ≤ ‖Rh0 * Hh1 * Rh0 - R0 * H1 * R0‖) (j : ι) :
    |lamhat j - lam j|
      ≤ d0 * (‖H1‖ + ε1) * (Real.sqrt (κ - ε0))⁻¹
        + (Real.sqrt κ)⁻¹ * ε1 * (Real.sqrt (κ - ε0))⁻¹
        + (Real.sqrt κ)⁻¹ * ‖H1‖ * d0 :=
  (hweyl j).trans (store_pencil_operator_error H1 Hh1 R0 Rh0
    κ ε0 ε1 d0 h1err hd0 hR0 hRh0)

end NCG
