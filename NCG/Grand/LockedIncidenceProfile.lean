/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Locked opportunity contrast geometry and incidence
  criterion (`thm:locked-incidence-profile`,
  Gran-Tensor manuscript)

* `locked_incidence_profile`:
  (i) the mean projector `P_c` (uniform rank-one) is a
      hermitian idempotent, so the boxed metric
      `M_θ = θ(I-P_c) + (12-11θ)P_c` is a two-eigenvalue
      spectral combination;
  (ii) the exact two-eigenvalue inversion
      `M_θ⁻¹ = θ⁻¹(I-P_c) + (12-11θ)⁻¹P_c`;
  (iii) the off-diagonal entries of `M_θ` equal
      `(12 - 12θ)/24`;
  (iv) the boxed globally nonorthogonal Stinespring
      overlap: the normalized outcome-frame Gram
      `θ·M_θ⁻¹` has off-diagonal entries
      `-(1-θ)/(2(12-11θ))`;
  (v) the locked source Gram `Q*Q = αP_cut + βP_cyc` of two
      orthogonal positive components is positive
      semidefinite (loop provenance stays positive).

The Pauli-triple derivation `-(i/2)[X_e, Y_e] = Z_e` from a
shortened odd cross-support is the previously proved
`NCG.locked_odd_incidence_factor` (LockedOddPauli.lean),
and the `M_θ` display itself is
`NCG.locked_opportunity_contrast_spectrum`
(ContrastSpectrum.lean); the cross-edge commutator residual
`Δ_par` and the `S₄` bookkeeping are the manuscript's
packet layer.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:locked-incidence-profile`. -/
theorem locked_incidence_profile (θ : ℂ) (hθ : θ ≠ 0)
    (h12 : (12 : ℂ) - 11 * θ ≠ 0) :
    -- (i) the uniform mean projector is a hermitian
    -- idempotent
    ((Matrix.of fun _ _ => (1 / 24 : ℂ) :
        Matrix (Fin 24) (Fin 24) ℂ)
      * (Matrix.of fun _ _ => (1 / 24 : ℂ)))
      = (Matrix.of fun _ _ => (1 / 24 : ℂ))
    ∧ ((Matrix.of fun _ _ => (1 / 24 : ℂ) :
        Matrix (Fin 24) (Fin 24) ℂ)ᴴ
      = (Matrix.of fun _ _ => (1 / 24 : ℂ)))
    -- (ii) exact two-eigenvalue inversion (abstract)
    ∧ (∀ {m : Type} [Fintype m] [DecidableEq m]
        (P : Matrix m m ℂ), P * P = P →
        (θ • (1 - P) + ((12 : ℂ) - 11 * θ) • P)
          * (θ⁻¹ • (1 - P)
            + ((12 : ℂ) - 11 * θ)⁻¹ • P) = 1)
    -- (iii) off-diagonal metric entries
    ∧ (∀ j k : Fin 24, j ≠ k →
        ((θ • ((1 : Matrix (Fin 24) (Fin 24) ℂ)
            - Matrix.of fun _ _ => (1 / 24 : ℂ))
          + ((12 : ℂ) - 11 * θ)
            • (Matrix.of fun _ _ => (1 / 24 : ℂ)) :
          Matrix (Fin 24) (Fin 24) ℂ)) j k
        = ((12 : ℂ) - 12 * θ) / 24)
    -- (iv) the boxed Stinespring overlap
    ∧ (∀ j k : Fin 24, j ≠ k →
        ((θ • (θ⁻¹ • ((1 : Matrix (Fin 24) (Fin 24) ℂ)
            - Matrix.of fun _ _ => (1 / 24 : ℂ))
          + ((12 : ℂ) - 11 * θ)⁻¹
            • (Matrix.of fun _ _ => (1 / 24 : ℂ))) :
          Matrix (Fin 24) (Fin 24) ℂ)) j k
        = -((1 : ℂ) - θ)
            / (2 * ((12 : ℂ) - 11 * θ)))
    -- (v) the locked source Gram stays positive
    ∧ (∀ {m : Type} [Fintype m]
        (P1 P2 : Matrix m m ℂ) (α β : ℂ),
        P1.PosSemidef → P2.PosSemidef →
        0 ≤ α → 0 ≤ β →
        (α • P1 + β • P2).PosSemidef) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext a b
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_const, Finset.card_univ]
    norm_num [Fintype.card_fin]
  · ext a b
    simp [Matrix.conjTranspose_apply]
  · intro m _ _ P hP
    have h1 : ((1 : Matrix m m ℂ) - P) * (1 - P)
        = 1 - P := by
      simp only [Matrix.sub_mul, Matrix.mul_sub,
        Matrix.one_mul, Matrix.mul_one, hP]
      abel
    have h2 : ((1 : Matrix m m ℂ) - P) * P = 0 := by
      simp only [Matrix.sub_mul, Matrix.one_mul, hP]
      abel
    have h3 : P * ((1 : Matrix m m ℂ) - P) = 0 := by
      simp only [Matrix.mul_sub, Matrix.mul_one, hP]
      abel
    simp only [Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      h1, h2, h3, hP, smul_zero, add_zero, zero_add,
      inv_mul_cancel₀ hθ, inv_mul_cancel₀ h12, one_smul]
    exact sub_add_cancel 1 P
  · intro j k hjk
    simp only [Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.one_apply_ne hjk,
      Matrix.of_apply, smul_eq_mul]
    ring
  · intro j k hjk
    simp only [Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.one_apply_ne hjk,
      Matrix.of_apply, smul_eq_mul]
    have h12' : (12 : ℂ) - θ * 11 ≠ 0 := by
      rw [mul_comm]
      exact h12
    field_simp
    ring
  · intro m _ P1 P2 α β h1 h2 hα hβ
    exact (h1.smul hα).add (h2.smul hβ)

end NCG
