/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteTorusFourierInversion
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Plancherel theorem on finite tori

The unnormalized product Fourier transform scales the counting-measure
inner product by the cardinality of the finite torus.  Its cardinality-
normalized form is therefore an isometry.
-/

open Finset AddChar

namespace NCG

variable {N : ℕ} [NeZero N]
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Conjugating the standard character negates its argument. -/
theorem star_stdAddChar (a : ZMod N) :
    star (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, Complex.star_def,
    ← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv]

/-- The conjugated kernel is the reflected Fourier kernel. -/
theorem star_finiteTorusAddChar_kernel
    (k x : d → ZMod N) :
    star (finiteTorusAddChar k (-x)) =
      finiteTorusAddChar (-x) (-k) := by
  rw [finiteTorusAddChar_apply, finiteTorusAddChar_apply,
    ← starRingEnd_apply, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [starRingEnd_apply, star_stdAddChar]
  congr 1
  simp only [Pi.neg_apply]
  ring

/-- The reflected transform is the adjoint of the unnormalized transform
for the counting inner product. -/
theorem sum_inner_finiteTorusFourier_left
    (Phi Psi : (d → ZMod N) → E) :
    ∑ k, inner ℂ (finiteTorusFourier Phi k) (Psi k) =
      ∑ x, inner ℂ (Phi x) (finiteTorusFourier Psi (-x)) := by
  simp only [finiteTorusFourier, sum_inner, inner_smul_left]
  rw [sum_comm]
  simp_rw [starRingEnd_apply, star_finiteTorusAddChar_kernel, inner_sum, inner_smul_right]

/-- Complex-valued Parseval identity for the unnormalized product Fourier
transform. -/
theorem sum_inner_finiteTorusFourier
    (Phi Psi : (d → ZMod N) → E) :
    ∑ k, inner ℂ (finiteTorusFourier Phi k)
        (finiteTorusFourier Psi k) =
      (Fintype.card (d → ZMod N) : ℂ) •
        ∑ x, inner ℂ (Phi x) (Psi x) := by
  rw [sum_inner_finiteTorusFourier_left]
  simp_rw [congrFun (finiteTorusFourier_fourier Psi), neg_neg,
    inner_smul_right, ← Finset.mul_sum]
  rfl

/-- Squared-norm Parseval identity for the unnormalized product Fourier
transform. -/
theorem sum_norm_sq_finiteTorusFourier (Phi : (d → ZMod N) → E) :
    ∑ k, ‖finiteTorusFourier Phi k‖ ^ 2 =
      Fintype.card (d → ZMod N) * ∑ x, ‖Phi x‖ ^ 2 := by
  have h := sum_inner_finiteTorusFourier Phi Phi
  simp only [inner_self_eq_norm_sq_to_K, smul_eq_mul] at h
  change (∑ k, (‖finiteTorusFourier Phi k‖ : ℂ) ^ 2) =
    (Fintype.card (d → ZMod N) : ℂ) *
      ∑ x, (‖Phi x‖ : ℂ) ^ 2 at h
  exact_mod_cast h

/-- Energy scaling for a constant multiple of the Fourier transform. -/
theorem sum_norm_sq_const_smul_finiteTorusFourier
    (c : ℂ) (Phi : (d → ZMod N) → E) :
    ∑ k, ‖c • finiteTorusFourier Phi k‖ ^ 2 =
      (‖c‖ ^ 2 * Fintype.card (d → ZMod N)) *
        ∑ x, ‖Phi x‖ ^ 2 := by
  simp_rw [norm_smul, mul_pow]
  rw [← Finset.mul_sum, sum_norm_sq_finiteTorusFourier]
  ring

/-- The canonical inverse-square-root normalization of the product Fourier
transform. -/
noncomputable def finiteTorusNormalizedFourier
    (Phi : (d → ZMod N) → E) (k : d → ZMod N) : E :=
  ((Real.sqrt (Fintype.card (d → ZMod N)) : ℂ)⁻¹) •
    finiteTorusFourier Phi k

/-- The inverse-square-root cardinal factor has precisely the normalization
required by Parseval. -/
theorem norm_inv_sqrt_card_finiteTorus_sq_mul_card :
    ‖(Real.sqrt (Fintype.card (d → ZMod N)) : ℂ)⁻¹‖ ^ 2 *
        Fintype.card (d → ZMod N) = 1 := by
  have hcard : 0 < Fintype.card (d → ZMod N) := Fintype.card_pos
  have hsqrt : 0 < Real.sqrt (Fintype.card (d → ZMod N)) :=
    Real.sqrt_pos.2 (by exact_mod_cast hcard)
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsqrt, inv_pow]
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-- The normalized product Fourier transform preserves the counting
`L²` energy exactly. -/
theorem sum_norm_sq_finiteTorusNormalizedFourier
    (Phi : (d → ZMod N) → E) :
    ∑ k, ‖finiteTorusNormalizedFourier Phi k‖ ^ 2 =
      ∑ x, ‖Phi x‖ ^ 2 := by
  rw [show (∑ k, ‖finiteTorusNormalizedFourier Phi k‖ ^ 2) =
      ∑ k,
        ‖(Real.sqrt (Fintype.card (d → ZMod N)) : ℂ)⁻¹ •
          finiteTorusFourier Phi k‖ ^ 2 by rfl]
  rw [sum_norm_sq_const_smul_finiteTorusFourier,
    norm_inv_sqrt_card_finiteTorus_sq_mul_card, one_mul]

end NCG
