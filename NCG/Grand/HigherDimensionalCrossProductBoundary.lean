/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.PrimitiveWeight

/-!
# Quantitative boundary of the seven-dimensional cross-product branch

This file proves the finite-dimensional quantitative conclusions (DS.15) and
(DS.16) of `thm:dimension-G2-boundary`.

The classification of metric vector cross products in dimensions
`0, 1, 3, 7` is proved downstream in
`MetricCrossProductDimensionClassification`.  The present module supplies
the independent rank-nullity and positive-source-loss conclusions used once
the classification selects the seven-dimensional branch.
-/

open Matrix

namespace NCG

/-- DS.15: a surjective cross-product map from the 21-dimensional exterior
square of a seven-dimensional carrier has a fourteen-dimensional kernel. -/
theorem seven_cross_product_kernel_dimension
    (cross : Matrix (Fin 7) (Fin 21) ℝ)
    (hsurj : Module.finrank ℝ (LinearMap.range cross.mulVecLin) = 7) :
    Module.finrank ℝ (LinearMap.ker cross.mulVecLin) = 14 := by
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker cross.mulVecLin
  rw [hsurj] at hrankNullity
  norm_num at hrankNullity ⊢
  omega

/-- A rank-fourteen orthogonal compression of a Gram matrix with floor
`lambda * I` loses at least `14 * lambda` of trace.  The rank is recorded as
the projector trace, which is the exact finite-matrix form used in DS.16. -/
theorem seven_cross_product_trace_loss
    (G P : Matrix (Fin 21) (Fin 21) ℝ) (lambda : ℝ)
    (hfloor : (G - lambda • (1 : Matrix (Fin 21) (Fin 21) ℝ)).PosSemidef)
    (hP : P.PosSemidef) (hP_sq : P * P = P)
    (hP_trace : P.trace = 14) :
    14 * lambda ≤ (P * G * P).trace := by
  have hnonneg :
      0 ≤ ((G - lambda • (1 : Matrix (Fin 21) (Fin 21) ℝ)) * P).trace :=
    NCG.Upstream.PrimitiveWeight.trace_mul_psd_nonneg hfloor hP
  have hcompressed : (P * G * P).trace = (G * P).trace := by
    calc
      (P * G * P).trace = (P * (P * G)).trace :=
        Matrix.trace_mul_comm (P * G) P
      _ = (P * P * G).trace := by rw [Matrix.mul_assoc]
      _ = (P * G).trace := by rw [hP_sq]
      _ = (G * P).trace := Matrix.trace_mul_comm P G
  rw [hcompressed]
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, hP_trace] at hnonneg
  linarith

/-- Nonzero two-vector interference removes the zero- and one-dimensional
members from the Hurwitz list, leaving precisely dimensions three and seven.
This is the arithmetic implication used after the classical classification. -/
theorem nonzero_interference_reduces_hurwitz_dimensions
    (d : ℕ) (hd : d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 7) (hinterference : 2 ≤ d) :
    d = 3 ∨ d = 7 := by
  omega

end NCG
