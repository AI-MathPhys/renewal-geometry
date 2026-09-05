/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/

import Mathlib

/-!
# Spectral compression defects and quasidiagonal off-diagonal blocks

This file proves the algebraic and C-star identities behind (SP.27)--(SP.28)
in `thm:GT-NCG-essential-image-trichotomy`.  For a self-adjoint idempotent
`P`, compression fails to be multiplicative by the corner
`P a (1-P) b P`.  On the pair `(a⋆,a)` this is the positive square of the
off-diagonal block `(1-P)aP`, so its norm is exactly the square of that block's
norm.  Applying the same identity to `a⋆` controls the opposite block.
-/

namespace NCG.SpectralCompression

variable {A : Type*}

/-- Compression of an algebra element to the range of `P`. -/
def compress [Mul A] (P a : A) : A := P * a * P

/-- The exact multiplicativity defect (SP.28). -/
theorem compress_mul_sub_mul_compress
    [Ring A] (P a b : A) (hP : P * P = P) :
    compress P (a * b) - compress P a * compress P b =
      P * a * (1 - P) * b * P := by
  simp only [compress]
  rw [show P * a * P * (P * b * P) = P * a * (P * P) * b * P by
    noncomm_ring]
  rw [hP]
  noncomm_ring

/-- For a self-adjoint projection, the `(a⋆,a)` compression defect is the
positive square of the outgoing off-diagonal corner. -/
theorem compress_star_mul_sub_mul_compress
    [Ring A] [StarRing A] (P a : A) (hP : P * P = P) (hPstar : star P = P) :
    compress P (star a * a) - compress P (star a) * compress P a =
      star ((1 - P) * a * P) * ((1 - P) * a * P) := by
  rw [compress_mul_sub_mul_compress P (star a) a hP]
  have hcomp : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP]; noncomm_ring
  have hstar : star ((1 - P) * a * P) = P * star a * (1 - P) := by
    simp only [star_mul, star_sub, star_one, hPstar, mul_assoc]
  rw [hstar]
  calc
    P * star a * (1 - P) * a * P =
        (P * star a) * ((1 - P) * (a * P)) := by noncomm_ring
    _ = (P * star a) * ((1 - P) * ((1 - P) * (a * P))) := by
      congr 1
      calc
        (1 - P) * (a * P) = ((1 - P) * (1 - P)) * (a * P) := by rw [hcomp]
        _ = (1 - P) * ((1 - P) * (a * P)) := by rw [mul_assoc]
    _ = (P * star a * (1 - P)) * ((1 - P) * a * P) := by noncomm_ring

/-- C-star norm form of the preceding positive-square identity. -/
theorem norm_compress_star_mul_defect
    [CStarAlgebra A]
    (P a : A) (hP : P * P = P) (hPstar : star P = P) :
    ‖compress P (star a * a) - compress P (star a) * compress P a‖ =
      ‖(1 - P) * a * P‖ ^ 2 := by
  rw [compress_star_mul_sub_mul_compress P a hP hPstar]
  simpa only [pow_two] using
    (CStarRing.norm_star_mul_self (x := (1 - P) * a * P))

/-- Vanishing of the positive compression defect is equivalent to vanishing
of the outgoing off-diagonal block. -/
theorem compress_star_mul_defect_eq_zero_iff
    [CStarAlgebra A]
    (P a : A) (hP : P * P = P) (hPstar : star P = P) :
    compress P (star a * a) - compress P (star a) * compress P a = 0 ↔
      (1 - P) * a * P = 0 := by
  rw [compress_star_mul_sub_mul_compress P a hP hPstar]
  constructor
  · intro h
    have hn : ‖(1 - P) * a * P‖ * ‖(1 - P) * a * P‖ = 0 := by
      rw [← CStarRing.norm_star_mul_self, h, norm_zero]
    have : ‖(1 - P) * a * P‖ = 0 := mul_self_eq_zero.mp hn
    exact norm_eq_zero.mp this
  · intro h
    rw [h, star_zero, zero_mul]

/-- The same test on `a⋆` detects the incoming off-diagonal block. -/
theorem norm_compress_mul_star_defect
    [CStarAlgebra A]
    (P a : A) (hP : P * P = P) (hPstar : star P = P) :
    ‖compress P (a * star a) - compress P a * compress P (star a)‖ =
      ‖P * a * (1 - P)‖ ^ 2 := by
  have h := norm_compress_star_mul_defect P (star a) hP hPstar
  rw [star_star] at h
  calc
    ‖compress P (a * star a) - compress P a * compress P (star a)‖ =
        ‖(1 - P) * star a * P‖ ^ 2 := h
    _ = ‖star (P * a * (1 - P))‖ ^ 2 := by
      simp only [star_mul, star_sub, star_one, hPstar, mul_assoc]
    _ = ‖P * a * (1 - P)‖ ^ 2 := by rw [norm_star]

/-- A quantitative strict-multiplicativity estimate from one off-diagonal
corner, valid in every normed ring. -/
theorem norm_compression_defect_le
    [NormedRing A] (P a b : A) (hP : P * P = P) :
    ‖compress P (a * b) - compress P a * compress P b‖ ≤
      ‖P‖ * ‖a‖ * ‖(1 - P) * b * P‖ := by
  rw [compress_mul_sub_mul_compress P a b hP]
  calc
    ‖P * a * (1 - P) * b * P‖ = ‖P * a * ((1 - P) * b * P)‖ := by
      congr 1
      noncomm_ring
    _ ≤ ‖P * a‖ * ‖(1 - P) * b * P‖ := norm_mul_le _ _
    _ ≤ (‖P‖ * ‖a‖) * ‖(1 - P) * b * P‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le P a) (norm_nonneg _)

end NCG.SpectralCompression
