/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.SpectralCompressionMultiplicativityExact
import Mathlib.Analysis.Real.Sqrt

/-!
# Strict compression is equivalent to quasidiagonal off-diagonal decay

This is the sequence/filter-level completion of (SP.27)--(SP.28).  For any
family of self-adjoint idempotents in a C-star algebra, norm multiplicativity
of all compressions is equivalent to norm decay of both off-diagonal corners.
No uniform projection bound is assumed: the C-star identity derives
`‖P‖ ≤ 1` directly from self-adjoint idempotence.
-/

namespace NCG.SpectralCompression

open Filter Topology

variable {A X : Type*} [CStarAlgebra A]

/-- Norm-multiplicativity of compression along a filter. -/
def NormMultiplicativeAlong (P : X → A) (l : Filter X) : Prop :=
  ∀ a b : A, Tendsto
    (fun n => ‖compress (P n) (a * b) -
      compress (P n) a * compress (P n) b‖) l (𝓝 0)

/-- Both quasidiagonal off-diagonal corners vanish in norm. -/
def QuasidiagonalAlong (P : X → A) (l : Filter X) : Prop :=
  ∀ a : A,
    Tendsto (fun n => ‖(1 - P n) * a * P n‖) l (𝓝 0) ∧
    Tendsto (fun n => ‖P n * a * (1 - P n)‖) l (𝓝 0)

/-- Every self-adjoint idempotent in a C-star algebra has norm at most one. -/
theorem norm_le_one_of_selfAdjoint_idempotent (P : A)
    (hP : P * P = P) (hPstar : star P = P) : ‖P‖ ≤ 1 := by
  have hsq : ‖P‖ ^ 2 = ‖P‖ := by
    calc
      ‖P‖ ^ 2 = ‖star P * P‖ := by
        simpa only [pow_two] using (CStarRing.norm_star_mul_self (x := P)).symm
      _ = ‖P‖ := by rw [hPstar, hP]
  nlinarith [norm_nonneg P]

/-- Strict norm-monoidality is exactly two-sided quasidiagonal decay. -/
theorem normMultiplicativeAlong_iff_quasidiagonalAlong
    (P : X → A) (l : Filter X)
    (hP : ∀ n, P n * P n = P n)
    (hPstar : ∀ n, star (P n) = P n) :
    NormMultiplicativeAlong P l ↔ QuasidiagonalAlong P l := by
  constructor
  · intro hmul a
    constructor
    · have hsq : Tendsto (fun n => ‖(1 - P n) * a * P n‖ ^ 2)
          l (𝓝 0) := by
        convert hmul (star a) a using 1
        · funext n
          exact (norm_compress_star_mul_defect
            (P n) a (hP n) (hPstar n)).symm
      have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
      change Tendsto
        (fun n => Real.sqrt (‖(1 - P n) * a * P n‖ ^ 2))
        l (𝓝 (Real.sqrt 0)) at hsqrt
      simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
    · have hsq : Tendsto (fun n => ‖P n * a * (1 - P n)‖ ^ 2)
          l (𝓝 0) := by
        convert hmul a (star a) using 1
        · funext n
          exact (norm_compress_mul_star_defect
            (P n) a (hP n) (hPstar n)).symm
      have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
      change Tendsto
        (fun n => Real.sqrt (‖P n * a * (1 - P n)‖ ^ 2))
        l (𝓝 (Real.sqrt 0)) at hsqrt
      simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  · intro hqd a b
    have hupper : Tendsto
        (fun n => ‖a‖ * ‖(1 - P n) * b * P n‖) l (𝓝 0) := by
      simpa using (hqd b).1.const_mul ‖a‖
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hupper
    calc
      ‖compress (P n) (a * b) -
          compress (P n) a * compress (P n) b‖
          ≤ ‖P n‖ * ‖a‖ * ‖(1 - P n) * b * P n‖ :=
            norm_compression_defect_le (P n) a b (hP n)
      _ ≤ ‖a‖ * ‖(1 - P n) * b * P n‖ := by
        have hp := norm_le_one_of_selfAdjoint_idempotent
          (P n) (hP n) (hPstar n)
        have hnonneg : 0 ≤ ‖a‖ * ‖(1 - P n) * b * P n‖ :=
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
        calc
          ‖P n‖ * ‖a‖ * ‖(1 - P n) * b * P n‖ =
              ‖P n‖ * (‖a‖ * ‖(1 - P n) * b * P n‖) := by ring
          _ ≤ 1 * (‖a‖ * ‖(1 - P n) * b * P n‖) :=
            mul_le_mul_of_nonneg_right hp hnonneg
          _ = ‖a‖ * ‖(1 - P n) * b * P n‖ := one_mul _

end NCG.SpectralCompression
