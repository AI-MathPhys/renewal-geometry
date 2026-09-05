/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AffineRelativeEntropyIntegralRemainderExact

/-!
# Normalized quadratic remainder for affine relative entropy

Rescaling both integrations in the exact FTC remainder identifies the
normalized second-order quotient with a BKM average over the unit square.
-/

open Matrix Filter Topology MeasureTheory intervalIntegral
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ d : Matrix n n ℂ}

/-- Unit-square BKM average appearing in the normalized affine entropy
remainder. -/
noncomputable def affineBkmQuadraticAverage
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) (t : ℝ) : ℝ :=
  2 * ∫ x in (0 : ℝ)..1,
    x * ∫ y in (0 : ℝ)..1, affineBkmForm hσ hd (t * x * y)

/-- Exact normalized quadratic remainder.  No asymptotic notation is used:
for every nonzero time whose whole segment is faithful, twice the literal
relative entropy divided by `t²` equals the unit-square BKM average. -/
theorem two_mul_inv_sq_mul_affineRelativeEntropy_eq_bkmAverage
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) (htrace : d.trace.re = 0)
    {A B t : ℝ} (ht : t ≠ 0)
    (hpos : ∀ u ∈ Set.Ioo A B, (σ + u • d).PosDef)
    (hseg : Set.uIcc 0 t ⊆ Set.Ioo A B) :
    2 * t⁻¹ ^ 2 * affineRelativeEntropy hσ hd t =
      affineBkmQuadraticAverage hσ hd t := by
  let f : ℝ → ℝ := affineBkmForm hσ hd
  have hmain := affineRelativeEntropy_eq_iteratedBkmIntegral
    hσ hd htrace hpos hseg
  have hinner : ∀ x : ℝ,
      (∫ s in (0 : ℝ)..t * x, f s) =
        (t * x) * ∫ y in (0 : ℝ)..1, f ((t * x) * y) := by
    intro x
    have hs := intervalIntegral.smul_integral_comp_mul_left
      (a := (0 : ℝ)) (b := 1) f (t * x)
    simpa only [mul_zero, mul_one, smul_eq_mul] using hs.symm
  have houter :
      (∫ u in (0 : ℝ)..t, ∫ s in (0 : ℝ)..u, f s) =
        t * ∫ x in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t * x, f s := by
    have hs := intervalIntegral.smul_integral_comp_mul_left
      (a := (0 : ℝ)) (b := 1)
      (fun u : ℝ => ∫ s in (0 : ℝ)..u, f s) t
    simpa only [mul_zero, mul_one, smul_eq_mul] using hs.symm
  have hscaled : affineRelativeEntropy hσ hd t =
      t ^ 2 * ∫ x in (0 : ℝ)..1,
        x * ∫ y in (0 : ℝ)..1, f (t * x * y) := by
    rw [hmain, houter]
    simp_rw [hinner]
    calc
      t * ∫ x in (0 : ℝ)..1,
          (t * x) * ∫ y in (0 : ℝ)..1, f ((t * x) * y)
          = ∫ x in (0 : ℝ)..1,
              t * ((t * x) * ∫ y in (0 : ℝ)..1, f ((t * x) * y)) := by
                rw [intervalIntegral.integral_const_mul]
      _ = ∫ x in (0 : ℝ)..1,
              t ^ 2 * (x * ∫ y in (0 : ℝ)..1, f (t * x * y)) := by
            apply intervalIntegral.integral_congr
            intro x _
            ring
      _ = t ^ 2 * ∫ x in (0 : ℝ)..1,
              x * ∫ y in (0 : ℝ)..1, f (t * x * y) := by
            rw [intervalIntegral.integral_const_mul]
  rw [hscaled]
  unfold affineBkmQuadraticAverage f
  field_simp

end QRE
end NCG
