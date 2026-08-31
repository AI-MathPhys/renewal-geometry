import Mathlib
import NCG.Grand.FeedbackTail

/-!
# Massive Green locality from exponential Duhamel bounds

This module integrates the weighted first- and second-response estimates on the
positive half-line.  The two scalar moments are evaluated exactly, so the
resulting constants are the manuscript constants rather than coarse bounds.
-/

open MeasureTheory Real Set

namespace NCG
namespace GreenLocalityLaplaceBounds

/-- The exact second time moment of an exponential tail. -/
theorem time_sq_mul_exp_tail_integral (a : ℝ) (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), t ^ 2 * Real.exp (-(a * t))) = 2 / a ^ 3 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (3 : ℝ)) (r := a) (by norm_num) ha
  norm_num [Real.rpow_two] at h ⊢
  rw [h]
  field_simp

/-- Integrability of the first exponential time moment. -/
theorem integrableOn_time_mul_exp_tail (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(a * t))) (Ioi 0) := by
  refine .of_integral_ne_zero ?_
  rw [NCG.time_mul_exp_tail_integral a ha]
  positivity

/-- Integrability of the second exponential time moment. -/
theorem integrableOn_time_sq_mul_exp_tail (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (-(a * t))) (Ioi 0) := by
  refine .of_integral_ne_zero ?_
  rw [time_sq_mul_exp_tail_integral a ha]
  positivity

section Banach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- A positive-time response bounded by
`M² t exp (ωt) ‖V‖` has a massive Green transform bounded by
`M² (μ-ω)⁻² ‖V‖`. -/
theorem norm_firstGreen_le
    (D : ℝ → E) (μ ω M v : ℝ)
    (hgap : ω < μ) (hM : 0 ≤ M) (hv : 0 ≤ v)
    (hmeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-(μ * t)) • D t)
      (volume.restrict (Ioi 0)))
    (hD : ∀ t : ℝ, 0 < t →
      ‖D t‖ ≤ M ^ 2 * t * Real.exp (ω * t) * v) :
    ‖∫ t in Ioi (0 : ℝ), Real.exp (-(μ * t)) • D t‖
      ≤ M ^ 2 / (μ - ω) ^ 2 * v := by
  have ha : 0 < μ - ω := sub_pos.mpr hgap
  let C : ℝ := M ^ 2 * v
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg M) hv
  have hmajor : IntegrableOn
      (fun t : ℝ => C * (t * Real.exp (-((μ - ω) * t)))) (Ioi 0) :=
    (integrableOn_time_mul_exp_tail (μ - ω) ha).const_mul C
  have hpoint : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖Real.exp (-(μ * t)) • D t‖
        ≤ C * (t * Real.exp (-((μ - ω) * t))) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 ≤ t := le_of_lt ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-(μ * t)) * ‖D t‖
          ≤ Real.exp (-(μ * t)) *
              (M ^ 2 * t * Real.exp (ω * t) * v) := by
            gcongr
            exact hD t ht
      _ = C * (t * Real.exp (-((μ - ω) * t))) := by
            rw [show -((μ - ω) * t) = -(μ * t) + ω * t by ring,
              Real.exp_add]
            simp only [C]
            ring
  have hint : IntegrableOn
      (fun t : ℝ => Real.exp (-(μ * t)) • D t) (Ioi 0) :=
    Integrable.mono' hmajor hmeas hpoint
  calc
    ‖∫ t in Ioi (0 : ℝ), Real.exp (-(μ * t)) • D t‖
        ≤ ∫ t in Ioi (0 : ℝ),
            C * (t * Real.exp (-((μ - ω) * t))) :=
      norm_integral_le_of_norm_le hmajor hpoint
    _ = C * (1 / (μ - ω) ^ 2) := by
      rw [integral_const_mul, NCG.time_mul_exp_tail_integral (μ - ω) ha]
    _ = M ^ 2 / (μ - ω) ^ 2 * v := by
      simp only [C]
      ring

/-- A positive-time pair response bounded by
`M³ t² exp (ωt) ‖V‖ ‖W‖` has the exact massive Green bound
`2 M³ (μ-ω)⁻³ ‖V‖ ‖W‖`. -/
theorem norm_pairGreen_le
    (Q : ℝ → E) (μ ω M v w : ℝ)
    (hgap : ω < μ) (hM : 0 ≤ M) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hmeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-(μ * t)) • Q t)
      (volume.restrict (Ioi 0)))
    (hQ : ∀ t : ℝ, 0 < t →
      ‖Q t‖ ≤ M ^ 3 * t ^ 2 * Real.exp (ω * t) * v * w) :
    ‖∫ t in Ioi (0 : ℝ), Real.exp (-(μ * t)) • Q t‖
      ≤ 2 * M ^ 3 / (μ - ω) ^ 3 * v * w := by
  have ha : 0 < μ - ω := sub_pos.mpr hgap
  let C : ℝ := M ^ 3 * v * w
  have hC : 0 ≤ C := by positivity
  have hmajor : IntegrableOn
      (fun t : ℝ => C * (t ^ 2 * Real.exp (-((μ - ω) * t)))) (Ioi 0) :=
    (integrableOn_time_sq_mul_exp_tail (μ - ω) ha).const_mul C
  have hpoint : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖Real.exp (-(μ * t)) • Q t‖
        ≤ C * (t ^ 2 * Real.exp (-((μ - ω) * t))) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-(μ * t)) * ‖Q t‖
          ≤ Real.exp (-(μ * t)) *
              (M ^ 3 * t ^ 2 * Real.exp (ω * t) * v * w) := by
            gcongr
            exact hQ t ht
      _ = C * (t ^ 2 * Real.exp (-((μ - ω) * t))) := by
            rw [show -((μ - ω) * t) = -(μ * t) + ω * t by ring,
              Real.exp_add]
            simp only [C]
            ring
  have hint : IntegrableOn
      (fun t : ℝ => Real.exp (-(μ * t)) • Q t) (Ioi 0) :=
    Integrable.mono' hmajor hmeas hpoint
  calc
    ‖∫ t in Ioi (0 : ℝ), Real.exp (-(μ * t)) • Q t‖
        ≤ ∫ t in Ioi (0 : ℝ),
            C * (t ^ 2 * Real.exp (-((μ - ω) * t))) :=
      norm_integral_le_of_norm_le hmajor hpoint
    _ = C * (2 / (μ - ω) ^ 3) := by
      rw [integral_const_mul,
        time_sq_mul_exp_tail_integral (μ - ω) ha]
    _ = 2 * M ^ 3 / (μ - ω) ^ 3 * v * w := by
      simp only [C]
      ring

end Banach

end GreenLocalityLaplaceBounds
end NCG
