/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact small transverse step
  (`lem:small-transverse-step-master`, flagship manuscript)

For `0 ≤ η ≤ 2θ`, `0 < θ ≤ π/2`, with `s = sin(η/2)/sinθ`,
`β = 2 arcsin s`, `z = cos(β/2) - i cosθ sin(β/2)`, `φ = arg z`,
and `a = φ + π/2`, `c = φ - π/2`, the boxed pulse identity

  `exp(-iη σ_y/2) = Z(a) N_θ(β) Z(c)`

holds exactly (`small_transverse_step`): the range condition gives
`0 ≤ s ≤ 1`, `|z|² = 1 - sin²θ sin²(β/2) = cos²(η/2)`, and the
four matrix entries reduce to `e^{-iφ}z = cos(η/2)`,
`e^{∓iπ/2} = ∓i`, and `sinθ sin(β/2) = sin(η/2)`.  The pulses are
the standard `SU(2)` matrices `Z(φ) = diag(e^{-iφ/2}, e^{iφ/2})`,
`N_θ(β) = exp(-iβ(cosθ σ_z + sinθ σ_x)/2)`, written in closed
form (disclosed).
-/

open Complex

namespace NCG

noncomputable section

/-- Longitudinal pulse `Z(φ) = diag(e^{-iφ/2}, e^{iφ/2})`. -/
def pulseZ (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp ((-(φ / 2) : ℝ) * Complex.I), 0;
     0, Complex.exp (((φ / 2) : ℝ) * Complex.I)]

/-- Tilted-axis pulse `N_θ(β) = exp(-iβ(cosθ σ_z + sinθ σ_x)/2)`
in closed form. -/
def pulseN (θ β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (β / 2) : ℝ)
      - ((Real.cos θ * Real.sin (β / 2) : ℝ)) * Complex.I,
     -(((Real.sin θ * Real.sin (β / 2) : ℝ)) * Complex.I);
     -(((Real.sin θ * Real.sin (β / 2) : ℝ)) * Complex.I),
     (Real.cos (β / 2) : ℝ)
      + ((Real.cos θ * Real.sin (β / 2) : ℝ)) * Complex.I]

/-- Transverse rotation `Y(η) = exp(-iη σ_y/2)`. -/
def pulseY (η : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (η / 2) : ℝ), -(Real.sin (η / 2) : ℝ);
     (Real.sin (η / 2) : ℝ), (Real.cos (η / 2) : ℝ)]

/-- `lem:small-transverse-step-master`, boxed identity:
`exp(-iη σ_y/2) = Z(φ+π/2) N_θ(β) Z(φ-π/2)`. -/
theorem small_transverse_step (θ η s β : ℝ) (z : ℂ) (φ : ℝ)
    (hθ0 : 0 < θ) (hθ : θ ≤ Real.pi / 2)
    (hη0 : 0 ≤ η) (hη : η ≤ 2 * θ)
    (hs : s = Real.sin (η / 2) / Real.sin θ)
    (hβ : β = 2 * Real.arcsin s)
    (hz : z = (Real.cos (β / 2) : ℝ)
      - ((Real.cos θ * Real.sin (β / 2) : ℝ)) * Complex.I)
    (hφ : φ = z.arg) :
    pulseZ (φ + Real.pi / 2) * pulseN θ β
      * pulseZ (φ - Real.pi / 2) = pulseY η := by
  have hπ := Real.pi_pos
  have hsθ : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith)
  have hsη : 0 ≤ Real.sin (η / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs0 : 0 ≤ s := by
    rw [hs]
    positivity
  have hmono : Real.sin (η / 2) ≤ Real.sin θ := by
    refine Real.strictMonoOn_sin.monotoneOn
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      (by linarith)
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one hsθ]
    exact hmono
  have hsinβ : Real.sin (β / 2) = s := by
    rw [hβ, show 2 * Real.arcsin s / 2 = Real.arcsin s by ring,
      Real.sin_arcsin (by linarith) hs1]
  have hss : Real.sin θ * Real.sin (β / 2) = Real.sin (η / 2) := by
    rw [hsinβ, hs]
    field_simp
  have hcosη : 0 ≤ Real.cos (η / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have e1 : Real.cos (β / 2) ^ 2 = 1 - Real.sin (β / 2) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (β / 2)]
  have e2 : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  have e3 : Real.cos (η / 2) ^ 2 = 1 - Real.sin (η / 2) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (η / 2)]
  have e4 : Real.sin θ ^ 2 * Real.sin (β / 2) ^ 2
      = Real.sin (η / 2) ^ 2 := by
    have h := congrArg (fun x => x ^ 2) hss
    simpa [mul_pow] using h
  have hnormSq : Complex.normSq z = Real.cos (η / 2) ^ 2 := by
    rw [hz]
    simp only [Complex.normSq_apply, Complex.sub_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.sub_im,
      Complex.mul_im]
    linear_combination e1 + Real.sin (β / 2) ^ 2 * e2 - e3 - e4
  have hnorm : ‖z‖ = Real.cos (η / 2) := by
    have h2 : ‖z‖ ^ 2 = Real.cos (η / 2) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hnormSq
    rw [← Real.sqrt_sq (norm_nonneg z), h2, Real.sqrt_sq hcosη]
  have hpolar : z = (Real.cos (η / 2) : ℂ)
      * Complex.exp ((φ : ℝ) * Complex.I) := by
    rw [hφ, ← hnorm]
    exact (Complex.norm_mul_exp_arg_mul_I z).symm
  have hpolar' : ((Real.cos (β / 2) : ℝ) : ℂ)
      + ((Real.cos θ * Real.sin (β / 2) : ℝ)) * Complex.I
      = (Real.cos (η / 2) : ℂ)
        * Complex.exp ((-φ : ℝ) * Complex.I) := by
    have h := congrArg (starRingEnd ℂ) hpolar
    rw [hz, map_sub, map_mul, map_mul, Complex.conj_ofReal,
      Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_conj,
      map_mul, Complex.conj_ofReal, Complex.conj_I,
      Complex.conj_ofReal] at h
    rw [show ((Real.cos (β / 2) : ℝ) : ℂ)
        + ((Real.cos θ * Real.sin (β / 2) : ℝ)) * Complex.I
        = ((Real.cos (β / 2) : ℝ) : ℂ)
          - ((Real.cos θ * Real.sin (β / 2) : ℝ)) * -Complex.I
        from by ring,
      show ((-φ : ℝ) : ℂ) * Complex.I = ((φ : ℝ) : ℂ) * -Complex.I
        from by push_cast; ring]
    exact h
  have hdiag : ∀ d1 d2 a b c d : ℂ,
      !![d1, 0; 0, d2] * !![a, b; c, d]
        = !![d1 * a, d1 * b; d2 * c, d2 * d] := by
    intro d1 d2 a b c d
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hdiag' : ∀ a b c d e1 e2 : ℂ,
      !![a, b; c, d] * !![e1, 0; 0, e2]
        = !![a * e1, b * e2; c * e1, d * e2] := by
    intro a b c d e1 e2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [pulseZ, pulseZ, pulseN, pulseY, hdiag, hdiag']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
  · -- (0,0)
    rw [← hz, hpolar,
      show Complex.exp ((-((φ + Real.pi / 2) / 2) : ℝ) * Complex.I)
          * ((Real.cos (η / 2) : ℂ)
            * Complex.exp ((φ : ℝ) * Complex.I))
          * Complex.exp ((-((φ - Real.pi / 2) / 2) : ℝ)
            * Complex.I)
        = (Real.cos (η / 2) : ℂ)
          * (Complex.exp ((-((φ + Real.pi / 2) / 2) : ℝ)
              * Complex.I)
            * Complex.exp ((φ : ℝ) * Complex.I)
            * Complex.exp ((-((φ - Real.pi / 2) / 2) : ℝ)
              * Complex.I)) from by ring,
      ← Complex.exp_add, ← Complex.exp_add,
      show ((-((φ + Real.pi / 2) / 2) : ℝ) : ℂ) * Complex.I
          + ((φ : ℝ) : ℂ) * Complex.I
          + ((-((φ - Real.pi / 2) / 2) : ℝ) : ℂ) * Complex.I = 0
        from by push_cast; ring,
      Complex.exp_zero, mul_one]
  · -- (0,1)
    rw [hss,
      show Complex.exp ((-((φ + Real.pi / 2) / 2) : ℝ) * Complex.I)
          * (-(((Real.sin (η / 2) : ℝ)) * Complex.I))
          * Complex.exp (((φ - Real.pi / 2) / 2 : ℝ) * Complex.I)
        = -(((Real.sin (η / 2) : ℝ)) * Complex.I)
          * (Complex.exp ((-((φ + Real.pi / 2) / 2) : ℝ)
              * Complex.I)
            * Complex.exp (((φ - Real.pi / 2) / 2 : ℝ)
              * Complex.I)) from by ring,
      ← Complex.exp_add,
      show ((-((φ + Real.pi / 2) / 2) : ℝ) : ℂ) * Complex.I
          + (((φ - Real.pi / 2) / 2 : ℝ) : ℂ) * Complex.I
          = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I
        from by push_cast; ring,
      show Complex.exp (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I)
          = -Complex.I from by
        rw [Complex.exp_mul_I, ← Complex.ofReal_cos,
          ← Complex.ofReal_sin]
        norm_num]
    ring_nf
    rw [Complex.I_sq]
    ring
  · -- (1,0)
    rw [hss,
      show Complex.exp (((φ + Real.pi / 2) / 2 : ℝ) * Complex.I)
          * (-(((Real.sin (η / 2) : ℝ)) * Complex.I))
          * Complex.exp ((-((φ - Real.pi / 2) / 2) : ℝ)
            * Complex.I)
        = -(((Real.sin (η / 2) : ℝ)) * Complex.I)
          * (Complex.exp (((φ + Real.pi / 2) / 2 : ℝ) * Complex.I)
            * Complex.exp ((-((φ - Real.pi / 2) / 2) : ℝ)
              * Complex.I)) from by ring,
      ← Complex.exp_add,
      show (((φ + Real.pi / 2) / 2 : ℝ) : ℂ) * Complex.I
          + ((-((φ - Real.pi / 2) / 2) : ℝ) : ℂ) * Complex.I
          = (((Real.pi / 2) : ℝ) : ℂ) * Complex.I
        from by push_cast; ring,
      show Complex.exp ((((Real.pi / 2) : ℝ) : ℂ) * Complex.I)
          = Complex.I from by
        rw [Complex.exp_mul_I, ← Complex.ofReal_cos,
          ← Complex.ofReal_sin]
        norm_num]
    ring_nf
    rw [Complex.I_sq]
    ring
  · -- (1,1)
    rw [hpolar',
      show Complex.exp (((φ + Real.pi / 2) / 2 : ℝ) * Complex.I)
          * ((Real.cos (η / 2) : ℂ)
            * Complex.exp ((-φ : ℝ) * Complex.I))
          * Complex.exp (((φ - Real.pi / 2) / 2 : ℝ) * Complex.I)
        = (Real.cos (η / 2) : ℂ)
          * (Complex.exp (((φ + Real.pi / 2) / 2 : ℝ) * Complex.I)
            * Complex.exp ((-φ : ℝ) * Complex.I)
            * Complex.exp (((φ - Real.pi / 2) / 2 : ℝ)
              * Complex.I)) from by ring,
      ← Complex.exp_add, ← Complex.exp_add,
      show (((φ + Real.pi / 2) / 2 : ℝ) : ℂ) * Complex.I
          + ((-φ : ℝ) : ℂ) * Complex.I
          + (((φ - Real.pi / 2) / 2 : ℝ) : ℂ) * Complex.I = 0
        from by push_cast; ring,
      Complex.exp_zero, mul_one]

end

end NCG
