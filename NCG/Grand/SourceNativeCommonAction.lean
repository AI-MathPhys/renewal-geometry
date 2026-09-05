/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExactSourceSchurResidual
import NCG.Flagship.CommonAction

/-!
# Source-native common-action criterion
  (`thm:SMST-common-action`)

Vanishing of the exact Moore--Penrose source Schur residual first constructs
a comparison factor through the clock source.  The multiplicity-free sector
classification then identifies that factor with its measured `1 + 5` form.
Explicit nonnegative amplitude and phase residuals force both amplitudes to
one and both phases to zero, hence the comparison is the identity.  The
common source, its future moments and its source-dependent control jets agree,
and the exact quadratic Legendre transform gives the reciprocal ADM
coefficients.
-/

open Matrix

namespace NCG
namespace SourceNativeCommonAction

/-- The relative-amplitude defect on the homogeneous and shape modules. -/
def amplitudeResidual (a1 a5 : ℝ) : ℝ :=
  (a1 - 1) ^ 2 + (a5 - 1) ^ 2

/-- The relative-phase defect on the homogeneous and shape modules. -/
def phaseResidual (phi1 phi5 : ℝ) : ℝ :=
  phi1 ^ 2 + phi5 ^ 2

theorem amplitudeResidual_eq_zero_iff (a1 a5 : ℝ) :
    amplitudeResidual a1 a5 = 0 ↔ a1 = 1 ∧ a5 = 1 := by
  constructor
  · intro h
    unfold amplitudeResidual at h
    constructor <;> nlinarith [sq_nonneg (a1 - 1), sq_nonneg (a5 - 1)]
  · rintro ⟨rfl, rfl⟩
    norm_num [amplitudeResidual]

theorem phaseResidual_eq_zero_iff (phi1 phi5 : ℝ) :
    phaseResidual phi1 phi5 = 0 ↔ phi1 = 0 ∧ phi5 = 0 := by
  constructor
  · intro h
    unfold phaseResidual at h
    constructor <;> nlinarith [sq_nonneg phi1, sq_nonneg phi5]
  · rintro ⟨rfl, rfl⟩
    norm_num [phaseResidual]

/-- Exact source-native common-action theorem.  The comparison factor and the
final source equality are conclusions, not hypotheses.  `hsector` is the
multiplicity-free sector classification: it applies to whichever comparison
factor the zero Schur residual constructs. -/
theorem source_native_common_action
    {h q : ℕ}
    (Sclk Sgeo : Matrix (Fin h) (Fin q) ℂ)
    (P1 P5 : Matrix (Fin q) (Fin q) ℂ)
    (hprojectors : P1 + P5 = 1)
    (a1 a5 phi1 phi5 : ℝ)
    (hsector : ∀ R : Matrix (Fin q) (Fin q) ℂ,
      Sgeo = Sclk * R →
      R = ((a1 : ℂ) * Complex.exp (phi1 * Complex.I)) • P1 +
        ((a5 : ℂ) * Complex.exp (phi5 * Complex.I)) • P5)
    (hSchur : sourceSchurResidual Sclk Sgeo = 0)
    (hAmplitude : amplitudeResidual a1 a5 = 0)
    (hPhase : phaseResidual phi1 phi5 = 0)
    (chi : ℝ) (hchi : 0 < chi) :
    Sgeo = Sclk
    ∧ (∀ (transfer : Matrix (Fin h) (Fin h) ℂ) (k : ℕ),
        transfer ^ k * Sgeo = transfer ^ k * Sclk)
    ∧ (∀ controlJet : Matrix (Fin h) (Fin q) ℂ →
          Matrix (Fin h) (Fin q) ℂ,
        controlJet Sgeo = controlJet Sclk)
    ∧ ((3 : ℝ) - 1)⁻¹ = 1 / 2
    ∧ (∀ p : ℝ, IsGreatest
        (Set.range fun v : ℝ ↦ p * v - chi / 2 * v ^ 2)
        (p ^ 2 / (2 * chi)))
    ∧ (∀ LambdaH sqrtq kinetic curvature : ℝ,
        hamiltonianADM chi LambdaH sqrtq kinetic curvature =
            chi⁻¹ * (kinetic / sqrtq) -
              chi * (sqrtq * curvature) + LambdaH * sqrtq
        ∧ chi⁻¹ * chi = 1) := by
  obtain ⟨ha1, ha5⟩ :=
    (amplitudeResidual_eq_zero_iff a1 a5).mp hAmplitude
  obtain ⟨hphi1, hphi5⟩ :=
    (phaseResidual_eq_zero_iff phi1 phi5).mp hPhase
  obtain ⟨R, hfactor⟩ :=
    (sourceSchurResidual_eq_zero_iff_rangeIncluded Sclk Sgeo).mp hSchur
  have hrouter : R = 1 :=
    sector_collapse P1 P5 R hprojectors a1 a5 phi1 phi5
      (hsector R hfactor) ha1 ha5 hphi1 hphi5
  have hsources : Sgeo = Sclk := by
    rw [hfactor, hrouter, Matrix.mul_one]
  refine ⟨hsources, ?_, ?_, by norm_num, legendre_kinetic chi hchi, ?_⟩
  · intro transfer k
    rw [hsources]
  · intro controlJet
    rw [hsources]
  · intro LambdaH sqrtq kinetic curvature
    exact ham_coefficients chi LambdaH sqrtq kinetic curvature hchi.ne'

end SourceNativeCommonAction
end NCG
