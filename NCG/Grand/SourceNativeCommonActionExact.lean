/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExactSourceSchurResidual
import NCG.Flagship.CommonAction

/-!
# Exact source-native common-action criterion
  (`thm:SMST-common-action`)

The comparison router is reconstructed canonically from the two source maps
with the Moore--Penrose source Gram inverse. Vanishing of the exact source
Schur residual proves that this router factors the geometry source through
the clock source. Explicit nonnegative amplitude and phase residuals on the
multiplicity-free `1 + 5` source module then force the router to be the
identity. The common source, all future moments and source-dependent control
jets consequently agree, and the exact quadratic Legendre transform gives
the displayed reciprocal ADM coefficients.
-/

open Matrix

namespace NCG
namespace SourceNativeCommonAction

/-- Canonical comparison router reconstructed from the cross Gram. -/
noncomputable def comparisonRouter {h q : ℕ}
    (Sclk Sgeo : Matrix (Fin h) (Fin q) ℂ) :
    Matrix (Fin q) (Fin q) ℂ :=
  sourceGramPseudoinverse Sclk * (Sclkᴴ * Sgeo)

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

/-- A zero source Schur residual gives the canonical, rather than merely an
existential, comparison factorization. -/
theorem comparisonRouter_factorization {h q : ℕ}
    (Sclk Sgeo : Matrix (Fin h) (Fin q) ℂ)
    (hSchur : sourceSchurResidual Sclk Sgeo = 0) :
    Sgeo = Sclk * comparisonRouter Sclk Sgeo := by
  rcases (sourceSchurResidual_eq_zero_iff_rangeIncluded Sclk Sgeo).mp hSchur
    with ⟨T, hT⟩
  let P := sourceRangeProjection Sclk
  have hPS : P * Sclk = Sclk := by
    simpa only [P] using (sourceGramPseudoinverse_projection Sclk).2.2.2.2.2
  have hcanonical : Sclk * comparisonRouter Sclk Sgeo = Sgeo := by
    calc
      Sclk * comparisonRouter Sclk Sgeo
          = P * Sgeo := by
              simp only [comparisonRouter, P, sourceRangeProjection,
                Matrix.mul_assoc]
      _ = P * (Sclk * T) := by rw [hT]
      _ = (P * Sclk) * T := by rw [Matrix.mul_assoc]
      _ = Sclk * T := by rw [hPS]
      _ = Sgeo := hT.symm
  exact hcanonical.symm

/-- Exact source-native common-action theorem. Neither the source
factorization nor the final source equality is assumed. -/
theorem source_native_common_action_exact {h q : ℕ}
    (Sclk Sgeo : Matrix (Fin h) (Fin q) ℂ)
    (P1 P5 : Matrix (Fin q) (Fin q) ℂ)
    (hprojectors : P1 + P5 = 1)
    (a1 a5 phi1 phi5 : ℝ)
    (hsector : comparisonRouter Sclk Sgeo =
      ((a1 : ℂ) * Complex.exp (phi1 * Complex.I)) • P1 +
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
        (Set.range fun v : ℝ ⇒ p * v - chi / 2 * v ^ 2)
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
  have hrouter : comparisonRouter Sclk Sgeo = 1 :=
    sector_collapse P1 P5 (comparisonRouter Sclk Sgeo)
      hprojectors a1 a5 phi1 phi5 hsector ha1 ha5 hphi1 hphi5
  have hfactor := comparisonRouter_factorization Sclk Sgeo hSchur
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
