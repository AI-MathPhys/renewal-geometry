/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCJumpCountTailExact
import NCG.Grand.NaturalGeometricTailIntegrabilityExact
import NCG.Grand.FiniteHorizonFeynmanKacBoundExact

/-!
# Integrability of the genuine finite-CTMC Feynman--Kac expectation

Every exponential moment of the finite-horizon jump count is integrable.
The deterministic occupation-plus-jump bound then proves integrability of
the actual Feynman--Kac path integrand for arbitrary finite-state rewards.
Neither an exponential-moment assumption nor the desired semigroup formula
is used as an input.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace NCG.FiniteCTMCFeynmanKacIntegrability

open DrivenProcess DrivenProcess.FinitePath
open FiniteCTMCJumpCountTail NaturalGeometricTailIntegrability
open FiniteCTMCAdmissiblePathLaw FiniteCTMCFeynmanKacPathMoment
open FiniteCTMCPathCarrierMeasurability FiniteCTMCPathEvaluationMeasurability
open FiniteHorizonFeynmanKacBound FiniteCTMCNonexplosion

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

variable (L : Matrix S S ℝ) (hL : IsGenerator L)
  (hescape : ∀ x, 0 < escapeRate L x)

/-- All real exponential moments of the genuine finite-horizon jump count
are integrable under every point-start CTMC law. -/
theorem integrable_exp_jumpCount (x : S) (c T : ℝ) (hT : 0 ≤ T) :
    Integrable (fun z => Real.exp (c * (admissibleJumpIndex z T : ℝ)))
      (admissiblePathLaw x (pointMass x) L hL hescape) := by
  let μ := admissiblePathLaw x (pointMass x) L hL hescape
  letI : IsProbabilityMeasure μ :=
    admissiblePathLaw_isProbabilityMeasure x (pointMass x) (pointMass_nonnegative x)
      (sum_pointMass x) L hL hescape
  let R := 1 + ∑ y, escapeRate L y
  have hsum : 0 ≤ ∑ y, escapeRate L y := Finset.sum_nonneg fun y _ => (hescape y).le
  have hRpos : 0 < R := by dsimp [R]; linarith
  have hR : ∀ y, escapeRate L y ≤ R := by
    intro y
    have hy := escapeRate_le_sum_escapeRate L hescape y
    dsimp [R]
    linarith
  let s := R * (Real.exp c + 1)
  have hs : 0 ≤ s := (mul_pos hRpos (by positivity : 0 < Real.exp c + 1)).le
  have hden : 0 < R+s := add_pos_of_pos_of_nonneg hRpos hs
  have hqc : (R / (R+s)) * Real.exp c < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hden]
    dsimp [s]
    nlinarith
  apply integrable_exp_of_geometric_tail μ (fun z => admissibleJumpIndex z T)
    (measurable_admissibleJumpIndex T hT) (Real.exp (s*T)) (R / (R+s)) c
    (div_nonneg hRpos.le hden.le) hqc
  intro n
  exact jumpCount_tail_le L hL hescape x s R T hs hRpos hR hT n

/-- Actual integrability of the occupation-plus-directed-jump Feynman--Kac
observable, for arbitrary finite-state rewards and terminal function. -/
theorem integrable_feynmanKacIntegrand
    (x : S) (v : S → ℝ) (g : S → S → ℝ) (k T : ℝ) (f : S → ℝ) (hT : 0 ≤ T) :
    Integrable (feynmanKacIntegrand v g k T f)
      (admissiblePathLaw x (pointMass x) L hL hescape) := by
  let V := ∑ y, |v y|
  let G := ∑ y, ∑ z, |g y z|
  let M := ∑ y, |f y|
  have hV : ∀ y, |v y| ≤ V := fun y =>
    Finset.single_le_sum (fun z _ => abs_nonneg (v z)) (Finset.mem_univ y)
  have hG : ∀ y z, |g y z| ≤ G := by
    intro y z
    exact (Finset.single_le_sum (fun w _ => abs_nonneg (g y w)) (Finset.mem_univ z)).trans
      (Finset.single_le_sum (fun w _ => Finset.sum_nonneg fun u _ => abs_nonneg (g w u))
        (Finset.mem_univ y))
  have hf : ∀ y, |f y| ≤ M := fun y =>
    Finset.single_le_sum (fun z _ => abs_nonneg (f z)) (Finset.mem_univ y)
  have hi := (integrable_exp_jumpCount L hL hescape x (|k| * G) T hT).const_mul
    (Real.exp (|k| * (V*T)) * M)
  apply hi.mono' (measurable_feynmanKacIntegrand v g k T f hT).aestronglyMeasurable
  apply ae_of_all
  intro z
  calc
    ‖feynmanKacIntegrand v g k T f z‖ ≤
        Real.exp (|k| * (V*T + G * (admissibleJumpIndex z T : ℝ))) * M :=
      norm_feynmanKacIntegrand_le v g k V G M T f hV hG hf z hT
    _ = (Real.exp (|k| * (V*T)) * M) *
        Real.exp ((|k| * G) * (admissibleJumpIndex z T : ℝ)) := by
      rw [mul_add, Real.exp_add, ← mul_assoc |k| G]
      ring

end

end NCG.FiniteCTMCFeynmanKacIntegrability
