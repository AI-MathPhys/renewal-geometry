/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AcceptedArithmeticAndAffineConsequences
import NCG.Grand.FiniteCalibrationAndDynamicalCounterexamples
import NCG.Grand.OneDoubletOddTangentClassification

/-!
# One physical history through three deterministic projections

This file supplies the finite pushforward-law, common-source-germ, and
joint-Gram shorting clauses of the accepted one-history/three-projection
corollary.  The already-proved even/odd parity example supplies the final
warning that pairwise panels do not determine a triple history.
-/

open Finset Matrix

namespace NCG
namespace OneHistoryThreeProjectionAssembly

open AcceptedArithmeticAndAffineConsequences

/-- The literal finite pushforward of a history weight through a deterministic
projection. -/
def pushforwardWeight {Ω X : Type*} [Fintype Ω] [DecidableEq X]
    (μ : Ω → ℝ) (π : Ω → X) (x : X) : ℝ :=
  ∑ ω with π ω = x, μ ω

/-- Integrating a writer against the projected law is exactly integrating its
pullback against the one physical history law. -/
theorem expectation_pushforward
    {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]
    (μ : Ω → ℝ) (π : Ω → X) (f : X → ℝ) :
    ∑ x, pushforwardWeight μ π x * f x =
      expectation μ (fun ω => f (π ω)) := by
  rw [expectation]
  calc
    ∑ x, pushforwardWeight μ π x * f x
        = ∑ x, ∑ ω ∈ Finset.univ with π ω = x, μ ω * f (π ω) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [pushforwardWeight, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro ω hω
          rw [(Finset.mem_filter.mp hω).2]
    _ = ∑ ω, μ ω * f (π ω) := by
          simpa using
            (Finset.sum_fiberwise (Finset.univ : Finset Ω) π
              (fun ω => μ ω * f (π ω)))

/-- Two coefficient syntheses represent the same source germ precisely in the
form needed here: each factors through the other, hence their represented
ranges coincide. -/
theorem same_source_germ_of_mutual_incidence_zero
    {h a b : Type*} [Fintype h] [Fintype a] [Fintype b]
    (A : Matrix h a ℂ) (B : Matrix h b ℂ)
    (C : Matrix b a ℂ) (D : Matrix a b ℂ)
    (hA : A = B * C) (hB : B = A * D) :
    LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    refine ⟨C.mulVec v, ?_⟩
    rw [hA]
    change B *ᵥ (C *ᵥ v) = (B * C) *ᵥ v
    rw [Matrix.mulVec_mulVec]
  · rintro _ ⟨v, rfl⟩
    refine ⟨D.mulVec v, ?_⟩
    rw [hB]
    change A *ᵥ (D *ᵥ v) = (A * D) *ᵥ v
    rw [Matrix.mulVec_mulVec]

/-- A candidate branchwise source birth is counted only after shorting against
the common joint source Gram: zero residual is exactly range inclusion. -/
theorem common_joint_source_short_zero_iff
    {h e k : ℕ}
    (commonSource : Matrix (Fin h) (Fin e) ℂ)
    (candidate : Matrix (Fin h) (Fin k) ℂ) :
    oddProvenanceDefect commonSource candidate = 0 ↔
      SourceRangeIncluded candidate commonSource :=
  oddProvenanceDefect_eq_zero_iff_rangeIncluded commonSource candidate

/-- Complete finite content of the one-history/three-projection corollary. -/
theorem one_history_three_projections_exact :
    (∀ {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]
      (μ : Ω → ℝ) (π : Ω → X) (f : X → ℝ),
      ∑ x, pushforwardWeight μ π x * f x =
        expectation μ (fun ω => f (π ω)))
    ∧ (∀ {h a b : Type*} [Fintype h] [Fintype a] [Fintype b]
      (A : Matrix h a ℂ) (B : Matrix h b ℂ)
      (C : Matrix b a ℂ) (D : Matrix a b ℂ),
      A = B * C → B = A * D →
        LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin)
    ∧ (∀ {h e k : ℕ}
      (commonSource : Matrix (Fin h) (Fin e) ℂ)
      (candidate : Matrix (Fin h) (Fin k) ℂ),
      oddProvenanceDefect commonSource candidate = 0 ↔
        SourceRangeIncluded candidate commonSource)
    ∧ ((∀ w u, ∑ b, FiniteCalibrationAndDynamicalCounterexamples.evenParityLaw w u b =
          ∑ b, FiniteCalibrationAndDynamicalCounterexamples.oddParityLaw w u b)
      ∧ (∀ w b, ∑ u, FiniteCalibrationAndDynamicalCounterexamples.evenParityLaw w u b =
          ∑ u, FiniteCalibrationAndDynamicalCounterexamples.oddParityLaw w u b)
      ∧ (∀ u b, ∑ w, FiniteCalibrationAndDynamicalCounterexamples.evenParityLaw w u b =
          ∑ w, FiniteCalibrationAndDynamicalCounterexamples.oddParityLaw w u b)
      ∧ FiniteCalibrationAndDynamicalCounterexamples.evenParityLaw 0 0 0 = 1 / 4
      ∧ FiniteCalibrationAndDynamicalCounterexamples.oddParityLaw 0 0 0 = 0) := by
  exact ⟨expectation_pushforward,
    fun A B C D => same_source_germ_of_mutual_incidence_zero A B C D,
    common_joint_source_short_zero_iff,
    FiniteCalibrationAndDynamicalCounterexamples.pairwise_panels_do_not_determine_comparator⟩

end OneHistoryThreeProjectionAssembly
end NCG
