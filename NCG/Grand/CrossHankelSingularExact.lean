/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.CrossHankel
import NCG.Grand.ExactSourceSchurResidual

/-!
# Rank-deficient cross-Hankel chronology

This is the Moore--Penrose version of the cross-Hankel alternative.  The clock
history Gram may be singular: its spectral pseudoinverse gives the orthogonal
history projection, the positive Schur residual, the exact joint-rank
increment, and the minimum-norm history coefficient formula.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- Vanishing of the singular history residual gives the canonical
Moore--Penrose coefficient matrix, without any independence or positive
definiteness assumption on the clock histories. -/
theorem singularHistoryResidual_reconstruction
    {h ec eg : ℕ} (K : Matrix (Fin h) (Fin ec) ℂ)
    (V : Matrix (Fin h) (Fin eg) ℂ)
    (hzero : sourceSchurResidual K V = 0) :
    V = K * (sourceGramPseudoinverse K * (Kᴴ * V)) := by
  obtain ⟨R, hV⟩ :=
    (sourceSchurResidual_eq_zero_iff_rangeIncluded K V).mp hzero
  have hfix := (sourceCoefficientSupport_properties K).2.2
  change K * (sourceGramPseudoinverse K * (Kᴴ * K)) = K at hfix
  rw [hV]
  calc
    K * R = (K * (sourceGramPseudoinverse K * (Kᴴ * K))) * R := by
      rw [hfix]
    _ = K * (sourceGramPseudoinverse K * (Kᴴ * (K * R))) := by
      simp only [Matrix.mul_assoc]

/-- Complete rank-deficient chronology packet in canonical finite
coordinates.  Taking `K` and `V` to be the clock and geometry Krylov matrices
gives the manuscript's singular cross-Hankel theorem; `cross_hankel_gram`
identifies their entries with the displayed moments. -/
theorem crossHankel_rankDeficient_chronologyAlternative
    {h ec eg : ℕ} (K : Matrix (Fin h) (Fin ec) ℂ)
    (V : Matrix (Fin h) (Fin eg) ℂ) :
    sourceSchurResidual K V =
        Vᴴ * (1 - sourceRangeProjection K) * V
    ∧ (sourceSchurResidual K V).PosSemidef
    ∧ (sourceSchurResidual K V = 0 ↔ SourceRangeIncluded V K)
    ∧ (Matrix.fromBlocks (Kᴴ * K) (Kᴴ * V)
          ((Kᴴ * V)ᴴ) (Vᴴ * V)).rank - (Kᴴ * K).rank
        = (sourceSchurResidual K V).rank
    ∧ (sourceSchurResidual K V = 0 →
        V = K * (sourceGramPseudoinverse K * (Kᴴ * V))) := by
  exact ⟨(exact_source_schur_residual K V).1,
    (exact_source_schur_residual K V).2.1,
    (exact_source_schur_residual K V).2.2.1,
    (exact_source_schur_residual K V).2.2.2,
    singularHistoryResidual_reconstruction K V⟩

end NCG
