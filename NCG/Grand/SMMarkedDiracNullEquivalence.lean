/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMBridgeAndMarkedDirac

/-!
# Marked Dirac null-factorization equivalence

This file completes the null-test clause of `thm:SM-marked-Dirac`.  For a
full-row-rank Gram factor, the two-sided Hilbert--Schmidt null defect vanishes
if and only if the independently measured marked panel factors through the
packet.  The factor is then the unique Moore--Penrose reconstruction already
proved in `SMMarkedDirac`.
-/

open Matrix

namespace NCG
namespace SMMarkedDiracNullEquivalence

variable {r w : Type*} [Fintype r] [Fintype w]
  [DecidableEq r] [DecidableEq w]

/-- The full-row-rank packet projection `Rᴴ (RRᴴ)⁻¹ R`. -/
noncomputable def packetProjection (R : Matrix r w ℂ) : Matrix w w ℂ :=
  Rᴴ * (R * Rᴴ)⁻¹ * R

/-- The literal two-sided trace form of `Δ_null^D`. -/
noncomputable def markedDiracNullDefect (R : Matrix r w ℂ)
    (N : Matrix w w ℂ) : ℂ :=
  ((((1 : Matrix w w ℂ) - packetProjection R) * N)ᴴ
      * (((1 : Matrix w w ℂ) - packetProjection R) * N)).trace
    + ((N * ((1 : Matrix w w ℂ) - packetProjection R))ᴴ
      * (N * ((1 : Matrix w w ℂ) - packetProjection R))).trace

section FullRowRank

variable (R : Matrix r w ℂ) [Invertible (R * Rᴴ)]

/-- The packet projection fixes the synthesis rows on the left. -/
theorem packetProjection_mul_conjTranspose :
    packetProjection R * Rᴴ = Rᴴ := by
  unfold packetProjection
  calc
    (Rᴴ * (R * Rᴴ)⁻¹ * R) * Rᴴ =
        Rᴴ * ((R * Rᴴ)⁻¹ * (R * Rᴴ)) := by
          simp only [Matrix.mul_assoc]
    _ = Rᴴ := by
      rw [Matrix.inv_mul_of_invertible, Matrix.mul_one]

/-- The packet projection fixes the synthesis rows on the right. -/
theorem mul_packetProjection :
    R * packetProjection R = R := by
  unfold packetProjection
  calc
    R * (Rᴴ * (R * Rᴴ)⁻¹ * R) =
        ((R * Rᴴ) * (R * Rᴴ)⁻¹) * R := by
          simp only [Matrix.mul_assoc]
    _ = R := by
      rw [Matrix.mul_inv_of_invertible, Matrix.one_mul]

/-- Every packet factorization has zero two-sided null defect. -/
theorem factorization_implies_nullDefect_zero (N : Matrix w w ℂ)
    (hfac : ∃ D : Matrix r r ℂ, N = Rᴴ * D * R) :
    markedDiracNullDefect R N = 0 := by
  obtain ⟨D, rfl⟩ := hfac
  have hleft : ((1 : Matrix w w ℂ) - packetProjection R) *
      (Rᴴ * D * R) = 0 := by
    calc
      ((1 : Matrix w w ℂ) - packetProjection R) * (Rᴴ * D * R) =
          (Rᴴ - packetProjection R * Rᴴ) * D * R := by
            simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = 0 := by rw [packetProjection_mul_conjTranspose]; simp
  have hright : (Rᴴ * D * R) *
      ((1 : Matrix w w ℂ) - packetProjection R) = 0 := by
    calc
      (Rᴴ * D * R) * ((1 : Matrix w w ℂ) - packetProjection R) =
          Rᴴ * D * (R - R * packetProjection R) := by
            simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
      _ = 0 := by rw [mul_packetProjection]; simp
  simp [markedDiracNullDefect, hleft, hright]

open scoped ComplexOrder in
/-- Exact missing equivalence in `thm:SM-marked-Dirac`: the null test vanishes
iff the marked panel has a unique packet factor, namely the Moore--Penrose
reconstruction `(R†)ᴴ N R†`. -/
theorem nullDefect_zero_iff_existsUnique_factorization (N : Matrix w w ℂ) :
    markedDiracNullDefect R N = 0 ↔
      ∃! D : Matrix r r ℂ, N = Rᴴ * D * R := by
  constructor
  · intro hnull
    have h := sm_marked_dirac_null_exact R N (by
      simpa [markedDiracNullDefect, packetProjection] using hnull)
    let D₀ : Matrix r r ℂ :=
      (Rᴴ * (R * Rᴴ)⁻¹)ᴴ * N * (Rᴴ * (R * Rᴴ)⁻¹)
    refine ⟨D₀, ?_, ?_⟩
    · exact h.1
    · intro D hD
      exact h.2 D hD
  · rintro ⟨D, hD, -⟩
    exact factorization_implies_nullDefect_zero R N ⟨D, hD⟩

end FullRowRank

end SMMarkedDiracNullEquivalence
end NCG
