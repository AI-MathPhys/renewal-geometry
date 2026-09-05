/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompletionAggregateInversion

/-!
# Synthesized range of the geometric dwell aggregate

This proves the boxed range identity in
`def:provenance-aware-connected-packet`: after any synthesis `J`, the signed
completion aggregate and the unsummed centered provenance channel have
exactly the same column range.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NCG
namespace CompletionAggregateSynthesizedRange

/-- The geometric-dwell aggregate
`A_s = (1-s) D (I-sD)⁻¹`, represented by its convergent Neumann series. -/
noncomputable def geometricDwellAggregate {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  (((1 - s : ℝ) : ℂ) •
    (D * ∑' k : ℕ, ((s : ℂ) • D) ^ k))

/-- Right multiplication cannot enlarge a matrix's synthesized column
range. -/
theorem range_mulVecLin_mul_le {a b c : Type*} [Fintype b] [Fintype c]
    (A : Matrix a b ℂ) (B : Matrix b c ℂ) :
    LinearMap.range (A * B).mulVecLin ≤ LinearMap.range A.mulVecLin := by
  rintro y ⟨x, rfl⟩
  refine ⟨B *ᵥ x, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]

/-- `Ran(J A_s) = Ran(J D₀)` for every synthesis `J`.  No injectivity of
`J`, `D₀`, or `A_s` is assumed. -/
theorem synthesized_geometricDwellAggregate_range_eq
    {n h : Type*} [Fintype n] [Fintype h] [DecidableEq n]
    (J : Matrix h n ℂ) (D : Matrix n n ℂ) {s : ℝ}
    (hD : ‖D‖ ≤ 1) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    LinearMap.range (J * geometricDwellAggregate D s).mulVecLin =
      LinearMap.range (J * D).mulVecLin := by
  let Ri : Matrix n n ℂ := ∑' k : ℕ, ((s : ℂ) • D) ^ k
  let A : Matrix n n ℂ := geometricDwellAggregate D s
  let B : Matrix n n ℂ :=
    ((((1 - s : ℝ) : ℂ))⁻¹ • (1 - (s : ℂ) • D))
  obtain ⟨_, _, _, _, _, hAB, _, _, _⟩ :=
    completion_aggregate_inversion_exact D hD hs0 hs1
  have hA : A = D * (((1 - s : ℝ) : ℂ) • Ri) := by
    unfold A geometricDwellAggregate Ri
    simp only [Matrix.mul_smul, Matrix.mul_assoc]
  have hAB' : A * B = D := by
    simpa [A, B, geometricDwellAggregate] using hAB
  have hJA : J * A = (J * D) * (((1 - s : ℝ) : ℂ) • Ri) := by
    rw [hA, Matrix.mul_assoc]
  have hJD : J * D = (J * A) * B := by
    calc
      J * D = J * (A * B) := by rw [hAB']
      _ = (J * A) * B := (Matrix.mul_assoc _ _ _).symm
  apply le_antisymm
  · rw [hJA]
    exact range_mulVecLin_mul_le _ _
  · rw [hJD]
    exact range_mulVecLin_mul_le _ _

end CompletionAggregateSynthesizedRange
end NCG
