/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.K4CutCycleIsotypicSchur

/-!
# Positivity of the faithful `K₄` cut/cycle Gram blocks

This file closes the remaining basis-instantiation and positivity step in
`thm:SMST-record-native-generations`.  In the transported cut/cycle bases the
locked synthesis Gram is a `2 × 2` block matrix.  The explicit `S₄` Schur
calculation makes the diagonal blocks scalar and kills the cross blocks;
injectivity of the synthesis then makes both scalar coefficients positive.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- A faithful locked synthesis whose Gram blocks have the two generator
covariances has strictly positive scalar cut and cycle blocks.  Thus, in the
explicit cut/cycle isotypic basis, its Gram is exactly
`α P_cut + β P_cyc` with `α, β > 0`. -/
theorem k4CutCycle_faithfulGram_blockScalar_positive
    {ι : Type*} [Fintype ι]
    (Q : Matrix ι (Sum (Fin 3) (Fin 3)) ℂ)
    (hQ : Function.Injective Q.mulVec)
    (A B C D : Matrix (Fin 3) (Fin 3) ℂ)
    (hGram : Qᴴ * Q = Matrix.fromBlocks A B C D)
    (hAs : A * k4StandardTransposition = k4StandardTransposition * A)
    (hAt : A * k4StandardFourCycle = k4StandardFourCycle * A)
    (hDs : D * k4StandardTransposition = k4StandardTransposition * D)
    (hDt : D * k4StandardFourCycle = k4StandardFourCycle * D)
    (hBs : B * k4StandardTransposition = -(k4StandardTransposition * B))
    (hBt : B * k4StandardFourCycle = -(k4StandardFourCycle * B))
    (hCs : C * k4StandardTransposition = -(k4StandardTransposition * C))
    (hCt : C * k4StandardFourCycle = -(k4StandardFourCycle * C)) :
    ∃ α β : ℂ, 0 < α ∧ 0 < β ∧
      Qᴴ * Q = Matrix.fromBlocks (α • 1) 0 0 (β • 1) := by
  obtain ⟨α, β, hA, hD, hB, hC⟩ :=
    k4CutCycle_equivariantGram_blockScalar A B C D
      hAs hAt hDs hDt hBs hBt hCs hCt
  have hpos : (Qᴴ * Q).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self Q hQ
  have hblock : Qᴴ * Q = Matrix.fromBlocks (α • 1) 0 0 (β • 1) := by
    simpa [hA, hD, hB, hC] using hGram
  have hx : Sum.elim (Pi.single (0 : Fin 3) 1) (0 : Fin 3 → ℂ) ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl (0 : Fin 3))
    simpa using this
  have hy : Sum.elim (0 : Fin 3 → ℂ) (Pi.single (0 : Fin 3) 1) ≠ 0 := by
    intro h
    have := congrFun h (Sum.inr (0 : Fin 3))
    simpa using this
  have hα : 0 < α := by
    have h := hpos.dotProduct_mulVec_pos hx
    rw [hblock] at h
    simpa [Matrix.fromBlocks_mulVec, dotProduct, Fin.sum_univ_three] using h
  have hβ : 0 < β := by
    have h := hpos.dotProduct_mulVec_pos hy
    rw [hblock] at h
    simpa [Matrix.fromBlocks_mulVec, dotProduct, Fin.sum_univ_three] using h
  exact ⟨α, β, hα, hβ, hblock⟩

end NCG
