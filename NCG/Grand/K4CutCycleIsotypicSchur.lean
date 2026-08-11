/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.NativeGenerations

/-!
# The `S₄` cut/cycle isotypic Schur computation for `K₄`

The cut triplet is the standard representation of `S₄`; the cycle triplet
is its sign twist.  A transposition and a four-cycle generate `S₄`.  This
file computes their simultaneous block commutant explicitly: diagonal blocks
are scalar and the intertwiners between the two inequivalent triplets vanish.
This discharges the Schur hypothesis in
`thm:SMST-record-native-generations`.
-/

namespace NCG

/-- The transposition `(01)` on the standard three-dimensional `S₄` carrier. -/
def k4StandardTransposition : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 1]

/-- The four-cycle `(0123)` on the standard carrier in the basis
`e₀-e₃, e₁-e₃, e₂-e₃`. -/
def k4StandardFourCycle : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-1, -1, -1; 1, 0, 0; 0, 1, 0]

/-- The standard `S₄` triplet is irreducible in the concrete sense needed
here: the joint commutant of the two generators consists only of scalars. -/
theorem k4StandardTriplet_jointCommutant_scalar
    (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hs : A * k4StandardTransposition = k4StandardTransposition * A)
    (ht : A * k4StandardFourCycle = k4StandardFourCycle * A) :
    ∃ α : ℂ, A = α • 1 := by
  have hs00 := congrArg (fun M => M 0 0) hs
  have hs01 := congrArg (fun M => M 0 1) hs
  have hs02 := congrArg (fun M => M 0 2) hs
  have hs20 := congrArg (fun M => M 2 0) hs
  have ht00 := congrArg (fun M => M 0 0) ht
  have ht01 := congrArg (fun M => M 0 1) ht
  have ht02 := congrArg (fun M => M 0 2) ht
  have ht10 := congrArg (fun M => M 1 0) ht
  simp [k4StandardTransposition, k4StandardFourCycle,
    Matrix.mul_apply, Fin.sum_univ_three] at hs00 hs01 hs02 hs20 ht00 ht01 ht02 ht10
  have h11 : A 1 1 = A 0 0 := hs01.symm
  rw [h11] at ht10
  have h10 : A 1 0 = 0 := by linear_combination -ht10
  have h01 : A 0 1 = 0 := by simpa [h10] using hs00
  rw [h01, h10] at ht00
  have h20 : A 2 0 = 0 := by linear_combination ht00
  have h21 : A 2 1 = 0 := by simpa [h20] using hs20
  rw [h01, h11, h21] at ht01
  have h02 : A 0 2 = 0 := by linear_combination ht01
  have h12 : A 1 2 = 0 := by simpa [h02] using hs02.symm
  rw [h02, h12] at ht02
  have h22 : A 2 2 = A 0 0 := by linear_combination ht02
  refine ⟨A 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h01, h02, h10, h11, h12, h20, h21, h22]

/-- There is no intertwiner from the standard triplet to its sign twist.  On
odd generators this is exactly simultaneous anticommutation. -/
theorem k4StandardToSignTwist_intertwiner_zero
    (B : Matrix (Fin 3) (Fin 3) ℂ)
    (hs : B * k4StandardTransposition =
      -(k4StandardTransposition * B))
    (ht : B * k4StandardFourCycle = -(k4StandardFourCycle * B)) :
    B = 0 := by
  have hs00 := congrArg (fun M => M 0 0) hs
  have hs01 := congrArg (fun M => M 0 1) hs
  have hs02 := congrArg (fun M => M 0 2) hs
  have hs20 := congrArg (fun M => M 2 0) hs
  have hs22 := congrArg (fun M => M 2 2) hs
  have ht00 := congrArg (fun M => M 0 0) ht
  have ht01 := congrArg (fun M => M 0 1) ht
  have ht02 := congrArg (fun M => M 0 2) ht
  have ht10 := congrArg (fun M => M 1 0) ht
  simp [k4StandardTransposition, k4StandardFourCycle,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at hs00 hs01 hs02 hs20 hs22 ht00 ht01 ht02 ht10
  have h11 : B 1 1 = -B 0 0 := by linear_combination hs01
  rw [h11] at ht10
  have h10 : B 1 0 = 0 := by linear_combination -ht10
  have h01 : B 0 1 = 0 := by simpa [h10] using hs00
  have h22two : B 2 2 * 2 = 0 := by linear_combination hs22
  have h22 : B 2 2 = 0 :=
    (mul_eq_zero.mp h22two).resolve_right (by norm_num)
  rw [hs02, h22] at ht02
  have h00 : B 0 0 = 0 := by linear_combination -ht02
  have h11zero : B 1 1 = 0 := by simpa [h00] using h11
  rw [h00, h01, h10] at ht00
  have h20 : B 2 0 = 0 := by linear_combination -ht00
  have h21 : B 2 1 = 0 := by simpa [h20] using hs20
  rw [h00, h01, h11zero, h21] at ht01
  have h02 : B 0 2 = 0 := by linear_combination ht01
  have h12 : B 1 2 = 0 := by simpa [h02] using hs02.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h00, h01, h02, h10, h11zero, h12, h20, h21, h22]

/-- Exact finite `S₄` Schur certificate on the cut/cycle decomposition.
Equivariance under the transposition and four-cycle forces two scalar diagonal
blocks and zero cross blocks. -/
theorem k4CutCycle_equivariantGram_blockScalar
    (A B C D : Matrix (Fin 3) (Fin 3) ℂ)
    (hAs : A * k4StandardTransposition = k4StandardTransposition * A)
    (hAt : A * k4StandardFourCycle = k4StandardFourCycle * A)
    (hDs : D * k4StandardTransposition = k4StandardTransposition * D)
    (hDt : D * k4StandardFourCycle = k4StandardFourCycle * D)
    (hBs : B * k4StandardTransposition = -(k4StandardTransposition * B))
    (hBt : B * k4StandardFourCycle = -(k4StandardFourCycle * B))
    (hCs : C * k4StandardTransposition = -(k4StandardTransposition * C))
    (hCt : C * k4StandardFourCycle = -(k4StandardFourCycle * C)) :
    ∃ α β : ℂ,
      A = α • 1 ∧ D = β • 1 ∧ B = 0 ∧ C = 0 := by
  obtain ⟨α, hA⟩ := k4StandardTriplet_jointCommutant_scalar A hAs hAt
  obtain ⟨β, hD⟩ := k4StandardTriplet_jointCommutant_scalar D hDs hDt
  exact ⟨α, β, hA, hD,
    k4StandardToSignTwist_intertwiner_zero B hBs hBt,
    k4StandardToSignTwist_intertwiner_zero C hCs hCt⟩

end NCG
