/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar
import NCG.Grand.TypedRecordScalarNeutralCommutant

/-!
# Typed singlet–adjoint Radon–Nikodym reduction
  (`thm:SM-typed-occurrence-RN`, Gran-Tensor manuscript)

* `typed_occurrence_RN`: the boxed positive-operator
  Radon–Nikodym effect — for a faithful typed metric
  `G ≻ 0` and a positive part `0 ⪯ G_Φ ⪯ G`, there is a
  **unique** effect `0 ⪯ K ⪯ I` with
  `G_Φ = √G · K · √G`, and then automatically
  `G - G_Φ = √G · (I - K) · √G` (the complement channel
  `G_Ω`).

Rendering disclosed: the `SU(4)`-covariant `1 ⊕ 15` block
form is Schur's lemma for the multiplicity-free conjugation
representation (the manuscript's representation-theoretic
step, tracked with the commutant records); the ten-parameter
nondemolition count is the commutant dimension bookkeeping of
the displayed record algebra. The sqrt-blocked analytic core
proved here is the effect existence, uniqueness, and the
two boxed factorizations.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

-- `CFC.sqrt` mentions the matrix CFC instance (which needs
-- `DecidableEq`) in every statement; the linter cannot see it.
set_option linter.unusedDecidableInType false

namespace NCG

/-- `thm:SM-typed-occurrence-RN` (Radon–Nikodym effect). -/
theorem typed_occurrence_RN {n : Type*} [Fintype n]
    [DecidableEq n] {G GΦ : Matrix n n ℂ} (hG : G.PosDef)
    (hΦ : GΦ.PosSemidef) (hle : (G - GΦ).PosSemidef) :
    ∃! K : Matrix n n ℂ,
      K.PosSemidef ∧ ((1 : Matrix n n ℂ) - K).PosSemidef
      ∧ GΦ = CFC.sqrt G * K * CFC.sqrt G
      ∧ G - GΦ = CFC.sqrt G
          * ((1 : Matrix n n ℂ) - K) * CFC.sqrt G := by
  haveI := (sqrt_isUnit hG).invertible
  have hs2 : CFC.sqrt G * CFC.sqrt G = G :=
    sqrt_mul_self_eq G hG.posSemidef
  have hsH : (CFC.sqrt G)ᴴ = CFC.sqrt G := sqrt_isHermitian G
  have hsiH : ((CFC.sqrt G)⁻¹)ᴴ = (CFC.sqrt G)⁻¹ :=
    sqrt_inv_isHermitian G
  -- the candidate effect
  set K : Matrix n n ℂ :=
    (CFC.sqrt G)⁻¹ * GΦ * (CFC.sqrt G)⁻¹ with hKdef
  -- sandwich cancellation: √G (√G⁻¹ M √G⁻¹) √G = M
  have hcan : ∀ M : Matrix n n ℂ,
      CFC.sqrt G * ((CFC.sqrt G)⁻¹ * M * (CFC.sqrt G)⁻¹)
        * CFC.sqrt G = M := by
    intro M
    calc CFC.sqrt G * ((CFC.sqrt G)⁻¹ * M * (CFC.sqrt G)⁻¹)
        * CFC.sqrt G
        = (CFC.sqrt G * (CFC.sqrt G)⁻¹) * M
            * ((CFC.sqrt G)⁻¹ * CFC.sqrt G) := by
          simp only [Matrix.mul_assoc]
      _ = M := by
          rw [Matrix.mul_inv_of_invertible,
            Matrix.inv_mul_of_invertible, Matrix.one_mul,
            Matrix.mul_one]
  -- the reverse sandwich: √G⁻¹ (√G M √G) √G⁻¹ = M
  have hcan' : ∀ M : Matrix n n ℂ,
      (CFC.sqrt G)⁻¹ * (CFC.sqrt G * M * CFC.sqrt G)
        * (CFC.sqrt G)⁻¹ = M := by
    intro M
    calc (CFC.sqrt G)⁻¹ * (CFC.sqrt G * M * CFC.sqrt G)
        * (CFC.sqrt G)⁻¹
        = ((CFC.sqrt G)⁻¹ * CFC.sqrt G) * M
            * (CFC.sqrt G * (CFC.sqrt G)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = M := by
          rw [Matrix.mul_inv_of_invertible,
            Matrix.inv_mul_of_invertible, Matrix.one_mul,
            Matrix.mul_one]
  -- 1 - K is the conjugated complement
  have hone : (1 : Matrix n n ℂ) - K
      = (CFC.sqrt G)⁻¹ * (G - GΦ) * (CFC.sqrt G)⁻¹ := by
    rw [hKdef, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    rw [show (CFC.sqrt G)⁻¹ * G * (CFC.sqrt G)⁻¹
        = (CFC.sqrt G)⁻¹ * (CFC.sqrt G * CFC.sqrt G)
          * (CFC.sqrt G)⁻¹ from by rw [hs2],
      ← Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
      Matrix.one_mul, Matrix.mul_inv_of_invertible]
  have hKpsd : K.PosSemidef := by
    have := hΦ.mul_mul_conjTranspose_same (CFC.sqrt G)⁻¹
    rwa [hsiH] at this
  have hKle : ((1 : Matrix n n ℂ) - K).PosSemidef := by
    rw [hone]
    have := hle.mul_mul_conjTranspose_same (CFC.sqrt G)⁻¹
    rwa [hsiH] at this
  refine ⟨K, ⟨hKpsd, hKle, (hcan GΦ).symm, ?_⟩, ?_⟩
  · rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      hs2, hcan GΦ]
  · rintro K' ⟨-, -, hK', -⟩
    have h := congrArg
      (fun M => (CFC.sqrt G)⁻¹ * M * (CFC.sqrt G)⁻¹) hK'
    rw [hcan' K'] at h
    rw [hKdef, h]

/-- Corrected typed Radon--Nikodym reduction on the concrete record carrier.
The unique effect is nondemolition exactly when it consists of six scalar
coordinates and one unrestricted neutral `2 × 2` block. -/
theorem typedOccurrenceRN_scalarNeutralRecord
    {G GΦ : Matrix (Fin 6 ⊕ Fin 2) (Fin 6 ⊕ Fin 2) ℂ}
    (hG : G.PosDef) (hΦ : GΦ.PosSemidef)
    (hle : (G - GΦ).PosSemidef) :
    ∃! K : Matrix (Fin 6 ⊕ Fin 2) (Fin 6 ⊕ Fin 2) ℂ,
      K.PosSemidef ∧ ((1 : Matrix (Fin 6 ⊕ Fin 2) (Fin 6 ⊕ Fin 2) ℂ) - K).PosSemidef ∧
      GΦ = CFC.sqrt G * K * CFC.sqrt G ∧
      G - GΦ = CFC.sqrt G * (1 - K) * CFC.sqrt G ∧
      ((∀ (a : Fin 6 → ℂ) (z : ℂ),
          TypedRecordScalarNeutralCommutant.scalarNeutralRecord a z * K =
            K * TypedRecordScalarNeutralCommutant.scalarNeutralRecord a z) ↔
        ∃ (k : Fin 6 → ℂ) (N : Matrix (Fin 2) (Fin 2) ℂ),
          K = Matrix.fromBlocks (Matrix.diagonal k) 0 0 N) := by
  obtain ⟨K, hK, huniq⟩ := typed_occurrence_RN hG hΦ hle
  refine ⟨K, ⟨hK.1, hK.2.1, hK.2.2.1, hK.2.2.2, ?_⟩, ?_⟩
  · exact TypedRecordScalarNeutralCommutant.mem_commutant_iff_scalarNeutralBlockForm K
  · intro K' hK'
    exact huniq K' ⟨hK'.1, hK'.2.1, hK'.2.2.1, hK'.2.2.2.1⟩

end NCG
