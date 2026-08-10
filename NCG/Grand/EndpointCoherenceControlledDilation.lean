/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.EndpointDefect
import NCG.Grand.JointSourceRangeUnitary

/-!
# Controlled dilation and minimal carrier of endpoint coherence

This module completes the multiplicative-domain, minimal-carrier, and
Gram-uniqueness clauses of `thm:endpoint-coherence-defect`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- Multiplicative-domain extraction for a fixed sharp population: if an
isometry pulls an output projection back to an input projection, then it
intertwines those projections. -/
theorem isometry_fixedProjection_intertwines {h k : Type*}
    [Fintype h] [Fintype k] [DecidableEq h]
    (V : Matrix k h ℂ) (P : Matrix k k ℂ) (Q : Matrix h h ℂ)
    (hV : Vᴴ * V = 1) (hPH : Pᴴ = P) (hP2 : P * P = P)
    (hQH : Qᴴ = Q) (hQ2 : Q * Q = Q)
    (hfix : Vᴴ * P * V = Q) : P * V = V * Q := by
  let A := P * V - V * Q
  have hAA : Aᴴ * A = 0 := by
    have hPV : Vᴴ * (P * V) = Q := by
      simpa only [← Matrix.mul_assoc] using hfix
    have hVV : Vᴴ * (V * Q) = Q := by
      rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
    have hPPV : Vᴴ * (P * (P * V)) = Q := by
      rw [← Matrix.mul_assoc P P V, hP2, hPV]
    have hPVQ : Vᴴ * (P * (V * Q)) = Q := by
      rw [← Matrix.mul_assoc P V Q, ← Matrix.mul_assoc, hPV, hQ2]
    calc
      Aᴴ * A = Vᴴ * (P * (P * V)) - Vᴴ * (P * (V * Q))
          - Q * (Vᴴ * (P * V)) + Q * (Vᴴ * (V * Q)) := by
        dsimp [A]
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_mul, hPH, hQH]
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
        abel
      _ = 0 := by rw [hPPV, hPVQ, hPV, hVV, hQ2]; abel
  exact sub_eq_zero.mp (Matrix.conjTranspose_mul_self_eq_zero.mp hAA)

/-- Fixing the endpoint sign observable fixes both spectral projections and
therefore forces both endpoint blocks to intertwine separately. -/
theorem isometry_fixedBinaryObservable_controlled {h k : Type*}
    [Fintype h] [Fintype k] [DecidableEq h] [DecidableEq k]
    (V : Matrix k h ℂ)
    (Pout : Matrix k k ℂ) (Pin : Matrix h h ℂ)
    (hV : Vᴴ * V = 1) (hPH : Poutᴴ = Pout)
    (hP2 : Pout * Pout = Pout) (hQH : Pinᴴ = Pin)
    (hQ2 : Pin * Pin = Pin) (hfix : Vᴴ * Pout * V = Pin) :
    Pout * V = V * Pin
      ∧ ((1 : Matrix k k ℂ) - Pout) * V
        = V * ((1 : Matrix h h ℂ) - Pin) := by
  have h0 := isometry_fixedProjection_intertwines V Pout Pin hV hPH hP2
    hQH hQ2 hfix
  constructor
  · exact h0
  · rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, h0]

/-- The defect square root has the same rank as the defect itself.  Hence the
extra summand `Ran D¹ᐟ²` in the canonical joint carrier has dimension
`rank D`. -/
theorem endpointDefect_sqrt_range_dimension {h : Type*} [Fintype h]
    [DecidableEq h] (D : Matrix h h ℂ) (hD : D.PosSemidef) :
    Module.finrank ℂ (LinearMap.range (CFC.sqrt D).mulVecLin) = D.rank := by
  change (CFC.sqrt D).rank = D.rank
  calc
    (CFC.sqrt D).rank = ((CFC.sqrt D)ᴴ * CFC.sqrt D).rank :=
      (Matrix.rank_conjTranspose_mul_self _).symm
    _ = (CFC.sqrt D * CFC.sqrt D).rank := by rw [sqrt_isHermitian]
    _ = D.rank := by rw [sqrt_mul_self_eq D hD]

/-- Any other minimal pair of endpoint sheets with the same complete Gram is
related to the canonical joint carrier by the unique source-fixing isometry. -/
theorem endpointJointCarrier_unique
    {h h' e : Type*} [Fintype h] [Fintype h'] [Fintype e]
    (S : Matrix h e ℂ) (T : Matrix h' e ℂ)
    (hGram : Sᴴ * S = Tᴴ * T) :
    ∃! U : LinearMap.range S.mulVecLin ≃ₗ[ℂ]
      LinearMap.range T.mulVecLin,
      (∀ u : e → ℂ,
        U (S.mulVecLin.rangeRestrict u) = T.mulVecLin.rangeRestrict u)
      ∧ (∀ x y : LinearMap.range S.mulVecLin,
        star (x : h → ℂ) ⬝ᵥ (y : h → ℂ)
          = star (U x : h' → ℂ) ⬝ᵥ (U y : h' → ℂ)) :=
  joint_source_unique_range_unitary S T hGram

theorem crossGram_inner {h k : Type*} [Fintype h] [Fintype k]
    (A B : Matrix k h ℂ) (x y : h → ℂ) :
    star (A *ᵥ x) ⬝ᵥ (B *ᵥ y)
      = star x ⬝ᵥ ((Aᴴ * B) *ᵥ y) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec]

/-- Zero overlap is exactly complete dephasing of the two endpoint sheets. -/
theorem endpointSheets_completelyDephased_iff {h k : Type*}
    [Fintype h] [Fintype k] [DecidableEq h]
    (V₀ V₁ : Matrix k h ℂ) :
    V₀ᴴ * V₁ = 0 ↔ ∀ x y, star (V₀ *ᵥ x) ⬝ᵥ (V₁ *ᵥ y) = 0 := by
  constructor
  · intro h x y
    rw [crossGram_inner, h, Matrix.zero_mulVec, dotProduct_zero]
  · intro h
    let M := V₀ᴴ * V₁
    have hzero : ∀ y, M *ᵥ y = 0 := by
      intro y
      have hy := h (M *ᵥ y) y
      rw [crossGram_inner] at hy
      exact dotProduct_star_self_eq_zero.mp hy
    change M = 0
    ext i j
    have hij := congrFun (hzero (Pi.single j 1)) i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hij
    rw [Finset.sum_eq_single j] at hij
    · simpa [Pi.single_apply] using hij
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · simp

end NCG
