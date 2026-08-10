/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.PredictiveRN
import Mathlib.Analysis.Matrix.Order

/-!
# Finite Choi Radon--Nikodym factorization

This file proves the finite matrix theorem underlying the completely positive
Radon--Nikodym envelope.  If `W` has full row rank, every positive matrix
dominated by its Gram `Wᴴ * W` is uniquely of the form `Wᴴ * F * W` for a
positive contraction `F`.  The proof constructs the derivative with the
canonical right inverse of `W`; no Radon--Nikodym theorem is assumed.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

section FullRowRankGram

variable {E J : Type*} [Fintype E] [Fintype J]
  [DecidableEq E] [DecidableEq J]

/-- The canonical right inverse of a full-row-rank matrix. -/
noncomputable def fullRowRankRightInverse (W : Matrix E J ℂ) :
    Matrix J E ℂ :=
  Wᴴ * (W * Wᴴ)⁻¹

/-- Surjectivity of `W` makes its canonical right inverse exact. -/
theorem mul_fullRowRankRightInverse
    (W : Matrix E J ℂ) (hW : Function.Surjective W.mulVec) :
    W * fullRowRankRightInverse W = 1 := by
  classical
  have hPD : (W * Wᴴ).PosDef :=
    ((hodge_cycle_observability W).2.1).mp hW
  have hdet : IsUnit (W * Wᴴ).det :=
    isUnit_iff_ne_zero.mpr hPD.det_pos.ne'
  rw [fullRowRankRightInverse]
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet]

/-- A vector killed by `W` is killed by every positive matrix dominated by
`WᴴW`.  This is the kernel step in the finite Douglas argument. -/
theorem dominatedGram_mulVec_eq_zero
    (W : Matrix E J ℂ) {C : Matrix J J ℂ}
    (hC : C.PosSemidef) (hdom : (Wᴴ * W - C).PosSemidef)
    {z : J → ℂ} (hz : W *ᵥ z = 0) :
    C *ᵥ z = 0 := by
  have hgram : star z ⬝ᵥ ((Wᴴ * W) *ᵥ z) = 0 := by
    rw [← Matrix.mulVec_mulVec z Wᴴ W, hz, Matrix.mulVec_zero,
      dotProduct_zero]
  have hCnonneg : 0 ≤ star z ⬝ᵥ (C *ᵥ z) :=
    hC.dotProduct_mulVec_nonneg z
  have hdiff : 0 ≤ star z ⬝ᵥ ((Wᴴ * W - C) *ᵥ z) :=
    hdom.dotProduct_mulVec_nonneg z
  have hCle : star z ⬝ᵥ (C *ᵥ z) ≤ 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, hgram, zero_sub] at hdiff
    exact neg_nonneg.mp hdiff
  have hquad : star z ⬝ᵥ (C *ᵥ z) = 0 :=
    le_antisymm hCle hCnonneg
  exact (hC.dotProduct_mulVec_zero_iff z).mp hquad

/-- The canonical support projection associated with a full-row-rank matrix. -/
noncomputable def fullRowRankSupport (W : Matrix E J ℂ) : Matrix J J ℂ :=
  fullRowRankRightInverse W * W

theorem fullRowRankSupport_isHermitian
    (W : Matrix E J ℂ) (hW : Function.Surjective W.mulVec) :
    (fullRowRankSupport W).IsHermitian := by
  classical
  have hPD : (W * Wᴴ).PosDef :=
    ((hodge_cycle_observability W).2.1).mp hW
  have hdet : IsUnit (W * Wᴴ).det :=
    isUnit_iff_ne_zero.mpr hPD.det_pos.ne'
  have hInv : ((W * Wᴴ)⁻¹)ᴴ = (W * Wᴴ)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  rw [Matrix.IsHermitian, fullRowRankSupport, fullRowRankRightInverse,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hInv]
  rw [Matrix.mul_assoc]

/-- A dominated Choi matrix is supported on the row space of `W`. -/
theorem dominatedGram_support
    (W : Matrix E J ℂ) (hW : Function.Surjective W.mulVec)
    {C : Matrix J J ℂ} (hC : C.PosSemidef)
    (hdom : (Wᴴ * W - C).PosSemidef) :
    fullRowRankSupport W * C * fullRowRankSupport W = C := by
  classical
  let P := fullRowRankSupport W
  have hWP : W * (1 - P) = 0 := by
    dsimp only [P]
    rw [fullRowRankSupport, Matrix.mul_sub, Matrix.mul_one,
      ← Matrix.mul_assoc, mul_fullRowRankRightInverse W hW,
      Matrix.one_mul, sub_self]
  have hright : C * (1 - P) = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro z
    simp only [Matrix.zero_mulVec]
    rw [← Matrix.mulVec_mulVec z C (1 - P)]
    apply dominatedGram_mulVec_eq_zero W hC hdom
    rw [Matrix.mulVec_mulVec, hWP, Matrix.zero_mulVec]
  have hPstar : Pᴴ = P := fullRowRankSupport_isHermitian W hW
  have hleft : (1 - P) * C = 0 := by
    have h := congrArg Matrix.conjTranspose hright
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hPstar, hC.isHermitian.eq,
      Matrix.conjTranspose_zero] at h
    exact h
  have hCP : C * P = C := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hright
    exact hright.symm
  have hPC : P * C = C := by
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hleft
    exact hleft.symm
  change P * C * P = C
  rw [hPC, hCP]

/-- Finite Choi Radon--Nikodym theorem: a positive matrix in the Gram order
interval has a unique positive-contraction derivative. -/
theorem dominatedGram_radonNikodym
    (W : Matrix E J ℂ) (hW : Function.Surjective W.mulVec)
    (C : Matrix J J ℂ) (hC : C.PosSemidef)
    (hdom : (Wᴴ * W - C).PosSemidef) :
    ∃! F : Matrix E E ℂ,
      F.PosSemidef ∧ ((1 : Matrix E E ℂ) - F).PosSemidef ∧
        Wᴴ * F * W = C := by
  classical
  let R := fullRowRankRightInverse W
  let F : Matrix E E ℂ := Rᴴ * C * R
  have hWR : W * R = 1 := mul_fullRowRankRightInverse W hW
  have hF : F.PosSemidef := hC.conjTranspose_mul_mul_same R
  have hIFeq : (1 : Matrix E E ℂ) - F =
      Rᴴ * (Wᴴ * W - C) * R := by
    have hone : Rᴴ * (Wᴴ * W) * R = 1 := by
      calc
        Rᴴ * (Wᴴ * W) * R = (W * R)ᴴ * (W * R) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hWR, Matrix.conjTranspose_one, Matrix.one_mul]
    change (1 : Matrix E E ℂ) - (Rᴴ * C * R) =
      Rᴴ * (Wᴴ * W - C) * R
    rw [Matrix.mul_sub, Matrix.sub_mul, hone]
  have hIF : ((1 : Matrix E E ℂ) - F).PosSemidef := by
    rw [hIFeq]
    exact hdom.conjTranspose_mul_mul_same R
  have hrepr : Wᴴ * F * W = C := by
    have hsupp := dominatedGram_support W hW hC hdom
    change (R * W) * C * (R * W) = C at hsupp
    have hsupportHerm := fullRowRankSupport_isHermitian W hW
    change (R * W)ᴴ = R * W at hsupportHerm
    change Wᴴ * (Rᴴ * C * R) * W = C
    calc
      Wᴴ * (Rᴴ * C * R) * W = (R * W)ᴴ * C * (R * W) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = (R * W) * C * (R * W) := by rw [hsupportHerm]
      _ = C := hsupp
  refine ⟨F, ⟨hF, hIF, hrepr⟩, ?_⟩
  intro G hG
  have hRG : Rᴴ * (Wᴴ * G * W) * R = G := by
    calc
      Rᴴ * (Wᴴ * G * W) * R = (W * R)ᴴ * G * (W * R) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = G := by rw [hWR, Matrix.conjTranspose_one,
        Matrix.one_mul, Matrix.mul_one]
  have hRF : Rᴴ * (Wᴴ * F * W) * R = F := by
    calc
      Rᴴ * (Wᴴ * F * W) * R = (W * R)ᴴ * F * (W * R) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = F := by rw [hWR, Matrix.conjTranspose_one,
        Matrix.one_mul, Matrix.mul_one]
  calc
    G = Rᴴ * (Wᴴ * G * W) * R := hRG.symm
    _ = Rᴴ * C * R := by rw [hG.2.2]
    _ = Rᴴ * (Wᴴ * F * W) * R := by rw [hrepr]
    _ = F := hRF

/-- Full row rank makes the Gram-coordinate map `F ↦ WᴴFW` injective. -/
theorem fullRowRank_gramCoordinate_injective
    (W : Matrix E J ℂ) (hW : Function.Surjective W.mulVec) :
    Function.Injective (fun F : Matrix E E ℂ => Wᴴ * F * W) := by
  classical
  let R := fullRowRankRightInverse W
  have hWR : W * R = 1 := mul_fullRowRankRightInverse W hW
  intro F G hFG
  change Wᴴ * F * W = Wᴴ * G * W at hFG
  have hrecover : ∀ T : Matrix E E ℂ,
      Rᴴ * (Wᴴ * T * W) * R = T := by
    intro T
    calc
      Rᴴ * (Wᴴ * T * W) * R = (W * R)ᴴ * T * (W * R) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = T := by rw [hWR, Matrix.conjTranspose_one,
        Matrix.one_mul, Matrix.mul_one]
  rw [← hrecover F, ← hrecover G, hFG]

/-- The Gram-coordinate map is an order embedding for the positive-semidefinite
difference order. -/
theorem fullRowRank_gramCoordinate_order_iff
    (W : Matrix E J ℂ) (hW : Function.Surjective W.mulVec)
    (F G : Matrix E E ℂ) :
    (G - F).PosSemidef ↔
      (Wᴴ * G * W - Wᴴ * F * W).PosSemidef := by
  classical
  constructor
  · intro h
    have hc := h.conjTranspose_mul_mul_same W
    simpa [Matrix.mul_sub, Matrix.sub_mul] using hc
  · intro h
    let R := fullRowRankRightInverse W
    have hWR : W * R = 1 := mul_fullRowRankRightInverse W hW
    have hc := h.conjTranspose_mul_mul_same R
    have hrecoverG : Rᴴ * (Wᴴ * G * W) * R = G := by
      calc
        Rᴴ * (Wᴴ * G * W) * R = (W * R)ᴴ * G * (W * R) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
        _ = G := by rw [hWR, Matrix.conjTranspose_one,
          Matrix.one_mul, Matrix.mul_one]
    have hrecoverF : Rᴴ * (Wᴴ * F * W) * R = F := by
      calc
        Rᴴ * (Wᴴ * F * W) * R = (W * R)ᴴ * F * (W * R) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
        _ = F := by rw [hWR, Matrix.conjTranspose_one,
          Matrix.one_mul, Matrix.mul_one]
    have hre : Rᴴ *
        (Wᴴ * G * W - Wᴴ * F * W) * R = G - F := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hrecoverG, hrecoverF]
    rwa [hre] at hc

end FullRowRankGram

end NCG
