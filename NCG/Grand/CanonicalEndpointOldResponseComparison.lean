/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FrameTransport

/-!
# Canonical endpoint comparison with an older response

This file proves `prop:ar-old-response` without assuming that the endpoint
writer has identity Gram.  Its Moore--Penrose inverse is represented by the
four Penrose equations, which is the intrinsic convention used elsewhere in
the library.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- The row-support projection associated with an endpoint writer and its
Moore--Penrose inverse. -/
def endpointRowProjection {r t : Type*} [Fintype r] [Fintype t]
    (J : Matrix r t ℂ) (Jdag : Matrix t r ℂ) : Matrix t t ℂ :=
  Jdag * J

/-- The Penrose equations make `Jdag * J` the orthogonal projection onto the
writer's row support, and the writer is unchanged on that support. -/
theorem endpointRowProjection_orthogonal
    {r t : Type*} [Fintype r] [Fintype t]
    (J : Matrix r t ℂ) (Jdag : Matrix t r ℂ)
    (hJJJ : J * Jdag * J = J)
    (hJdJH : (Jdag * J)ᴴ = Jdag * J) :
    let P := endpointRowProjection J Jdag
    Pᴴ = P ∧ P * P = P ∧ J * P = J := by
  dsimp [endpointRowProjection]
  refine ⟨hJdJH, ?_, ?_⟩
  · calc
      (Jdag * J) * (Jdag * J) = Jdag * (J * Jdag * J) := by
        simp only [Matrix.mul_assoc]
      _ = Jdag * J := by rw [hJJJ]
  · simpa only [Matrix.mul_assoc] using hJJJ

/-- Exact Moore--Penrose split of an independently measured response.  The
innovation vanishes exactly when the response factors through the canonical
endpoint quotient. -/
theorem canonicalEndpoint_oldResponse_split
    {r t h : Type*} [Fintype r] [Fintype t] [Fintype h]
    [DecidableEq t]
    (J : Matrix r t ℂ) (Jdag : Matrix t r ℂ) (Cold : Matrix h t ℂ)
    (hJJJ : J * Jdag * J = J) :
    let P := endpointRowProjection J Jdag
    let Rold := Cold * Jdag
    let defect := Cold * ((1 : Matrix t t ℂ) - P)
    Cold = Rold * J + defect
      ∧ (defect = 0 ↔ Cold = Rold * J)
      ∧ (defect = 0 ↔ ∃ R : Matrix h r ℂ, Cold = R * J) := by
  dsimp [endpointRowProjection]
  have hsplit : Cold = (Cold * Jdag) * J +
      Cold * ((1 : Matrix t t ℂ) - Jdag * J) := by
    calc
      Cold = Cold * (1 : Matrix t t ℂ) := by rw [Matrix.mul_one]
      _ = Cold * (Jdag * J + (1 - Jdag * J)) := by
        congr 1
        noncomm_ring
      _ = (Cold * Jdag) * J + Cold * (1 - Jdag * J) := by
        rw [Matrix.mul_add]
        simp only [Matrix.mul_assoc]
  refine ⟨hsplit, ?_, ?_⟩
  · constructor
    · intro hdef
      simpa [hdef] using hsplit
    · intro hfac
      rw [hfac, Matrix.mul_sub, Matrix.mul_one]
      have hJP : J * (Jdag * J) = J := by
        simpa only [Matrix.mul_assoc] using hJJJ
      calc
        Cold * Jdag * J - Cold * Jdag * J * (Jdag * J) =
            (Cold * Jdag) * (J - J * (Jdag * J)) := by
              rw [Matrix.mul_sub]
              simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hJP, sub_self, Matrix.mul_zero]
  · constructor
    · intro hdef
      exact ⟨Cold * Jdag, (hsplit.trans (by simp [hdef]))⟩
    · rintro ⟨R, hfac⟩
      rw [hfac, Matrix.mul_sub, Matrix.mul_one]
      have hJP : J * (Jdag * J) = J := by
        simpa only [Matrix.mul_assoc] using hJJJ
      calc
        R * J - R * J * (Jdag * J) = R * (J - J * (Jdag * J)) := by
          rw [Matrix.mul_sub]
          simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hJP, sub_self, Matrix.mul_zero]

/-- Polar whitening of the factorized old response.  Positive definiteness of
the response Gram produces an isometric source map, and multiplication by the
positive square root reconstructs the old response router exactly. -/
theorem canonicalEndpoint_oldResponse_polarWhitening
    {r h : Type*} [Fintype r] [Fintype h] [DecidableEq r]
    (Rold : Matrix h r ℂ) (hGram : (Roldᴴ * Rold).PosDef) :
    let G := Roldᴴ * Rold
    let U := Rold * (CFC.sqrt G)⁻¹
    Uᴴ * U = 1 ∧ U * CFC.sqrt G = Rold := by
  dsimp only
  haveI := (sqrt_isUnit hGram).invertible
  have hiso :
      (Rold * (CFC.sqrt (Roldᴴ * Rold))⁻¹)ᴴ *
          (Rold * (CFC.sqrt (Roldᴴ * Rold))⁻¹) = 1 := by
    rw [Matrix.conjTranspose_mul, sqrt_inv_isHermitian]
    calc
      (CFC.sqrt (Roldᴴ * Rold))⁻¹ * Roldᴴ *
          (Rold * (CFC.sqrt (Roldᴴ * Rold))⁻¹) =
          (CFC.sqrt (Roldᴴ * Rold))⁻¹ * (Roldᴴ * Rold) *
            (CFC.sqrt (Roldᴴ * Rold))⁻¹ := by
            simp only [Matrix.mul_assoc]
      _ = (CFC.sqrt (Roldᴴ * Rold))⁻¹ *
          (CFC.sqrt (Roldᴴ * Rold) * CFC.sqrt (Roldᴴ * Rold)) *
            (CFC.sqrt (Roldᴴ * Rold))⁻¹ := by
            rw [sqrt_mul_self_eq _ hGram.posSemidef]
      _ = 1 := by
            rw [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
              Matrix.one_mul, Matrix.mul_inv_of_invertible]
  refine ⟨hiso, ?_⟩
  rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_one]

/-- Complete exact form of the optional old-response comparison: the support
projection, response/innovation split, quotient-factorization test, and polar
whitening certificate are all available from the same Penrose data. -/
theorem canonicalEndpoint_oldResponse_comparison
    {r t h : Type*} [Fintype r] [Fintype t] [Fintype h]
    [DecidableEq r] [DecidableEq t]
    (J : Matrix r t ℂ) (Jdag : Matrix t r ℂ) (Cold : Matrix h t ℂ)
    (hJJJ : J * Jdag * J = J)
    (hJdJH : (Jdag * J)ᴴ = Jdag * J)
    (hdefect : Cold * ((1 : Matrix t t ℂ) - Jdag * J) = 0)
    (hGram : ((Cold * Jdag)ᴴ * (Cold * Jdag)).PosDef) :
    let P := endpointRowProjection J Jdag
    let Rold := Cold * Jdag
    Pᴴ = P ∧ P * P = P ∧ J * P = J
      ∧ Cold = Rold * J
      ∧ ∃ U : Matrix h r ℂ,
          Uᴴ * U = 1 ∧ U * CFC.sqrt (Roldᴴ * Rold) = Rold := by
  dsimp [endpointRowProjection]
  obtain ⟨hPH, hP2, hJP⟩ :=
    endpointRowProjection_orthogonal J Jdag hJJJ hJdJH
  have hfac : Cold = (Cold * Jdag) * J :=
    (canonicalEndpoint_oldResponse_split J Jdag Cold hJJJ).2.1.mp hdefect
  obtain ⟨hU, hrec⟩ :=
    canonicalEndpoint_oldResponse_polarWhitening (Cold * Jdag) hGram
  exact ⟨hPH, hP2, hJP, hfac,
    ⟨Cold * Jdag * (CFC.sqrt ((Cold * Jdag)ᴴ * (Cold * Jdag)))⁻¹,
      hU, hrec⟩⟩

end NCG
