/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Singular polar-edge equivalence
  (`lem:SMST-polar-edge`, Gran-Tensor manuscript)

* `polar_edge_singular`: for an arbitrary rectangular,
  singular or rank-deficient incidence map `F = UP` with
  polar data `P = (F*F)^{1/2} ⪰ 0`, partial isometry `U`,
  support projection `p = U*U`, and a support pseudoinverse
  `P†` (`PP† = P†P = p`), the two incidence equations
  `R_H F = F R_E`, `R_E F* = F* R_H`
  are equivalent to the boxed transport triple
  `[R_E, P²] = 0`, `R_H U = U R_E`, `R_E U* = U* R_H`.
  No invertibility and no equality of source and target
  dimensions is required.

* On either branch the boxed support commutations hold:
  `[R_E, p] = 0`, `[R_H, q] = 0` with `q = UU*`, and
  `[R_H, UP²U*] = 0`.

The functional-calculus input `[R, P²] = 0 ⟹ [R, P] = 0`
is `NCG.commute_of_commute_sq`; the existence of the polar
data for an arbitrary matrix (singular-value decomposition,
with `p` the spectral support projection of `P²` — the last
property is carried here as the hypothesis `hsupp`) is the
manuscript's decomposition step. The positive-definite
branch is `NCG.polar_edge` / `NCG.polar_edge_of_posDef`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

set_option linter.unusedDecidableInType false

namespace NCG

/-- `lem:SMST-polar-edge` (singular branch). -/
theorem polar_edge_singular {E H : Type*} [Fintype E]
    [Fintype H] [DecidableEq E] [DecidableEq H]
    (F : Matrix H E ℂ) (U : Matrix H E ℂ)
    (P Pd : Matrix E E ℂ) (RE : Matrix E E ℂ)
    (RH : Matrix H H ℂ)
    (hP : P.PosSemidef) (hFUP : F = U * P)
    (hPP : P * P = Fᴴ * F)
    (hUp : U * (Uᴴ * U) = U)
    (hPd1 : P * Pd = Uᴴ * U) (hPd2 : Pd * P = Uᴴ * U)
    (hsupp : ∀ R : Matrix E E ℂ,
      R * (P * P) = (P * P) * R →
      R * (Uᴴ * U) = (Uᴴ * U) * R) :
    -- the boxed equivalence
    ((RH * F = F * RE ∧ RE * Fᴴ = Fᴴ * RH)
      ↔ (RE * (P * P) = (P * P) * RE
        ∧ RH * U = U * RE
        ∧ RE * Uᴴ = Uᴴ * RH))
    -- the boxed support commutations on either branch
    ∧ ((RE * (P * P) = (P * P) * RE ∧ RH * U = U * RE
          ∧ RE * Uᴴ = Uᴴ * RH) →
        (RE * (Uᴴ * U) = (Uᴴ * U) * RE
          ∧ RH * (U * Uᴴ) = (U * Uᴴ) * RH
          ∧ RH * (U * (P * P) * Uᴴ)
              = (U * (P * P) * Uᴴ) * RH)) := by
  have hPH : Pᴴ = P := hP.isHermitian
  have hpH : (Uᴴ * U)ᴴ = Uᴴ * U := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hpU : (Uᴴ * U) * Uᴴ = Uᴴ := by
    have h := congrArg conjTranspose hUp
    rw [Matrix.conjTranspose_mul, hpH] at h
    exact h
  have hFadj : Fᴴ = P * Uᴴ := by
    rw [hFUP, Matrix.conjTranspose_mul, hPH]
  constructor
  · constructor
    · rintro ⟨h1, h2⟩
      -- the source metric commutes with `P²`
      have hsq : RE * (P * P) = (P * P) * RE := by
        have hL : Fᴴ * (RH * F) = RE * (P * P) := by
          rw [← Matrix.mul_assoc, ← h2, Matrix.mul_assoc,
            hPP]
        have hR : Fᴴ * (RH * F) = (P * P) * RE := by
          rw [h1, ← Matrix.mul_assoc, hPP]
        rw [← hL, hR]
      -- hence with `P` itself and with the support
      have hcomP : RE * P = P * RE :=
        commute_of_commute_sq hP hsq
      have hcomp : RE * (Uᴴ * U) = (Uᴴ * U) * RE :=
        hsupp RE hsq
      refine ⟨hsq, ?_, ?_⟩
      · -- transport of the partial isometry
        have hUP : (RH * U) * P = (U * RE) * P := by
          calc (RH * U) * P = RH * (U * P) := by
                rw [Matrix.mul_assoc]
            _ = (U * P) * RE := by rw [← hFUP, h1]
            _ = U * (P * RE) := by rw [Matrix.mul_assoc]
            _ = (U * RE) * P := by
                rw [← hcomP, Matrix.mul_assoc]
        have h := congrArg (fun M => M * Pd) hUP
        simp only [Matrix.mul_assoc, hPd1] at h
        calc RH * U = RH * (U * (Uᴴ * U)) := by rw [hUp]
          _ = U * (RE * (Uᴴ * U)) := h
          _ = U * ((Uᴴ * U) * RE) := by rw [hcomp]
          _ = U * RE := by
              rw [← Matrix.mul_assoc, hUp]
      · -- transport of the adjoint
        have hPU : P * (RE * Uᴴ) = P * (Uᴴ * RH) := by
          calc P * (RE * Uᴴ) = (P * RE) * Uᴴ := by
                rw [Matrix.mul_assoc]
            _ = (RE * P) * Uᴴ := by rw [hcomP]
            _ = RE * Fᴴ := by
                rw [hFadj, Matrix.mul_assoc]
            _ = Fᴴ * RH := h2
            _ = P * (Uᴴ * RH) := by
                rw [hFadj, Matrix.mul_assoc]
        have h := congrArg (fun M => Pd * M) hPU
        simp only [← Matrix.mul_assoc, hPd2] at h
        calc RE * Uᴴ = RE * ((Uᴴ * U) * Uᴴ) := by
              rw [hpU]
          _ = (RE * (Uᴴ * U)) * Uᴴ := by
              simp only [Matrix.mul_assoc]
          _ = ((Uᴴ * U) * RE) * Uᴴ := by rw [hcomp]
          _ = (Uᴴ * U) * (Uᴴ * RH) := by
              simp only [← Matrix.mul_assoc]
              exact h
          _ = Uᴴ * RH := by
              rw [← Matrix.mul_assoc, hpU]
    · rintro ⟨hsq, hU1, hU2⟩
      have hcomP : RE * P = P * RE :=
        commute_of_commute_sq hP hsq
      constructor
      · calc RH * F = (RH * U) * P := by
              rw [hFUP, Matrix.mul_assoc]
          _ = (U * RE) * P := by rw [hU1]
          _ = U * (P * RE) := by
              rw [Matrix.mul_assoc, ← hcomP]
          _ = F * RE := by rw [hFUP, Matrix.mul_assoc]
      · calc RE * Fᴴ = (RE * P) * Uᴴ := by
              rw [hFadj, Matrix.mul_assoc]
          _ = P * (RE * Uᴴ) := by
              rw [hcomP, Matrix.mul_assoc]
          _ = Fᴴ * RH := by
              rw [hU2, hFadj, Matrix.mul_assoc]
  · rintro ⟨hsq, hU1, hU2⟩
    refine ⟨?_, ?_, ?_⟩
    · calc RE * (Uᴴ * U) = (RE * Uᴴ) * U := by
            rw [Matrix.mul_assoc]
        _ = Uᴴ * (RH * U) := by
            rw [hU2, Matrix.mul_assoc]
        _ = (Uᴴ * U) * RE := by
            rw [hU1, ← Matrix.mul_assoc]
    · calc RH * (U * Uᴴ) = (RH * U) * Uᴴ := by
            rw [Matrix.mul_assoc]
        _ = U * (RE * Uᴴ) := by
            rw [hU1, Matrix.mul_assoc]
        _ = (U * Uᴴ) * RH := by
            rw [hU2, ← Matrix.mul_assoc]
    · calc RH * (U * (P * P) * Uᴴ)
          = ((RH * U) * (P * P)) * Uᴴ := by
            simp only [Matrix.mul_assoc]
        _ = U * ((RE * (P * P)) * Uᴴ) := by
            rw [hU1]
            simp only [Matrix.mul_assoc]
        _ = U * ((P * P) * (RE * Uᴴ)) := by
            rw [hsq]
            simp only [Matrix.mul_assoc]
        _ = (U * (P * P) * Uᴴ) * RH := by
            rw [hU2]
            simp only [Matrix.mul_assoc]

end NCG
