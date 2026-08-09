/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PolarEdgeSingular
import NCG.Upstream.PrimitiveWeight
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Exact EASY 80: construction of singular rectangular polar data

This completes `lem:SMST-polar-edge`. For an arbitrary rectangular complex
matrix, the positive factor, support pseudoinverse, support projection, and
partial isometry are constructed by the Hermitian functional calculus of
`FᴴF`. The resulting data discharge every hypothesis of the already-proved
singular polar-edge equivalence.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

set_option linter.unusedDecidableInType false
set_option maxHeartbeats 800000

private noncomputable def polarPinvSqrt (x : ℝ) : ℝ :=
  if x = 0 then 0 else (Real.sqrt x)⁻¹

private noncomputable def polarSupport (x : ℝ) : ℝ :=
  if x = 0 then 0 else 1

/-- Every rectangular complex matrix admits exactly the singular polar data
required by `polar_edge_singular`. -/
theorem exists_singular_polar_data {e h : ℕ}
    (F : Matrix (Fin h) (Fin e) ℂ) :
    ∃ (U : Matrix (Fin h) (Fin e) ℂ)
      (P Pd : Matrix (Fin e) (Fin e) ℂ),
      P.PosSemidef ∧ F = U * P ∧ P * P = Fᴴ * F ∧
      U * (Uᴴ * U) = U ∧
      P * Pd = Uᴴ * U ∧ Pd * P = Uᴴ * U ∧
      (∀ R : Matrix (Fin e) (Fin e) ℂ,
        R * (P * P) = (P * P) * R →
        R * (Uᴴ * U) = (Uᴴ * U) * R) := by
  let X : Matrix (Fin e) (Fin e) ℂ := Fᴴ * F
  have hX : X.PosSemidef := by
    exact Matrix.posSemidef_conjTranspose_mul_self F
  let hXH : X.IsHermitian := hX.isHermitian
  let P : Matrix (Fin e) (Fin e) ℂ := hXH.cfc Real.sqrt
  let Pd : Matrix (Fin e) (Fin e) ℂ := hXH.cfc polarPinvSqrt
  let p : Matrix (Fin e) (Fin e) ℂ := hXH.cfc polarSupport
  let U : Matrix (Fin h) (Fin e) ℂ := F * Pd
  have hP : P.PosSemidef := by
    dsimp only [P]
    exact Upstream.PrimitiveWeight.cfc_posSemidef hXH
      (fun i => Real.sqrt_nonneg _)
  have hP2 : P * P = X := by
    calc
      P * P = hXH.cfc (fun x => Real.sqrt x * Real.sqrt x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc id := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        exact Real.mul_self_sqrt (hX.eigenvalues_nonneg i)
      _ = X := Upstream.PrimitiveWeight.cfc_id' hXH
  have hPPd : P * Pd = p := by
    calc
      P * Pd = hXH.cfc
          (fun x => Real.sqrt x * polarPinvSqrt x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc polarSupport := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        have hnon := hX.eigenvalues_nonneg i
        by_cases hz : hXH.eigenvalues i = 0
        · simp [polarPinvSqrt, polarSupport, hz]
        · have hp : 0 < hXH.eigenvalues i := lt_of_le_of_ne hnon (Ne.symm hz)
          have hs : Real.sqrt (hXH.eigenvalues i) ≠ 0 :=
            (Real.sqrt_pos.2 hp).ne'
          simp [polarPinvSqrt, polarSupport, hz, hs]
      _ = p := rfl
  have hPdP : Pd * P = p := by
    calc
      Pd * P = hXH.cfc
          (fun x => polarPinvSqrt x * Real.sqrt x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc polarSupport := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        have hnon := hX.eigenvalues_nonneg i
        by_cases hz : hXH.eigenvalues i = 0
        · simp [polarPinvSqrt, polarSupport, hz]
        · have hp : 0 < hXH.eigenvalues i := lt_of_le_of_ne hnon (Ne.symm hz)
          have hs : Real.sqrt (hXH.eigenvalues i) ≠ 0 :=
            (Real.sqrt_pos.2 hp).ne'
          simp [polarPinvSqrt, polarSupport, hz, hs]
      _ = p := rfl
  have hp2 : p * p = p := by
    calc
      p * p = hXH.cfc (fun x => polarSupport x * polarSupport x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc polarSupport := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        simp [polarSupport]
      _ = p := rfl
  have hpH : pᴴ = p :=
    Upstream.PrimitiveWeight.cfc_isHermitian hXH polarSupport
  have hPdH : Pdᴴ = Pd :=
    Upstream.PrimitiveWeight.cfc_isHermitian hXH polarPinvSqrt
  have hXp : X * p = X := by
    calc
      X * p = hXH.cfc id * hXH.cfc polarSupport := by
        rw [Upstream.PrimitiveWeight.cfc_id' hXH]
      _ = hXH.cfc (fun x => x * polarSupport x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc id := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        by_cases hz : hXH.eigenvalues i = 0 <;>
          simp [polarSupport, hz]
      _ = X := Upstream.PrimitiveWeight.cfc_id' hXH
  have hpX : p * X = X := by
    have ht := congrArg conjTranspose hXp
    rw [Matrix.conjTranspose_mul, hpH, hXH] at ht
    exact ht
  have hFp : F * p = F := by
    let Y : Matrix (Fin h) (Fin e) ℂ := F * (1 - p)
    have hY2 : Yᴴ * Y = 0 := by
      calc
        Yᴴ * Y = (1 - p) * X * (1 - p) := by
          dsimp only [Y, X]
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
            Matrix.conjTranspose_one, hpH]
          simp only [Matrix.mul_assoc]
        _ = 0 := by
          rw [Matrix.sub_mul, Matrix.one_mul, hpX, Matrix.mul_sub,
            Matrix.mul_one]
          simp
    have hY : Y = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hY2
    dsimp only [Y] at hY
    rw [Matrix.mul_sub, Matrix.mul_one] at hY
    exact (sub_eq_zero.mp hY).symm
  have hPdp : Pd * p = Pd := by
    calc
      Pd * p = hXH.cfc
          (fun x => polarPinvSqrt x * polarSupport x) :=
        Upstream.PrimitiveWeight.cfc_mul hXH _ _
      _ = hXH.cfc polarPinvSqrt := by
        apply Upstream.PrimitiveWeight.cfc_congr hXH
        intro i
        by_cases hz : hXH.eigenvalues i = 0 <;>
          simp [polarPinvSqrt, polarSupport, hz]
      _ = Pd := rfl
  have hFUP : F = U * P := by
    dsimp only [U]
    rw [Matrix.mul_assoc, hPdP, hFp]
  have hUtU : Uᴴ * U = p := by
    calc
      Uᴴ * U = Pd * X * Pd := by
        dsimp only [U, X]
        rw [Matrix.conjTranspose_mul, hPdH]
        simp only [Matrix.mul_assoc]
      _ = Pd * (P * P) * Pd := by rw [hP2]
      Pd * (P * P) * Pd = (Pd * P) * (P * Pd) := by
        simp only [Matrix.mul_assoc]
      _ = p * p := by rw [hPdP, hPPd]
      _ = p := hp2
  have hUp : U * (Uᴴ * U) = U := by
    rw [hUtU]
    dsimp only [U]
    rw [Matrix.mul_assoc, hPdp]
  have hsupp : ∀ R : Matrix (Fin e) (Fin e) ℂ,
      R * (P * P) = (P * P) * R →
      R * (Uᴴ * U) = (Uᴴ * U) * R := by
    intro R hR
    have hc : Commute R X := by
      rw [← hP2]
      exact hR
    have hcfc := hc.symm.cfc_real polarSupport
    rw [hXH.cfc_eq] at hcfc
    rw [hUtU]
    exact hcfc.symm.eq
  exact ⟨U, P, Pd, hP, hFUP, by simpa [X] using hP2,
    hUp, by rw [hUtU, hPPd], by rw [hUtU, hPdP], hsupp⟩

/-- The singular polar-edge equivalence, with its polar factors constructed
from an arbitrary rectangular matrix rather than supplied as hypotheses. -/
theorem polar_edge_singular_arbitrary {e h : ℕ}
    (F : Matrix (Fin h) (Fin e) ℂ)
    (RE : Matrix (Fin e) (Fin e) ℂ)
    (RH : Matrix (Fin h) (Fin h) ℂ) :
    ∃ (U : Matrix (Fin h) (Fin e) ℂ)
      (P Pd : Matrix (Fin e) (Fin e) ℂ),
      P.PosSemidef ∧ F = U * P ∧ P * P = Fᴴ * F ∧
      U * (Uᴴ * U) = U ∧
      P * Pd = Uᴴ * U ∧ Pd * P = Uᴴ * U ∧
      (((RH * F = F * RE ∧ RE * Fᴴ = Fᴴ * RH) ↔
          (RE * (P * P) = (P * P) * RE ∧
            RH * U = U * RE ∧ RE * Uᴴ = Uᴴ * RH)) ∧
        ((RE * (P * P) = (P * P) * RE ∧
            RH * U = U * RE ∧ RE * Uᴴ = Uᴴ * RH) →
          (RE * (Uᴴ * U) = (Uᴴ * U) * RE ∧
            RH * (U * Uᴴ) = (U * Uᴴ) * RH ∧
            RH * (U * (P * P) * Uᴴ) =
              (U * (P * P) * Uᴴ) * RH))) := by
  rcases exists_singular_polar_data F with
    ⟨U, P, Pd, hP, hFUP, hP2, hUp, hPPd, hPdP, hsupp⟩
  refine ⟨U, P, Pd, hP, hFUP, hP2, hUp, hPPd, hPdP, ?_⟩
  exact polar_edge_singular F U P Pd RE RH hP hFUP hP2 hUp
    hPPd hPdP hsupp

end NCG
