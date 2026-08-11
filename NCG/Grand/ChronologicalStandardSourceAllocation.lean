/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.ExactSourceSchurResidual

/-!
# No-double-counting allocation of a chronological standard source

This module proves `thm:SMST-standard-source-allocation` after cancelling the
common `W₀` standard-representation tensor factor.  A readable source `S` has
coefficient Gram `G`; the one-column chronological source `C` has norm `a` and
cross row `ell = CᴴS`.  The residual

`R = G - a⁻¹ ellᴴ ell`

is identified with the Gram of the component of `S` orthogonal to `C`.
Consequently, the image under `S` of `ker R` is exactly
`range S ∩ range C`.  On a faithful coefficient quotient, restriction of
`ell` to `ker R` is injective into a one-dimensional space, proving
`dim ker R ≤ 1`.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- The chronological rank-one range projector. -/
noncomputable def chronologicalSourceProjection {h : ℕ}
    (C : Matrix (Fin h) (Fin 1) ℂ) (a : ℝ) :
    Matrix (Fin h) (Fin h) ℂ :=
  ((a : ℂ)⁻¹) • (C * Cᴴ)

/-- The coefficient residual after allocating the chronological source. -/
noncomputable def chronologicalStandardResidual {e : ℕ}
    (G : Matrix (Fin e) (Fin e) ℂ) (a : ℝ)
    (ell : Matrix (Fin 1) (Fin e) ℂ) :
    Matrix (Fin e) (Fin e) ℂ :=
  G - ((a : ℂ)⁻¹) • (ellᴴ * ell)

private theorem chronologicalSourceProjection_properties {h : ℕ}
    (C : Matrix (Fin h) (Fin 1) ℂ) (a : ℝ) (ha : 0 < a)
    (hC : Cᴴ * C = (a : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) :
    let P := chronologicalSourceProjection C a
    Pᴴ = P ∧ P * P = P ∧ P * C = C := by
  dsimp only [chronologicalSourceProjection]
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  constructor
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    simp [star_inv₀, Complex.star_def]
  constructor
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Cᴴ C Cᴴ, hC, Matrix.smul_mul,
      Matrix.one_mul, smul_smul]
    have hcoef : (((a : ℂ)⁻¹ * (a : ℂ)⁻¹) * (a : ℂ)) =
        (a : ℂ)⁻¹ := by field_simp
    rw [Matrix.mul_smul, smul_smul]
    rw [hcoef]
  · rw [Matrix.smul_mul, Matrix.mul_assoc, hC, Matrix.mul_smul,
      Matrix.mul_one, smul_smul]
    have hcoef : ((a : ℂ)⁻¹ * (a : ℂ)) = 1 := by field_simp
    rw [hcoef, one_smul]

/-- The displayed residual is the Gram of the orthogonal chronological
innovation. -/
theorem chronologicalStandardResidual_eq_orthogonalGram
    {h e : ℕ}
    (S : Matrix (Fin h) (Fin e) ℂ)
    (C : Matrix (Fin h) (Fin 1) ℂ)
    (G : Matrix (Fin e) (Fin e) ℂ)
    (ell : Matrix (Fin 1) (Fin e) ℂ)
    (a : ℝ) (ha : 0 < a)
    (hG : G = Sᴴ * S) (hell : ell = Cᴴ * S)
    (hC : Cᴴ * C = (a : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) :
    chronologicalStandardResidual G a ell =
      ((1 - chronologicalSourceProjection C a) * S)ᴴ
        * ((1 - chronologicalSourceProjection C a) * S) := by
  let P := chronologicalSourceProjection C a
  obtain ⟨hPH, hP2, -⟩ := chronologicalSourceProjection_properties C a ha hC
  have hQH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hP2]
    abel
  change chronologicalStandardResidual G a ell = ((1 - P) * S)ᴴ * ((1 - P) * S)
  rw [chronologicalStandardResidual, hG, hell]
  simp only [Matrix.conjTranspose_mul]
  rw [hQH]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (1 - P) (1 - P) S, hQ2]
  dsimp only [P, chronologicalSourceProjection]
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
    Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- Pointwise form of
`Ran S(ker R) = Ran S ∩ Ran C`. -/
theorem chronologicalStandardSource_rangeIntersection
    {h e : ℕ}
    (S : Matrix (Fin h) (Fin e) ℂ)
    (C : Matrix (Fin h) (Fin 1) ℂ)
    (G : Matrix (Fin e) (Fin e) ℂ)
    (ell : Matrix (Fin 1) (Fin e) ℂ)
    (a : ℝ) (ha : 0 < a)
    (hG : G = Sᴴ * S) (hell : ell = Cᴴ * S)
    (hC : Cᴴ * C = (a : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ))
    (y : Fin h → ℂ) :
    (∃ x : Fin e → ℂ,
        (chronologicalStandardResidual G a ell).mulVec x = 0 ∧
        y = S.mulVec x)
      ↔ (∃ x : Fin e → ℂ, y = S.mulVec x)
        ∧ (∃ z : Fin 1 → ℂ, y = C.mulVec z) := by
  let P := chronologicalSourceProjection C a
  let Q := 1 - P
  let A := Q * S
  have hR := chronologicalStandardResidual_eq_orthogonalGram
    S C G ell a ha hG hell hC
  obtain ⟨hPH, hP2, hPC⟩ := chronologicalSourceProjection_properties C a ha hC
  change Pᴴ = P at hPH
  change P * C = C at hPC
  have hQC : Q * C = 0 := by
    dsimp only [Q]
    rw [Matrix.sub_mul, Matrix.one_mul, hPC, sub_self]
  constructor
  · rintro ⟨x, hxR, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    have hxA : A.mulVec x = 0 := by
      apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero A x).mp
      rw [← hR]
      exact hxR
    have hQS : Q.mulVec (S.mulVec x) = 0 := by
      simpa [A, Matrix.mulVec_mulVec] using hxA
    have hPS : P.mulVec (S.mulVec x) = S.mulVec x := by
      dsimp only [Q] at hQS
      rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hQS
      exact (sub_eq_zero.mp hQS).symm
    let z : Fin 1 → ℂ := ((a : ℂ)⁻¹) • (Cᴴ).mulVec (S.mulVec x)
    refine ⟨z, ?_⟩
    change S.mulVec x = C.mulVec z
    rw [← hPS]
    simp only [P, chronologicalSourceProjection, z,
      Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    have hmat : (((a : ℂ)⁻¹ • (C * Cᴴ)) * S) =
        (a : ℂ)⁻¹ • (C * (Cᴴ * S)) := by
      rw [Matrix.smul_mul, Matrix.mul_assoc]
    rw [hmat, Matrix.smul_mulVec]
  · rintro ⟨⟨x, hyS⟩, ⟨z, hyC⟩⟩
    refine ⟨x, ?_, hyS⟩
    rw [hR]
    change (Aᴴ * A).mulVec x = 0
    apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero A x).mpr
    have hAy : A.mulVec x = Q.mulVec (S.mulVec x) := by
      simp [A, Matrix.mulVec_mulVec]
    rw [hAy, ← hyS, hyC]
    simpa [Matrix.mulVec_mulVec] using congrArg (fun M => M.mulVec z) hQC
    
/-- On a faithful coefficient quotient the chronological residual kernel has
dimension at most one. -/
theorem chronologicalStandardResidual_kernel_finrank_le_one
    {e : ℕ}
    (G : Matrix (Fin e) (Fin e) ℂ) (hG : G.PosDef)
    (ell : Matrix (Fin 1) (Fin e) ℂ)
    (a : ℝ) (ha : 0 < a) :
    Module.finrank ℂ
        (LinearMap.ker (chronologicalStandardResidual G a ell).mulVecLin)
      ≤ 1 := by
  let R := chronologicalStandardResidual G a ell
  let K := LinearMap.ker R.mulVecLin
  let phi : K →ₗ[ℂ] (Fin 1 → ℂ) :=
    ell.mulVecLin.comp K.subtype
  have hphi : Function.Injective phi := by
    intro x y hxy
    apply Subtype.ext
    have hellxy : ell.mulVec (x.1 - y.1) = 0 := by
      have hellEq : ell.mulVec x.1 = ell.mulVec y.1 := hxy
      rw [Matrix.mulVec_sub, hellEq, sub_self]
    have hRxy : R.mulVec (x.1 - y.1) = 0 := by
      have hx : R.mulVec x.1 = 0 := x.2
      have hy : R.mulVec y.1 = 0 := y.2
      rw [Matrix.mulVec_sub, hx, hy, sub_self]
    have hGxy : G.mulVec (x.1 - y.1) = 0 := by
      dsimp only [R, chronologicalStandardResidual] at hRxy
      rw [Matrix.sub_mulVec] at hRxy
      have hinner : (ellᴴ * ell).mulVec (x.1 - y.1) = 0 := by
        rw [← Matrix.mulVec_mulVec, hellxy, Matrix.mulVec_zero]
      have hzeroTerm :
          (((a : ℂ)⁻¹ • (ellᴴ * ell)).mulVec (x.1 - y.1)) = 0 := by
        rw [Matrix.smul_mulVec, hinner, smul_zero]
      rw [hzeroTerm, sub_zero] at hRxy
      exact hRxy
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hG.isUnit)
    rw [← sub_eq_zero, ← Matrix.mulVec_sub]
    exact hGxy
  have hle := LinearMap.finrank_le_finrank_of_injective hphi
  simpa [Module.finrank_pi_fintype] using hle

/-- `thm:SMST-standard-source-allocation`: assembled range allocation and
faithful-quotient kernel bound. -/
theorem chronologicalStandardSource_noDoubleCounting
    {h e : ℕ}
    (S : Matrix (Fin h) (Fin e) ℂ)
    (C : Matrix (Fin h) (Fin 1) ℂ)
    (G : Matrix (Fin e) (Fin e) ℂ) (hGpos : G.PosDef)
    (ell : Matrix (Fin 1) (Fin e) ℂ)
    (a : ℝ) (ha : 0 < a)
    (hG : G = Sᴴ * S) (hell : ell = Cᴴ * S)
    (hC : Cᴴ * C = (a : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) :
    (∀ y : Fin h → ℂ,
      (∃ x : Fin e → ℂ,
          (chronologicalStandardResidual G a ell).mulVec x = 0 ∧
          y = S.mulVec x)
        ↔ (∃ x : Fin e → ℂ, y = S.mulVec x)
          ∧ (∃ z : Fin 1 → ℂ, y = C.mulVec z))
      ∧ Module.finrank ℂ
          (LinearMap.ker (chronologicalStandardResidual G a ell).mulVecLin)
        ≤ 1 := by
  exact ⟨fun y => chronologicalStandardSource_rangeIntersection
      S C G ell a ha hG hell hC y,
    chronologicalStandardResidual_kernel_finrank_le_one G hGpos ell a ha⟩

end NCG
