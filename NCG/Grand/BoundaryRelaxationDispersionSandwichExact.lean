/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTBoundaryShort
import NCG.Grand.MatrixLoewnerInverseBoundsExact

/-!
# Exact boundary-relaxation dispersion sandwich

This completes `cor:GT-boundary-relaxation-dispersion`: positivity of the matrix
discrepancy, its exact square-root vanishing criterion, the two-sided BC.7 Loewner
sandwich derived from `C ≥ γI` and `‖D_T‖ ≤ d`, and persistence of every interior floor.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NCG
namespace BoundaryRelaxationDispersionSandwich

/-- A positive-definite middle factor detects every nonzero rectangular matrix. -/
theorem conj_posDef_eq_zero_iff
    {b m : Type*} [Fintype b] [Fintype m] [DecidableEq b]
    {W : Matrix b b ℂ} (hW : W.PosDef) (A : Matrix b m ℂ) :
    Aᴴ * W * A = 0 ↔ A = 0 := by
  let R := CFC.sqrt W
  have hRH : Rᴴ = R := sqrt_isHermitian W
  have hRR : R * R = W := sqrt_mul_self_eq W hW.posSemidef
  have hfactor : Aᴴ * W * A = (R * A)ᴴ * (R * A) := by
    rw [Matrix.conjTranspose_mul, hRH, ← hRR]
    simp only [Matrix.mul_assoc]
  constructor
  · intro hzero
    have hRA : R * A = 0 := by
      apply Matrix.conjTranspose_mul_self_eq_zero.mp
      rwa [← hfactor]
    have hRu : IsUnit R := sqrt_isUnit hW
    haveI := hRu.invertible
    calc
      A = R⁻¹ * (R * A) := by
        rw [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.one_mul]
      _ = 0 := by rw [hRA, Matrix.mul_zero]
  · rintro rfl
    simp

/-- Under the scalar floor on `C` and the operator norm cap on `D_T`, the boundary kernel
`K = D_T C⁻¹ D_Tᴴ` satisfies `0 ≤ K ≤ (d²/γ)I`. -/
theorem boundaryKernel_bounds
    {T b : Type*} [Fintype T] [Fintype b] [DecidableEq T] [DecidableEq b]
    (C : Matrix T T ℂ) (DT : Matrix b T ℂ) {γ d₀ : ℝ}
    (hγ : 0 < γ) (hC : γ • (1 : Matrix T T ℂ) ≤ C)
    (hD : ‖DT‖ ≤ d₀) :
    (0 : Matrix b b ℂ) ≤ DT * C⁻¹ * DTᴴ ∧
      DT * C⁻¹ * DTᴴ ≤ (d₀ ^ 2 / γ : ℝ) • (1 : Matrix b b ℂ) := by
  have hCpd : C.PosDef := MatrixLoewnerInverseBounds.posDef_of_smul_one_le hγ hC
  have hCinvPos : (C⁻¹).PosSemidef := hCpd.inv.posSemidef
  have hKpos : (DT * C⁻¹ * DTᴴ).PosSemidef :=
    hCinvPos.mul_mul_conjTranspose_same DT
  have hCinvUpper : C⁻¹ ≤ γ⁻¹ • (1 : Matrix T T ℂ) :=
    MatrixLoewnerInverseBounds.inv_le_smul_one_of_smul_one_le hγ hC
  have hfirst := MatrixLoewnerInverseBounds.conj_le_conj' hCinvUpper DT
  have hcap : DT * DTᴴ ≤ (d₀ ^ 2 : ℝ) • (1 : Matrix b b ℂ) :=
    MatrixLoewnerInverseBounds.mul_conjTranspose_le_smul_one hD
  have hγinv : (0 : ℝ) ≤ γ⁻¹ := (inv_pos.mpr hγ).le
  have hscaledPos := (Matrix.le_iff.mp hcap).smul (a := γ⁻¹) hγinv
  have hscaled : γ⁻¹ • (DT * DTᴴ) ≤
      γ⁻¹ • ((d₀ ^ 2 : ℝ) • (1 : Matrix b b ℂ)) :=
    by
      rw [Matrix.le_iff]
      simpa [smul_sub] using hscaledPos
  have hfirst' : DT * C⁻¹ * DTᴴ ≤ γ⁻¹ • (DT * DTᴴ) := by
    simpa [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] using hfirst
  refine ⟨Matrix.le_iff.mpr (by simpa using hKpos), hfirst'.trans ?_⟩
  calc
    γ⁻¹ • (DT * DTᴴ)
        ≤ γ⁻¹ • ((d₀ ^ 2 : ℝ) • (1 : Matrix b b ℂ)) := hscaled
    _ = (d₀ ^ 2 / γ : ℝ) • (1 : Matrix b b ℂ) := by
      rw [smul_smul]
      congr 1
      field_simp

set_option maxHeartbeats 2000000 in
/-- Complete BC.6--BC.7 theorem.  The larger elaboration budget is needed for
normalizing the nested matrix-order and square-root expressions in this single
assembled certificate. -/
theorem boundary_relaxation_dispersion_full
    {T b m : Type*} [Fintype T] [Fintype b] [Fintype m]
    [DecidableEq T] [DecidableEq b] [DecidableEq m]
    (C : Matrix T T ℂ) (DT : Matrix b T ℂ)
    (S : Matrix m m ℂ) (E : Matrix b m ℂ)
    {γ d₀ g : ℝ} (hγ : 0 < γ)
    (hC : γ • (1 : Matrix T T ℂ) ≤ C) (hD : ‖DT‖ ≤ d₀)
    (hS : g • (1 : Matrix m m ℂ) ≤ S) :
    let K := DT * C⁻¹ * DTᴴ
    let W := ((1 : Matrix b b ℂ) + K)⁻¹
    let Gshort := S + Eᴴ * W * E
    let Gnaive := S + Eᴴ * E
    (Gnaive - Gshort).PosSemidef ∧
      (Gnaive - Gshort = 0 ↔ CFC.sqrt K * E = 0) ∧
      S + ((1 + d₀ ^ 2 / γ)⁻¹ : ℝ) • (Eᴴ * E) ≤ Gshort ∧
      Gshort ≤ S + Eᴴ * E ∧
      g • (1 : Matrix m m ℂ) ≤ Gshort := by
  dsimp only
  let K := DT * C⁻¹ * DTᴴ
  have hKbounds := boundaryKernel_bounds C DT hγ hC hD
  have hKpos : K.PosSemidef := by
    simpa [K] using Matrix.le_iff.mp hKbounds.1
  have hMlower : (1 : Matrix b b ℂ) ≤ 1 + K := by
    simpa using add_le_add_left hKbounds.1 (1 : Matrix b b ℂ)
  have hMlowerR : (1 : ℝ) • (1 : Matrix b b ℂ) ≤ 1 + K := by
    simpa [Complex.real_smul] using hMlower
  have hαpos : 0 < 1 + d₀ ^ 2 / γ := by
    have hd0 : 0 ≤ d₀ := (norm_nonneg DT).trans hD
    positivity
  have hMupper : (1 : Matrix b b ℂ) + K ≤
      (1 + d₀ ^ 2 / γ : ℝ) • (1 : Matrix b b ℂ) := by
    calc
      (1 : Matrix b b ℂ) + K
          ≤ 1 + (d₀ ^ 2 / γ : ℝ) • (1 : Matrix b b ℂ) :=
            by
              simpa [K, add_comm] using
                add_le_add_left hKbounds.2 (1 : Matrix b b ℂ)
      _ = (1 + d₀ ^ 2 / γ : ℝ) • (1 : Matrix b b ℂ) := by
        ext i j
        by_cases hij : i = j <;> simp [hij]
  have hMpd : ((1 : Matrix b b ℂ) + K).PosDef :=
    MatrixLoewnerInverseBounds.posDef_of_smul_one_le
      (by norm_num : (0 : ℝ) < 1) hMlowerR
  let W := ((1 : Matrix b b ℂ) + K)⁻¹
  have hWupper : W ≤ (1 : Matrix b b ℂ) := by
    simpa [W] using
      (MatrixLoewnerInverseBounds.inv_le_smul_one_of_smul_one_le
        (M := (1 : Matrix b b ℂ) + K) (γ := 1) (by norm_num) hMlowerR)
  have hWlower : ((1 + d₀ ^ 2 / γ)⁻¹ : ℝ) • (1 : Matrix b b ℂ) ≤ W := by
    simpa [W] using MatrixLoewnerInverseBounds.smul_one_le_inv_of_le_smul_one
      hαpos hMpd hMupper
  have hWpd : W.PosDef := by
    simpa [W] using hMpd.inv
  have hupperCong := MatrixLoewnerInverseBounds.conj_le_conj hWupper E
  have hlowerCong := MatrixLoewnerInverseBounds.conj_le_conj hWlower E
  have hupper : Eᴴ * W * E ≤ Eᴴ * E := by
    simpa [Matrix.mul_one] using hupperCong
  have hlower : ((1 + d₀ ^ 2 / γ)⁻¹ : ℝ) • (Eᴴ * E) ≤ Eᴴ * W * E := by
    simpa [Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul] using hlowerCong
  have hdispEq : Eᴴ * E - Eᴴ * W * E = Eᴴ * (K * (W * E)) := by
    haveI := hMpd.isUnit.invertible
    have hW1 : ((1 : Matrix b b ℂ) + K) * W = 1 := by
      simpa [W] using Matrix.mul_inv_of_invertible ((1 : Matrix b b ℂ) + K)
    have hres : (1 : Matrix b b ℂ) - W = K * W := by
      have h := hW1
      rw [Matrix.add_mul, Matrix.one_mul] at h
      rw [← h]
      abel
    calc
      Eᴴ * E - Eᴴ * W * E = Eᴴ * (((1 : Matrix b b ℂ) - W) * E) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
      _ = Eᴴ * (K * (W * E)) := by rw [hres, Matrix.mul_assoc]
  have hsqrtK : (CFC.sqrt K).IsHermitian := sqrt_isHermitian K
  have hsqrtSq : CFC.sqrt K * CFC.sqrt K = K := sqrt_mul_self_eq K hKpos
  haveI := hMpd.isUnit.invertible
  have hcommKM : CFC.sqrt K * ((1 : Matrix b b ℂ) + K) =
      ((1 : Matrix b b ℂ) + K) * CFC.sqrt K := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
    congr 1
    calc
      CFC.sqrt K * K =
          CFC.sqrt K * (CFC.sqrt K * CFC.sqrt K) := by
            exact congrArg (fun Z => CFC.sqrt K * Z) hsqrtSq.symm
      _ = (CFC.sqrt K * CFC.sqrt K) * CFC.sqrt K := by
            simp only [Matrix.mul_assoc]
      _ = K * CFC.sqrt K := by
            exact congrArg (fun Z => Z * CFC.sqrt K) hsqrtSq
  have hcommKW : CFC.sqrt K * W = W * CFC.sqrt K := by
    exact MatrixLoewnerInverseBounds.commute_nonsing_inv hcommKM
  have hgram : Eᴴ * (K * (W * E)) =
      (CFC.sqrt K * E)ᴴ * W * (CFC.sqrt K * E) := by
    calc
      Eᴴ * (K * (W * E)) =
          Eᴴ * ((CFC.sqrt K * CFC.sqrt K) * (W * E)) := by
            exact congrArg (fun Z => Eᴴ * (Z * (W * E))) hsqrtSq.symm
      _ = Eᴴ * (CFC.sqrt K *
          ((CFC.sqrt K * W) * E)) := by simp only [Matrix.mul_assoc]
      _ = Eᴴ * (CFC.sqrt K *
          ((W * CFC.sqrt K) * E)) := by rw [hcommKW]
      _ = Eᴴ * CFC.sqrt K * W * (CFC.sqrt K * E) := by
            simp only [Matrix.mul_assoc]
      _ = (CFC.sqrt K * E)ᴴ * W * (CFC.sqrt K * E) := by
            rw [Matrix.conjTranspose_mul, hsqrtK.eq]
  have hdisp : (Eᴴ * E - Eᴴ * W * E).PosSemidef := by
    rw [hdispEq, hgram]
    exact hWpd.posSemidef.conjTranspose_mul_mul_same (CFC.sqrt K * E)
  have hzero : Eᴴ * E - Eᴴ * W * E = 0 ↔ CFC.sqrt K * E = 0 := by
    rw [hdispEq, hgram]
    exact conj_posDef_eq_zero_iff hWpd (CFC.sqrt K * E)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change ((S + Eᴴ * E) - (S + Eᴴ * W * E)).PosSemidef
    have heq : (S + Eᴴ * E) - (S + Eᴴ * W * E) =
        Eᴴ * E - Eᴴ * W * E := by abel
    rw [heq]
    exact hdisp
  · change ((S + Eᴴ * E) - (S + Eᴴ * W * E) = 0 ↔
      CFC.sqrt K * E = 0)
    have heq : (S + Eᴴ * E) - (S + Eᴴ * W * E) =
        Eᴴ * E - Eᴴ * W * E := by abel
    rw [heq]
    exact hzero
  · change S + ((1 + d₀ ^ 2 / γ)⁻¹ : ℝ) • (Eᴴ * E) ≤ S + Eᴴ * W * E
    simpa [add_comm] using add_le_add_left hlower S
  · change S + Eᴴ * W * E ≤ S + Eᴴ * E
    simpa [add_comm] using add_le_add_left hupper S
  · change g • (1 : Matrix m m ℂ) ≤ S + Eᴴ * W * E
    have hEW : (0 : Matrix m m ℂ) ≤ Eᴴ * W * E :=
      Matrix.le_iff.mpr (by
        simpa using hWpd.posSemidef.conjTranspose_mul_mul_same E)
    exact hS.trans (by
      simpa [add_comm] using add_le_add_left hEW S)

end BoundaryRelaxationDispersionSandwich
end NCG
