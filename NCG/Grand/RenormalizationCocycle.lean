/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Finite metric congruence and cocycle obstruction
  (`thm:renormalization-cocycle`, Gran-Tensor manuscript)

* `renormalization_cocycle`:
  (i) the boxed solution form: for `B ≻ 0`, `A ⪰ 0`, and any
      isometry-modulus `U` (`UᴴU = 1`), the arrow
      `Z = B^{-1/2}·U·A^{1/2}` satisfies the metric
      congruence `ZᴴBZ = A`;
  (ii) rank necessity: any solution forces
      `rank A ≤ rank B`;
  (iii) the kernel freedom: adding `N` with `BN = 0` leaves
      the congruence unchanged (`Ran N ⊆ Ker B`);
  (iv) the boxed diamond obstruction:
      `𝔻 = DᴴG_ℓD ⪰ 0` for `D = Z_{ℓn}Z_{nm} - Z_{ℓm}`, and
      for `G_ℓ ≻ 0` the faithful arrows form a strict cocycle
      exactly when every diamond Gram vanishes
      (`𝔻 = 0 ↔ D = 0`).

The full Stiefel classification of the solution set on
singular supports is the manuscript's polar-decomposition
bookkeeping over these clauses.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

set_option linter.unusedDecidableInType false

namespace NCG

/-- `thm:renormalization-cocycle`. -/
theorem renormalization_cocycle {n m : Type*} [Fintype n]
    [Fintype m] [DecidableEq n] [DecidableEq m]
    (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (hA : A.PosSemidef) (hB : B.PosDef) :
    -- (i) the boxed solution form solves the congruence
    (∀ U : Matrix m n ℂ, Uᴴ * U = 1 →
      ((CFC.sqrt B)⁻¹ * U * CFC.sqrt A)ᴴ * B
        * ((CFC.sqrt B)⁻¹ * U * CFC.sqrt A) = A)
    -- (ii) rank necessity
    ∧ (∀ Z : Matrix m n ℂ, Zᴴ * B * Z = A →
        A.rank ≤ B.rank)
    -- (iii) kernel freedom
    ∧ (∀ (Z N : Matrix m n ℂ), B * N = 0 →
        (Z + N)ᴴ * B * (Z + N) = Zᴴ * B * Z)
    -- (iv) the diamond obstruction
    ∧ (∀ (G D : Matrix m m ℂ), G.PosSemidef →
        (Dᴴ * G * D).PosSemidef)
    ∧ (∀ (G D : Matrix m m ℂ), G.PosDef →
        (Dᴴ * G * D = 0 ↔ D = 0)) := by
  have hBs := sqrt_isUnit hB
  haveI := hBs.invertible
  have hBH : (CFC.sqrt B)ᴴ = CFC.sqrt B := sqrt_isHermitian B
  have hBinvH : ((CFC.sqrt B)⁻¹)ᴴ = (CFC.sqrt B)⁻¹ :=
    sqrt_inv_isHermitian B
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro U hU
    have hAs : CFC.sqrt A * CFC.sqrt A = A :=
      sqrt_mul_self_eq A hA
    set S := CFC.sqrt B with hSdef
    have hBs2 : S * S = B := sqrt_mul_self_eq B hB.posSemidef
    have hkey : S⁻¹ * (B * S⁻¹) = 1 := by
      rw [← hBs2]
      calc S⁻¹ * (S * S * S⁻¹)
          = S⁻¹ * (S * (S * S⁻¹)) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [Matrix.mul_inv_of_invertible,
              Matrix.mul_one, Matrix.inv_mul_of_invertible]
    calc (S⁻¹ * U * CFC.sqrt A)ᴴ * B
          * (S⁻¹ * U * CFC.sqrt A)
        = (CFC.sqrt A)ᴴ * Uᴴ * ((S⁻¹)ᴴ
            * (B * (S⁻¹ * (U * CFC.sqrt A)))) := by
          simp only [Matrix.conjTranspose_mul,
            Matrix.mul_assoc]
      _ = (CFC.sqrt A)ᴴ * Uᴴ * (U * CFC.sqrt A) := by
          rw [hBinvH, ← Matrix.mul_assoc B,
            ← Matrix.mul_assoc S⁻¹, hkey, Matrix.one_mul]
      _ = A := by
          rw [sqrt_isHermitian A, ← Matrix.mul_assoc,
            Matrix.mul_assoc (CFC.sqrt A), hU,
            Matrix.mul_one, hAs]
  · intro Z hZ
    rw [← hZ]
    calc (Zᴴ * B * Z).rank ≤ (B * Z).rank := by
          rw [Matrix.mul_assoc]
          exact Matrix.rank_mul_le_right _ _
      _ ≤ B.rank := Matrix.rank_mul_le_left _ _
  · intro Z N hN
    have hNB : Nᴴ * B = 0 := by
      have h := congrArg conjTranspose hN
      rwa [Matrix.conjTranspose_mul, hB.posSemidef.1,
        Matrix.conjTranspose_zero] at h
    have hNBX : ∀ X : Matrix m n ℂ,
        Nᴴ * (B * X) = 0 := fun X => by
      rw [← Matrix.mul_assoc, hNB, Matrix.zero_mul]
    simp only [Matrix.conjTranspose_add, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_assoc, hN, hNBX,
      Matrix.mul_zero, add_zero]
  · intro G D hG
    exact hG.conjTranspose_mul_mul_same D
  · intro G D hG
    have hfac : Dᴴ * G * D
        = (CFC.sqrt G * D)ᴴ * (CFC.sqrt G * D) := by
      rw [Matrix.conjTranspose_mul, sqrt_isHermitian]
      calc Dᴴ * G * D
          = Dᴴ * ((CFC.sqrt G * CFC.sqrt G) * D) := by
            rw [sqrt_mul_self_eq G hG.posSemidef,
              Matrix.mul_assoc]
        _ = Dᴴ * CFC.sqrt G * (CFC.sqrt G * D) := by
            simp only [Matrix.mul_assoc]
    constructor
    · intro h0
      rw [hfac] at h0
      have hSD := Matrix.conjTranspose_mul_self_eq_zero.mp h0
      have hGs := sqrt_isUnit hG
      haveI := hGs.invertible
      have h := congrArg
        (fun X => (CFC.sqrt G)⁻¹ * X) hSD
      simpa [← Matrix.mul_assoc,
        Matrix.inv_mul_of_invertible] using h
    · intro h0
      rw [h0, Matrix.mul_zero]

end NCG
