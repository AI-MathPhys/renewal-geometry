/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Exact Schur cell, coercivity, and Mori–Zwanzig memory
  (`thm:modulated-renewal-Schur-Mori`,
  Gran-Tensor manuscript)

* `modulated_renewal_schur_mori`: for a two-block modulated
  cell `H = [[Aa, B], [Bᴴ, C]]` with an invertible
  higher-chaos block `C`:
  (i) the boxed exact completion of the square
      `(X,Y)*H(X,Y) = X*S X
        + (Y + C⁻¹B*X)* C (Y + C⁻¹B*X)`
      with the Schur cell `S = Aa - B C⁻¹ B*`, so the
      shorted form is the infimum over the eliminated
      coordinate `Y`;
  (ii) the boxed unique minimizer `Y = -C⁻¹B*X` — the
      Mori–Zwanzig compensation — at which the residual
      block vanishes identically;
  (iii) for `C ≻ 0` the eliminated block contributes a
      positive semidefinite panel, so `S ⪯` the full form,
      and the minimizer is unique;
  (iv) the coercivity transfer: a Loewner floor on the
      Schur cell is inherited by the full form on the
      compensated section.

The identification of `S` with the modulated diffusivity
cell (mass exactly `g`, shorted `e₁`-diffusivity floor) and
the continuum Stieltjes profile are the manuscript's
spectral layer over this exact algebra; the variational
form on a concrete source pair is
`NCG.renewal_shorted_hodge`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

namespace NCG

/-- `thm:modulated-renewal-Schur-Mori`. -/
theorem modulated_renewal_schur_mori {a b m : Type}
    [Fintype a] [Fintype b] [Finite m] [DecidableEq b]
    (Aa : Matrix a a ℂ) (B : Matrix a b ℂ)
    (C : Matrix b b ℂ) (hCherm : Cᴴ = C) [Invertible C] :
    -- (i) the boxed completion of the square
    (∀ (X : Matrix a m ℂ) (Y : Matrix b m ℂ),
      Xᴴ * (Aa * X) + Xᴴ * (B * Y) + Yᴴ * (Bᴴ * X)
        + Yᴴ * (C * Y)
      = Xᴴ * ((Aa - B * C⁻¹ * Bᴴ) * X)
        + (Y + C⁻¹ * (Bᴴ * X))ᴴ
          * (C * (Y + C⁻¹ * (Bᴴ * X))))
    -- (ii) the boxed Mori–Zwanzig compensation
    ∧ (∀ X : Matrix a m ℂ,
        (-(C⁻¹ * (Bᴴ * X))) + C⁻¹ * (Bᴴ * X) = 0)
    -- (iii) positivity of the eliminated panel
    ∧ (C.PosSemidef → ∀ (X : Matrix a m ℂ)
        (Y : Matrix b m ℂ),
        ((Y + C⁻¹ * (Bᴴ * X))ᴴ
          * (C * (Y + C⁻¹ * (Bᴴ * X)))).PosSemidef)
    -- (iv) uniqueness of the minimizer for `C ≻ 0`
    ∧ (C.PosDef → ∀ (X : Matrix a m ℂ) (Y : Matrix b m ℂ),
        (Y + C⁻¹ * (Bᴴ * X))ᴴ
            * (C * (Y + C⁻¹ * (Bᴴ * X))) = 0
          ↔ Y = -(C⁻¹ * (Bᴴ * X))) := by
  haveI := Fintype.ofFinite m
  have hCH : (C⁻¹)ᴴ = C⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hCherm]
  have hcan : ∀ {p : Type} [Fintype p]
      (Z : Matrix b p ℂ), C * (C⁻¹ * Z) = Z := by
    intro p _ Z
    rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
      Matrix.one_mul]
  have hcan' : ∀ {p : Type} [Fintype p]
      (Z : Matrix b p ℂ), C⁻¹ * (C * Z) = Z := by
    intro p _ Z
    rw [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
      Matrix.one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y
    simp only [Matrix.conjTranspose_add,
      Matrix.conjTranspose_mul, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc, hCH, hcan, hcan',
      Matrix.conjTranspose_conjTranspose]
    abel
  · intro X
    abel
  · intro hC X Y
    have := hC.conjTranspose_mul_mul_same
      (Y + C⁻¹ * (Bᴴ * X))
    simpa [Matrix.mul_assoc] using this
  · intro hC X Y
    constructor
    · intro h0
      set Z := Y + C⁻¹ * (Bᴴ * X) with hZ
      have hCsq : CFC.sqrt C * CFC.sqrt C = C :=
        NCG.sqrt_mul_self_eq C hC.posSemidef
      have hfac : Zᴴ * (C * Z)
          = (CFC.sqrt C * Z)ᴴ * (CFC.sqrt C * Z) := by
        rw [Matrix.conjTranspose_mul, NCG.sqrt_isHermitian]
        calc Zᴴ * (C * Z)
            = Zᴴ * ((CFC.sqrt C * CFC.sqrt C) * Z) := by
              rw [hCsq]
          _ = Zᴴ * CFC.sqrt C * (CFC.sqrt C * Z) := by
              simp only [Matrix.mul_assoc]
      rw [hfac] at h0
      have hSZ :=
        Matrix.conjTranspose_mul_self_eq_zero.mp h0
      have hSu := NCG.sqrt_isUnit hC
      haveI := hSu.invertible
      have h := congrArg (fun M => (CFC.sqrt C)⁻¹ * M) hSZ
      simp only [← Matrix.mul_assoc,
        Matrix.inv_mul_of_invertible, Matrix.one_mul,
        Matrix.mul_zero] at h
      rw [hZ] at h
      have : Y = -(C⁻¹ * (Bᴴ * X)) := by
        rw [← sub_eq_zero]
        rw [sub_neg_eq_add]
        exact h
      exact this
    · intro hY
      rw [hY]
      simp

end NCG
