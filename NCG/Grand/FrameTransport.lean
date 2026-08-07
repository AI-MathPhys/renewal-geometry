/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Actual transport derives finite connection, curvature, and
  Cartan translation
  (`thm:SMST-frame-transport`, Gran-Tensor manuscript)

* `smst_frame_transport`:
  (0) whitening — the normalized frame `Ê = E·(√(EᴴE))⁻¹` is an
      isometry for a faithful frame Gram;
  (1) the boxed insertion decomposition
      `ÊₓᴴTᴴTÊₓ = AᴴA + 𝕍` with `A = Ê_yᴴTÊₓ` and the strain
      `𝕍 = ÊₓᴴTᴴ(I−Ê_yÊ_yᴴ)TÊₓ ⪰ 0`, plus the exact closure
      criterion `𝕍 = 0 ⟺ (I−Ê_yÊ_yᴴ)TÊₓ = 0`;
  (2) polar connection — an invertible link `A` splits as
      `A = U·P` with `U` unitary (the finite frame connection)
      and `P ≻ 0` hermitian (the strain);
  (3) coframe closure — `(I−Ê_yÊ_yᴴ)d = 0` forces
      `d = Ê_y·ξ` with `ξ = Ê_yᴴd`;
  (4) affine link composition — the boxed
      `SO(3)⋉ℝ³`-type product law
      `[[U,ξ],[0,1]]·[[U',ξ'],[0,1]] = [[UU', Uξ'+ξ],[0,1]]`.

Rendering disclosed: loop holonomy is ordered multiplication of
the proved links; the principal-logarithm curvature and the
real/orientation (`SO(3)`) branch are the manuscript's
functional-calculus and reality tests on the proved unitary
factor; the Cartan/torsion reading of the accumulated
translation is clause (4) iterated around a face.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

-- `CFC.sqrt` mentions the matrix CFC instance (which needs
-- `DecidableEq`) in every statement; the linter cannot see it.
set_option linter.unusedDecidableInType false

namespace NCG

/-- `thm:SMST-frame-transport`. -/
theorem smst_frame_transport :
    -- (0) whitening isometry
    (∀ {h k : Type} [Fintype h] [Fintype k] [DecidableEq k]
      (E : Matrix h k ℂ), (Eᴴ * E).PosDef →
      (E * (CFC.sqrt (Eᴴ * E))⁻¹)ᴴ
          * (E * (CFC.sqrt (Eᴴ * E))⁻¹) = 1)
    -- (1) insertion decomposition, positivity, closure
    ∧ (∀ {h kx ky : Type} [Fintype h] [Fintype kx]
        [Fintype ky] [DecidableEq h] [DecidableEq ky]
        (Wx : Matrix h kx ℂ) (Wy : Matrix h ky ℂ)
        (T : Matrix h h ℂ), Wyᴴ * Wy = 1 →
        (Wxᴴ * Tᴴ * T * Wx
            = (Wyᴴ * T * Wx)ᴴ * (Wyᴴ * T * Wx)
              + Wxᴴ * Tᴴ * ((1 : Matrix h h ℂ) - Wy * Wyᴴ)
                * T * Wx)
        ∧ (Wxᴴ * Tᴴ * ((1 : Matrix h h ℂ) - Wy * Wyᴴ)
            * T * Wx).PosSemidef
        ∧ (Wxᴴ * Tᴴ * ((1 : Matrix h h ℂ) - Wy * Wyᴴ)
              * T * Wx = 0
            ↔ ((1 : Matrix h h ℂ) - Wy * Wyᴴ) * T * Wx = 0))
    -- (2) polar connection of an invertible link
    ∧ (∀ {k : Type} [Fintype k] [DecidableEq k]
        (A : Matrix k k ℂ), IsUnit A →
        ∃ U P : Matrix k k ℂ, U * Uᴴ = 1 ∧ Uᴴ * U = 1
          ∧ P.PosDef ∧ Pᴴ = P ∧ A = U * P)
    -- (3) coframe closure
    ∧ (∀ {h ky : Type} [Fintype h] [Fintype ky]
        [DecidableEq h] (Wy : Matrix h ky ℂ) (d : h → ℂ),
        ((1 : Matrix h h ℂ) - Wy * Wyᴴ) *ᵥ d = 0 →
        d = Wy *ᵥ (Wyᴴ *ᵥ d))
    -- (4) affine link composition
    ∧ (∀ {k : Type} [Fintype k] [DecidableEq k]
        (U U' : Matrix k k ℂ) (ξ ξ' : Matrix k Unit ℂ),
        Matrix.fromBlocks U ξ 0 (1 : Matrix Unit Unit ℂ)
            * Matrix.fromBlocks U' ξ' 0 1
          = Matrix.fromBlocks (U * U') (U * ξ' + ξ) 0 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- whitening
    intro h k _ _ _ E hq
    haveI := (sqrt_isUnit hq).invertible
    rw [Matrix.conjTranspose_mul, sqrt_inv_isHermitian]
    calc (CFC.sqrt (Eᴴ * E))⁻¹ * Eᴴ
        * (E * (CFC.sqrt (Eᴴ * E))⁻¹)
        = (CFC.sqrt (Eᴴ * E))⁻¹ * (Eᴴ * E)
          * (CFC.sqrt (Eᴴ * E))⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (CFC.sqrt (Eᴴ * E))⁻¹
          * (CFC.sqrt (Eᴴ * E) * CFC.sqrt (Eᴴ * E))
          * (CFC.sqrt (Eᴴ * E))⁻¹ := by
          rw [sqrt_mul_self_eq _ hq.posSemidef]
      _ = 1 := by
          rw [← Matrix.mul_assoc,
            Matrix.inv_mul_of_invertible, Matrix.one_mul,
            Matrix.mul_inv_of_invertible]
  · -- insertion decomposition
    intro h kx ky _ _ _ _ _ Wx Wy T hWy
    have hQH : ((1 : Matrix h h ℂ) - Wy * Wyᴴ)ᴴ
        = (1 : Matrix h h ℂ) - Wy * Wyᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
        Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    have hWW : Wy * Wyᴴ * (Wy * Wyᴴ) = Wy * Wyᴴ := by
      rw [Matrix.mul_assoc Wy Wyᴴ (Wy * Wyᴴ),
        ← Matrix.mul_assoc Wyᴴ Wy Wyᴴ, hWy, Matrix.one_mul]
    have hQ2 : ((1 : Matrix h h ℂ) - Wy * Wyᴴ)
        * ((1 : Matrix h h ℂ) - Wy * Wyᴴ)
        = (1 : Matrix h h ℂ) - Wy * Wyᴴ := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
        Matrix.one_mul, hWW, sub_self, sub_zero]
    have hgram : Wxᴴ * Tᴴ
          * ((1 : Matrix h h ℂ) - Wy * Wyᴴ) * T * Wx
        = (((1 : Matrix h h ℂ) - Wy * Wyᴴ) * T * Wx)ᴴ
            * (((1 : Matrix h h ℂ) - Wy * Wyᴴ) * T * Wx) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        hQH]
      rw [show Wxᴴ * (Tᴴ * ((1 : Matrix h h ℂ) - Wy * Wyᴴ))
          * (((1 : Matrix h h ℂ) - Wy * Wyᴴ) * T * Wx)
          = Wxᴴ * Tᴴ
            * (((1 : Matrix h h ℂ) - Wy * Wyᴴ)
              * ((1 : Matrix h h ℂ) - Wy * Wyᴴ)) * T
            * Wx from by
        simp only [Matrix.mul_assoc]]
      rw [hQ2]
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
        Matrix.sub_mul]
      rw [show (Wyᴴ * T * Wx)ᴴ * (Wyᴴ * T * Wx)
          = Wxᴴ * Tᴴ * (Wy * Wyᴴ) * T * Wx from by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose]
        simp only [Matrix.mul_assoc]]
      abel
    · rw [hgram]
      exact Matrix.posSemidef_conjTranspose_mul_self _
    · rw [hgram]
      exact Matrix.conjTranspose_mul_self_eq_zero
  · -- polar connection
    intro k _ _ A hA
    exact polar_decomposition hA
  · -- coframe closure
    intro h ky _ _ _ Wy d hd
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
      at hd
    rw [← Matrix.mulVec_mulVec]
      at hd
    exact hd
  · -- affine composition
    intro k _ _ U U' ξ ξ'
    simp [Matrix.fromBlocks_multiply]

end NCG
