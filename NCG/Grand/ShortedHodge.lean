/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GramHelpers

/-!
# Protected-soft Hodge short and the common compact screen
  (`thm:renewal-shorted-Hodge`, Gran-Tensor manuscript)

* `renewal_shorted_hodge`: for a physical differential `D`
  and protected-soft synthesis `Z` with projection
  `P = Z(ZᴴZ)⁻¹Zᴴ`:
  (i) the shorted action is an exact square
      `S^sh = Dᴴ(1-P)D = ((1-P)D)ᴴ((1-P)D) ⪰ 0`;
  (ii) the boxed variational characterization as an exact
      Pythagoras: for every soft compensation `Y`,
      `(DX+ZY)ᴴ(DX+ZY) = ((1-P)DX)ᴴ((1-P)DX)
        + (PDX+ZY)ᴴ(PDX+ZY)` — so
      `⟨x,S^sh x⟩ = inf_y ‖Dx+Zy‖²`;
  (iii) the infimum is attained at the least-squares
      compensation `Y* = -(ZᴴZ)⁻¹Zᴴ(DX)`:
      `DX + ZY* = (1-P)(DX)`.

The optimal Poincaré-constant and compact-screen clauses are
the manuscript's spectral packaging of these identities.
-/

open Matrix
open scoped ComplexOrder

set_option linter.unusedSimpArgs false

namespace NCG

/-- `thm:renewal-shorted-Hodge`. -/
theorem renewal_shorted_hodge {E Y F : Type*} [Fintype E]
    [Fintype Y] [Fintype F] [DecidableEq Y] [DecidableEq F]
    (D : Matrix Y E ℂ) (Z : Matrix Y F ℂ)
    [Invertible (Zᴴ * Z)] :
    -- (i) the shorted action is an exact square
    Dᴴ * ((1 - Z * (Zᴴ * Z)⁻¹ * Zᴴ) * D)
      = ((1 - Z * (Zᴴ * Z)⁻¹ * Zᴴ) * D)ᴴ
        * ((1 - Z * (Zᴴ * Z)⁻¹ * Zᴴ) * D)
    -- (ii) the exact variational Pythagoras
    ∧ (∀ {m : Type} [Fintype m]
        (X : Matrix E m ℂ) (W : Matrix F m ℂ),
        (D * X + Z * W)ᴴ * (D * X + Z * W)
        = ((1 - Z * (Zᴴ * Z)⁻¹ * Zᴴ) * (D * X))ᴴ
            * ((1 - Z * (Zᴴ * Z)⁻¹ * Zᴴ) * (D * X))
          + (Z * (Zᴴ * Z)⁻¹ * Zᴴ * (D * X) + Z * W)ᴴ
            * (Z * (Zᴴ * Z)⁻¹ * Zᴴ * (D * X) + Z * W))
    -- (iii) attained at the least-squares compensation
    ∧ (∀ {m : Type} [Fintype m] (X : Matrix E m ℂ),
        D * X + Z * (-(Zᴴ * Z)⁻¹ * (Zᴴ * (D * X)))
          = (1 - Z * (Zᴴ * Z)⁻¹ * Zᴴ) * (D * X)) := by
  have hGH : (Zᴴ * Z)ᴴ = Zᴴ * Z := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hGinvH : ((Zᴴ * Z)⁻¹)ᴴ = (Zᴴ * Z)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hGH]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      hGinvH, Matrix.conjTranspose_conjTranspose,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one]
    simp only [Matrix.mul_assoc, proj_cancel Z]
    abel
  · intro m _ X W
    simp only [Matrix.conjTranspose_add,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hGinvH,
      Matrix.conjTranspose_conjTranspose, Matrix.add_mul,
      Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one]
    simp only [Matrix.mul_assoc, proj_cancel Z,
      proj_cancel' Z]
    abel
  · intro m _ X
    rw [Matrix.sub_mul, Matrix.one_mul]
    rw [show Z * (-(Zᴴ * Z)⁻¹ * (Zᴴ * (D * X)))
        = -(Z * (Zᴴ * Z)⁻¹ * Zᴴ * (D * X)) from by
      rw [Matrix.neg_mul, Matrix.mul_neg]
      simp only [Matrix.mul_assoc]]
    abel

end NCG
