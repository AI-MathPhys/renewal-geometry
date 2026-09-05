/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Simple poles give rank-one residues
  (`prop:rank-one-residues-current`, SM_emergence)

For a simple eigenpair `Cξ = λξ` of the environmental block, the
resolvent acts on the eigenline by `(λ - z)⁻¹`, and the spectral
projector insertion `L(ξξ*)R` is the rank-one matrix `x y*` with
`x = Lξ`, `y = R*ξ`:

* `eigen_resolvent_action` — `(C - z)⁻¹ξ = (λ - z)⁻¹ξ` away from
  the spectrum;
* `residue_rank_one` — `L·ξξ*·R = x y*` with rank at most one.

The meromorphic resolvent expansion collecting these terms into
`-x y*/(λ - z)` is the declared complex-analytic packaging.
-/

namespace NCG

open Matrix

/-- `prop:rank-one-residues-current` (eigenline action): the
resolvent acts on a simple eigenline by the scalar `(λ - z)⁻¹`. -/
theorem eigen_resolvent_action {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℂ) (ξ : Fin n → ℂ) (lam z : ℂ)
    (hξ : C.mulVec ξ = lam • ξ) (hz : lam ≠ z)
    (hinv : IsUnit (C - z • 1).det) :
    (C - z • 1)⁻¹.mulVec ξ = (lam - z)⁻¹ • ξ := by
  have hact : (C - z • 1).mulVec ((lam - z)⁻¹ • ξ) = ξ := by
    rw [Matrix.mulVec_smul, Matrix.sub_mulVec, hξ, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    rw [← sub_smul, smul_smul,
      inv_mul_cancel₀ (sub_ne_zero.mpr hz), one_smul]
  calc (C - z • 1)⁻¹.mulVec ξ
      = (C - z • 1)⁻¹.mulVec ((C - z • 1).mulVec
          ((lam - z)⁻¹ • ξ)) := by rw [hact]
  _ = (lam - z)⁻¹ • ξ := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hinv,
          Matrix.one_mulVec]

/-- `prop:rank-one-residues-current` (rank-one residue): the
projector insertion is the rank-one matrix `x y*` with `x = Lξ`,
`y = R*ξ`. -/
theorem residue_rank_one {kL kR e : ℕ}
    (L : Matrix (Fin kL) (Fin e) ℂ) (R : Matrix (Fin e) (Fin kR) ℂ)
    (ξ : Fin e → ℂ) :
    L * Matrix.vecMulVec ξ (star ξ) * R
        = Matrix.vecMulVec (L.mulVec ξ) (star (Rᴴ.mulVec ξ))
      ∧ (L * Matrix.vecMulVec ξ (star ξ) * R).rank ≤ 1 := by
  have hL : L * Matrix.vecMulVec ξ (star ξ)
      = Matrix.vecMulVec (L.mulVec ξ) (star ξ) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply,
      Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hR : Matrix.vecMulVec (L.mulVec ξ) (star ξ) * R
      = Matrix.vecMulVec (L.mulVec ξ) (star (Rᴴ.mulVec ξ)) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply,
      Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      Pi.star_apply]
    rw [show star (∑ k, star (R k j) * ξ k)
      = ∑ k, R k j * star (ξ k) from by
        rw [star_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [star_mul', star_star]]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have heq : L * Matrix.vecMulVec ξ (star ξ) * R
      = Matrix.vecMulVec (L.mulVec ξ) (star (Rᴴ.mulVec ξ)) := by
    rw [hL, hR]
  refine ⟨heq, ?_⟩
  rw [heq]
  exact Matrix.rank_vecMulVec_le _ _

end NCG
