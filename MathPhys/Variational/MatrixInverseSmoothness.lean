/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Smoothness of the determinant and of the inverse entries of real `4 × 4` matrices

* `NativeScaling.Mat`: real `4 × 4` matrices;
* `contDiff_det`, `contDiff_adjugate_entry`: the determinant and the adjugate entries are
  polynomial, hence `C^k` for every `k`;
* `invEntry i j e = e⁻¹ i j` and `contDiffAt_invEntry`: the inverse entries are `C^k` at every
  invertible matrix (`A⁻¹ = (det A)⁻¹ adj A`).

Split out of `NativeScalingBlocksExact` (`Mat`) and `NativeDensitiesExact` (the smoothness
lemmas); declaration names unchanged.
-/

open NormedSpace Finset
open scoped ContDiff

namespace MathPhys
namespace NativeScaling


/-- Real `4 × 4` matrices: coframes `e^a_μ` (row `a`, column `μ`) and jets. -/
abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ

end NativeScaling

namespace NativeDensity

open NativeScaling (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_det {k : WithTop ℕ∞} : ContDiff ℝ k (fun M : Mat => M.det) := by
  simp only [Matrix.det_apply']
  fun_prop

theorem contDiff_adjugate_entry (i j : Fin 4) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun A : Mat => A.adjugate i j) := by
  simp only [Matrix.adjugate_apply, Matrix.det_apply', Matrix.updateRow_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun k _ => ?_)
  split_ifs <;> fun_prop

/-- The `(i, j)` entry of the matrix inverse, as a named function. -/
noncomputable def invEntry (i j : Fin 4) (e : Mat) : ℝ := e⁻¹ i j

theorem invEntry_apply (i j : Fin 4) (e : Mat) : invEntry i j e = e⁻¹ i j := rfl

@[fun_prop]
theorem contDiffAt_invEntry (i j : Fin 4) {k : WithTop ℕ∞} {A : Mat} (hA : A.det ≠ 0) :
    ContDiffAt ℝ k (invEntry i j) A := by
  have : invEntry i j = fun M : Mat => (M.det)⁻¹ * M.adjugate i j := by
    funext M
    rw [invEntry, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [this]
  exact ((contDiffAt_inv ℝ hA).comp A contDiff_det.contDiffAt).mul
    (contDiff_adjugate_entry i j).contDiffAt

end NativeDensity
end MathPhys
