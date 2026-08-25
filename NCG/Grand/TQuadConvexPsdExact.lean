/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.BkmScalingExact

/-!
# The affine quadratic form at singular members

Step (B4d) of the BKM programme for `cor:accepted-BKM-loss` (QS.5): the
generic convexity of the affine quadratic form at **PSD** members with
range-supported tangents, and the intertwining discharge of the support
condition — the two inputs of the metric twirl.

* `affineOp_posSemidef`: positivity of the affine operator at PSD base;
* `supp_of_intertwine`: `M'·M'⁻ (𝕎x) = 𝕎x` from `M'𝕎 = 𝕎M`, `M` faithful;
* `tQuad_convex_psd`: **convexity at supported PSD members**.
-/

open Matrix Unitary Finset Kronecker
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ : Matrix n n ℂ}

/-! ### Positivity at PSD base -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
theorem affineOp_posSemidef (hσ : σ.PosSemidef) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : (affineOp σ t).PosSemidef := by
  unfold affineOp
  have h1 : (t • (σ ⊗ₖ (1 : Matrix n n ℂ))).PosSemidef :=
    posSemidef_smul_real ht0 (kronR_posSemidef hσ)
  have h2 : ((1 - t) • ((1 : Matrix n n ℂ) ⊗ₖ σᵀ)).PosSemidef :=
    posSemidef_smul_real (by linarith)
      (one_kron_posSemidef (transpose_posSemidef hσ))
  exact h1.add h2

/-! ### The intertwining support discharge -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **The support condition from the intertwining**: if `M'𝕎 = 𝕎M` with
`M` faithful, then vectors in the range of `𝕎` are supported in the
range of `M'`. -/
theorem supp_of_intertwine {N : Type*} [Fintype N] [DecidableEq N]
    {M' : Matrix (N × N) (N × N) ℂ} {M : Matrix (n × n) (n × n) ℂ}
    {𝕎 : Matrix (N × N) (n × n) ℂ}
    (hM' : M'.IsHermitian) (hMp : M.PosDef)
    (hint : M' * 𝕎 = 𝕎 * M) (x : n × n → ℂ) :
    (M' * invMat hM') *ᵥ (𝕎 *ᵥ x) = 𝕎 *ᵥ x := by
  have h1 := invMat_intertwine hM' hMp.1 hint
  calc (M' * invMat hM') *ᵥ (𝕎 *ᵥ x)
      = ((M' * invMat hM') * 𝕎) *ᵥ x := Matrix.mulVec_mulVec _ _ _
    _ = (𝕎 * (M * invMat hMp.1)) *ᵥ x := by
        rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, hint,
          Matrix.mul_assoc]
    _ = 𝕎 *ᵥ x := by
        rw [mul_invMat hMp, Matrix.mul_one]

/-! ### Convexity at supported PSD members -/

set_option maxHeartbeats 1600000 in -- singular Schur transfer
/-- **Convexity of the affine quadratic form at supported PSD members**:
for nonnegative weights, PSD bases with range-supported tangents and a
faithful mixture. -/
theorem tQuad_convex_psd {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ j, 0 ≤ lam j) {σs vs : ι → Matrix n n ℂ}
    (hσj : ∀ j, (σs j).PosSemidef) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hsupp : ∀ j, (affineOp (σs j) t *
      invMat (affineOp_isHermitian (hσj j).1 t)) *ᵥ vecM (vs j) =
      vecM (vs j))
    (hσbar : (∑ j, lam j • σs j).PosDef) :
    tQuad hσbar.1 (∑ j, lam j • vs j) t ≤
      ∑ j, lam j * tQuad (hσj j).1 (vs j) t := by
  have hPj : ∀ j, (affineOp (σs j) t).PosSemidef := fun j =>
    affineOp_posSemidef (hσj j) ht0 ht1
  have hPbar : (∑ j, lam j • affineOp (σs j) t).PosDef := by
    rw [affineOp_linear]
    exact affineOp_posDef hσbar ht0 ht1
  have hconv := quadForm_convex_psd hlam
    (Pmat := fun j => affineOp (σs j) t)
    (xvec := fun j => vecM (vs j)) hPj hsupp hPbar
  unfold tQuad
  rw [vecM_sum_smul]
  rw [invMat_congr (affineOp_linear lam σs t).symm
    (affineOp_isHermitian hσbar.1 t) hPbar.1]
  exact hconv

end QRE
end NCG
