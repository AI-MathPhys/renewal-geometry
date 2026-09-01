/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AffineMatrixLogDerivativeExact
import NCG.Grand.BkmMonotonicityExact

/-!
# The BKM relative-entropy Hessian and channel loss

This file packages the exact matrix-log derivative as the derivative of the
first variation of relative entropy.  Subtracting the output first variation
for a Kraus channel gives the local data-processing Hessian, and the existing
BKM contraction proves its nonnegativity.
-/

open Matrix Filter Topology
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ v : Matrix n n ℂ}

/-- The first variation of `D(σ+u v ‖ σ)` in the affine tangent `v`.
For normalized state paths the omitted trace variation vanishes, leaving
exactly this logarithmic pairing. -/
noncomputable def affineRelativeEntropyFirstVariation
    (hσ : σ.IsHermitian) (hv : v.IsHermitian) (u : ℝ) : ℝ :=
  (Matrix.trace (v *
    (matLog (affineMatrix_isHermitian hσ hv u) - matLog hσ))).re

/-- The derivative of the relative-entropy first variation is the BKM form.
Equivalently, this is the exact directional Hessian at every faithful point
of the affine state path. -/
theorem affineRelativeEntropyFirstVariation_hasDerivAt
    (hσ : σ.IsHermitian) (hv : v.IsHermitian) {A B t : ℝ}
    (hpos : ∀ u ∈ Set.Ioo A B, (σ + u • v).PosDef)
    (ht : t ∈ Set.Ioo A B) :
    HasDerivAt (affineRelativeEntropyFirstVariation hσ hv)
      (affineBkmForm hσ hv t) t := by
  have hd := affineMatrixLogPairing_hasDerivAt hσ hv hpos ht
  have hc : HasDerivAt
      (fun _ : ℝ => (Matrix.trace (v * matLog hσ)).re) 0 t :=
    hasDerivAt_const t _
  have hout := hd.sub hc
  have hfun :
      ((fun u : ℝ =>
        (Matrix.trace (v * matLog (affineMatrix_isHermitian hσ hv u))).re) -
        (fun _ : ℝ => (Matrix.trace (v * matLog hσ)).re)) =
      affineRelativeEntropyFirstVariation hσ hv := by
    funext u
    simp only [Pi.sub_apply, affineRelativeEntropyFirstVariation,
      Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [← hfun]
  exact hout.congr_deriv (sub_zero _)

/-- At the base point, the affine relative-entropy Hessian is exactly the
BKM quadratic form `g_σ(v,v)`. -/
theorem affineRelativeEntropyFirstVariation_hasDerivAt_zero
    (hσ : σ.IsHermitian) (hv : v.IsHermitian) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ u ∈ Set.Ioo (-ε) ε, (σ + u • v).PosDef) :
    HasDerivAt (affineRelativeEntropyFirstVariation hσ hv)
      (bkmForm hσ v) 0 := by
  have hd := affineRelativeEntropyFirstVariation_hasDerivAt hσ hv hpos
    (show (0 : ℝ) ∈ Set.Ioo (-ε) ε by constructor <;> linarith)
  have heq : affineBkmForm hσ hv 0 = bkmForm hσ v := by
    unfold affineBkmForm
    apply Petz.bkmForm_congr
    · simp
    · rfl
  exact hd.congr_deriv heq

end QRE

namespace Petz

open NCG.QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {σ v : Matrix n n ℂ}

/-- The first variation of the relative-entropy data-processing loss for a
Kraus channel. -/
noncomputable def affineDataProcessingFirstVariation
    {κ : Type*} [Fintype κ] (K : κ → Matrix m n ℂ)
    (hσ : σ.IsHermitian) (hv : v.IsHermitian) (u : ℝ) : ℝ :=
  affineRelativeEntropyFirstVariation hσ hv u -
    affineRelativeEntropyFirstVariation
      (kraus_isHermitian K hσ) (kraus_isHermitian K hv) u

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **QS.5 as an exact local Hessian identity.**  The derivative at zero of
the data-processing first variation is the input BKM form minus the output
BKM form. -/
theorem affineDataProcessingFirstVariation_hasDerivAt_zero
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix m n ℂ) (hσ : σ.IsHermitian) (hv : v.IsHermitian)
    {ε : ℝ} (hε : 0 < ε)
    (hposIn : ∀ u ∈ Set.Ioo (-ε) ε, (σ + u • v).PosDef)
    (hposOut : ∀ u ∈ Set.Ioo (-ε) ε,
      (kraus K σ + u • kraus K v).PosDef) :
    HasDerivAt (affineDataProcessingFirstVariation K hσ hv)
      (bkmForm hσ v -
        bkmForm (kraus_isHermitian K hσ) (kraus K v)) 0 := by
  have hin := affineRelativeEntropyFirstVariation_hasDerivAt_zero
    hσ hv hε hposIn
  have hout := affineRelativeEntropyFirstVariation_hasDerivAt_zero
    (kraus_isHermitian K hσ) (kraus_isHermitian K hv) hε hposOut
  exact hin.sub hout

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Nonnegative local data-processing Hessian.**  For a trace-preserving
finite Kraus channel with faithful input and output bases, the exact Hessian
coefficient in `affineDataProcessingFirstVariation_hasDerivAt_zero` is
nonnegative. -/
theorem affineDataProcessingBkmHessian_nonneg
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (K : κ → Matrix m n ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)
    (hσ : σ.PosDef) (hbσ : (kraus K σ).PosDef) (v : Matrix n n ℂ) :
    0 ≤ bkmForm hσ.1 v - bkmForm hbσ.1 (kraus K v) :=
  bkmLoss_nonneg K hK hσ hbσ v

end Petz
end NCG
