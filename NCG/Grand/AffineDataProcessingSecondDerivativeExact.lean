/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AffineRelativeEntropySecondDerivativeExact

/-!
# Exact affine data-processing Hessian

For a finite Kraus channel, the literal input-minus-output relative-entropy
loss has an explicit derivative field on any faithful affine interval.  Its
base derivative is the BKM loss, which is nonnegative for a trace-preserving
channel.
-/

open Matrix Filter Topology BigOperators
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace Petz

open QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {σ d : Matrix n n ℂ}

/-- Literal relative-entropy data-processing loss along an affine state path,
written in the exactly equal affine coordinates of the output path. -/
noncomputable def affineDataProcessingRelativeEntropy
    {κ : Type*} [Fintype κ] (K : κ → Matrix m n ℂ)
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) (u : ℝ) : ℝ :=
  affineRelativeEntropy hσ hd u -
    affineRelativeEntropy
      (kraus_isHermitian K hσ) (kraus_isHermitian K hd) u

/-- Exact derivative field of the affine data-processing loss. -/
noncomputable def affineDataProcessingRelativeEntropyDerivative
    {κ : Type*} [Fintype κ] (K : κ → Matrix m n ℂ)
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) (u : ℝ) : ℝ :=
  affineRelativeEntropyDerivative hσ hd u -
    affineRelativeEntropyDerivative
      (kraus_isHermitian K hσ) (kraus_isHermitian K hd) u

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
/-- Kraus linearity identifies the affine output coordinates with the channel
applied to the affine input. -/
theorem kraus_affine
    {κ : Type*} [Fintype κ] (K : κ → Matrix m n ℂ) (u : ℝ) :
    kraus K (σ + u • d) = kraus K σ + u • kraus K d := by
  rw [kraus_add]
  have hs := kraus_smul K (u : ℂ) d
  exact congrArg (fun X => kraus K σ + X) hs

/-- The displayed derivative field differentiates the literal
data-processing loss at every point where input and output remain faithful. -/
theorem affineDataProcessingRelativeEntropy_hasDerivAt
    {κ : Type*} [Fintype κ] (K : κ → Matrix m n ℂ)
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) {A B t : ℝ}
    (hposIn : ∀ u ∈ Set.Ioo A B, (σ + u • d).PosDef)
    (hposOut : ∀ u ∈ Set.Ioo A B,
      (kraus K σ + u • kraus K d).PosDef)
    (ht : t ∈ Set.Ioo A B) :
    HasDerivAt (affineDataProcessingRelativeEntropy K hσ hd)
      (affineDataProcessingRelativeEntropyDerivative K hσ hd t) t := by
  have hin := affineRelativeEntropy_hasDerivAt hσ hd hposIn ht
  have hout := affineRelativeEntropy_hasDerivAt
    (kraus_isHermitian K hσ) (kraus_isHermitian K hd) hposOut ht
  exact hin.sub hout

/-- The derivative of the literal loss derivative field is the input BKM
form minus the output BKM form. -/
theorem affineDataProcessingRelativeEntropyDerivative_hasDerivAt_zero
    {κ : Type*} [Fintype κ] (K : κ → Matrix m n ℂ)
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) {ε : ℝ} (hε : 0 < ε)
    (hposIn : ∀ u ∈ Set.Ioo (-ε) ε, (σ + u • d).PosDef)
    (hposOut : ∀ u ∈ Set.Ioo (-ε) ε,
      (kraus K σ + u • kraus K d).PosDef) :
    HasDerivAt (affineDataProcessingRelativeEntropyDerivative K hσ hd)
      (bkmForm hσ d -
        bkmForm (kraus_isHermitian K hσ) (kraus K d)) 0 := by
  have hin := affineRelativeEntropyDerivative_hasDerivAt_zero
    hσ hd hε hposIn
  have hout := affineRelativeEntropyDerivative_hasDerivAt_zero
    (kraus_isHermitian K hσ) (kraus_isHermitian K hd) hε hposOut
  exact hin.sub hout

/-- Literal second-derivative package for the affine data-processing loss. -/
theorem affineDataProcessingRelativeEntropy_hasBkmSecondDerivativeAt_zero
    {κ : Type*} [Fintype κ] (K : κ → Matrix m n ℂ)
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) {ε : ℝ} (hε : 0 < ε)
    (hposIn : ∀ u ∈ Set.Ioo (-ε) ε, (σ + u • d).PosDef)
    (hposOut : ∀ u ∈ Set.Ioo (-ε) ε,
      (kraus K σ + u • kraus K d).PosDef) :
    (∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt (affineDataProcessingRelativeEntropy K hσ hd)
        (affineDataProcessingRelativeEntropyDerivative K hσ hd t) t) ∧
    HasDerivAt (affineDataProcessingRelativeEntropyDerivative K hσ hd)
      (bkmForm hσ d -
        bkmForm (kraus_isHermitian K hσ) (kraus K d)) 0 := by
  constructor
  · intro t ht
    exact affineDataProcessingRelativeEntropy_hasDerivAt
      K hσ hd hposIn hposOut ht
  · exact affineDataProcessingRelativeEntropyDerivative_hasDerivAt_zero
      K hσ hd hε hposIn hposOut

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- The literal affine data-processing Hessian is nonnegative for a finite
trace-preserving Kraus channel with faithful input and output bases. -/
theorem affineDataProcessingRelativeEntropy_secondDerivative_nonneg
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (K : κ → Matrix m n ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)
    (hσ : σ.PosDef) (hbσ : (kraus K σ).PosDef) (d : Matrix n n ℂ) :
    0 ≤ bkmForm hσ.1 d -
      bkmForm (kraus_isHermitian K hσ.1) (kraus K d) :=
  bkmLoss_nonneg K hK hσ hbσ d

end Petz
end NCG
