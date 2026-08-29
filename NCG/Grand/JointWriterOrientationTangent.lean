/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMSTJointWriter
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Infinitesimal joint-writer orientation

This file supplies the derivative layer SMW.6 omitted from
`SMSTJointWriter`.  Differentiating the polar factorization `W = U P`, the
unitary identity `U*U=I`, and self-adjointness of `P` shows that the connected
orientation tangent is exactly the skew part of the whitened overlap tangent.
The self-adjoint endpoint-Fisher stretch cancels, leaving
`Ω = 1/2 M⁻¹(C₁-C₁*)`.
-/

open Matrix

namespace NCG
namespace JointWriterOrientationTangent

attribute [local instance 2000] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Differentiated polar decomposition at the identity. -/
theorem polar_orientation_derivative
    (W U P : ℝ → Matrix n n ℂ)
    (W₁ Ω S : Matrix n n ℂ)
    (hW0 : W 0 = 1) (hU0 : U 0 = 1) (hP0 : P 0 = 1)
    (hW : HasDerivAt W W₁ 0)
    (hU : HasDerivAt U Ω 0)
    (hP : HasDerivAt P S 0)
    (hUstar : HasDerivAt (fun t => (U t)ᴴ) Ωᴴ 0)
    (hPstar : HasDerivAt (fun t => (P t)ᴴ) Sᴴ 0)
    (hfactor : W = fun t => U t * P t)
    (hunitary : (fun t => (U t)ᴴ * U t) = fun _ => 1)
    (hself : (fun t => (P t)ᴴ) = P) :
    W₁ = Ω + S ∧ Ωᴴ = -Ω ∧ Sᴴ = S ∧
      Ω = (2 : ℂ)⁻¹ • (W₁ - W₁ᴴ) := by
  have hprod : HasDerivAt (fun t => U t * P t)
      (Ω * P 0 + U 0 * S) 0 := hU.mul hP
  rw [hU0, hP0, Matrix.mul_one, Matrix.one_mul] at hprod
  have hsplit : W₁ = Ω + S := by
    rw [hfactor] at hW
    exact hW.unique hprod
  have hgram : HasDerivAt (fun t => (U t)ᴴ * U t)
      (Ωᴴ * U 0 + (U 0)ᴴ * Ω) 0 := hUstar.mul hU
  rw [hU0, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul] at hgram
  have hzero : HasDerivAt (fun _ : ℝ => (1 : Matrix n n ℂ)) 0 0 :=
    hasDerivAt_const 0 1
  rw [hunitary] at hgram
  have hskewsum : Ωᴴ + Ω = 0 := hgram.unique hzero
  have hskew : Ωᴴ = -Ω := eq_neg_of_add_eq_zero_left hskewsum
  rw [hself] at hPstar
  have hSself : Sᴴ = S := hPstar.unique hP
  refine ⟨hsplit, hskew, hSself, ?_⟩
  rw [hsplit, Matrix.conjTranspose_add, hskew, hSself]
  module

/-- SMW.6.  If the first-order whitened overlap consists of the mixed-score
tangent `M⁻¹C₁` minus a self-adjoint endpoint-Fisher stretch, then only its
skew part enters the connected writer. -/
theorem connected_writer_formula
    (W U P : ℝ → Matrix n n ℂ)
    (MInv C₁ endpointStretch Ω modulusTangent : Matrix n n ℂ)
    (hW0 : W 0 = 1) (hU0 : U 0 = 1) (hP0 : P 0 = 1)
    (hW : HasDerivAt W (MInv * C₁ - endpointStretch) 0)
    (hU : HasDerivAt U Ω 0)
    (hP : HasDerivAt P modulusTangent 0)
    (hUstar : HasDerivAt (fun t => (U t)ᴴ) Ωᴴ 0)
    (hPstar : HasDerivAt (fun t => (P t)ᴴ) modulusTangentᴴ 0)
    (hfactor : W = fun t => U t * P t)
    (hunitary : (fun t => (U t)ᴴ * U t) = fun _ => 1)
    (hself : (fun t => (P t)ᴴ) = P)
    (hM : MInvᴴ = MInv)
    (hEndpoint : endpointStretchᴴ = endpointStretch)
    (hComm : C₁ᴴ * MInv = MInv * C₁ᴴ) :
    Ω = (2 : ℂ)⁻¹ • (MInv * (C₁ - C₁ᴴ)) := by
  have hpolar := polar_orientation_derivative W U P
    (MInv * C₁ - endpointStretch) Ω modulusTangent
    hW0 hU0 hP0 hW hU hP hUstar hPstar hfactor hunitary hself
  rw [hpolar.2.2.2]
  congr 1
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hM, hEndpoint,
    hComm, Matrix.mul_sub]
  abel

/-- Complete orientation packet: the existing twelve-angle parameter count
and the derived connected-writer formula are available together. -/
theorem joint_writer_orientation_with_derivative :
    (3 + 2 * 3 + 3 = 12) ∧
    ∀ (W U P : ℝ → Matrix n n ℂ)
      (MInv C₁ endpointStretch Ω modulusTangent : Matrix n n ℂ),
      W 0 = 1 → U 0 = 1 → P 0 = 1 →
      HasDerivAt W (MInv * C₁ - endpointStretch) 0 →
      HasDerivAt U Ω 0 → HasDerivAt P modulusTangent 0 →
      HasDerivAt (fun t => (U t)ᴴ) Ωᴴ 0 →
      HasDerivAt (fun t => (P t)ᴴ) modulusTangentᴴ 0 →
      W = (fun t => U t * P t) →
      (fun t => (U t)ᴴ * U t) = (fun _ => 1) →
      (fun t => (P t)ᴴ) = P →
      MInvᴴ = MInv → endpointStretchᴴ = endpointStretch →
      C₁ᴴ * MInv = MInv * C₁ᴴ →
      Ω = (2 : ℂ)⁻¹ • (MInv * (C₁ - C₁ᴴ)) := by
  refine ⟨by norm_num, ?_⟩
  intro W U P MInv C₁ endpointStretch Ω modulusTangent
  exact connected_writer_formula W U P MInv C₁ endpointStretch Ω modulusTangent

end JointWriterOrientationTangent
end NCG
