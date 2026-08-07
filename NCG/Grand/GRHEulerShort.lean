/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointSourceCore

/-!
# Canonical completed–Euler short
  (`thm:GRH-completed-Euler-short`, Gran-Tensor manuscript)

* `grh_completed_euler_short`: for the hatted (nuisance-free)
  completed and Euler syntheses `Â, Ŝ` with Gram blocks
  `M̂ = ÂᴴÂ`, `Ê = ŜᴴŜ`, `B̂ = ÂᴴŜ`, the exact Euler source
  innovation `R = Ê - B̂ᴴM̂⁻¹B̂` is the projected Gram
  `Ŝᴴ(1-Π_A)Ŝ ⪰ 0`, it vanishes exactly on source inclusion,
  and the boxed Pythagoras `Ê = DᴴM̂D + R` holds with the
  reduced factor `D = M̂⁻¹B̂`.

Rendering disclosed: the faithful-support (invertible `M̂`)
rendering as in `thm:joint-source-short`; the relative density
`H_{E/M} = M̂^{†/2}ÊM̂^{†/2}` order criterion and the sharp
bridge defect `η⁺` are `thm:relative-metric-density` (hard tier,
needs the matrix square-root library).
-/

open Matrix
open scoped ComplexOrder

namespace NCG

set_option linter.unusedFintypeInType false

/-- `thm:GRH-completed-Euler-short`. -/
theorem grh_completed_euler_short {h eM eE : Type*} [Fintype h]
    [Fintype eM] [Fintype eE] [DecidableEq h] [DecidableEq eM]
    (A : Matrix h eM ℂ) (S : Matrix h eE ℂ)
    [Invertible (Aᴴ * A)] :
    (Sᴴ * S - (Aᴴ * S)ᴴ * (Aᴴ * A)⁻¹ * (Aᴴ * S)
      = Sᴴ * ((1 - A * (Aᴴ * A)⁻¹ * Aᴴ) * S))
    ∧ (Sᴴ * S
        - (Aᴴ * S)ᴴ * (Aᴴ * A)⁻¹ * (Aᴴ * S)).PosSemidef
    ∧ (Sᴴ * S - (Aᴴ * S)ᴴ * (Aᴴ * A)⁻¹ * (Aᴴ * S) = 0
        ↔ (1 - A * (Aᴴ * A)⁻¹ * Aᴴ) * S = 0)
    ∧ (((Aᴴ * A)⁻¹ * (Aᴴ * S))ᴴ * (Aᴴ * A)
          * ((Aᴴ * A)⁻¹ * (Aᴴ * S))
        + (Sᴴ * S - (Aᴴ * S)ᴴ * (Aᴴ * A)⁻¹ * (Aᴴ * S))
      = Sᴴ * S) := by
  obtain ⟨hres, hpsd, hiff⟩ := joint_source_short S A
  refine ⟨hres, hpsd, hiff, ?_⟩
  -- the Pythagoras: DᴴM̂D collapses to B̂ᴴM̂⁻¹B̂
  have hGherm : (Aᴴ * A)ᴴ = Aᴴ * A := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hGinvherm : ((Aᴴ * A)⁻¹)ᴴ = (Aᴴ * A)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hGherm]
  have hD : ((Aᴴ * A)⁻¹ * (Aᴴ * S))ᴴ * (Aᴴ * A)
      * ((Aᴴ * A)⁻¹ * (Aᴴ * S))
      = (Aᴴ * S)ᴴ * (Aᴴ * A)⁻¹ * (Aᴴ * S) := by
    calc ((Aᴴ * A)⁻¹ * (Aᴴ * S))ᴴ * (Aᴴ * A)
          * ((Aᴴ * A)⁻¹ * (Aᴴ * S))
        = (Aᴴ * S)ᴴ * (((Aᴴ * A)⁻¹)ᴴ * ((Aᴴ * A)
            * ((Aᴴ * A)⁻¹ * (Aᴴ * S)))) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (Aᴴ * S)ᴴ * ((Aᴴ * A)⁻¹ * (Aᴴ * S)) := by
          rw [hGinvherm, show (Aᴴ * A)
              * ((Aᴴ * A)⁻¹ * (Aᴴ * S))
              = ((Aᴴ * A) * (Aᴴ * A)⁻¹) * (Aᴴ * S) from by
            simp only [Matrix.mul_assoc],
            Matrix.mul_inv_of_invertible, Matrix.one_mul]
      _ = (Aᴴ * S)ᴴ * (Aᴴ * A)⁻¹ * (Aᴴ * S) := by
          simp only [Matrix.mul_assoc]
  rw [hD]
  abel

end NCG
