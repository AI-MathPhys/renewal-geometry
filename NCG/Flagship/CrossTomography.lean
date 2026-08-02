/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite clock–geometry branch-interference tomography
  (`thm:cross-source-tomography-master`, flagship manuscript)

With the inner product conjugate-linear in its first variable
(Mathlib's convention, matching the manuscript), coherent branch
preparations of `x = S_clk v` and `y = S_geo w` with relative
phases `1, -1, i, -i` reconstruct the cross Gram: the boxed
polarization identities

  `Re⟨x,y⟩ = ¼(‖x+y‖² - ‖x-y‖²)`,
  `Im⟨x,y⟩ = ¼(‖x-iy‖² - ‖x+iy‖²)`,

and the assembled complex matrix element
`⟨x,y⟩ = Re + i·Im` (`cross_source_tomography`).  Applying them
to a finite basis of the metric carrier reconstructs every matrix
element of `B = S_clk*S_geo` and hence every source-identity
defect (prose instantiation).
-/

namespace NCG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `thm:cross-source-tomography-master`, boxed polarization
identities and the reconstructed complex matrix element. -/
theorem cross_source_tomography (x y : E) :
    (inner ℂ x y : ℂ).re
      = 4⁻¹ * (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2)
    ∧ (inner ℂ x y : ℂ).im
      = 4⁻¹ * (‖x - Complex.I • y‖ ^ 2 - ‖x + Complex.I • y‖ ^ 2)
    ∧ (inner ℂ x y : ℂ)
      = ((4⁻¹ * (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) : ℝ) : ℂ)
        + ((4⁻¹ * (‖x - Complex.I • y‖ ^ 2
            - ‖x + Complex.I • y‖ ^ 2) : ℝ) : ℂ) * Complex.I := by
  have hre : (inner ℂ x y : ℂ).re
      = 4⁻¹ * (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) := by
    have h1 := norm_add_sq (𝕜 := ℂ) x y
    have h2 := norm_sub_sq (𝕜 := ℂ) x y
    simp only [RCLike.re_to_complex] at h1 h2
    linarith
  have him : (inner ℂ x y : ℂ).im
      = 4⁻¹ * (‖x - Complex.I • y‖ ^ 2
          - ‖x + Complex.I • y‖ ^ 2) := by
    have h1 := norm_add_sq (𝕜 := ℂ) x (Complex.I • y)
    have h2 := norm_sub_sq (𝕜 := ℂ) x (Complex.I • y)
    rw [inner_smul_right] at h1 h2
    simp only [RCLike.re_to_complex, Complex.mul_re, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_sub] at h1 h2
    have h3 : ‖Complex.I • y‖ = ‖y‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    rw [h3] at h1 h2
    linarith
  refine ⟨hre, him, ?_⟩
  rw [← hre, ← him]
  exact (Complex.re_add_im _).symm

end NCG
