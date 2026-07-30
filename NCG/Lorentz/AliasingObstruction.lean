/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.ResetDifference

/-!
# The aliasing obstruction to global norm-resolvent convergence

`prop:no-overstatement` (7) of the flagship manuscript: the symmetric
centered-difference scheme does **not** converge in norm resolvent on
the whole momentum space.  At the aliasing momentum `ξ = π/h` the
discrete symbol `sin(hξ)/h` vanishes while the continuum symbol `ξ`
diverges, so the resolvent multipliers stay a definite distance
apart:

* `aliasing_resolvent_gap` — for every mesh `0 < h ≤ π/2` there is a
  momentum at which the two resolvent multipliers (at `z = i`) differ
  by at least `1/2`.

Since the operator norm of the resolvent difference of two Fourier
multipliers is the essential supremum of the pointwise multiplier
difference, this witnesses that the global norm-resolvent distance
never falls below `1/2` — exactly the manuscript's countermodel and
the reason `thm:flat-limit` claims norm-resolvent convergence only on
fixed momentum bands (`thm:band-norm-resolvent`).
-/

namespace NCG

/-- **`prop:no-overstatement` (7)**: at the aliasing momentum
`ξ = π/h` the discrete and continuum resolvent multipliers at `z = i`
stay at least `1/2` apart, for every mesh `0 < h ≤ π/2`. -/
theorem aliasing_resolvent_gap {h : ℝ} (hh : 0 < h)
    (hsmall : h ≤ Real.pi / 2) :
    ∃ ξ : ℝ, (1:ℝ)/2 ≤
      ‖((resetSymbol ξ h : ℂ) - Complex.I)⁻¹
        - ((ξ : ℂ) - Complex.I)⁻¹‖ := by
  refine ⟨Real.pi / h, ?_⟩
  -- the discrete symbol vanishes at the aliasing momentum
  have hsym : resetSymbol (Real.pi / h) h = 0 := by
    unfold resetSymbol
    rw [mul_div_cancel₀ Real.pi hh.ne', Real.sin_pi, mul_zero]
  rw [hsym]
  -- the discrete resolvent multiplier is exactly `i`
  have hdisc : (((0:ℝ) : ℂ) - Complex.I)⁻¹ = Complex.I := by
    rw [Complex.ofReal_zero, zero_sub, inv_neg, Complex.inv_I,
      neg_neg]
  rw [hdisc]
  -- the continuum multiplier is small: `‖(π/h − i)⁻¹‖ ≤ h/π`
  have hπpos : 0 < Real.pi := Real.pi_pos
  have hratio : 0 < Real.pi / h := div_pos hπpos hh
  have hre : Real.pi / h ≤ ‖((Real.pi / h : ℝ) : ℂ) - Complex.I‖ := by
    have h1 : ((((Real.pi / h : ℝ) : ℂ) - Complex.I).re)
        = Real.pi / h := by
      simp
    calc Real.pi / h
        = |(((Real.pi / h : ℝ) : ℂ) - Complex.I).re| := by
          rw [h1, abs_of_pos hratio]
      _ ≤ ‖((Real.pi / h : ℝ) : ℂ) - Complex.I‖ :=
          Complex.abs_re_le_norm _
  have hcont : ‖(((Real.pi / h : ℝ) : ℂ) - Complex.I)⁻¹‖
      ≤ h / Real.pi := by
    rw [norm_inv]
    rw [show h / Real.pi = (Real.pi / h)⁻¹ by
      rw [inv_div]]
    exact inv_anti₀ hratio hre
  -- the continuum multiplier norm is at most `1/2`
  have hhalf : ‖(((Real.pi / h : ℝ) : ℂ) - Complex.I)⁻¹‖ ≤ 1/2 := by
    refine le_trans hcont ?_
    rw [div_le_div_iff₀ hπpos (by norm_num : (0:ℝ) < 2)]
    linarith [hsmall]
  -- reverse triangle inequality against `‖i‖ = 1`
  calc (1:ℝ)/2
      = 1 - 1/2 := by norm_num
    _ ≤ ‖Complex.I‖
        - ‖(((Real.pi / h : ℝ) : ℂ) - Complex.I)⁻¹‖ := by
        rw [Complex.norm_I]
        linarith
    _ ≤ ‖Complex.I - (((Real.pi / h : ℝ) : ℂ) - Complex.I)⁻¹‖ :=
        norm_sub_norm_le _ _

end NCG
