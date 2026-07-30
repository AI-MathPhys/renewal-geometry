/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Threshold masses, congruence transport, and the free-history
Weyl function (SM_emergence, Phase 2)

* `sqrt_mass_leading`, `sqrt_mass_scale` — `thm:sqrt-mass-main`: if
  the threshold-restored chiral block on a character line satisfies
  `Y(δ) = c·δ^{1/2} + O(δ)`, its physical singular value is
  `m = |c|·δ^{1/2} + O(δ)`; with a bound-state gap `δ ≍ Δ²` the
  generic chiral mass is `m ≍ Δ`, not `Δ²`;
* `congruence_kernel_iff`, `congruence_massless_preserved` —
  `thm:neutrino-leading-log-consolidated`: the leading-log transport
  `M ↦ Tᵀ M T` with invertible `T` preserves kernels, so rank is
  preserved and an exact massless state remains massless;
* `freeWeyl`, `freeWeyl_selfConsistent`, `freeWeyl_mem_unit` —
  `thm:free-history-isometry` (Weyl-function layer): the free
  half-line Jacobi chain's Weyl function `U(z) = (z - √(z²-4))/2`
  satisfies the renewal self-consistency `U(z)·(z - U(z)) = 1` and
  lies in `(0,1)` for `z > 2`, so all carrier directions share one
  environmental dependence and can differ only through the finite
  residue matrix `L*L`.
-/

namespace NCG

open Real Matrix

/-! ## `thm:sqrt-mass-main` -/

/-- `thm:sqrt-mass-main` (leading order): if
`|Y(δ) - c·√δ| ≤ K·δ`, then the physical singular value `|Y(δ)|`
satisfies `||Y(δ)| - |c|·√δ| ≤ K·δ` — the chiral mass carries the
square-root threshold order unless the selection rule `c = 0`
holds. -/
theorem sqrt_mass_leading (Y : ℝ → ℂ) (c : ℂ) (K delta : ℝ)
    (h : ‖Y delta - c * (Real.sqrt delta : ℂ)‖ ≤ K * delta) :
    |‖Y delta‖ - ‖c‖ * Real.sqrt delta| ≤ K * delta := by
  have h1 : ‖c * (Real.sqrt delta : ℂ)‖ = ‖c‖ * Real.sqrt delta := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  calc |‖Y delta‖ - ‖c‖ * Real.sqrt delta|
      = |‖Y delta‖ - ‖c * (Real.sqrt delta : ℂ)‖| := by rw [h1]
    _ ≤ ‖Y delta - c * (Real.sqrt delta : ℂ)‖ :=
        abs_norm_sub_norm_le _ _
    _ ≤ K * delta := h

/-- `thm:sqrt-mass-main` (scale): with a bound-state gap
`δ = Δ²`, the leading chiral mass is `|c|·Δ` — linear in the gap
scale `Δ`, not quadratic. -/
theorem sqrt_mass_scale (c : ℂ) (Delta : ℝ) (hD : 0 ≤ Delta) :
    ‖c‖ * Real.sqrt (Delta ^ 2) = ‖c‖ * Delta := by
  rw [Real.sqrt_sq hD]

/-! ## `thm:neutrino-leading-log-consolidated` -/

/-- Congruence transport preserves kernels: for invertible `T`,
`(Tᵀ M T)v = 0` iff `M(Tv) = 0`. -/
theorem congruence_kernel_iff {n : Type*} [Fintype n] [DecidableEq n]
    (M T : Matrix n n ℂ) (hT : IsUnit T) (v : n → ℂ) :
    (Tᵀ * M * T).mulVec v = 0 ↔ M.mulVec (T.mulVec v) = 0 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    have hTt : IsUnit Tᵀ := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
      exact (Matrix.isUnit_iff_isUnit_det T).mp hT
    obtain ⟨U, hU⟩ := hTt.exists_left_inv
    have := congrArg (U.mulVec) h
    rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  · intro h
    rw [h, Matrix.mulVec_zero]

/-- `thm:neutrino-leading-log-consolidated`: an exact massless state
survives the piecewise leading-log congruence transport
`M ↦ Tᵀ M T`: `w` is a null vector of the transported matrix iff
`Tw` is a null vector of the boundary matrix — rank is preserved and
the exact massless state remains massless. -/
theorem congruence_massless_preserved {n : Type*} [Fintype n]
    [DecidableEq n] (M T : Matrix n n ℂ) (hT : IsUnit T)
    (w : n → ℂ) (hw : M.mulVec (T.mulVec w) = 0) :
    (Tᵀ * M * T).mulVec w = 0 :=
  (congruence_kernel_iff M T hT w).mpr hw

/-! ## `thm:free-history-isometry` (Weyl-function layer) -/

/-- The free half-line Jacobi Weyl function
`U(z) = (z - √(z²-4))/2`. -/
noncomputable def freeWeyl (z : ℝ) : ℝ :=
  (z - Real.sqrt (z ^ 2 - 4)) / 2

/-- The renewal self-consistency equation of the free
orthogonal-history environment: `U(z)·(z - U(z)) = 1` — the Weyl
function is the fixed point of one renewal step
`U = (z - U)⁻¹`. -/
theorem freeWeyl_selfConsistent (z : ℝ) (hz : 2 ≤ z) :
    freeWeyl z * (z - freeWeyl z) = 1 := by
  unfold freeWeyl
  have hsq : Real.sqrt (z ^ 2 - 4) ^ 2 = z ^ 2 - 4 :=
    Real.sq_sqrt (by nlinarith)
  nlinarith [hsq]

/-- For `z > 2` the Weyl function lies in `(0, 1)`: the free-history
environment is a strict contraction, so all carrier directions share
one environmental dependence — mass hierarchies must come from the
finite residue matrix `L*L`, not from the free environment. -/
theorem freeWeyl_mem_unit (z : ℝ) (hz : 2 < z) :
    0 < freeWeyl z ∧ freeWeyl z < 1 := by
  unfold freeWeyl
  have h4 : (0:ℝ) ≤ z ^ 2 - 4 := by nlinarith
  have hsq : Real.sqrt (z ^ 2 - 4) ^ 2 = z ^ 2 - 4 :=
    Real.sq_sqrt h4
  have hnn : 0 ≤ Real.sqrt (z ^ 2 - 4) := Real.sqrt_nonneg _
  constructor
  · have hlt : Real.sqrt (z ^ 2 - 4) < z := by
      nlinarith [hsq, hnn]
    linarith
  · have hgt : z - 2 < Real.sqrt (z ^ 2 - 4) := by
      nlinarith [hsq, hnn]
    linarith

end NCG
