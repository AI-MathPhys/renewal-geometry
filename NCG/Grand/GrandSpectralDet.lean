/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Spectral-determinant zero lines, circle duality, and gaps
  (`thm:eigenvalue-zero-lines`, `thm:critical-line-circle`,
   `thm:gap-zero-free`, Gran-Tensor manuscript)

In the spectral frame (the normal matrix diagonalized; the
disclosed unitary conjugation leaves every determinant and zero
set unchanged):

* `det_zero_iff` / `zero_line_real_part`: the zeros of
  `D(s) = det(I - e^{-ℓs}·diag λ)` are exactly the eigenvalue
  resonances `e^{-ℓs}λ_j = 1`, and every zero satisfies
  `ℓ·Re s = log‖λ_j‖` — the real parts of the determinant zeros
  are the logarithmic eigenvalue moduli divided by `ℓ`;
* `critical_line_circle`: the boxed equivalences — every zero on
  the line `ℓ·Re s = log√c` iff every eigenvalue has modulus
  `√c` iff `AᴴA = cI`;
* `gap_zero_free`: mass gap ⟷ zero-free half plane —
  `‖λ_j‖ ≤ q` makes `D` zero free in `Re s > τ⁻¹log q`, and
  conversely any eigenvalue of modulus `> r` produces a zero
  with `τ·Re s = log‖λ_j‖ > log r`.

Rendering disclosed: a normal contraction is unitarily
diagonalizable and determinants are conjugation invariant, so
the spectral frame carries the full content; the identification
of `q` with the operator norm is the normal-matrix spectral
radius.
-/

open Matrix

set_option linter.unusedSimpArgs false

namespace NCG

/-- Zeros of the finite spectral determinant are exactly the
eigenvalue resonances `c·λ_j = 1`. -/
theorem det_zero_iff {n : Type*} [Fintype n] [DecidableEq n]
    (lam : n → ℂ) (c : ℂ) :
    Matrix.det (1 - c • Matrix.diagonal lam) = 0
      ↔ ∃ j, c * lam j = 1 := by
  have hdiag : (1 : Matrix n n ℂ) - c • Matrix.diagonal lam
      = Matrix.diagonal (fun j => 1 - c * lam j) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.sub_apply, Matrix.one_apply,
        Matrix.diagonal_apply, hij]
  rw [hdiag, Matrix.det_diagonal, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, -, hj⟩
    exact ⟨j, by linear_combination -hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, Finset.mem_univ j,
      by linear_combination -hj⟩

/-- Every determinant zero lies on an eigenvalue line:
`ℓ·Re s = log‖λ_j‖` for the resonating eigenvalue. -/
theorem zero_line_real_part (lam : ℂ) (l : ℝ) (s : ℂ)
    (hzero : Complex.exp (-(l : ℂ) * s) * lam = 1) :
    l * s.re = Real.log ‖lam‖ := by
  have hlam : lam ≠ 0 := by
    intro h
    rw [h, mul_zero] at hzero
    exact one_ne_zero hzero.symm
  have hnorm := congrArg norm hzero
  rw [norm_mul, Complex.norm_exp, norm_one] at hnorm
  have hre : (-(l : ℂ) * s).re = -(l * s.re) := by
    simp [Complex.mul_re]
  rw [hre] at hnorm
  have hlog := congrArg Real.log hnorm
  rw [Real.log_mul (Real.exp_ne_zero _)
      (norm_ne_zero_iff.mpr hlam), Real.log_exp,
    Real.log_one] at hlog
  linarith

/-- A resonance exists for every nonzero eigenvalue: the zero
at `s = ℓ⁻¹log λ_j`. -/
theorem zero_line_exists (lam : ℂ) (hlam : lam ≠ 0) (l : ℝ)
    (hl : l ≠ 0) :
    Complex.exp (-(l : ℂ) * (Complex.log lam / l)) * lam
      = 1 := by
  have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  have hcast : (-(l : ℂ)) * (Complex.log lam / l)
      = -Complex.log lam := by
    field_simp
  rw [hcast, Complex.exp_neg, Complex.exp_log hlam,
    inv_mul_cancel₀ hlam]

/-- `thm:critical-line-circle` in the spectral frame: every
zero on the critical line iff every eigenvalue on the circle
iff `AᴴA = cI`. -/
theorem critical_line_circle {n : Type*} [Fintype n]
    [DecidableEq n] (lam : n → ℂ) (hlam : ∀ j, lam j ≠ 0)
    (l : ℝ) (hl : 0 < l) (c : ℝ) (hc : 0 < c) :
    ((∀ s : ℂ, Matrix.det (1 - Complex.exp (-(l : ℂ) * s)
          • Matrix.diagonal lam) = 0
        → l * s.re = Real.log (Real.sqrt c))
      ↔ ∀ j, ‖lam j‖ = Real.sqrt c)
    ∧ ((∀ j, ‖lam j‖ = Real.sqrt c)
      ↔ (Matrix.diagonal lam)ᴴ * Matrix.diagonal lam
        = (c : ℂ) • 1) := by
  constructor
  · constructor
    · intro hline j
      have hz := zero_line_exists (lam j) (hlam j) l hl.ne'
      have hdet : Matrix.det (1 - Complex.exp (-(l : ℂ)
          * (Complex.log (lam j) / l))
          • Matrix.diagonal lam) = 0 :=
        (det_zero_iff lam _).mpr ⟨j, hz⟩
      have hres := hline _ hdet
      have hpart := zero_line_real_part (lam j) l _ hz
      have : Real.log ‖lam j‖ = Real.log (Real.sqrt c) := by
        linarith
      have hexp := congrArg Real.exp this
      rwa [Real.exp_log (norm_pos_iff.mpr (hlam j)),
        Real.exp_log (Real.sqrt_pos.mpr hc)] at hexp
    · intro hcirc s hdet
      obtain ⟨j, hj⟩ := (det_zero_iff lam _).mp hdet
      have := zero_line_real_part (lam j) l s hj
      rw [hcirc j] at this
      exact this
  · constructor
    · intro hcirc
      have hdd : (Matrix.diagonal lam)ᴴ * Matrix.diagonal lam
          = Matrix.diagonal
            (fun j => star (lam j) * lam j) := by
        rw [Matrix.diagonal_conjTranspose,
          Matrix.diagonal_mul_diagonal]
        congr 1
      rw [hdd]
      have hval : ∀ j, star (lam j) * lam j = (c : ℂ) := by
        intro j
        rw [Complex.star_def, mul_comm, Complex.mul_conj,
          Complex.normSq_eq_norm_sq, hcirc j,
          Real.sq_sqrt hc.le]
      rw [show (fun j => star (lam j) * lam j)
          = fun _ => (c : ℂ) from funext hval]
      ext i j
      by_cases hij : i = j <;>
        simp [hij, Matrix.diagonal_apply, Matrix.one_apply]
    · intro heq j
      have hdd : (Matrix.diagonal lam)ᴴ * Matrix.diagonal lam
          = Matrix.diagonal
            (fun j => star (lam j) * lam j) := by
        rw [Matrix.diagonal_conjTranspose,
          Matrix.diagonal_mul_diagonal]
        congr 1
      rw [hdd] at heq
      have hent := congrFun (congrFun heq j) j
      rw [Matrix.diagonal_apply_eq] at hent
      rw [Complex.star_def, mul_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq] at hent
      have hreal : ‖lam j‖ ^ 2 = c := by
        have := hent
        simp only [Matrix.smul_apply, Matrix.one_apply_eq,
          smul_eq_mul, mul_one] at this
        exact_mod_cast this
      rw [show Real.sqrt c = Real.sqrt (‖lam j‖ ^ 2) from by
        rw [hreal], Real.sqrt_sq (norm_nonneg _)]

/-- `thm:gap-zero-free` in the spectral frame: the eigenvalue
bound gives the zero-free half plane, and any larger eigenvalue
produces a zero above the corresponding line. -/
theorem gap_zero_free {n : Type*} [Fintype n] [DecidableEq n]
    (lam : n → ℂ) (tau : ℝ) (htau : 0 < tau) (q : ℝ)
    (_hq : 0 < q) (hbound : ∀ j, ‖lam j‖ ≤ q) :
    (∀ s : ℂ, Real.log q / tau < s.re →
      Matrix.det (1 - Complex.exp (-(tau : ℂ) * s)
        • Matrix.diagonal lam) ≠ 0)
    ∧ (∀ (j : n) (r : ℝ), 0 < r → r < ‖lam j‖ →
      ∃ s : ℂ, Complex.exp (-(tau : ℂ) * s) * lam j = 1
        ∧ Real.log r / tau < s.re) := by
  constructor
  · intro s hs hdet
    obtain ⟨j, hj⟩ := (det_zero_iff lam _).mp hdet
    have hline := zero_line_real_part (lam j) tau s hj
    have hlamne : lam j ≠ 0 := by
      intro h
      rw [h, mul_zero] at hj
      exact one_ne_zero hj.symm
    have hle : Real.log ‖lam j‖ ≤ Real.log q :=
      Real.log_le_log (norm_pos_iff.mpr hlamne) (hbound j)
    have : s.re ≤ Real.log q / tau := by
      rw [le_div_iff₀ htau]
      nlinarith [hline]
    linarith
  · intro j r hr hrlam
    have hlamne : lam j ≠ 0 := by
      intro h
      rw [h, norm_zero] at hrlam
      linarith
    refine ⟨Complex.log (lam j) / tau,
      zero_line_exists (lam j) hlamne tau htau.ne', ?_⟩
    have hre : (Complex.log (lam j) / (tau : ℂ)).re
        = Real.log ‖lam j‖ / tau := by
      rw [div_eq_mul_inv, ← Complex.ofReal_inv,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.log_re]
      simp [div_eq_mul_inv]
    rw [hre]
    have hlt : Real.log r < Real.log ‖lam j‖ :=
      Real.log_lt_log hr hrlam
    gcongr

end NCG
