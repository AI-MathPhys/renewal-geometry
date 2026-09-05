/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Rigidity of the local one-doublet and minimal gauge actions
  (`thm:SMST-action-rigidity`, Gran-Tensor manuscript)

* `smst_action_rigidity`:
  (A1) edge rigidity — a quadratic edge form with coefficient
       matrix `[[a, −c̄],[−c, b]]` whose kernel contains the
       transported diagonal has `c = a` (real) and `b = a`,
       hence is the boxed `w‖Uφ_x − φ_y‖²` multiple;
  (A2) site rigidity — a quartic radial polynomial
       `As² + Bs + C` vanishing to second order at the source
       sphere `s = ρ²` is the boxed `λ(s − ρ²)²`
       (`B = −2Aρ²`, `C = Aρ⁴` from the double zero);
  (A3) face rigidity — the boxed plaquette identity
       `n − Re Tr U = ½‖I − U‖²_HS` for unitary `U`, and the
       affine normalization `S(I) = 0` forces `a = b·n`.

Rendering disclosed: the reduction of a locally gauge-covariant
quadratic form to the constant-coefficient normal form (edge
conjugation by the actual transport), the reduction of
`U(2)`-invariant quartics to radial polynomials, and the
sign/exactness bookkeeping (`w_e, λ_x, w_f > 0` from the
exact zero sets) are the manuscript's invariant-theory and
positivity steps around the proved coefficient identities.
-/

open Matrix

namespace NCG

/-- `thm:SMST-action-rigidity`. -/
theorem smst_action_rigidity :
    -- (A1) diagonal kernel forces the boxed edge coefficients
    (∀ a b : ℝ, ∀ c : ℂ,
      (a : ℂ) - starRingEnd ℂ c = 0 →
      -c + (b : ℂ) = 0 →
      c = (a : ℂ) ∧ (b : ℂ) = (a : ℂ))
    -- (A2) the double zero forces the boxed quartic
    ∧ (∀ A B C ρ2 : ℝ, 0 < ρ2 →
        A * ρ2 ^ 2 + B * ρ2 + C = 0 →
        B + 2 * A * ρ2 = 0 →
        ∀ s : ℝ, A * s ^ 2 + B * s + C
          = A * (s - ρ2) ^ 2)
    -- (A3) the boxed plaquette identity
    ∧ (∀ {n : Type} [Fintype n] [DecidableEq n]
        (U : Matrix n n ℂ), Uᴴ * U = 1 →
        ((Fintype.card n : ℝ) - (U.trace).re)
          = 2⁻¹ * (((1 - U)ᴴ * (1 - U)).trace).re)
    ∧ (∀ (a b : ℝ) (nn : ℕ),
        a - b * nn = 0 → a = b * nn) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c h0 h1
    have hcbar : starRingEnd ℂ c = (a : ℂ) := by
      linear_combination -h0
    have hca : c = (a : ℂ) := by
      have h2 := congrArg (starRingEnd ℂ) hcbar
      rwa [Complex.conj_conj, Complex.conj_ofReal] at h2
    refine ⟨hca, ?_⟩
    have hb : (b : ℂ) = c := by linear_combination h1
    rw [hb, hca]
  · intro A B C ρ2 hρ hzero hderiv s
    have hB : B = -(2 * A * ρ2) := by linarith
    have hC : C = A * ρ2 ^ 2 := by
      rw [hB] at hzero
      nlinarith [hzero]
    rw [hB, hC]
    ring
  · intro n _ _ U hU
    have hexp : (1 - U)ᴴ * (1 - U)
        = 1 - Uᴴ - U + 1 := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
        Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hU]
      abel
    rw [hexp]
    simp only [Matrix.trace_add, Matrix.trace_sub,
      Matrix.trace_one, Matrix.trace_conjTranspose]
    rw [Complex.add_re, Complex.sub_re, Complex.sub_re]
    simp only [Complex.natCast_re, RCLike.star_def,
      Complex.conj_re]
    ring
  · intro a b nn h
    linarith

end NCG
