/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite secant geometry, nuisance shorting, and the
  Fisher limit (`thm:GT-Hellinger-Fisher`,
  Gran-Tensor manuscript)

* `gt_hellinger_identity`: clause (i) — the boxed exact
  Hellinger identity
  `‖𝔥(p) - 𝔥(q)‖² = 8(1 - ∑ √(p q))` for the canonical
  secant embedding `𝔥(p) = 2√p` of full-support laws.

* `gt_hellinger_shorted_gram`: clause (ii) — the boxed
  efficient retained Gram
  `G_{S|N} = S*(1-P_N)S = G_SS - G_SN G_NN⁻¹ G_NS ⪰ 0`
  with `P_N = N(N*N)⁻¹N*` the nuisance secant projection
  (rendered with the invertible normal matrix; the
  pseudoinverse case is the manuscript's degenerate-bank
  reading).

Clauses (iii) and (iv) — the score identification
`∂_θ 𝔥(p_θ)|₀ = √p₀ s` with Fisher Gram
`⟨∂ᵢ𝔥, ∂ⱼ𝔥⟩ = E[sᵢs̄ⱼ]`, and the profiled relative-entropy
Hessian `D²I_prof(0) = S*(1-P_N)S` — are the manuscript's
shrinking-family calculus, converting this finite secant
geometry into the efficient Fisher action.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:GT-Hellinger-Fisher` (i): the boxed exact
Hellinger identity for the secant embedding `2√p`. -/
theorem gt_hellinger_identity {Ω : Type} [Fintype Ω]
    (p q : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (hq : ∀ ω, 0 ≤ q ω)
    (hp1 : ∑ ω, p ω = 1) (hq1 : ∑ ω, q ω = 1) :
    ∑ ω, (2 * Real.sqrt (p ω)
        - 2 * Real.sqrt (q ω)) ^ 2
      = 8 * (1 - ∑ ω, Real.sqrt (p ω * q ω)) := by
  have hterm : ∀ ω,
      (2 * Real.sqrt (p ω) - 2 * Real.sqrt (q ω)) ^ 2
      = 4 * p ω + 4 * q ω
        - 8 * Real.sqrt (p ω * q ω) := by
    intro ω
    have h1 : Real.sqrt (p ω) ^ 2 = p ω :=
      Real.sq_sqrt (hp ω)
    have h2 : Real.sqrt (q ω) ^ 2 = q ω :=
      Real.sq_sqrt (hq ω)
    have h3 : Real.sqrt (p ω * q ω)
        = Real.sqrt (p ω) * Real.sqrt (q ω) :=
      Real.sqrt_mul (hp ω) _
    nlinarith [h1, h2, h3]
  rw [Finset.sum_congr rfl fun ω _ => hterm ω,
    Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    hp1, hq1]
  ring

set_option linter.unusedFintypeInType false in
/-- `thm:GT-Hellinger-Fisher` (ii): the boxed efficient
retained Gram after nuisance shorting. -/
theorem gt_hellinger_shorted_gram {n m k : Type}
    [Fintype n] [Fintype m] [Fintype k] [DecidableEq n]
    [DecidableEq m]
    (N : Matrix n m ℂ) (S : Matrix n k ℂ)
    [Invertible (Nᴴ * N)] :
    -- the boxed Schur form of the shorted Gram
    (Sᴴ * (1 - N * ((Nᴴ * N)⁻¹ * Nᴴ)) * S
      = Sᴴ * S
        - (Sᴴ * N) * ((Nᴴ * N)⁻¹ * (Nᴴ * S)))
    -- and its positivity
    ∧ (Sᴴ * (1 - N * ((Nᴴ * N)⁻¹ * Nᴴ)) * S).PosSemidef
    := by
  set P := N * ((Nᴴ * N)⁻¹ * Nᴴ) with hP
  have hNNH : (Nᴴ * N)ᴴ = Nᴴ * N := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hNNinvH : ((Nᴴ * N)⁻¹)ᴴ = (Nᴴ * N)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hNNH]
  have hPH : Pᴴ = P := by
    rw [hP, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hNNinvH,
      Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hPP : P * P = P := by
    rw [hP]
    calc N * ((Nᴴ * N)⁻¹ * Nᴴ)
          * (N * ((Nᴴ * N)⁻¹ * Nᴴ))
        = N * ((Nᴴ * N)⁻¹ * ((Nᴴ * N)
            * ((Nᴴ * N)⁻¹ * Nᴴ))) := by
          simp only [Matrix.mul_assoc]
      _ = N * ((Nᴴ * N)⁻¹ * Nᴴ) := by
          rw [Matrix.mul_inv_cancel_left_of_invertible]
  constructor
  · rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    congr 1
    rw [hP]
    simp only [Matrix.mul_assoc]
  · have h1P : (1 - P) * (1 - P) = 1 - P := by
      simp only [Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_one, Matrix.one_mul, hPP]
      abel
    have hidem : (1 - P) * ((1 - P) * S) = (1 - P) * S := by
      rw [← Matrix.mul_assoc, h1P]
    have hfact : Sᴴ * (1 - P) * S
        = ((1 - P) * S)ᴴ * ((1 - P) * S) := by
      rw [Matrix.conjTranspose_mul,
        Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one, hPH,
        Matrix.mul_assoc Sᴴ (1 - P) S, ← hidem,
        ← Matrix.mul_assoc, hidem]
    rw [hfact]
    exact Matrix.posSemidef_conjTranspose_mul_self _

/-! ### The physical score derivative and Fisher Gram -/

/-- Differentiating the Hellinger embedding `2√p` along a full-support
one-parameter law family gives the square-root-weighted score.  The hypothesis
`p' = p s` is the derivative form of `s = ∂ log p`. -/
theorem hasDerivAt_hellinger_of_probabilityScore
    {Ω : Type*} (p p' s : ℝ → Ω → ℝ) (θ : ℝ)
    (hp : ∀ ω, HasDerivAt (fun t => p t ω) (p' θ ω) θ)
    (hpos : ∀ ω, 0 < p θ ω)
    (hscore : ∀ ω, p' θ ω = p θ ω * s θ ω) (ω : Ω) :
    HasDerivAt (fun t => 2 * Real.sqrt (p t ω))
      (Real.sqrt (p θ ω) * s θ ω) θ := by
  have hsqrt := (hp ω).sqrt (hpos ω).ne'
  refine (hsqrt.const_mul 2).congr_deriv ?_
  rw [hscore ω]
  have hsne : Real.sqrt (p θ ω) ≠ 0 :=
    (Real.sqrt_pos.mpr (hpos ω)).ne'
  have hsq : Real.sqrt (p θ ω) * Real.sqrt (p θ ω) = p θ ω :=
    Real.mul_self_sqrt (hpos ω).le
  calc
    2 * (p θ ω * s θ ω / (2 * Real.sqrt (p θ ω))) =
        (p θ ω * s θ ω) / Real.sqrt (p θ ω) := by
          field_simp [hsne]
    _ = (Real.sqrt (p θ ω) * Real.sqrt (p θ ω) * s θ ω) /
          Real.sqrt (p θ ω) := by rw [hsq]
    _ = Real.sqrt (p θ ω) * s θ ω := by field_simp [hsne]

/-- The Gram of square-root-weighted score tangents is exactly the finite
Fisher score Gram. -/
theorem hellinger_scoreTangent_gram_eq_fisher
    {Ω J : Type*} [Fintype Ω]
    (p : Ω → ℝ) (s : J → Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (i j : J) :
    ∑ ω, (Real.sqrt (p ω) * s i ω) *
        (Real.sqrt (p ω) * s j ω) =
      ∑ ω, p ω * s i ω * s j ω := by
  apply Finset.sum_congr rfl
  intro ω hω
  calc
    (Real.sqrt (p ω) * s i ω) * (Real.sqrt (p ω) * s j ω) =
        (Real.sqrt (p ω) * Real.sqrt (p ω)) * (s i ω * s j ω) := by ring
    _ = p ω * (s i ω * s j ω) := by
      rw [Real.mul_self_sqrt (hp ω)]
    _ = p ω * s i ω * s j ω := by ring

/-- Clause (iii) of `thm:GT-Hellinger-Fisher`, simultaneously for a finite
bank of coordinate lines. -/
theorem gt_hellinger_score_derivative_and_fisher
    {Ω J : Type*} [Fintype Ω]
    (p p' : J → ℝ → Ω → ℝ) (s : J → Ω → ℝ)
    (hderiv : ∀ j ω, HasDerivAt (fun t => p j t ω) (p' j 0 ω) 0)
    (hpos : ∀ j ω, 0 < p j 0 ω)
    (hbase : ∀ i j ω, p i 0 ω = p j 0 ω)
    (hscore : ∀ j ω, p' j 0 ω = p j 0 ω * s j ω) :
    (∀ j ω, HasDerivAt (fun t => 2 * Real.sqrt (p j t ω))
      (Real.sqrt (p j 0 ω) * s j ω) 0)
    ∧ (∀ i j,
      ∑ ω, (Real.sqrt (p i 0 ω) * s i ω) *
          (Real.sqrt (p j 0 ω) * s j ω) =
        ∑ ω, p i 0 ω * s i ω * s j ω) := by
  constructor
  · intro j ω
    exact hasDerivAt_hellinger_of_probabilityScore
      (p j) (p' j) (fun _ => s j) 0 (hderiv j) (hpos j)
      (hscore j) ω
  · intro i j
    calc
      ∑ ω, (Real.sqrt (p i 0 ω) * s i ω) *
          (Real.sqrt (p j 0 ω) * s j ω) =
          ∑ ω, (Real.sqrt (p i 0 ω) * s i ω) *
            (Real.sqrt (p i 0 ω) * s j ω) := by
              apply Finset.sum_congr rfl
              intro ω hω
              rw [hbase j i ω]
      _ = ∑ ω, p i 0 ω * s i ω * s j ω :=
        hellinger_scoreTangent_gram_eq_fisher
          (p i 0) s (fun ω => (hpos i ω).le) i j

end NCG
