/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# All-order exponential localization in Walsh degree
  (`thm:renewal-chaos-localization`, Gran-Tensor manuscript)

* `graded_conjugation_entry`: the conjugation mechanism — for
  the diagonal degree weight `e^{α(𝒩-2)}`, conjugation scales
  each matrix entry by exactly `e^{α(n_i - n_j)}`, so a
  degree-band operator picks up at most `e^{α·band}` (the source
  of the boxed `q_φ(1+2·sinh α)` bound for a `±1`-band
  insertion);
* `neumann_resummation_bound`: the resummation step — under the
  boxed smallness `ρ = |θ|q_φ(1+2·sinh α) < 1` the corrector
  Neumann series converges with norm at most `(1-ρ)⁻¹`;
* `degree_tail_bound`: the boxed exponential tail — the
  spectral mass of the corrector above Walsh degree `R` is at
  most `e^{-2α(R-2)}` times the conjugated (weighted) square
  norm, uniformly in the cutoff.

Rendering disclosed: the Walsh chaos decomposition, the
identification of the modulation insertion as a `±1` degree-band
operator with band norms `≤ q_φ`, and the constant
`C_{θ,α}` as the conjugated corrector norm are the manuscript's
process layer; the conjugation scaling, the Neumann bound, and
the exponential tail extraction are proved here.
-/

namespace NCG

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Graded conjugation: the diagonal degree weight scales each
entry by exactly `e^{α(nᵢ-nⱼ)}`. -/
theorem graded_conjugation_entry (n : ι → ℝ) (α : ℝ)
    (T : Matrix ι ι ℝ) (i j : ι) :
    (Matrix.diagonal (fun k => Real.exp (α * (n k - 2)))
        * T
        * Matrix.diagonal
          (fun k => Real.exp (-α * (n k - 2)))) i j
      = Real.exp (α * (n i - n j)) * T i j := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [show Real.exp (α * (n i - 2)) * T i j
      * Real.exp (-α * (n j - 2))
    = Real.exp (α * (n i - 2)) * Real.exp (-α * (n j - 2))
      * T i j from by ring]
  rw [← Real.exp_add]
  congr 2
  ring

/-- Exact decomposition of the manuscript weight
`1 + 2 sinh α = 1 + exp α - exp (-α)`. -/
theorem one_add_two_sinh (α : ℝ) :
    1 + 2 * Real.sinh α = 1 + Real.exp α - Real.exp (-α) := by
  rw [Real.sinh_eq]
  ring

/-- The boxed weighted insertion estimate follows by adding the diagonal,
raising, and signed lowering block bounds.  These are precisely the three
blocks exposed by a degree-at-most-one Walsh insertion. -/
theorem walsh_weighted_insertion_bound
    (q α diagonalNorm raisingNorm loweringNorm weightedNorm : ℝ)
    (hq : 0 ≤ q) (hα : 0 ≤ α)
    (hdiag : diagonalNorm ≤ q)
    (hraise : raisingNorm ≤ q)
    (hlower : loweringNorm ≤ q)
    (hweighted : weightedNorm ≤ diagonalNorm
      + (Real.exp α - 1) * raisingNorm
      + (1 - Real.exp (-α)) * loweringNorm) :
    weightedNorm ≤ q * (1 + 2 * Real.sinh α) := by
  have he : 1 ≤ Real.exp α := by
    simpa using Real.exp_le_exp.mpr hα
  have hen : Real.exp (-α) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hα)
  calc
    weightedNorm ≤ diagonalNorm + (Real.exp α - 1) * raisingNorm
        + (1 - Real.exp (-α)) * loweringNorm := hweighted
    _ ≤ q + (Real.exp α - 1) * q
        + (1 - Real.exp (-α)) * q := by
          gcongr
    _ = q * (1 + 2 * Real.sinh α) := by
          rw [one_add_two_sinh]
          ring

section Resummation

variable {A : Type*} [NormedRing A] [NormOneClass A]

/-- Neumann resummation under the boxed smallness condition:
`‖M‖ ≤ ρ < 1` gives `‖Σₖ Mᵏ‖ ≤ (1-ρ)⁻¹`. -/
theorem neumann_resummation_bound [CompleteSpace A]
    (M : A) (ρ : ℝ) (hρ : ρ < 1)
    (hM : ‖M‖ ≤ ρ) :
    ‖∑' k : ℕ, M ^ k‖ ≤ (1 - ρ)⁻¹ := by
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg M) hM
  have hgeo : Summable fun k : ℕ => ρ ^ k :=
    summable_geometric_of_lt_one hρ0 hρ
  have hdom : ∀ k : ℕ, ‖M ^ k‖ ≤ ρ ^ k := by
    intro k
    cases k with
    | zero => simp
    | succ k =>
      calc ‖M ^ (k + 1)‖ ≤ ‖M‖ ^ (k + 1) :=
            norm_pow_le' M k.succ_pos
        _ ≤ ρ ^ (k + 1) :=
            pow_le_pow_left₀ (norm_nonneg M) hM _
  have hsum : Summable fun k : ℕ => ‖M ^ k‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      hdom hgeo
  calc ‖∑' k : ℕ, M ^ k‖
      ≤ ∑' k : ℕ, ‖M ^ k‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' k : ℕ, ρ ^ k := hsum.tsum_le_tsum hdom hgeo
    _ = (1 - ρ)⁻¹ := tsum_geometric_of_lt_one hρ0 hρ

end Resummation

omit [DecidableEq ι] in
/-- Boxed exponential degree tail: the mass above Walsh degree
`R` is at most `e^{-2α(R-2)}` times the conjugated square
norm. -/
theorem degree_tail_bound (n y : ι → ℝ) (hy : ∀ i, 0 ≤ y i)
    (α R : ℝ) (hα : 0 ≤ α) :
    ∑ i ∈ Finset.univ.filter (fun i => R ≤ n i), y i
      ≤ Real.exp (-2 * α * (R - 2))
        * ∑ i, Real.exp (2 * α * (n i - 2)) * y i := by
  have hstep : ∀ i ∈ Finset.univ.filter (fun i => R ≤ n i),
      y i ≤ Real.exp (-2 * α * (R - 2))
        * (Real.exp (2 * α * (n i - 2)) * y i) := by
    intro i hi
    have hni : R ≤ n i := (Finset.mem_filter.mp hi).2
    have hfac : 1 ≤ Real.exp (-2 * α * (R - 2))
        * Real.exp (2 * α * (n i - 2)) := by
      rw [← Real.exp_add]
      have harg : 0 ≤ -2 * α * (R - 2)
          + 2 * α * (n i - 2) := by nlinarith
      calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ _ := Real.exp_le_exp.mpr harg
    calc y i = 1 * y i := (one_mul _).symm
      _ ≤ (Real.exp (-2 * α * (R - 2))
            * Real.exp (2 * α * (n i - 2))) * y i :=
          mul_le_mul_of_nonneg_right hfac (hy i)
      _ = Real.exp (-2 * α * (R - 2))
          * (Real.exp (2 * α * (n i - 2)) * y i) := by ring
  calc ∑ i ∈ Finset.univ.filter (fun i => R ≤ n i), y i
      ≤ ∑ i ∈ Finset.univ.filter (fun i => R ≤ n i),
          Real.exp (-2 * α * (R - 2))
            * (Real.exp (2 * α * (n i - 2)) * y i) :=
        Finset.sum_le_sum hstep
    _ = Real.exp (-2 * α * (R - 2))
        * ∑ i ∈ Finset.univ.filter (fun i => R ≤ n i),
            Real.exp (2 * α * (n i - 2)) * y i := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_
          (Real.exp_nonneg _)
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) fun i _ _ => ?_
        have := hy i
        positivity

/-- Complete localization assembly: the weighted Neumann correction has
square norm at most `sourceNorm²/(1-ρ)²`, hence its mass above degree `R`
has the advertised exponential tail. -/
theorem renewal_chaos_localization
    (n y : ι → ℝ) (hy : ∀ i, 0 ≤ y i)
    (α R ρ sourceNorm weightedNorm : ℝ)
    (hα : 0 ≤ α) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hsource : 0 ≤ sourceNorm) (hwn : 0 ≤ weightedNorm)
    (hweighted : weightedNorm ≤ sourceNorm / (1 - ρ))
    (hsq : ∑ i, Real.exp (2 * α * (n i - 2)) * y i
      ≤ weightedNorm ^ 2) :
    ∑ i ∈ Finset.univ.filter (fun i => R ≤ n i), y i
      ≤ Real.exp (-2 * α * (R - 2))
        * (sourceNorm / (1 - ρ)) ^ 2 := by
  have hden : 0 < 1 - ρ := sub_pos.mpr hρ
  have hs0 : 0 ≤ sourceNorm / (1 - ρ) := by
    positivity
  calc
    ∑ i ∈ Finset.univ.filter (fun i => R ≤ n i), y i
        ≤ Real.exp (-2 * α * (R - 2))
          * ∑ i, Real.exp (2 * α * (n i - 2)) * y i :=
            degree_tail_bound n y hy α R hα
    _ ≤ Real.exp (-2 * α * (R - 2)) * weightedNorm ^ 2 := by
          gcongr
    _ ≤ Real.exp (-2 * α * (R - 2))
        * (sourceNorm / (1 - ρ)) ^ 2 := by
          exact mul_le_mul_of_nonneg_left
            ((sq_le_sq₀ hwn hs0).2 hweighted) (Real.exp_nonneg _)

end NCG
