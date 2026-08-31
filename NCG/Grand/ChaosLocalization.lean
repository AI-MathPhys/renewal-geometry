/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.WalshBandWeightedOperator

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
* `renewal_chaos_localization_from_degree_blocks`: the complete assembly from
  native diagonal/raising/lowering block bounds, with both boxed estimates
  derived rather than assumed.

The Walsh coordinate Parseval estimate and identification of the concrete
modulation insertion with its three degree bands are the manuscript's process
data.  From those native data, the conjugated insertion bound, Neumann bound,
and exponential tail are all proved here.
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

/-- Operator-level discharge of the boxed weighted insertion estimate.  Unlike
`walsh_weighted_insertion_bound`, this theorem does not assume an inequality
for the conjugated norm: it derives it from the exact diagonal/raising/lowering
decomposition and the three native block bounds. -/
theorem walsh_weighted_insertion_bound_from_blocks
    {A : Type*} [SeminormedAddCommGroup A] [NormedSpace ℝ A]
    (D R L : A) (q α : ℝ) (hα : 0 ≤ α)
    (hT : ‖D + R + L‖ ≤ q) (hR : ‖R‖ ≤ q) (hL : ‖L‖ ≤ q) :
    ‖D + Real.exp α • R + Real.exp (-α) • L‖ ≤
      q * (1 + 2 * Real.sinh α) :=
  WalshBandWeightedOperator.norm_weighted_band_le D R L q α hα hT hR hL

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

section WeightedResummation

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
  [NormOneClass B] [CompleteSpace B]

/-- The weighted Neumann corrector bound derived from the degree-band
decomposition.  The strict manuscript condition is used directly with
`ρ = |θ| q (1 + 2 sinh α)`; no norm bound for the conjugated insertion or
for the resummed corrector is assumed. -/
theorem weighted_neumann_corrector_norm_le
    (D R L x : B) (q α θ : ℝ) (hα : 0 ≤ α)
    (hT : ‖D + R + L‖ ≤ q) (hR : ‖R‖ ≤ q) (hL : ‖L‖ ≤ q)
    (hsmall : |θ| * (q * (1 + 2 * Real.sinh α)) < 1) :
    ‖(∑' k : ℕ,
        ((-θ) • (D + Real.exp α • R + Real.exp (-α) • L)) ^ k) * x‖
      ≤ ‖x‖ / (1 - |θ| * (q * (1 + 2 * Real.sinh α))) := by
  let W : B := D + Real.exp α • R + Real.exp (-α) • L
  let ρ : ℝ := |θ| * (q * (1 + 2 * Real.sinh α))
  have hW : ‖W‖ ≤ q * (1 + 2 * Real.sinh α) := by
    exact walsh_weighted_insertion_bound_from_blocks D R L q α hα hT hR hL
  have hM : ‖(-θ) • W‖ ≤ ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
    exact mul_le_mul_of_nonneg_left hW (abs_nonneg θ)
  have hseries : ‖∑' k : ℕ, ((-θ) • W) ^ k‖ ≤ (1 - ρ)⁻¹ :=
    neumann_resummation_bound ((-θ) • W) ρ hsmall hM
  calc
    ‖(∑' k : ℕ, ((-θ) • W) ^ k) * x‖
        ≤ ‖∑' k : ℕ, ((-θ) • W) ^ k‖ * ‖x‖ := norm_mul_le _ _
    _ ≤ (1 - ρ)⁻¹ * ‖x‖ :=
      mul_le_mul_of_nonneg_right hseries (norm_nonneg x)
    _ = ‖x‖ / (1 - ρ) := by rw [div_eq_mul_inv]; ring

end WeightedResummation

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

section NativeDegreeBandAssembly

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
  [NormOneClass B] [CompleteSpace B]

/-- Full operator-level closure of `thm:renewal-chaos-localization` from the
native Walsh degree-band data.  The normalized insertion is split into its
degree-preserving, raising, and lowering blocks `D`, `R`, and `L`.  Their
unweighted bounds imply the manuscript's boxed conjugated-operator estimate;
the strict positivity inequality then controls the exact weighted Neumann
corrector and hence, through the Walsh Parseval estimate `hsq`, its
exponentially small high-degree tail.  In particular, neither boxed norm bound
is supplied as a hypothesis. -/
theorem renewal_chaos_localization_from_degree_blocks
    (D R L x : B) (q α θ : ℝ) (hα : 0 ≤ α)
    (hT : ‖D + R + L‖ ≤ q) (hR : ‖R‖ ≤ q) (hL : ‖L‖ ≤ q)
    (hsmall : |θ| * (q * (1 + 2 * Real.sinh α)) < 1)
    (n y : ι → ℝ) (hy : ∀ i, 0 ≤ y i) (cutoff : ℝ)
    (hsq : ∑ i, Real.exp (2 * α * (n i - 2)) * y i ≤
      ‖(∑' k : ℕ,
          ((-θ) • (D + Real.exp α • R + Real.exp (-α) • L)) ^ k) * x‖ ^ 2) :
    ‖D + Real.exp α • R + Real.exp (-α) • L‖ ≤
        q * (1 + 2 * Real.sinh α)
      ∧ ∑ i ∈ Finset.univ.filter (fun i => cutoff ≤ n i), y i ≤
        Real.exp (-2 * α * (cutoff - 2)) *
          (‖x‖ / (1 - |θ| * (q * (1 + 2 * Real.sinh α)))) ^ 2 := by
  let ρ : ℝ := |θ| * (q * (1 + 2 * Real.sinh α))
  let weightedCorrector : B :=
    (∑' k : ℕ,
      ((-θ) • (D + Real.exp α • R + Real.exp (-α) • L)) ^ k) * x
  have hweightedInsertion :
      ‖D + Real.exp α • R + Real.exp (-α) • L‖ ≤
        q * (1 + 2 * Real.sinh α) :=
    walsh_weighted_insertion_bound_from_blocks D R L q α hα hT hR hL
  have hcorrector : ‖weightedCorrector‖ ≤ ‖x‖ / (1 - ρ) := by
    exact weighted_neumann_corrector_norm_le D R L x q α θ hα hT hR hL hsmall
  have hq : 0 ≤ q := le_trans (norm_nonneg (D + R + L)) hT
  have hsinh : 0 ≤ Real.sinh α := Real.sinh_nonneg_iff.mpr hα
  have hρ0 : 0 ≤ ρ := by
    exact mul_nonneg (abs_nonneg θ)
      (mul_nonneg hq (by positivity))
  have htail := renewal_chaos_localization n y hy α cutoff ρ ‖x‖
    ‖weightedCorrector‖ hα hρ0 hsmall (norm_nonneg x)
    (norm_nonneg weightedCorrector) hcorrector hsq
  exact ⟨hweightedInsertion, htail⟩

end NativeDegreeBandAssembly

end NCG
