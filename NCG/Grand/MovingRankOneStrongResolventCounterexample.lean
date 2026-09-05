/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# A moving rank-one strong-resolvent counterexample

On complex `ℓ²(ℕ)`, let `eₙ` be the standard unit vectors, `Pₙ` the
rank-one projection onto `ℂ eₙ`, and `Aₙ = I - Pₙ`.  Then `Pₙ` converges
strongly but not in norm to zero, so `Aₙ` converges strongly to `I`.  More
specifically, `(Aₙ + I)⁻¹ = (I + Pₙ) / 2` converges strongly to
`(I + I)⁻¹ = I / 2`, while `Aₙ eₙ = 0` and the unit zero modes escape.
-/

open Filter Topology
open scoped lp

noncomputable section

namespace NCG.MovingRankOneCounterexample

abbrev Space := ℓ²(ℕ, ℂ)

/-- The `n`th standard unit vector in complex `ℓ²`. -/
def basisVector (n : ℕ) : Space := lp.single 2 n 1

/-- Orthogonal projection onto the moving coordinate line. -/
def projection (n : ℕ) : Space →L[ℂ] Space :=
  InnerProductSpace.rankOne ℂ (basisVector n) (basisVector n)

/-- The positive contraction with the moving coordinate line as kernel. -/
def defectOperator (n : ℕ) : Space →L[ℂ] Space := 1 - projection n

/-- The explicit inverse of `Aₙ + I`. -/
def shiftedResolvent (n : ℕ) : Space →L[ℂ] Space :=
  (2 : ℂ)⁻¹ • (1 + projection n)

@[simp] theorem norm_basisVector (n : ℕ) : ‖basisVector n‖ = 1 := by
  simp [basisVector, lp.norm_single]

@[simp] theorem inner_basisVector_left (n : ℕ) (x : Space) :
    inner ℂ (basisVector n) x = x n := by
  simp [basisVector, lp.inner_single_left]

@[simp] theorem inner_basisVector_basisVector (n m : ℕ) :
    inner ℂ (basisVector n) (basisVector m) = if n = m then 1 else 0 := by
  by_cases hnm : n = m
  · subst m
    simp [basisVector]
  · simp [basisVector, lp.inner_single_left, lp.single_apply, hnm]

/-- Distinct moving zero modes stay a fixed positive distance apart. -/
theorem norm_sub_basisVector_sq {n m : ℕ} (hnm : n ≠ m) :
    ‖basisVector n - basisVector m‖ ^ 2 = 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_basisVector_basisVector]
  simp [hnm]
  norm_num

theorem dist_basisVector_sq {n m : ℕ} (hnm : n ≠ m) :
    dist (basisVector n) (basisVector m) ^ 2 = 2 := by
  simpa only [dist_eq_norm] using norm_sub_basisVector_sq hnm

/-- Every fixed `ℓ²` vector has coordinates tending to zero. -/
theorem coordinate_tendsto_zero (x : Space) :
    Tendsto (fun n : ℕ ↦ x n) atTop (𝓝 0) := by
  let p : ENNReal := 2
  have hsummable :
      Summable (fun n : ℕ ↦ ‖x n‖ ^ p.toReal) := by
    exact (lp.hasSum_norm (p := p) (by simp [p]) x).summable
  have hsq : Tendsto (fun n : ℕ ↦ ‖x n‖ ^ p.toReal) atTop (𝓝 0) :=
    hsummable.tendsto_atTop_zero
  simp only [p, ENNReal.toReal_ofNat, Real.rpow_two] at hsq
  have hnorm : Tendsto (fun n : ℕ ↦ ‖x n‖) atTop (𝓝 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    change Tendsto (fun n : ℕ ↦ √(‖x n‖ ^ 2)) atTop (𝓝 (√0)) at hsqrt
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- The moving rank-one projections converge strongly to zero. -/
theorem projection_tendsto_zero (x : Space) :
    Tendsto (fun n ↦ projection n x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [projection, InnerProductSpace.rankOne_apply, norm_smul,
    norm_basisVector] using
    (coordinate_tendsto_zero x).norm

/-- The projection is idempotent. -/
theorem projection_mul_self (n : ℕ) : projection n * projection n = projection n := by
  exact (InnerProductSpace.isIdempotentElem_rankOne_self (norm_basisVector n)).eq

@[simp] theorem projection_projection (n : ℕ) (x : Space) :
    projection n (projection n x) = projection n x := by
  simp [projection, InnerProductSpace.rankOne_apply]


@[simp] theorem projection_basisVector (n : ℕ) :
    projection n (basisVector n) = basisVector n := by
  simp [projection, InnerProductSpace.rankOne_apply]

@[simp] theorem defectOperator_basisVector (n : ℕ) :
    defectOperator n (basisVector n) = 0 := by
  simp [defectOperator]

/-- `Aₙ + I` has the displayed explicit inverse. -/
theorem defect_add_one_mul_shiftedResolvent (n : ℕ) :
    (defectOperator n + 1) * shiftedResolvent n = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change (defectOperator n + 1) (shiftedResolvent n x) = x
  simp [defectOperator, shiftedResolvent, projection_projection]
  norm_num
  module

/-- The explicit inverse is also a left inverse. -/
theorem shiftedResolvent_mul_defect_add_one (n : ℕ) :
    shiftedResolvent n * (defectOperator n + 1) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change shiftedResolvent n ((defectOperator n + 1) x) = x
  simp [defectOperator, shiftedResolvent, projection_projection]
  norm_num
  module

/-- The shifted resolvents converge strongly to the resolvent `I / 2` of
the strong limit `I`. -/
theorem shiftedResolvent_tendsto_halfIdentity (x : Space) :
    Tendsto (fun n ↦ shiftedResolvent n x) atTop
      (𝓝 ((2 : ℂ)⁻¹ • x)) := by
  have hp := (projection_tendsto_zero x).const_smul (2 : ℂ)⁻¹
  simpa [shiftedResolvent, add_apply, smul_apply] using
    (tendsto_const_nhds.add hp)

/-- The defect operators themselves converge strongly to the identity. -/
theorem defectOperator_tendsto_identity (x : Space) :
    Tendsto (fun n ↦ defectOperator n x) atTop (𝓝 x) := by
  simpa [defectOperator, sub_apply] using
    tendsto_const_nhds.sub (projection_tendsto_zero x)

/-- The convergence is not operator-norm convergence. -/
theorem norm_projection (n : ℕ) : ‖projection n‖ = 1 := by
  simp [projection]

theorem norm_defectOperator_sub_identity (n : ℕ) :
    ‖defectOperator n - 1‖ = 1 := by
  rw [defectOperator]
  simpa using norm_projection n

end NCG.MovingRankOneCounterexample
