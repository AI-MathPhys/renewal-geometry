/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ScoreExport

/-!
# Finite conditional-score and Fisher export

This file proves `thm:conditional-score-panel-export` for one finite record
law differentiated in a common parameter experiment.  Fibre summation
commutes with every coordinate derivative, the coarse score is the weighted
conditional expectation of the fine score, and its Fisher matrix is the
derivative-quotient block displayed in the manuscript.
-/

open Matrix

namespace NCG

/-- Coarse probability obtained by summing a finite law over the fibre of a
declared record map. -/
noncomputable def finiteCoarseMass {Ω Ωc : Type*} [Fintype Ω]
    [DecidableEq Ωc] (c : Ω → Ωc) (p : (ι → ℝ) → Ω → ℝ)
    (θ : ι → ℝ) (y : Ωc) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => c x = y), p θ x

/-- Coordinate derivative of the coarse mass. -/
noncomputable def finiteCoarseDerivative {Ω Ωc ι : Type*} [Fintype Ω]
    [DecidableEq Ωc] (c : Ω → Ωc) (dp : ι → Ω → ℝ)
    (i : ι) (y : Ωc) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => c x = y), dp i x

/-- Score obtained from a positive baseline mass and its coordinate
derivative. -/
noncomputable def finiteScore {Ω ι : Type*} (p₀ : Ω → ℝ)
    (dp : ι → Ω → ℝ) (i : ι) (x : Ω) : ℝ :=
  dp i x / p₀ x

/-- The coarse score in derivative-over-mass form. -/
noncomputable def finiteCoarseScore {Ωc ι : Type*} (q₀ : Ωc → ℝ)
    (dq : ι → Ωc → ℝ) (i : ι) (y : Ωc) : ℝ :=
  dq i y / q₀ y

/-- Weighted conditional expectation of a fine score on a coarse fibre. -/
noncomputable def finiteConditionalScore {Ω Ωc ι : Type*} [Fintype Ω]
    [DecidableEq Ωc] (c : Ω → Ωc) (p₀ : Ω → ℝ)
    (q₀ : Ωc → ℝ) (s : ι → Ω → ℝ) (i : ι) (y : Ωc) : ℝ :=
  (q₀ y)⁻¹ * ∑ x ∈ Finset.univ.filter (fun x => c x = y),
    p₀ x * s i x

/-- Real weighted score Gram. -/
noncomputable def realFisherBlock {Ω ι : Type*} [Fintype Ω]
    (p : Ω → ℝ) (s : ι → Ω → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∑ x, p x * s i x * s j x

/-- The derivative-quotient presentation of a finite Fisher block. -/
noncomputable def derivativeQuotientFisherBlock {Ω ι : Type*} [Fintype Ω]
    (p : Ω → ℝ) (dp : ι → Ω → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∑ x, dp i x * dp j x / p x

/-- Fibre summation commutes with coordinate differentiation of a common
finite parameter experiment. -/
theorem finiteCoarseMass_hasDerivAt {Ω Ωc ι : Type*} [Fintype Ω]
    [DecidableEq Ωc] [DecidableEq ι]
    (c : Ω → Ωc) (p : (ι → ℝ) → Ω → ℝ) (dp : ι → Ω → ℝ)
    (hp : ∀ i x, HasDerivAt (fun t => p (Pi.single i t) x) (dp i x) 0)
    (i : ι) (y : Ωc) :
    HasDerivAt (fun t => finiteCoarseMass c p (Pi.single i t) y)
      (finiteCoarseDerivative c dp i y) 0 := by
  unfold finiteCoarseMass finiteCoarseDerivative
  have h := HasDerivAt.sum (u := Finset.univ.filter (fun x => c x = y))
    (fun x _ => hp i x)
  have heq :
      (∑ x ∈ Finset.univ.filter (fun x => c x = y),
        fun t => p (Pi.single i t) x) =
      fun t => ∑ x ∈ Finset.univ.filter (fun x => c x = y),
        p (Pi.single i t) x := by
    funext t
    simp [Finset.sum_apply]
  rw [heq] at h
  exact h

/-- The full operational export: coarse derivatives, conditional-expectation
scores, and the complete Fisher derivative-quotient formula. -/
theorem finiteConditionalScore_fisherExport
    {Ω Ωc ι : Type*} [Fintype Ω] [Fintype Ωc]
    [DecidableEq Ωc] [DecidableEq ι]
    (c : Ω → Ωc) (p : (ι → ℝ) → Ω → ℝ)
    (p₀ : Ω → ℝ) (dp : ι → Ω → ℝ)
    (hp₀ : ∀ x, p 0 x = p₀ x)
    (hp : ∀ i x, HasDerivAt (fun t => p (Pi.single i t) x) (dp i x) 0)
    (hpne : ∀ x, p₀ x ≠ 0)
    (q₀ : Ωc → ℝ)
    (hq₀ : ∀ y, q₀ y = ∑ x ∈ Finset.univ.filter (fun x => c x = y), p₀ x)
    (hqne : ∀ y, q₀ y ≠ 0) :
    (∀ i y, HasDerivAt
      (fun t => finiteCoarseMass c p (Pi.single i t) y)
      (finiteCoarseDerivative c dp i y) 0)
    ∧ (∀ y, finiteCoarseMass c p 0 y = q₀ y)
    ∧ (∀ i y,
      finiteCoarseScore q₀ (finiteCoarseDerivative c dp) i y =
        finiteConditionalScore c p₀ q₀ (finiteScore p₀ dp) i y)
    ∧ (realFisherBlock q₀
        (finiteCoarseScore q₀ (finiteCoarseDerivative c dp)) =
      derivativeQuotientFisherBlock q₀ (finiteCoarseDerivative c dp)) := by
  constructor
  · exact fun i y => finiteCoarseMass_hasDerivAt c p dp hp i y
  constructor
  · intro y
    rw [hq₀ y]
    unfold finiteCoarseMass
    exact Finset.sum_congr rfl fun x _ => hp₀ x
  constructor
  · intro i y
    unfold finiteCoarseScore finiteConditionalScore finiteScore
    have hsum :
        (∑ x ∈ Finset.univ.filter (fun x => c x = y),
          p₀ x * (dp i x / p₀ x)) =
        ∑ x ∈ Finset.univ.filter (fun x => c x = y), dp i x := by
      refine Finset.sum_congr rfl fun x _ => ?_
      field_simp [hpne x]
    rw [hsum]
    unfold finiteCoarseDerivative
    rw [div_eq_inv_mul]
  · ext i j
    unfold realFisherBlock derivativeQuotientFisherBlock finiteCoarseScore
    refine Finset.sum_congr rfl fun y _ => ?_
    field_simp [hqne y]

/-- Restricting a Fisher matrix to declared coordinate blocks is literal
matrix restriction, so nuisance/provenance/connected subblocks are the
corresponding entries of the common joint Fisher panel. -/
theorem fisherSubblock_apply {ι κ : Type*} (I : Matrix ι ι ℝ)
    (f : κ → ι) (a b : κ) :
    (fun i j => I (f i) (f j)) a b = I (f a) (f b) := rfl

/-- Separate one-coordinate quadratic panels do not determine a mixed sign:
two positive rank-one Fisher blocks can have identical diagonals and opposite
off-diagonal entries. -/
theorem separateFisherDiagonals_doNotDetermineMixedSign :
    let Iplus : Matrix (Fin 2) (Fin 2) ℝ := fun i j => (![1, 1] i) * (![1, 1] j)
    let Iminus : Matrix (Fin 2) (Fin 2) ℝ := fun i j => (![1, -1] i) * (![1, -1] j)
    (∀ i, Iplus i i = Iminus i i) ∧ Iplus 0 1 = -Iminus 0 1 := by
  dsimp
  constructor
  · intro i
    fin_cases i <;> norm_num
  · norm_num

end NCG
