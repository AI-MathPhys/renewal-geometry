/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ScoreDwellSpectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Global spectral assembly for score--dwell dynamics

This module completes the finite block assembly and exact Hilbert--Schmidt
operator-norm clause of `thm:score-dwell-spectrum`.  The mean, difference,
and odd coordinates of every ordered pair of Store blocks form an explicit
finite mode space.  The score--dwell map is diagonal on that space, so its
fixed space and every power of its distance from the retained expectation
can be read off exactly from the diagonal multipliers.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NCG

/-- Global modes in the dephased Store-block decomposition.  The two odd
coordinates are retained in the bookkeeping even though dephasing assigns
them multiplier zero. -/
inductive ScoreDwellMode (J : Type*)
  | mean : J → J → ScoreDwellMode J
  | difference : J → J → ScoreDwellMode J
  | odd : J → J → Fin 2 → ScoreDwellMode J
  deriving DecidableEq, Fintype

/-- The assembled multiplier of each score--dwell mode. -/
def scoreDwellModeMultiplier {J : Type*} (μ : J → ℝ) (φ : ℝ → ℂ) :
    ScoreDwellMode J → ℂ
  | .mean j k => φ (μ j - μ k)
  | .difference j k => φ (μ j + μ k)
  | .odd _ _ _ => 0

/-- The modes corresponding to the Store commutant
`⊕_j (I₂ ⊗ B(M_j))`: precisely the mean modes with equal block labels. -/
def scoreDwellRetainedMode {J : Type*} [DecidableEq J] :
    ScoreDwellMode J → Bool
  | .mean j k => decide (j = k)
  | .difference _ _ => false
  | .odd _ _ _ => false

/-- The exact global assembly of the two cosine-frequency formulas and the
annihilation of odd modes. -/
theorem scoreDwellModeMultiplier_apply {J : Type*} (μ : J → ℝ)
    (φ : ℝ → ℂ) :
    (∀ j k, scoreDwellModeMultiplier μ φ (.mean j k) =
      φ (μ j - μ k))
    ∧ (∀ j k, scoreDwellModeMultiplier μ φ (.difference j k) =
      φ (μ j + μ k))
    ∧ (∀ j k s, scoreDwellModeMultiplier μ φ (.odd j k s) = 0) := by
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- Orthogonal spectral-coordinate evolution.  Under vectorization of the
Hilbert--Schmidt operator space this is the score--dwell superoperator. -/
def scoreDwellDiagonalEvolution {mode : Type*} [Fintype mode]
    [DecidableEq mode] (multiplier : mode → ℂ) : Matrix mode mode ℂ :=
  Matrix.diagonal multiplier

/-- Orthogonal expectation onto a chosen family of retained modes. -/
def scoreDwellRetainedExpectation {mode : Type*} [Fintype mode]
    [DecidableEq mode] (retained : mode → Bool) : Matrix mode mode ℂ :=
  Matrix.diagonal fun i => if retained i then 1 else 0

/-- The residual diagonal multiplier after the retained modes are removed. -/
def scoreDwellResidualMultiplier {mode : Type*} (retained : mode → Bool)
    (multiplier : mode → ℂ) : mode → ℂ :=
  fun i => if retained i then 0 else multiplier i

/-- Exact fixed-space identification: if retained modes have multiplier one
and every other multiplier differs from one, then a vector is fixed exactly
when it vanishes on all non-retained modes. -/
theorem scoreDwell_fixedSpace_exact {mode : Type*} [Fintype mode]
    [DecidableEq mode] (retained : mode → Bool) (multiplier : mode → ℂ)
    (hone : ∀ i, retained i = true → multiplier i = 1)
    (hother : ∀ i, retained i = false → multiplier i ≠ 1) (x : mode → ℂ) :
    scoreDwellDiagonalEvolution multiplier *ᵥ x = x ↔
      ∀ i, retained i = false → x i = 0 := by
  constructor
  · intro hx i hi
    have hentry := congr_fun hx i
    simp only [scoreDwellDiagonalEvolution, mulVec_diagonal] at hentry
    have hzero : (multiplier i - 1) * x i = 0 := by
      calc
        (multiplier i - 1) * x i = multiplier i * x i - x i := by ring
        _ = 0 := sub_eq_zero.mpr hentry
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr (hother i hi))
  · intro hx
    funext i
    simp only [scoreDwellDiagonalEvolution, mulVec_diagonal]
    cases hret : retained i
    · simp [hx i hret]
    · rw [hone i hret, one_mul]

/-- Exact `2 → 2` norm identity for every positive iterate of a diagonal
score--dwell evolution.  This is the finite Hilbert--Schmidt identity
`‖R^n-E‖ = ρ^n`, with `ρ` the norm of the residual multiplier vector. -/
theorem scoreDwell_power_distance_exact {mode : Type*} [Fintype mode]
    [DecidableEq mode] [Nonempty mode]
    (retained : mode → Bool) (multiplier : mode → ℂ)
    (hone : ∀ i, retained i = true → multiplier i = 1)
    (n : ℕ) (hn : 0 < n) :
    ‖scoreDwellDiagonalEvolution multiplier ^ n -
        scoreDwellRetainedExpectation retained‖ =
      ‖scoreDwellResidualMultiplier retained multiplier‖ ^ n := by
  have hmatrix : scoreDwellDiagonalEvolution multiplier ^ n -
        scoreDwellRetainedExpectation retained =
      Matrix.diagonal (scoreDwellResidualMultiplier retained multiplier ^ n) := by
    rw [scoreDwellDiagonalEvolution, scoreDwellRetainedExpectation,
      Matrix.diagonal_pow]
    ext i j
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    by_cases hij : i = j
    · subst j
      cases hret : retained i
      · simp [scoreDwellResidualMultiplier, hret, hn0]
      · simp [scoreDwellResidualMultiplier, hret, hone i hret, hn0]
    · simp [Matrix.diagonal_apply_ne _ hij]
  rw [hmatrix, Matrix.l2_opNorm_diagonal]
  let residual := scoreDwellResidualMultiplier retained multiplier
  have huniv : (Finset.univ : Finset mode).Nonempty := Finset.univ_nonempty
  have hsup :
      Finset.univ.sup (fun i => ‖(residual ^ n) i‖₊) =
        (Finset.univ.sup fun i => ‖residual i‖₊) ^ n := by
    rw [← Finset.sup'_eq_sup huniv, ← Finset.sup'_eq_sup huniv]
    symm
    rw [Finset.sup'_pow]
    refine Finset.sup'_congr huniv rfl ?_
    intro i hi
    simp [residual]
  rw [Pi.norm_def, Pi.norm_def, hsup]
  norm_cast

/-- Full score--dwell specialization.  If the zero-frequency multiplier is
one and every noncommutant frequency has multiplier different from one, the
fixed coordinates are exactly the Store commutant coordinates.  The same
statement supplies the exact `ρ^n` norm identity for all positive iterates. -/
theorem scoreDwell_global_fixedAlgebra_and_powerNorm
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (μ : J → ℝ) (φ : ℝ → ℂ)
    (hzero : φ 0 = 1)
    (hmean : ∀ j k, j ≠ k → φ (μ j - μ k) ≠ 1)
    (hdifference : ∀ j k, φ (μ j + μ k) ≠ 1)
    (x : ScoreDwellMode J → ℂ) (n : ℕ) (hn : 0 < n) :
    (scoreDwellDiagonalEvolution (scoreDwellModeMultiplier μ φ) *ᵥ x = x ↔
      ∀ mode, scoreDwellRetainedMode mode = false → x mode = 0)
    ∧ (‖scoreDwellDiagonalEvolution (scoreDwellModeMultiplier μ φ) ^ n -
          scoreDwellRetainedExpectation scoreDwellRetainedMode‖ =
        ‖scoreDwellResidualMultiplier scoreDwellRetainedMode
          (scoreDwellModeMultiplier μ φ)‖ ^ n) := by
  let j0 : J := Classical.choice (inferInstance : Nonempty J)
  letI : Nonempty (ScoreDwellMode J) := ⟨.mean j0 j0⟩
  have hone : ∀ mode, scoreDwellRetainedMode mode = true →
      scoreDwellModeMultiplier μ φ mode = 1 := by
    intro mode hret
    cases mode with
    | mean j k =>
        have hjk : j = k := by
          simpa [scoreDwellRetainedMode] using hret
        subst k
        simpa [scoreDwellModeMultiplier] using hzero
    | difference j k => simp [scoreDwellRetainedMode] at hret
    | odd j k s => simp [scoreDwellRetainedMode] at hret
  have hother : ∀ mode, scoreDwellRetainedMode mode = false →
      scoreDwellModeMultiplier μ φ mode ≠ 1 := by
    intro mode hret
    cases mode with
    | mean j k =>
        have hjk : j ≠ k := by
          simpa [scoreDwellRetainedMode] using hret
        exact hmean j k hjk
    | difference j k => exact hdifference j k
    | odd j k s => simp [scoreDwellModeMultiplier]
  exact ⟨scoreDwell_fixedSpace_exact scoreDwellRetainedMode
      (scoreDwellModeMultiplier μ φ) hone hother x,
    scoreDwell_power_distance_exact scoreDwellRetainedMode
      (scoreDwellModeMultiplier μ φ) hone n hn⟩

end NCG
