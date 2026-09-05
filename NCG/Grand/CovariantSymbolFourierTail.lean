import NCG.Grand.FourierPhaseChordLowerBound
import NCG.Grand.IntegerFourierBox

/-!
# Uniform Fourier tails for covariant lattice symbols

The phase-chord estimate gives coercivity once one Fourier coordinate is
large.  This file combines it with the finite integer boxes from
`IntegerFourierBox` and records a radius-only lower bound.  The result is the
quantitative tail input for norm-resolvent convergence.
-/

namespace NCG

/-- The quadratic coercivity floor outside a Fourier box of radius `R`, when
all connection contributions are bounded by `M`. -/
def covariantFourierTailFloor (R M : ℝ) : ℝ :=
  (4 * R - M) ^ 2

theorem covariantFourierTailFloor_nonneg (R M : ℝ) :
    0 ≤ covariantFourierTailFloor R M := by
  exact sq_nonneg _

/-- Outside the integer Fourier box, one coordinate supplies a uniform
quadratic lower bound for the full covariant symbol. -/
theorem covariantSymbolTotalEnergy_lower_outside_integerFourierBox
    {d : Type*} [Fintype d] [DecidableEq d]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [Nontrivial E]
    (h : ℝ) (R : ℕ) (M : ℝ) (k : d → ℤ)
    (B : d → E →L[ℂ] E) (v : E)
    (hh : 0 < h) (hk : k ∉ integerFourierBox d R)
    (hNyquist : ∀ j, |2 * Real.pi * h * (k j : ℝ)| ≤ Real.pi)
    (hconnection : ∀ j, ‖B j‖ * Real.exp (h * ‖B j‖) ≤ M)
    (hthreshold : M ≤ 4 * (R : ℝ)) :
    covariantFourierTailFloor (R : ℝ) M * ‖v‖ ^ 2 ≤
      covariantSymbolTotalEnergy h (fun j ↦ (k j : ℝ)) B v := by
  obtain ⟨j, hj⟩ :=
    exists_coordinate_natCast_lt_abs_intCast_of_not_mem_integerFourierBox hk
  have hMmode : M ≤ 4 * |(k j : ℝ)| := by
    nlinarith
  have hmode : ‖B j‖ * Real.exp (h * ‖B j‖) ≤ 4 * |(k j : ℝ)| :=
    (hconnection j).trans hMmode
  have hcoordinate := covariantSymbolTotalEnergy_lower_of_coordinate
    h (fun i ↦ (k i : ℝ)) B v j hh (hNyquist j) hmode
  have hleft : 0 ≤ 4 * (R : ℝ) - M := by
    linarith
  have hright :
      0 ≤ 4 * |(k j : ℝ)| - ‖B j‖ * Real.exp (h * ‖B j‖) := by
    linarith
  have hbase :
      4 * (R : ℝ) - M ≤
        4 * |(k j : ℝ)| - ‖B j‖ * Real.exp (h * ‖B j‖) := by
    have := hconnection j
    nlinarith
  have hsquare :
      (4 * (R : ℝ) - M) ^ 2 ≤
        (4 * |(k j : ℝ)| - ‖B j‖ * Real.exp (h * ‖B j‖)) ^ 2 := by
    nlinarith
  calc
    covariantFourierTailFloor (R : ℝ) M * ‖v‖ ^ 2 ≤
        (4 * |(k j : ℝ)| - ‖B j‖ * Real.exp (h * ‖B j‖)) ^ 2 *
          ‖v‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
    _ ≤ covariantSymbolTotalEnergy h (fun i ↦ (k i : ℝ)) B v :=
      hcoordinate

/-- The canonical radius-only coercivity floor used by the global tail
compiler. -/
def integerFourierCoercivityFloor (R : ℕ) : ℝ :=
  (R : ℝ) ^ 2

theorem integerFourierCoercivityFloor_nonneg (R : ℕ) :
    0 ≤ integerFourierCoercivityFloor R := by
  exact sq_nonneg _

/-- The canonical Fourier coercivity floors diverge with the box radius. -/
theorem tendsto_integerFourierCoercivityFloor_atTop :
    Filter.Tendsto integerFourierCoercivityFloor Filter.atTop Filter.atTop := by
  have hcast : Filter.Tendsto (fun R : ℕ ↦ (R : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hfun : integerFourierCoercivityFloor =
      (fun R : ℕ ↦ (R : ℝ) * (R : ℝ)) := by
    funext R
    simp only [integerFourierCoercivityFloor, pow_two]
  rw [hfun]
  exact hcast.atTop_mul_atTop₀ hcast

/-- If the connection term is at most three times the screen radius, the
full symbol has the particularly simple coercivity floor `R²` outside that
screen. -/
theorem integerFourierCoercivityFloor_mul_norm_sq_le_totalEnergy
    {d : Type*} [Fintype d] [DecidableEq d]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [Nontrivial E]
    (h : ℝ) (R : ℕ) (M : ℝ) (k : d → ℤ)
    (B : d → E →L[ℂ] E) (v : E)
    (hh : 0 < h) (hk : k ∉ integerFourierBox d R)
    (hNyquist : ∀ j, |2 * Real.pi * h * (k j : ℝ)| ≤ Real.pi)
    (hconnection : ∀ j,
      ‖B j‖ * Real.exp (h * ‖B j‖) ≤ M)
    (hthreshold : M ≤ 3 * (R : ℝ)) :
    integerFourierCoercivityFloor R * ‖v‖ ^ 2 ≤
      covariantSymbolTotalEnergy h (fun j ↦ (k j : ℝ)) B v := by
  have hmain := covariantSymbolTotalEnergy_lower_outside_integerFourierBox
    h R M k B v hh hk hNyquist hconnection (by linarith)
  have hbase : (R : ℝ) ≤ 4 * (R : ℝ) - M := by
    linarith
  have hsquare : (R : ℝ) ^ 2 ≤ (4 * (R : ℝ) - M) ^ 2 := by
    have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
    nlinarith
  exact (mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)).trans hmain

end NCG
