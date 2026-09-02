import NCG.Grand.L2FiniteCoordinateScreensStrongConvergenceExact

/-!
# The unilateral shift and the finite diagonal-screen obstruction

This file constructs the unilateral shift on `ℓ²(ℕ,ℂ)` from Mathlib's
orthogonal-family extension theorem.  Every nonempty finite diagonal screen
has a last occupied basis vector, and the commutator of that screen with the
shift has operator norm at least one.  Hence no cofinal family of nonzero
finite diagonal screens can commute with the shift in operator norm, although
the initial-segment screens converge strongly by
`L2FiniteCoordinateScreensStrongConvergenceExact`.

This is the core Toeplitz obstruction used in
`thm:GT-NCG-essential-image-trichotomy`.
-/

noncomputable section

open Filter Topology
open scoped lp

namespace NCG
namespace ToeplitzScreenObstruction

abbrev H := ℓ²(ℕ, ℂ)

/-- The standard basis vector `e_n` in `ℓ²(ℕ,ℂ)`. -/
def basisVector (n : ℕ) : H := lp.single 2 n 1

@[simp]
theorem basisVector_apply (n j : ℕ) : basisVector n j = if j = n then 1 else 0 := by
  simp [basisVector, lp.single_apply, Pi.single_apply]

@[simp]
theorem norm_basisVector (n : ℕ) : ‖basisVector n‖ = 1 := by
  simp [basisVector]

/-- The shifted standard basis is orthonormal. -/
theorem shiftedBasis_orthonormal :
    Orthonormal ℂ (fun n : ℕ ↦ basisVector (n + 1)) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp [basisVector, lp.inner_single_left, lp.single_apply, Pi.single_apply]

/-- The unilateral shift `S e_n = e_{n+1}`, constructed as the isometric
extension of the shifted standard basis. -/
def unilateralShiftIsometry : H →ₗᵢ[ℂ] H :=
  (shiftedBasis_orthonormal.orthogonalFamily).linearIsometry

/-- The unilateral shift as a bounded operator. -/
def unilateralShift : H →L[ℂ] H :=
  unilateralShiftIsometry.toContinuousLinearMap

@[simp]
theorem unilateralShift_basisVector (n : ℕ) :
    unilateralShift (basisVector n) = basisVector (n + 1) := by
  change unilateralShiftIsometry (lp.single 2 n 1) = basisVector (n + 1)
  rw [unilateralShiftIsometry,
    OrthogonalFamily.linearIsometry_apply_single]
  simp [basisVector, LinearIsometry.toSpanSingleton_apply]

@[simp]
theorem norm_unilateralShift : ‖unilateralShift‖ = 1 := by
  letI : Nontrivial H :=
    ⟨⟨basisVector 0, 0, by
      intro h
      have h0 := congrArg (fun f : H ↦ f 0) h
      simpa using h0⟩⟩
  exact unilateralShiftIsometry.norm_toContinuousLinearMap

/-- A finite diagonal screen keeps a basis vector precisely when its index is
in the screen. -/
theorem screen_basisVector (s : Finset ℕ) (n : ℕ) :
    l2FinsetScreen (E := ℂ) s (basisVector n) =
      if n ∈ s then basisVector n else 0 := by
  apply lp.ext
  funext j
  by_cases hn : n ∈ s <;> by_cases hj : j = n <;>
    simp [l2FinsetScreen_apply, basisVector_apply, hn, hj]

/-- The screen-shift commutator. -/
def screenShiftCommutator (s : Finset ℕ) : H →L[ℂ] H :=
  (l2FinsetScreen (E := ℂ) s).comp unilateralShift -
    unilateralShift.comp (l2FinsetScreen (E := ℂ) s)

/-- On the last occupied coordinate, the screen-shift commutator is exactly
the negative of the next basis vector. -/
theorem screenShiftCommutator_apply_boundary
    (s : Finset ℕ) (m : ℕ) (hm : m ∈ s) (hnext : m + 1 ∉ s) :
    screenShiftCommutator s (basisVector m) = -basisVector (m + 1) := by
  simp [screenShiftCommutator, screen_basisVector, hm, hnext]

/-- Every finite screen has an index immediately after its maximum outside the
screen. -/
theorem max_succ_not_mem (s : Finset ℕ) (hs : s.Nonempty) :
    s.max' hs + 1 ∉ s := by
  intro hmem
  have hle := Finset.le_max' s (s.max' hs + 1) hmem
  omega

/-- A boundary vector forces the screen-shift commutator norm to be at least
one. -/
theorem one_le_norm_screenShiftCommutator_of_boundary
    (s : Finset ℕ) (m : ℕ) (hm : m ∈ s) (hnext : m + 1 ∉ s) :
    1 ≤ ‖screenShiftCommutator s‖ := by
  have hop := ContinuousLinearMap.le_opNorm
    (screenShiftCommutator s) (basisVector m)
  rw [screenShiftCommutator_apply_boundary s m hm hnext,
    norm_neg, norm_basisVector, norm_basisVector, mul_one] at hop
  exact hop

/-- Every nonzero finite diagonal screen has commutator norm at least one with
the unilateral shift. -/
theorem one_le_norm_screenShiftCommutator
    (s : Finset ℕ) (hs : s.Nonempty) :
    1 ≤ ‖screenShiftCommutator s‖ :=
  one_le_norm_screenShiftCommutator_of_boundary s (s.max' hs)
    (Finset.max'_mem s hs) (max_succ_not_mem s hs)

/-- In particular, commutator norms along any sequence of nonempty finite
diagonal screens cannot tend to zero. -/
theorem not_tendsto_screenShiftCommutator_norm_zero
    (s : ℕ → Finset ℕ) (hs : ∀ n, (s n).Nonempty) :
    ¬ Tendsto (fun n ↦ ‖screenShiftCommutator (s n)‖) atTop (𝓝 0) := by
  intro hzero
  have hevent : ∀ᶠ n in atTop,
      ‖screenShiftCommutator (s n)‖ < (1 : ℝ) / 2 := by
    have := (Metric.tendsto_atTop.mp hzero) (1 / 2) (by norm_num)
    obtain ⟨N, hN⟩ := this
    refine eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
    simpa [Real.dist_eq] using hN n hn
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have hlower := one_le_norm_screenShiftCommutator (s N) (hs N)
  have hupper := hN N le_rfl
  linarith

end ToeplitzScreenObstruction
end NCG
