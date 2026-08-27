import NCG.Grand.AcceptedArithmeticAndAffineConsequences
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Target-native arithmetic scalar: exact L² projection criterion

The manuscript's boxed statement is a Hilbert-space identity.  The calibration
class is represented by a finite-dimensional closed subspace `H`; its complete
moment equations hold exactly when the orthogonal projection of the discrepancy
`Y-w` onto `H` has zero squared norm.  Constant calibration and the already
formalized threshold comparator are then direct corollaries.
-/

open scoped InnerProductSpace

namespace NCG.ArithmeticTargetNativeL2Projection

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The exact L² projection characterization of all multiplier moments. -/
theorem projection_sqnorm_zero_iff_multiplier_moments
    (H : Submodule ℝ V) (Y w : V) :
    ‖H.orthogonalProjectionOnto (Y - w)‖ ^ 2 = 0 ↔
      ∀ h : V, h ∈ H → ⟪h, Y⟫_ℝ = ⟪h, w⟫_ℝ := by
  constructor
  · intro hzero h hh
    have hnorm : ‖H.orthogonalProjectionOnto (Y - w)‖ = 0 :=
      sq_eq_zero_iff.mp hzero
    have hproj : H.orthogonalProjectionOnto (Y - w) = 0 :=
      norm_eq_zero.mp hnorm
    have horth : Y - w ∈ Hᗮ :=
      H.orthogonalProjectionOnto_eq_zero_iff.mp hproj
    have hz : ⟪Y - w, h⟫_ℝ = 0 := (H.mem_orthogonal' (Y - w)).mp horth h hh
    rw [real_inner_comm, inner_sub_right, sub_eq_zero] at hz
    exact hz
  · intro hmom
    have horth : Y - w ∈ Hᗮ := by
      apply (H.mem_orthogonal' (Y - w)).mpr
      intro h hh
      rw [real_inner_comm, inner_sub_right, hmom h hh, sub_self]
    have hproj : H.orthogonalProjectionOnto (Y - w) = 0 :=
      H.orthogonalProjectionOnto_eq_zero_iff.mpr horth
    rw [hproj, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- If the constant multiplier vector belongs to the declared calibration
class, the projection criterion implies equality of the selected means. -/
theorem constant_multiplier_gives_mean
    (H : Submodule ℝ V) (Y w one : V) (hone : one ∈ H)
    (hzero : ‖H.orthogonalProjectionOnto (Y - w)‖ ^ 2 = 0) :
    ⟪one, Y⟫_ℝ = ⟪one, w⟫_ℝ :=
  (projection_sqnorm_zero_iff_multiplier_moments H Y w).mp hzero one hone

/-- Conversely, a declared multiplier bank closes the projection residual as
soon as all of its moments agree. -/
theorem multiplier_moments_close_projection
    (H : Submodule ℝ V) (Y w : V)
    (hmom : ∀ h : V, h ∈ H → ⟪h, Y⟫_ℝ = ⟪h, w⟫_ℝ) :
    ‖H.orthogonalProjectionOnto (Y - w)‖ ^ 2 = 0 :=
  (projection_sqnorm_zero_iff_multiplier_moments H Y w).mpr hmom

/-- Finite comparator identity used in the arithmetic packet: once
`w=a+(b-a)q` and the same-event comparator realizes `E[q]=P(U≤q)`, the target
mean is the affine threshold probability. -/
theorem same_event_comparator_mean
    {Ω : Type*} [Fintype Ω] (μ w q : Ω → ℝ)
    (a b probability : ℝ)
    (hμ : ∑ ω, μ ω = 1)
    (hq : ∀ ω, w ω = a + (b - a) * q ω)
    (hcomparator :
      NCG.AcceptedArithmeticAndAffineConsequences.expectation μ q = probability) :
    NCG.AcceptedArithmeticAndAffineConsequences.expectation μ w =
      a + (b - a) * probability :=
  NCG.AcceptedArithmeticAndAffineConsequences.arithmetic_threshold_comparator
    μ w q a b probability hμ hq hcomparator

/-- Bundled exact theorem matching the target-native scalar statement. -/
theorem target_native_arithmetic_scalar
    (H : Submodule ℝ V) (Y w one : V) (hone : one ∈ H) :
    (‖H.orthogonalProjectionOnto (Y - w)‖ ^ 2 = 0 ↔
      ∀ h : V, h ∈ H → ⟪h, Y⟫_ℝ = ⟪h, w⟫_ℝ) ∧
      (‖H.orthogonalProjectionOnto (Y - w)‖ ^ 2 = 0 →
        ⟪one, Y⟫_ℝ = ⟪one, w⟫_ℝ) := by
  exact ⟨projection_sqnorm_zero_iff_multiplier_moments H Y w,
    constant_multiplier_gives_mean H Y w one hone⟩

end NCG.ArithmeticTargetNativeL2Projection
