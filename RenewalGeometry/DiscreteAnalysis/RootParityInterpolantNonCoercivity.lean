/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicGridInterpolation
import RenewalGeometry.DiscreteAnalysis.RootParityConnectorExact

/-!
# Root-parity non-coercivity against the interpolant gradient (`lem:supp-open-parity`)

`RootParityConnectorExact` proves the root-parity obstruction against the coordinate
Dirichlet form `𝒟_C(u) = Σ_i ‖D_i⁺ u‖_h²`.  With the uniform symbol comparison of
`PeriodicGridInterpolation` (`(2/π)² ‖∇𝓘_h u‖²_{L²} ≤ 𝒟_C(u) ≤ ‖∇𝓘_h u‖²_{L²}`) this
becomes the manuscript's statement for the trigonometric interpolant:

* `coordDirichlet_eq_coordForm`: the two encodings of `𝒟_C` agree;
* `rootDirichlet_not_uniformly_coercive_interp`: no `c > 0` satisfies
  `c ‖∇𝓘_h u‖²_{L²} ≤ 𝒟_F(u)` for all odd `N` and all `u`;
* `parityTest_gradient_ge`: the parity test has `‖∇𝓘_h u_h‖² ≥ 6N²` while
  `𝒟_F(u_h) ≤ 12π²`;
* `connector_coercivity_interp`: `(1/5)(2/π)² ‖∇𝓘_h u‖² ≤ 𝒟₊(u) ≤ 9 ‖∇𝓘_h u‖²`.
-/

open Finset
open scoped BigOperators Real

namespace RenewalGeometry.RootParityInterpolant

open PeriodicGridSobolev RootParityConnector

variable {N : ℕ} [NeZero N]

/-- The coordinate Dirichlet form of `RootParityConnectorExact` equals
`Σ_i ‖D_i⁺ u‖_h²` of the grid Sobolev calculus. -/
theorem coordDirichlet_eq_coordForm (u : RootParityConnector.Grid N → ℂ) :
    coordDirichlet N u = coordForm u := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hterm : ∀ i : Fin 3, gridNormSq (Dp i u) = (N : ℝ)⁻¹ * shiftEnergy N (e N i) u := by
    intro i
    unfold gridNormSq shiftEnergy
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [Dp_apply, norm_mul, mul_pow, Complex.norm_natCast]
    simp only [e, unit]
    field_simp
  unfold coordDirichlet coordForm
  rw [Fin.sum_univ_three, hterm 0, hterm 1, hterm 2]
  ring

/-- `(2/π)² ‖∇𝓘_h u‖²_{L²} ≤ 𝒟_C(u) ≤ ‖∇𝓘_h u‖²_{L²}`. -/
theorem coordDirichlet_equiv_interp (u : RootParityConnector.Grid N → ℂ) :
    (2 / π) ^ 2 * trigGradSq (interp u) ≤ coordDirichlet N u ∧
      coordDirichlet N u ≤ trigGradSq (interp u) := by
  rw [coordDirichlet_eq_coordForm]
  exact ⟨trigGradSq_interp_le_coordForm u, coordForm_le_trigGradSq_interp u⟩

/-- `lem:supp-open-parity`, non-coercivity clause: the root Dirichlet form is not uniformly
coercive for `‖∇𝓘_h u‖²_{L²}` on the odd periodic grids. -/
theorem rootDirichlet_not_uniformly_coercive_interp :
    ∀ c : ℝ, 0 < c → ∃ m : ℕ, ∃ u : RootParityConnector.Grid (2 * m + 1) → ℂ,
      rootDirichlet (2 * m + 1) u < c * trigGradSq (interp u) := by
  intro c hc
  obtain ⟨m, u, hu⟩ := rootDirichlet_not_uniformly_coercive c hc
  refine ⟨m, u, hu.trans_le ?_⟩
  exact mul_le_mul_of_nonneg_left (coordDirichlet_equiv_interp u).2 hc.le

/-- The parity test: `𝒟_F(u_h) ≤ 12π²` while `‖∇𝓘_h u_h‖²_{L²} ≥ 6N²`. -/
theorem parityTest_gradient_ge (m : ℕ) (hm : 1 ≤ m) :
    rootDirichlet (2 * m + 1) (parityTest (2 * m + 1) m) ≤ 12 * π ^ 2 ∧
      6 * ((2 * m + 1 : ℕ) : ℝ) ^ 2 ≤ trigGradSq (interp (parityTest (2 * m + 1) m)) := by
  obtain ⟨h1, h2⟩ := root_parity_obstruction m hm
  exact ⟨h1, h2.trans (coordDirichlet_equiv_interp _).2⟩

/-- `eq:supp-open-connector-coercivity` transported to the interpolant gradient. -/
theorem connector_coercivity_interp (u : RootParityConnector.Grid N → ℂ) :
    (1 / 5 : ℝ) * ((2 / π) ^ 2 * trigGradSq (interp u)) ≤ connectorDirichlet N u ∧
      connectorDirichlet N u ≤ 9 * trigGradSq (interp u) := by
  obtain ⟨h1, h2⟩ := connector_coercivity N u
  obtain ⟨e1, e2⟩ := coordDirichlet_equiv_interp u
  constructor <;> linarith

end RenewalGeometry.RootParityInterpolant
