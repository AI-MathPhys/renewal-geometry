/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TetrahedralK4OperatorGap

/-!
# Tetrahedral gap directly from triangle-holonomy bounds

This derives the three non-tree energy estimates from the actual holonomy
closeness bounds, then invokes the six-edge operator theorem.  It closes the
last interface in `thm:tetrahedral-prototype-gap`.
-/

open Finset
open scoped InnerProductSpace

namespace NCG

section

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- A metric-preserving router within `delta` of the identity changes one
edge energy by at most the manuscript's `M delta` endpoint error. -/
theorem router_energy_le_of_pointwise_holonomy
    (S : V →L[ℝ] W) (U : V ≃ₗᵢ[ℝ] V) (x y : V) (M δ : ℝ)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hSnorm : ‖S‖ ^ 2 ≤ M)
    (hmetric : ∀ z, ‖S (U z)‖ = ‖S z‖)
    (hclose : ∀ z, ‖U z - z‖ ≤ δ * ‖z‖) :
    ‖S (y - x)‖ ^ 2 ≤
      ‖S (y - U x)‖ ^ 2 + M * δ * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hSy : ‖S y‖ ≤ ‖S‖ * ‖y‖ := S.le_opNorm y
  have hSd : ‖S (U x - x)‖ ≤ ‖S‖ * ‖U x - x‖ := S.le_opNorm (U x - x)
  have hprod : ‖S y‖ * ‖S (U x - x)‖ ≤
      M * δ * ‖y‖ * ‖x‖ := by
    calc
      ‖S y‖ * ‖S (U x - x)‖ ≤
          (‖S‖ * ‖y‖) * (‖S‖ * ‖U x - x‖) :=
        mul_le_mul hSy hSd (norm_nonneg _) (mul_nonneg (norm_nonneg S) (norm_nonneg y))
      _ = ‖S‖ ^ 2 * (‖y‖ * ‖U x - x‖) := by ring
      _ ≤ M * (‖y‖ * ‖U x - x‖) :=
        mul_le_mul_of_nonneg_right hSnorm
          (mul_nonneg (norm_nonneg y) (norm_nonneg _))
      _ ≤ M * (‖y‖ * (δ * ‖x‖)) := by
        apply mul_le_mul_of_nonneg_left _ hM
        exact mul_le_mul_of_nonneg_left (hclose x) (norm_nonneg y)
      _ = M * δ * ‖y‖ * ‖x‖ := by ring
  have htwo :
      2 * (M * δ * ‖y‖ * ‖x‖) ≤
        M * δ * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    have hxy : 2 * ‖y‖ * ‖x‖ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
    nlinarith [mul_nonneg hM hδ]
  have hinner :
      2 * ⟪S y, S (U x - x)⟫_ℝ ≤
        M * δ * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    have habs := abs_real_inner_le_norm (S y) (S (U x - x))
    have hone : ⟪S y, S (U x - x)⟫_ℝ ≤
        M * δ * ‖y‖ * ‖x‖ :=
      (le_abs_self _).trans (habs.trans hprod)
    linarith
  rw [map_sub, map_sub, norm_sub_sq_real, norm_sub_sq_real]
  rw [hmetric x]
  have hlin :
      ⟪S y, S (U x)⟫_ℝ - ⟪S y, S x⟫_ℝ =
        ⟪S y, S (U x - x)⟫_ℝ := by
    rw [map_sub, inner_sub_right]
  linarith

/-- The complete tetrahedral lower bound with the three non-tree hypotheses
derived from pointwise triangle-holonomy closeness. -/
theorem tetrahedralK4_operatorGap_of_holonomy
    (S : V →L[ℝ] W) (U : Fin 6 → V ≃ₗᵢ[ℝ] V)
    (E : Fin 6 → V →L[ℝ] V) (f : Fin 4 → V)
    (m M δ ε : ℝ)
    (hsum : f 0 + f 1 + f 2 + f 3 = 0)
    (hm : ∀ x, m * ‖x‖ ^ 2 ≤ ‖S x‖ ^ 2)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hSnorm : ‖S‖ ^ 2 ≤ M)
    (htree0 : U 0 = LinearIsometryEquiv.refl ℝ V)
    (htree1 : U 1 = LinearIsometryEquiv.refl ℝ V)
    (htree2 : U 2 = LinearIsometryEquiv.refl ℝ V)
    (hmetric : ∀ e x, ‖S (U e x)‖ = ‖S x‖)
    (hclose3 : ∀ x, ‖U 3 x - x‖ ≤ δ * ‖x‖)
    (hclose4 : ∀ x, ‖U 4 x - x‖ ≤ δ * ‖x‖)
    (hclose5 : ∀ x, ‖U 5 x - x‖ ≤ δ * ‖x‖)
    (hE : ∀ e, ‖E e‖ ≤ ε) :
    (4 * m - 2 * M * δ - 6 * ε) * (∑ i : Fin 4, ‖f i‖ ^ 2) ≤
      k4ActualRouterEnergy S U E f := by
  apply tetrahedralK4_operatorGap S U E f m M δ ε hsum hm hM hδ hε
    htree0 htree1 htree2
  · exact router_energy_le_of_pointwise_holonomy S (U 3) (f 1) (f 2)
      M δ hM hδ hSnorm (hmetric 3) hclose3
  · exact router_energy_le_of_pointwise_holonomy S (U 4) (f 1) (f 3)
      M δ hM hδ hSnorm (hmetric 4) hclose4
  · exact router_energy_le_of_pointwise_holonomy S (U 5) (f 2) (f 3)
      M δ hM hδ hSnorm (hmetric 5) hclose5
  · exact hE

end

end NCG
