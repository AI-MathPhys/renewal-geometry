/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphNormCarrier
import NCG.Grand.ENNRealOperatorGraphEnergy

/-!
# Graph-norm carriers and extended operator energies

The graph carrier's inherited Hilbert norm is identified exactly with the
manuscript-style extended graph energy.  In particular, its closed unit ball
is the effective-domain energy ball
`‖u‖² + q(u) ≤ 1`.
-/

open Set
open scoped ENNReal

noncomputable section

namespace NCG.VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F]

/-- The graph-carrier squared norm is ambient squared norm plus the finite
part of the extended operator graph energy. -/
theorem operatorGraphNormVector_norm_sq_eq_ennrealGraphEnergy
    (D : Submodule K E) (A : D →ₗ[K] F) (x : D) :
    ‖operatorGraphNormVector D A x‖ ^ 2 =
      ‖(x : E)‖ ^ 2 +
        (ennrealOperatorGraphEnergy D A (x : E)).toReal := by
  rw [operatorGraphNormVector_norm_sq,
    ennrealOperatorGraphEnergy_toReal D A (x : E) x.property]

/-- Membership in the carrier unit ball is exactly the manuscript's
quadratic graph-energy bound. -/
theorem operatorGraphNormVector_mem_closedBall_iff_ennrealGraphEnergy
    (D : Submodule K E) (A : D →ₗ[K] F) (x : D) :
    operatorGraphNormVector D A x ∈ Metric.closedBall 0 1 ↔
      ‖(x : E)‖ ^ 2 +
        (ennrealOperatorGraphEnergy D A (x : E)).toReal ≤ 1 := by
  rw [Metric.mem_closedBall, dist_zero_right,
    operatorGraphNormVector_norm_le_one_iff,
    ennrealOperatorGraphEnergy_toReal D A (x : E) x.property]

/-- Every vector in the graph-carrier unit ball comes from an effective-domain
vector satisfying the exact extended graph-energy inequality. -/
theorem operatorGraphNormCarrier_unitBall_exists_energyBound
    (D : Submodule K E) (A : D →ₗ[K] F)
    (u : operatorGraphNormCarrier D A)
    (hu : u ∈ Metric.closedBall 0 1) :
    ∃ x : D, u = operatorGraphNormVector D A x ∧
      ‖(x : E)‖ ^ 2 +
        (ennrealOperatorGraphEnergy D A (x : E)).toReal ≤ 1 := by
  obtain ⟨x, hx⟩ := u.property
  have hux : u = operatorGraphNormVector D A x := by
    apply Subtype.ext
    exact hx.symm
  refine ⟨x, hux, ?_⟩
  exact (operatorGraphNormVector_mem_closedBall_iff_ennrealGraphEnergy
    D A x).mp (hux ▸ hu)

/-- Conversely, every effective-domain vector satisfying the manuscript's
graph-energy bound defines a vector in the graph-carrier unit ball. -/
theorem operatorGraphNormVector_mem_unitBall_of_energyBound
    (D : Submodule K E) (A : D →ₗ[K] F) (x : D)
    (hx : ‖(x : E)‖ ^ 2 +
      (ennrealOperatorGraphEnergy D A (x : E)).toReal ≤ 1) :
    operatorGraphNormVector D A x ∈ Metric.closedBall 0 1 :=
  (operatorGraphNormVector_mem_closedBall_iff_ennrealGraphEnergy D A x).2 hx

end NCG.VaryingHilbert
