/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CollectivelyCompactStrongToNorm

/-!
# Compact limits of collectively compact families

This file closes the compact-limit step in the collectively compact convergence theorem.  A
pointwise strong limit of a collectively compact family is compact, so compactness of the limit
does not have to be assumed separately in the strong-to-operator-norm upgrade.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]

/-- A pointwise strong limit of a collectively compact family is a compact operator. -/
theorem CollectivelyCompact.isCompactOperator_limit
    (T : ℕ → H →L[K] H) (Tlim : H →L[K] H)
    (hcompact : (constantSystem K H).CollectivelyCompact T)
    (hstrong : ∀ x : H, Tendsto (fun n ↦ T n x) atTop (𝓝 (Tlim x))) :
    IsCompactOperator Tlim := by
  obtain ⟨C, hC, hsub⟩ := hcompact
  have himage : Tlim '' Metric.closedBall (0 : H) 1 ⊆ C := by
    rintro y ⟨x, hx, rfl⟩
    apply hC.isClosed.mem_of_tendsto (hstrong x)
    filter_upwards [] with n
    exact hsub n ⟨x, hx, by simp [embeddedOperator, constantSystem]⟩
  have hlinear : IsCompactOperator Tlim.toLinearMap := by
    apply (isCompactOperator_iff_image_closedBall_subset_compact
      Tlim.toLinearMap zero_lt_one).2
    exact ⟨C, hC, himage⟩
  simpa using hlinear

/-- Collective compactness and symmetric strong convergence imply operator-norm convergence;
compactness of the limit is obtained automatically from the preceding theorem. -/
theorem tendsto_operatorNorm_of_collectivelyCompact_of_symmetric'
    (T : ℕ → H →L[K] H) (Tlim : H →L[K] H)
    (hcompact : (constantSystem K H).CollectivelyCompact T)
    (hsymm : ∀ n, LinearMap.IsSymmetric (T n).toLinearMap)
    (hlim_symm : LinearMap.IsSymmetric Tlim.toLinearMap)
    (hstrong : ∀ y : H, Tendsto (fun n ↦ T n y) atTop (𝓝 (Tlim y))) :
    Tendsto T atTop (𝓝 Tlim) := by
  exact tendsto_operatorNorm_of_collectivelyCompact_of_symmetric
    T Tlim hcompact (hcompact.isCompactOperator_limit T Tlim hstrong)
      hsymm hlim_symm hstrong

end NCG.VaryingHilbert.System
