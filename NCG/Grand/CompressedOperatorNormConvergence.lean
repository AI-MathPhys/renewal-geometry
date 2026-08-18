/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCompressedOperators
import NCG.Grand.CollectivelyCompactLimit

/-!
# Operator-norm convergence of compressed varying-space operators

Collective compactness of a varying-space family passes to its literal common-carrier
compressions.  For symmetric operators, asymptotic density and varying-space strong convergence
then upgrade to operator-norm convergence of `Jₙ Tₙ Jₙ†`.
-/

open Filter Topology
open scoped InnerProduct

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- The adjoint of an isometric stage embedding is contractive. -/
theorem norm_adjointLift_le (n : ℕ) (x : H) :
    ‖J.adjointLift n x‖ ≤ ‖x‖ := by
  let e : Hn n →L[K] H := (J.embedding n).toContinuousLinearMap
  have he : ‖e‖ ≤ 1 := by
    apply e.opNorm_le_bound zero_le_one
    intro y
    simp [e]
  calc
    ‖J.adjointLift n x‖ ≤ ‖e†‖ * ‖x‖ := by
      simpa [adjointLift, e] using (e†).le_opNorm x
    _ = ‖e‖ * ‖x‖ := by simp
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right he (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-- Collective compactness of a varying-space family implies collective compactness of the
common-carrier compressions. -/
theorem CollectivelyCompact.compressedOperator
    (Tn : ∀ n, Hn n →L[K] Hn n)
    (hcompact : J.CollectivelyCompact Tn) :
    (constantSystem K H).CollectivelyCompact (J.compressedOperator Tn) := by
  obtain ⟨C, hC, hTC⟩ := hcompact
  refine ⟨C, hC, ?_⟩
  intro n y hy
  obtain ⟨x, hx, rfl⟩ := hy
  apply hTC n
  refine ⟨J.adjointLift n x, ?_, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using
      (J.norm_adjointLift_le n x).trans (by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
  · rfl

/-- Compression by an isometric embedding preserves symmetry. -/
theorem compressedOperator_isSymmetric
    (Tn : ∀ n, Hn n →L[K] Hn n)
    (hsymm : ∀ n, LinearMap.IsSymmetric (Tn n).toLinearMap) (n : ℕ) :
    LinearMap.IsSymmetric (J.compressedOperator Tn n).toLinearMap := by
  rw [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  simp only [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint,
    compressedOperator, adjointLift, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    hsymm n |>.clm_adjoint_eq]
  rw [ContinuousLinearMap.comp_assoc]

/-- Collectively compact symmetric varying-space strong convergence upgrades to literal
operator-norm convergence of the common-carrier compressions `Jₙ Tₙ Jₙ†`. -/
theorem compressedOperator_tendsto_operatorNorm
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hsymm : ∀ n, LinearMap.IsSymmetric (Tn n).toLinearMap)
    (hlimSymm : LinearMap.IsSymmetric T.toLinearMap) :
    Tendsto (J.compressedOperator Tn) atTop (nhds T) := by
  exact tendsto_operatorNorm_of_collectivelyCompact_of_symmetric'
    (J.compressedOperator Tn) T
    (hcompact.compressedOperator J Tn)
    (J.compressedOperator_isSymmetric Tn hsymm) hlimSymm
    (J.compressedOperator_tendsto Tn T hdense hstrong)

end NCG.VaryingHilbert.System
