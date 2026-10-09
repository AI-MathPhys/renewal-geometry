/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactInitialPreparedJet

/-!
# The full right inverse at a prepared record (`eq:supp-initial-full-inverse`)

* `full_inverse_at`: at a record `I = ι x + R y(ι x)` over a free point `x`, if the reduced mean
  derivative along the balancing directions is `|t| η`-close to `t A` (`A` invertible), then
  `D𝒞(I) = L + DN(I)` has a bounded linear right inverse with the bordered bound of
  `NormalizedMeanRoot.bordered_right_inverse` (range block `O(1)`, mean block `O(|t|⁻¹)`); this
  combines `NormalizedMeanRoot.mean_block_bound` (the mean block of `DN(I)` is the reduced mean
  derivative up to `O(β²)`) with the bordered inverse.
-/

open Filter Finset Metric Set
open scoped Topology

noncomputable section

namespace RenewalGeometry.ExactPhaseAction.PreparedChart

set_option linter.unusedSectionVars false

open QuadJet PeriodicGridSobolev GridLocalOps InitialCalculus InitialRange PreparedSeed
open LyapunovSchmidt HessianRay IteratedDerivBounds UniformDerivBounds

variable {N : ℕ} [NeZero N] {r : ℕ}

theorem norm_iotaC_op_le (D : RD N r) {cι : ℝ} (hι : ∀ z, ‖iotaC D cι z‖ ≤ ‖z‖) :
    ‖iotaC D cι‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by rw [one_mul]; exact hι z

/-- The derivative of `z ↦ y(ι z)` exists at every free point with `‖ι x‖ < δ` (analytic
nonlinearity). -/
theorem hasFDerivAt_sol_iota (D : RD N r) {σ δ cι : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ)
    (hNa : ∀ x ∈ ball (0 : XH N r) D.ρ, AnalyticAt ℝ D.N x) {x : XH N r}
    (hx : ‖iotaC D cι x‖ < δ) :
    HasFDerivAt (fun z => D.sol σ δ (iotaC D cι z))
      (fderiv ℝ (fun z => D.sol σ δ (iotaC D cι z)) x) x := by
  have h := D.analyticAt_sol hNa hr (z0 := iotaK D cι x) hx
  have h2 : AnalyticAt ℝ (fun z => D.sol σ δ ((iotaK D cι z : D.K) : XH N r)) x :=
    h.comp ((iotaK D cι).analyticAt x)
  exact h2.differentiableAt.hasFDerivAt

/-- **The full right inverse at a record** (`eq:supp-initial-full-inverse`, abstract assembly). -/
theorem full_inverse_at (D : RD N r) {σ δ cι : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ)
    (hNa : ∀ x ∈ ball (0 : XH N r) D.ρ, AnalyticAt ℝ D.N x)
    (hP0P : ∀ w, D.P0 (D.P w) = 0) (hι : ∀ z, ‖iotaC D cι z‖ ≤ ‖z‖) {x : XH N r}
    (hx : ‖iotaC D cι x‖ < δ) {DΘx : XH N r →L[ℝ] (Fin 4 → ℝ)}
    (hΘx : HasFDerivAt (ThX D σ δ cι) DΘx x)
    (Zl : (ℝ × (Fin 3 → ℝ)) →L[ℝ] XH N r) {j : ℝ} (hZl : ‖Zl‖ ≤ j)
    {β : ℝ} (hβ : ‖D.DN (iotaC D cι x + D.R (D.sol σ δ (iotaC D cι x)))‖ ≤ β)
    (A : (ℝ × (Fin 3 → ℝ)) ≃L[ℝ] (Fin 4 → ℝ)) {M η t : ℝ}
    (hM : ‖(A.symm : (Fin 4 → ℝ) →L[ℝ] (ℝ × (Fin 3 → ℝ)))‖ ≤ M) (ht : t ≠ 0)
    (hblock : ‖DΘx ∘L Zl - t • (A : (ℝ × (Fin 3 → ℝ)) →L[ℝ] (Fin 4 → ℝ))‖ ≤ η * |t|)
    (hsmall : D.p * β * D.a ≤ 1 / 2)
    (hMε : M * (η + ‖D.P0‖ * β * D.a * (2 * D.p * β) * j / |t|) ≤ 1 / 2)
    (hq : D.p * β * D.a + D.p * β * j * (2 * M / |t|) * (‖D.P0‖ * β * D.a) ≤ 1 / 2) :
    ∃ S : (YH N r) →L[ℝ] XH N r,
      (∀ f, D.L (S f) + D.DN (iotaC D cι x + D.R (D.sol σ δ (iotaC D cι x))) (S f) = f) ∧
      ∀ f, ‖S f‖ ≤ D.a * (2 * (‖D.P f‖ + D.p * β * j * (2 * M / |t|) * ‖D.P0 f‖)) +
        j * (2 * M / |t| * (‖D.P0 f‖ + ‖D.P0‖ * β * D.a *
          (2 * (‖D.P f‖ + D.p * β * j * (2 * M / |t|) * ‖D.P0 f‖)))) := by
  set ι := iotaC D cι with hιdef
  set I := ι x + D.R (D.sol σ δ (ι x)) with hIdef
  have hι1 : ‖ι‖ ≤ 1 := norm_iotaC_op_le D hι
  have hDy := hasFDerivAt_sol_iota D hr hNa hx
  obtain ⟨-, hmb⟩ := NormalizedMeanRoot.mean_block_bound D hr ι (L_iotaC D cι) hι1 hx hDy
    (DΘ := DΘx) hΘx hβ hsmall
  have hat : 0 < |t| := abs_pos.mpr ht
  have hj0 : 0 ≤ j := (norm_nonneg _).trans hZl
  set J := ι ∘L Zl with hJdef
  have hJ : ‖J‖ ≤ j :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by nlinarith [norm_nonneg ι, norm_nonneg Zl])
  have hLJ : ∀ v, D.L (J v) = 0 := fun v => L_iotaC D cι (Zl v)
  have hE : ‖D.P0 ∘L D.DN I ∘L J - t • (A : (ℝ × (Fin 3 → ℝ)) →L[ℝ] (Fin 4 → ℝ))‖ ≤
      (η + ‖D.P0‖ * β * D.a * (2 * D.p * β) * j / |t|) * |t| := by
    have e : D.P0 ∘L D.DN I ∘L J - t • (A : (ℝ × (Fin 3 → ℝ)) →L[ℝ] (Fin 4 → ℝ)) =
        (D.P0 ∘L D.DN I ∘L ι - DΘx) ∘L Zl +
          (DΘx ∘L Zl - t • (A : (ℝ × (Fin 3 → ℝ)) →L[ℝ] (Fin 4 → ℝ))) := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [hJdef, add_apply, sub_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]
      abel
    rw [e]
    calc ‖(D.P0 ∘L D.DN I ∘L ι - DΘx) ∘L Zl +
          (DΘx ∘L Zl - t • (A : (ℝ × (Fin 3 → ℝ)) →L[ℝ] (Fin 4 → ℝ)))‖
        ≤ ‖D.P0 ∘L D.DN I ∘L ι - DΘx‖ * ‖Zl‖ + η * |t| :=
          (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) hblock)
      _ ≤ ‖D.P0‖ * β * D.a * (2 * D.p * β) * j + η * |t| :=
          add_le_add (mul_le_mul hmb hZl (norm_nonneg _) (by
            have := (norm_nonneg _).trans hβ
            have := D.a_nonneg; have := D.p_nonneg
            positivity)) le_rfl
      _ = (η + ‖D.P0‖ * β * D.a * (2 * D.p * β) * j / |t|) * |t| := by
          field_simp
          ring
  exact NormalizedMeanRoot.bordered_right_inverse D hP0P (D.DN I) hβ J hJ hLJ A hM ht hE hMε hq

end RenewalGeometry.ExactPhaseAction.PreparedChart
