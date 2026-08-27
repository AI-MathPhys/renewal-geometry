/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.YMNSHodgeShort

/-!
# Critical source-sheet and within-fibre Pythagoras

The NS.1 sheet projection together with the exact NS.2 split into weighted
router dispersion, phase quadrature, and zero-writer first births.
-/

open Finset
open scoped InnerProductSpace

namespace NCG
namespace NSSourceSheetFibrePythagorasExact

/-- Weighted line projection followed by weighted centering gives the exact
three-term within-fibre work-null split. -/
theorem within_fibre_workNull_split
    {K V : Type*} [Fintype K] [DecidableEq K]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (active : Finset K) (h v ζ : K → V) (r : K → ℝ) (rbar : ℝ)
    (hdecomp : ∀ k, k ∈ active → h k = r k • v k + ζ k)
    (horth : ∀ k, k ∈ active → ⟪v k, ζ k⟫_ℝ = 0)
    (hcenter : (∑ k, if k ∈ active then ‖v k‖ ^ 2 * (r k - rbar) else 0) = 0) :
    (∑ k, ‖h k‖ ^ 2) -
        (∑ k, if k ∈ active then ‖v k‖ ^ 2 else 0) * rbar ^ 2 =
      (∑ k, if k ∈ active then ‖v k‖ ^ 2 * (r k - rbar) ^ 2 else 0) +
      (∑ k, if k ∈ active then ‖ζ k‖ ^ 2 else 0) +
      ∑ k, if k ∉ active then ‖h k‖ ^ 2 else 0 := by
  have hpoint : ∀ k, k ∈ active →
      ‖h k‖ ^ 2 = (r k) ^ 2 * ‖v k‖ ^ 2 + ‖ζ k‖ ^ 2 := by
    intro k hv
    rw [hdecomp k hv]
    have ho : ⟪r k • v k, ζ k⟫_ℝ = 0 := by
      rw [real_inner_smul_left, horth k hv, mul_zero]
    have hp := norm_add_sq_eq_norm_sq_add_norm_sq_real ho
    rw [norm_smul, Real.norm_eq_abs] at hp
    nlinarith [sq_abs (r k)]
  have htotal : ∑ k, ‖h k‖ ^ 2 =
      (∑ k, if k ∈ active then (r k) ^ 2 * ‖v k‖ ^ 2 + ‖ζ k‖ ^ 2 else 0) +
      ∑ k, if k ∉ active then ‖h k‖ ^ 2 else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hv : k ∈ active
    · simp [hv, hpoint k hv]
    · simp [hv]
  rw [htotal]
  have hvariance :
      (∑ k, if k ∈ active then (r k) ^ 2 * ‖v k‖ ^ 2 else 0) -
          (∑ k, if k ∈ active then ‖v k‖ ^ 2 else 0) * rbar ^ 2 =
        ∑ k, if k ∈ active then ‖v k‖ ^ 2 * (r k - rbar) ^ 2 else 0 := by
    have hcenter' :
        (∑ k, if k ∈ active then ‖v k‖ ^ 2 * r k else 0) =
          rbar * (∑ k, if k ∈ active then ‖v k‖ ^ 2 else 0) := by
      apply sub_eq_zero.mp
      calc
        (∑ k, if k ∈ active then ‖v k‖ ^ 2 * r k else 0) -
              rbar * (∑ k, if k ∈ active then ‖v k‖ ^ 2 else 0) =
            ∑ k, if k ∈ active then ‖v k‖ ^ 2 * (r k - rbar) else 0 := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro k _
          by_cases hk : k ∈ active <;> simp [hk] <;> ring
        _ = 0 := hcenter
    have hexpand :
        (∑ k, if k ∈ active then ‖v k‖ ^ 2 * (r k - rbar) ^ 2 else 0) =
          (∑ k, if k ∈ active then (r k) ^ 2 * ‖v k‖ ^ 2 else 0) -
            2 * rbar * (∑ k, if k ∈ active then ‖v k‖ ^ 2 * r k else 0) +
            rbar ^ 2 * (∑ k, if k ∈ active then ‖v k‖ ^ 2 else 0) := by
      calc
        (∑ k, if k ∈ active then ‖v k‖ ^ 2 * (r k - rbar) ^ 2 else 0) =
            ∑ k, ((if k ∈ active then (r k) ^ 2 * ‖v k‖ ^ 2 else 0) -
              2 * rbar * (if k ∈ active then ‖v k‖ ^ 2 * r k else 0) +
              rbar ^ 2 * (if k ∈ active then ‖v k‖ ^ 2 else 0)) := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases hk : k ∈ active <;> simp [hk] <;> ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hexpand, hcenter']
    ring
  rw [show (∑ k, if k ∈ active then (r k) ^ 2 * ‖v k‖ ^ 2 + ‖ζ k‖ ^ 2 else 0) =
      (∑ k, if k ∈ active then (r k) ^ 2 * ‖v k‖ ^ 2 else 0) +
      ∑ k, if k ∈ active then ‖ζ k‖ ^ 2 else 0 by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hv : k ∈ active <;> simp [hv]]
  rw [← hvariance]
  ring

/-- The complete NS.1/NS.2 source-sheet packet. -/
theorem ns_source_sheet_pythagoras_complete
    {K V : Type*} [Fintype K] [DecidableEq K]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (vp vm residual g : V) (a b : ℝ)
    (hg : g = a • vp + b • vm + residual)
    (hpm : ⟪vp, vm⟫_ℝ = 0)
    (hpr : ⟪vp, residual⟫_ℝ = 0)
    (hmr : ⟪vm, residual⟫_ℝ = 0)
    (active : Finset K) (hf vf ζf : K → V) (rf : K → ℝ) (rbar : ℝ)
    (hdecomp : ∀ k, k ∈ active → hf k = rf k • vf k + ζf k)
    (horth : ∀ k, k ∈ active → ⟪vf k, ζf k⟫_ℝ = 0)
    (hcenter : (∑ k, if k ∈ active then
      ‖vf k‖ ^ 2 * (rf k - rbar) else 0) = 0) :
    (‖g‖ ^ 2 = a ^ 2 * ‖vp‖ ^ 2 + b ^ 2 * ‖vm‖ ^ 2 + ‖residual‖ ^ 2) ∧
    (⟪vp, g⟫_ℝ = a * ‖vp‖ ^ 2) ∧
    (⟪vm, g⟫_ℝ = b * ‖vm‖ ^ 2) ∧
    ((∑ k, ‖hf k‖ ^ 2) -
        (∑ k, if k ∈ active then ‖vf k‖ ^ 2 else 0) * rbar ^ 2 =
      (∑ k, if k ∈ active then ‖vf k‖ ^ 2 * (rf k - rbar) ^ 2 else 0) +
      (∑ k, if k ∈ active then ‖ζf k‖ ^ 2 else 0) +
      ∑ k, if k ∉ active then ‖hf k‖ ^ 2 else 0) := by
  obtain ⟨henergy, hplus, hminus⟩ :=
    ns_source_sheet_pythagoras vp vm residual g a b hg hpm hpr hmr
  exact ⟨henergy, hplus, hminus,
    within_fibre_workNull_split active hf vf ζf rf rbar hdecomp horth hcenter⟩

end NSSourceSheetFibrePythagorasExact
end NCG
