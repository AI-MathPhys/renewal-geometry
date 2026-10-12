/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import MathPhys.Variational.FiniteGibbsActionGap
import MathPhys.StatMech.FiniteKLPartitionChain
open MathPhys
/-!
# Four-term accepted/action information Pythagoras

This file develops the finite, strictly positive KL identities used by
`thm:accepted-four-term-Pythagoras`.  The two ingredients are the KL chain
rule along a finite terminal read and the barycentric projection identity for
the conditional mean row.  Their combination gives the four nonnegative
terms and the sharp simultaneous-vanishing criterion.
-/

open Finset

namespace RenewalGeometry
namespace AcceptedActionInformationPythagoras
open MathPhys.AcceptedActionInformationPythagoras

/-- Weighted barycentric projection of fine rows onto their conditional mean. -/
theorem finiteKL_barycentric_projection
    {Omega Theta U : Type*} [Fintype Omega] [Fintype Theta] [Fintype U]
    [DecidableEq Theta]
    (F : Omega → Theta) (mu : Omega → ℝ) (nu : Theta → ℝ)
    (kappa : Omega → U → ℝ) (bar q : Theta → U → ℝ)
    (_hmu : ∀ x, 0 < mu x) (_hnu : ∀ theta, 0 < nu theta)
    (hkappa : ∀ x u, 0 < kappa x u)
    (hbar : ∀ theta u, 0 < bar theta u)
    (hq : ∀ theta u, 0 < q theta u)
    (hbary : ∀ theta u,
      ∑ x ∈ (Finset.univ.filter fun x ↦ F x = theta),
        mu x * kappa x u = nu theta * bar theta u) :
    ∑ x, mu x * finiteKL (kappa x) (q (F x)) =
      ∑ x, mu x * finiteKL (kappa x) (bar (F x)) +
        ∑ theta, nu theta * finiteKL (bar theta) (q theta) := by
  have hlog (x : Omega) (u : U) :
      Real.log (kappa x u / q (F x) u) =
        Real.log (kappa x u / bar (F x) u) +
          Real.log (bar (F x) u / q (F x) u) := by
    rw [← Real.log_mul
      (div_ne_zero (ne_of_gt (hkappa x u)) (ne_of_gt (hbar _ u)))
      (div_ne_zero (ne_of_gt (hbar _ u)) (ne_of_gt (hq _ u)))]
    congr 1
    field_simp [ne_of_gt (hbar (F x) u), ne_of_gt (hq (F x) u)]
  unfold finiteKL
  calc
    ∑ x, mu x * ∑ u, kappa x u * Real.log (kappa x u / q (F x) u) =
        ∑ x, mu x * ∑ u, kappa x u * Real.log (kappa x u / bar (F x) u) +
          ∑ x, mu x * ∑ u, kappa x u * Real.log (bar (F x) u / q (F x) u) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro x _
            rw [← mul_add, ← Finset.sum_add_distrib]
            apply congrArg (mu x * ·)
            apply Finset.sum_congr rfl
            intro u _
            rw [hlog x u]
            ring
    _ = ∑ x, mu x * ∑ u, kappa x u * Real.log (kappa x u / bar (F x) u) +
          ∑ theta, nu theta * ∑ u, bar theta u * Real.log (bar theta u / q theta u) := by
      congr 1
      calc
        ∑ x, mu x * ∑ u, kappa x u * Real.log (bar (F x) u / q (F x) u) =
            ∑ u, ∑ x, mu x * kappa x u *
              Real.log (bar (F x) u / q (F x) u) := by
                simp_rw [Finset.mul_sum]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro u _
                apply Finset.sum_congr rfl
                intro x _
                ring
        _ = ∑ u, ∑ theta, nu theta * bar theta u *
              Real.log (bar theta u / q theta u) := by
          apply Finset.sum_congr rfl
          intro u _
          rw [← Finset.sum_fiberwise_of_maps_to
            (s := Finset.univ) (t := Finset.univ) (g := F)
            (fun _ _ ↦ Finset.mem_univ _)
            (fun x ↦ mu x * kappa x u *
              Real.log (bar (F x) u / q (F x) u))]
          apply Finset.sum_congr rfl
          intro theta _
          rw [← hbary theta u, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          have hFx : F x = theta := (Finset.mem_filter.mp hx).2
          rw [hFx]
        _ = ∑ theta, nu theta * ∑ u,
              bar theta u * Real.log (bar theta u / q theta u) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro theta _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          ring

/-- The exact four-term accepted/action decomposition.  `K x`, `B theta`, and
`Q theta` are the pushforward/conditional resolutions of the observed,
conditional-mean, and comparator rows along the same terminal read. -/
theorem accepted_action_four_term_pythagoras
    {Omega Theta U Z : Type*}
    [Fintype Omega] [Fintype Theta] [Fintype U] [Fintype Z]
    [DecidableEq Theta] [DecidableEq Z]
    (F : Omega → Theta) (C : U → Z)
    (mu : Omega → ℝ) (nu : Theta → ℝ)
    (kappa : Omega → U → ℝ) (bar q : Theta → U → ℝ)
    (K : ∀ x, PartitionedRow C (kappa x))
    (B : ∀ theta, PartitionedRow C (bar theta))
    (Q : ∀ theta, PartitionedRow C (q theta))
    (hmu : ∀ x, 0 < mu x) (hnu : ∀ theta, 0 < nu theta)
    (hkappa_sum : ∀ x, ∑ u, kappa x u = 1)
    (hbar_sum : ∀ theta, ∑ u, bar theta u = 1)
    (hq_sum : ∀ theta, ∑ u, q theta u = 1)
    (hbary : ∀ theta u,
      ∑ x ∈ (Finset.univ.filter fun x ↦ F x = theta),
        mu x * kappa x u = nu theta * bar theta u) :
    let lumped := ∑ x, mu x * finiteKL (K x).coarse (B (F x)).coarse
    let fieldHidden := ∑ x, mu x *
      ∑ z, (K x).coarse z *
        fibreKL C z ((K x).conditional z) ((B (F x)).conditional z)
    let actionCoarse := ∑ theta, nu theta *
      finiteKL (B theta).coarse (Q theta).coarse
    let actionHidden := ∑ theta, nu theta *
      ∑ z, (B theta).coarse z *
        fibreKL C z ((B theta).conditional z) ((Q theta).conditional z)
    let total := ∑ x, mu x * finiteKL (kappa x) (q (F x))
    total = lumped + fieldHidden + actionCoarse + actionHidden ∧
      0 ≤ lumped ∧ 0 ≤ fieldHidden ∧
      0 ≤ actionCoarse ∧ 0 ≤ actionHidden ∧
      ((lumped = 0 ∧ fieldHidden = 0 ∧
          actionCoarse = 0 ∧ actionHidden = 0) ↔
        ∀ x, kappa x = q (F x)) := by
  dsimp only
  have hprojection := finiteKL_barycentric_projection F mu nu kappa bar q
    hmu hnu (fun x u ↦ (K x).row_pos u)
    (fun theta u ↦ (B theta).row_pos u)
    (fun theta u ↦ (Q theta).row_pos u) hbary
  have hK (x : Omega) := finiteKL_partition_chain C (kappa x) (bar (F x))
    (K x) (B (F x))
  have hB (theta : Theta) := finiteKL_partition_chain C (bar theta) (q theta)
    (B theta) (Q theta)
  have hdecomp :
      ∑ x, mu x * finiteKL (kappa x) (q (F x)) =
        (∑ x, mu x * finiteKL (K x).coarse (B (F x)).coarse) +
        (∑ x, mu x * ∑ z, (K x).coarse z *
          fibreKL C z ((K x).conditional z) ((B (F x)).conditional z)) +
        (∑ theta, nu theta * finiteKL (B theta).coarse (Q theta).coarse) +
        (∑ theta, nu theta * ∑ z, (B theta).coarse z *
          fibreKL C z ((B theta).conditional z) ((Q theta).conditional z)) := by
    rw [hprojection]
    simp_rw [hK, hB, mul_add, Finset.sum_add_distrib]
    ring
  have hKcoarse_sum (x : Omega) :=
    (K x).coarse_sum_one C (kappa x) (hkappa_sum x)
  have hBcoarse_sum (theta : Theta) :=
    (B theta).coarse_sum_one C (bar theta) (hbar_sum theta)
  have hQcoarse_sum (theta : Theta) :=
    (Q theta).coarse_sum_one C (q theta) (hq_sum theta)
  have hlump_nonneg : 0 ≤ ∑ x, mu x * finiteKL (K x).coarse (B (F x)).coarse := by
    apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg (le_of_lt (hmu x))
      (finiteKL_nonneg_eq_iff _ _ (K x).coarse_pos (B (F x)).coarse_pos
        (hKcoarse_sum x) (hBcoarse_sum (F x))).1
  have hfield_nonneg : 0 ≤ ∑ x, mu x *
      ∑ z, (K x).coarse z *
        fibreKL C z ((K x).conditional z) ((B (F x)).conditional z) := by
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg (le_of_lt (hmu x))
    apply Finset.sum_nonneg
    intro z _
    apply mul_nonneg (le_of_lt ((K x).coarse_pos z))
    exact fibreKL_nonneg C (kappa x) (bar (F x)) (K x) (B (F x)) z
  have haction_coarse_nonneg : 0 ≤ ∑ theta, nu theta *
      finiteKL (B theta).coarse (Q theta).coarse := by
    apply Finset.sum_nonneg
    intro theta _
    exact mul_nonneg (le_of_lt (hnu theta))
      (finiteKL_nonneg_eq_iff _ _ (B theta).coarse_pos (Q theta).coarse_pos
        (hBcoarse_sum theta) (hQcoarse_sum theta)).1
  have haction_hidden_nonneg : 0 ≤ ∑ theta, nu theta *
      ∑ z, (B theta).coarse z *
        fibreKL C z ((B theta).conditional z) ((Q theta).conditional z) := by
    apply Finset.sum_nonneg
    intro theta _
    apply mul_nonneg (le_of_lt (hnu theta))
    apply Finset.sum_nonneg
    intro z _
    apply mul_nonneg (le_of_lt ((B theta).coarse_pos z))
    exact fibreKL_nonneg C (bar theta) (q theta) (B theta) (Q theta) z
  have htotal_term : ∀ x ∈ (Finset.univ : Finset Omega),
      0 ≤ mu x * finiteKL (kappa x) (q (F x)) := by
    intro x _
    exact mul_nonneg (le_of_lt (hmu x))
      (finiteKL_nonneg_eq_iff _ _ (K x).row_pos (Q (F x)).row_pos
        (hkappa_sum x) (hq_sum (F x))).1
  have htotal_zero_iff :
      (∑ x, mu x * finiteKL (kappa x) (q (F x)) = 0) ↔
        ∀ x, kappa x = q (F x) := by
    constructor
    · intro hzero x
      have hall := (Finset.sum_eq_zero_iff_of_nonneg htotal_term).mp hzero
      have hproduct := hall x (Finset.mem_univ x)
      have hkl : finiteKL (kappa x) (q (F x)) = 0 :=
        (mul_eq_zero.mp hproduct).resolve_left (ne_of_gt (hmu x))
      exact (finiteKL_nonneg_eq_iff _ _ (K x).row_pos (Q (F x)).row_pos
        (hkappa_sum x) (hq_sum (F x))).2.mp hkl
    · intro hrows
      apply Finset.sum_eq_zero
      intro x _
      rw [hrows x]
      simp [finiteKL, ne_of_gt ((Q (F x)).row_pos _)]
  refine ⟨hdecomp, hlump_nonneg, hfield_nonneg,
    haction_coarse_nonneg, haction_hidden_nonneg, ?_⟩
  constructor
  · rintro ⟨hlump, hfield, hactionCoarse, hactionHidden⟩
    apply htotal_zero_iff.mp
    rw [hdecomp, hlump, hfield, hactionCoarse, hactionHidden]
    ring
  · intro hrows
    have htotal := htotal_zero_iff.mpr hrows
    have hsum :
        (∑ x, mu x * finiteKL (K x).coarse (B (F x)).coarse) +
        (∑ x, mu x * ∑ z, (K x).coarse z *
          fibreKL C z ((K x).conditional z) ((B (F x)).conditional z)) +
        (∑ theta, nu theta * finiteKL (B theta).coarse (Q theta).coarse) +
        (∑ theta, nu theta * ∑ z, (B theta).coarse z *
          fibreKL C z ((B theta).conditional z) ((Q theta).conditional z)) = 0 := by
      rw [← hdecomp]
      exact htotal
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith

end AcceptedActionInformationPythagoras
end RenewalGeometry
