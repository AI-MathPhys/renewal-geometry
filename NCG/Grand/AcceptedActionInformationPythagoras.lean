/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteGibbsActionGap

/-!
# Four-term accepted/action information Pythagoras

This file develops the finite, strictly positive KL identities used by
`thm:accepted-four-term-Pythagoras`.  The two ingredients are the KL chain
rule along a finite terminal read and the barycentric projection identity for
the conditional mean row.  Their combination gives the four nonnegative
terms and the sharp simultaneous-vanishing criterion.
-/

open Finset

namespace NCG
namespace AcceptedActionInformationPythagoras

/-- Gibbs' inequality and its equality case when the first probability row
may have zero entries but the reference row is faithful. -/
theorem finiteKL_nonneg_eq_iff_of_nonnegative
    {Y : Type*} [Fintype Y] (q p : Y → ℝ)
    (hq : ∀ y, 0 ≤ q y) (hp : ∀ y, 0 < p y)
    (hqsum : ∑ y, q y = 1) (hpsum : ∑ y, p y = 1) :
    0 ≤ finiteKL q p ∧ (finiteKL q p = 0 ↔ q = p) := by
  have hrewrite := finiteKL_eq_sum_klFun q p hp hqsum hpsum
  have hterm : ∀ y ∈ Finset.univ,
      0 ≤ p y * InformationTheory.klFun (q y / p y) := by
    intro y _
    exact mul_nonneg (le_of_lt (hp y))
      (InformationTheory.klFun_nonneg (div_nonneg (hq y) (le_of_lt (hp y))))
  constructor
  · rw [hrewrite]
    exact Finset.sum_nonneg hterm
  · constructor
    · intro hzero
      apply funext
      intro y
      have hall : ∀ z ∈ Finset.univ,
          p z * InformationTheory.klFun (q z / p z) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hterm).mp (hrewrite ▸ hzero)
      have hkl : InformationTheory.klFun (q y / p y) = 0 := by
        exact (mul_eq_zero.mp (hall y (Finset.mem_univ y))).resolve_left
          (ne_of_gt (hp y))
      have hratio : q y / p y = 1 :=
        (InformationTheory.klFun_eq_zero_iff
          (div_nonneg (hq y) (le_of_lt (hp y)))).mp hkl
      exact (div_eq_one_iff_eq (ne_of_gt (hp y))).mp hratio
    · intro h
      subst q
      unfold finiteKL
      simp [ne_of_gt (hp _)]

/-- KL divergence restricted to one fibre of a finite read. -/
noncomputable def fibreKL {U Z : Type*} [Fintype U] [DecidableEq Z]
    (C : U → Z) (z : Z) (r s : U → ℝ) : ℝ :=
  ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
    r u * Real.log (r u / s u)

/-- A strictly positive row resolved into its pushforward and normalized
conditional rows along `C`. -/
structure PartitionedRow {U Z : Type*} [Fintype U] [Fintype Z]
    [DecidableEq Z] (C : U → Z) (row : U → ℝ) where
  coarse : Z → ℝ
  conditional : Z → U → ℝ
  row_pos : ∀ u, 0 < row u
  coarse_pos : ∀ z, 0 < coarse z
  conditional_pos : ∀ z u, C u = z → 0 < conditional z u
  factor : ∀ u, row u = coarse (C u) * conditional (C u) u
  conditional_sum : ∀ z,
    ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z), conditional z u = 1

/-- Pushforward of a finite row through a terminal read. -/
noncomputable def pushforwardRow {U Z : Type*} [Fintype U] [DecidableEq Z]
    (C : U → Z) (row : U → ℝ) (z : Z) : ℝ :=
  ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z), row u

theorem pushforwardRow_pos
    {U Z : Type*} [Fintype U] [DecidableEq Z]
    (C : U → Z) (row : U → ℝ)
    (hC : Function.Surjective C) (hrow : ∀ u, 0 < row u) (z : Z) :
    0 < pushforwardRow C row z := by
  obtain ⟨u, rfl⟩ := hC z
  unfold pushforwardRow
  exact Finset.sum_pos (fun v _ ↦ hrow v)
    ⟨u, by simp⟩

/-- Conditional row inside one fibre of a terminal read. -/
noncomputable def conditionalRow {U Z : Type*} [Fintype U] [DecidableEq Z]
    (C : U → Z) (row : U → ℝ) (z : Z) (u : U) : ℝ :=
  row u / pushforwardRow C row z

/-- Every strictly positive finite row has its canonical pushforward and
conditional resolution along a surjective terminal read. -/
noncomputable def canonicalPartitionedRow
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (row : U → ℝ)
    (hC : Function.Surjective C) (hrow : ∀ u, 0 < row u) :
    PartitionedRow C row where
  coarse := pushforwardRow C row
  conditional := conditionalRow C row
  row_pos := hrow
  coarse_pos := pushforwardRow_pos C row hC hrow
  conditional_pos := by
    intro z u _
    exact div_pos (hrow u) (pushforwardRow_pos C row hC hrow z)
  factor := by
    intro u
    unfold conditionalRow
    field_simp [ne_of_gt (pushforwardRow_pos C row hC hrow (C u))]
  conditional_sum := by
    intro z
    unfold conditionalRow pushforwardRow
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (pushforwardRow_pos C row hC hrow z))

/-- The coarse component in any valid partitioned row is necessarily the
literal pushforward through the read. -/
theorem PartitionedRow.coarse_eq_pushforward
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (row : U → ℝ) (R : PartitionedRow C row) (z : Z) :
    R.coarse z = pushforwardRow C row z := by
  unfold pushforwardRow
  calc
    R.coarse z = R.coarse z *
        ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
          R.conditional z u := by rw [R.conditional_sum z, mul_one]
    _ = ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
          R.coarse z * R.conditional z u := by rw [Finset.mul_sum]
    _ = ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z), row u := by
      apply Finset.sum_congr rfl
      intro u hu
      have hCu : C u = z := (Finset.mem_filter.mp hu).2
      rw [R.factor u, hCu]

/-- The coarse row of a partitioned probability row is again normalized. -/
theorem PartitionedRow.coarse_sum_one
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (row : U → ℝ) (R : PartitionedRow C row)
    (hrow : ∑ u, row u = 1) :
    ∑ z, R.coarse z = 1 := by
  rw [← hrow]
  calc
    ∑ z, R.coarse z =
        ∑ z, ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
          R.coarse z * R.conditional z u := by
            apply Finset.sum_congr rfl
            intro z _
            rw [← Finset.mul_sum, R.conditional_sum z, mul_one]
    _ = ∑ u, row u := by
      calc
        ∑ z, ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
            R.coarse z * R.conditional z u =
            ∑ z, ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
              R.coarse (C u) * R.conditional (C u) u := by
                apply Finset.sum_congr rfl
                intro z _
                apply Finset.sum_congr rfl
                intro u hu
                rw [(Finset.mem_filter.mp hu).2]
        _ = ∑ u, R.coarse (C u) * R.conditional (C u) u :=
          Finset.sum_fiberwise_of_maps_to
            (s := Finset.univ) (t := Finset.univ) (g := C)
            (fun _ _ ↦ Finset.mem_univ _)
            (fun u ↦ R.coarse (C u) * R.conditional (C u) u)
        _ = ∑ u, row u := by
          apply Finset.sum_congr rfl
          intro u _
          rw [R.factor u]

/-- Finite KL chain rule along a terminal read. -/
theorem finiteKL_partition_chain
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (r s : U → ℝ)
    (R : PartitionedRow C r) (S : PartitionedRow C s) :
    finiteKL r s = finiteKL R.coarse S.coarse +
      ∑ z, R.coarse z * fibreKL C z (R.conditional z) (S.conditional z) := by
  have hlog (u : U) :
      Real.log (r u / s u) =
        Real.log (R.coarse (C u) / S.coarse (C u)) +
          Real.log (R.conditional (C u) u / S.conditional (C u) u) := by
    rw [R.factor u, S.factor u, mul_div_mul_comm,
      Real.log_mul
        (div_ne_zero (ne_of_gt (R.coarse_pos _)) (ne_of_gt (S.coarse_pos _)))
        (div_ne_zero
          (ne_of_gt (R.conditional_pos _ _ rfl))
          (ne_of_gt (S.conditional_pos _ _ rfl)))]
  unfold fibreKL finiteKL
  calc
    ∑ u, r u * Real.log (r u / s u) =
        ∑ u, r u * Real.log (R.coarse (C u) / S.coarse (C u)) +
          ∑ u, r u *
            Real.log (R.conditional (C u) u / S.conditional (C u) u) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro u _
              rw [hlog u]
              ring
    _ = ∑ z, R.coarse z * Real.log (R.coarse z / S.coarse z) +
          ∑ z, R.coarse z *
            ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
              R.conditional z u *
                Real.log (R.conditional z u / S.conditional z u) := by
      congr 1
      · rw [← Finset.sum_fiberwise_of_maps_to
          (s := Finset.univ) (t := Finset.univ) (g := C)
          (fun _ _ ↦ Finset.mem_univ _)
          (fun u ↦ r u * Real.log (R.coarse (C u) / S.coarse (C u)))]
        apply Finset.sum_congr rfl
        intro z _
        calc
          ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
              r u * Real.log (R.coarse (C u) / S.coarse (C u)) =
              ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
                (R.coarse z * Real.log (R.coarse z / S.coarse z)) *
                  R.conditional z u := by
                    apply Finset.sum_congr rfl
                    intro u hu
                    have hCu : C u = z := (Finset.mem_filter.mp hu).2
                    rw [R.factor u, hCu]
                    ring
          _ = (R.coarse z * Real.log (R.coarse z / S.coarse z)) *
              ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
                R.conditional z u := by rw [Finset.mul_sum]
          _ = R.coarse z * Real.log (R.coarse z / S.coarse z) := by
            rw [R.conditional_sum z, mul_one]
      · rw [← Finset.sum_fiberwise_of_maps_to
          (s := Finset.univ) (t := Finset.univ) (g := C)
          (fun _ _ ↦ Finset.mem_univ _)
          (fun u ↦ r u * Real.log
            (R.conditional (C u) u / S.conditional (C u) u))]
        apply Finset.sum_congr rfl
        intro z _
        calc
          ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
              r u * Real.log
                (R.conditional (C u) u / S.conditional (C u) u) =
              ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
                R.coarse z * (R.conditional z u *
                  Real.log (R.conditional z u / S.conditional z u)) := by
                    apply Finset.sum_congr rfl
                    intro u hu
                    have hCu : C u = z := (Finset.mem_filter.mp hu).2
                    rw [R.factor u, hCu]
                    ring
          _ = R.coarse z *
              ∑ u ∈ (Finset.univ.filter fun u ↦ C u = z),
                R.conditional z u *
                  Real.log (R.conditional z u / S.conditional z u) := by
            rw [Finset.mul_sum]

/-- Fibrewise Gibbs inequality for two partitioned rows. -/
theorem fibreKL_nonneg
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (r s : U → ℝ)
    (R : PartitionedRow C r) (S : PartitionedRow C s) (z : Z) :
    0 ≤ fibreKL C z (R.conditional z) (S.conditional z) := by
  let r' : {u // C u = z} → ℝ := fun u ↦ R.conditional z u
  let s' : {u // C u = z} → ℝ := fun u ↦ S.conditional z u
  have hrpos : ∀ u, 0 < r' u := fun u ↦
    R.conditional_pos z u u.property
  have hspos : ∀ u, 0 < s' u := fun u ↦
    S.conditional_pos z u u.property
  have hrsum : ∑ u, r' u = 1 := by
    rw [← Finset.sum_subtype
      (p := fun u ↦ C u = z)
      (Finset.univ.filter fun u ↦ C u = z) (by simp) (R.conditional z)]
    exact R.conditional_sum z
  have hssum : ∑ u, s' u = 1 := by
    rw [← Finset.sum_subtype
      (p := fun u ↦ C u = z)
      (Finset.univ.filter fun u ↦ C u = z) (by simp) (S.conditional z)]
    exact S.conditional_sum z
  have hnonneg := (finiteKL_nonneg_eq_iff r' s' hrpos hspos hrsum hssum).1
  unfold fibreKL
  rw [Finset.sum_subtype
    (p := fun u ↦ C u = z)
    (Finset.univ.filter fun u ↦ C u = z) (by simp)
      (fun u ↦ R.conditional z u *
        Real.log (R.conditional z u / S.conditional z u))]
  exact hnonneg

/-- Sharp equality case of the fibrewise Gibbs inequality. -/
theorem fibreKL_eq_zero_iff
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq Z]
    (C : U → Z) (r s : U → ℝ)
    (R : PartitionedRow C r) (S : PartitionedRow C s) (z : Z) :
    fibreKL C z (R.conditional z) (S.conditional z) = 0 ↔
      (fun u : {u // C u = z} ↦ R.conditional z u) =
        (fun u : {u // C u = z} ↦ S.conditional z u) := by
  let r' : {u // C u = z} → ℝ := fun u ↦ R.conditional z u
  let s' : {u // C u = z} → ℝ := fun u ↦ S.conditional z u
  have hrpos : ∀ u, 0 < r' u := fun u ↦
    R.conditional_pos z u u.property
  have hspos : ∀ u, 0 < s' u := fun u ↦
    S.conditional_pos z u u.property
  have hrsum : ∑ u, r' u = 1 := by
    rw [← Finset.sum_subtype
      (p := fun u ↦ C u = z)
      (Finset.univ.filter fun u ↦ C u = z) (by simp) (R.conditional z)]
    exact R.conditional_sum z
  have hssum : ∑ u, s' u = 1 := by
    rw [← Finset.sum_subtype
      (p := fun u ↦ C u = z)
      (Finset.univ.filter fun u ↦ C u = z) (by simp) (S.conditional z)]
    exact S.conditional_sum z
  have hfinite := (finiteKL_nonneg_eq_iff r' s' hrpos hspos hrsum hssum).2
  have hidentify : fibreKL C z (R.conditional z) (S.conditional z) =
      finiteKL r' s' := by
    unfold fibreKL finiteKL
    rw [Finset.sum_subtype
      (p := fun u ↦ C u = z)
      (Finset.univ.filter fun u ↦ C u = z) (by simp)
        (fun u ↦ R.conditional z u *
          Real.log (R.conditional z u / S.conditional z u))]
  rw [hidentify]
  exact hfinite

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
end NCG
