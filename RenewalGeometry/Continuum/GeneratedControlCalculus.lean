/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledUniqueness

/-!
# Zero-order control of fields on a slab (generic)

A small calculus for the constraint (subsidiary) systems of `app:generated-dynamics`: a field
`r` is **controlled** by an unknown field `U` on a set `s` if `‖r(y)‖ ≤ K‖U(y)‖` on `s`.  Sums,
products with bounded coefficients and applications of uniformly bounded linear operators of
controlled fields are controlled; coefficients that are continuous on an open slab and spatially
periodic are bounded on every closed sub-slab.

* `Ctrl`, `Ctrl.add`, `Ctrl.sub`, `Ctrl.neg`, `Ctrl.sum`, `Ctrl.smul`, `Ctrl.endo`, `Ctrl.clm`,
  `Ctrl.congr`, `Ctrl.of_norm_le`, `Ctrl.mono`;
* `bdd_of_cont` — continuous periodic coefficients are bounded on closed sub-slabs;
* `endBdd_of_cont` — endomorphism-valued coefficients whose applications are continuous are
  uniformly bounded operators on closed sub-slabs (finite dimension).
-/

open Set Finset

noncomputable section

namespace RenewalGeometry.GenCtrl

open SymHypEnergy SlabWaveHk

set_option linter.unusedSectionVars false

variable {E F G : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [SeminormedAddCommGroup G]

/-- **`r` is controlled by `U` on `s`**: `‖r y‖ ≤ K‖U y‖` on `s`. -/
def Ctrl (U : ST 3 → E) (s : Set (ST 3)) (r : ST 3 → F) : Prop :=
  ∃ K, 0 ≤ K ∧ ∀ y ∈ s, ‖r y‖ ≤ K * ‖U y‖

variable {U : ST 3 → E} {s : Set (ST 3)}

theorem Ctrl.zero : Ctrl U s (fun _ => (0 : F)) := ⟨0, le_rfl, fun y _ => by simp⟩

theorem Ctrl.of_norm_le {r : ST 3 → F} {r' : ST 3 → G} (h : Ctrl U s r')
    (hle : ∀ y ∈ s, ‖r y‖ ≤ ‖r' y‖) : Ctrl U s r := by
  obtain ⟨K, hK, hb⟩ := h
  exact ⟨K, hK, fun y hy => (hle y hy).trans (hb y hy)⟩

theorem Ctrl.congr {r r' : ST 3 → F} (h : Ctrl U s r) (he : ∀ y ∈ s, r' y = r y) :
    Ctrl U s r' := h.of_norm_le fun y hy => by rw [he y hy]

theorem Ctrl.add {r r' : ST 3 → F} (h : Ctrl U s r) (h' : Ctrl U s r') :
    Ctrl U s (fun y => r y + r' y) := by
  obtain ⟨K, hK, hb⟩ := h
  obtain ⟨K', hK', hb'⟩ := h'
  refine ⟨K + K', add_nonneg hK hK', fun y hy => ?_⟩
  calc ‖r y + r' y‖ ≤ ‖r y‖ + ‖r' y‖ := norm_add_le _ _
    _ ≤ K * ‖U y‖ + K' * ‖U y‖ := add_le_add (hb y hy) (hb' y hy)
    _ = (K + K') * ‖U y‖ := by ring

theorem Ctrl.neg {r : ST 3 → F} (h : Ctrl U s r) : Ctrl U s (fun y => -r y) :=
  h.of_norm_le fun y _ => by rw [norm_neg]

theorem Ctrl.sub {r r' : ST 3 → F} (h : Ctrl U s r) (h' : Ctrl U s r') :
    Ctrl U s (fun y => r y - r' y) := by
  simp only [sub_eq_add_neg]
  exact h.add h'.neg

theorem Ctrl.sum {ι : Type*} (t : Finset ι) {r : ι → ST 3 → F} (h : ∀ i ∈ t, Ctrl U s (r i)) :
    Ctrl U s (fun y => ∑ i ∈ t, r i y) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (Ctrl.zero (U := U) (s := s) (F := F))
  | insert i t hi ih =>
    have h1 := h i (Finset.mem_insert_self i t)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    exact (h1.add h2).congr fun y _ => by rw [Finset.sum_insert hi]

/-- Bounded coefficients on a set. -/
def Bdd (c : ST 3 → G) (s : Set (ST 3)) : Prop := ∃ C, ∀ y ∈ s, ‖c y‖ ≤ C

theorem Bdd.nonneg_bound {c : ST 3 → G} (h : Bdd c s) : ∃ C, 0 ≤ C ∧ ∀ y ∈ s, ‖c y‖ ≤ C := by
  obtain ⟨C, hC⟩ := h
  exact ⟨max C 0, le_max_right _ _, fun y hy => (hC y hy).trans (le_max_left _ _)⟩

theorem Ctrl.smul {F' : Type*} [SeminormedAddCommGroup F'] [NormedSpace ℝ F']
    {c : ST 3 → ℝ} {r : ST 3 → F'} (hc : Bdd c s) (h : Ctrl U s r) :
    Ctrl U s (fun y => c y • r y) := by
  obtain ⟨C, hC0, hC⟩ := hc.nonneg_bound
  obtain ⟨K, hK, hb⟩ := h
  refine ⟨C * K, mul_nonneg hC0 hK, fun y hy => ?_⟩
  rw [norm_smul]
  calc ‖c y‖ * ‖r y‖ ≤ C * (K * ‖U y‖) :=
        mul_le_mul (hC y hy) (hb y hy) (norm_nonneg _) hC0
    _ = C * K * ‖U y‖ := by ring

/-- **Uniformly bounded operator coefficients**: `‖T(y)v‖ ≤ C‖v‖` on `s`. -/
def EndBdd {F' G' : Type*} [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
    (T : ST 3 → F' → G') (s : Set (ST 3)) : Prop :=
  ∃ C, 0 ≤ C ∧ ∀ y ∈ s, ∀ v, ‖T y v‖ ≤ C * ‖v‖

theorem Ctrl.endo {F' G' : Type*} [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
    {T : ST 3 → F' → G'} {r : ST 3 → F'} (hT : EndBdd T s) (h : Ctrl U s r) :
    Ctrl U s (fun y => T y (r y)) := by
  obtain ⟨C, hC0, hC⟩ := hT
  obtain ⟨K, hK, hb⟩ := h
  refine ⟨C * K, mul_nonneg hC0 hK, fun y hy => ?_⟩
  calc ‖T y (r y)‖ ≤ C * ‖r y‖ := hC y hy _
    _ ≤ C * (K * ‖U y‖) := mul_le_mul_of_nonneg_left (hb y hy) hC0
    _ = C * K * ‖U y‖ := by ring

/-- A fixed continuous linear map is a uniformly bounded operator. -/
theorem endBdd_clm {F' G' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [NormedAddCommGroup G'] [NormedSpace ℝ G'] (L : F' →L[ℝ] G') :
    EndBdd (fun _ v => L v) s :=
  ⟨‖L‖, norm_nonneg _, fun _ _ v => L.le_opNorm v⟩

/-- Controlled by a component: `‖r y‖ ≤ C‖U y‖` directly. -/
theorem Ctrl.of_le_mul {r : ST 3 → F} {C : ℝ} (hC : 0 ≤ C) (h : ∀ y ∈ s, ‖r y‖ ≤ C * ‖U y‖) :
    Ctrl U s r := ⟨C, hC, h⟩

theorem Ctrl.self : Ctrl U s U := ⟨1, zero_le_one, fun y _ => by rw [one_mul]⟩

/-- Monotonicity in the unknown. -/
theorem Ctrl.mono {E' : Type*} [SeminormedAddCommGroup E'] {U' : ST 3 → E'} {r : ST 3 → F}
    (h : Ctrl U s r) {C : ℝ} (hC : 0 ≤ C) (hU : ∀ y ∈ s, ‖U y‖ ≤ C * ‖U' y‖) : Ctrl U' s r := by
  obtain ⟨K, hK, hb⟩ := h
  refine ⟨K * C, mul_nonneg hK hC, fun y hy => ?_⟩
  calc ‖r y‖ ≤ K * ‖U y‖ := hb y hy
    _ ≤ K * (C * ‖U' y‖) := mul_le_mul_of_nonneg_left (hU y hy) hK
    _ = K * C * ‖U' y‖ := by ring

/-! ### Bounded coefficients from continuity and periodicity -/

section Cont

variable {a b t₀ t₁ : ℝ}

/-- Continuous periodic coefficients are bounded on closed sub-slabs. -/
theorem bdd_of_cont {G' : Type*} [NormedAddCommGroup G'] {c : ST 3 → G'}
    (hc : ContinuousOn c (openSlab a b)) (hp : IsSPeriodic c) (ha : a < t₀) (hb : t₁ < b) :
    Bdd c (slab t₀ t₁) :=
  KatoGalerkin.exists_bound_slab hc hp ha hb

/-- Endomorphism coefficients with continuous applications are uniformly bounded operators on
closed sub-slabs. -/
theorem endBdd_of_cont {F' G' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [FiniteDimensional ℝ F'] [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {T : ST 3 → F' →ₗ[ℝ] G'} (hc : ∀ v, ContinuousOn (fun y => T y v) (openSlab a b))
    (hp : IsSPeriodic T) (ha : a < t₀) (hb : t₁ < b) :
    EndBdd (fun y v => T y v) (slab t₀ t₁) := by
  set L : ST 3 → F' →L[ℝ] G' := fun y => LinearMap.toContinuousLinearMap (T y) with hL
  have hLc : ContinuousOn L (openSlab a b) := continuousOn_clm_apply.2 fun v => hc v
  have hLp : IsSPeriodic L := fun k y => by simp only [hL, hp k y]
  obtain ⟨C, hC⟩ := KatoGalerkin.exists_bound_slab hLc hLp ha hb
  refine ⟨max C 0, le_max_right _ _, fun y hy v => ?_⟩
  have := (L y).le_opNorm v
  calc ‖T y v‖ = ‖L y v‖ := rfl
    _ ≤ ‖L y‖ * ‖v‖ := this
    _ ≤ max C 0 * ‖v‖ :=
      mul_le_mul_of_nonneg_right ((hC y hy).trans (le_max_left _ _)) (norm_nonneg _)

end Cont

end RenewalGeometry.GenCtrl
