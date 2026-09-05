/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite domain-enriched synchronized-interface theorem
  (`thm:primitive-phase-selection`, Gran-Tensor manuscript)

The boxed criterion `γ_odd,X > 0 ∧ Δ_phase,X = 0` is a finite
checkable panel: `Δ_phase,X` is a finite sum of nonnegative
defect terms, and the theorem's operational content is that the
panel passes iff every term vanishes, with any positive term a
concrete first-failure witness.

* `phase_panel_zero_iff`: the nonnegative defect ledger
  `Δ_phase,X = Σ δᵢ` vanishes iff every declared defect term
  vanishes;
* `locked_phase_criterion`: the boxed conjunction
  `γ_odd > 0 ∧ Δ_phase = 0` is equivalent to the fully-resolved
  panel `γ_odd > 0 ∧ ∀ i, δᵢ = 0`;
* `first_failure_witness`: if the panel fails, there is a least
  index with a strictly positive defect — the concrete
  first-failure witness, naming the single Read or environment
  POVM that must be added.

The operational-isomorphism classification onto the locked
twenty-five-cell synchronized Store phase, including its allowed
Stinespring, determinant-sign, and Kraus-phase coordinate freedoms,
is proved in `NCG.Grand.PrimitivePhaseSelectionClassification`.
-/

namespace NCG

/-- The nonnegative defect ledger vanishes iff every declared
defect term vanishes. -/
theorem phase_panel_zero_iff {N : ℕ} (δ : Fin N → ℝ)
    (hδ : ∀ i, 0 ≤ δ i) :
    (∑ i, δ i = 0) ↔ ∀ i, δ i = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => hδ i]
  exact ⟨fun h i => h i (Finset.mem_univ i),
    fun h i _ => h i⟩

/-- Boxed criterion: `γ_odd > 0 ∧ Δ_phase = 0` is the
fully-resolved finite panel. -/
theorem locked_phase_criterion {N : ℕ} (γodd : ℝ)
    (δ : Fin N → ℝ) (hδ : ∀ i, 0 ≤ δ i) :
    (0 < γodd ∧ ∑ i, δ i = 0)
      ↔ (0 < γodd ∧ ∀ i, δ i = 0) :=
  and_congr_right fun _ => phase_panel_zero_iff δ hδ

/-- First-failure witness: a failing panel has a least index
with strictly positive defect. -/
theorem first_failure_witness {N : ℕ} (δ : Fin N → ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (h : ¬ ∀ i, δ i = 0) :
    ∃ i : Fin N, 0 < δ i ∧ ∀ j, j < i → δ j = 0 := by
  obtain ⟨i₀, hi₀⟩ := not_forall.mp h
  classical
  have hex : ∃ k : ℕ, ∃ hk : k < N, δ ⟨k, hk⟩ ≠ 0 :=
    ⟨i₀.val, i₀.isLt, by simpa using hi₀⟩
  obtain ⟨hk, hne⟩ := Nat.find_spec hex
  refine ⟨⟨Nat.find hex, hk⟩,
    lt_of_le_of_ne (hδ _) (Ne.symm hne), fun j hj => ?_⟩
  by_contra hj0
  exact Nat.find_min hex hj ⟨j.isLt, by simpa using hj0⟩

end NCG
