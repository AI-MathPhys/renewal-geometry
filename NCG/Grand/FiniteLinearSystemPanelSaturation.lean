/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ProvenancePanelSaturation

/-!
# Finite-panel saturation for algebraic linear systems

This file supplies carrier-independent finite-dimensional stabilization
lemmas for reachable and observable panels.  Unlike the Hilbert-space
Krylov API, these results apply directly to quotient modules.
-/

namespace NCG

/-- A decreasing filtration starting at the full carrier, freezing after
its first plateau, and exhausting the zero subspace is already zero at the
carrier dimension. -/
theorem decreasing_filtration_saturates_by_finrank
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (K : ℕ → Submodule ℂ V)
    (hzero : K 0 = ⊤)
    (hstep : ∀ k, K (k + 1) ≤ K k)
    (hfreeze : ∀ k, K k = K (k + 1) →
      ∀ j, k ≤ j → K j = K k)
    (hexhaust : (⨅ k, K k) = ⊥) :
    ∀ p, Module.finrank ℂ V ≤ p → K p = ⊥ := by
  let d := Module.finrank ℂ V
  have hanti : Antitone K := antitone_nat_of_succ_le hstep
  have hKd : K d = ⊥ := by
    by_contra hnot
    have hstrict : ∀ k, k < d → K (k + 1) < K k := by
      intro k hk
      refine lt_of_le_of_ne (hstep k) ?_
      intro heq
      have hconst := hfreeze k heq.symm
      have hkBot : K k = ⊥ := by
        apply le_bot_iff.mp
        rw [← hexhaust]
        apply le_iInf
        intro j
        by_cases hj : k ≤ j
        · rw [hconst j hj]
        · exact hanti (Nat.le_of_lt (lt_of_not_ge hj))
      have hle : K d ≤ K k := hanti (Nat.le_of_lt hk)
      rw [hkBot] at hle
      exact hnot (le_bot_iff.mp hle)
    have hrank : ∀ k, k ≤ d →
        Module.finrank ℂ (K k) + k ≤ d := by
      intro k hk
      induction k with
      | zero =>
          rw [hzero, finrank_top]
          exact le_rfl
      | succ k ih =>
          have hklt : k < d := by omega
          have hlt := Submodule.finrank_lt_finrank_of_lt (hstrict k hklt)
          have hprev := ih (by omega)
          omega
    have hpos : 0 < Module.finrank ℂ (K d) :=
      Submodule.one_le_finrank_iff.mpr hnot
    have := hrank d le_rfl
    omega
  intro p hp
  apply le_bot_iff.mp
  rw [← hKd]
  exact hanti hp

/-- A decreasing filtration that freezes after its first plateau and exhausts
zero is already zero at the carrier dimension.  No assumption on its initial
term is needed. -/
theorem decreasing_filtration_saturates_by_finrank_of_exhausts
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (K : ℕ → Submodule ℂ V)
    (hstep : ∀ k, K (k + 1) ≤ K k)
    (hfreeze : ∀ k, K k = K (k + 1) →
      ∀ j, k ≤ j → K j = K k)
    (hexhaust : (⨅ k, K k) = ⊥) :
    ∀ p, Module.finrank ℂ V ≤ p → K p = ⊥ := by
  let d := Module.finrank ℂ V
  have hanti : Antitone K := antitone_nat_of_succ_le hstep
  have hKd : K d = ⊥ := by
    by_contra hnot
    have hstrict : ∀ k, k < d → K (k + 1) < K k := by
      intro k hk
      refine lt_of_le_of_ne (hstep k) ?_
      intro heq
      have hconst := hfreeze k heq.symm
      have hkBot : K k = ⊥ := by
        apply le_bot_iff.mp
        rw [← hexhaust]
        apply le_iInf
        intro j
        by_cases hj : k ≤ j
        · rw [hconst j hj]
        · exact hanti (Nat.le_of_lt (lt_of_not_ge hj))
      have hle : K d ≤ K k := hanti (Nat.le_of_lt hk)
      rw [hkBot] at hle
      exact hnot (le_bot_iff.mp hle)
    have hrank : ∀ k, k ≤ d →
        Module.finrank ℂ (K k) + k ≤ d := by
      intro k hk
      induction k with
      | zero => simpa using Submodule.finrank_le (K 0)
      | succ k ih =>
          have hklt : k < d := by omega
          have hlt := Submodule.finrank_lt_finrank_of_lt (hstrict k hklt)
          have hprev := ih (by omega)
          omega
    have hpos : 0 < Module.finrank ℂ (K d) :=
      Submodule.one_le_finrank_iff.mpr hnot
    have := hrank d le_rfl
    omega
  intro p hp
  apply le_bot_iff.mp
  rw [← hKd]
  exact hanti hp
end NCG
