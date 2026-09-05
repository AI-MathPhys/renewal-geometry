/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# A finite separating Read panel exists
  (`lem:finite-read-panel`, Gran-Tensor manuscript)

* `finite_read_panel`: even when the admitted future family of
  contextual Read coordinates is infinite, at most
  `dim 𝒜_X^proc` of them already have the common kernel
  `𝒩_X^fut` — the terminating kernel-intersection descent.

Rendering disclosed: scalar contextual Read coordinates are
rendered as linear functionals on the finite-dimensional process
algebra (each contextual coordinate `q ↦ R_j(u q v)` is such a
functional), and the common kernel `𝒩_X^fut` is the infimum of
their kernels; the lemma produces a finite subfamily of size at
most the algebra dimension with the same kernel, by the
manuscript's strictly-decreasing intersection argument.
-/

namespace NCG

set_option maxHeartbeats 800000 in
-- the nested `biInf` submodule rewriting in the descent
-- recursion is instance-search heavy
/-- Kernel-descent recursion: if the current finite panel's
kernel has dimension at most `k`, it refines to a full panel of
at most `k` more coordinates. -/
private lemma read_panel_aux {V ι : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V]
    (φ : ι → V →ₗ[ℂ] ℂ) :
    ∀ (k : ℕ) (s : Finset ι),
      Module.finrank ℂ
          (⨅ i ∈ s, LinearMap.ker (φ i) : Submodule ℂ V) ≤ k →
      ∃ t : Finset ι, t.card ≤ s.card + k
        ∧ (⨅ i ∈ t, LinearMap.ker (φ i))
            = ⨅ i, LinearMap.ker (φ i) := by
  classical
  intro k
  induction k with
  | zero =>
      intro s hs
      refine ⟨s, by omega, ?_⟩
      have hbot : (⨅ i ∈ s, LinearMap.ker (φ i) : Submodule ℂ V)
          = ⊥ :=
        Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hs)
      have hle : (⨅ i, LinearMap.ker (φ i) : Submodule ℂ V)
          ≤ ⨅ i ∈ s, LinearMap.ker (φ i) :=
        le_iInf₂ fun i _ => iInf_le _ i
      rw [hbot] at hle ⊢
      exact (le_bot_iff.mp hle).symm
  | succ k ih =>
      intro s hs
      by_cases heq :
          (⨅ i ∈ s, LinearMap.ker (φ i) : Submodule ℂ V)
            = ⨅ i, LinearMap.ker (φ i)
      · exact ⟨s, by omega, heq⟩
      · have hle : (⨅ i, LinearMap.ker (φ i) : Submodule ℂ V)
            ≤ ⨅ i ∈ s, LinearMap.ker (φ i) :=
          le_iInf₂ fun i _ => iInf_le _ i
        have hlt : (⨅ i, LinearMap.ker (φ i) : Submodule ℂ V)
            < ⨅ i ∈ s, LinearMap.ker (φ i) :=
          lt_of_le_of_ne hle (Ne.symm heq)
        obtain ⟨x, hxs, hxi⟩ := SetLike.exists_of_lt hlt
        have hj : ∃ j, φ j x ≠ 0 := by
          by_contra hall
          simp only [not_exists, ne_eq, not_not] at hall
          exact hxi (Submodule.mem_iInf _ |>.mpr fun j =>
            LinearMap.mem_ker.mpr (hall j))
        obtain ⟨j, hj⟩ := hj
        have hstrict :
            (⨅ i ∈ insert j s, LinearMap.ker (φ i)
              : Submodule ℂ V)
              < ⨅ i ∈ s, LinearMap.ker (φ i) := by
          refine lt_of_le_of_ne
            (le_iInf₂ fun i hi =>
              iInf₂_le i (Finset.mem_insert_of_mem hi)) ?_
          intro hcontra
          apply hj
          have hx : x ∈ (⨅ i ∈ insert j s,
              LinearMap.ker (φ i) : Submodule ℂ V) := by
            rw [hcontra]
            exact hxs
          have hmem : (⨅ i ∈ insert j s,
              LinearMap.ker (φ i) : Submodule ℂ V)
              ≤ LinearMap.ker (φ j) :=
            iInf₂_le j (Finset.mem_insert_self j s)
          exact LinearMap.mem_ker.mp (hmem hx)
        have hrank : Module.finrank ℂ
            (⨅ i ∈ insert j s, LinearMap.ker (φ i)
              : Submodule ℂ V)
            < Module.finrank ℂ
              (⨅ i ∈ s, LinearMap.ker (φ i) : Submodule ℂ V) :=
          Submodule.finrank_lt_finrank_of_lt hstrict
        obtain ⟨t, htc, hteq⟩ := ih (insert j s) (by omega)
        have hcard := Finset.card_insert_le j s
        exact ⟨t, by omega, hteq⟩

/-- `lem:finite-read-panel`: at most `dim V` contextual Read
coordinates already cut out the common kernel. -/
theorem finite_read_panel {V ι : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V]
    (φ : ι → V →ₗ[ℂ] ℂ) :
    ∃ s : Finset ι, s.card ≤ Module.finrank ℂ V
      ∧ (⨅ i ∈ s, LinearMap.ker (φ i))
          = ⨅ i, LinearMap.ker (φ i) := by
  classical
  obtain ⟨t, htc, hteq⟩ :=
    read_panel_aux φ (Module.finrank ℂ V) ∅ (by
      have hempty : (⨅ i ∈ (∅ : Finset ι),
          LinearMap.ker (φ i) : Submodule ℂ V) = ⊤ := by
        simp
      rw [hempty]
      exact le_of_eq (finrank_top ℂ V))
  exact ⟨t, by simpa using htc, hteq⟩

end NCG
