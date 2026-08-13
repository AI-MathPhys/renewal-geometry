/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ChaosLocalization
import NCG.Grand.CollisionParityHodge

/-!
# All-degree hard-core corrector profile

Quantitative assembly for `thm:renewal-hard-core-all-degree`.  The local
three-dimensional Green/Feshbach construction produces finitely many profiles
below a fixed degree ceiling.  This file turns their uniform relative
`L²+Dirichlet` bound and the exact external `d/N` factor into the displayed
`N⁻²` estimate, and combines fixed-ceiling disappearance with the uniform
high-degree localization theorem.
-/

open scoped BigOperators Topology

namespace NCG

/-- The exact `d_N/N` profile representation gives the fixed-ceiling
`N⁻²` bound with its constants visible. -/
theorem hard_core_fixed_degree_bound
    {R : ℕ} (N : ℕ) (d D B : ℝ)
    (profileNorm correctorNorm : Fin R → ℝ)
    (hN : 0 < N) (hD : |d| ≤ D) (hD0 : 0 ≤ D)
    (hprofile : ∀ r, 0 ≤ profileNorm r)
    (hcorrector : ∀ r, correctorNorm r
      = (d / N) ^ 2 * profileNorm r)
    (hsum : ∑ r, profileNorm r ≤ B) :
    ∑ r, correctorNorm r ≤ D ^ 2 * B / N ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd2 : d ^ 2 ≤ D ^ 2 := by
    calc d ^ 2 = |d| ^ 2 := by rw [sq_abs]
      _ ≤ D ^ 2 := (sq_le_sq₀ (abs_nonneg d) hD0).2 hD
  calc
    ∑ r, correctorNorm r
        = (d / N) ^ 2 * ∑ r, profileNorm r := by
          simp_rw [hcorrector]
          rw [Finset.mul_sum]
    _ ≤ (d / N) ^ 2 * B := by
          exact mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ ≤ (D / N) ^ 2 * B := by
          have hB0 : 0 ≤ B := le_trans
            (Finset.sum_nonneg fun r _ => hprofile r) hsum
          apply mul_le_mul_of_nonneg_right _ hB0
          rw [div_pow, div_pow]
          exact div_le_div_of_nonneg_right hd2 (sq_nonneg (N : ℝ))
    _ = D ^ 2 * B / N ^ 2 := by ring

/-- Adding a nonnegative Dirichlet energy to every relative profile preserves
the same uniform finite-ceiling control of its `L²` part. -/
theorem hard_core_profile_l2_of_l2_energy
    {R : ℕ} (l2 energy : Fin R → ℝ) (B : ℝ)
    (hl2 : ∀ r, 0 ≤ l2 r) (henergy : ∀ r, 0 ≤ energy r)
    (hbound : ∑ r, (l2 r + energy r) ≤ B) :
    ∑ r, l2 r ≤ B := by
  calc
    ∑ r, l2 r ≤ ∑ r, (l2 r + energy r) := by
      gcongr with r
      exact le_add_of_nonneg_right (henergy r)
    _ ≤ B := hbound

/-- Double-limit assembly used in the manuscript: every fixed-degree part
vanishes, while the high-degree tail is uniformly small, so the full
corrector vanishes. -/
theorem hard_core_corrector_disappears
    (total low tail : ℕ → ℕ → ℝ)
    (htotal : ∀ N R, total N R = low N R + tail N R)
    (hlow : ∀ R, Filter.Tendsto (fun N => low N R)
      Filter.atTop (nhds 0))
    (htail : ∀ ε > 0, ∃ R, ∀ N, |tail N R| ≤ ε)
    (htotalIndependent : ∀ N R S, total N R = total N S) :
    Filter.Tendsto (fun N => total N 0) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR⟩ := htail (ε / 2) (by positivity)
  have hlowR := (Metric.tendsto_atTop.1 (hlow R)) (ε / 2) (by positivity)
  obtain ⟨N0, hN0⟩ := hlowR
  refine ⟨N0, fun N hN => ?_⟩
  rw [htotalIndependent N 0 R, htotal]
  have h1 := hN0 N hN
  have h2 := hR N
  rw [Real.dist_eq] at h1 ⊢
  have hl : |low N R| < ε / 2 := by simpa only [sub_zero] using h1
  have hsum : |low N R| + |tail N R| < ε := by linarith
  have htri := abs_add_le (low N R) (tail N R)
  simpa only [sub_zero] using htri.trans_lt hsum

/-- Finite Feshbach alternative in the form needed by the connected-cluster
induction: if a mixed-scale operator has no kernel, its kernel quotient is
trivial; conversely any failed injectivity exhibits a nonzero reflecting
state. -/
theorem finite_feshbach_kernel_alternative
    {X : Type*} [Fintype X] (F : Matrix X X ℂ) :
    (∀ x : X → ℂ, Matrix.mulVec F x = 0 → x = 0)
      ∨ ∃ x : X → ℂ, x ≠ 0 ∧ Matrix.mulVec F x = 0 := by
  by_cases h : ∀ x : X → ℂ, Matrix.mulVec F x = 0 → x = 0
  · exact Or.inl h
  · push Not at h
    obtain ⟨x, hx0, hxne⟩ := h
    exact Or.inr ⟨x, hxne, hx0⟩

end NCG
