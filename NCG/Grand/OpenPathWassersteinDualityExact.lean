/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTSourceVariance

/-!
# Exact Wasserstein duality on a finite open path

This file supplies the Wasserstein half omitted from the earlier encoding of
`thm:GT-open-current`.  The supremum is encoded by `IsGreatest`: every
one-Lipschitz potential is bounded by the cumulative-mass cost, and an
explicit potential whose increments oppose the cumulative mass attains it.
-/

open Finset

namespace NCG
namespace OpenPathWassersteinDuality

/-- Cumulative source mass through vertex `k`. -/
def prefixMass (s : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (k + 1), s r

/-- Unit-edge transport cost on the path with `N` edges. -/
def pathTransportCost (N : ℕ) (s : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, |prefixMass s k|

/-- Potentials with edge increments of absolute value at most one. -/
def IsUnitLipschitz (N : ℕ) (φ : ℕ → ℝ) : Prop :=
  ∀ k < N, |φ (k + 1) - φ k| ≤ 1

/-- The dual pairing of a potential with a source on vertices `0,...,N`. -/
def sourcePairing (N : ℕ) (s φ : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), φ k * s k

theorem prefixMass_succ (s : ℕ → ℝ) (k : ℕ) :
    prefixMass s (k + 1) = prefixMass s k + s (k + 1) := by
  simp [prefixMass, Finset.sum_range_succ]

/-- Finite summation by parts, including the terminal boundary term. -/
theorem summation_by_parts (N : ℕ) (s φ : ℕ → ℝ) :
    sourcePairing N s φ =
      φ N * prefixMass s N -
        ∑ k ∈ Finset.range N,
          (φ (k + 1) - φ k) * prefixMass s k := by
  induction N with
  | zero => simp [sourcePairing, prefixMass]
  | succ N ih =>
      rw [show sourcePairing (N + 1) s φ =
          sourcePairing N s φ + φ (N + 1) * s (N + 1) by
        simp [sourcePairing, Finset.sum_range_succ]]
      rw [ih, prefixMass_succ, Finset.sum_range_succ]
      ring

theorem prefixMass_terminal_eq_zero {N : ℕ} {s : ℕ → ℝ}
    (hmass : ∑ k ∈ Finset.range (N + 1), s k = 0) :
    prefixMass s N = 0 := by
  simpa [prefixMass] using hmass

/-- Summation by parts on the zero-total-mass branch. -/
theorem summation_by_parts_zero_mass {N : ℕ} {s φ : ℕ → ℝ}
    (hmass : ∑ k ∈ Finset.range (N + 1), s k = 0) :
    sourcePairing N s φ =
      -∑ k ∈ Finset.range N,
        (φ (k + 1) - φ k) * prefixMass s k := by
  rw [summation_by_parts, prefixMass_terminal_eq_zero hmass]
  ring

theorem pairing_le_transportCost {N : ℕ} {s φ : ℕ → ℝ}
    (hmass : ∑ k ∈ Finset.range (N + 1), s k = 0)
    (hφ : IsUnitLipschitz N φ) :
    sourcePairing N s φ ≤ pathTransportCost N s := by
  rw [summation_by_parts_zero_mass hmass]
  unfold pathTransportCost
  rw [show -(∑ k ∈ Finset.range N,
      (φ (k + 1) - φ k) * prefixMass s k) =
      ∑ k ∈ Finset.range N,
        -((φ (k + 1) - φ k) * prefixMass s k) by
    rw [Finset.sum_neg_distrib]]
  refine Finset.sum_le_sum (fun (k : ℕ) (hk : k ∈ Finset.range N) => ?_)
  have hinc : |φ (k + 1) - φ k| ≤ 1 := hφ k (Finset.mem_range.mp hk)
  calc
    -((φ (k + 1) - φ k) * prefixMass s k)
        ≤ |(φ (k + 1) - φ k) * prefixMass s k| := neg_le_abs _
    _ = |φ (k + 1) - φ k| * |prefixMass s k| := abs_mul _ _
    _ ≤ 1 * |prefixMass s k| :=
      mul_le_mul_of_nonneg_right hinc (abs_nonneg _)
    _ = |prefixMass s k| := one_mul _

/-- A Kantorovich maximizing potential, pinned to zero at the left endpoint. -/
noncomputable def maximizingPotential (s : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ r ∈ Finset.range k, -((SignType.sign (prefixMass s r) : SignType) : ℝ)

theorem maximizingPotential_increment (s : ℕ → ℝ) (k : ℕ) :
    maximizingPotential s (k + 1) - maximizingPotential s k =
      -((SignType.sign (prefixMass s k) : SignType) : ℝ) := by
  simp [maximizingPotential, Finset.sum_range_succ]

theorem maximizingPotential_lipschitz (N : ℕ) (s : ℕ → ℝ) :
    IsUnitLipschitz N (maximizingPotential s) := by
  intro k hk
  rw [maximizingPotential_increment]
  cases SignType.sign (prefixMass s k) <;> norm_num

theorem maximizingPotential_attains {N : ℕ} {s : ℕ → ℝ}
    (hmass : ∑ k ∈ Finset.range (N + 1), s k = 0) :
    sourcePairing N s (maximizingPotential s) = pathTransportCost N s := by
  rw [summation_by_parts_zero_mass hmass]
  unfold pathTransportCost
  rw [show -(∑ k ∈ Finset.range N,
      (maximizingPotential s (k + 1) - maximizingPotential s k) * prefixMass s k) =
      ∑ k ∈ Finset.range N,
        -((maximizingPotential s (k + 1) - maximizingPotential s k) * prefixMass s k) by
    rw [Finset.sum_neg_distrib]]
  refine Finset.sum_congr rfl (fun (k : ℕ) (hk : k ∈ Finset.range N) => ?_)
  rw [maximizingPotential_increment]
  simp

/-- The boxed finite-path `W₁` duality from `thm:GT-open-current`, in the
strong attained-maximum form. -/
theorem open_path_wasserstein_isGreatest {N : ℕ} {s : ℕ → ℝ}
    (hmass : ∑ k ∈ Finset.range (N + 1), s k = 0) :
    IsGreatest
      {x : ℝ | ∃ φ : ℕ → ℝ,
        IsUnitLipschitz N φ ∧ x = sourcePairing N s φ}
      (pathTransportCost N s) := by
  refine ⟨?_, ?_⟩
  · exact ⟨maximizingPotential s, maximizingPotential_lipschitz N s,
      (maximizingPotential_attains hmass).symm⟩
  · rintro x ⟨φ, hφ, rfl⟩
    exact pairing_le_transportCost hmass hφ

end OpenPathWassersteinDuality
end NCG
