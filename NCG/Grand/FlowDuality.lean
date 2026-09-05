/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact pressure-flow characterization of spatial isoperimetry
  (`thm:pressure-flow-isoperimetry`, Gran-Tensor manuscript)

Finite flow/cut mini-library:

* `boundary_flux_identity`: the discrete Stokes identity — for an
  antisymmetric edge current, the total divergence inside `A`
  equals the net flux across the cut `∂A` (interior pairs cancel
  exactly);
* `flow_cut_weak_duality`: the certifying direction of the boxed
  equivalence — a physical edge-current realization of a demand
  with congestion at most `κ` bounds the realized demand by
  `κ` times the cut capacity, so uniform congestion `I_*⁻¹`
  yields the uniform cut inequality;
* `min_energy_unique`: among all admissible currents there is at
  most one minimizer of the weighted energy
  `Σ_e |j_e|²/(h c_e)` — the parallelogram identity makes the
  energy strictly convex on the midpoint-closed constraint set;
* `canonical_current_invariant`: the canonical minimum-energy
  current is invariant under every energy-preserving symmetry of
  the constraint set — uniqueness forces `T j* = j*`.

Rendering disclosed: the converse (max-flow/min-cut — every
uniform cut margin produces a flow of congestion `I_*⁻¹`; LP
duality on the finite graph) and the identification
`Γ_press,X = I_X⁻¹` through the pressure-demand normalization
are the manuscript's duality layer; the certifying direction,
the exact interior cancellation, and the uniqueness/invariance
of the canonical current are proved here.
-/

namespace NCG

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Discrete Stokes: for an antisymmetric current, total interior
divergence equals the net flux across the cut. -/
theorem boundary_flux_identity (j : ι → ι → ℝ)
    (hanti : ∀ u v, j u v = -j v u) (A : Finset ι) :
    ∑ v ∈ A, ∑ u, j v u
      = ∑ v ∈ A, ∑ u ∈ Aᶜ, j v u := by
  have hsplit : ∀ v ∈ A, (∑ u, j v u)
      = ∑ u ∈ A, j v u + ∑ u ∈ Aᶜ, j v u := by
    intro v _
    rw [← Finset.sum_add_sum_compl A]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hinterior : ∑ v ∈ A, ∑ u ∈ A, j v u = 0 := by
    have hswap : ∑ v ∈ A, ∑ u ∈ A, j v u
        = ∑ v ∈ A, ∑ u ∈ A, j u v := Finset.sum_comm
    have hneg : ∑ v ∈ A, ∑ u ∈ A, j u v
        = -∑ v ∈ A, ∑ u ∈ A, j v u := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun u _ => (hanti u v)
    linarith [hswap, hneg, hswap.trans hneg]
  rw [hinterior, zero_add]

/-- Certifying direction of the boxed equivalence: a current
realizing total demand `d` inside `A` with congestion `κ`
(`|j| ≤ κ·c` edgewise) bounds the demand by `κ` times the cut
capacity. -/
theorem flow_cut_weak_duality (j c : ι → ι → ℝ)
    (hanti : ∀ u v, j u v = -j v u) (A : Finset ι) (κ : ℝ)
    (hcong : ∀ u v, |j u v| ≤ κ * c u v) :
    ∑ v ∈ A, ∑ u, j v u
      ≤ κ * ∑ v ∈ A, ∑ u ∈ Aᶜ, c v u := by
  rw [boundary_flux_identity j hanti A, Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun u _ => ?_
  exact le_trans (le_abs_self _) (hcong v u)

/-- Strict convexity of the weighted flow energy: on a
midpoint-closed admissible set, the minimizer of
`Σ_p w_p j_p²` is unique. -/
theorem min_energy_unique {P : Type*} [Fintype P] (w : P → ℝ)
    (hw : ∀ p, 0 < w p) (S : Set (P → ℝ))
    (hmid : ∀ j₁ ∈ S, ∀ j₂ ∈ S,
      (fun p => (j₁ p + j₂ p) / 2) ∈ S)
    (j₁ j₂ : P → ℝ) (h₁ : j₁ ∈ S) (h₂ : j₂ ∈ S)
    (hmin₁ : ∀ j ∈ S,
      ∑ p, w p * j₁ p ^ 2 ≤ ∑ p, w p * j p ^ 2)
    (hmin₂ : ∀ j ∈ S,
      ∑ p, w p * j₂ p ^ 2 ≤ ∑ p, w p * j p ^ 2) :
    j₁ = j₂ := by
  by_contra hne
  obtain ⟨p₀, hp₀⟩ := Function.ne_iff.mp hne
  have hEeq : ∑ p, w p * j₁ p ^ 2 = ∑ p, w p * j₂ p ^ 2 :=
    le_antisymm (hmin₁ j₂ h₂) (hmin₂ j₁ h₁)
  have hident : ∑ p, w p * ((j₁ p + j₂ p) / 2) ^ 2
      = (∑ p, w p * j₁ p ^ 2 + ∑ p, w p * j₂ p ^ 2) / 2
        - ∑ p, w p * ((j₁ p - j₂ p) / 2) ^ 2 := by
    calc ∑ p, w p * ((j₁ p + j₂ p) / 2) ^ 2
        = ∑ p, ((w p * j₁ p ^ 2 + w p * j₂ p ^ 2) / 2
            - w p * ((j₁ p - j₂ p) / 2) ^ 2) :=
          Finset.sum_congr rfl fun p _ => by ring
      _ = (∑ p, (w p * j₁ p ^ 2 + w p * j₂ p ^ 2)) / 2
          - ∑ p, w p * ((j₁ p - j₂ p) / 2) ^ 2 := by
          rw [Finset.sum_sub_distrib, Finset.sum_div]
      _ = (∑ p, w p * j₁ p ^ 2 + ∑ p, w p * j₂ p ^ 2) / 2
          - ∑ p, w p * ((j₁ p - j₂ p) / 2) ^ 2 := by
          rw [Finset.sum_add_distrib]
  have hpos : 0 < ∑ p, w p * ((j₁ p - j₂ p) / 2) ^ 2 := by
    have hne0 : (j₁ p₀ - j₂ p₀) / 2 ≠ 0 :=
      div_ne_zero (sub_ne_zero.mpr hp₀) two_ne_zero
    have hsq : 0 < ((j₁ p₀ - j₂ p₀) / 2) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _)
        (Ne.symm (pow_ne_zero 2 hne0))
    have hterm : 0 < w p₀ * ((j₁ p₀ - j₂ p₀) / 2) ^ 2 :=
      mul_pos (hw p₀) hsq
    refine lt_of_lt_of_le hterm ?_
    refine Finset.single_le_sum
      (f := fun p => w p * ((j₁ p - j₂ p) / 2) ^ 2)
      (fun p _ => ?_) (Finset.mem_univ p₀)
    have := (hw p).le
    positivity
  have hmidmem := hmid j₁ h₁ j₂ h₂
  have hmidmin := hmin₁ _ hmidmem
  rw [hident, ← hEeq] at hmidmin
  linarith

/-- Symmetry invariance of the canonical current: an
energy-preserving symmetry of the admissible set fixes the
unique minimizer. -/
theorem canonical_current_invariant {P : Type*} [Fintype P]
    (w : P → ℝ) (hw : ∀ p, 0 < w p) (S : Set (P → ℝ))
    (hmid : ∀ j₁ ∈ S, ∀ j₂ ∈ S,
      (fun p => (j₁ p + j₂ p) / 2) ∈ S)
    (T : (P → ℝ) → (P → ℝ)) (hTS : ∀ j ∈ S, T j ∈ S)
    (hTE : ∀ j, ∑ p, w p * (T j) p ^ 2 = ∑ p, w p * j p ^ 2)
    (jstar : P → ℝ) (hstar : jstar ∈ S)
    (hminstar : ∀ j ∈ S,
      ∑ p, w p * jstar p ^ 2 ≤ ∑ p, w p * j p ^ 2) :
    T jstar = jstar := by
  have hTmem : T jstar ∈ S := hTS jstar hstar
  have hTmin : ∀ j ∈ S,
      ∑ p, w p * (T jstar) p ^ 2 ≤ ∑ p, w p * j p ^ 2 := by
    intro j hj
    rw [hTE jstar]
    exact hminstar j hj
  exact min_energy_unique w hw S hmid (T jstar) jstar hTmem
    hstar hTmin hminstar

end NCG
