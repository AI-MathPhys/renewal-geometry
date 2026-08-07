/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact first-chaos reaction–diffusion closure
  (`thm:renewal-interchange-first-chaos`,
  Gran-Tensor manuscript)

* `renewal_interchange_first_chaos`:
  (i) the boxed first-chaos invariance and closure
      `ℒ_G Φ_c = Φ_{Δ_κ c - g c}` — the first-chaos space
      is invariant and the induced action is the graph
      Laplacian shifted by the exact renewal gap `g`;
  (ii) the boxed coefficient quadratic form
      `-∑ c_i(Δ_κ c - g c)_i
        = g∑ c_i² + ∑_{i,j} κ_ij(c_i - c_j)c_i`,
      whose symmetrization is the edge Dirichlet energy.

The identification of `g = 22λ/15` with the uniformized
single-cell relaxation rate is `NCG.renewal_uniformization`;
the tensorized construction of the interchange generator
and the orthonormality of the Walsh generators `φ_i` are
the manuscript's product-space layer feeding the
per-generator action assumed here.
-/

open Finset

namespace NCG

/-- `thm:renewal-interchange-first-chaos`. -/
theorem renewal_interchange_first_chaos {V W : Type*}
    [Fintype V] [AddCommGroup W]
    [Module ℝ W] (L : W →ₗ[ℝ] W) (φ : V → W)
    (κ : V → V → ℝ) (g : ℝ)
    (hsym : ∀ i j, κ i j = κ j i)
    (hgen : ∀ i, L (φ i)
      = (-g) • φ i + ∑ j, κ i j • (φ j - φ i)) :
    -- (i) the boxed first-chaos closure
    (∀ c : V → ℝ, L (∑ i, c i • φ i)
      = ∑ i, ((∑ j, κ i j * (c j - c i)) - g * c i)
          • φ i)
    -- (ii) the boxed coefficient quadratic form
    ∧ (∀ c : V → ℝ,
        -(∑ i, c i * ((∑ j, κ i j * (c j - c i))
            - g * c i))
        = g * (∑ i, c i * c i)
          + ∑ i, ∑ j, κ i j * (c i - c j) * c i) := by
  constructor
  · intro c
    have hterm : ∀ i : V, L (c i • φ i)
        = ((-(g * c i)) - (∑ j, c i * κ i j)) • φ i
          + ∑ j, (c i * κ i j) • φ j := by
      intro i
      rw [map_smul, hgen i, smul_add, smul_smul,
        Finset.smul_sum]
      have hin : ∀ j ∈ (Finset.univ : Finset V),
          c i • (κ i j • (φ j - φ i))
          = (c i * κ i j) • φ j
            - (c i * κ i j) • φ i := by
        intro j _
        rw [smul_smul, smul_sub]
      rw [Finset.sum_congr rfl hin,
        Finset.sum_sub_distrib, ← Finset.sum_smul,
        sub_smul]
      have hg : c i * -g = -(g * c i) := by ring
      rw [hg]
      abel
    have hswap : ∑ i : V, ∑ j : V, (c i * κ i j) • φ j
        = ∑ i : V, (∑ j, κ i j * c j) • φ i := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by
        rw [hsym j i]
        ring
    calc L (∑ i, c i • φ i)
        = ∑ i, L (c i • φ i) := map_sum _ _ _
      _ = ∑ i, (((-(g * c i)) - (∑ j, c i * κ i j))
            • φ i + ∑ j, (c i * κ i j) • φ j) :=
          Finset.sum_congr rfl fun i _ => hterm i
      _ = (∑ i, ((-(g * c i)) - (∑ j, c i * κ i j))
            • φ i)
          + ∑ i, ∑ j, (c i * κ i j) • φ j :=
          Finset.sum_add_distrib
      _ = (∑ i, ((-(g * c i)) - (∑ j, c i * κ i j))
            • φ i)
          + ∑ i, (∑ j, κ i j * c j) • φ i := by
          rw [hswap]
      _ = ∑ i, ((∑ j, κ i j * (c j - c i))
            - g * c i) • φ i := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← add_smul]
          congr 1
          have hd : ∑ j, κ i j * (c j - c i)
              = (∑ j, κ i j * c j)
                - ∑ j, c i * κ i j := by
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring
          rw [hd]
          ring
  · intro c
    have hexp : ∀ i : V,
        c i * ((∑ j, κ i j * (c j - c i)) - g * c i)
        = (∑ j, κ i j * (c j - c i) * c i)
          - g * (c i * c i) := by
      intro i
      rw [mul_sub, Finset.mul_sum]
      have : ∀ j ∈ (Finset.univ : Finset V),
          c i * (κ i j * (c j - c i))
          = κ i j * (c j - c i) * c i := by
        intro j _
        ring
      rw [Finset.sum_congr rfl this]
      ring
    have hfinal : ∀ i : V,
        -(∑ j, κ i j * (c j - c i) * c i)
        = ∑ j, κ i j * (c i - c j) * c i := by
      intro i
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl fun i _ => hexp i,
      Finset.sum_sub_distrib, neg_sub, ← Finset.mul_sum,
      sub_eq_add_neg, ← Finset.sum_neg_distrib,
      Finset.sum_congr rfl fun i _ => hfinal i]

end NCG
