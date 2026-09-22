/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.DiscreteAnalysis.FiniteWeightedGraphHeatKernel

/-!
# Spatial Dirichlet normalization: Dirichlet identity and `L^q` contraction
  (`def:supp-spatial-dirichlet`, `eq:supp-spatial-dirichlet`,
  `eq:main-spatial-dirichlet`; emergent-spacetime manuscript)

For a finite weighted graph (`FiniteWeightedGraph`: positive vertex masses
`μ`, symmetric nonnegative conductances `c`) the definition record fixes the
Dirichlet normalization `⟨f, Δ^sp f⟩_{L²(μ)} = ℰ^sp(f)` and remarks that the
heat semigroup `e^{-tΔ^sp}` is a finite Markov semigroup, contractive on every
`L^q(μ)`, `1 ≤ q ≤ ∞`.

* `laplacianApply_dirichletForm`: the normalization identity
  `∑_v μ_v f(v) (Δ^sp f)(v) = ℰ^sp(f)` in function coordinates for the
  mass-weighted Laplacian `laplacianApply` (the symmetric-coordinate version
  is `symmetricLaplacian_quadraticForm`).
* `heatApply_abs_le_sum`, `heatApply_weightedLq_le`: for `1 ≤ q < ∞`,
  `∑_v μ_v |e^{-tΔ} f (v)|^q ≤ ∑_v μ_v |f(v)|^q` (Jensen on the stochastic
  rows of the heat kernel and detailed balance).
* `heatApply_sup_le`: the `L^∞` contraction `sup |e^{-tΔ} f| ≤ sup |f|`.
  The `L¹` case is `heatApply_weightedL1_le` in the heat-kernel file.
-/

open scoped BigOperators

namespace RenewalGeometry
namespace FiniteWeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : FiniteWeightedGraph V)

/-- The Dirichlet normalization `⟨f, Δ^sp f⟩_{L²(μ)} = ℰ^sp(f)`
(`eq:supp-spatial-dirichlet`) for the mass-weighted Laplacian in function
coordinates. -/
theorem laplacianApply_dirichletForm (f : V → ℝ) :
    ∑ v, G.mass v * (f v * G.laplacianApply f v) =
      finiteSpatialEnergy G.conductance f := by
  unfold laplacianApply finiteSpatialEnergy
  have hcancel : ∀ v, G.mass v * (f v * ((∑ u, G.conductance v u * (f v - f u)) /
      G.mass v)) = ∑ u, G.conductance v u * (f v * (f v - f u)) := by
    intro v
    rw [Finset.mul_sum]
    have hm : G.mass v ≠ 0 := (G.mass_pos v).ne'
    field_simp
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  simp_rw [hcancel]
  have hswap : ∑ v, ∑ u, G.conductance v u * (f v * (f v - f u)) =
      ∑ v, ∑ u, G.conductance v u * (f u * (f u - f v)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
    rw [G.conductance_symm u v]
  have h2 : 2 * ∑ v, ∑ u, G.conductance v u * (f v * (f v - f u)) =
      ∑ v, ∑ u, G.conductance v u * (f v - f u) ^ 2 := by
    rw [two_mul]
    nth_rewrite 2 [hswap]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  linarith

/-- Row-wise triangle inequality for the heat kernel. -/
theorem heatApply_abs_le_sum (t : ℝ) (ht : 0 ≤ t) (f : V → ℝ) (v : V) :
    |G.heatApply t f v| ≤ ∑ u, G.heatKernel t v u * |f u| := by
  have hnonneg := (G.heatKernel_rowStochastic t ht).1
  unfold heatApply
  calc |∑ u, G.heatKernel t v u * f u|
      ≤ ∑ u, |G.heatKernel t v u * f u| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ u, G.heatKernel t v u * |f u| := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [abs_mul, abs_of_nonneg (hnonneg v u)]

/-- Jensen on a stochastic row: `|e^{-tΔ} f (v)|^q ≤ ∑_u K_t(v,u) |f(u)|^q`
for `q ≥ 1`. -/
theorem heatApply_abs_rpow_le (t : ℝ) (ht : 0 ≤ t) (f : V → ℝ) (v : V)
    {q : ℝ} (hq : 1 ≤ q) :
    |G.heatApply t f v| ^ q ≤ ∑ u, G.heatKernel t v u * |f u| ^ q := by
  have hnonneg := (G.heatKernel_rowStochastic t ht).1
  have hrow := (G.heatKernel_rowStochastic t ht).2 v
  calc |G.heatApply t f v| ^ q
      ≤ (∑ u, G.heatKernel t v u * |f u|) ^ q :=
        Real.rpow_le_rpow (abs_nonneg _) (G.heatApply_abs_le_sum t ht f v)
          (by linarith)
    _ ≤ ∑ u, G.heatKernel t v u * |f u| ^ q := by
        have hJ := (convexOn_rpow hq).map_sum_le (t := Finset.univ)
          (w := fun u => G.heatKernel t v u) (p := fun u => |f u|)
          (fun u _ => hnonneg v u) hrow (fun u _ => abs_nonneg (f u))
        simpa [smul_eq_mul] using hJ

/-- `L^q(μ)` contraction of the heat semigroup, `1 ≤ q < ∞`:
`∑_v μ_v |e^{-tΔ} f (v)|^q ≤ ∑_v μ_v |f(v)|^q`. -/
theorem heatApply_weightedLq_le (t : ℝ) (ht : 0 ≤ t) (f : V → ℝ)
    {q : ℝ} (hq : 1 ≤ q) :
    ∑ v, G.mass v * |G.heatApply t f v| ^ q ≤ ∑ v, G.mass v * |f v| ^ q := by
  calc ∑ v, G.mass v * |G.heatApply t f v| ^ q
      ≤ ∑ v, G.mass v * ∑ u, G.heatKernel t v u * |f u| ^ q := by
        refine Finset.sum_le_sum fun v _ => ?_
        exact mul_le_mul_of_nonneg_left (G.heatApply_abs_rpow_le t ht f v hq)
          (G.mass_pos v).le
    _ = ∑ u, (∑ v, G.mass v * G.heatKernel t v u) * |f u| ^ q := by
        calc ∑ v, G.mass v * ∑ u, G.heatKernel t v u * |f u| ^ q
            = ∑ v, ∑ u, (G.mass v * G.heatKernel t v u) * |f u| ^ q := by
              refine Finset.sum_congr rfl fun v _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun u _ => ?_
              ring
          _ = ∑ u, ∑ v, (G.mass v * G.heatKernel t v u) * |f u| ^ q :=
              Finset.sum_comm
          _ = ∑ u, (∑ v, G.mass v * G.heatKernel t v u) * |f u| ^ q := by
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [Finset.sum_mul]
    _ = ∑ u, G.mass u * |f u| ^ q := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [G.heatKernel_weightedColumnSum t ht u]

/-- `L^∞` contraction of the heat semigroup: a uniform bound on `f` is a
uniform bound on `e^{-tΔ} f`. -/
theorem heatApply_sup_le (t : ℝ) (ht : 0 ≤ t) (f : V → ℝ) (M : ℝ)
    (hM : ∀ u, |f u| ≤ M) (v : V) : |G.heatApply t f v| ≤ M := by
  have hnonneg := (G.heatKernel_rowStochastic t ht).1
  have hrow := (G.heatKernel_rowStochastic t ht).2 v
  calc |G.heatApply t f v|
      ≤ ∑ u, G.heatKernel t v u * |f u| := G.heatApply_abs_le_sum t ht f v
    _ ≤ ∑ u, G.heatKernel t v u * M := by
        refine Finset.sum_le_sum fun u _ => ?_
        exact mul_le_mul_of_nonneg_left (hM u) (hnonneg v u)
    _ = M := by rw [← Finset.sum_mul, hrow, one_mul]

end FiniteWeightedGraph
end RenewalGeometry
