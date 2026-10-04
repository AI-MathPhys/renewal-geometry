/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.UnitCubeRiemannSum

/-!
# Quantitative Riemann-sum error for Lipschitz and `C¹` densities on the unit cube

The quadrature step of `prop:mesh-consistency` (Einstein–Standard-Model action-closure
manuscript, "A Riemann sum over cells of volume `O(h⁴)` has `O(h⁻⁴)` terms on a fixed region, so
the integrated error is `O(h)`, not an extensive error").  On the uniform grid of mesh
`h = 1/M` of the unit cube `[0,1]^d` (cells `Π_i [k_i h, (k_i+1) h)`, left-endpoint nodes
`gridPoint M k = k h`, see `UnitCubeRiemannSum`), for a Banach-valued density `g`:

* `setIntegral_Icc_eq_sum_cell_of_integrableOn`: `∫_{[0,1]^d} g = Σ_k ∫_{cell k} g` for
  integrable `g` (no continuity needed);
* `norm_riemannSum_sub_integral_le` (**Lipschitz quadrature**): if `g` is `L`-Lipschitz on the
  cube (sup metric of `Fin d → ℝ`), then `‖h^d Σ_k g(kh) - ∫ g‖ ≤ L h`;
* `norm_riemannSum_sub_integral_le_of_fderiv` (**`C¹` quadrature**): if `g` has a derivative
  (within the cube) of operator norm `≤ B`, then `‖h^d Σ_k g(kh) - ∫ g‖ ≤ B h`;
* `norm_perturbed_riemannSum_sub_integral_le` (**pointwise consistency + quadrature**): if the
  discrete cell densities `g_h(k)` satisfy `‖g_h(k) - g(kh)‖ ≤ ε`, then
  `‖h^d Σ_k g_h(k) - ∫ g‖ ≤ ε + L h`; with `ε = C h` this is the non-extensive `O(h)` integrated
  error of the manuscript.

Norms: the sup norm on `Fin d → ℝ` (Mathlib's default), so `L`, `B` are sup-norm Lipschitz /
operator-norm constants; any other norm changes the constants by a dimensional factor.
-/

open MeasureTheory Set Filter Topology Finset
open scoped NNReal

namespace RenewalGeometry.LipschitzRiemannSum

open UnitCubeRiemannSum

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The integral over the closed cube is the sum of the cell integrals (integrable densities). -/
theorem setIntegral_Icc_eq_sum_cell_of_integrableOn {M : ℕ} (hM : 0 < M)
    (g : (Fin d → ℝ) → E) (hg : IntegrableOn g (Icc (0 : Fin d → ℝ) 1)) :
    ∫ x in Icc (0 : Fin d → ℝ) 1, g x = ∑ k : Fin d → Fin M, ∫ x in cell M k, g x := by
  have hae : (Icc (0 : Fin d → ℝ) 1 : Set (Fin d → ℝ)) =ᵐ[volume]
      (pi univ fun _ => Ico (0 : ℝ) 1) :=
    (Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin d => (volume : Measure ℝ))
      (f := (0 : Fin d → ℝ)) (g := 1)).symm
  rw [setIntegral_congr_set hae, ← iUnion_cell hM,
    integral_iUnion (fun k => measurableSet_cell M k) (pairwise_disjoint_cell hM)
      (hg.mono_set (by
        rw [iUnion_cell hM]
        exact fun x hx => ⟨fun i => (hx i (mem_univ i)).1, fun i => (hx i (mem_univ i)).2.le⟩)),
    tsum_fintype]

/-- One-cell error for a Banach-valued density: `‖∫_{cell} g - h^d g(x_k)‖ ≤ ε h^d` when `g`
varies by at most `ε` from its node value on the cell. -/
theorem norm_setIntegral_cell_sub_le {M : ℕ} (hM : 0 < M) (g : (Fin d → ℝ) → E)
    (hg : IntegrableOn g (Icc (0 : Fin d → ℝ) 1)) (k : Fin d → Fin M) {ε : ℝ}
    (hε : ∀ x ∈ cell M k, ‖g x - g (gridPoint M k)‖ ≤ ε) :
    ‖(∫ x in cell M k, g x) - (1 / (M : ℝ)) ^ d • g (gridPoint M k)‖ ≤
      ε * (1 / (M : ℝ)) ^ d := by
  have hint : IntegrableOn g (cell M k) volume := hg.mono_set (cell_subset_Icc hM k)
  have hsub : (∫ x in cell M k, g x) - (1 / (M : ℝ)) ^ d • g (gridPoint M k) =
      ∫ x in cell M k, (g x - g (gridPoint M k)) := by
    rw [integral_sub hint (integrableOn_const (volume_cell_lt_top hM k).ne),
      setIntegral_const, volume_real_cell hM k]
  rw [hsub, ← volume_real_cell hM k]
  exact norm_setIntegral_le_of_norm_le_const (volume_cell_lt_top hM k) hε

/-- The node weights sum to one: `M^d · h^d = 1`. -/
theorem card_mul_cellVolume {M : ℕ} (hM : 0 < M) :
    ((Fintype.card (Fin d → Fin M) : ℕ) : ℝ) * (1 / (M : ℝ)) ^ d = 1 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow, ← mul_pow,
    mul_one_div_cancel hM'.ne', one_pow]

/-- **Quadrature with pointwise control**: if on every cell `g` stays within `ε` of its node
value, then `‖h^d Σ_k g(kh) - ∫_{[0,1]^d} g‖ ≤ ε`. -/
theorem norm_riemannSum_sub_integral_le_of_cell {M : ℕ} (hM : 0 < M) (g : (Fin d → ℝ) → E)
    (hg : IntegrableOn g (Icc (0 : Fin d → ℝ) 1)) {ε : ℝ}
    (hε : ∀ k : Fin d → Fin M, ∀ x ∈ cell M k, ‖g x - g (gridPoint M k)‖ ≤ ε) :
    ‖(1 / (M : ℝ)) ^ d • ∑ k : Fin d → Fin M, g (gridPoint M k) -
        ∫ x in Icc (0 : Fin d → ℝ) 1, g x‖ ≤ ε := by
  rw [setIntegral_Icc_eq_sum_cell_of_integrableOn hM g hg, Finset.smul_sum,
    ← Finset.sum_sub_distrib]
  calc ‖∑ k : Fin d → Fin M, ((1 / (M : ℝ)) ^ d • g (gridPoint M k) - ∫ x in cell M k, g x)‖
      ≤ ∑ k : Fin d → Fin M, ε * (1 / (M : ℝ)) ^ d := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_sub_rev]
        exact norm_setIntegral_cell_sub_le hM g hg k (hε k)
    _ = ε := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm ε, ← mul_assoc,
          card_mul_cellVolume hM, one_mul]

/-- **Quantitative Riemann sums for Lipschitz densities**: if `g` is `L`-Lipschitz on the unit
cube, then `‖h^d Σ_k g(kh) - ∫_{[0,1]^d} g‖ ≤ L h`, `h = 1/M`. -/
theorem norm_riemannSum_sub_integral_le {M : ℕ} (hM : 0 < M) {g : (Fin d → ℝ) → E} {L : ℝ≥0}
    (hg : LipschitzOnWith L g (Icc (0 : Fin d → ℝ) 1)) :
    ‖(1 / (M : ℝ)) ^ d • ∑ k : Fin d → Fin M, g (gridPoint M k) -
        ∫ x in Icc (0 : Fin d → ℝ) 1, g x‖ ≤ L * (1 / (M : ℝ)) := by
  have hint : IntegrableOn g (Icc (0 : Fin d → ℝ) 1) :=
    hg.continuousOn.integrableOn_compact isCompact_Icc
  refine norm_riemannSum_sub_integral_le_of_cell hM g hint fun k x hx => ?_
  rw [← dist_eq_norm]
  refine (hg.dist_le_mul x (cell_subset_Icc hM k hx) _ (gridPoint_mem_Icc hM k)).trans ?_
  exact mul_le_mul_of_nonneg_left (dist_lt_of_mem_cell hM k hx).le L.coe_nonneg

/-- **Quantitative Riemann sums for `C¹` densities**: if `g` has derivatives `g' x` within the
cube with `‖g' x‖ ≤ B`, then `‖h^d Σ_k g(kh) - ∫_{[0,1]^d} g‖ ≤ B h`. -/
theorem norm_riemannSum_sub_integral_le_of_fderiv {M : ℕ} (hM : 0 < M) {g : (Fin d → ℝ) → E}
    {g' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] E} {B : ℝ}
    (hg : ∀ x ∈ Icc (0 : Fin d → ℝ) 1, HasFDerivWithinAt g (g' x) (Icc 0 1) x)
    (hB : ∀ x ∈ Icc (0 : Fin d → ℝ) 1, ‖g' x‖ ≤ B) :
    ‖(1 / (M : ℝ)) ^ d • ∑ k : Fin d → Fin M, g (gridPoint M k) -
        ∫ x in Icc (0 : Fin d → ℝ) 1, g x‖ ≤ B * (1 / (M : ℝ)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
  have hL : LipschitzOnWith B.toNNReal g (Icc (0 : Fin d → ℝ) 1) :=
    (convex_Icc (0 : Fin d → ℝ) 1).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le hg fun x hx => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hB0]
      exact hB x hx
  have := norm_riemannSum_sub_integral_le hM hL
  rwa [Real.coe_toNNReal _ hB0] at this

/-- **Pointwise consistency plus quadrature**: if the discrete cell densities satisfy
`‖g_h(k) - g(kh)‖ ≤ ε` at every node and `g` is `L`-Lipschitz on the cube, then
`‖h^d Σ_k g_h(k) - ∫_{[0,1]^d} g‖ ≤ ε + L h`.  With `ε = C h` the integrated error is `O(h)`
(the `O(h⁻⁴)` node terms carry the weight `h⁴`), as in the proof of `prop:mesh-consistency`. -/
theorem norm_perturbed_riemannSum_sub_integral_le {M : ℕ} (hM : 0 < M)
    {g : (Fin d → ℝ) → E} {L : ℝ≥0} (hg : LipschitzOnWith L g (Icc (0 : Fin d → ℝ) 1))
    (gh : (Fin d → Fin M) → E) {ε : ℝ} (hε : ∀ k, ‖gh k - g (gridPoint M k)‖ ≤ ε) :
    ‖(1 / (M : ℝ)) ^ d • ∑ k : Fin d → Fin M, gh k - ∫ x in Icc (0 : Fin d → ℝ) 1, g x‖ ≤
      ε + L * (1 / (M : ℝ)) := by
  have hε0 : 0 ≤ ε := by
    have : Nonempty (Fin d → Fin M) := ⟨fun _ => ⟨0, hM⟩⟩
    obtain ⟨k⟩ := this
    exact (norm_nonneg _).trans (hε k)
  have hsplit : (1 / (M : ℝ)) ^ d • ∑ k : Fin d → Fin M, gh k - ∫ x in Icc (0 : Fin d → ℝ) 1, g x
      = (1 / (M : ℝ)) ^ d • ∑ k : Fin d → Fin M, (gh k - g (gridPoint M k)) +
        ((1 / (M : ℝ)) ^ d • ∑ k : Fin d → Fin M, g (gridPoint M k) -
          ∫ x in Icc (0 : Fin d → ℝ) 1, g x) := by
    rw [Finset.sum_sub_distrib, smul_sub]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_riemannSum_sub_integral_le hM hg))
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (1 / (M : ℝ)) ^ d * ‖∑ k : Fin d → Fin M, (gh k - g (gridPoint M k))‖
      ≤ (1 / (M : ℝ)) ^ d * ∑ _k : Fin d → Fin M, ε := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hε k)
    _ = ε := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          mul_comm ((1 / (M : ℝ)) ^ d), card_mul_cellVolume hM, one_mul]

/-- Non-vacuity / sharpness of the rate: for `g(x) = x₀` on `[0,1]` (Lipschitz constant `1`)
the left Riemann sum `h Σ_{k<M} k h = (1 - h)/2` misses `∫ = 1/2` by exactly `h/2`, so the
`O(h)` rate cannot be improved for general Lipschitz densities. -/
example : LipschitzOnWith 1 (fun x : Fin 1 → ℝ => x 0) (Icc (0 : Fin 1 → ℝ) 1) :=
  (LipschitzWith.eval (α := fun _ : Fin 1 => ℝ) 0).lipschitzOnWith

end RenewalGeometry.LipschitzRiemannSum
