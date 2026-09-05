/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.TracePowFormulaExact

/-!
# The entropy limit of the dyadic trace interpolation

Step (D4j) of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: the relative entropy is the derivative of
the dyadic trace interpolation at zero,

`(Tr ρ − Re Tr(ρ^{1−t} σ^t))/t → D(ρ‖σ)` along `t = 2⁻ᵏ`.

* `slope_tendsto`: the per-eigenpair scalar limit, by the exponential
  derivative;
* `relEntropy_tendsto`: **the entropy limit**, summing the finitely many
  eigenpair slopes.
-/

open Matrix Unitary Finset Filter Topology
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ρ σ : Matrix n n ℂ}

/-! ### The scalar slope limit -/

theorem slope_tendsto (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    Tendsto (fun k : ℕ =>
      (p - p ^ (1 - (2 : ℝ)⁻¹ ^ k) * q ^ ((2 : ℝ)⁻¹ ^ k)) /
        ((2 : ℝ)⁻¹ ^ k))
      atTop (𝓝 (p * Real.log p - p * Real.log q)) := by
  rcases eq_or_lt_of_le hp with h0 | hppos
  · -- vanishing eigenvalue: the terms are eventually zero
    rw [← h0]
    have hev : ∀ᶠ k : ℕ in atTop,
        ((0 : ℝ) - (0 : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ k) *
          q ^ ((2 : ℝ)⁻¹ ^ k)) / ((2 : ℝ)⁻¹ ^ k) = 0 := by
      filter_upwards [eventually_ge_atTop 1] with k hk
      have ht1 : (2 : ℝ)⁻¹ ^ k < 1 := by
        calc (2 : ℝ)⁻¹ ^ k ≤ (2 : ℝ)⁻¹ ^ 1 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
          _ < 1 := by norm_num
      rw [Real.zero_rpow (by linarith : 1 - (2 : ℝ)⁻¹ ^ k ≠ 0)]
      simp
    have hgoal : (0 : ℝ) * Real.log 0 - 0 * Real.log q = 0 := by ring
    rw [hgoal]
    have heq : (fun k : ℕ =>
        ((0 : ℝ) - (0 : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ k) *
          q ^ ((2 : ℝ)⁻¹ ^ k)) / ((2 : ℝ)⁻¹ ^ k)) =ᶠ[atTop]
        fun _ => (0 : ℝ) := hev
    exact Tendsto.congr' heq.symm tendsto_const_nhds
  · -- positive eigenvalue: the exponential derivative
    set c : ℝ := Real.log q - Real.log p with hc
    have hterm : ∀ t : ℝ, p ^ (1 - t) * q ^ t = p * Real.exp (t * c) := by
      intro t
      rw [Real.rpow_def_of_pos hppos, Real.rpow_def_of_pos hq,
        ← Real.exp_add]
      rw [show p * Real.exp (t * c) = Real.exp (Real.log p + t * c) from by
        rw [Real.exp_add, Real.exp_log hppos]]
      congr 1
      rw [hc]
      ring
    have hderiv : HasDerivAt (fun t : ℝ => p * Real.exp (t * c))
        (p * c) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t * c) c 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).mul_const c
      have h2 := h1.exp
      have h3 := h2.const_mul p
      simpa using h3
    have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
    have hseq : Tendsto (fun k : ℕ => (2 : ℝ)⁻¹ ^ k) atTop
        (𝓝[≠] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
        (by norm_num), Eventually.of_forall fun k => ?_⟩
      exact (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k).ne'
    have hcomp := (hslope.comp hseq).neg
    have hgoal : p * Real.log p - p * Real.log q = -(p * c) := by
      rw [hc]
      ring
    rw [hgoal]
    refine hcomp.congr fun k => ?_
    have hs : slope (fun t : ℝ => p * Real.exp (t * c)) 0
        ((2 : ℝ)⁻¹ ^ k) =
        (p * Real.exp (((2 : ℝ)⁻¹ ^ k) * c) - p) / ((2 : ℝ)⁻¹ ^ k) := by
      rw [slope_def_field]
      simp [sub_zero]
    change -(slope (fun t : ℝ => p * Real.exp (t * c)) 0
      ((2 : ℝ)⁻¹ ^ k)) = _
    rw [hs, hterm]
    rw [← neg_div, neg_sub]

/-! ### The entropy limit -/

set_option maxHeartbeats 1600000 in -- eigenpair sum of slopes
/-- **The entropy limit**:
`(Tr ρ − Re Tr(ρ^{1−t} σ^t))/t → D(ρ‖σ)` along `t = 2⁻ᵏ`. -/
theorem relEntropy_tendsto (hρp : ρ.PosSemidef) (hσp : σ.PosDef) :
    Tendsto (fun k : ℕ =>
      ((ρ.trace).re - tracePow hρp.1 hσp.1 ((2 : ℝ)⁻¹ ^ k)) /
        ((2 : ℝ)⁻¹ ^ k))
      atTop (𝓝 (relEntropy hρp.1 hσp.1)) := by
  have hform : ∀ k : ℕ,
      ((ρ.trace).re - tracePow hρp.1 hσp.1 ((2 : ℝ)⁻¹ ^ k)) /
        ((2 : ℝ)⁻¹ ^ k) =
      ∑ i, ∑ j, ((hρp.1.eigenvalues i -
        (hρp.1.eigenvalues i) ^ (1 - (2 : ℝ)⁻¹ ^ k) *
        (hσp.1.eigenvalues j) ^ ((2 : ℝ)⁻¹ ^ k)) /
        ((2 : ℝ)⁻¹ ^ k)) *
        Complex.normSq (overlap hρp.1 hσp.1 i j) := by
    intro k
    rw [numerator_spread, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hD : relEntropy hρp.1 hσp.1 =
      ∑ i, ∑ j, (hρp.1.eigenvalues i *
        Real.log (hρp.1.eigenvalues i) -
        hρp.1.eigenvalues i * Real.log (hσp.1.eigenvalues j)) *
        Complex.normSq (overlap hρp.1 hσp.1 i j) := by
    rw [relEntropy_eq_klein_sum]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  rw [hD]
  refine Tendsto.congr (fun k => (hform k).symm) ?_
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  exact (slope_tendsto _ _ (hρp.eigenvalues_nonneg i)
    (hσp.eigenvalues_pos j)).mul_const _

end QRE
end NCG
