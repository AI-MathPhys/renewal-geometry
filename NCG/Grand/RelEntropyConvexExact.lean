/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.LiebLimitExact

/-!
# Joint convexity of the finite quantum relative entropy

Step (D4k) of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: passing the dyadic Lieb concavity
inequalities to the entropy limit yields **joint convexity**,

`D(Σλ ρ_j ‖ Σλ σ_j) ≤ Σ λ_j D(ρ_j‖σ_j)`,

for positive definite data.

* `relEntropy_convex_posDef`: **joint convexity of the relative
  entropy** (Lieb–Lindblad), by dyadic approximation.
-/

open Matrix Unitary Finset Filter Topology
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1600000 in -- limit passage of the Lieb chain
/-- **Joint convexity of the finite quantum relative entropy**
(Lieb–Lindblad): `D(Σλ ρ_j ‖ Σλ σ_j) ≤ Σ λ_j D(ρ_j‖σ_j)` for positive
definite data. -/
theorem relEntropy_convex_posDef {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ j, 0 ≤ lam j)
    {ρmat σmat : ι → Matrix n n ℂ}
    (hρj : ∀ j, (ρmat j).PosDef) (hσj : ∀ j, (σmat j).PosDef)
    (hρbar : (∑ j, lam j • ρmat j).PosDef)
    (hσbar : (∑ j, lam j • σmat j).PosDef) :
    relEntropy hρbar.1 hσbar.1 ≤
      ∑ j, lam j * relEntropy (hρj j).1 (hσj j).1 := by
  have htr : ((∑ j, lam j • ρmat j).trace).re =
      ∑ j, lam j * ((ρmat j).trace).re := by
    rw [Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.trace_smul, Complex.real_smul, Complex.mul_re]
    simp
  have hineq : ∀ k : ℕ,
      (((∑ j, lam j • ρmat j).trace).re -
        tracePow hρbar.1 hσbar.1 ((2 : ℝ)⁻¹ ^ k)) / ((2 : ℝ)⁻¹ ^ k) ≤
      ∑ j, lam j * ((((ρmat j).trace).re -
        tracePow (hρj j).1 (hσj j).1 ((2 : ℝ)⁻¹ ^ k)) /
        ((2 : ℝ)⁻¹ ^ k)) := by
    intro k
    have hlieb := lieb_dyadic hlam hρj (fun j => (hσj j).posSemidef)
      hρbar hσbar.posSemidef k
    have htk : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
    have hRHS : ∑ j, lam j * ((((ρmat j).trace).re -
        tracePow (hρj j).1 (hσj j).1 ((2 : ℝ)⁻¹ ^ k)) /
        ((2 : ℝ)⁻¹ ^ k)) =
        ((∑ j, lam j * ((ρmat j).trace).re) -
          ∑ j, lam j * tracePow (hρj j).1 (hσj j).1 ((2 : ℝ)⁻¹ ^ k)) /
          ((2 : ℝ)⁻¹ ^ k) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hRHS, htr]
    gcongr
  have hL := relEntropy_tendsto hρbar.posSemidef hσbar
  have hR : Tendsto (fun k : ℕ => ∑ j, lam j *
      ((((ρmat j).trace).re -
        tracePow (hρj j).1 (hσj j).1 ((2 : ℝ)⁻¹ ^ k)) /
        ((2 : ℝ)⁻¹ ^ k)))
      atTop (𝓝 (∑ j, lam j * relEntropy (hρj j).1 (hσj j).1)) := by
    refine tendsto_finsetSum _ fun j _ => ?_
    exact (relEntropy_tendsto (hρj j).posSemidef (hσj j)).const_mul _
  exact le_of_tendsto_of_tendsto' hL hR hineq

end QRE
end NCG
