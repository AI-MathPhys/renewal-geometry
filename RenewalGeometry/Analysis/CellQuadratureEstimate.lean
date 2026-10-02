/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Cell quadrature on finite measurable partitions

General error bounds for one-point (e.g. midpoint) quadrature rules on a finite family of
pairwise disjoint measurable cells.  Used for the Palatini first-variation part of
`thm:supp-finite-defects` (emergent-spacetime manuscript), where the midpoint quadrature of a
Lipschitz density on `O(h⁻⁴)` four-dimensional cells of diameter `O(h)` has total error `O(h)`.

* `CellQuadrature.abs_sum_sub_setIntegral_le`: if on every cell `cᵢ` the integrand stays within
  `η` of the cell value `qᵢ`, then `|∑ᵢ |cᵢ| qᵢ − ∫_{⋃ cᵢ} f| ≤ η |⋃ cᵢ|`.
* `CellQuadrature.abs_sum_sub_setIntegral_le_of_lipschitz`: the Lipschitz form: if
  `|f y − f(xᵢ)| ≤ L dist(y, xᵢ)` on `cᵢ`, every point of `cᵢ` lies within `δ` of the quadrature
  point `xᵢ`, and the cell values `qᵢ` are within `ε` of `f(xᵢ)`, the error is
  `≤ (L δ + ε) |⋃ cᵢ|`.
-/

namespace RenewalGeometry.CellQuadrature

open MeasureTheory Set

variable {X ι : Type*} [MeasurableSpace X] (μ : Measure X)

/-- **Cell quadrature error**: on a finite family of pairwise disjoint measurable cells of finite
measure, if `|f y − qᵢ| ≤ η` for every `y ∈ cᵢ`, the one-point rule `∑ᵢ μ(cᵢ) qᵢ` approximates
`∫_{⋃ cᵢ} f dμ` to within `η μ(⋃ cᵢ)`. -/
theorem abs_sum_sub_setIntegral_le (s : Finset ι) (c : ι → Set X)
    (hmeas : ∀ i ∈ s, MeasurableSet (c i)) (hdisj : Set.Pairwise (↑s) (Function.onFun Disjoint c))
    (hfin : ∀ i ∈ s, μ (c i) < ⊤) (f : X → ℝ) (hint : ∀ i ∈ s, IntegrableOn f (c i) μ)
    (q : ι → ℝ) (η : ℝ) (hη : ∀ i ∈ s, ∀ y ∈ c i, |f y - q i| ≤ η) :
    |∑ i ∈ s, μ.real (c i) * q i - ∫ y in ⋃ i ∈ s, c i, f y ∂μ|
      ≤ η * μ.real (⋃ i ∈ s, c i) := by
  rw [integral_biUnion_finset s hmeas hdisj hint,
    measureReal_biUnion_finset hdisj hmeas (fun i hi => (hfin i hi).ne), Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hconst : ∫ _ in c i, q i ∂μ = μ.real (c i) * q i := by
    rw [setIntegral_const, smul_eq_mul]
  have hq : IntegrableOn (fun _ => q i) (c i) μ := integrableOn_const (hfin i hi).ne
  rw [← hconst, ← integral_sub hq (hint i hi)]
  have := norm_setIntegral_le_of_norm_le_const (μ := μ) (f := fun y => q i - f y) (hfin i hi)
    (C := η) fun y hy => by rw [Real.norm_eq_abs, abs_sub_comm]; exact hη i hi y hy
  rw [Real.norm_eq_abs] at this
  linarith

/-- **Lipschitz cell quadrature**: if `f` is `L`-Lipschitz towards the quadrature point `xᵢ` on
each cell, every point of `cᵢ` lies within `δ` of `xᵢ`, and the cell values `qᵢ` are `ε`-close
to `f(xᵢ)`, then `|∑ᵢ μ(cᵢ) qᵢ − ∫_{⋃ cᵢ} f| ≤ (L δ + ε) μ(⋃ cᵢ)`. -/
theorem abs_sum_sub_setIntegral_le_of_lipschitz [PseudoMetricSpace X] (s : Finset ι)
    (c : ι → Set X) (hmeas : ∀ i ∈ s, MeasurableSet (c i))
    (hdisj : Set.Pairwise (↑s) (Function.onFun Disjoint c)) (hfin : ∀ i ∈ s, μ (c i) < ⊤) (f : X → ℝ)
    (hint : ∀ i ∈ s, IntegrableOn f (c i) μ) (x : ι → X) {L δ ε : ℝ} (hL : 0 ≤ L)
    (hδ : ∀ i ∈ s, ∀ y ∈ c i, dist y (x i) ≤ δ)
    (hf : ∀ i ∈ s, ∀ y ∈ c i, |f y - f (x i)| ≤ L * dist y (x i))
    (q : ι → ℝ) (hq : ∀ i ∈ s, |f (x i) - q i| ≤ ε) :
    |∑ i ∈ s, μ.real (c i) * q i - ∫ y in ⋃ i ∈ s, c i, f y ∂μ|
      ≤ (L * δ + ε) * μ.real (⋃ i ∈ s, c i) := by
  refine abs_sum_sub_setIntegral_le μ s c hmeas hdisj hfin f hint q _ fun i hi y hy => ?_
  calc |f y - q i| = |(f y - f (x i)) + (f (x i) - q i)| := by ring_nf
    _ ≤ |f y - f (x i)| + |f (x i) - q i| := abs_add_le _ _
    _ ≤ L * dist y (x i) + ε := add_le_add (hf i hi y hy) (hq i hi)
    _ ≤ L * δ + ε := by gcongr; exact hδ i hi y hy

end RenewalGeometry.CellQuadrature
