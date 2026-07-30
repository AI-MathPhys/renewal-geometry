/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The renewal flat slicing as a planar de Sitter chart
  (`prop:planar-desitter-chart`, GR_emergence)

The explicit embedding of the flat FLRW slicing
`ds² = -dt² + e^{2Ht}δᵢⱼdxⁱdxʲ` into the de Sitter hyperboloid:

  `X₀ = H⁻¹sinh(Ht) + (H/2)e^{Ht}|x|²`,
  `Xᵢ = e^{Ht}xᵢ`,
  `X_{d+1} = H⁻¹cosh(Ht) - (H/2)e^{Ht}|x|²`.

* `dsChart_on_hyperboloid` — the image satisfies
  `-X₀² + Σᵢ Xᵢ² + X_{d+1}² = H⁻²`;
* `dsChart_planar_patch` — `X₀ + X_{d+1} = H⁻¹e^{Ht} > 0`: the image
  is the expanding planar region;
* `dsChart_pullback_metric` — the pullback of the ambient Minkowski
  form along the explicit differentials equals the flat-slicing FLRW
  metric `-dt² + e^{2Ht}Σᵢ dxᵢ²` (so the chart is an isometry onto
  its image).

All three are exact algebra from `cosh² - sinh² = 1` and
`sinh + cosh = exp`.  Geodesic incompleteness of the slicing (the
patch is proper) is the global statement `X₀ + X_{d+1} > 0`, which
excludes the contracting half.
-/

namespace NCG

open Real

variable {d : ℕ}

/-- Embedding time component. -/
noncomputable def dsX0 (H t : ℝ) (x : Fin d → ℝ) : ℝ :=
  H⁻¹ * Real.sinh (H * t) + H / 2 * Real.exp (H * t) * ∑ i, x i ^ 2

/-- Embedding spatial components. -/
noncomputable def dsXi (H t : ℝ) (x : Fin d → ℝ) (i : Fin d) : ℝ :=
  Real.exp (H * t) * x i

/-- Embedding last component. -/
noncomputable def dsXlast (H t : ℝ) (x : Fin d → ℝ) : ℝ :=
  H⁻¹ * Real.cosh (H * t) - H / 2 * Real.exp (H * t) * ∑ i, x i ^ 2

/-- `prop:planar-desitter-chart` (hyperboloid): the image lies on
the de Sitter hyperboloid of radius `H⁻¹`. -/
theorem dsChart_on_hyperboloid {H : ℝ} (hH : H ≠ 0) (t : ℝ)
    (x : Fin d → ℝ) :
    -(dsX0 H t x) ^ 2 + (∑ i, dsXi H t x i ^ 2)
      + (dsXlast H t x) ^ 2 = (H ^ 2)⁻¹ := by
  have hcs : Real.cosh (H * t) ^ 2 - Real.sinh (H * t) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (H * t)
  have hsc : Real.sinh (H * t) + Real.cosh (H * t)
      = Real.exp (H * t) := Real.sinh_add_cosh (H * t)
  have hsum : ∑ i, dsXi H t x i ^ 2
      = Real.exp (H * t) ^ 2 * ∑ i, x i ^ 2 := by
    unfold dsXi
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold dsX0 dsXlast
  rw [hsum]
  set c : ℝ := Real.cosh (H * t)
  set s : ℝ := Real.sinh (H * t)
  set e : ℝ := Real.exp (H * t)
  set r2 : ℝ := ∑ i, x i ^ 2
  field_simp
  linear_combination 4 * hcs + (-(4 * H ^ 2 * e * r2)) * hsc

/-- `prop:planar-desitter-chart` (planar patch): the image lies in
the expanding region `X₀ + X_{d+1} = H⁻¹e^{Ht} > 0`. -/
theorem dsChart_planar_patch {H : ℝ} (hH : 0 < H) (t : ℝ)
    (x : Fin d → ℝ) :
    dsX0 H t x + dsXlast H t x = H⁻¹ * Real.exp (H * t) ∧
      0 < dsX0 H t x + dsXlast H t x := by
  have hsc : Real.sinh (H * t) + Real.cosh (H * t)
      = Real.exp (H * t) := Real.sinh_add_cosh (H * t)
  constructor
  · unfold dsX0 dsXlast
    rw [← hsc]
    ring
  · unfold dsX0 dsXlast
    rw [show H⁻¹ * Real.sinh (H * t)
        + H / 2 * Real.exp (H * t) * ∑ i, x i ^ 2
        + (H⁻¹ * Real.cosh (H * t)
        - H / 2 * Real.exp (H * t) * ∑ i, x i ^ 2)
        = H⁻¹ * (Real.sinh (H * t) + Real.cosh (H * t)) from by ring,
      hsc]
    positivity

/-- `prop:planar-desitter-chart` (isometry): along the explicit
differentials, the ambient Minkowski quadratic form pulls back to
the flat-slicing FLRW metric `-dt² + e^{2Ht}Σdxᵢ²`. -/
theorem dsChart_pullback_metric {H : ℝ} (t : ℝ)
    (x : Fin d → ℝ) (dt : ℝ) (dx : Fin d → ℝ) :
    -((Real.cosh (H * t) + H ^ 2 / 2 * Real.exp (H * t)
          * ∑ i, x i ^ 2) * dt
        + H * Real.exp (H * t) * ∑ i, x i * dx i) ^ 2
      + (∑ i, (H * Real.exp (H * t) * x i * dt
          + Real.exp (H * t) * dx i) ^ 2)
      + ((Real.sinh (H * t) - H ^ 2 / 2 * Real.exp (H * t)
          * ∑ i, x i ^ 2) * dt
        - H * Real.exp (H * t) * ∑ i, x i * dx i) ^ 2
      = -dt ^ 2 + Real.exp (H * t) ^ 2 * ∑ i, dx i ^ 2 := by
  set c : ℝ := Real.cosh (H * t) with hc
  set s : ℝ := Real.sinh (H * t) with hs
  set e : ℝ := Real.exp (H * t) with he
  have hcs : c ^ 2 - s ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq (H * t)
  have hsc : s + c = e := Real.sinh_add_cosh (H * t)
  have hmid : ∑ i, (H * e * x i * dt + e * dx i) ^ 2
      = H ^ 2 * e ^ 2 * dt ^ 2 * (∑ i, x i ^ 2)
        + 2 * H * e ^ 2 * dt * (∑ i, x i * dx i)
        + e ^ 2 * (∑ i, dx i ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hmid]
  set r2 : ℝ := ∑ i, x i ^ 2
  set P : ℝ := ∑ i, x i * dx i
  set Q : ℝ := ∑ i, dx i ^ 2
  linear_combination (-(dt ^ 2)) * hcs
    - (H ^ 2 * e * r2 * dt ^ 2 + 2 * dt * H * e * P) * hsc

end NCG
