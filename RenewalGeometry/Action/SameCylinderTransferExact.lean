/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Variance-sensitive source-preserving transfer
  (`lem:supp-same-cylinder-transfer`, `eq:supp-same-cylinder-transfer`,
  `eq:supp-same-cylinder-transfer-thomson`, `eq:supp-same-cylinder-variance`;
  emergent-spacetime manuscript)

Finite stage spaces `X, Y`; a source law `α ≥ 0`; a stochastic comparator
`Q x y = Q(y | x) ≥ 0` with `∑_y Q(y | x) = 1`; the reference coupling
`R(x,y) = α(x) Q(y | x)`.  Edge arrays are functions on `X × Y` supported on
the admitted support (where `R > 0`); the weighted norm is
`‖h‖²_{R⁻¹} = ∑ h² / R` (`eq:supp-same-cylinder-edge-geometry`; with Lean's
`t / 0 = 0` this is the sum over the support for arrays supported there), the
source map is `(A h)(x) = ∑_y h(x,y)`, the source average is
`c̄(x) = (Q c)(x) = ∑_y Q(y | x) c(x,y)` and the variance is
`𝒱_R(c) = ∑_{x,y} R(x,y) (c(x,y) - c̄(x))²` (`eq:supp-same-cylinder-variance`).

* `abs_sum_mul_le_of_source_null`: if `A h = 0` then
  `|∑ h c| ≤ ‖h‖_{R⁻¹} 𝒱_R(c)^{1/2}` (`eq:supp-same-cylinder-transfer`);
  the reference coupling and `Q` may be arbitrary here (only `R ≥ 0` and the
  support condition are used).
* `thomson_transfer`: the Thomson correction `h_*(x,y) = R(x,y)(u(y) - (Qu)(x))`
  built from any `u` with `𝓛_{α,Q} u = d`, where
  `𝓛_{α,Q} = diag(ρ) - Qᵀ diag(α) Q` (`eq:main-thomson-operator`), satisfies
  `A h_* = 0`, `‖h_*‖²_{R⁻¹} = ⟨d, u⟩`, and hence
  `|𝔼_{R + h_*} c - 𝔼_R c| ≤ √(⟨d, u⟩ 𝒱_R(c))`
  (`eq:supp-same-cylinder-transfer-thomson`).  For the paper's choice
  `u = 𝓛† d` with `d ∈ Ran 𝓛` one has `𝓛 u = d` and `⟨d, u⟩ = ⟨d, 𝓛† d⟩ = 𝓔_occ`
  (`eq:main-occurrence-energy`); `occurrence_energy_well_defined` shows that
  `⟨d, u⟩` is the same for every solution `u` of `𝓛 u = d`.
* `variance_le_bound_mul_mean`: if `0 ≤ c ≤ B` then `𝒱_R(c) ≤ B 𝔼_R c`.
-/

namespace RenewalGeometry
namespace SameCylinderTransfer

open Finset

noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The reference coupling `R(x,y) = α(x) Q(y | x)`. -/
def refCoupling (α : X → ℝ) (Q : X → Y → ℝ) : X → Y → ℝ := fun x y => α x * Q x y

/-- The weighted edge norm squared `‖h‖²_{R⁻¹} = ∑_{x,y} h(x,y)² / R(x,y)`
(`eq:supp-same-cylinder-edge-geometry`). -/
def invWeightNormSq (R h : X → Y → ℝ) : ℝ := ∑ x, ∑ y, h x y ^ 2 / R x y

/-- The source average `(Q c)(x) = ∑_y Q(y | x) c(x,y)`. -/
def sourceAvg (Q c : X → Y → ℝ) (x : X) : ℝ := ∑ y, Q x y * c x y

/-- The variance `𝒱_R(c) = ∑_{x,y} R(x,y) |c(x,y) - c̄(x)|²`
(`eq:supp-same-cylinder-variance`). -/
def cylVariance (R Q c : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, R x y * (c x y - sourceAvg Q c x) ^ 2

/-- First inequality of `lem:supp-same-cylinder-transfer`
(`eq:supp-same-cylinder-transfer`): if the source marginal of `h` vanishes
(`A h = 0`) and `h` is supported where `R > 0`, then
`|∑ h c| ≤ ‖h‖_{R⁻¹} 𝒱_R(c)^{1/2}`. -/
theorem abs_sum_mul_le_of_source_null (R Q h c : X → Y → ℝ)
    (hR : ∀ x y, 0 ≤ R x y) (hsupp : ∀ x y, h x y ≠ 0 → 0 < R x y)
    (hA : ∀ x, ∑ y, h x y = 0) :
    |∑ x, ∑ y, h x y * c x y|
      ≤ Real.sqrt (invWeightNormSq R h) * Real.sqrt (cylVariance R Q c) := by
  -- centre by the source average
  have hcentre : ∑ x, ∑ y, h x y * c x y
      = ∑ x, ∑ y, h x y * (c x y - sourceAvg Q c x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hA x, zero_mul, sub_zero]
  -- pointwise factorisation `h (c - c̄) = (h / √R) (√R (c - c̄))`
  set f : X × Y → ℝ := fun p => h p.1 p.2 / Real.sqrt (R p.1 p.2) with hf
  set g : X × Y → ℝ := fun p => Real.sqrt (R p.1 p.2) * (c p.1 p.2 - sourceAvg Q c p.1)
    with hg
  have hfg : ∀ x y, h x y * (c x y - sourceAvg Q c x) = f (x, y) * g (x, y) := by
    intro x y
    by_cases h0 : h x y = 0
    · simp [hf, h0]
    · have hpos := hsupp x y h0
      have hs : Real.sqrt (R x y) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
      simp only [hf, hg]
      field_simp
  have hf2 : ∀ x y, f (x, y) ^ 2 = h x y ^ 2 / R x y := by
    intro x y
    simp only [hf, div_pow, Real.sq_sqrt (hR x y)]
  have hg2 : ∀ x y, g (x, y) ^ 2 = R x y * (c x y - sourceAvg Q c x) ^ 2 := by
    intro x y
    simp only [hg, mul_pow, Real.sq_sqrt (hR x y)]
  have hsum : ∀ φ : X × Y → ℝ, ∑ x, ∑ y, φ (x, y) = ∑ p : X × Y, φ p := fun φ =>
    (Fintype.sum_prod_type' fun x y => φ (x, y)).symm
  rw [hcentre]
  simp only [hfg, hsum (fun p => f p * g p)]
  have hN : invWeightNormSq R h = ∑ p : X × Y, f p ^ 2 := by
    unfold invWeightNormSq
    simp only [← hf2]
    exact hsum (fun p => f p ^ 2)
  have hV : cylVariance R Q c = ∑ p : X × Y, g p ^ 2 := by
    unfold cylVariance
    simp only [← hg2]
    exact hsum (fun p => g p ^ 2)
  rw [hN, hV, ← Real.sqrt_mul (Finset.sum_nonneg fun p _ => sq_nonneg (f p))]
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq univ f g)

/-- The target marginal `ρ(y) = ∑_x α(x) Q(y | x)`. -/
def targetMarginal (α : X → ℝ) (Q : X → Y → ℝ) (y : Y) : ℝ := ∑ x, α x * Q x y

/-- The row average `(Q u)(x) = ∑_y Q(y | x) u(y)` of a target function. -/
def rowAvg (Q : X → Y → ℝ) (u : Y → ℝ) (x : X) : ℝ := ∑ y, Q x y * u y

/-- The source-shorted operator `𝓛_{α,Q} = diag(ρ) - Qᵀ diag(α) Q`
(`eq:main-thomson-operator`, `eq:supp-thomson-L`). -/
def thomsonOperator (α : X → ℝ) (Q : X → Y → ℝ) (u : Y → ℝ) (y : Y) : ℝ :=
  targetMarginal α Q y * u y - ∑ x, Q x y * (α x * rowAvg Q u x)

/-- The Thomson correction `h_*(x,y) = R(x,y) (u(y) - (Q u)(x))`
(`eq:supp-thomson-hstar`). -/
def thomsonCorrection (α : X → ℝ) (Q : X → Y → ℝ) (u : Y → ℝ) : X → Y → ℝ :=
  fun x y => refCoupling α Q x y * (u y - rowAvg Q u x)

omit [Fintype X] in
/-- The Thomson correction is source preserving: `A h_* = 0`. -/
theorem thomsonCorrection_source_null (α : X → ℝ) (Q : X → Y → ℝ)
    (hQ1 : ∀ x, ∑ y, Q x y = 1) (u : Y → ℝ) (x : X) :
    ∑ y, thomsonCorrection α Q u x y = 0 := by
  simp only [thomsonCorrection, refCoupling, mul_sub, Finset.sum_sub_distrib]
  have h1 : ∑ y, α x * Q x y * u y = α x * rowAvg Q u x := by
    simp only [rowAvg, Finset.mul_sum, mul_assoc]
  have h2 : ∑ y, α x * Q x y * rowAvg Q u x = α x * rowAvg Q u x := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hQ1 x, mul_one]
  rw [h1, h2, sub_self]

/-- The energy of the Thomson correction is the quadratic form of the
source-shorted operator: `‖h_*‖²_{R⁻¹} = ⟨u, 𝓛_{α,Q} u⟩`
(`eq:supp-thomson-variance`). -/
theorem invWeightNormSq_thomsonCorrection (α : X → ℝ) (Q : X → Y → ℝ)
    (hQ1 : ∀ x, ∑ y, Q x y = 1)
    (u : Y → ℝ) :
    invWeightNormSq (refCoupling α Q) (thomsonCorrection α Q u)
      = ∑ y, u y * thomsonOperator α Q u y := by
  have hpt : ∀ x y, thomsonCorrection α Q u x y ^ 2 / refCoupling α Q x y
      = refCoupling α Q x y * (u y - rowAvg Q u x) ^ 2 := by
    intro x y
    simp only [thomsonCorrection]
    by_cases h0 : refCoupling α Q x y = 0
    · simp [h0]
    · field_simp
  unfold invWeightNormSq
  simp only [hpt]
  -- expand both sides to `∑ ρ u² - ∑ α (Q u)²`
  have hL : ∑ x, ∑ y, refCoupling α Q x y * (u y - rowAvg Q u x) ^ 2
      = ∑ y, targetMarginal α Q y * u y ^ 2 - ∑ x, α x * rowAvg Q u x ^ 2 := by
    have hrow : ∀ x, ∑ y, refCoupling α Q x y * (u y - rowAvg Q u x) ^ 2
        = ∑ y, α x * Q x y * u y ^ 2 - α x * rowAvg Q u x ^ 2 := by
      intro x
      have e1 : ∑ y, α x * Q x y * u y = α x * rowAvg Q u x := by
        simp only [rowAvg, Finset.mul_sum, mul_assoc]
      have e2 : ∑ y, α x * Q x y = α x := by rw [← Finset.mul_sum, hQ1 x, mul_one]
      have : ∀ y, refCoupling α Q x y * (u y - rowAvg Q u x) ^ 2
          = α x * Q x y * u y ^ 2 - 2 * rowAvg Q u x * (α x * Q x y * u y)
            + rowAvg Q u x ^ 2 * (α x * Q x y) := by
        intro y; simp only [refCoupling]; ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2]
      ring
    simp only [hrow, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_comm]
    simp only [targetMarginal, Finset.sum_mul]
  have hR : ∑ y, u y * thomsonOperator α Q u y
      = ∑ y, targetMarginal α Q y * u y ^ 2 - ∑ x, α x * rowAvg Q u x ^ 2 := by
    simp only [thomsonOperator, mul_sub, Finset.sum_sub_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun y _ => by ring
    · simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [rowAvg, Finset.sum_mul, Finset.mul_sum, sq]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
  rw [hL, hR]

/-- `𝓛_{α,Q}` is symmetric. -/
theorem thomsonOperator_symm (α : X → ℝ) (Q : X → Y → ℝ) (u v : Y → ℝ) :
    ∑ y, v y * thomsonOperator α Q u y = ∑ y, u y * thomsonOperator α Q v y := by
  have key : ∀ u v : Y → ℝ, ∑ y, v y * thomsonOperator α Q u y
      = ∑ y, targetMarginal α Q y * u y * v y - ∑ x, α x * rowAvg Q u x * rowAvg Q v x := by
    intro u v
    simp only [thomsonOperator, mul_sub, Finset.sum_sub_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun y _ => by ring
    · simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [rowAvg, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => by ring
  rw [key u v, key v u]
  congr 1
  · exact Finset.sum_congr rfl fun y _ => by ring
  · exact Finset.sum_congr rfl fun x _ => by ring

/-- The occurrence energy is well defined: `⟨d, u⟩` does not depend on the
solution `u` of `𝓛_{α,Q} u = d` (so it equals `⟨d, 𝓛† d⟩` for `d ∈ Ran 𝓛`,
`eq:main-occurrence-energy`). -/
theorem occurrence_energy_well_defined (α : X → ℝ) (Q : X → Y → ℝ) (d u u' : Y → ℝ)
    (hu : ∀ y, thomsonOperator α Q u y = d y) (hu' : ∀ y, thomsonOperator α Q u' y = d y) :
    ∑ y, d y * u y = ∑ y, d y * u' y := by
  have h1 : ∑ y, d y * u y = ∑ y, u y * thomsonOperator α Q u' y := by
    simp only [hu', mul_comm]
  have h2 : ∑ y, d y * u' y = ∑ y, u' y * thomsonOperator α Q u y := by
    simp only [hu, mul_comm]
  rw [h1, h2, thomsonOperator_symm]

/-- The Thomson clause of `lem:supp-same-cylinder-transfer`
(`eq:supp-same-cylinder-transfer-thomson`): for the Thomson correction built
from a solution `u` of `𝓛_{α,Q} u = d` (the paper's `u = 𝓛† d`, `d ∈ Ran 𝓛`),
with occurrence energy `𝓔_occ = ⟨d, u⟩`, the coupling `π^T = R + h_*` satisfies
`|𝔼_{π^T} c - 𝔼_R c| ≤ √(𝓔_occ 𝒱_R(c))`. -/
theorem thomson_transfer (α : X → ℝ) (Q : X → Y → ℝ)
    (hα : ∀ x, 0 ≤ α x) (hQ : ∀ x y, 0 ≤ Q x y) (hQ1 : ∀ x, ∑ y, Q x y = 1)
    (d u : Y → ℝ) (hu : ∀ y, thomsonOperator α Q u y = d y) (c : X → Y → ℝ) :
    |∑ x, ∑ y, (refCoupling α Q x y + thomsonCorrection α Q u x y) * c x y
        - ∑ x, ∑ y, refCoupling α Q x y * c x y|
      ≤ Real.sqrt ((∑ y, d y * u y) * cylVariance (refCoupling α Q) Q c) := by
  have hdiff : ∑ x, ∑ y, (refCoupling α Q x y + thomsonCorrection α Q u x y) * c x y
        - ∑ x, ∑ y, refCoupling α Q x y * c x y
      = ∑ x, ∑ y, thomsonCorrection α Q u x y * c x y := by
    simp only [add_mul, Finset.sum_add_distrib]; ring
  have hRnn : ∀ x y, 0 ≤ refCoupling α Q x y := fun x y => mul_nonneg (hα x) (hQ x y)
  have hsupp : ∀ x y, thomsonCorrection α Q u x y ≠ 0 → 0 < refCoupling α Q x y := by
    intro x y hne
    rcases (hRnn x y).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (by simp [thomsonCorrection, ← heq]) hne
  have hE : ∑ y, d y * u y
      = invWeightNormSq (refCoupling α Q) (thomsonCorrection α Q u) := by
    rw [invWeightNormSq_thomsonCorrection α Q hQ1]
    simp only [hu, mul_comm]
  have hN : 0 ≤ invWeightNormSq (refCoupling α Q) (thomsonCorrection α Q u) :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => div_nonneg (sq_nonneg _) (hRnn x y)
  rw [hdiff, hE, Real.sqrt_mul hN]
  exact abs_sum_mul_le_of_source_null _ Q _ c hRnn hsupp
    (thomsonCorrection_source_null α Q hQ1 u)

/-- Last clause of `lem:supp-same-cylinder-transfer`: if `0 ≤ c ≤ B` then
`𝒱_R(c) ≤ B m` with `m = 𝔼_R c = ∑ R c`. -/
theorem variance_le_bound_mul_mean (α : X → ℝ) (Q : X → Y → ℝ)
    (hα : ∀ x, 0 ≤ α x) (hQ : ∀ x y, 0 ≤ Q x y) (hQ1 : ∀ x, ∑ y, Q x y = 1)
    (c : X → Y → ℝ) (B : ℝ) (hc0 : ∀ x y, 0 ≤ c x y) (hcB : ∀ x y, c x y ≤ B) :
    cylVariance (refCoupling α Q) Q c ≤ B * ∑ x, ∑ y, refCoupling α Q x y * c x y := by
  unfold cylVariance
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  -- rowwise: `∑_y Q (c - c̄)² = ∑_y Q c² - c̄² ≤ ∑_y Q c² ≤ B c̄`
  set m := sourceAvg Q c x with hm
  have hrow : ∑ y, Q x y * (c x y - m) ^ 2 = ∑ y, Q x y * c x y ^ 2 - m ^ 2 := by
    have : ∀ y, Q x y * (c x y - m) ^ 2
        = Q x y * c x y ^ 2 - 2 * m * (Q x y * c x y) + m ^ 2 * Q x y := by
      intro y; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hQ1 x]
    simp only [hm, sourceAvg]; ring
  have hsq : ∑ y, Q x y * c x y ^ 2 ≤ B * m := by
    rw [hm, sourceAvg, Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    have : c x y ^ 2 ≤ B * c x y := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (hcB x y) (hc0 x y)
    nlinarith [hQ x y]
  have hL : ∑ y, refCoupling α Q x y * (c x y - m) ^ 2
      = α x * ∑ y, Q x y * (c x y - m) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by simp only [refCoupling]; ring
  have hR : B * ∑ y, refCoupling α Q x y * c x y = α x * (B * m) := by
    rw [hm, sourceAvg, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by simp only [refCoupling]; ring
  rw [hL, hR, hrow]
  exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg m]) (hα x)

end

end SameCylinderTransfer
end RenewalGeometry
