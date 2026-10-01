/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.SupplementLawMultiplierExact
import RenewalGeometry.Gravity.SupplementLawMultiplierOrders

/-!
# Exact periodic discrete Hodge identity
  (`lem:supp-connection-hodge`, `eq:supp-discrete-hodge-identity`;
  emergent-spacetime manuscript)

On a finite periodic grid `G` (any finite additive group, e.g. the paper's
`(hℤ/ℤ)³ = PeriodicGrid N`) with steps `e i`, forward and backward
differences `D_i^± = LawMultiplier.forwardDiff / backwardDiff` and the grid
norm `‖w‖_h² = h³ ∑_x ‖w x‖²`, a one-cochain `A = (A_i)` with values in a real
inner product space `F` satisfies

`∑_{i,j} ‖D_i^+ A_j‖_h² = ∑_{i<j} ‖D_i^+ A_j - D_j^+ A_i‖_h² + ‖∑_i D_i^- A_i‖_h²`.

The proof is in physical space (no Fourier transform): the summation-by-parts
identity `∑_x ⟪D_i^- u, D_j^- v⟫ = ∑_x ⟪D_j^+ u, D_i^+ v⟫`
(`sum_inner_backwardDiff`) — obtained from translation invariance of the
grid sum — shows that the divergence square equals `∑_{i,j} ⟪a_{ij}, a_{ji}⟫`
with `a_{ij} = D_i^+ A_j`, and the curl squares give
`∑_{i,j} ‖a_{ij}‖² - ∑_{i,j} ⟪a_{ij}, a_{ji}⟫`.

`discrete_hodge_identity` holds for any finite linearly ordered index set of
directions and any step `h`; `periodic_discrete_hodge_identity` is the
paper's three-dimensional periodic instance.
-/

namespace RenewalGeometry
namespace PeriodicHodge

open Finset LawMultiplier

open scoped RealInnerProductSpace

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Summation by parts on the periodic grid:
`∑_x ⟪D_i^- u x, D_j^- v x⟫ = ∑_x ⟪D_j^+ u x, D_i^+ v x⟫`
(`lem:supp-connection-hodge`, proof ingredient). -/
theorem sum_inner_backwardDiff (h : ℝ) (ei ej : G) (u v : G → F) :
    ∑ x, ⟪backwardDiff h ei u x, backwardDiff h ej v x⟫
      = ∑ x, ⟪forwardDiff h ej u x, forwardDiff h ei v x⟫ := by
  simp only [backwardDiff, forwardDiff, inner_smul_left, inner_smul_right,
    inner_sub_left, inner_sub_right, RCLike.conj_to_real]
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1
  have e1 : ∑ x, ⟪u (x - ei), v (x - ej)⟫ = ∑ x, ⟪u (x + ej), v (x + ei)⟫ := by
    rw [← Equiv.sum_comp (Equiv.addRight (ei + ej))]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Equiv.coe_addRight]
    congr 2 <;> abel
  have e2 : ∑ x, ⟪u x, v (x - ej)⟫ = ∑ x, ⟪u (x + ej), v x⟫ := by
    rw [← Equiv.sum_comp (Equiv.addRight ej)]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
  have e3 : ∑ x, ⟪u (x - ei), v x⟫ = ∑ x, ⟪u x, v (x + ei)⟫ := by
    rw [← Equiv.sum_comp (Equiv.addRight ei)]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
  rw [e1, e2, e3]
  ring

/-- Splitting a double sum into diagonal, upper and lower parts:
`∑_{i,j} f i j = ∑_i f i i + ∑_{i<j} (f i j + f j i)`. -/
theorem sum_sum_eq_diag_add_upper {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ℝ) :
    ∑ i, ∑ j, f i j
      = ∑ i, f i i + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (f i j + f j i) := by
  have hpt : ∀ i j, f i j = (if i < j then f i j else 0) + (if i = j then f i j else 0)
      + (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, hij.ne, not_lt.mpr hij.le]
    · subst hij; simp
    · simp [hij, hij.ne', not_lt.mpr hij.le]
  have hlow : ∑ i, ∑ j, (if j < i then f i j else 0)
      = ∑ i, ∑ j, (if i < j then f j i else 0) := Finset.sum_comm
  calc ∑ i, ∑ j, f i j
      = ∑ i, ∑ j, (if i < j then f i j else 0) + ∑ i, ∑ j, (if i = j then f i j else 0)
        + ∑ i, ∑ j, (if j < i then f i j else 0) := by
        simp only [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j
    _ = ∑ i, f i i + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (f i j + f j i) := by
        rw [hlow]
        have hdiag : ∑ i, ∑ j, (if i = j then f i j else 0) = ∑ i, f i i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_ite_eq]; simp
        rw [hdiag]
        simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
        have : ∀ i j, (if i < j then f i j + f j i else 0)
            = (if i < j then f i j else 0) + (if i < j then f j i else 0) := by
          intro i j; split_ifs <;> simp
        simp only [this, Finset.sum_add_distrib]
        ring

omit [AddCommGroup G] in
/-- The algebraic core of the Hodge identity: for arrays `a i j` with
`∑_{i,j} ∑_x ⟪a j i x, a i j x⟫ = S`,
`∑_{i,j} ∑_x ‖a i j x‖² = ∑_{i<j} ∑_x ‖(a i j - a j i) x‖² + S`. -/
theorem hodge_algebra {ι : Type*} [Fintype ι] [LinearOrder ι] (a : ι → ι → G → F) :
    ∑ i, ∑ j, ∑ x, ‖a i j x‖ ^ 2
      = ∑ i, ∑ j ∈ univ.filter (fun j => i < j), ∑ x, ‖(a i j - a j i) x‖ ^ 2
        + ∑ i, ∑ j, ∑ x, ⟪a j i x, a i j x⟫ := by
  have h1 := sum_sum_eq_diag_add_upper (fun i j => ∑ x, ‖a i j x‖ ^ 2)
  have h2 := sum_sum_eq_diag_add_upper (fun i j => ∑ x, ⟪a j i x, a i j x⟫)
  beta_reduce at h1 h2
  have hdiag : ∑ i, ∑ x, ⟪a i i x, a i i x⟫ = ∑ i, ∑ x, ‖a i i x‖ ^ 2 :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => real_inner_self_eq_norm_sq _
  have hc : ∑ i, ∑ j ∈ univ.filter (fun j => i < j), ∑ x, ‖(a i j - a j i) x‖ ^ 2
      = ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (∑ x, ‖a i j x‖ ^ 2 + ∑ x, ‖a j i x‖ ^ 2)
        - ∑ i, ∑ j ∈ univ.filter (fun j => i < j),
            (∑ x, ⟪a j i x, a i j x⟫ + ∑ x, ⟪a i j x, a j i x⟫) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Pi.sub_apply, norm_sub_sq_real, real_inner_comm (a j i x)]
    ring
  rw [hc, h2, hdiag, h1]
  ring

/-- **Exact periodic discrete Hodge identity** (`lem:supp-connection-hodge`,
`eq:supp-discrete-hodge-identity`), for any finite linearly ordered set of
directions with steps `e i` on a finite periodic grid `G`, any step `h`, and
any cochain `A` with values in a real inner product space:
`∑_{i,j} ‖D_i^+ A_j‖_h² = ∑_{i<j} ‖D_i^+ A_j - D_j^+ A_i‖_h²
  + ‖∑_i D_i^- A_i‖_h²`. -/
theorem discrete_hodge_identity {ι : Type*} [Fintype ι] [LinearOrder ι]
    (h : ℝ) (e : ι → G) (A : ι → G → F) :
    ∑ i, ∑ j, gridNormSq h (forwardDiff h (e i) (A j))
      = ∑ i, ∑ j ∈ univ.filter (fun j => i < j),
          gridNormSq h (forwardDiff h (e i) (A j) - forwardDiff h (e j) (A i))
        + gridNormSq h (∑ i, backwardDiff h (e i) (A i)) := by
  -- the divergence square is `∑_{i,j} ⟪D_j^+ A_i, D_i^+ A_j⟫`
  have hdiv : ∑ x, ‖(∑ i, backwardDiff h (e i) (A i)) x‖ ^ 2
      = ∑ i, ∑ j, ∑ x, ⟪forwardDiff h (e j) (A i) x, forwardDiff h (e i) (A j) x⟫ := by
    have hpt : ∀ x, ‖(∑ i, backwardDiff h (e i) (A i)) x‖ ^ 2
        = ∑ i, ∑ j, ⟪backwardDiff h (e i) (A i) x, backwardDiff h (e j) (A j) x⟫ := by
      intro x
      rw [← real_inner_self_eq_norm_sq, Finset.sum_apply, sum_inner]
      simp only [inner_sum]
    rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => sum_inner_backwardDiff h (e i) (e j) (A i) (A j)
  have key := hodge_algebra (fun i j => forwardDiff h (e i) (A j))
  beta_reduce at key
  rw [← hdiv] at key
  simp only [gridNormSq, ← Finset.mul_sum]
  rw [key, mul_add]

/-- `eq:supp-discrete-hodge-identity` on the paper's three-dimensional periodic
grid `(hℤ/ℤ)³ = PeriodicGrid N` with its unit steps
(`lem:supp-connection-hodge`). -/
theorem periodic_discrete_hodge_identity (N : ℕ) [NeZero N] (h : ℝ)
    (A : Fin 3 → PeriodicGrid N → F) :
    ∑ i, ∑ j, gridNormSq h (forwardDiff h (unitStep N i) (A j))
      = ∑ i, ∑ j ∈ univ.filter (fun j => i < j),
          gridNormSq h (forwardDiff h (unitStep N i) (A j)
            - forwardDiff h (unitStep N j) (A i))
        + gridNormSq h (∑ i, backwardDiff h (unitStep N i) (A i)) :=
  discrete_hodge_identity h (unitStep N) A

end

end PeriodicHodge
end RenewalGeometry
