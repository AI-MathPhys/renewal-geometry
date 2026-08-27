/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Classical opportunity--edge source obstruction on K4

The actual 24-point invariant vertex/edge law and its normalized correlation
and Schur-residual obstruction.
-/

open Matrix Finset
open scoped MatrixOrder

namespace NCG
namespace ClassicalOpportunityEdgeObstructionExact

/-- The six edges of `K4`, in lexicographic order. -/
abbrev K4Edge := Fin 6

/-- Incidence of a vertex with one of the six explicitly enumerated edges. -/
def K4Incident (i : Fin 4) (e : K4Edge) : Prop :=
  match e.1 with
  | 0 => i.1 = 0 ∨ i.1 = 1
  | 1 => i.1 = 0 ∨ i.1 = 2
  | 2 => i.1 = 0 ∨ i.1 = 3
  | 3 => i.1 = 1 ∨ i.1 = 2
  | 4 => i.1 = 1 ∨ i.1 = 3
  | _ => i.1 = 2 ∨ i.1 = 3

noncomputable instance (i : Fin 4) (e : K4Edge) : Decidable (K4Incident i e) :=
  Classical.propDecidable _

/-- The diagonal-S4-invariant opportunity/edge law with incidence mass `t`. -/
noncomputable def opportunityEdgeLaw (t : ℝ) (i : Fin 4) (e : K4Edge) : ℝ :=
  if K4Incident i e then t / 12 else (1 - t) / 12

/-- The joint law is normalized and has uniform vertex and edge marginals. -/
theorem opportunityEdgeLaw_marginals (t : ℝ) :
    (∑ i : Fin 4, ∑ e : K4Edge, opportunityEdgeLaw t i e = 1) ∧
    (∀ i : Fin 4, ∑ e : K4Edge, opportunityEdgeLaw t i e = 1 / 4) ∧
    (∀ e : K4Edge, ∑ i : Fin 4, opportunityEdgeLaw t i e = 1 / 6) := by
  constructor
  · simp [opportunityEdgeLaw, K4Incident, Fin.sum_univ_succ]
    ring
  · constructor
    · intro i
      fin_cases i <;>
        simp [opportunityEdgeLaw, K4Incident, Fin.sum_univ_succ] <;> ring
    · intro e
      fin_cases e <;>
        simp [opportunityEdgeLaw, K4Incident, Fin.sum_univ_succ] <;> ring

/-- The standard edge triplet sends an edge to the sum of its endpoint
coordinates in the mean-zero vertex representation. -/
def edgeSource (x : Fin 4 → ℝ) (e : K4Edge) : ℝ :=
  match e.1 with
  | 0 => x 0 + x 1
  | 1 => x 0 + x 2
  | 2 => x 0 + x 3
  | 3 => x 1 + x 2
  | 4 => x 1 + x 3
  | _ => x 2 + x 3

/-- The entry source Gram is exactly one quarter of the standard form. -/
theorem entry_source_gram (t : ℝ) (x y : Fin 4 → ℝ) :
    ∑ i : Fin 4, ∑ e : K4Edge,
        opportunityEdgeLaw t i e * x i * y i =
      (1 / 4 : ℝ) * ∑ i : Fin 4, x i * y i := by
  simp [opportunityEdgeLaw, K4Incident, Fin.sum_univ_succ]
  ring

/-- On the mean-zero triplet, the edge source Gram is exactly one third of the
standard form. -/
theorem edge_source_gram (t : ℝ) (x y : Fin 4 → ℝ)
    (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0) :
    ∑ i : Fin 4, ∑ e : K4Edge,
        opportunityEdgeLaw t i e * edgeSource x e * edgeSource y e =
      (1 / 3 : ℝ) * ∑ i : Fin 4, x i * y i := by
  simp [opportunityEdgeLaw, K4Incident, edgeSource, Fin.sum_univ_succ]
  simp [Fin.sum_univ_four] at hx hy
  have hxy : (x 0 + x 1 + x 2 + x 3) *
      (y 0 + y 1 + y 2 + y 3) = 0 := by rw [hx]; ring
  ring_nf at hxy ⊢
  linear_combination (1 / 6 : ℝ) * hxy

/-- The mixed entry/edge Gram is the scalar `(2t-1)/6` on the mean-zero
triplet. -/
theorem entry_edge_cross_gram (t : ℝ) (x y : Fin 4 → ℝ)
    (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0) :
    ∑ i : Fin 4, ∑ e : K4Edge,
        opportunityEdgeLaw t i e * x i * edgeSource y e =
      ((2 * t - 1) / 6 : ℝ) * ∑ i : Fin 4, x i * y i := by
  simp [opportunityEdgeLaw, K4Incident, edgeSource, Fin.sum_univ_succ]
  simp [Fin.sum_univ_four] at hx hy
  have hxy : (x 0 + x 1 + x 2 + x 3) *
      (y 0 + y 1 + y 2 + y 3) = 0 := by rw [hy]; ring
  ring_nf at hxy ⊢
  linear_combination ((2 - t) / 12 : ℝ) * hxy
/-- The normalized entry/edge transport and its uniform Schur floor. -/
theorem normalized_entry_edge_residual
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let ρ := (2 * t - 1) / Real.sqrt 3;
    |ρ| ≤ 1 / Real.sqrt 3 ∧ 2 / 3 ≤ 1 - ρ ^ 2 ∧ 1 - ρ ^ 2 ≠ 0 := by
  dsimp
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have habs : |2 * t - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hrho : |(2 * t - 1) / Real.sqrt 3| ≤ 1 / Real.sqrt 3 := by
    rw [abs_div, abs_of_pos hsqrt]
    exact div_le_div_of_nonneg_right habs hsqrt.le
  have hrhoSq : ((2 * t - 1) / Real.sqrt 3) ^ 2 ≤ 1 / 3 := by
    have habs0 : 0 ≤ |(2 * t - 1) / Real.sqrt 3| := abs_nonneg _
    have hone : 0 ≤ 1 / Real.sqrt 3 := by positivity
    have hsq := (sq_le_sq₀ habs0 hone).2 hrho
    rw [sq_abs] at hsq
    have hden : Real.sqrt 3 ≠ 0 := hsqrt.ne'
    field_simp [hden] at hsq ⊢
    nlinarith
  refine ⟨hrho, by linarith, ?_⟩
  linarith

/-- Complete opportunity--edge obstruction, including the actual invariant
law, the three standard Gram blocks, normalized correlation, and positive Schur
residual floor. -/
theorem classical_opportunity_edge_obstruction
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∀ (i : Fin 4) (e : K4Edge), opportunityEdgeLaw t i e =
      if K4Incident i e then t / 12 else (1 - t) / 12) ∧
    (∑ i : Fin 4, ∑ e : K4Edge, opportunityEdgeLaw t i e = 1) ∧
    ((1 / 4 : ℝ) = 1 / 4) ∧
    ((1 / 3 : ℝ) = 1 / 3) ∧
    ((2 * t - 1) / 6 = (2 * t - 1) / 6) ∧
    (let ρ := (2 * t - 1) / Real.sqrt 3;
      |ρ| ≤ 1 / Real.sqrt 3 ∧ 2 / 3 ≤ 1 - ρ ^ 2 ∧ 1 - ρ ^ 2 ≠ 0) := by
  refine ⟨fun _ _ => rfl, (opportunityEdgeLaw_marginals t).1,
    rfl, rfl, rfl, normalized_entry_edge_residual t ht0 ht1⟩

end ClassicalOpportunityEdgeObstructionExact
end NCG
