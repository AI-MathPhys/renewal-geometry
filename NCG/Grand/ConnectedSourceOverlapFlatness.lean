/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTOverlapFlatness

/-!
# Connected zero-innovation source atlases are flat

This closes the connected-graph step in
`thm:GT-source-overlap-flatness`.  The older theorem proves the algebraic
flatness packet once all whitened source ranges coincide.  Here we derive
that common-range hypothesis from the manuscript's local assumption: every
edge has zero range innovation in both directions.
-/

open Matrix

namespace NCG

/-- The innovation of `Vᵢ` relative to the whitened range of `Vⱼ`. -/
def whitenedSourceRangeInnovation {n r : Type} [Fintype n] [Fintype r]
    [DecidableEq n] (Vj Vi : Matrix n r ℂ) : Matrix n r ℂ :=
  (1 - Vj * Vjᴴ) * Vi

/-- Graph connectedness expressed by the reflexive-transitive closure of its
edge relation.  Symmetry is supplied separately, as it is for an undirected
graph. -/
def EdgeConnected {ι : Type} (edge : ι → ι → Prop) : Prop :=
  ∀ i j, Relation.ReflTransGen edge i j

/-- Zero innovation in both directions between two whitened isometries forces
their range projections to agree. -/
theorem whitened_zero_innovation_range_eq {n r : Type}
    [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]
    (Vi Vj : Matrix n r ℂ)
    (hi : Viᴴ * Vi = 1) (hj : Vjᴴ * Vj = 1)
    (hij : whitenedSourceRangeInnovation Vj Vi = 0)
    (hji : whitenedSourceRangeInnovation Vi Vj = 0) :
    Vi * Viᴴ = Vj * Vjᴴ := by
  have hVjVi : (Vj * Vjᴴ) * Vi = Vi := by
    have h := hij
    simp only [whitenedSourceRangeInnovation, Matrix.sub_mul,
      Matrix.one_mul] at h
    exact (sub_eq_zero.mp h).symm
  have hViVj : (Vi * Viᴴ) * Vj = Vj := by
    have h := hji
    simp only [whitenedSourceRangeInnovation, Matrix.sub_mul,
      Matrix.one_mul] at h
    exact (sub_eq_zero.mp h).symm
  have hleft : (Vj * Vjᴴ) * (Vi * Viᴴ) = Vi * Viᴴ := by
    rw [← Matrix.mul_assoc, hVjVi]
  have hright : (Vi * Viᴴ) * (Vj * Vjᴴ) = Vj * Vjᴴ := by
    rw [← Matrix.mul_assoc, hViVj]
  have hright' : (Vi * Viᴴ) * (Vj * Vjᴴ) = Vi * Viᴴ := by
    have h := congrArg Matrix.conjTranspose hleft
    simpa [Matrix.conjTranspose_mul] using h
  exact hright'.symm.trans hright

/-- Edgewise equality of whitened source ranges propagates across a connected
graph. -/
theorem connected_zero_innovation_common_range {ι n r : Type}
    [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]
    (edge : ι → ι → Prop) (hconnected : EdgeConnected edge)
    (V : ι → Matrix n r ℂ)
    (hiso : ∀ i, (V i)ᴴ * V i = 1)
    (hzero : ∀ ⦃i j⦄, edge i j →
      whitenedSourceRangeInnovation (V j) (V i) = 0 ∧
      whitenedSourceRangeInnovation (V i) (V j) = 0) :
    ∀ i j, V i * (V i)ᴴ = V j * (V j)ᴴ := by
  intro i j
  have hedge : ∀ ⦃a b⦄, edge a b →
      V a * (V a)ᴴ = V b * (V b)ᴴ := by
    intro a b hab
    exact whitened_zero_innovation_range_eq (V a) (V b)
      (hiso a) (hiso b) (hzero hab).1 (hzero hab).2
  have hclosure := Relation.ReflTransGen.lift
    (fun k => V k * (V k)ᴴ) (fun _ _ hab => hedge hab) i j
    (hconnected i j)
  simpa only [Relation.reflTransGen_eq_self] using hclosure

/-- Exact connected-graph form of `thm:GT-source-overlap-flatness`: local
zero innovation gives common ranges, unitary normalized overlaps, a pure
gauge, and an exactly flat cocycle. -/
theorem connected_source_overlap_flatness_exact {ι n r : Type}
    [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]
    (edge : ι → ι → Prop) (hconnected : EdgeConnected edge)
    (V : ι → Matrix n r ℂ)
    (hiso : ∀ i, (V i)ᴴ * V i = 1)
    (hzero : ∀ ⦃i j⦄, edge i j →
      whitenedSourceRangeInnovation (V j) (V i) = 0 ∧
      whitenedSourceRangeInnovation (V i) (V j) = 0)
    (i0 : ι) :
    (∀ i j, V i * (V i)ᴴ = V j * (V j)ᴴ)
    ∧ (∀ i j, ((V j)ᴴ * V i)ᴴ * ((V j)ᴴ * V i) = 1
      ∧ ((V j)ᴴ * V i) * ((V j)ᴴ * V i)ᴴ = 1)
    ∧ (∀ i j, (V j)ᴴ * V i
        = ((V i0)ᴴ * V j)ᴴ * ((V i0)ᴴ * V i))
    ∧ (∀ i j k, ((V k)ᴴ * V j) * ((V j)ᴴ * V i)
        = (V k)ᴴ * V i)
    ∧ (∀ i, (V i)ᴴ * V i = 1) := by
  have hrange := connected_zero_innovation_common_range edge hconnected V hiso hzero
  exact ⟨hrange, gt_source_overlap_flatness V hiso hrange i0⟩

end NCG
