/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Closed convex hulls of compact orbits from uniform quadrature bounds

In finite-dimensional applications Carathéodory supplies a uniform bound on
the number of points in a convex combination.  This file packages the
topological consequence needed for compact Haar quadratures: if every point
of the convex hull of a continuous compact orbit has a positive quadrature of
length at most `N`, then that convex hull is compact (and hence closed).

The key point is exact rather than asymptotic.  A quadrature of length `L ≤ N`
is padded by zero weights to length `N`; the convex hull is therefore the image
of the compact space `stdSimplex ℝ (Fin N) × (Fin N → G)`.
-/

open scoped Topology
open Set

namespace NCG
namespace CompactOrbitConvexHull

variable {G E : Type*} [TopologicalSpace G] [CompactSpace G] [Nonempty G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [T2Space E]

/-- A continuous compact orbit has compact convex hull once a uniform exact
positive-quadrature bound is available. -/
theorem isCompact_convexHull_range_of_uniform_quadrature
    (f : G → E) (hf : Continuous f) (N : ℕ)
    (hquad : ∀ x ∈ convexHull ℝ (Set.range f),
      ∃ (L : ℕ) (w : Fin L → ℝ) (g : Fin L → G),
        L ≤ N ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
          x = ∑ i, w i • f (g i)) :
    IsCompact (convexHull ℝ (Set.range f)) := by
  classical
  let combine : (stdSimplex ℝ (Fin N)) × (Fin N → G) → E :=
    fun q => ∑ i, q.1.1 i • f (q.2 i)
  have hcombine : Continuous combine := by
    dsimp [combine]
    apply continuous_finset_sum
    intro i _
    exact ((continuous_apply i).comp
      (continuous_subtype_val.comp continuous_fst)).smul
        (hf.comp ((continuous_apply i).comp continuous_snd))
  have hrangeCompact : IsCompact (Set.range combine) :=
    isCompact_range hcombine
  suffices heq : convexHull ℝ (Set.range f) = Set.range combine by
    simpa [heq] using hrangeCompact
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨L, w, g, hLN, hw0, hw1, hxsum⟩ := hquad x hx
    let M := N - L
    have hLM : L + M = N := Nat.add_sub_of_le hLN
    let wpad : Fin (L + M) → ℝ := Fin.append w (fun _ : Fin M => 0)
    let gpad : Fin (L + M) → G := Fin.append g (fun _ : Fin M => Classical.arbitrary G)
    let e : Fin (L + M) ≃ Fin N := finCongr hLM
    let wN : Fin N → ℝ := fun i => wpad (e.symm i)
    let gN : Fin N → G := fun i => gpad (e.symm i)
    have hwN0 : ∀ i, 0 ≤ wN i := by
      intro i
      obtain ⟨j, rfl⟩ := e.surjective i
      change 0 ≤ wpad j
      refine Fin.addCases (motive := fun j => 0 ≤ wpad j)
        (fun j => ?_) (fun j => ?_) j
      · simpa [wpad] using hw0 j
      · simp [wpad]
    have hwN1 : ∑ i, wN i = 1 := by
      calc
        (∑ i : Fin N, wN i) = ∑ j : Fin (L + M), wpad j :=
          Equiv.sum_comp e.symm wpad
        _ = (∑ j : Fin L, w j) + ∑ _j : Fin M, (0 : ℝ) := by
          simp [wpad, Fin.sum_univ_add]
        _ = 1 := by simp [hw1]
    have hcomb : ∑ i : Fin N, wN i • f (gN i) =
        ∑ i : Fin L, w i • f (g i) := by
      calc
        (∑ i : Fin N, wN i • f (gN i)) =
            ∑ j : Fin (L + M), wpad j • f (gpad j) :=
          Equiv.sum_comp e.symm (fun j => wpad j • f (gpad j))
        _ = (∑ j : Fin L, w j • f (g j)) +
            ∑ _j : Fin M, (0 : ℝ) • f (Classical.arbitrary G) := by
          simp [wpad, gpad, Fin.sum_univ_add]
        _ = ∑ j : Fin L, w j • f (g j) := by simp
    refine ⟨(⟨wN, hwN0, hwN1⟩, gN), ?_⟩
    change combine (⟨wN, hwN0, hwN1⟩, gN) = x
    dsimp [combine]
    rw [hcomb, ← hxsum]
  · rintro x ⟨q, rfl⟩
    change (∑ i, q.1.1 i • f (q.2 i)) ∈ convexHull ℝ (Set.range f)
    rw [← Finset.univ.centerMass_eq_of_sum_1 _ (by simpa using q.1.2.2)]
    exact Finset.centerMass_mem_convexHull
      (t := (Finset.univ : Finset (Fin N)))
      (w := fun i => q.1.1 i) (z := fun i => f (q.2 i))
      (fun i _ => q.1.2.1 i)
      (by simpa [q.1.2.2] using (zero_lt_one : (0 : ℝ) < 1))
      (fun i _ => Set.mem_range_self (q.2 i))

/-- Closedness form of
`isCompact_convexHull_range_of_uniform_quadrature`. -/
theorem isClosed_convexHull_range_of_uniform_quadrature
    (f : G → E) (hf : Continuous f) (N : ℕ)
    (hquad : ∀ x ∈ convexHull ℝ (Set.range f),
      ∃ (L : ℕ) (w : Fin L → ℝ) (g : Fin L → G),
        L ≤ N ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
          x = ∑ i, w i • f (g i)) :
    IsClosed (convexHull ℝ (Set.range f)) :=
  (isCompact_convexHull_range_of_uniform_quadrature f hf N hquad).isClosed

end CompactOrbitConvexHull
end NCG
