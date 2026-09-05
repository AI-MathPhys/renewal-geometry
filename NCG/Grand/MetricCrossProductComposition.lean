/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SevenDimensionalPositiveThreeForm

/-!
# Metric cross products and Hurwitz composition

This file constructs the real quadratic composition algebra associated to a
metric vector cross product.  It is the algebraic input to the remaining
Hurwitz dimension obstruction.
-/

open scoped BigOperators

namespace NCG.MetricCrossProduct

/-- Coordinate real vector space of dimension `d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Euclidean scalar product in coordinates. -/
def dot {d : ℕ} (x y : Vec d) : ℝ := ∑ i, x i * y i

/-- Squared Euclidean norm in coordinates. -/
def normSq {d : ℕ} (x : Vec d) : ℝ := dot x x

theorem dot_comm {d : ℕ} (x y : Vec d) : dot x y = dot y x := by
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem dot_add_left {d : ℕ} (x y z : Vec d) :
    dot (x + y) z = dot x z + dot y z := by
  simp only [dot, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem dot_add_right {d : ℕ} (x y z : Vec d) :
    dot x (y + z) = dot x y + dot x z := by
  simp only [dot, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem dot_smul_left {d : ℕ} (a : ℝ) (x y : Vec d) :
    dot (a • x) y = a * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem dot_smul_right {d : ℕ} (a : ℝ) (x y : Vec d) :
    dot x (a • y) = a * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem normSq_add {d : ℕ} (x y : Vec d) :
    normSq (x + y) = normSq x + normSq y + 2 * dot x y := by
  rw [normSq, dot_add_left, dot_add_right, dot_add_right]
  rw [dot_comm y x]
  simp only [normSq]
  ring

theorem normSq_smul {d : ℕ} (a : ℝ) (x : Vec d) :
    normSq (a • x) = a ^ 2 * normSq x := by
  rw [normSq, dot_smul_left, dot_smul_right]
  simp only [normSq]
  ring

theorem normSq_nonneg {d : ℕ} (x : Vec d) : 0 ≤ normSq x := by
  simp only [normSq, dot]
  exact Finset.sum_nonneg fun i hi => mul_self_nonneg (x i)

/-- A bilinear alternating metric vector cross product in dimension `d`. -/
structure CrossProduct (d : ℕ) where
  cross : Vec d →ₗ[ℝ] Vec d →ₗ[ℝ] Vec d
  alternating : ∀ x, cross x x = 0
  orthogonal_left : ∀ x y, dot (cross x y) x = 0
  orthogonal_right : ∀ x y, dot (cross x y) y = 0
  normSq_cross : ∀ x y,
    normSq (cross x y) = normSq x * normSq y - dot x y ^ 2

theorem CrossProduct.cross_self (X : CrossProduct d) (x : Vec d) :
    X.cross x x = 0 := X.alternating x

theorem CrossProduct.cross_swap (X : CrossProduct d) (x y : Vec d) :
    X.cross x y = -X.cross y x := by
  have h := X.alternating (x + y)
  change X.cross (x + y) (x + y) = 0 at h
  have h' : X.cross x y + X.cross y x = 0 := by
    simpa only [map_add, LinearMap.add_apply, X.alternating, add_zero,
      zero_add, add_assoc, add_comm] using h
  exact eq_neg_of_add_eq_zero_left h'

/-- Polarizing orthogonality makes the induced trilinear form alternating in
its last two entries. -/
theorem CrossProduct.dot_cross_right_swap (X : CrossProduct d)
    (x y z : Vec d) :
    dot (X.cross x y) z = -dot (X.cross x z) y := by
  have h := X.orthogonal_right x (y + z)
  simp only [map_add, dot_add_left, dot_add_right,
    X.orthogonal_right, add_zero, zero_add] at h
  linarith

/-- The real unitization `ℝ ⊕ ℝᵈ` of the cross-product carrier. -/
abbrev CompositionSpace (d : ℕ) := ℝ × Vec d

/-- Quadratic norm on the Hurwitz unitization. -/
def compositionNormSq {d : ℕ} (u : CompositionSpace d) : ℝ :=
  u.1 ^ 2 + normSq u.2

/-- Multiplication induced by the metric cross product. -/
def compositionMul (X : CrossProduct d)
    (u v : CompositionSpace d) : CompositionSpace d :=
  (u.1 * v.1 - dot u.2 v.2,
    u.1 • v.2 + v.1 • u.2 + X.cross u.2 v.2)

/-- The Hurwitz multiplication has a multiplicative quadratic norm. -/
theorem compositionNormSq_mul (X : CrossProduct d)
    (u v : CompositionSpace d) :
    compositionNormSq (compositionMul X u v) =
      compositionNormSq u * compositionNormSq v := by
  rcases u with ⟨a, x⟩
  rcases v with ⟨b, y⟩
  simp only [compositionMul, compositionNormSq]
  rw [normSq_add, normSq_add, normSq_smul, normSq_smul,
    X.normSq_cross]
  rw [dot_add_left, dot_smul_left, dot_smul_left]
  have hcx : dot (X.cross x y) x = 0 := X.orthogonal_left x y
  have hcy : dot (X.cross x y) y = 0 := X.orthogonal_right x y
  rw [dot_smul_right, dot_comm y x]
  rw [dot_comm y (X.cross x y), hcy,
    dot_smul_left, dot_comm x (X.cross x y), hcx]
  ring

/-- A nonzero element of the unitized composition algebra has nonzero
quadratic norm. -/
theorem compositionNormSq_pos_of_ne_zero {u : CompositionSpace d}
    (hu : u ≠ 0) : 0 < compositionNormSq u := by
  rcases u with ⟨a, x⟩
  simp only [compositionNormSq]
  have hx : 0 ≤ normSq x := normSq_nonneg x
  have ha : 0 ≤ a ^ 2 := sq_nonneg a
  have hne : a ≠ 0 ∨ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (Prod.ext h.1 (funext fun i => by
      have := congrFun h.2 i
      simpa using this))
  rcases hne with ha0 | hx0
  · nlinarith [sq_pos_of_ne_zero ha0]
  · have hnorm : 0 < normSq x := by
      rw [normSq, dot]
      have hexists : ∃ i, x i ≠ 0 := by
        by_contra h
        push Not at h
        exact hx0 (funext h)
      obtain ⟨i, hi⟩ := hexists
      have hterm : 0 < x i * x i := mul_self_pos.mpr hi
      exact Finset.sum_pos' (fun j hj => mul_self_nonneg (x j))
        ⟨i, Finset.mem_univ i, hterm⟩
    linarith

/-- The multiplicative norm implies there are no zero divisors. -/
theorem compositionMul_eq_zero_iff (X : CrossProduct d)
    (u v : CompositionSpace d) :
    compositionMul X u v = 0 ↔ u = 0 ∨ v = 0 := by
  constructor
  · intro huv
    by_contra h
    push Not at h
    have hu := compositionNormSq_pos_of_ne_zero h.1
    have hv := compositionNormSq_pos_of_ne_zero h.2
    have hmul := compositionNormSq_mul X u v
    rw [huv] at hmul
    have hz : compositionNormSq (0 : CompositionSpace d) = 0 := by
      simp [compositionNormSq, normSq, dot]
    rw [hz] at hmul
    nlinarith
  · rintro (rfl | rfl) <;>
      simp [compositionMul, dot, compositionNormSq]

end NCG.MetricCrossProduct
