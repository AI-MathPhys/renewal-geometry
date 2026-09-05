/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MetricCrossProductComposition

/-!
# The Clifford system of a metric cross product

Imaginary left multiplication on the Hurwitz unitization is skew-adjoint and
satisfies the real Clifford relations.  These identities reduce the remaining
dimension classification to a finite-dimensional Clifford-module obstruction.
-/

open scoped BigOperators

namespace NCG.MetricCrossProduct

/-- Polar form of the quadratic norm on the composition space. -/
def compositionDot {d : ℕ} (u v : CompositionSpace d) : ℝ :=
  u.1 * v.1 + dot u.2 v.2

theorem compositionDot_comm {d : ℕ} (u v : CompositionSpace d) :
    compositionDot u v = compositionDot v u := by
  simp only [compositionDot]
  rw [dot_comm]
  ring

theorem compositionDot_add_left {d : ℕ} (u v w : CompositionSpace d) :
    compositionDot (u + v) w = compositionDot u w + compositionDot v w := by
  rcases u with ⟨a, x⟩
  rcases v with ⟨b, y⟩
  rcases w with ⟨c, z⟩
  simp only [compositionDot, Prod.fst_add, Prod.snd_add, dot_add_left]
  ring

theorem compositionDot_add_right {d : ℕ} (u v w : CompositionSpace d) :
    compositionDot u (v + w) = compositionDot u v + compositionDot u w := by
  rw [compositionDot_comm, compositionDot_add_left]
  rw [compositionDot_comm u v, compositionDot_comm u w]

theorem compositionDot_smul_left {d : ℕ} (a : ℝ)
    (u v : CompositionSpace d) :
    compositionDot (a • u) v = a * compositionDot u v := by
  rcases u with ⟨b, x⟩
  rcases v with ⟨c, y⟩
  simp only [compositionDot, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, dot_smul_left]
  ring

theorem compositionNormSq_eq_dot_self {d : ℕ} (u : CompositionSpace d) :
    compositionNormSq u = compositionDot u u := by
  simp only [compositionNormSq, compositionDot, normSq]
  ring

theorem compositionNormSq_add {d : ℕ} (u v : CompositionSpace d) :
    compositionNormSq (u + v) = compositionNormSq u + compositionNormSq v +
      2 * compositionDot u v := by
  rcases u with ⟨a, x⟩
  rcases v with ⟨b, y⟩
  simp only [compositionNormSq, compositionDot, Prod.fst_add, Prod.snd_add,
    normSq_add]
  ring

/-- Nondegeneracy of the coordinate inner product. -/
theorem compositionDot_ext {d : ℕ} {u v : CompositionSpace d}
    (h : ∀ w, compositionDot u w = compositionDot v w) : u = v := by
  apply Prod.ext
  · have hscalar := h ((1 : ℝ), (0 : Vec d))
    simpa [compositionDot, dot] using hscalar
  · funext i
    have hcoord := h ((0 : ℝ), Pi.single i 1)
    simpa [compositionDot, dot, Pi.single_apply] using hcoord

/-- Imaginary left multiplication by `x` on `ℝ ⊕ ℝᵈ`. -/
def imaginaryLeft (X : CrossProduct d) (x : Vec d) :
    CompositionSpace d →ₗ[ℝ] CompositionSpace d where
  toFun u := (-dot x u.2, u.1 • x + X.cross x u.2)
  map_add' u v := by
    rcases u with ⟨a, y⟩
    rcases v with ⟨b, z⟩
    apply Prod.ext
    · simp only [dot_add_right, Prod.fst_add, Prod.snd_add]
      ring
    · funext i
      simp only [Prod.snd_add, Prod.fst_add, map_add, Pi.add_apply,
        Pi.smul_apply]
      ring
  map_smul' a u := by
    rcases u with ⟨b, y⟩
    apply Prod.ext
    · change -dot x (a • y) = a * (-dot x y)
      rw [dot_smul_right]
      ring
    · funext i
      change (a * b) * x i + (X.cross x (a • y)) i =
        a * (b * x i + (X.cross x y) i)
      rw [map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring

@[simp] theorem imaginaryLeft_apply (X : CrossProduct d) (x : Vec d)
    (u : CompositionSpace d) :
    imaginaryLeft X x u = (-dot x u.2, u.1 • x + X.cross x u.2) := rfl

theorem imaginaryLeft_add (X : CrossProduct d) (x y : Vec d)
    (u : CompositionSpace d) :
    imaginaryLeft X (x + y) u = imaginaryLeft X x u + imaginaryLeft X y u := by
  rcases u with ⟨a, z⟩
  apply Prod.ext
  · simp only [imaginaryLeft_apply, dot_add_left, Prod.fst_add]
    ring
  · funext i
    simp only [imaginaryLeft_apply, Pi.add_apply, Pi.smul_apply, map_add,
      Prod.snd_add, LinearMap.add_apply]
    ring

/-- The multiplicative norm says imaginary left multiplication scales the
quadratic norm by `‖x‖²`. -/
theorem imaginaryLeft_normSq (X : CrossProduct d) (x : Vec d)
    (u : CompositionSpace d) :
    compositionNormSq (imaginaryLeft X x u) =
      normSq x * compositionNormSq u := by
  have h := compositionNormSq_mul X ((0 : ℝ), x) u
  simpa [compositionMul, imaginaryLeft_apply, compositionNormSq] using h

/-- Imaginary left multiplication is skew-adjoint for the composition inner
product. -/
theorem imaginaryLeft_skew (X : CrossProduct d) (x : Vec d)
    (u v : CompositionSpace d) :
    compositionDot (imaginaryLeft X x u) v =
      -compositionDot u (imaginaryLeft X x v) := by
  rcases u with ⟨a, y⟩
  rcases v with ⟨b, z⟩
  simp only [imaginaryLeft_apply, compositionDot,
    dot_add_left, dot_add_right, dot_smul_left, dot_smul_right]
  have hcross := X.dot_cross_right_swap x y z
  rw [dot_comm y x, dot_comm y (X.cross x z)]
  linarith

/-- Polarization upgrades quadratic norm preservation to the full scaled
inner-product identity. -/
theorem imaginaryLeft_inner (X : CrossProduct d) (x : Vec d)
    (u v : CompositionSpace d) :
    compositionDot (imaginaryLeft X x u) (imaginaryLeft X x v) =
      normSq x * compositionDot u v := by
  have hsum := imaginaryLeft_normSq X x (u + v)
  have hu := imaginaryLeft_normSq X x u
  have hv := imaginaryLeft_normSq X x v
  rw [map_add, compositionNormSq_add, compositionNormSq_add, hu, hv] at hsum
  nlinarith

/-- Clifford square relation `J_x² = -‖x‖² I`. -/
theorem imaginaryLeft_sq (X : CrossProduct d) (x : Vec d)
    (u : CompositionSpace d) :
    imaginaryLeft X x (imaginaryLeft X x u) = -(normSq x) • u := by
  apply compositionDot_ext
  intro w
  rw [imaginaryLeft_skew, imaginaryLeft_inner,
    compositionDot_smul_left]
  ring

/-- Polarizing the square relation gives the Clifford anticommutator. -/
theorem imaginaryLeft_anticomm (X : CrossProduct d) (x y : Vec d)
    (u : CompositionSpace d) :
    imaginaryLeft X x (imaginaryLeft X y u) +
        imaginaryLeft X y (imaginaryLeft X x u) =
      -(2 * dot x y) • u := by
  have hxy := imaginaryLeft_sq X (x + y) u
  have hx := imaginaryLeft_sq X x u
  have hy := imaginaryLeft_sq X y u
  rw [imaginaryLeft_add, imaginaryLeft_add, map_add, map_add] at hxy
  rw [normSq_add] at hxy
  linear_combination (norm := module) hxy - hx - hy

/-- Standard coordinate vector. -/
def coordinateVector (i : Fin d) : Vec d := Pi.single i 1

@[simp] theorem dot_coordinateVector (i j : Fin d) :
    dot (coordinateVector i) (coordinateVector j) = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    unfold dot coordinateVector
    rw [Finset.sum_eq_single i]
    · simp
    · intro k hk hki
      simp [Pi.single_apply, hki]
    · simp
  · unfold dot coordinateVector
    rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro k hk
      by_cases hki : k = i
      · subst k
        simp [Pi.single_apply, hij]
      · simp [Pi.single_apply, Ne.symm hki]

/-- Coordinate imaginary multiplications form the Clifford system
`J_i J_j + J_j J_i = -2 δᵢⱼ I`. -/
theorem coordinate_imaginaryLeft_clifford (X : CrossProduct d)
    (i j : Fin d) (u : CompositionSpace d) :
    imaginaryLeft X (coordinateVector i)
          (imaginaryLeft X (coordinateVector j) u) +
        imaginaryLeft X (coordinateVector j)
          (imaginaryLeft X (coordinateVector i) u) =
      ((-2 : ℝ) * (if i = j then 1 else 0)) • u := by
  by_cases hij : i = j
  · subst j
    simpa [neg_smul] using
      imaginaryLeft_anticomm X (coordinateVector i) (coordinateVector i) u
  · simpa [hij, neg_smul] using
      imaginaryLeft_anticomm X (coordinateVector i) (coordinateVector j) u

end NCG.MetricCrossProduct
