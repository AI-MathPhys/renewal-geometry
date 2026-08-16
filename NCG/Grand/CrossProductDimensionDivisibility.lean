/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.QuaternionicDimensionDivisibility

/-!
# Four-divisibility for metric cross products

The first two coordinate Clifford generators make the Hurwitz unitization
quaternionic.  Thus, in every cross-product dimension at least two, `d + 1`
is divisible by four.
-/

namespace NCG.MetricCrossProduct

theorem finrank_compositionSpace (d : ℕ) :
    Module.finrank ℝ (CompositionSpace d) = d + 1 := by
  simp [CompositionSpace, Vec, add_comm]

theorem coordinate_imaginaryLeft_sq (X : CrossProduct d) (i : Fin d) :
    imaginaryLeft X (coordinateVector i) *
        imaginaryLeft X (coordinateVector i) =
      -(1 : Module.End ℝ (CompositionSpace d)) := by
  apply LinearMap.ext
  intro u
  have h := imaginaryLeft_sq X (coordinateVector i) u
  simpa [Module.End.mul_apply, normSq, dot_coordinateVector] using h

theorem coordinate_imaginaryLeft_anticomm_of_ne (X : CrossProduct d)
    {i j : Fin d} (hij : i ≠ j) :
    imaginaryLeft X (coordinateVector i) *
        imaginaryLeft X (coordinateVector j) =
      -(imaginaryLeft X (coordinateVector j) *
        imaginaryLeft X (coordinateVector i)) := by
  apply LinearMap.ext
  intro u
  have h := coordinate_imaginaryLeft_clifford X i j u
  simp only [hij, if_false, mul_zero, zero_smul] at h
  simp only [Module.End.mul_apply, LinearMap.neg_apply]
  linear_combination (norm := module) h

/-- A metric vector cross product in dimension at least two has a
quaternionic unitization, so `4 ∣ d + 1`. -/
theorem four_dvd_dimension_succ (X : CrossProduct d) (hd : 2 ≤ d) :
    4 ∣ d + 1 := by
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    norm_num [i, j] at this
  have hdiv := NCG.QuaternionicDimension.four_dvd_finrank
    (imaginaryLeft X (coordinateVector i))
    (imaginaryLeft X (coordinateVector j))
    (coordinate_imaginaryLeft_sq X i)
    (coordinate_imaginaryLeft_sq X j)
    (coordinate_imaginaryLeft_anticomm_of_ne X hij)
  rwa [finrank_compositionSpace] at hdiv

end NCG.MetricCrossProduct
