/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Physical point/fibre connection and magnetic-loop
  alternative (`thm:GT-point-fibre-holonomy`,
  Gran-Tensor manuscript)

* `gt_point_fibre_holonomy`: for edge transports `W` with
  the flat-cocycle property
  (`W_{k←j}W_{j←i} = W_{k←i}`, `W_{i←i} = 1`):
  (i) every edge transport is two-sided invertible
      (`W_{i←j}W_{j←i} = 1`);
  (ii) the boxed HOL.1 common-gauge trivialization — the
      block gauge `Gᵢ = W_{i₀←i}` makes every edge the
      identity, `W_{j←i} = (W_{i₀←j})⁻¹W_{i₀←i}`;
  (iii) conversely, a pure-gauge family
      `W_{j←i} = Qⱼ⁻¹Qᵢ` has every triangle holonomy
      trivial — with (ii) this is the boxed "common gauge
      ⟺ every fundamental-cycle holonomy is `I_r`".

The polar splitting `-K_{ji} = V_{j←i}A_{j←i}` of the
supported blocks (the repo's `NCG.polar_decomposition`),
the boxed HOL.2 log-det walk expansion
`log det K = n log Λ - ∑ Tr(P_Λ^m)/m` with its signed
magnetic amplitudes, and the non-scalarization of the
positive polar factors are the manuscript's spectral and
gauge-reading layers.
-/

open Matrix

namespace NCG

/-- `thm:GT-point-fibre-holonomy` (HOL.1). -/
theorem gt_point_fibre_holonomy {ι : Type} {r : Type}
    [Fintype r] [DecidableEq r]
    (W : ι → ι → Matrix r r ℂ) (i0 : ι)
    (hcoc : ∀ i j k, W k j * W j i = W k i)
    (hid : ∀ i, W i i = 1) :
    -- (i) every edge transport is two-sided invertible
    (∀ i j, W i j * W j i = 1)
    -- (ii) the boxed common-gauge trivialization
    ∧ (∀ i j, W j i = (W i0 j)⁻¹ * W i0 i)
    -- (iii) a pure-gauge family has trivial triangle
    -- holonomy
    ∧ (∀ (Q : ι → Matrix r r ℂ),
        (∀ i, IsUnit (Q i)) →
        (∀ i j, W j i = (Q j)⁻¹ * Q i) →
        ∀ i j k, W i k * W k j * W j i = 1) := by
  have hinv : ∀ i j, W i j * W j i = 1 := by
    intro i j
    rw [hcoc i j i, hid i]
  have hinveq : ∀ i j, (W i j)⁻¹ = W j i := fun i j =>
    Matrix.inv_eq_right_inv (hinv i j)
  refine ⟨hinv, ?_, ?_⟩
  · intro i j
    rw [hinveq i0 j, hcoc i i0 j]
  · intro Q hQ hW i j k
    haveI : ∀ i, Invertible (Q i) := fun i =>
      (hQ i).invertible
    rw [hW k i, hW j k, hW i j]
    calc (Q i)⁻¹ * Q k * ((Q k)⁻¹ * Q j)
          * ((Q j)⁻¹ * Q i)
        = (Q i)⁻¹ * (Q k * (Q k)⁻¹)
          * (Q j * (Q j)⁻¹) * Q i := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [Matrix.mul_inv_of_invertible,
            Matrix.mul_inv_of_invertible,
            Matrix.mul_one, Matrix.mul_one,
            Matrix.inv_mul_of_invertible]

end NCG
