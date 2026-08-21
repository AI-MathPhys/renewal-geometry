/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.NearbyProjectionRankStability

/-!
# Quantitative convergence of projection ranges

Operator-norm proximity of idempotents controls the distance between their ranges: applying the
second operator to a vector in the first range gives an explicit nearby vector in the second
range.  Consequently norm-convergent idempotents have bilaterally convergent unit-range sets.
-/

open Filter Topology

noncomputable section

namespace NCG.ProjectionStability

universe u v

variable {K : Type u} [NontriviallyNormedField K]
variable {H : Type v} [NormedAddCommGroup H] [NormedSpace K H]

/-- A vector in the range of an idempotent `P` is within
`‖P-Q‖ * ‖x‖` of the explicit vector `Q x` in the range of `Q`. -/
theorem exists_mem_range_norm_sub_le_of_mem_range
    (P Q : H →L[K] H) (hP : IsIdempotentElem P.toLinearMap)
    (x : H) (hx : x ∈ LinearMap.range P.toLinearMap) :
    ∃ y ∈ LinearMap.range Q.toLinearMap,
      ‖x - y‖ ≤ ‖P - Q‖ * ‖x‖ := by
  refine ⟨Q x, ⟨x, rfl⟩, ?_⟩
  have hPx : P x = x :=
    LinearMap.IsIdempotentElem.mem_range_iff hP |>.mp hx
  calc
    ‖x - Q x‖ = ‖(P - Q) x‖ := by simp [hPx]
    _ ≤ ‖P - Q‖ * ‖x‖ := (P - Q).le_opNorm x

/-- For a unit-bounded vector in the range of `P`, the operator distance `‖P-Q‖` itself bounds
the error of approximation by a vector in the range of `Q`. -/
theorem exists_mem_range_norm_sub_le_norm_sub_of_mem_range_of_norm_le_one
    (P Q : H →L[K] H) (hP : IsIdempotentElem P.toLinearMap)
    (x : H) (hx : x ∈ LinearMap.range P.toLinearMap) (hxnorm : ‖x‖ ≤ 1) :
    ∃ y ∈ LinearMap.range Q.toLinearMap, ‖x - y‖ ≤ ‖P - Q‖ := by
  obtain ⟨y, hy, hxy⟩ :=
    exists_mem_range_norm_sub_le_of_mem_range P Q hP x hx
  refine ⟨y, hy, hxy.trans ?_⟩
  simpa using mul_le_of_le_one_right (norm_nonneg (P - Q)) hxnorm

/-- Norm-convergent idempotents have bilaterally convergent unit-range sets: eventually every
unit vector in either range is within any prescribed positive error of the other range. -/
theorem eventually_unit_ranges_mutually_approximated_of_tendsto
    {I : Type*} {l : Filter I}
    (Pseq : I → H →L[K] H) (P : H →L[K] H)
    (hconv : Tendsto Pseq l (𝓝 P))
    (hidemSeq : ∀ᶠ i in l, IsIdempotentElem (Pseq i).toLinearMap)
    (hidem : IsIdempotentElem P.toLinearMap) :
    ∀ ε > 0, ∀ᶠ i in l,
      (∀ x, x ∈ LinearMap.range (Pseq i).toLinearMap → ‖x‖ ≤ 1 →
        ∃ y, y ∈ LinearMap.range P.toLinearMap ∧ ‖x - y‖ < ε) ∧
      (∀ y, y ∈ LinearMap.range P.toLinearMap → ‖y‖ ≤ 1 →
        ∃ x, x ∈ LinearMap.range (Pseq i).toLinearMap ∧ ‖y - x‖ < ε) := by
  intro ε hε
  have hnorm : Tendsto (fun i ↦ ‖Pseq i - P‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hconv
  have hclose : ∀ᶠ i in l, ‖Pseq i - P‖ < ε :=
    hnorm.eventually (Iio_mem_nhds hε)
  filter_upwards [hidemSeq, hclose] with i hi hdist
  constructor
  · intro x hx hxnorm
    obtain ⟨y, hy, hxy⟩ :=
      exists_mem_range_norm_sub_le_norm_sub_of_mem_range_of_norm_le_one
        (Pseq i) P hi x hx hxnorm
    exact ⟨y, hy, hxy.trans_lt hdist⟩
  · intro y hy hynorm
    obtain ⟨x, hx, hyx⟩ :=
      exists_mem_range_norm_sub_le_norm_sub_of_mem_range_of_norm_le_one
        P (Pseq i) hidem y hy hynorm
    have hdist' : ‖P - Pseq i‖ < ε := by
      simpa only [norm_sub_rev] using hdist
    exact ⟨x, hx, hyx.trans_lt hdist'⟩

/-- Orthogonal projections converging in operator norm have bilaterally convergent unit-range
sets. -/
theorem eventually_unit_ranges_mutually_approximated_of_starProjection_tendsto
    {I : Type*} {l : Filter I}
    [Star (H →L[K] H)]
    (Pseq : I → H →L[K] H) (P : H →L[K] H)
    (hconv : Tendsto Pseq l (𝓝 P))
    (hstarSeq : ∀ᶠ i in l, IsStarProjection (Pseq i))
    (hstar : IsStarProjection P) :
    ∀ ε > 0, ∀ᶠ i in l,
      (∀ x, x ∈ LinearMap.range (Pseq i).toLinearMap → ‖x‖ ≤ 1 →
        ∃ y, y ∈ LinearMap.range P.toLinearMap ∧ ‖x - y‖ < ε) ∧
      (∀ y, y ∈ LinearMap.range P.toLinearMap → ‖y‖ ≤ 1 →
        ∃ x, x ∈ LinearMap.range (Pseq i).toLinearMap ∧ ‖y - x‖ < ε) := by
  exact eventually_unit_ranges_mutually_approximated_of_tendsto
    Pseq P hconv
      (hstarSeq.mono fun _ hi ↦
        ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr
          hi.isIdempotentElem)
      (ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr
        hstar.isIdempotentElem)


end NCG.ProjectionStability
