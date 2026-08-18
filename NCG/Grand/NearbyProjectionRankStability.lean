/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RieszProjectionStability
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Rank stability of nearby projections

Two idempotent bounded operators at operator-norm distance strictly less than one have linearly
isomorphic finite-dimensional ranges.  This file proves the rank consequence needed to turn
Riesz-projection convergence into stability of isolated spectral multiplicities.
-/

open Filter Topology

noncomputable section

namespace NCG.ProjectionStability

universe u v

variable {K : Type u} [NontriviallyNormedField K]
variable {H : Type v} [NormedAddCommGroup H] [NormedSpace K H]

/-- Restrict `Q` to the range of `P`, with codomain the range of `Q`. -/
def rangeMap (P Q : H →L[K] H) :
    LinearMap.range P.toLinearMap →ₗ[K] LinearMap.range Q.toLinearMap :=
  Q.toLinearMap.rangeRestrict.comp (LinearMap.range P.toLinearMap).subtype

/-- If two idempotents are less than one apart in operator norm, applying the second projection
to the range of the first is injective. -/
theorem rangeMap_injective_of_norm_sub_lt_one
    (P Q : H →L[K] H)
    (hP : IsIdempotentElem P.toLinearMap)
    (hPQ : ‖P - Q‖ < 1) : Function.Injective (rangeMap P Q) := by
  intro x y hxy
  apply sub_eq_zero.mp
  let u := x - y
  have hu : rangeMap P Q u = 0 := by
    dsimp [u]
    rw [map_sub, hxy, sub_self]
  change u = 0
  apply Subtype.ext
  change (u : H) = 0
  have hQu : Q (u : H) = 0 := by
    have := congrArg Subtype.val hu
    simpa [rangeMap] using this
  have hPu : P (u : H) = u := LinearMap.IsIdempotentElem.mem_range_iff hP |>.mp u.property
  have hdiff : (P - Q) (u : H) = u := by
    simp [hPu, hQu]
  have hbound : ‖(u : H)‖ ≤ ‖P - Q‖ * ‖(u : H)‖ := by
    calc
      ‖(u : H)‖ = ‖(P - Q) (u : H)‖ := congrArg norm hdiff.symm
      _ ≤ ‖P - Q‖ * ‖(u : H)‖ := (P - Q).le_opNorm (u : H)
  by_contra hu0
  have hupos : 0 < ‖(u : H)‖ := norm_pos_iff.mpr hu0
  have hstrict : ‖P - Q‖ * ‖(u : H)‖ < ‖(u : H)‖ := by
    simpa using mul_lt_mul_of_pos_right hPQ hupos
  exact (not_lt_of_ge hbound) hstrict

/-- Finite-dimensional ranges of idempotents at distance less than one have equal dimension. -/
theorem finrank_range_eq_of_norm_sub_lt_one
    (P Q : H →L[K] H)
    (hP : IsIdempotentElem P.toLinearMap)
    (hQ : IsIdempotentElem Q.toLinearMap)
    (hPQ : ‖P - Q‖ < 1)
    [Module.Finite K (LinearMap.range P.toLinearMap)]
    [Module.Finite K (LinearMap.range Q.toLinearMap)] :
    Module.finrank K (LinearMap.range P.toLinearMap) =
      Module.finrank K (LinearMap.range Q.toLinearMap) := by
  apply le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective
      (rangeMap_injective_of_norm_sub_lt_one P Q hP hPQ)
  · exact LinearMap.finrank_le_finrank_of_injective
      (rangeMap_injective_of_norm_sub_lt_one Q P hQ (by simpa [norm_sub_rev] using hPQ))

/-- A norm-convergent family of finite-rank idempotents has eventually constant range dimension.
This is the abstract isolated-spectral-multiplicity consequence of Riesz-projection convergence. -/
theorem eventually_finrank_range_eq_of_tendsto
    {I : Type*} {l : Filter I} (Pseq : I → H →L[K] H) (P : H →L[K] H)
    (hconv : Tendsto Pseq l (𝓝 P))
    (hidem_seq : ∀ᶠ i in l, IsIdempotentElem (Pseq i).toLinearMap)
    (hidem : IsIdempotentElem P.toLinearMap)
    (hfinite_seq : ∀ᶠ i in l,
      Module.Finite K (LinearMap.range (Pseq i).toLinearMap))
    [Module.Finite K (LinearMap.range P.toLinearMap)] :
    ∀ᶠ i in l,
      Module.finrank K (LinearMap.range (Pseq i).toLinearMap) =
        Module.finrank K (LinearMap.range P.toLinearMap) := by
  have hnorm :
      Tendsto (fun i ↦ ‖Pseq i - P‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hconv
  have hclose : ∀ᶠ i in l, ‖Pseq i - P‖ < 1 :=
    hnorm.eventually (Iio_mem_nhds zero_lt_one)
  filter_upwards [hidem_seq, hfinite_seq, hclose] with i hi hfinite hdist
  letI : Module.Finite K (LinearMap.range (Pseq i).toLinearMap) :=
    hfinite
  exact finrank_range_eq_of_norm_sub_lt_one (Pseq i) P hi hidem hdist
end NCG.ProjectionStability
