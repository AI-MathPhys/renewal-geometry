/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Star
import Mathlib.Algebra.Star.StarProjection

/-!
# Idempotence under norm limits

Idempotence is closed under convergence in a normed ring.  This elementary lemma lets contour
projection convergence supply idempotence of the limiting Riesz operator automatically once the
cutoff contour operators are known to be idempotent.
-/

open Filter Topology

namespace NCG

universe u v

/-- A limit of eventually idempotent elements in a normed ring is idempotent. -/
theorem isIdempotentElem_of_tendsto
    {A : Type u} [NormedRing A] [ContinuousMul A]
    {I : Type v} {l : Filter I} [NeBot l]
    (a : I → A) (alim : A) (ha : Tendsto a l (nhds alim))
    (hidem : ∀ᶠ i in l, IsIdempotentElem (a i)) :
    IsIdempotentElem alim := by
  have hmul : Tendsto (fun i ↦ a i * a i) l (nhds (alim * alim)) := ha.mul ha
  have hmul' : Tendsto (fun i ↦ a i * a i) l (nhds alim) :=
    ha.congr' (hidem.mono fun i hi ↦ hi.symm)
  exact tendsto_nhds_unique hmul hmul'

/-- A limit of eventually orthogonal projections is an orthogonal projection. -/
theorem isStarProjection_of_tendsto
    {A : Type u} [NormedRing A] [StarRing A] [ContinuousMul A] [ContinuousStar A]
    {I : Type v} {l : Filter I} [NeBot l]
    (a : I → A) (alim : A) (ha : Tendsto a l (nhds alim))
    (hproj : ∀ᶠ i in l, IsStarProjection (a i)) :
    IsStarProjection alim := by
  refine ⟨isIdempotentElem_of_tendsto a alim ha
    (hproj.mono fun _ hi ↦ hi.isIdempotentElem), ?_⟩
  have hstar : Tendsto (fun i ↦ star (a i)) l (nhds (star alim)) := ha.star
  have hstar' : Tendsto (fun i ↦ star (a i)) l (nhds alim) :=
    ha.congr' (hproj.mono fun _ hi ↦ hi.isSelfAdjoint.symm)
  exact tendsto_nhds_unique hstar hstar'

end NCG
