/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertMosco
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Compressed operators on a common Hilbert carrier

For an isometric stage embedding `Jₙ`, its adjoint supplies the canonical lift `Jₙ†` from the
common carrier.  Asymptotic density forces the range projections `Jₙ Jₙ†` to converge strongly to
the identity.  Consequently varying-space strong operator convergence implies literal pointwise
convergence of the compressed common-carrier operators `Jₙ Tₙ Jₙ†`.
-/

open Filter Topology
open scoped InnerProduct

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- The canonical adjoint lift from the common carrier to stage `n`. -/
def adjointLift (n : ℕ) : H →L[K] Hn n :=
  (J.embedding n).toContinuousLinearMap†

/-- Orthogonal projection of the common carrier onto the range of the stage embedding. -/
def rangeProjection (n : ℕ) : H →L[K] H :=
  (J.embedding n).toContinuousLinearMap.comp (J.adjointLift n)

/-- The manuscript's common-carrier compression `Jₙ Tₙ Jₙ†`. -/
def compressedOperator (Tn : ∀ n, Hn n →L[K] Hn n) (n : ℕ) : H →L[K] H :=
  (J.embedding n).toContinuousLinearMap.comp
    ((Tn n).comp (J.adjointLift n))

/-- The stage-range projection is at least as good an approximation as every point in the stage
range. -/
theorem norm_sub_rangeProjection_le (n : ℕ) (x : H) (y : Hn n) :
    ‖x - J.rangeProjection n x‖ ≤ ‖x - J.embedding n y‖ := by
  let e : Hn n →L[K] H := (J.embedding n).toContinuousLinearMap
  let p : H := e ((e†) x)
  have horth : inner K (x - p) (p - e y) = 0 := by
    change inner K (x - e ((e†) x)) (e ((e†) x) - e y) = 0
    rw [← map_sub, inner_sub_left,
      ← e.adjoint_inner_left ((e†) x - y) x]
    have hiso :
        inner K (e ((e†) x)) (e ((e†) x - y)) =
          inner K ((e†) x) ((e†) x - y) := by
      simpa [e] using (J.embedding n).inner_map_map ((e†) x) ((e†) x - y)
    rw [hiso, sub_self]
  have hdecomp : x - e y = (x - p) + (p - e y) := by abel
  have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (x - p) (p - e y) horth
  rw [← hdecomp] at hsq
  have hsquares : ‖x - p‖ ^ 2 ≤ ‖x - e y‖ ^ 2 := by
    nlinarith [sq_nonneg ‖p - e y‖]
  have hnorm : ‖x - p‖ ≤ ‖x - e y‖ := by
    nlinarith [norm_nonneg (x - p), norm_nonneg (x - e y)]
  simpa [rangeProjection, adjointLift, e, p] using hnorm

/-- Under asymptotic density, the canonical adjoint lifts converge strongly to their common-space
source. -/
theorem stronglyConverges_adjointLift
    (hdense : J.IsAsymptoticallyDense) (x : H) :
    J.StronglyConverges (fun n ↦ J.adjointLift n x) x := by
  obtain ⟨y, hy⟩ := hdense x
  rw [StronglyConverges, tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero
  · intro n
    exact norm_nonneg _
  · intro n
    simpa [rangeProjection, adjointLift, norm_sub_rev] using
      J.norm_sub_rangeProjection_le n x (y n)
  · simpa only [norm_sub_rev] using
      (tendsto_iff_norm_sub_tendsto_zero.mp hy)

/-- Every strongly convergent stage lift is asymptotically equal, in its
native stage norm, to the canonical adjoint lift of the same limit vector. -/
theorem StronglyConverges.norm_sub_adjointLift_tendsto_zero
    (hdense : J.IsAsymptoticallyDense) {x : ∀ n, Hn n} {xlim : H}
    (hx : J.StronglyConverges x xlim) :
    Tendsto (fun n ↦ ‖x n - J.adjointLift n xlim‖) atTop (nhds 0) := by
  have hadj := J.stronglyConverges_adjointLift hdense xlim
  have hdiff : J.StronglyConverges
      (fun n ↦ x n - J.adjointLift n xlim) (xlim - xlim) := by
    simpa [sub_eq_add_neg] using
      StronglyConverges.add J hx (StronglyConverges.smul J (-1 : K) hadj)
  rw [StronglyConverges] at hdiff
  have hnorm := hdiff.norm
  simpa only [LinearIsometry.norm_map, sub_self, norm_zero] using hnorm

/-- Varying-space strong convergence gives pointwise strong convergence of the literal
common-carrier compressions `Jₙ Tₙ Jₙ†`. -/
theorem compressedOperator_tendsto
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (hT : J.StrongOperatorConverges J Tn T) (x : H) :
    Tendsto (fun n ↦ J.compressedOperator Tn n x) atTop (nhds (T x)) := by
  have hx := J.stronglyConverges_adjointLift hdense x
  have hout := hT (fun n ↦ J.adjointLift n x) x hx
  simpa [StronglyConverges, compressedOperator, adjointLift] using hout

end NCG.VaryingHilbert.System
