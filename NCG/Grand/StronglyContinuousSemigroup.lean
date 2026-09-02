/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Strongly continuous linear semigroups

A lightweight C₀-semigroup interface for continuous linear maps.  Mathlib
currently has no unbounded-generator semigroup API, so this module records the
exact algebraic and strong-continuity data needed by the Gran-Tensor analytic
layer, together with the right-derivative generator relation.
-/

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace NCG

universe u v w

variable (K : Type u) [RCLike K]
variable (E : Type v) [NormedAddCommGroup E] [NormedSpace K E]
  [NormedSpace ℝ E] [IsScalarTower ℝ K E]

/-- A strongly continuous semigroup of bounded linear operators, represented
on real time and constrained on the physical half-line `t ≥ 0`.  Values at
negative time are deliberately unspecified. -/
structure StronglyContinuousSemigroup where
  /-- The time-indexed bounded operator. -/
  toFun : ℝ → E →L[K] E
  map_zero : toFun 0 = 1
  map_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
    toFun (s + t) = (toFun s).comp (toFun t)
  stronglyContinuous : ∀ x : E,
    ContinuousOn (fun t ↦ toFun t x) (Ici 0)

namespace StronglyContinuousSemigroup

variable {K E}

instance : CoeFun (StronglyContinuousSemigroup K E)
    (fun _ ↦ ℝ → E →L[K] E) :=
  ⟨StronglyContinuousSemigroup.toFun⟩

omit [NormedSpace ℝ E] [IsScalarTower ℝ K E] in
@[simp] theorem apply_zero (S : StronglyContinuousSemigroup K E) :
    S 0 = 1 := S.map_zero

omit [NormedSpace ℝ E] [IsScalarTower ℝ K E] in
theorem apply_add (S : StronglyContinuousSemigroup K E)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    S (s + t) = (S s).comp (S t) :=
  S.map_add s t hs ht

omit [NormedSpace ℝ E] [IsScalarTower ℝ K E] in
theorem continuousOn_orbit (S : StronglyContinuousSemigroup K E) (x : E) :
    ContinuousOn (fun t ↦ S t x) (Ici 0) :=
  S.stronglyContinuous x

/-- A strongly continuous semigroup is uniformly bounded in operator norm
on every compact nonnegative time interval.  This is the usual
Banach--Steinhaus consequence of pointwise compact-orbit boundedness. -/
theorem exists_norm_le_on_Icc
    (S : StronglyContinuousSemigroup K E) [CompleteSpace E]
    (t : ℝ) :
    ∃ B : ℝ, ∀ q ∈ Icc (0 : ℝ) t, ‖S q‖ ≤ B := by
  let I := {q : ℝ // q ∈ Icc (0 : ℝ) t}
  obtain ⟨B, hB⟩ := banach_steinhaus
      (g := fun q : I ↦ S q.1) (fun x ↦ by
    obtain ⟨C, hC⟩ :=
      isCompact_Icc.bddAbove_image
        ((S.continuousOn_orbit x).norm.mono Icc_subset_Ici_self)
    refine ⟨C, fun q ↦ hC ?_⟩
    exact ⟨q.1, q.2, rfl⟩)
  exact ⟨B, fun q hq ↦ hB ⟨q, hq⟩⟩

/-- A vector `x` belongs to the right-generator graph with generator value
`Ax` when its semigroup orbit has that right derivative at zero. -/
def IsRightGeneratorVector (S : StronglyContinuousSemigroup K E)
    (x Ax : E) : Prop :=
  HasDerivWithinAt (fun t : ℝ ↦ S t x) Ax (Ici 0) 0

omit [IsScalarTower ℝ K E] in
theorem isRightGeneratorVector_iff
    (S : StronglyContinuousSemigroup K E) (x Ax : E) :
    S.IsRightGeneratorVector x Ax ↔
      HasDerivWithinAt (fun t : ℝ ↦ S t x) Ax (Ici 0) 0 :=
  Iff.rfl

omit [IsScalarTower ℝ K E] in
/-- The right-generator value of a fixed vector is unique. -/
theorem rightGeneratorVector_unique
    (S : StronglyContinuousSemigroup K E) {x Ax Ax' : E}
    (hAx : S.IsRightGeneratorVector x Ax)
    (hAx' : S.IsRightGeneratorVector x Ax') :
    Ax = Ax' := by
  exact UniqueDiffWithinAt.eq_deriv (Ici (0 : ℝ))
    (uniqueDiffWithinAt_Ici 0) hAx hAx'

/-- The semigroup law propagates a right-generator derivative at zero to a
right derivative of the shifted orbit. -/
theorem hasDerivWithinAt_shifted_orbit
    (S : StronglyContinuousSemigroup K E) {x Ax : E}
    (hAx : S.IsRightGeneratorVector x Ax) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun h : ℝ ↦ S (t + h) x) (S t Ax) (Ici 0) 0 := by
  have hfixed : HasDerivWithinAt
      (fun h : ℝ ↦ S t (S h x)) (S t Ax) (Ici 0) 0 :=
    ((S t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt 0 hAx
  apply hfixed.congr_of_mem
  · intro h hh
    exact DFunLike.congr_fun (S.apply_add ht hh) x
  · exact self_mem_Ici

/-- A generator vector has the expected right derivative at every
nonnegative time: `d⁺/dt S(t)x = S(t)Ax`. -/
theorem hasDerivWithinAt_orbit_Ioi
    (S : StronglyContinuousSemigroup K E) {x Ax : E}
    (hAx : S.IsRightGeneratorVector x Ax) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r : ℝ ↦ S r x) (S t Ax) (Ioi t) t := by
  have hshift := S.hasDerivWithinAt_shifted_orbit hAx ht
  have hsub : HasDerivWithinAt (fun r : ℝ ↦ r - t) 1 (Ioi t) t :=
    (hasDerivWithinAt_id t (Ioi t)).sub_const t
  have hmaps : MapsTo (fun r : ℝ ↦ r - t) (Ioi t) (Ici 0) := by
    intro r hr
    have htr : t < r := by simpa only [mem_Ioi] using hr
    exact sub_nonneg.mpr htr.le
  have hcomp := hshift.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq
    t hsub hmaps (by simp)
  convert hcomp using 1 <;> simp [Function.comp_def]

/-- In particular, every generator vector stays in the generator graph and
its generator value evolves by the same semigroup. -/
theorem isRightGeneratorVector_orbit
    (S : StronglyContinuousSemigroup K E) {x Ax : E}
    (hAx : S.IsRightGeneratorVector x Ax) {t : ℝ} (ht : 0 ≤ t) :
    S.IsRightGeneratorVector (S t x) (S t Ax) := by
  have hshift := S.hasDerivWithinAt_shifted_orbit hAx ht
  apply hshift.congr_of_mem
  · intro h hh
    calc
      S h (S t x) = S (h + t) x := by
        simpa using (DFunLike.congr_fun (S.apply_add hh ht) x).symm
      _ = S (t + h) x := by rw [add_comm]
  · exact self_mem_Ici

section Complete

variable [CompleteSpace E]

/-- On every strictly positive time, a generator orbit has a genuine
two-sided derivative.  The proof uses uniqueness for continuous paths with a
continuous right derivative, comparing the orbit with the interval integral
of `r ↦ S(r)Ax`. -/
theorem hasDerivAt_orbit
    (S : StronglyContinuousSemigroup K E) {x Ax : E}
    (hAx : S.IsRightGeneratorVector x Ax) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r : ℝ ↦ S r x) (S t Ax) t := by
  let a : ℝ := t / 2
  let b : ℝ := 3 * t / 2
  let f : ℝ → E := fun r ↦ S r x
  let g : ℝ → E := fun r ↦ S r Ax
  let G : ℝ → E := fun r ↦ f a + ∫ u in a..r, g u
  have ha : 0 < a := by dsimp [a]; linarith
  have hat : a < t := by dsimp [a]; linarith
  have htb : t < b := by dsimp [b]; linarith
  have hab : a < b := hat.trans htb
  have hnonneg : ∀ y ∈ Icc a b, 0 ≤ y := by
    intro y hy
    exact ha.le.trans hy.1
  have hfcont : ContinuousOn f (Icc a b) := by
    exact (S.continuousOn_orbit x).mono fun y hy ↦ hnonneg y hy
  have hgcont : ContinuousOn g (Icc a b) := by
    exact (S.continuousOn_orbit Ax).mono fun y hy ↦ hnonneg y hy
  have hg_at : ∀ y ∈ Icc a b, ContinuousAt g y := by
    intro y hy
    exact (S.continuousOn_orbit Ax).continuousAt
      (Ici_mem_nhds (ha.trans_le hy.1))
  have hg_open : ∀ y ∈ Ioi (0 : ℝ), ContinuousAt g y := by
    intro y hy
    exact (S.continuousOn_orbit Ax).continuousAt (Ici_mem_nhds hy)
  have hGderiv : ∀ y ∈ Icc a b, HasDerivAt G (g y) y := by
    intro y hy
    have hay : a ≤ y := hy.1
    have hgay : ContinuousOn g (Icc a y) :=
      hgcont.mono (Icc_subset_Icc_right hy.2)
    have hint : IntervalIntegrable g volume a y :=
      hgay.intervalIntegrable_of_Icc hay
    have hmeas := ContinuousAt.stronglyMeasurableAtFilter (μ := volume)
      isOpen_Ioi hg_open y (ha.trans_le hy.1)
    have hintDeriv := intervalIntegral.integral_hasDerivAt_right hint
      hmeas (hg_at y hy)
    simpa only [G] using hintDeriv.const_add (f a)
  have hGcont : ContinuousOn G (Icc a b) :=
    HasDerivAt.continuousOn hGderiv
  have hfRight : ∀ y ∈ Ico a b,
      HasDerivWithinAt f (g y) (Ici y) y := by
    intro y hy
    have hy0 : 0 ≤ y := ha.le.trans hy.1
    exact (S.hasDerivWithinAt_orbit_Ioi hAx hy0).Ici_of_Ioi
  have hGRight : ∀ y ∈ Ico a b,
      HasDerivWithinAt G (g y) (Ici y) y := by
    intro y hy
    exact (hGderiv y ⟨hy.1, hy.2.le⟩).hasDerivWithinAt
  have hsame : ∀ y ∈ Icc a b, f y = G y := by
    apply eq_of_has_deriv_right_eq hfRight hGRight hfcont hGcont
    simp only [G, intervalIntegral.integral_same, add_zero]
  have hnear : f =ᶠ[𝓝 t] G := by
    filter_upwards [Ioo_mem_nhds hat htb] with y hy
    exact hsame y ⟨hy.1.le, hy.2.le⟩
  exact (hGderiv t ⟨hat.le, htb.le⟩).congr_of_eventuallyEq hnear

/-- Backward-time form of positive-time generator-orbit differentiability,
as used by the left factor in Duhamel's product path. -/
theorem hasDerivAt_const_sub_orbit
    (S : StronglyContinuousSemigroup K E) {x Ax : E}
    (hAx : S.IsRightGeneratorVector x Ax) {total r : ℝ}
    (hr : 0 < total - r) :
    HasDerivAt (fun s : ℝ ↦ S (total - s) x)
      (-(S (total - r) Ax)) r := by
  exact (S.hasDerivAt_orbit hAx hr).comp_const_sub total r

end Complete

variable {F : Type w} [NormedAddCommGroup F] [NormedSpace K F]
  [NormedSpace ℝ F] [IsScalarTower ℝ K F]

/-- Intertwining one orbit at every nonnegative time forces intertwining of
the corresponding right-generator values.  This pointwise form is the
natural one for graph-domain carriers. -/
theorem generatorIntertwining_of_semigroupIntertwining_on_vector
    (S : StronglyContinuousSemigroup K E)
    (T : StronglyContinuousSemigroup K F)
    (V : E →L[K] F) {x Ax : E} {NVx : F}
    (hintertwine : ∀ t : ℝ, 0 ≤ t →
      T t (V x) = V (S t x))
    (hAx : S.IsRightGeneratorVector x Ax)
    (hNVx : T.IsRightGeneratorVector (V x) NVx) :
    NVx = V Ax := by
  have hVAx : HasDerivWithinAt
      (fun t : ℝ ↦ V (S t x)) (V Ax) (Ici 0) 0 :=
    (V.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt 0 hAx
  have htransfer : HasDerivWithinAt
      (fun t : ℝ ↦ T t (V x)) (V Ax) (Ici 0) 0 := by
    apply hVAx.congr_of_mem
    · intro t ht
      exact hintertwine t ht
    · exact self_mem_Ici
  exact UniqueDiffWithinAt.eq_deriv (Ici (0 : ℝ))
    (uniqueDiffWithinAt_Ici 0) hNVx htransfer

/-- Intertwining all nonnegative-time semigroup operators forces
intertwining of their right generators.  This is the exact differentiation
at `t = 0` implication for possibly unbounded generators, stated on their
generator graphs. -/
theorem generatorIntertwining_of_semigroupIntertwining
    (S : StronglyContinuousSemigroup K E)
    (T : StronglyContinuousSemigroup K F)
    (V : E →L[K] F) {x Ax : E} {NVx : F}
    (hintertwine : ∀ t : ℝ, 0 ≤ t →
      (T t).comp V = V.comp (S t))
    (hAx : S.IsRightGeneratorVector x Ax)
    (hNVx : T.IsRightGeneratorVector (V x) NVx) :
    NVx = V Ax :=
  generatorIntertwining_of_semigroupIntertwining_on_vector
    S T V (fun t ht ↦ DFunLike.congr_fun (hintertwine t ht) x) hAx hNVx

end StronglyContinuousSemigroup

end NCG
