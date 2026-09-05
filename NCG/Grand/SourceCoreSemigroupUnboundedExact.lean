/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.StronglyContinuousSemigroupDuhamel
import NCG.Grand.UnboundedResolventDefect

/-!
# Unbounded source-core semigroup intertwining

This module gives the graph-domain version of
`thm:source-core-semigroup`.  The source generator is represented by its
Banach graph carrier `DA`, continuous inclusion `iA`, and graph-bounded
action `A`.  The restricted semigroup `SD` transports the graph carrier,
while `S` is the ambient source semigroup.

The results include the generator/semigroup equivalence, the exact
graph-domain resolvent defect identity, Duhamel's formula for every graph
vector, and the manuscript's operator-norm estimate with the square-root
leakage/compression residual.
-/

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace NCG
namespace SourceCoreSemigroup

universe u v w x y

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace K E]
  [NormedSpace ℝ E] [IsScalarTower ℝ K E] [CompleteSpace E]
variable {H : Type w} [NormedAddCommGroup H] [NormedSpace K H]
  [NormedSpace ℝ H] [IsScalarTower ℝ K H] [CompleteSpace H]
variable {DA : Type x} [NormedAddCommGroup DA] [NormedSpace K DA]
  [NormedSpace ℝ DA] [IsScalarTower ℝ K DA] [CompleteSpace DA]
variable {DN : Type y} [NormedAddCommGroup DN] [NormedSpace K DN]

open StronglyContinuousSemigroup

/-- The ambient generator action commutes with the lifted graph semigroup.
This standard invariance fact follows only from uniqueness of the
right-generator value. -/
theorem graphGeneratorAction_apply_semigroup
    (S : StronglyContinuousSemigroup K E)
    (SD : StronglyContinuousSemigroup K DA)
    (iA : DA →L[K] E) (A : DA →L[K] E)
    (hSD : ∀ t : ℝ, 0 ≤ t →
      iA.comp (SD t) = (S t).comp iA)
    (hAgen : ∀ x : DA, S.IsRightGeneratorVector (iA x) (A x))
    (x : DA) {t : ℝ} (ht : 0 ≤ t) :
    A (SD t x) = S t (A x) := by
  have horbit := S.isRightGeneratorVector_orbit (hAgen x) ht
  have hembed : iA (SD t x) = S t (iA x) := by
    exact DFunLike.congr_fun (hSD t ht) x
  have horbit' : S.IsRightGeneratorVector
      (iA (SD t x)) (S t (A x)) := by
    simpa only [hembed] using horbit
  exact S.rightGeneratorVector_unique (hAgen (SD t x)) horbit'

/-- Exact Duhamel formula on an unbounded source generator's graph carrier.
No bounded-generator assumption is made. -/
theorem unbounded_duhamel
    (S : StronglyContinuousSemigroup K E)
    (SD : StronglyContinuousSemigroup K DA)
    (T : StronglyContinuousSemigroup K H)
    (iA : DA →L[K] E) (A : DA →L[K] E)
    (iN : DN →L[K] H) (N : DN →L[K] H)
    (V : E →L[K] H) (Vdom : DA →L[K] DN)
    (R : DA →L[K] H)
    (hSD : ∀ t : ℝ, 0 ≤ t →
      iA.comp (SD t) = (S t).comp iA)
    (hAgen : ∀ x : DA, S.IsRightGeneratorVector (iA x) (A x))
    (hNgen : ∀ y : DN, T.IsRightGeneratorVector (iN y) (N y))
    (hVdom : iN.comp Vdom = V.comp iA)
    (hR : R = N.comp Vdom - V.comp A)
    (x : DA) {t : ℝ} (ht : 0 ≤ t) :
    T t (V (iA x)) - V (iA (SD t x)) =
      ∫ s in 0..t, T (t - s) (R (SD s x)) := by
  obtain ⟨B, hTbound⟩ := T.exists_norm_le_on_Icc t
  let Vg : DA →L[K] H := V.comp iA
  have hpath : ContinuousOn
      (fun r ↦ T (t - r) (Vg (SD r x))) (Icc (0 : ℝ) t) :=
    continuousOn_constSub_apply_orbit SD T Vg x hTbound
  have hintegrand : ContinuousOn
      (fun s ↦ T (t - s) (R (SD s x))) (Icc (0 : ℝ) t) :=
    continuousOn_constSub_apply_orbit SD T R x hTbound
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) t,
      HasDerivWithinAt (fun r ↦ T (t - r) (Vg (SD r x)))
        (-(T (t - s) (R (SD s x)))) (Ioi s) s := by
    intro s hs
    have hambient := S.hasDerivAt_orbit (hAgen x) hs.1
    have hsource0 : HasDerivAt
        (fun r ↦ V (S r (iA x))) (V (S s (A x))) s :=
      (V.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hambient
    have hevent : (fun r ↦ V (iA (SD r x))) =ᶠ[𝓝 s]
        (fun r ↦ V (S r (iA x))) := by
      filter_upwards [Ici_mem_nhds hs.1] with r hr
      exact congrArg V (DFunLike.congr_fun (hSD r hr) x)
    have hsource : HasDerivAt
        (fun r ↦ V (iA (SD r x))) (V (S s (A x))) s :=
      hsource0.congr_of_eventuallyEq hevent
    let y : DA := SD s x
    have htarget0 := hNgen (Vdom y)
    have hbase : iN (Vdom y) = V (iA y) :=
      DFunLike.congr_fun hVdom y
    have htarget : T.IsRightGeneratorVector
        (V (iA y)) (N (Vdom y)) := by
      simpa only [hbase] using htarget0
    have hcomm : A y = S s (A x) :=
      graphGeneratorAction_apply_semigroup S SD iA A hSD hAgen x hs.1.le
    have hRpoint : R y = N (Vdom y) - V (A y) := by
      simpa only [ContinuousLinearMap.comp_apply, sub_apply] using
        DFunLike.congr_fun hR y
    have hdefect :
        N (Vdom y) = V (S s (A x)) + R y := by
      rw [← hcomm, hRpoint]
      abel
    exact (hasDerivAt_duhamelProductPath_of_sourcePath
      T (fun r ↦ V (iA (SD r x))) (fun r ↦ R (SD r x))
      hs.1 hs.2 hsource htarget hdefect
      ⟨B, eventually_norm_constSub_restrictScalars_le
        T hs.1 hs.2 hTbound⟩).hasDerivWithinAt
  simpa only [Vg, ContinuousLinearMap.comp_apply] using
    semigroupDefect_eq_duhamel_of_rightPathDerivative
      T SD Vg R t x ht T.map_zero SD.map_zero hpath hderiv
        (hintegrand.intervalIntegrable_of_Icc ht)

/-- On graph domains, generator intertwining is equivalent to semigroup
intertwining for every nonnegative time. -/
theorem unbounded_generatorIntertwining_iff_semigroupIntertwining
    (S : StronglyContinuousSemigroup K E)
    (SD : StronglyContinuousSemigroup K DA)
    (T : StronglyContinuousSemigroup K H)
    (iA : DA →L[K] E) (A : DA →L[K] E)
    (iN : DN →L[K] H) (N : DN →L[K] H)
    (V : E →L[K] H) (Vdom : DA →L[K] DN)
    (hSD : ∀ t : ℝ, 0 ≤ t →
      iA.comp (SD t) = (S t).comp iA)
    (hAgen : ∀ x : DA, S.IsRightGeneratorVector (iA x) (A x))
    (hNgen : ∀ y : DN, T.IsRightGeneratorVector (iN y) (N y))
    (hVdom : iN.comp Vdom = V.comp iA) :
    N.comp Vdom = V.comp A ↔
      ∀ t : ℝ, 0 ≤ t →
        (T t).comp (V.comp iA) = (V.comp iA).comp (SD t) := by
  constructor
  · intro hgen t ht
    let R : DA →L[K] H := N.comp Vdom - V.comp A
    have hRzero : R = 0 := by
      dsimp only [R]
      rw [hgen, sub_self]
    ext x
    have hduhamel := unbounded_duhamel
      S SD T iA A iN N V Vdom R hSD hAgen hNgen hVdom rfl x ht
    rw [hRzero] at hduhamel
    have hintegral :
        (∫ s in 0..t, T (t - s) ((0 : DA →L[K] H) (SD s x))) = 0 := by
      simp
    rw [hintegral] at hduhamel
    exact sub_eq_zero.mp hduhamel
  · intro hintertwine
    ext x
    have htarget0 := hNgen (Vdom x)
    have hbase : iN (Vdom x) = V (iA x) :=
      DFunLike.congr_fun hVdom x
    have htarget : T.IsRightGeneratorVector
        (V (iA x)) (N (Vdom x)) := by
      simpa only [hbase] using htarget0
    apply generatorIntertwining_of_semigroupIntertwining_on_vector
      S T V (hAx := hAgen x) (hNVx := htarget)
    intro t ht
    have hgraph := DFunLike.congr_fun (hintertwine t ht) x
    have hsource := DFunLike.congr_fun (hSD t ht) x
    simpa only [ContinuousLinearMap.comp_apply] using
      hgraph.trans (congrArg V hsource)

/-- The exact graph-domain resolvent defect identity, specialized to the
source-core data. -/
theorem unbounded_resolvent_defect
    (iA : DA →L[K] E) (A : DA →L[K] E)
    (iN : DN →L[K] H) (N : DN →L[K] H)
    (V : E →L[K] H) (Vdom : DA →L[K] DN)
    (R : DA →L[K] H) (RA : E →L[K] DA) (RN : H →L[K] DN)
    (z : K)
    (hVdom : iN.comp Vdom = V.comp iA)
    (hR : R = N.comp Vdom - V.comp A)
    (hRA : (z • iA - A).comp RA = 1)
    (hRN : RN.comp (z • iN - N) = 1) :
    iN.comp (RN.comp V) - V.comp (iA.comp RA) =
      iN.comp (RN.comp (R.comp RA)) :=
  graphDomain_resolvent_defect
    iA A iN N V Vdom R RA RN z hVdom hR hRA hRN

/-- Quantitative graph-norm Duhamel estimate with the exact exponential
convolution and the leakage/compression square-root residual. -/
theorem unbounded_semigroup_defect_bound
    (S : StronglyContinuousSemigroup K E)
    (SD : StronglyContinuousSemigroup K DA)
    (T : StronglyContinuousSemigroup K H)
    (iA : DA →L[K] E) (A : DA →L[K] E)
    (iN : DN →L[K] H) (N : DN →L[K] H)
    (V : E →L[K] H) (Vdom : DA →L[K] DN)
    (R : DA →L[K] H)
    (hSD : ∀ t : ℝ, 0 ≤ t →
      iA.comp (SD t) = (S t).comp iA)
    (hAgen : ∀ x : DA, S.IsRightGeneratorVector (iA x) (A x))
    (hNgen : ∀ y : DN, T.IsRightGeneratorVector (iN y) (N y))
    (hVdom : iN.comp Vdom = V.comp iA)
    (hRdef : R = N.comp Vdom - V.comp A)
    (MN MA omegaN omegaA deltaLeak deltaComp : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (hMN : 0 ≤ MN) (hMA : 0 ≤ MA)
    (hR : ‖R‖ ≤ Real.sqrt (deltaLeak + deltaComp))
    (hT : ∀ q : ℝ, 0 ≤ q →
      ‖T q‖ ≤ MN * Real.exp (omegaN * q))
    (hSDbound : ∀ q : ℝ, 0 ≤ q →
      ‖SD q‖ ≤ MA * Real.exp (omegaA * q)) :
    ‖(T t).comp (V.comp iA) - (V.comp iA).comp (SD t)‖ ≤
      MN * MA * exponentialConvolution t omegaN omegaA *
        Real.sqrt (deltaLeak + deltaComp) := by
  apply opNorm_semigroupDefect_le_sqrt_residual
    T SD R ((T t).comp (V.comp iA) - (V.comp iA).comp (SD t))
      t MN MA omegaN omegaA deltaLeak deltaComp
      ht hMN hMA hR
  · intro s hs
    exact hT (t - s) (sub_nonneg.mpr hs.2)
  · intro s hs
    exact hSDbound s hs.1
  · intro x
    simpa only [sub_apply,
      ContinuousLinearMap.comp_apply] using
      unbounded_duhamel S SD T iA A iN N V Vdom R
        hSD hAgen hNgen hVdom hRdef x ht

end SourceCoreSemigroup
end NCG
