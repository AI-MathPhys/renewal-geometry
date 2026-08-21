/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DuhamelDefectBound
import NCG.Grand.StronglyContinuousSemigroup
import NCG.Grand.StrongOperatorCalculus

/-!
# Duhamel paths for strongly continuous semigroups

This module combines positive-time generator-orbit differentiability with
the locally bounded strong-operator product rule.  It derives the standard
Duhamel product-path derivative from generator graph data without assuming
operator-norm differentiability of a C₀ semigroup.
-/

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace NCG

universe u v w

variable {K : Type u} [RCLike K]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace K X]
  [NormedSpace ℝ X] [IsScalarTower ℝ K X] [CompleteSpace X]
variable {H : Type w} [NormedAddCommGroup H] [NormedSpace K H]
  [NormedSpace ℝ H] [IsScalarTower ℝ K H] [CompleteSpace H]

open StronglyContinuousSemigroup

omit [CompleteSpace H] in
/-- A uniform operator bound on `[0,t]` supplies the local realified bound
needed by the strong-operator product rule at every interior time. -/
theorem eventually_norm_constSub_restrictScalars_le
    (T : StronglyContinuousSemigroup K H) {t s B : ℝ}
    (hs : 0 < s) (hst : s < t)
    (hT : ∀ q ∈ Icc (0 : ℝ) t, ‖T q‖ ≤ B) :
    ∀ᶠ r in 𝓝 s, ‖(T (t - r)).restrictScalars ℝ‖ ≤ B := by
  filter_upwards [Ioo_mem_nhds hs hst] with r hr
  rw [ContinuousLinearMap.norm_restrictScalars]
  apply hT (t - r)
  constructor <;> linarith [hr.1, hr.2]

omit [CompleteSpace X] [CompleteSpace H] in
/-- A bounded bridge between two C₀ semigroup orbits gives a continuous
Duhamel-type product path on every compact positive-time interval. -/
theorem continuousOn_constSub_apply_orbit
    (S : StronglyContinuousSemigroup K X)
    (T : StronglyContinuousSemigroup K H)
    (Bop : X →L[K] H) (x : X) {t B : ℝ}
    (hTbound : ∀ q ∈ Icc (0 : ℝ) t, ‖T q‖ ≤ B) :
    ContinuousOn (fun r ↦ T (t - r) (Bop (S r x)))
      (Icc (0 : ℝ) t) := by
  intro s hs
  let Aop : ℝ → H →L[ℝ] H := fun r ↦
    (T (t - r)).restrictScalars ℝ
  let v : ℝ → H := fun r ↦ Bop (S r x)
  have hv : ContinuousWithinAt v (Icc (0 : ℝ) t) s := by
    apply (Bop.restrictScalars ℝ).continuous.continuousAt.comp_continuousWithinAt
    exact ((S.continuousOn_orbit x).continuousWithinAt hs.1).mono
      Icc_subset_Ici_self
  have hback : ContinuousWithinAt (fun r ↦ Aop r (v s))
      (Icc (0 : ℝ) t) s := by
    have horbit : ContinuousWithinAt (fun q ↦ T q (Bop (S s x)))
        (Ici 0) (t - s) :=
      (T.continuousOn_orbit (Bop (S s x))).continuousWithinAt
        (sub_nonneg.mpr hs.2)
    have hsub : ContinuousWithinAt (fun r : ℝ ↦ t - r)
        (Icc (0 : ℝ) t) s :=
      continuousWithinAt_const.sub continuousWithinAt_id
    have hmaps : MapsTo (fun r : ℝ ↦ t - r)
        (Icc (0 : ℝ) t) (Ici 0) := by
      intro r hr
      exact sub_nonneg.mpr hr.2
    change ContinuousWithinAt (fun r ↦ T (t - r) (Bop (S s x)))
      (Icc (0 : ℝ) t) s
    exact horbit.comp hsub hmaps
  have hlocal : ∃ C : ℝ, ∀ᶠ r in 𝓝[Icc (0 : ℝ) t] s,
      ‖Aop r‖ ≤ C := by
    refine ⟨B, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    change ‖(T (t - r)).restrictScalars ℝ‖ ≤ B
    rw [ContinuousLinearMap.norm_restrictScalars]
    apply hTbound (t - r)
    constructor <;> linarith [hr.1, hr.2]
  exact ContinuousWithinAt.clm_apply_of_strong Aop v (Icc (0 : ℝ) t)
    hv hback hlocal

/-- The Duhamel product-path derivative at one interior time.  Local
operator boundedness is required only for the strong-operator product rule;
it is automatic for a C₀ semigroup and follows immediately from any local
exponential bound. -/
theorem hasDerivAt_duhamelProductPath
    (S : StronglyContinuousSemigroup K X)
    (T : StronglyContinuousSemigroup K H)
    (V : X →L[K] H) (R : X →L[K] H)
    {x Ax : X} (hAx : S.IsRightGeneratorVector x Ax)
    {t s : ℝ} (hs : 0 < s) (hst : s < t)
    {NVs : H}
    (hTgen : T.IsRightGeneratorVector (V (S s x)) NVs)
    (hdefect : NVs = V (S s Ax) + R (S s x))
    (hbound : ∃ C : ℝ, ∀ᶠ r in 𝓝 s,
      ‖(T (t - r)).restrictScalars ℝ‖ ≤ C) :
    HasDerivAt (fun r ↦ T (t - r) (V (S r x)))
      (-(T (t - s) (R (S s x)))) s := by
  let Aop : ℝ → H →L[ℝ] H := fun r ↦
    (T (t - r)).restrictScalars ℝ
  let v : ℝ → H := fun r ↦ V (S r x)
  have hsource : HasDerivAt v (V (S s Ax)) s := by
    exact (V.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
      (S.hasDerivAt_orbit hAx hs)
  have htarget : HasDerivAt (fun r ↦ Aop r (v s))
      (-(T (t - s) NVs)) s := by
    change HasDerivAt (fun r ↦ T (t - r) (V (S s x)))
      (-(T (t - s) NVs)) s
    exact T.hasDerivAt_const_sub_orbit hTgen (sub_pos.mpr hst)
  have hstrong : ContinuousAt (fun r ↦ Aop r (V (S s Ax))) s := by
    have horbit : ContinuousAt (fun q ↦ T q (V (S s Ax))) (t - s) :=
      (T.continuousOn_orbit (V (S s Ax))).continuousAt
        (Ici_mem_nhds (sub_pos.mpr hst))
    change ContinuousAt (fun r ↦ T (t - r) (V (S s Ax))) s
    exact horbit.comp (continuousAt_const.sub continuousAt_id)
  have hproduct := hasDerivAt_clm_apply_of_strong
    Aop v hsource htarget hstrong hbound
  convert hproduct using 1
  · rfl
  · change -(T (t - s) (R (S s x))) =
      T (t - s) (V (S s Ax)) + -(T (t - s) NVs)
    rw [hdefect, (T (t - s)).map_add]
    abel

/-- Exact Duhamel identity derived from the generator graph relations along
the source orbit.  Continuity of the product path and integrability of the
Duhamel integrand are kept explicit so this theorem also applies to graph-norm
source carriers; exponential semigroup estimates discharge both in the usual
applications. -/
theorem semigroupDefect_eq_duhamel_of_generators
    (S : StronglyContinuousSemigroup K X)
    (T : StronglyContinuousSemigroup K H)
    (V : X →L[K] H) (R : X →L[K] H)
    {x Ax : X} (hAx : S.IsRightGeneratorVector x Ax)
    {t : ℝ} (ht : 0 ≤ t)
    (hTgen : ∀ s ∈ Ioo (0 : ℝ) t, ∃ NVs : H,
      T.IsRightGeneratorVector (V (S s x)) NVs ∧
        NVs = V (S s Ax) + R (S s x))
    (hbound : ∀ s ∈ Ioo (0 : ℝ) t, ∃ C : ℝ,
      ∀ᶠ r in 𝓝 s, ‖(T (t - r)).restrictScalars ℝ‖ ≤ C)
    (hpath : ContinuousOn (fun r ↦ T (t - r) (V (S r x)))
      (Icc (0 : ℝ) t))
    (hint : IntervalIntegrable
      (fun s ↦ T (t - s) (R (S s x))) volume 0 t) :
    T t (V x) - V (S t x) =
      ∫ s in 0..t, T (t - s) (R (S s x)) := by
  apply semigroupDefect_eq_duhamel_of_rightPathDerivative
    T S V R t x ht T.map_zero S.map_zero hpath
  · intro s hs
    rcases hTgen s hs with ⟨NVs, hNVs, hdefect⟩
    exact (hasDerivAt_duhamelProductPath S T V R hAx hs.1 hs.2
      hNVs hdefect (hbound s hs)).hasDerivWithinAt
  · exact hint

/-- Uniformly bounded form of the generator-derived Duhamel identity.  A
single finite-time bound on the target semigroup now discharges every local
strong-product-rule bound. -/
theorem semigroupDefect_eq_duhamel_of_generators_of_uniformBound
    (S : StronglyContinuousSemigroup K X)
    (T : StronglyContinuousSemigroup K H)
    (V : X →L[K] H) (R : X →L[K] H)
    {x Ax : X} (hAx : S.IsRightGeneratorVector x Ax)
    {t B : ℝ} (ht : 0 ≤ t)
    (hTbound : ∀ q ∈ Icc (0 : ℝ) t, ‖T q‖ ≤ B)
    (hTgen : ∀ s ∈ Ioo (0 : ℝ) t, ∃ NVs : H,
      T.IsRightGeneratorVector (V (S s x)) NVs ∧
        NVs = V (S s Ax) + R (S s x))
    (hpath : ContinuousOn (fun r ↦ T (t - r) (V (S r x)))
      (Icc (0 : ℝ) t))
    (hint : IntervalIntegrable
      (fun s ↦ T (t - s) (R (S s x))) volume 0 t) :
    T t (V x) - V (S t x) =
      ∫ s in 0..t, T (t - s) (R (S s x)) := by
  apply semigroupDefect_eq_duhamel_of_generators
    S T V R hAx ht hTgen
  · intro s hs
    exact ⟨B, eventually_norm_constSub_restrictScalars_le
      T hs.1 hs.2 hTbound⟩
  · exact hpath
  · exact hint

/-- Fully automatic finite-time Duhamel theorem for generator graph data.
Strong continuity and a uniform target-semigroup bound now discharge the
product-path continuity, integrability, and every local strong-product bound. -/
theorem semigroupDefect_eq_duhamel_of_generator_bounds
    (S : StronglyContinuousSemigroup K X)
    (T : StronglyContinuousSemigroup K H)
    (V : X →L[K] H) (R : X →L[K] H)
    {x Ax : X} (hAx : S.IsRightGeneratorVector x Ax)
    {t B : ℝ} (ht : 0 ≤ t)
    (hTbound : ∀ q ∈ Icc (0 : ℝ) t, ‖T q‖ ≤ B)
    (hTgen : ∀ s ∈ Ioo (0 : ℝ) t, ∃ NVs : H,
      T.IsRightGeneratorVector (V (S s x)) NVs ∧
        NVs = V (S s Ax) + R (S s x)) :
    T t (V x) - V (S t x) =
      ∫ s in 0..t, T (t - s) (R (S s x)) := by
  have hpath := continuousOn_constSub_apply_orbit
    S T V x hTbound
  have hintegrand := continuousOn_constSub_apply_orbit
    S T R x hTbound
  apply semigroupDefect_eq_duhamel_of_generators_of_uniformBound
    S T V R hAx ht hTbound hTgen hpath
  exact hintegrand.intervalIntegrable_of_Icc ht

/-- Zero-defect specialization: generator intertwining along a source
generator orbit implies semigroup intertwining on that vector.  Together with
`generatorIntertwining_of_semigroupIntertwining`, this supplies the two
directions of the C₀ generator/semigroup equivalence on generator graphs. -/
theorem semigroupIntertwining_of_generatorIntertwining
    (S : StronglyContinuousSemigroup K X)
    (T : StronglyContinuousSemigroup K H)
    (V : X →L[K] H) {x Ax : X}
    (hAx : S.IsRightGeneratorVector x Ax)
    {t B : ℝ} (ht : 0 ≤ t)
    (hTbound : ∀ q ∈ Icc (0 : ℝ) t, ‖T q‖ ≤ B)
    (hintertwineGenerator : ∀ s ∈ Ioo (0 : ℝ) t,
      T.IsRightGeneratorVector (V (S s x)) (V (S s Ax))) :
    T t (V x) = V (S t x) := by
  have hduhamel := semigroupDefect_eq_duhamel_of_generator_bounds
    S T V (0 : X →L[K] H) hAx ht hTbound (fun s hs ↦
      ⟨V (S s Ax), hintertwineGenerator s hs, by simp⟩)
  have hzero : T t (V x) - V (S t x) = 0 := by
    simpa using hduhamel
  exact sub_eq_zero.mp hzero

omit [NormedSpace ℝ X] [IsScalarTower ℝ K X]
  [NormedSpace ℝ H] [IsScalarTower ℝ K H]
  [CompleteSpace X] [CompleteSpace H] in
/-- Intertwining on a dense differentiable core extends to the whole graph
carrier because both sides are bounded linear maps there. -/
theorem semigroupIntertwining_of_denseCore
    (S : StronglyContinuousSemigroup K X)
    (T : StronglyContinuousSemigroup K H)
    (V : X →L[K] H) (t : ℝ) (core : Set X)
    (hcoreDense : Dense core)
    (hcore : ∀ x ∈ core, T t (V x) = V (S t x)) :
    (T t).comp V = V.comp (S t) := by
  have hfun : (fun x ↦ T t (V x)) = (fun x ↦ V (S t x)) :=
    Continuous.ext_on hcoreDense
      ((T t).continuous.comp V.continuous)
      (V.continuous.comp (S t).continuous) hcore
  ext x
  exact congrFun hfun x

end NCG
