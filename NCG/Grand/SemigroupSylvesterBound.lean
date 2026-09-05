/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exponentially represented Sylvester bounds

This file isolates the dimension-free analytic estimate behind the
Davis--Kahan step.  Once a Sylvester solution is represented by a semigroup
integral whose norm decays like `exp (-gap * t)`, its norm is at most the
forcing norm divided by the spectral gap.
-/

noncomputable section

open MeasureTheory Real Set

namespace NCG.SemigroupSylvester

/-- Composition of complex-linear maps, regarded as a real continuous
bilinear map.  The real form is what is needed when the semigroup time
parameter is real. -/
private noncomputable def composeReal
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] :
    (F →L[ℂ] G) →L[ℝ] (E →L[ℂ] F) →L[ℝ] (E →L[ℂ] G) :=
  (ContinuousLinearMap.compL ℂ E F G).bilinearRestrictScalars ℝ

@[simp]
private theorem composeReal_apply
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (f : F →L[ℂ] G) (g : E →L[ℂ] F) :
    composeReal f g = f.comp g := rfl

/-- Product rule for the two-sided operator evolution used in the Sylvester
integral. -/
theorem hasDerivAt_twoSidedSemigroup
    {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℂ U] [CompleteSpace U]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (S : U →L[ℂ] U) (T : V →L[ℂ] V) (X : V →L[ℂ] U)
    (t : ℝ) :
    HasDerivAt
      (fun r : ℝ => ((NormedSpace.exp (r • S)).comp X).comp
        (NormedSpace.exp ((-r) • T)))
      (((NormedSpace.exp (t • S) * S).comp X).comp
          (NormedSpace.exp ((-t) • T)) +
        ((NormedSpace.exp (t • S)).comp X).comp
          (-(NormedSpace.exp ((-t) • T) * T))) t := by
  have hleft : HasDerivAt (fun r : ℝ => NormedSpace.exp (r • S))
      (NormedSpace.exp (t • S) * S) t :=
    NormedSpace.hasDerivAt_exp_smul_const S t
  have hright : HasDerivAt (fun r : ℝ => NormedSpace.exp ((-r) • T))
      (-(NormedSpace.exp ((-t) • T) * T)) t := by
    simpa using
      (NormedSpace.hasDerivAt_exp_smul_const T (-t)).comp t
        (hasDerivAt_neg t)
  have hfirst : HasDerivAt
      (fun r : ℝ => (NormedSpace.exp (r • S)).comp X)
      ((NormedSpace.exp (t • S) * S).comp X) t := by
    have hc : HasDerivAt
        (fun r : ℝ => composeReal (NormedSpace.exp (r • S)))
        (composeReal (NormedSpace.exp (t • S) * S)) t :=
      (composeReal (E := V) (F := U) (G := U)).hasFDerivAt.comp_hasDerivAt t hleft
    simpa using hc.clm_apply (hasDerivAt_const t X)
  have hc : HasDerivAt
      (fun r : ℝ => composeReal ((NormedSpace.exp (r • S)).comp X))
      (composeReal ((NormedSpace.exp (t • S) * S).comp X)) t :=
    (composeReal (E := V) (F := V) (G := U)).hasFDerivAt.comp_hasDerivAt t hfirst
  simpa using hc.clm_apply hright

/-- If `X * T - S * X = C`, the two-sided evolution has derivative
`-exp(tS) * C * exp(-tT)`.  This is the algebraic heart of the Sylvester
semigroup representation. -/
theorem hasDerivAt_twoSidedSemigroup_of_sylvester
    {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℂ U] [CompleteSpace U]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (S : U →L[ℂ] U) (T : V →L[ℂ] V)
    (X C : V →L[ℂ] U)
    (hSylvester : X.comp T - S.comp X = C)
    (t : ℝ) :
    HasDerivAt
      (fun r : ℝ => ((NormedSpace.exp (r • S)).comp X).comp
        (NormedSpace.exp ((-r) • T)))
      (-(((NormedSpace.exp (t • S)).comp C).comp
        (NormedSpace.exp ((-t) • T)))) t := by
  have hcommS :
      NormedSpace.exp (t • S) * S = S * NormedSpace.exp (t • S) :=
    ((Commute.refl S).smul_left t).exp_left.eq
  have hcommT :
      NormedSpace.exp ((-t) • T) * T =
        T * NormedSpace.exp ((-t) • T) :=
    ((Commute.refl T).smul_left (-t)).exp_left.eq
  convert hasDerivAt_twoSidedSemigroup S T X t using 1
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.mul_apply]
  rw [hcommS, hcommT]
  simp only [ContinuousLinearMap.mul_apply, map_neg, neg_add_rev]
  have hv := congrArg (fun L : V →L[ℂ] U =>
    L (NormedSpace.exp ((-t) • T) v)) hSylvester
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply] at hv
  rw [← hv]
  simp only [map_sub]
  abel

/-- Fundamental-theorem-of-calculus form used to obtain a semigroup
representation.  If an evolution starts at `x`, tends to zero, and has
derivative `-kernel`, then `x` is the integral of `kernel` on the positive
half-line. -/
theorem eq_integral_Ioi_of_hasDerivAt_eq_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (x : E) (evolution kernel : ℝ → E)
    (hzero : evolution 0 = x)
    (hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt evolution (-kernel t) t)
    (hintegrable : IntegrableOn kernel (Ioi (0 : ℝ)))
    (htendsto : Filter.Tendsto evolution Filter.atTop (nhds 0)) :
    x = ∫ t in Ioi (0 : ℝ), kernel t := by
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto'
    hderiv hintegrable.neg htendsto
  rw [integral_neg, hzero, zero_sub] at hFTC
  exact neg_injective (by simpa using hFTC.symm)

/-- A Banach-valued exponentially decaying integral has the exact reciprocal
gap bound.  This is the norm-estimate half of the semigroup proof of the
separated Sylvester theorem. -/
theorem norm_le_div_of_eq_integral_exp_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (x : E) (f : ℝ → E) (gap forcingNorm : ℝ)
    (hgap : 0 < gap)
    (hrep : x = ∫ t in Ioi 0, f t)
    (hdecay : ∀ t ∈ Ioi (0 : ℝ),
      ‖f t‖ ≤ Real.exp (-gap * t) * forcingNorm) :
    ‖x‖ ≤ forcingNorm / gap := by
  have hg : IntegrableOn
      (fun t : ℝ => Real.exp (-gap * t) * forcingNorm) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -gap) (by linarith) 0).mul_const forcingNorm
  have hnorm :
      ‖∫ t in Ioi (0 : ℝ), f t‖ ≤
        ∫ t in Ioi (0 : ℝ), Real.exp (-gap * t) * forcingNorm := by
    exact norm_integral_le_of_norm_le hg
      (ae_restrict_iff' measurableSet_Ioi |>.mpr
        (Filter.Eventually.of_forall fun t => hdecay t))
  rw [hrep]
  calc
    ‖∫ t in Ioi (0 : ℝ), f t‖
        ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-gap * t) * forcingNorm := hnorm
    _ = (∫ t in Ioi (0 : ℝ), Real.exp (-gap * t)) * forcingNorm := by
      rw [integral_mul_const]
    _ = forcingNorm / gap := by
      rw [integral_exp_mul_Ioi (a := -gap) (by linarith) 0]
      simp
      field_simp

/-- Operator-valued form of the semigroup estimate.  The left evolution grows
at rate at most `upper`, the right inverse evolution decays at rate at least
`lower`, and the strict separation `upper < lower` supplies the Sylvester
denominator. -/
theorem norm_le_div_of_eq_semigroup_integral
    {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℂ U] [CompleteSpace U]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (S : U →L[ℂ] U) (T : V →L[ℂ] V)
    (X C : V →L[ℂ] U) (upper lower : ℝ)
    (hsep : upper < lower)
    (hleft : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • S)‖ ≤ Real.exp (upper * t))
    (hright : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp ((-t) • T)‖ ≤ Real.exp (-lower * t))
    (hrep : X = ∫ t in Ioi (0 : ℝ),
      ((NormedSpace.exp (t • S)).comp C).comp
        (NormedSpace.exp ((-t) • T))) :
    ‖X‖ ≤ ‖C‖ / (lower - upper) := by
  apply norm_le_div_of_eq_integral_exp_decay
    X
    (fun t : ℝ => ((NormedSpace.exp (t • S)).comp C).comp
      (NormedSpace.exp ((-t) • T)))
    (lower - upper) ‖C‖ (sub_pos.mpr hsep) hrep
  intro t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  calc
    ‖((NormedSpace.exp (t • S)).comp C).comp
        (NormedSpace.exp ((-t) • T))‖
        ≤ (‖NormedSpace.exp (t • S)‖ * ‖C‖) *
            ‖NormedSpace.exp ((-t) • T)‖ := by
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_right
              (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (Real.exp (upper * t) * ‖C‖) * Real.exp (-lower * t) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right (hleft t ht0) (norm_nonneg C)
          · exact hright t ht0
          · exact norm_nonneg _
          · exact mul_nonneg (Real.exp_pos _).le (norm_nonneg C)
    _ = Real.exp (-(lower - upper) * t) * ‖C‖ := by
          rw [mul_assoc, mul_comm ‖C‖, ← mul_assoc, ← Real.exp_add]
          congr 2
          ring

/-- The separated semigroup kernel is Bochner-integrable on the positive
half-line. -/
theorem twoSidedSemigroup_integrableOn
    {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℂ U] [CompleteSpace U]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (S : U →L[ℂ] U) (T : V →L[ℂ] V) (C : V →L[ℂ] U)
    (upper lower : ℝ) (hsep : upper < lower)
    (hleft : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • S)‖ ≤ Real.exp (upper * t))
    (hright : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp ((-t) • T)‖ ≤ Real.exp (-lower * t)) :
    IntegrableOn
      (fun t : ℝ => ((NormedSpace.exp (t • S)).comp C).comp
        (NormedSpace.exp ((-t) • T))) (Ioi 0) := by
  have hg : IntegrableOn
      (fun t : ℝ => Real.exp (-(lower - upper) * t) * ‖C‖) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -(lower - upper)) (by linarith) 0).mul_const ‖C‖
  have hcont : Continuous
      (fun t : ℝ => ((NormedSpace.exp (t • S)).comp C).comp
        (NormedSpace.exp ((-t) • T))) := by
    fun_prop
  apply hg.mono' hcont.aestronglyMeasurable.restrict
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  exact Filter.Eventually.of_forall fun t ht => by
    have ht0 : 0 ≤ t := le_of_lt ht
    calc
      ‖((NormedSpace.exp (t • S)).comp C).comp
          (NormedSpace.exp ((-t) • T))‖
          ≤ (‖NormedSpace.exp (t • S)‖ * ‖C‖) *
              ‖NormedSpace.exp ((-t) • T)‖ := by
            exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul_of_nonneg_right
                (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ (Real.exp (upper * t) * ‖C‖) * Real.exp (-lower * t) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_right (hleft t ht0) (norm_nonneg C)
            · exact hright t ht0
            · exact norm_nonneg _
            · exact mul_nonneg (Real.exp_pos _).le (norm_nonneg C)
      _ = Real.exp (-(lower - upper) * t) * ‖C‖ := by
            rw [mul_assoc, mul_comm ‖C‖, ← mul_assoc, ← Real.exp_add]
            congr 2
            ring

/-- The homogeneous two-sided evolution tends to zero when its two
semigroups are spectrally separated. -/
theorem twoSidedSemigroup_tendsto_zero
    {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℂ U] [CompleteSpace U]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (S : U →L[ℂ] U) (T : V →L[ℂ] V) (X : V →L[ℂ] U)
    (upper lower : ℝ) (hsep : upper < lower)
    (hleft : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • S)‖ ≤ Real.exp (upper * t))
    (hright : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp ((-t) • T)‖ ≤ Real.exp (-lower * t)) :
    Filter.Tendsto
      (fun t : ℝ => ((NormedSpace.exp (t • S)).comp X).comp
        (NormedSpace.exp ((-t) • T))) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have harg : Filter.Tendsto (fun t : ℝ => -(lower - upper) * t)
      Filter.atTop Filter.atBot :=
    Filter.tendsto_id.const_mul_atTop_of_neg (by linarith)
  have hmajorant : Filter.Tendsto
      (fun t : ℝ => Real.exp (-(lower - upper) * t) * ‖X‖)
      Filter.atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_atBot.comp harg).mul_const ‖X‖
  refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _)
    ?_ hmajorant
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht0
  calc
    ‖((NormedSpace.exp (t • S)).comp X).comp
        (NormedSpace.exp ((-t) • T))‖
        ≤ (‖NormedSpace.exp (t • S)‖ * ‖X‖) *
            ‖NormedSpace.exp ((-t) • T)‖ := by
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_right
              (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (Real.exp (upper * t) * ‖X‖) * Real.exp (-lower * t) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right (hleft t ht0) (norm_nonneg X)
          · exact hright t ht0
          · exact norm_nonneg _
          · exact mul_nonneg (Real.exp_pos _).le (norm_nonneg X)
    _ = Real.exp (-(lower - upper) * t) * ‖X‖ := by
          rw [mul_assoc, mul_comm ‖X‖, ← mul_assoc, ← Real.exp_add]
          congr 2
          ring

/-- A separated Sylvester equation has the standard semigroup integral
representation. -/
theorem eq_twoSidedSemigroup_integral_of_sylvester
    {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℂ U] [CompleteSpace U]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (S : U →L[ℂ] U) (T : V →L[ℂ] V)
    (X C : V →L[ℂ] U) (upper lower : ℝ)
    (hsep : upper < lower)
    (hSylvester : X.comp T - S.comp X = C)
    (hleft : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • S)‖ ≤ Real.exp (upper * t))
    (hright : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp ((-t) • T)‖ ≤ Real.exp (-lower * t)) :
    X = ∫ t in Ioi (0 : ℝ),
      ((NormedSpace.exp (t • S)).comp C).comp
        (NormedSpace.exp ((-t) • T)) := by
  apply eq_integral_Ioi_of_hasDerivAt_eq_neg X
    (fun t : ℝ => ((NormedSpace.exp (t • S)).comp X).comp
      (NormedSpace.exp ((-t) • T)))
    (fun t : ℝ => ((NormedSpace.exp (t • S)).comp C).comp
      (NormedSpace.exp ((-t) • T)))
  · simp
  · intro t _
    exact hasDerivAt_twoSidedSemigroup_of_sylvester S T X C hSylvester t
  · exact twoSidedSemigroup_integrableOn S T C upper lower hsep hleft hright
  · exact twoSidedSemigroup_tendsto_zero S T X upper lower hsep hleft hright

/-- Dimension-free norm estimate for a separated Sylvester equation. -/
theorem norm_le_div_of_sylvester
    {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℂ U] [CompleteSpace U]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (S : U →L[ℂ] U) (T : V →L[ℂ] V)
    (X C : V →L[ℂ] U) (upper lower : ℝ)
    (hsep : upper < lower)
    (hSylvester : X.comp T - S.comp X = C)
    (hleft : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • S)‖ ≤ Real.exp (upper * t))
    (hright : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp ((-t) • T)‖ ≤ Real.exp (-lower * t)) :
    ‖X‖ ≤ ‖C‖ / (lower - upper) :=
  norm_le_div_of_eq_semigroup_integral S T X C upper lower hsep hleft hright
    (eq_twoSidedSemigroup_integral_of_sylvester
      S T X C upper lower hsep hSylvester hleft hright)

/-- Direct exponentially-decaying form of the Sylvester estimate.  It is
useful when only the source and target spectral supports, rather than the
full semigroups, satisfy the required bounds. -/
theorem norm_le_div_of_sylvester_of_exp_decay
    {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℂ U] [CompleteSpace U]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (S : U →L[ℂ] U) (T : V →L[ℂ] V)
    (X C : V →L[ℂ] U) (gap : ℝ) (hgap : 0 < gap)
    (hSylvester : X.comp T - S.comp X = C)
    (hkernel : ∀ t : ℝ, 0 ≤ t →
      ‖((NormedSpace.exp (t • S)).comp C).comp
          (NormedSpace.exp ((-t) • T))‖
        ≤ Real.exp (-gap * t) * ‖C‖)
    (hevolution : ∀ t : ℝ, 0 ≤ t →
      ‖((NormedSpace.exp (t • S)).comp X).comp
          (NormedSpace.exp ((-t) • T))‖
        ≤ Real.exp (-gap * t) * ‖X‖) :
    ‖X‖ ≤ ‖C‖ / gap := by
  let kernel : ℝ → (V →L[ℂ] U) := fun t =>
    ((NormedSpace.exp (t • S)).comp C).comp
      (NormedSpace.exp ((-t) • T))
  let evolution : ℝ → (V →L[ℂ] U) := fun t =>
    ((NormedSpace.exp (t • S)).comp X).comp
      (NormedSpace.exp ((-t) • T))
  have hkernelInt : IntegrableOn kernel (Ioi 0) := by
    have hg : IntegrableOn
        (fun t : ℝ => Real.exp (-gap * t) * ‖C‖) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (a := -gap) (by linarith) 0).mul_const ‖C‖
    have hcont : Continuous kernel := by
      dsimp only [kernel]
      fun_prop
    apply hg.mono' hcont.aestronglyMeasurable.restrict
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact Filter.Eventually.of_forall fun t ht => hkernel t (le_of_lt ht)
  have hevolutionZero : Filter.Tendsto evolution Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have harg : Filter.Tendsto (fun t : ℝ => -gap * t)
        Filter.atTop Filter.atBot :=
      Filter.tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hgap)
    have hmajorant : Filter.Tendsto
        (fun t : ℝ => Real.exp (-gap * t) * ‖X‖)
        Filter.atTop (nhds 0) := by
      simpa using (Real.tendsto_exp_atBot.comp harg).mul_const ‖X‖
    refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _)
      ?_ hmajorant
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact hevolution t ht
  have hrep : X = ∫ t in Ioi (0 : ℝ), kernel t := by
    apply eq_integral_Ioi_of_hasDerivAt_eq_neg X evolution kernel
    · simp [evolution]
    · intro t _
      exact hasDerivAt_twoSidedSemigroup_of_sylvester
        S T X C hSylvester t
    · exact hkernelInt
    · exact hevolutionZero
  exact norm_le_div_of_eq_integral_exp_decay
    X kernel gap ‖C‖ hgap hrep
      (fun t ht => hkernel t (le_of_lt ht))

/-- Support-aware separated Sylvester estimate.  Only the supported pieces of
the two semigroups need exponential bounds. -/
theorem norm_le_div_of_supported_sylvester
    {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℂ U] [CompleteSpace U]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (S : U →L[ℂ] U) (T : V →L[ℂ] V)
    (P : U →L[ℂ] U) (R : V →L[ℂ] V)
    (X C : V →L[ℂ] U) (upper lower : ℝ)
    (hsep : upper < lower)
    (hSylvester : X.comp T - S.comp X = C)
    (hPX : P.comp X = X) (hXR : X.comp R = X)
    (hPC : P.comp C = C) (hCR : C.comp R = C)
    (hleft : ∀ t : ℝ, 0 ≤ t →
      ‖(NormedSpace.exp (t • S)).comp P‖ ≤ Real.exp (upper * t))
    (hright : ∀ t : ℝ, 0 ≤ t →
      ‖R.comp (NormedSpace.exp ((-t) • T))‖ ≤ Real.exp (-lower * t)) :
    ‖X‖ ≤ ‖C‖ / (lower - upper) := by
  apply norm_le_div_of_sylvester_of_exp_decay
    S T X C (lower - upper) (sub_pos.mpr hsep) hSylvester
  · intro t ht
    have hfactor :
        ((NormedSpace.exp (t • S)).comp C).comp
            (NormedSpace.exp ((-t) • T)) =
          ((((NormedSpace.exp (t • S)).comp P).comp C).comp R).comp
            (NormedSpace.exp ((-t) • T)) := by
      ext v
      simp only [ContinuousLinearMap.comp_apply]
      rw [show P (C (R (NormedSpace.exp ((-t) • T) v))) =
          C (NormedSpace.exp ((-t) • T) v) by
        rw [show C (R (NormedSpace.exp ((-t) • T) v)) =
          C (NormedSpace.exp ((-t) • T) v) by
            exact congrArg (fun L : V →L[ℂ] U =>
              L (NormedSpace.exp ((-t) • T) v)) hCR,
          show P (C (NormedSpace.exp ((-t) • T) v)) =
            C (NormedSpace.exp ((-t) • T) v) by
              exact congrArg (fun L : V →L[ℂ] U =>
                L (NormedSpace.exp ((-t) • T) v)) hPC]
    rw [hfactor]
    calc
      ‖((((NormedSpace.exp (t • S)).comp P).comp C).comp R).comp
          (NormedSpace.exp ((-t) • T))‖
          ≤ (‖(NormedSpace.exp (t • S)).comp P‖ * ‖C‖) *
              ‖R.comp (NormedSpace.exp ((-t) • T))‖ := by
            exact (ContinuousLinearMap.opNorm_comp_le
              (((NormedSpace.exp (t • S)).comp P).comp C)
              (R.comp (NormedSpace.exp ((-t) • T)))).trans
              (mul_le_mul_of_nonneg_right
                (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ (Real.exp (upper * t) * ‖C‖) * Real.exp (-lower * t) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_right (hleft t ht) (norm_nonneg C)
            · exact hright t ht
            · exact norm_nonneg _
            · exact mul_nonneg (Real.exp_pos _).le (norm_nonneg C)
      _ = Real.exp (-(lower - upper) * t) * ‖C‖ := by
            rw [mul_assoc, mul_comm ‖C‖, ← mul_assoc, ← Real.exp_add]
            congr 2
            ring
  · intro t ht
    have hfactor :
        ((NormedSpace.exp (t • S)).comp X).comp
            (NormedSpace.exp ((-t) • T)) =
          ((((NormedSpace.exp (t • S)).comp P).comp X).comp R).comp
            (NormedSpace.exp ((-t) • T)) := by
      ext v
      simp only [ContinuousLinearMap.comp_apply]
      rw [show P (X (R (NormedSpace.exp ((-t) • T) v))) =
          X (NormedSpace.exp ((-t) • T) v) by
        rw [show X (R (NormedSpace.exp ((-t) • T) v)) =
          X (NormedSpace.exp ((-t) • T) v) by
            exact congrArg (fun L : V →L[ℂ] U =>
              L (NormedSpace.exp ((-t) • T) v)) hXR,
          show P (X (NormedSpace.exp ((-t) • T) v)) =
            X (NormedSpace.exp ((-t) • T) v) by
              exact congrArg (fun L : V →L[ℂ] U =>
                L (NormedSpace.exp ((-t) • T) v)) hPX]
    rw [hfactor]
    calc
      ‖((((NormedSpace.exp (t • S)).comp P).comp X).comp R).comp
          (NormedSpace.exp ((-t) • T))‖
          ≤ (‖(NormedSpace.exp (t • S)).comp P‖ * ‖X‖) *
              ‖R.comp (NormedSpace.exp ((-t) • T))‖ := by
            exact (ContinuousLinearMap.opNorm_comp_le
              (((NormedSpace.exp (t • S)).comp P).comp X)
              (R.comp (NormedSpace.exp ((-t) • T)))).trans
              (mul_le_mul_of_nonneg_right
                (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ (Real.exp (upper * t) * ‖X‖) * Real.exp (-lower * t) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_right (hleft t ht) (norm_nonneg X)
            · exact hright t ht
            · exact norm_nonneg _
            · exact mul_nonneg (Real.exp_pos _).le (norm_nonneg X)
      _ = Real.exp (-(lower - upper) * t) * ‖X‖ := by
            rw [mul_assoc, mul_comm ‖X‖, ← mul_assoc, ← Real.exp_add]
            congr 2
            ring

end NCG.SemigroupSylvester
