/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AffineBkmTwoDirectionUniformLimitExact
import NCG.Grand.PetzRecoveryExact

/-!
# Mixed affine matrix-log derivatives

Polarization of the locally uniform diagonal BKM cutoffs supplies the mixed
resolvent derivative for an arbitrary Hermitian log pairing and an
independent Hermitian affine path direction.
-/

open Matrix Filter Topology MeasureTheory intervalIntegral
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ d w : Matrix n n ℂ}

/-- The mixed BKM form obtained by real polarization. -/
noncomputable def mixedBkmForm (hσ : σ.IsHermitian)
    (w d : Matrix n n ℂ) : ℝ :=
  (bkmForm hσ (w + d) - bkmForm hσ (w - d)) / 4

/-- The mixed resolvent form before integration. -/
noncomputable def mixedSForm (hσ : σ.IsHermitian)
    (w d : Matrix n n ℂ) (s : ℝ) : ℝ :=
  (Matrix.trace (w * (resolvent hσ s * (d * resolvent hσ s)))).re

/-- Cyclicity of trace identifies the two cross terms in the polarization
of the resolvent quadratic form. -/
theorem mixedSForm_eq_polarization (hσ : σ.IsHermitian)
    (w d : Matrix n n ℂ) (s : ℝ) :
    mixedSForm hσ w d s =
      (sForm hσ (w + d) s - sForm hσ (w - d) s) / 4 := by
  unfold mixedSForm sForm
  let R := resolvent hσ s
  have hcycle :
      (Matrix.trace (d * (R * (w * R)))).re =
        (Matrix.trace (w * (R * (d * R)))).re := by
    have htr := Matrix.trace_mul_cycle d R (w * R)
    simpa only [Matrix.mul_assoc] using congrArg Complex.re htr
  change (Matrix.trace (w * (R * (d * R)))).re = _
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re]
  simp only [Matrix.mul_assoc]
  rw [hcycle]
  ring

/-- Normalized resolvent integrand for pairing a fixed Hermitian matrix `w`
with the logarithm along the independently directed affine path `σ + u d`. -/
noncomputable def affineMixedLogIntegrand
    (w σ d : Matrix n n ℂ) (u s : ℝ) : ℝ :=
  w.trace.re * (1 + s)⁻¹ -
    (Matrix.trace (w * Ring.inverse
      (σ + u • d + s • (1 : Matrix n n ℂ)))).re

/-- Proof-independent mixed resolvent derivative integrand. -/
noncomputable def affineMixedRawSForm
    (w σ d : Matrix n n ℂ) (p : ℝ × ℝ) : ℝ :=
  (Matrix.trace (w * (Ring.inverse
    (σ + p.1 • d + p.2 • (1 : Matrix n n ℂ)) * (d * Ring.inverse
      (σ + p.1 • d + p.2 • (1 : Matrix n n ℂ)))))).re

/-- The proof-independent mixed derivative is the spectral mixed resolvent
form at faithful affine points. -/
theorem affineMixedRawSForm_eq_mixedSForm (hσ : σ.IsHermitian)
    (hd : d.IsHermitian) {u s : ℝ} (hu : (σ + u • d).PosDef)
    (hs : 0 ≤ s) :
    affineMixedRawSForm w σ d (u, s) =
      mixedSForm (affineMatrix_isHermitian hσ hd u) w d s := by
  unfold affineMixedRawSForm mixedSForm
  have heq : affineMatrix_isHermitian hσ hd u = hu.1 := Subsingleton.elim _ _
  rw [heq, ringInverse_shift_eq_resolvent_nonneg hu hs]

/-- Joint continuity of the raw mixed resolvent derivative on compact
faithful rectangles. -/
theorem affineMixedRawSForm_continuousOn_rect {a b R : ℝ}
    (hpos : ∀ u ∈ Set.Icc a b, (σ + u • d).PosDef) :
    ContinuousOn (affineMixedRawSForm w σ d)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) R) := by
  intro p hp
  have hpath : ContinuousAt
      (fun q : ℝ × ℝ =>
        σ + q.1 • d + q.2 • (1 : Matrix n n ℂ)) p := by
    fun_prop
  have hunit : IsUnit
      (σ + p.1 • d + p.2 • (1 : Matrix n n ℂ)) :=
    isUnit_shift_of_posDef_nonneg (hpos p.1 hp.1) hp.2.1
  have hinvAt : ContinuousAt Ring.inverse
      (σ + p.1 • d + p.2 • (1 : Matrix n n ℂ)) := by
    simpa [hunit.unit_spec] using
      (NormedRing.inverse_continuousAt hunit.unit)
  let r : ℝ × ℝ → Matrix n n ℂ := fun q => Ring.inverse
    (σ + q.1 • d + q.2 • (1 : Matrix n n ℂ))
  have hinv : ContinuousAt r p :=
    ContinuousAt.comp'
      (f := fun q : ℝ × ℝ =>
        σ + q.1 • d + q.2 • (1 : Matrix n n ℂ)) hinvAt hpath
  have hinner : ContinuousAt
      (fun q : ℝ × ℝ => r q * (d * r q)) p :=
    hinv.mul (continuousAt_const.mul hinv)
  have htrace : ContinuousAt
      (fun q : ℝ × ℝ => realTraceLeft w (r q * (d * r q))) p :=
    ((realTraceLeft w).continuous.continuousAt).comp' hinner
  change ContinuousWithinAt
    (fun q : ℝ × ℝ =>
      (Matrix.trace (w * (Ring.inverse
        (σ + q.1 • d + q.2 • (1 : Matrix n n ℂ)) * (d * Ring.inverse
          (σ + q.1 • d + q.2 • (1 : Matrix n n ℂ)))))).re)
    (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) R) p
  simpa only [r, realTraceLeft_apply] using htrace.continuousWithinAt

/-- Compact faithful rectangles uniformly bound the mixed resolvent
derivative integrand. -/
theorem exists_affineMixedSForm_bound_rect (hσ : σ.IsHermitian)
    (hd : d.IsHermitian) {a b R : ℝ}
    (hpos : ∀ u ∈ Set.Icc a b, (σ + u • d).PosDef) :
    ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) R, ∀ u ∈ Set.Icc a b,
      |mixedSForm (affineMatrix_isHermitian hσ hd u) w d s| ≤ C := by
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) R) :=
    isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p => |affineMixedRawSForm w σ d p|)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) R) :=
    (affineMixedRawSForm_continuousOn_rect hpos).abs
  obtain ⟨C, hC⟩ := hK.bddAbove_image hcont
  refine ⟨C, ?_⟩
  intro s hs u hu
  have hle := hC ⟨(u, s), ⟨hu, hs⟩, rfl⟩
  change |affineMixedRawSForm w σ d (u, s)| ≤ C at hle
  rw [affineMixedRawSForm_eq_mixedSForm hσ hd (hpos u hu) hs.1] at hle
  exact hle

/-- The pointwise affine derivative of the mixed normalized log-resolvent
integrand. -/
theorem affineMixedLogIntegrand_hasDerivAt {u s : ℝ}
    (hu : (σ + u • d).PosDef) (hs : 0 < s) :
    HasDerivAt (fun x : ℝ => affineMixedLogIntegrand w σ d x s)
      (mixedSForm hu.1 w d s) u := by
  have hres := resolvent_affine_hasDerivAt_at hu hs
  have hpair : HasDerivAt
      (fun x : ℝ => (Matrix.trace (w * Ring.inverse
        (σ + x • d + s • (1 : Matrix n n ℂ)))).re)
      (-mixedSForm hu.1 w d s) u := by
    have hcomp : HasDerivAt
        (fun x : ℝ => realTraceLeft w (Ring.inverse
          (σ + x • d + s • (1 : Matrix n n ℂ))))
        (realTraceLeft w
          (-(resolvent hu.1 s * d * resolvent hu.1 s))) u :=
      (realTraceLeft w).hasFDerivAt.comp_hasDerivAt u hres
    have hval : realTraceLeft w
        (-(resolvent hu.1 s * d * resolvent hu.1 s)) =
        -mixedSForm hu.1 w d s := by
      unfold mixedSForm
      simp only [realTraceLeft_apply, map_neg, Matrix.mul_assoc]
    simpa only [realTraceLeft_apply] using hcomp.congr_deriv hval
  have hconst : HasDerivAt (fun _ : ℝ => w.trace.re * (1 + s)⁻¹) 0 u :=
    hasDerivAt_const u _
  unfold affineMixedLogIntegrand
  exact (hconst.sub hpair).congr_deriv (by ring)

/-- The finite-cutoff mixed matrix-log pairing. -/
noncomputable def truncatedAffineMixedMatrixLogPairing
    (_hw : w.IsHermitian) (hσ : σ.IsHermitian) (hd : d.IsHermitian)
    (R u : ℝ) : ℝ :=
  truncatedMatrixLogPairing w (affineMatrix_isHermitian hσ hd u) R

/-- At faithful affine points the mixed spectral cutoff is its concrete
normalized resolvent integral. -/
theorem truncatedAffineMixedMatrixLogPairing_eq_integral
    (hw : w.IsHermitian) (hσ : σ.IsHermitian) (hd : d.IsHermitian)
    {R u : ℝ} (hR : 0 ≤ R) (hu : (σ + u • d).PosDef) :
    truncatedAffineMixedMatrixLogPairing hw hσ hd R u =
      ∫ s in (0 : ℝ)..R, affineMixedLogIntegrand w σ d u s := by
  unfold truncatedAffineMixedMatrixLogPairing affineMixedLogIntegrand
  have heq : affineMatrix_isHermitian hσ hd u = hu.1 := Subsingleton.elim _ _
  rw [heq, truncatedMatrixLogPairing_eq_integral hw hu hR]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hR] at hs
  change w.trace.re * (1 + s)⁻¹ -
      (Matrix.trace (w * resolvent hu.1 s)).re =
    w.trace.re * (1 + s)⁻¹ -
      (Matrix.trace (w * Ring.inverse
        ((σ + u • d) + s • (1 : Matrix n n ℂ)))).re
  rw [ringInverse_shift_eq_resolvent_nonneg hu hs.1]

/-- Continuity of the mixed normalized log-resolvent integrand in the
nonnegative resolvent parameter. -/
theorem affineMixedLogIntegrand_continuousAt_s {u s : ℝ}
    (hu : (σ + u • d).PosDef) (hs : 0 ≤ s) :
    ContinuousAt (fun r : ℝ => affineMixedLogIntegrand w σ d u r) s := by
  have hpath : ContinuousAt
      (fun r : ℝ => (σ + u • d) + r • (1 : Matrix n n ℂ)) s := by
    have hlin : HasDerivAt (fun r : ℝ => r • (1 : Matrix n n ℂ))
        (1 : Matrix n n ℂ) s := by
      simpa using (hasDerivAt_id s).smul_const (1 : Matrix n n ℂ)
    exact (hlin.const_add (σ + u • d)).continuousAt
  have hunit : IsUnit ((σ + u • d) + s • (1 : Matrix n n ℂ)) :=
    isUnit_shift_of_posDef_nonneg hu hs
  have hinvAt : ContinuousAt Ring.inverse
      ((σ + u • d) + s • (1 : Matrix n n ℂ)) := by
    simpa [hunit.unit_spec] using
      (NormedRing.inverse_continuousAt hunit.unit)
  have hinv : ContinuousAt
      (fun r : ℝ => Ring.inverse
        ((σ + u • d) + r • (1 : Matrix n n ℂ))) s :=
    ContinuousAt.comp'
      (f := fun r : ℝ => (σ + u • d) + r • (1 : Matrix n n ℂ))
      hinvAt hpath
  have htrace : ContinuousAt
      (fun r : ℝ => realTraceLeft w (Ring.inverse
        ((σ + u • d) + r • (1 : Matrix n n ℂ)))) s :=
    ((realTraceLeft w).continuous.continuousAt).comp' hinv
  have hscalar : ContinuousAt (fun r : ℝ => w.trace.re * (1 + r)⁻¹) s := by
    have hone : 1 + s ≠ 0 := ne_of_gt (by linarith)
    exact continuousAt_const.mul
      ((continuousAt_const.add continuousAt_id).inv₀ hone)
  unfold affineMixedLogIntegrand
  change ContinuousAt
    ((fun r : ℝ => w.trace.re * (1 + r)⁻¹) -
      fun r : ℝ => (Matrix.trace (w * Ring.inverse
        ((σ + u • d) + r • (1 : Matrix n n ℂ)))).re) s
  simpa only [realTraceLeft_apply] using hscalar.sub htrace

/-- Finite-cutoff interval integrability of the mixed normalized
log-resolvent integrand. -/
theorem affineMixedLogIntegrand_intervalIntegrable {u R : ℝ}
    (hu : (σ + u • d).PosDef) (hR : 0 ≤ R) :
    IntervalIntegrable (fun s : ℝ => affineMixedLogIntegrand w σ d u s)
      volume 0 R := by
  apply ContinuousOn.intervalIntegrable
  intro s hs
  rw [Set.uIcc_of_le hR] at hs
  exact (affineMixedLogIntegrand_continuousAt_s hu hs.1).continuousWithinAt

set_option maxHeartbeats 1600000 in
-- The dominated parameter-integral derivative carries two independent
-- matrix directions and needs the enlarged finite-dimensional elaboration
-- budget used by the diagonal theorem.
/-- Differentiation of a finite mixed matrix-log cutoff under a local uniform
mixed-curvature bound. -/
theorem truncatedAffineMixedMatrixLogPairing_hasDerivAt_of_bound
    (hw : w.IsHermitian) (hσ : σ.IsHermitian) (hd : d.IsHermitian)
    {U : Set ℝ} {u R C : ℝ} (hU : U ∈ 𝓝 u)
    (hpos : ∀ x ∈ U, (σ + x • d).PosDef) (hR : 0 ≤ R)
    (hbound : ∀ s ∈ Set.Ioc (0 : ℝ) R, ∀ x ∈ U,
      |mixedSForm (affineMatrix_isHermitian hσ hd x) w d s| ≤ C) :
    HasDerivAt
      (fun x : ℝ => truncatedAffineMixedMatrixLogPairing hw hσ hd R x)
      (∫ s in (0 : ℝ)..R,
        mixedSForm (affineMatrix_isHermitian hσ hd u) w d s) u := by
  have huU : u ∈ U := mem_of_mem_nhds hU
  have hu : (σ + u • d).PosDef := hpos u huU
  have hFmeas : ∀ᶠ x in 𝓝 u,
      AEStronglyMeasurable (affineMixedLogIntegrand w σ d x)
        (volume.restrict (Set.Ioc (0 : ℝ) R)) := by
    filter_upwards [hU] with x hx
    exact ((affineMixedLogIntegrand_intervalIntegrable
      (hpos x hx) hR).1).aestronglyMeasurable
  have hFint : Integrable (affineMixedLogIntegrand w σ d u)
      (volume.restrict (Set.Ioc (0 : ℝ) R)) :=
    (affineMixedLogIntegrand_intervalIntegrable hu hR).1
  have hF'meas : AEStronglyMeasurable
      (fun s => mixedSForm (affineMatrix_isHermitian hσ hd u) w d s)
      (volume.restrict (Set.Ioc (0 : ℝ) R)) := by
    have hraw := affineMixedRawSForm_continuousOn_rect
      (w := w) (σ := σ) (d := d) (a := u) (b := u) (R := R)
      (fun x hx => by
        have hxu : x = u := le_antisymm hx.2 hx.1
        subst x
        exact hu)
    have hslice : ContinuousOn
        (fun s : ℝ => affineMixedRawSForm w σ d (u, s))
        (Set.Icc (0 : ℝ) R) := by
      intro s hs
      have hpair : ContinuousWithinAt (fun y : ℝ => (u, y))
          (Set.Icc (0 : ℝ) R) s :=
        continuousWithinAt_const.prodMk continuousWithinAt_id
      exact (hraw (u, s) ⟨⟨le_rfl, le_rfl⟩, hs⟩).comp hpair
        (fun y hy => ⟨⟨le_rfl, le_rfl⟩, hy⟩)
    have hint : IntervalIntegrable
        (fun s : ℝ => affineMixedRawSForm w σ d (u, s)) volume 0 R := by
      apply ContinuousOn.intervalIntegrable
      rwa [Set.uIcc_of_le hR]
    apply AEStronglyMeasurable.congr
      (by simpa only [Set.uIoc_of_le hR] using hint.1.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact affineMixedRawSForm_eq_mixedSForm hσ hd hu hs.1.le
  have hboundAE : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) R)),
      ∀ x ∈ U,
        ‖mixedSForm (affineMatrix_isHermitian hσ hd x) w d s‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    intro x hx
    simpa only [Real.norm_eq_abs] using hbound s hs x hx
  have hCint : Integrable (fun _ : ℝ => C)
      (volume.restrict (Set.Ioc (0 : ℝ) R)) :=
    continuous_const.integrableOn_Ioc
  have hdiff : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) R)),
      ∀ x ∈ U, HasDerivAt
        (fun y : ℝ => affineMixedLogIntegrand w σ d y s)
        (mixedSForm (affineMatrix_isHermitian hσ hd x) w d s) x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    intro x hx
    have hxpos := hpos x hx
    have hdif := affineMixedLogIntegrand_hasDerivAt
      (w := w) hxpos hs.1
    have heq : affineMatrix_isHermitian hσ hd x = hxpos.1 :=
      Subsingleton.elim _ _
    exact hdif.congr_deriv (by rw [heq])
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc (0 : ℝ) R))
    (F := fun x s => affineMixedLogIntegrand w σ d x s)
    (F' := fun x s => mixedSForm
      (affineMatrix_isHermitian hσ hd x) w d s)
    (bound := fun _ => C) hU hFmeas hFint hF'meas hboundAE hCint hdiff
  have hderInt : HasDerivAt
      (fun x : ℝ => ∫ s in (0 : ℝ)..R,
        affineMixedLogIntegrand w σ d x s)
      (∫ s in (0 : ℝ)..R,
        mixedSForm (affineMatrix_isHermitian hσ hd u) w d s) u := by
    simpa only [intervalIntegral.integral_of_le hR] using hmain.2
  refine hderInt.congr_of_eventuallyEq ?_
  filter_upwards [hU] with x hx
  exact truncatedAffineMixedMatrixLogPairing_eq_integral
    hw hσ hd hR (hpos x hx)

/-- Unconditional finite-cutoff mixed matrix-log derivative on a compactly
contained faithful neighborhood. -/
theorem truncatedAffineMixedMatrixLogPairing_hasDerivAt
    (hw : w.IsHermitian) (hσ : σ.IsHermitian) (hd : d.IsHermitian)
    {u R δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ x ∈ Set.Icc (u - δ) (u + δ),
      (σ + x • d).PosDef) (hR : 0 ≤ R) :
    HasDerivAt
      (fun x : ℝ => truncatedAffineMixedMatrixLogPairing hw hσ hd R x)
      (∫ s in (0 : ℝ)..R,
        mixedSForm (affineMatrix_isHermitian hσ hd u) w d s) u := by
  obtain ⟨C, hC⟩ := exists_affineMixedSForm_bound_rect
    (w := w) hσ hd (R := R) hpos
  refine truncatedAffineMixedMatrixLogPairing_hasDerivAt_of_bound
    hw hσ hd (U := Set.Ioo (u - δ) (u + δ)) (C := C)
    (Ioo_mem_nhds (by linarith) (by linarith)) ?_ hR ?_
  · intro x hx
    exact hpos x ⟨hx.1.le, hx.2.le⟩
  · intro s hs x hx
    exact hC s ⟨hs.1.le, hs.2⟩ x ⟨hx.1.le, hx.2.le⟩

/-- Four times the finite mixed resolvent integral is the difference of the
two polarized diagonal curvature cutoffs. -/
theorem four_mul_integral_mixedSForm_eq_cutoff_sub
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) (hw : w.IsHermitian)
    {u : ℝ} (hu : (σ + u • d).PosDef) (N : ℕ) :
    4 * (∫ s in (0 : ℝ)..(N : ℝ),
      mixedSForm (affineMatrix_isHermitian hσ hd u) w d s) =
      affineTruncatedBkmCurvatureAlong σ d (w + d) N u -
        affineTruncatedBkmCurvatureAlong σ d (w - d) N u := by
  rw [affineTruncatedBkmCurvatureAlong_eq_truncated hσ hd hu,
    affineTruncatedBkmCurvatureAlong_eq_truncated hσ hd hu]
  unfold truncatedResolventCurvature
  let hu' : (σ + u • d).PosDef :=
    ⟨affineMatrix_isHermitian hσ hd u, hu.2⟩
  have hp : IntervalIntegrable
      (fun s : ℝ => sForm hu'.1 (w + d) s) volume 0 (N : ℝ) :=
    sForm_intervalIntegrable hu' (hw.add hd) (Nat.cast_nonneg N)
  have hm : IntervalIntegrable
      (fun s : ℝ => sForm hu'.1 (w - d) s) volume 0 (N : ℝ) :=
    sForm_intervalIntegrable hu' (hw.sub hd) (Nat.cast_nonneg N)
  rw [← intervalIntegral.integral_sub hp hm]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  have hpol := mixedSForm_eq_polarization hu'.1 w d s
  change 4 * mixedSForm hu'.1 w d s =
    sForm hu'.1 (w + d) s - sForm hu'.1 (w - d) s
  rw [hpol]
  ring

/-- **Mixed affine matrix-log derivative.**  Pairing the logarithm with a
Hermitian matrix `w` and differentiating along an independent Hermitian
direction `d` yields the polarized BKM form. -/
theorem affineMatrixLogPairing_mixed_hasDerivAt
    (hw : w.IsHermitian) (hσ : σ.IsHermitian) (hd : d.IsHermitian)
    {A B u : ℝ} (hpos : ∀ x ∈ Set.Ioo A B, (σ + x • d).PosDef)
    (hu : u ∈ Set.Ioo A B) :
    HasDerivAt
      (fun x : ℝ =>
        (Matrix.trace (w * matLog (affineMatrix_isHermitian hσ hd x))).re)
      (mixedBkmForm (affineMatrix_isHermitian hσ hd u) w d) u := by
  let f : ℕ → ℝ → ℝ := fun N x =>
    4 * truncatedAffineMixedMatrixLogPairing hw hσ hd (N : ℝ) x
  let f' : ℕ → ℝ → ℝ := fun N x =>
    affineTruncatedBkmCurvatureAlong σ d (w + d) N x -
      affineTruncatedBkmCurvatureAlong σ d (w - d) N x
  let g : ℝ → ℝ := fun x =>
    4 * (Matrix.trace
      (w * matLog (affineMatrix_isHermitian hσ hd x))).re
  let g' : ℝ → ℝ := fun x =>
    affineBkmFormAlong hσ hd (w + d) x -
      affineBkmFormAlong hσ hd (w - d) x
  have hp := tendstoLocallyUniformlyOn_affineTruncatedBkmCurvatureAlong
    hσ hd (hw.add hd) hpos
  have hm := tendstoLocallyUniformlyOn_affineTruncatedBkmCurvatureAlong
    hσ hd (hw.sub hd) hpos
  have hf' : TendstoLocallyUniformlyOn f' g' atTop (Set.Ioo A B) := by
    change TendstoLocallyUniformlyOn
      ((fun N : ℕ => affineTruncatedBkmCurvatureAlong σ d (w + d) N) -
        fun N : ℕ => affineTruncatedBkmCurvatureAlong σ d (w - d) N)
      (affineBkmFormAlong hσ hd (w + d) -
        affineBkmFormAlong hσ hd (w - d)) atTop (Set.Ioo A B)
    exact hp.sub hm
  have hfderiv : ∀ᶠ N in atTop, ∀ x ∈ Set.Ioo A B,
      HasDerivAt (f N) (f' N x) x := by
    filter_upwards with N
    intro x hx
    let δ : ℝ := min (x - A) (B - x) / 2
    have hmin : 0 < min (x - A) (B - x) :=
      lt_min (by linarith [hx.1]) (by linarith [hx.2])
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hδleft : δ < x - A := by
      have hle := min_le_left (x - A) (B - x)
      dsimp [δ]
      linarith
    have hδright : δ < B - x := by
      have hle := min_le_right (x - A) (B - x)
      dsimp [δ]
      linarith
    have hposIcc : ∀ y ∈ Set.Icc (x - δ) (x + δ),
        (σ + y • d).PosDef := by
      intro y hy
      apply hpos y
      constructor <;> linarith [hy.1, hy.2]
    have hdcut := truncatedAffineMixedMatrixLogPairing_hasDerivAt
      hw hσ hd hδ hposIcc (Nat.cast_nonneg N)
    have hfour := four_mul_integral_mixedSForm_eq_cutoff_sub
      hσ hd hw (hpos x hx) N
    change HasDerivAt
      (fun y : ℝ =>
        4 * truncatedAffineMixedMatrixLogPairing hw hσ hd (N : ℝ) y)
      (affineTruncatedBkmCurvatureAlong σ d (w + d) N x -
        affineTruncatedBkmCurvatureAlong σ d (w - d) N x) x
    exact (hdcut.const_mul 4).congr_deriv hfour
  have hfg : ∀ x ∈ Set.Ioo A B,
      Tendsto (fun N : ℕ => f N x) atTop (𝓝 (g x)) := by
    intro x hx
    let hx' : (σ + x • d).PosDef :=
      ⟨affineMatrix_isHermitian hσ hd x, (hpos x hx).2⟩
    have hlim := (tendsto_truncatedMatrixLogPairing hw hx').comp
      tendsto_natCast_atTop_atTop
    change Tendsto
      (fun N : ℕ => 4 * truncatedMatrixLogPairing w hx'.1 (N : ℝ)) atTop
      (𝓝 (4 * (Matrix.trace (w * matLog hx'.1)).re))
    exact tendsto_const_nhds.mul (hlim.congr' <| by
      filter_upwards with N
      rfl)
  have hfourDeriv : HasDerivAt g (g' u) u :=
    hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_Ioo
      hf' hfderiv hfg hu
  have hscaled := hfourDeriv.const_mul ((4 : ℝ)⁻¹)
  have hcoef : (4 : ℝ)⁻¹ * g' u =
      mixedBkmForm (affineMatrix_isHermitian hσ hd u) w d := by
    unfold g' affineBkmFormAlong mixedBkmForm
    ring
  have hfun : (fun x : ℝ => (4 : ℝ)⁻¹ * g x) =
      fun x : ℝ =>
        (Matrix.trace (w * matLog (affineMatrix_isHermitian hσ hd x))).re := by
    funext x
    unfold g
    ring
  rw [hfun] at hscaled
  exact hscaled.congr_deriv hcoef

/-- The spectral functional calculus is additive in its scalar function. -/
theorem matFun_add_functions {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (f g : ℝ → ℝ) :
    matFun hA (fun x => f x + g x) = matFun hA f + matFun hA g := by
  unfold matFun
  rw [← map_add]
  congr 1
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp only [Matrix.diagonal_apply_eq, Function.comp_apply,
      Matrix.add_apply]
    exact RCLike.ofReal_add (K := ℂ) _ _
  · simp [Matrix.diagonal_apply_ne _ hij]

/-- Matrix logarithm transports across equality of its Hermitian matrix
argument. -/
theorem matLog_congr {A B : Matrix n n ℂ} (h : A = B)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    matLog hA = matLog hB := by
  subst B
  have hp : hA = hB := Subsingleton.elim _ _
  subst hp
  rfl

/-- Matrix logarithm of a positive real scaling. -/
theorem matLog_pos_smul {A : Matrix n n ℂ} (hA : A.PosDef)
    {c : ℝ} (hc : 0 < c) (hcA : (c • A).IsHermitian) :
    matLog hcA = Real.log c • (1 : Matrix n n ℂ) + matLog hA.1 := by
  unfold matLog
  rw [matFun_smul_pos hA.1 c hcA Real.log]
  rw [Petz.matFun_congr hA.1 _
    (fun x => Real.log c + Real.log x) (fun i => by
      rw [← Real.log_mul hc.ne' (hA.eigenvalues_pos i).ne'])]
  rw [matFun_add_functions]
  rw [show matFun hA.1 (fun _ => Real.log c) =
      Real.log c • (1 : Matrix n n ℂ) by
    have hcst := matFun_real_smul hA.1 (Real.log c) (fun _ => 1)
    rw [Petz.matFun_one] at hcst
    simpa only [mul_one] using hcst]

/-- The BKM quadratic form is even in its tangent. -/
theorem bkmForm_neg (hσ : σ.IsHermitian) (x : Matrix n n ℂ) :
    bkmForm hσ (-x) = bkmForm hσ x := by
  unfold bkmForm tangentIn
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply,
    Complex.normSq_neg]

/-- Symmetry of the real-polarized BKM form. -/
theorem mixedBkmForm_symm (hσ : σ.IsHermitian)
    (x y : Matrix n n ℂ) :
    mixedBkmForm hσ x y = mixedBkmForm hσ y x := by
  unfold mixedBkmForm
  rw [add_comm]
  have hsub : y - x = -(x - y) := by module
  rw [hsub, bkmForm_neg]

end QRE
end NCG
