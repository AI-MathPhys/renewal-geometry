/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MatrixLogResolventApproximationExact

/-!
# Affine derivative of the normalized matrix-log resolvent integrand

This file puts the scalar logarithm normalization and the noncommutative
resolvent derivative into one concrete parameter-dependent integrand.  At
every faithful point of the affine path, its derivative is exactly the BKM
resolvent `sForm`.
-/

open Matrix Filter Topology MeasureTheory intervalIntegral
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ v : Matrix n n ℂ}

omit [Fintype n] [DecidableEq n] in
/-- The Hermitian proof for the affine path `σ + t v`. -/
theorem affineMatrix_isHermitian (hσ : σ.IsHermitian)
    (hv : v.IsHermitian) (t : ℝ) : (σ + t • v).IsHermitian :=
  hσ.add (real_smul_isHermitian' t hv)

/-- The normalized resolvent integrand whose cutoff integral approximates
`Re Tr(v log(σ+t v))`. -/
noncomputable def affineLogResolventIntegrand
    (σ v : Matrix n n ℂ) (t s : ℝ) : ℝ :=
  v.trace.re * (1 + s)⁻¹ -
    (Matrix.trace (v * Ring.inverse
      (σ + t • v + s • (1 : Matrix n n ℂ)))).re

/-- The BKM resolvent curvature along the Hermitian affine path. -/
noncomputable def affineSForm (hσ : σ.IsHermitian)
    (hv : v.IsHermitian) (t s : ℝ) : ℝ :=
  sForm (affineMatrix_isHermitian hσ hv t) v s

/-- Proof-independent ring-inverse expression for the affine BKM curvature. -/
noncomputable def affineRawSForm
    (σ v : Matrix n n ℂ) (p : ℝ × ℝ) : ℝ :=
  (Matrix.trace (v * (Ring.inverse
    (σ + p.1 • v + p.2 • (1 : Matrix n n ℂ)) * (v * Ring.inverse
      (σ + p.1 • v + p.2 • (1 : Matrix n n ℂ)))))).re

/-- On a faithful affine point and at nonnegative resolvent parameter, the
proof-independent curvature is the spectral `affineSForm`. -/
theorem affineRawSForm_eq_affineSForm (hσ : σ.IsHermitian)
    (hv : v.IsHermitian) {u s : ℝ} (hu : (σ + u • v).PosDef)
    (hs : 0 ≤ s) :
    affineRawSForm σ v (u, s) = affineSForm hσ hv u s := by
  unfold affineRawSForm affineSForm sForm
  have heq : affineMatrix_isHermitian hσ hv u = hu.1 := Subsingleton.elim _ _
  rw [heq, ringInverse_shift_eq_resolvent_nonneg hu hs]
  simp only [Matrix.mul_assoc]

/-- Joint continuity of the proof-independent affine curvature on a compact
rectangle where the affine base remains faithful. -/
theorem affineRawSForm_continuousOn_rect {a b R : ℝ}
    (hpos : ∀ u ∈ Set.Icc a b, (σ + u • v).PosDef) :
    ContinuousOn (affineRawSForm σ v)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) R) := by
  intro p hp
  have hpath : ContinuousAt
      (fun q : ℝ × ℝ =>
        σ + q.1 • v + q.2 • (1 : Matrix n n ℂ)) p := by
    fun_prop
  have hunit : IsUnit
      (σ + p.1 • v + p.2 • (1 : Matrix n n ℂ)) :=
    isUnit_shift_of_posDef_nonneg (hpos p.1 hp.1) hp.2.1
  have hinvAt : ContinuousAt Ring.inverse
      (σ + p.1 • v + p.2 • (1 : Matrix n n ℂ)) := by
    simpa [hunit.unit_spec] using
      (NormedRing.inverse_continuousAt hunit.unit)
  let r : ℝ × ℝ → Matrix n n ℂ := fun q => Ring.inverse
    (σ + q.1 • v + q.2 • (1 : Matrix n n ℂ))
  have hinv : ContinuousAt r p :=
    ContinuousAt.comp'
      (f := fun q : ℝ × ℝ =>
        σ + q.1 • v + q.2 • (1 : Matrix n n ℂ)) hinvAt hpath
  have hinner : ContinuousAt
      (fun q : ℝ × ℝ => r q * (v * r q)) p :=
    hinv.mul (continuousAt_const.mul hinv)
  have htrace : ContinuousAt
      (fun q : ℝ × ℝ => realTraceLeft v
        (r q * (v * r q))) p :=
    ((realTraceLeft v).continuous.continuousAt).comp' hinner
  change ContinuousWithinAt
    (fun q : ℝ × ℝ =>
      (Matrix.trace (v * (Ring.inverse
        (σ + q.1 • v + q.2 • (1 : Matrix n n ℂ)) * (v * Ring.inverse
          (σ + q.1 • v + q.2 • (1 : Matrix n n ℂ)))))).re)
    (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) R) p
  simpa only [r, realTraceLeft_apply] using htrace.continuousWithinAt

/-- Compact faithful rectangles carry a uniform bound for the affine BKM
curvature. -/
theorem exists_affineSForm_bound_rect (hσ : σ.IsHermitian)
    (hv : v.IsHermitian) {a b R : ℝ}
    (hpos : ∀ u ∈ Set.Icc a b, (σ + u • v).PosDef) :
    ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) R, ∀ u ∈ Set.Icc a b,
      |affineSForm hσ hv u s| ≤ C := by
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) R) :=
    isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p => |affineRawSForm σ v p|)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) R) :=
    (affineRawSForm_continuousOn_rect hpos).abs
  obtain ⟨C, hC⟩ := hK.bddAbove_image hcont
  refine ⟨C, ?_⟩
  intro s hs u hu
  have hle := hC ⟨(u, s), ⟨hu, hs⟩, rfl⟩
  change |affineRawSForm σ v (u, s)| ≤ C at hle
  rw [affineRawSForm_eq_affineSForm hσ hv (hpos u hu) hs.1] at hle
  exact hle

/-- At a faithful affine point and positive resolvent parameter, the path
derivative of the normalized log-resolvent integrand is exactly `sForm`. -/
theorem affineLogResolventIntegrand_hasDerivAt {t s : ℝ}
    (ht : (σ + t • v).PosDef) (hs : 0 < s) :
    HasDerivAt (fun u : ℝ => affineLogResolventIntegrand σ v u s)
      (sForm ht.1 v s) t := by
  have hconst : HasDerivAt (fun _ : ℝ => v.trace.re * (1 + s)⁻¹) 0 t :=
    hasDerivAt_const t _
  have hres := trace_resolvent_affine_hasDerivAt_at ht hs
  have hout := hconst.sub hres
  unfold affineLogResolventIntegrand
  change HasDerivAt
    ((fun _ : ℝ => v.trace.re * (1 + s)⁻¹) -
      fun u : ℝ => (Matrix.trace (v * Ring.inverse
        (σ + u • v + s • (1 : Matrix n n ℂ)))).re)
    (sForm ht.1 v s) t
  exact hout.congr_deriv (by ring)

/-- Continuity in the resolvent parameter on the nonnegative half-line at a
faithful affine point. -/
theorem affineLogResolventIntegrand_continuousAt_s {t s : ℝ}
    (ht : (σ + t • v).PosDef) (hs : 0 ≤ s) :
    ContinuousAt (fun r : ℝ => affineLogResolventIntegrand σ v t r) s := by
  have hpath : ContinuousAt
      (fun r : ℝ => (σ + t • v) + r • (1 : Matrix n n ℂ)) s := by
    have hlin : HasDerivAt (fun r : ℝ => r • (1 : Matrix n n ℂ))
        (1 : Matrix n n ℂ) s := by
      simpa using (hasDerivAt_id s).smul_const (1 : Matrix n n ℂ)
    exact (hlin.const_add (σ + t • v)).continuousAt
  have hunit : IsUnit ((σ + t • v) + s • (1 : Matrix n n ℂ)) :=
    isUnit_shift_of_posDef_nonneg ht hs
  have hinvAt : ContinuousAt Ring.inverse
      ((σ + t • v) + s • (1 : Matrix n n ℂ)) := by
    simpa [hunit.unit_spec] using
      (NormedRing.inverse_continuousAt hunit.unit)
  have hinv : ContinuousAt
      (fun r : ℝ => Ring.inverse
        ((σ + t • v) + r • (1 : Matrix n n ℂ))) s :=
    ContinuousAt.comp'
      (f := fun r : ℝ => (σ + t • v) + r • (1 : Matrix n n ℂ))
      hinvAt hpath
  have htrace : ContinuousAt
      (fun r : ℝ => realTraceLeft v (Ring.inverse
        ((σ + t • v) + r • (1 : Matrix n n ℂ)))) s :=
    ((realTraceLeft v).continuous.continuousAt).comp' hinv
  have hscalar : ContinuousAt (fun r : ℝ => v.trace.re * (1 + r)⁻¹) s := by
    have hone : 1 + s ≠ 0 := ne_of_gt (by linarith)
    exact continuousAt_const.mul
      ((continuousAt_const.add continuousAt_id).inv₀ hone)
  unfold affineLogResolventIntegrand
  change ContinuousAt
    ((fun r : ℝ => v.trace.re * (1 + r)⁻¹) -
      fun r : ℝ => (Matrix.trace (v * Ring.inverse
        ((σ + t • v) + r • (1 : Matrix n n ℂ)))).re) s
  simpa only [realTraceLeft_apply] using hscalar.sub htrace

/-- The normalized affine log-resolvent integrand is interval integrable on
every finite nonnegative cutoff. -/
theorem affineLogResolventIntegrand_intervalIntegrable {t R : ℝ}
    (ht : (σ + t • v).PosDef) (hR : 0 ≤ R) :
    IntervalIntegrable (fun s : ℝ => affineLogResolventIntegrand σ v t s)
      MeasureTheory.volume 0 R := by
  apply ContinuousOn.intervalIntegrable
  intro s hs
  rw [Set.uIcc_of_le hR] at hs
  exact (affineLogResolventIntegrand_continuousAt_s ht hs.1).continuousWithinAt

/-- The finite-cutoff affine matrix-log pairing, defined through the
repository's spectral functional calculus. -/
noncomputable def truncatedAffineMatrixLogPairing
    (hσ : σ.IsHermitian) (hv : v.IsHermitian) (R t : ℝ) : ℝ :=
  truncatedMatrixLogPairing v (affineMatrix_isHermitian hσ hv t) R

/-- Whenever the affine point is faithful, the spectral cutoff pairing is
the concrete normalized resolvent integral. -/
theorem truncatedAffineMatrixLogPairing_eq_integral
    (hσ : σ.IsHermitian) (hv : v.IsHermitian) {R t : ℝ}
    (hR : 0 ≤ R) (ht : (σ + t • v).PosDef) :
    truncatedAffineMatrixLogPairing hσ hv R t =
      ∫ s in (0 : ℝ)..R, affineLogResolventIntegrand σ v t s := by
  unfold truncatedAffineMatrixLogPairing affineLogResolventIntegrand
  have heq : affineMatrix_isHermitian hσ hv t = ht.1 := Subsingleton.elim _ _
  rw [heq, truncatedMatrixLogPairing_eq_integral hv ht hR]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hR] at hs
  change v.trace.re * (1 + s)⁻¹ -
      (Matrix.trace (v * resolvent ht.1 s)).re =
    v.trace.re * (1 + s)⁻¹ -
      (Matrix.trace (v * Ring.inverse
        ((σ + t • v) + s • (1 : Matrix n n ℂ)))).re
  rw [ringInverse_shift_eq_resolvent_nonneg ht hs.1]

set_option maxHeartbeats 1600000 in
-- dominated parameter-integral assembly
/-- Differentiation of the finite-cutoff spectral matrix-log pairing under a
uniform local curvature bound.  All measurability and integrability
hypotheses are discharged from the concrete continuity lemmas; `hbound` is
the sole quantitative domination input. -/
theorem truncatedAffineMatrixLogPairing_hasDerivAt_of_bound
    (hσ : σ.IsHermitian) (hv : v.IsHermitian)
    {U : Set ℝ} {t R C : ℝ} (hU : U ∈ 𝓝 t)
    (hpos : ∀ u ∈ U, (σ + u • v).PosDef) (hR : 0 ≤ R)
    (hbound : ∀ s ∈ Set.Ioc (0 : ℝ) R, ∀ u ∈ U,
      |affineSForm hσ hv u s| ≤ C) :
    HasDerivAt (fun u : ℝ => truncatedAffineMatrixLogPairing hσ hv R u)
      (truncatedResolventCurvature
        (affineMatrix_isHermitian hσ hv t) v R) t := by
  have htU : t ∈ U := mem_of_mem_nhds hU
  have ht : (σ + t • v).PosDef := hpos t htU
  have hFmeas : ∀ᶠ u in 𝓝 t,
      AEStronglyMeasurable (affineLogResolventIntegrand σ v u)
        (volume.restrict (Set.Ioc (0 : ℝ) R)) := by
    filter_upwards [hU] with u hu
    exact ((affineLogResolventIntegrand_intervalIntegrable
      (hpos u hu) hR).1).aestronglyMeasurable
  have hFint : Integrable (affineLogResolventIntegrand σ v t)
      (volume.restrict (Set.Ioc (0 : ℝ) R)) :=
    (affineLogResolventIntegrand_intervalIntegrable ht hR).1
  have hF'meas : AEStronglyMeasurable (affineSForm hσ hv t)
      (volume.restrict (Set.Ioc (0 : ℝ) R)) := by
    let ht' : (σ + t • v).PosDef :=
      ⟨affineMatrix_isHermitian hσ hv t, ht.2⟩
    change AEStronglyMeasurable (sForm ht'.1 v)
      (volume.restrict (Set.Ioc (0 : ℝ) R))
    exact ((sForm_intervalIntegrable ht' hv hR).1).aestronglyMeasurable
  have hboundAE : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) R)),
      ∀ u ∈ U, ‖affineSForm hσ hv u s‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    intro u hu
    simpa [Real.norm_eq_abs] using hbound s hs u hu
  have hCint : Integrable (fun _ : ℝ => C)
      (volume.restrict (Set.Ioc (0 : ℝ) R)) :=
    continuous_const.integrableOn_Ioc
  have hdiff : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) R)),
      ∀ u ∈ U, HasDerivAt
        (fun x : ℝ => affineLogResolventIntegrand σ v x s)
        (affineSForm hσ hv u s) u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    intro u hu
    have hd := affineLogResolventIntegrand_hasDerivAt
      (hpos u hu) hs.1
    have heq : affineMatrix_isHermitian hσ hv u = (hpos u hu).1 :=
      Subsingleton.elim _ _
    unfold affineSForm
    exact hd.congr_deriv (by rw [heq])
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc (0 : ℝ) R))
    (F := fun u s => affineLogResolventIntegrand σ v u s)
    (F' := fun u s => affineSForm hσ hv u s)
    (bound := fun _ => C) hU hFmeas hFint hF'meas hboundAE hCint hdiff
  have hderInt : HasDerivAt
      (fun u : ℝ => ∫ s in (0 : ℝ)..R,
        affineLogResolventIntegrand σ v u s)
      (∫ s in (0 : ℝ)..R, affineSForm hσ hv t s) t := by
    simpa only [intervalIntegral.integral_of_le hR] using hmain.2
  have hcurv : (∫ s in (0 : ℝ)..R, affineSForm hσ hv t s) =
      truncatedResolventCurvature
        (affineMatrix_isHermitian hσ hv t) v R := by
    rfl
  refine (hderInt.congr_deriv hcurv).congr_of_eventuallyEq ?_
  filter_upwards [hU] with u hu
  exact truncatedAffineMatrixLogPairing_eq_integral hσ hv hR (hpos u hu)

/-- **Unconditional finite-cutoff matrix-log derivative on a faithful
neighborhood.**  Compactness automatically supplies the domination bound:
the derivative of the cutoff log pairing is the cutoff BKM curvature. -/
theorem truncatedAffineMatrixLogPairing_hasDerivAt
    (hσ : σ.IsHermitian) (hv : v.IsHermitian)
    {t R δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ u ∈ Set.Icc (t - δ) (t + δ),
      (σ + u • v).PosDef) (hR : 0 ≤ R) :
    HasDerivAt (fun u : ℝ => truncatedAffineMatrixLogPairing hσ hv R u)
      (truncatedResolventCurvature
        (affineMatrix_isHermitian hσ hv t) v R) t := by
  obtain ⟨C, hC⟩ := exists_affineSForm_bound_rect hσ hv hpos
    (R := R)
  refine truncatedAffineMatrixLogPairing_hasDerivAt_of_bound hσ hv
    (U := Set.Ioo (t - δ) (t + δ))
    (C := C) (Ioo_mem_nhds (by linarith) (by linarith)) ?_ hR ?_
  · intro u hu
    exact hpos u ⟨hu.1.le, hu.2.le⟩
  · intro s hs u hu
    exact hC s ⟨hs.1.le, hs.2⟩ u ⟨hu.1.le, hu.2.le⟩

end QRE
end NCG
