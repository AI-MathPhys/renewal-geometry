/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AffineBkmLocalUniformLimitExact

/-!
# Two-direction affine BKM cutoff convergence

The base path direction and the tangent inserted in the BKM quadratic form
need not coincide.  This generalization supplies local uniform convergence
for a fixed Hermitian tangent along an independently chosen faithful affine
base path.  It is the diagonal input for polarization of mixed matrix-log
derivatives.
-/

open Matrix Finset Filter Topology MeasureTheory intervalIntegral
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ d z : Matrix n n ℂ}

/-- BKM curvature in tangent `z` along the affine base path `σ + u d`. -/
noncomputable def affineBkmFormAlong (hσ : σ.IsHermitian)
    (hd : d.IsHermitian) (z : Matrix n n ℂ) (u : ℝ) : ℝ :=
  bkmForm (affineMatrix_isHermitian hσ hd u) z

/-- Convexity of a fixed-tangent BKM form along an independent affine base
path. -/
theorem affineBkmFormAlong_convexOn (hσ : σ.IsHermitian)
    (hd : d.IsHermitian) (_hz : z.IsHermitian) {U : Set ℝ}
    (hU : Convex ℝ U)
    (hpos : ∀ u ∈ U, (σ + u • d).PosDef) :
    ConvexOn ℝ U (affineBkmFormAlong hσ hd z) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy a b ha hb hab
  have hbval : b = 1 - a := by linarith
  subst b
  have hxy : a • x + (1 - a) • y ∈ U := hU hx hy ha hb hab
  let lam : Fin 2 → ℝ := ![a, 1 - a]
  let σs : Fin 2 → Matrix n n ℂ := ![σ + x • d, σ + y • d]
  let zs : Fin 2 → Matrix n n ℂ := ![z, z]
  have hσj : ∀ j, (σs j).PosDef := by
    intro j
    fin_cases j
    · exact hpos x hx
    · exact hpos y hy
  have hbase : (∑ j, lam j • σs j) =
      σ + (a • x + (1 - a) • y) • d := by
    simp only [lam, σs, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    module
  have hbar : (∑ j, lam j • σs j).PosDef := by
    rw [hbase]
    exact hpos (a • x + (1 - a) • y) hxy
  have hconv := bkmForm_convex (n := n) (lam := lam)
    (σs := σs) (vs := zs) (fun j => by
      fin_cases j <;> assumption) hσj hbar
  have hzsum : (∑ j, lam j • zs j) = z := by
    simp only [lam, zs, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    module
  have hleft : bkmForm hbar.1 (∑ j, lam j • zs j) =
      affineBkmFormAlong hσ hd z (a • x + (1 - a) • y) := by
    unfold affineBkmFormAlong
    exact Petz.bkmForm_congr hbase hzsum hbar.1
      (affineMatrix_isHermitian hσ hd (a • x + (1 - a) • y))
  have hxform : bkmForm (hσj 0).1 (zs 0) =
      affineBkmFormAlong hσ hd z x := by
    unfold affineBkmFormAlong
    apply Petz.bkmForm_congr <;> rfl
  have hyform : bkmForm (hσj 1).1 (zs 1) =
      affineBkmFormAlong hσ hd z y := by
    unfold affineBkmFormAlong
    apply Petz.bkmForm_congr <;> rfl
  have hright : (∑ j, lam j * bkmForm (hσj j).1 (zs j)) =
      a * affineBkmFormAlong hσ hd z x +
        (1 - a) * affineBkmFormAlong hσ hd z y := by
    rw [Fin.sum_univ_two]
    change a * bkmForm (hσj 0).1 (zs 0) +
      (1 - a) * bkmForm (hσj 1).1 (zs 1) = _
    rw [hxform, hyform]
  rw [hleft, hright] at hconv
  simpa only [smul_eq_mul] using hconv

/-- A fixed-tangent affine BKM curvature is continuous on every open
faithful base interval. -/
theorem affineBkmFormAlong_continuousOn (hσ : σ.IsHermitian)
    (hd : d.IsHermitian) (hz : z.IsHermitian) {U : Set ℝ}
    (hU : IsOpen U) (hUc : Convex ℝ U)
    (hpos : ∀ u ∈ U, (σ + u • d).PosDef) :
    ContinuousOn (affineBkmFormAlong hσ hd z) U :=
  (affineBkmFormAlong_convexOn hσ hd hz hUc hpos).continuousOn hU

/-- Proof-independent fixed-tangent curvature along an independent affine
base path. -/
noncomputable def affineRawSFormAlong
    (σ d z : Matrix n n ℂ) (p : ℝ × ℝ) : ℝ :=
  (Matrix.trace (z * (Ring.inverse
    (σ + p.1 • d + p.2 • (1 : Matrix n n ℂ)) * (z * Ring.inverse
      (σ + p.1 • d + p.2 • (1 : Matrix n n ℂ)))))).re

/-- The raw two-direction curvature equals the spectral `sForm` at faithful
bases and nonnegative resolvent parameter. -/
theorem affineRawSFormAlong_eq_sForm (hσ : σ.IsHermitian)
    (hd : d.IsHermitian) {u s : ℝ} (hu : (σ + u • d).PosDef)
    (hs : 0 ≤ s) :
    affineRawSFormAlong σ d z (u, s) =
      sForm (affineMatrix_isHermitian hσ hd u) z s := by
  unfold affineRawSFormAlong sForm
  have heq : affineMatrix_isHermitian hσ hd u = hu.1 := Subsingleton.elim _ _
  rw [heq, ringInverse_shift_eq_resolvent_nonneg hu hs]
  simp only [Matrix.mul_assoc]

/-- Joint continuity of the two-direction raw curvature on a compact
faithful rectangle. -/
theorem affineRawSFormAlong_continuousOn_rect {a b R : ℝ}
    (hpos : ∀ u ∈ Set.Icc a b, (σ + u • d).PosDef) :
    ContinuousOn (affineRawSFormAlong σ d z)
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
      (fun q : ℝ × ℝ => r q * (z * r q)) p :=
    hinv.mul (continuousAt_const.mul hinv)
  have htrace : ContinuousAt
      (fun q : ℝ × ℝ => realTraceLeft z (r q * (z * r q))) p :=
    ((realTraceLeft z).continuous.continuousAt).comp' hinner
  change ContinuousWithinAt
    (fun q : ℝ × ℝ =>
      (Matrix.trace (z * (Ring.inverse
        (σ + q.1 • d + q.2 • (1 : Matrix n n ℂ)) * (z * Ring.inverse
          (σ + q.1 • d + q.2 • (1 : Matrix n n ℂ)))))).re)
    (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) R) p
  simpa only [r, realTraceLeft_apply] using htrace.continuousWithinAt

/-- Compact faithful rectangles uniformly bound a fixed-tangent BKM
curvature along an independent affine base direction. -/
theorem exists_affineSFormAlong_bound_rect (hσ : σ.IsHermitian)
    (hd : d.IsHermitian) {a b R : ℝ}
    (hpos : ∀ u ∈ Set.Icc a b, (σ + u • d).PosDef) :
    ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) R, ∀ u ∈ Set.Icc a b,
      |sForm (affineMatrix_isHermitian hσ hd u) z s| ≤ C := by
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) R) :=
    isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p => |affineRawSFormAlong σ d z p|)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) R) :=
    (affineRawSFormAlong_continuousOn_rect hpos).abs
  obtain ⟨C, hC⟩ := hK.bddAbove_image hcont
  refine ⟨C, ?_⟩
  intro s hs u hu
  have hle := hC ⟨(u, s), ⟨hu, hs⟩, rfl⟩
  change |affineRawSFormAlong σ d z (u, s)| ≤ C at hle
  rw [affineRawSFormAlong_eq_sForm hσ hd (hpos u hu) hs.1] at hle
  exact hle

/-- Finite fixed-tangent curvature cutoff along an independent affine base
path. -/
noncomputable def affineTruncatedBkmCurvatureAlong
    (σ d z : Matrix n n ℂ) (N : ℕ) (u : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..(N : ℝ), affineRawSFormAlong σ d z (u, s)

/-- At faithful affine points, the raw two-direction cutoff is the spectral
truncated resolvent curvature. -/
theorem affineTruncatedBkmCurvatureAlong_eq_truncated
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) {N : ℕ} {u : ℝ}
    (hu : (σ + u • d).PosDef) :
    affineTruncatedBkmCurvatureAlong σ d z N u =
      truncatedResolventCurvature
        (affineMatrix_isHermitian hσ hd u) z (N : ℝ) := by
  unfold affineTruncatedBkmCurvatureAlong truncatedResolventCurvature
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : 0 ≤ s := by
    rw [Set.uIcc_of_le (Nat.cast_nonneg N)] at hs
    exact hs.1
  exact affineRawSFormAlong_eq_sForm hσ hd hu hs'

set_option maxHeartbeats 1600000 in
-- Dominated convergence through the independent path and tangent matrix
-- instances requires substantial finite-dimensional elaboration.
/-- Every two-direction finite cutoff is continuous on compact faithful base
intervals. -/
theorem affineTruncatedBkmCurvatureAlong_continuousOn
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) {a b : ℝ}
    (hpos : ∀ u ∈ Set.Icc a b, (σ + u • d).PosDef) (N : ℕ) :
    ContinuousOn (affineTruncatedBkmCurvatureAlong σ d z N)
      (Set.Icc a b) := by
  let R : ℝ := (N : ℝ)
  have hR : 0 ≤ R := Nat.cast_nonneg N
  have hraw := affineRawSFormAlong_continuousOn_rect
    (σ := σ) (d := d) (z := z) (R := R) hpos
  obtain ⟨C, hC⟩ := exists_affineSFormAlong_bound_rect
    (z := z) hσ hd (R := R) hpos
  intro u hu
  have hmeas : ∀ᶠ x in 𝓝[Set.Icc a b] u,
      AEStronglyMeasurable (fun s : ℝ => affineRawSFormAlong σ d z (x, s))
        (volume.restrict (Set.uIoc (0 : ℝ) R)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hslice : ContinuousOn
        (fun s : ℝ => affineRawSFormAlong σ d z (x, s))
        (Set.Icc (0 : ℝ) R) := by
      intro s hs
      have hpair : ContinuousWithinAt (fun y : ℝ => (x, y))
          (Set.Icc (0 : ℝ) R) s :=
        continuousWithinAt_const.prodMk continuousWithinAt_id
      exact (hraw (x, s) ⟨hx, hs⟩).comp hpair
        (fun y hy => ⟨hx, hy⟩)
    have hint : IntervalIntegrable
        (fun s : ℝ => affineRawSFormAlong σ d z (x, s)) volume 0 R := by
      apply ContinuousOn.intervalIntegrable
      rwa [Set.uIcc_of_le hR]
    simpa only [Set.uIoc_of_le hR] using hint.1.aestronglyMeasurable
  have hbound : ∀ᶠ x in 𝓝[Set.Icc a b] u,
      ∀ᵐ s ∂volume, s ∈ Set.uIoc (0 : ℝ) R →
        ‖affineRawSFormAlong σ d z (x, s)‖ ≤ C := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    filter_upwards with s
    intro hs
    rw [Set.uIoc_of_le hR] at hs
    have hs' : s ∈ Set.Icc (0 : ℝ) R := ⟨hs.1.le, hs.2⟩
    rw [affineRawSFormAlong_eq_sForm hσ hd (hpos x hx) hs'.1]
    simpa only [Real.norm_eq_abs] using hC s hs' x hx
  have hcont : ∀ᵐ s ∂volume, s ∈ Set.uIoc (0 : ℝ) R →
      ContinuousWithinAt
        (fun x : ℝ => affineRawSFormAlong σ d z (x, s))
        (Set.Icc a b) u := by
    filter_upwards with s
    intro hs
    rw [Set.uIoc_of_le hR] at hs
    have hs' : s ∈ Set.Icc (0 : ℝ) R := ⟨hs.1.le, hs.2⟩
    have hpair : ContinuousOn (fun x : ℝ => (x, s)) (Set.Icc a b) :=
      continuousOn_id.prodMk continuousOn_const
    have hslice := hraw.comp hpair (fun x hx => ⟨hx, hs'⟩)
    change ContinuousWithinAt
      (affineRawSFormAlong σ d z ∘ fun x : ℝ => (x, s))
      (Set.Icc a b) u
    exact hslice u hu
  have hmain := intervalIntegral.continuousWithinAt_of_dominated_interval
    (F := fun x s => affineRawSFormAlong σ d z (x, s))
    (bound := fun _ => C) (a := (0 : ℝ)) (b := R)
    (s := Set.Icc a b) hmeas hbound intervalIntegrable_const hcont
  change ContinuousWithinAt
    (fun x : ℝ => ∫ s in (0 : ℝ)..(N : ℝ),
      affineRawSFormAlong σ d z (x, s)) (Set.Icc a b) u
  simpa only [R] using hmain

/-- At a faithful point, the fixed-tangent cutoffs are monotone in the
natural-number cutoff. -/
theorem affineTruncatedBkmCurvatureAlong_monotone
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) (hz : z.IsHermitian)
    {u : ℝ} (hu : (σ + u • d).PosDef) :
    Monotone (fun N : ℕ =>
      affineTruncatedBkmCurvatureAlong σ d z N u) := by
  intro N M hNM
  change affineTruncatedBkmCurvatureAlong σ d z N u ≤
    affineTruncatedBkmCurvatureAlong σ d z M u
  rw [affineTruncatedBkmCurvatureAlong_eq_truncated hσ hd hu,
    affineTruncatedBkmCurvatureAlong_eq_truncated hσ hd hu]
  unfold truncatedResolventCurvature
  let hu' : (σ + u • d).PosDef :=
    ⟨affineMatrix_isHermitian hσ hd u, hu.2⟩
  apply intervalIntegral.integral_mono_interval
    (c := (0 : ℝ)) (d := (M : ℝ)) le_rfl (Nat.cast_nonneg N)
  · exact_mod_cast hNM
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact sForm_nonneg hu'.posSemidef hz hs.1
  · exact sForm_intervalIntegrable hu' hz (Nat.cast_nonneg M)

/-- Pointwise convergence of the fixed-tangent cutoffs to the two-direction
affine BKM form. -/
theorem tendsto_affineTruncatedBkmCurvatureAlong
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) (hz : z.IsHermitian)
    {u : ℝ} (hu : (σ + u • d).PosDef) :
    Tendsto (fun N : ℕ => affineTruncatedBkmCurvatureAlong σ d z N u)
      atTop (𝓝 (affineBkmFormAlong hσ hd z u)) := by
  let hu' : (σ + u • d).PosDef :=
    ⟨affineMatrix_isHermitian hσ hd u, hu.2⟩
  have hlim := (tendsto_truncatedResolventCurvature hu' hz).comp
    tendsto_natCast_atTop_atTop
  apply hlim.congr'
  filter_upwards with N
  rw [affineTruncatedBkmCurvatureAlong_eq_truncated hσ hd hu]
  rfl

/-- Finite fixed-tangent cutoffs are continuous throughout an open faithful
base interval. -/
theorem affineTruncatedBkmCurvatureAlong_continuousOn_Ioo
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) {A B : ℝ}
    (hpos : ∀ u ∈ Set.Ioo A B, (σ + u • d).PosDef) (N : ℕ) :
    ContinuousOn (affineTruncatedBkmCurvatureAlong σ d z N)
      (Set.Ioo A B) := by
  rw [isOpen_Ioo.continuousOn_iff]
  intro u hu
  let δ : ℝ := min (u - A) (B - u) / 2
  have hmin : 0 < min (u - A) (B - u) :=
    lt_min (by linarith [hu.1]) (by linarith [hu.2])
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδleft : δ < u - A := by
    have hle := min_le_left (u - A) (B - u)
    dsimp [δ]
    linarith
  have hδright : δ < B - u := by
    have hle := min_le_right (u - A) (B - u)
    dsimp [δ]
    linarith
  have hposIcc : ∀ x ∈ Set.Icc (u - δ) (u + δ),
      (σ + x • d).PosDef := by
    intro x hx
    apply hpos x
    constructor <;> linarith [hx.1, hx.2]
  have hc := affineTruncatedBkmCurvatureAlong_continuousOn
    (z := z) hσ hd hposIcc N
  exact hc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- Local uniform Dini convergence for a fixed Hermitian tangent along an
independent faithful affine base direction. -/
theorem tendstoLocallyUniformlyOn_affineTruncatedBkmCurvatureAlong
    (hσ : σ.IsHermitian) (hd : d.IsHermitian) (hz : z.IsHermitian)
    {A B : ℝ} (hpos : ∀ u ∈ Set.Ioo A B, (σ + u • d).PosDef) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => affineTruncatedBkmCurvatureAlong σ d z N)
      (affineBkmFormAlong hσ hd z) atTop (Set.Ioo A B) := by
  apply Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto
  · intro N
    exact affineTruncatedBkmCurvatureAlong_continuousOn_Ioo
      (z := z) hσ hd hpos N
  · intro u hu
    exact affineTruncatedBkmCurvatureAlong_monotone
      hσ hd hz (hpos u hu)
  · exact affineBkmFormAlong_continuousOn hσ hd hz isOpen_Ioo
      (convex_Ioo A B) hpos
  · intro u hu
    exact tendsto_affineTruncatedBkmCurvatureAlong
      hσ hd hz (hpos u hu)

end QRE
end NCG
