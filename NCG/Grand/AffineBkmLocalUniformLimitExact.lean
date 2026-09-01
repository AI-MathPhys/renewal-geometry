/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AffineMatrixLogResolventIntegrandExact
import NCG.Grand.BkmMonotonicityExact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UniformSpace.Dini

/-!
# Local uniform convergence of affine BKM resolvent curvatures

The finite resolvent cutoffs are increasing because their integrand is
nonnegative.  Joint convexity of the BKM form makes the faithful affine limit
continuous.  Dini's theorem then upgrades pointwise cutoff convergence to
uniform convergence on compact faithful subintervals.
-/

open Matrix Finset Filter Topology MeasureTheory intervalIntegral
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ v : Matrix n n ℂ}

/-- The BKM curvature along a Hermitian affine matrix path. -/
noncomputable def affineBkmForm (hσ : σ.IsHermitian)
    (hv : v.IsHermitian) (u : ℝ) : ℝ :=
  bkmForm (affineMatrix_isHermitian hσ hv u) v

/-- Joint convexity of `bkmForm` specializes to convexity along every
faithful affine base path with fixed tangent. -/
theorem affineBkmForm_convexOn (hσ : σ.IsHermitian)
    (hv : v.IsHermitian) {U : Set ℝ} (hU : Convex ℝ U)
    (hpos : ∀ u ∈ U, (σ + u • v).PosDef) :
    ConvexOn ℝ U (affineBkmForm hσ hv) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy a b ha hb hab
  have hbval : b = 1 - a := by linarith
  subst b
  have hxy : a • x + (1 - a) • y ∈ U := hU hx hy ha hb hab
  let lam : Fin 2 → ℝ := ![a, 1 - a]
  let σs : Fin 2 → Matrix n n ℂ := ![σ + x • v, σ + y • v]
  let vs : Fin 2 → Matrix n n ℂ := ![v, v]
  have hσj : ∀ j, (σs j).PosDef := by
    intro j
    fin_cases j
    · exact hpos x hx
    · exact hpos y hy
  have hbase : (∑ j, lam j • σs j) =
      σ + (a • x + (1 - a) • y) • v := by
    simp only [lam, σs, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    module
  have hbar : (∑ j, lam j • σs j).PosDef := by
    rw [hbase]
    exact hpos (a • x + (1 - a) • y) hxy
  have hconv := bkmForm_convex (n := n) (lam := lam)
    (σs := σs) (vs := vs) (fun j => by
      fin_cases j <;> assumption) hσj hbar
  have hvsum : (∑ j, lam j • vs j) = v := by
    simp only [lam, vs, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    module
  have hleft : bkmForm hbar.1 (∑ j, lam j • vs j) =
      affineBkmForm hσ hv (a • x + (1 - a) • y) := by
    unfold affineBkmForm
    exact Petz.bkmForm_congr hbase hvsum hbar.1
      (affineMatrix_isHermitian hσ hv (a • x + (1 - a) • y))
  have hxform : bkmForm (hσj 0).1 (vs 0) = affineBkmForm hσ hv x := by
    unfold affineBkmForm
    apply Petz.bkmForm_congr
    · rfl
    · rfl
  have hyform : bkmForm (hσj 1).1 (vs 1) = affineBkmForm hσ hv y := by
    unfold affineBkmForm
    apply Petz.bkmForm_congr
    · rfl
    · rfl
  have hright : (∑ j, lam j * bkmForm (hσj j).1 (vs j)) =
      a * affineBkmForm hσ hv x + (1 - a) * affineBkmForm hσ hv y := by
    rw [Fin.sum_univ_two]
    change a * bkmForm (hσj 0).1 (vs 0) +
      (1 - a) * bkmForm (hσj 1).1 (vs 1) = _
    rw [hxform, hyform]
  rw [hleft, hright] at hconv
  simpa only [smul_eq_mul] using hconv

/-- The affine BKM curvature is continuous on every open faithful interval. -/
theorem affineBkmForm_continuousOn (hσ : σ.IsHermitian)
    (hv : v.IsHermitian) {U : Set ℝ} (hU : IsOpen U)
    (hUc : Convex ℝ U) (hpos : ∀ u ∈ U, (σ + u • v).PosDef) :
    ContinuousOn (affineBkmForm hσ hv) U :=
  (affineBkmForm_convexOn hσ hv hUc hpos).continuousOn hU

/-- The proof-independent finite resolvent cutoff of the affine BKM
curvature.  Using the raw ring inverse makes this a genuine function of the
base parameter, independently of any positivity proof. -/
noncomputable def affineTruncatedBkmCurvature
    (σ v : Matrix n n ℂ) (N : ℕ) (u : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..(N : ℝ), affineRawSForm σ v (u, s)

/-- On a faithful affine point, the proof-independent cutoff is the spectral
truncated resolvent curvature. -/
theorem affineTruncatedBkmCurvature_eq_truncated
    (hσ : σ.IsHermitian) (hv : v.IsHermitian) {N : ℕ} {u : ℝ}
    (hu : (σ + u • v).PosDef) :
    affineTruncatedBkmCurvature σ v N u =
      truncatedResolventCurvature
        (affineMatrix_isHermitian hσ hv u) v (N : ℝ) := by
  unfold affineTruncatedBkmCurvature truncatedResolventCurvature
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : 0 ≤ s := by
    rw [Set.uIcc_of_le (Nat.cast_nonneg N)] at hs
    exact hs.1
  exact affineRawSForm_eq_affineSForm hσ hv hu hs'

set_option maxHeartbeats 1600000 in
-- Dominated convergence over the proof-independent matrix resolvent requires
-- substantial elaboration through the finite-dimensional matrix instances.
/-- Each finite affine curvature cutoff is continuous on every compact
faithful interval. -/
theorem affineTruncatedBkmCurvature_continuousOn
    (hσ : σ.IsHermitian) (hv : v.IsHermitian) {a b : ℝ}
    (hpos : ∀ u ∈ Set.Icc a b, (σ + u • v).PosDef) (N : ℕ) :
    ContinuousOn (affineTruncatedBkmCurvature σ v N) (Set.Icc a b) := by
  let R : ℝ := (N : ℝ)
  have hR : 0 ≤ R := Nat.cast_nonneg N
  have hraw := affineRawSForm_continuousOn_rect
    (σ := σ) (v := v) (R := R) hpos
  obtain ⟨C, hC⟩ := exists_affineSForm_bound_rect hσ hv
    (R := R) hpos
  intro u hu
  have hmeas : ∀ᶠ x in 𝓝[Set.Icc a b] u,
      AEStronglyMeasurable (fun s : ℝ => affineRawSForm σ v (x, s))
        (volume.restrict (Set.uIoc (0 : ℝ) R)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hslice : ContinuousOn (fun s : ℝ => affineRawSForm σ v (x, s))
        (Set.Icc (0 : ℝ) R) := by
      intro s hs
      have hpair : ContinuousWithinAt (fun y : ℝ => (x, y))
          (Set.Icc (0 : ℝ) R) s :=
        continuousWithinAt_const.prodMk continuousWithinAt_id
      exact (hraw (x, s) ⟨hx, hs⟩).comp hpair
        (fun y hy => ⟨hx, hy⟩)
    have hint : IntervalIntegrable
        (fun s : ℝ => affineRawSForm σ v (x, s)) volume 0 R := by
      apply ContinuousOn.intervalIntegrable
      rwa [Set.uIcc_of_le hR]
    simpa only [Set.uIoc_of_le hR] using hint.1.aestronglyMeasurable
  have hbound : ∀ᶠ x in 𝓝[Set.Icc a b] u,
      ∀ᵐ s ∂volume, s ∈ Set.uIoc (0 : ℝ) R →
        ‖affineRawSForm σ v (x, s)‖ ≤ C := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    filter_upwards with s
    intro hs
    rw [Set.uIoc_of_le hR] at hs
    have hs' : s ∈ Set.Icc (0 : ℝ) R := ⟨hs.1.le, hs.2⟩
    rw [affineRawSForm_eq_affineSForm hσ hv (hpos x hx) hs'.1]
    simpa only [Real.norm_eq_abs] using hC s hs' x hx
  have hcont : ∀ᵐ s ∂volume, s ∈ Set.uIoc (0 : ℝ) R →
      ContinuousWithinAt (fun x : ℝ => affineRawSForm σ v (x, s))
        (Set.Icc a b) u := by
    filter_upwards with s
    intro hs
    rw [Set.uIoc_of_le hR] at hs
    have hs' : s ∈ Set.Icc (0 : ℝ) R := ⟨hs.1.le, hs.2⟩
    have hpair : ContinuousOn (fun x : ℝ => (x, s)) (Set.Icc a b) :=
      continuousOn_id.prodMk continuousOn_const
    have hslice := hraw.comp hpair (fun x hx => ⟨hx, hs'⟩)
    change ContinuousWithinAt
      (affineRawSForm σ v ∘ fun x : ℝ => (x, s)) (Set.Icc a b) u
    exact hslice u hu
  have hmain := intervalIntegral.continuousWithinAt_of_dominated_interval
    (F := fun x s => affineRawSForm σ v (x, s))
    (bound := fun _ => C) (a := (0 : ℝ)) (b := R)
    (s := Set.Icc a b) hmeas hbound intervalIntegrable_const hcont
  change ContinuousWithinAt
    (fun x : ℝ => ∫ s in (0 : ℝ)..(N : ℝ),
      affineRawSForm σ v (x, s)) (Set.Icc a b) u
  simpa only [R] using hmain

/-- At every faithful affine point, the finite curvature cutoffs increase
with the natural-number cutoff. -/
theorem affineTruncatedBkmCurvature_monotone
    (hσ : σ.IsHermitian) (hv : v.IsHermitian) {u : ℝ}
    (hu : (σ + u • v).PosDef) :
    Monotone (fun N : ℕ => affineTruncatedBkmCurvature σ v N u) := by
  intro N M hNM
  change affineTruncatedBkmCurvature σ v N u ≤
    affineTruncatedBkmCurvature σ v M u
  rw [affineTruncatedBkmCurvature_eq_truncated hσ hv hu,
    affineTruncatedBkmCurvature_eq_truncated hσ hv hu]
  unfold truncatedResolventCurvature
  let hu' : (σ + u • v).PosDef :=
    ⟨affineMatrix_isHermitian hσ hv u, hu.2⟩
  apply intervalIntegral.integral_mono_interval
    (c := (0 : ℝ)) (d := (M : ℝ)) le_rfl (Nat.cast_nonneg N)
  · exact_mod_cast hNM
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact sForm_nonneg hu'.posSemidef hv hs.1
  · exact sForm_intervalIntegrable hu' hv (Nat.cast_nonneg M)

/-- At a faithful affine point, natural-number resolvent cutoffs converge to
the exact BKM curvature. -/
theorem tendsto_affineTruncatedBkmCurvature
    (hσ : σ.IsHermitian) (hv : v.IsHermitian) {u : ℝ}
    (hu : (σ + u • v).PosDef) :
    Tendsto (fun N : ℕ => affineTruncatedBkmCurvature σ v N u) atTop
      (𝓝 (affineBkmForm hσ hv u)) := by
  let hu' : (σ + u • v).PosDef :=
    ⟨affineMatrix_isHermitian hσ hv u, hu.2⟩
  have hlim := (tendsto_truncatedResolventCurvature hu' hv).comp
    tendsto_natCast_atTop_atTop
  apply hlim.congr'
  filter_upwards with N
  rw [affineTruncatedBkmCurvature_eq_truncated hσ hv hu]
  rfl

/-- **Dini convergence for affine BKM curvature.**  On every compact
subinterval strictly contained in a faithful open affine interval, the
finite resolvent curvatures converge uniformly to the exact BKM form. -/
theorem tendstoUniformlyOn_affineTruncatedBkmCurvature
    (hσ : σ.IsHermitian) (hv : v.IsHermitian)
    {A a b B : ℝ} (hAa : A < a) (_hab : a ≤ b) (hbB : b < B)
    (hpos : ∀ u ∈ Set.Ioo A B, (σ + u • v).PosDef) :
    TendstoUniformlyOn
      (fun N : ℕ => affineTruncatedBkmCurvature σ v N)
      (affineBkmForm hσ hv) atTop (Set.Icc a b) := by
  have hposIcc : ∀ u ∈ Set.Icc a b, (σ + u • v).PosDef := by
    intro u hu
    exact hpos u ⟨hAa.trans_le hu.1, hu.2.trans_lt hbB⟩
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
  · intro N
    exact affineTruncatedBkmCurvature_continuousOn hσ hv hposIcc N
  · intro u hu
    exact affineTruncatedBkmCurvature_monotone hσ hv (hposIcc u hu)
  · exact (affineBkmForm_continuousOn hσ hv isOpen_Ioo (convex_Ioo A B) hpos).mono
      (fun u hu => ⟨hAa.trans_le hu.1, hu.2.trans_lt hbB⟩)
  · intro u hu
    exact tendsto_affineTruncatedBkmCurvature hσ hv (hposIcc u hu)

/-- Every finite curvature cutoff is continuous throughout an open faithful
affine interval. -/
theorem affineTruncatedBkmCurvature_continuousOn_Ioo
    (hσ : σ.IsHermitian) (hv : v.IsHermitian) {A B : ℝ}
    (hpos : ∀ u ∈ Set.Ioo A B, (σ + u • v).PosDef) (N : ℕ) :
    ContinuousOn (affineTruncatedBkmCurvature σ v N) (Set.Ioo A B) := by
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
      (σ + x • v).PosDef := by
    intro x hx
    apply hpos x
    constructor <;> linarith [hx.1, hx.2]
  have hc := affineTruncatedBkmCurvature_continuousOn hσ hv hposIcc N
  exact hc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- The cutoff curvatures converge locally uniformly throughout any open
faithful affine interval. -/
theorem tendstoLocallyUniformlyOn_affineTruncatedBkmCurvature
    (hσ : σ.IsHermitian) (hv : v.IsHermitian) {A B : ℝ}
    (hpos : ∀ u ∈ Set.Ioo A B, (σ + u • v).PosDef) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => affineTruncatedBkmCurvature σ v N)
      (affineBkmForm hσ hv) atTop (Set.Ioo A B) := by
  apply Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto
  · intro N
    exact affineTruncatedBkmCurvature_continuousOn_Ioo hσ hv hpos N
  · intro u hu
    exact affineTruncatedBkmCurvature_monotone hσ hv (hpos u hu)
  · exact affineBkmForm_continuousOn hσ hv isOpen_Ioo (convex_Ioo A B) hpos
  · intro u hu
    exact tendsto_affineTruncatedBkmCurvature hσ hv (hpos u hu)

end QRE
end NCG
