/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.FiniteMeasureL2L6InterpolationExact

/-!
# Hölder wedge estimate for the weak-curvature Palatini passage
(`prop:weak-palatini`, Einstein–SM action closure)

The `L^p` product estimate of the proposition's proof,

  `‖e_h ∧ e_h − e ∧ e‖_{r} ≤ ‖∧‖ ‖e_h − e‖_{2r} (‖e_h‖_{2r} + ‖e‖_{2r})`,

is proved at the level of `MeasureTheory.eLpNorm` for any bounded bilinear map
`w : E →L[ℝ] E →L[ℝ] Biv` (the wedge / internal-dual map `B`) and any exponent
`1 ≤ r < ∞` (`eLpNorm_wedge_sub_le`), from Mathlib's Hölder inequality with the triple
`(2r, 2r, r)` (`holderTriple_two_mul`).

Combined with the `L²`–`L⁶` interpolation of
`Continuum/FiniteMeasureL2L6InterpolationExact.lean` this gives, for `p > 3/2` and
`r = p' = p/(p-1)`, the Palatini form (`eLpNorm_wedge_sub_le_interpolation`):

  `‖B(e_h) − B(e)‖_{p'} ≤ ‖B‖ · ‖e_h − e‖₂^{(2p−3)/(2p)} ‖e_h − e‖₆^{3/(2p)} · (‖e_h‖_{2p'} + ‖e‖_{2p'})`,

which is exactly the interpolation hypothesis `‖coframe_h − coframe‖ ≤ C · lowError^θ`
(`θ = (2p−3)/(2p) > 0`) consumed by
`Gravity/PalatiniWeakStrongLimitExact.lean:curvature_pairing_tendsto_of_coframe_interpolation`
once the `L^{p'}` bivector is read in the Banach space `L^{p'}` and the curvature pairing
against weak-`L^p` curvature is represented there.  That representation (the `Lp`-space
instantiation of the pairing and the weak-space rendering of `R_h ⇀ R`) is what remains.
-/

open MeasureTheory ENNReal

namespace RenewalGeometry.PalatiniWedgeHolder

variable {α E Biv : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Biv] [NormedSpace ℝ Biv]

/-- The Hölder triple `(2r, 2r, r)`: `1/(2r) + 1/(2r) = 1/r`. -/
theorem holderTriple_two_mul (r : ℝ≥0∞) (hr' : r ≠ ∞) :
    HolderTriple (2 * r) (2 * r) r := by
  refine ⟨?_⟩
  rw [ENNReal.mul_inv (Or.inr hr') (Or.inl (by norm_num)), ← add_mul, ENNReal.inv_two_add_inv_two,
    one_mul]

/-- The pointwise decomposition `w f f − w g g = w (f − g) f + w g (f − g)`. -/
theorem wedge_sub_eq (w : E →L[ℝ] E →L[ℝ] Biv) (x y : E) :
    w x x - w y y = w (x - y) x + w y (x - y) := by
  simp only [map_sub, sub_apply]
  abel

/-- **Hölder wedge estimate.**  For `1 ≤ r < ∞`,
`‖w f f − w g g‖_r ≤ ‖w‖ ‖f − g‖_{2r} (‖f‖_{2r} + ‖g‖_{2r})`. -/
theorem eLpNorm_wedge_sub_le (w : E →L[ℝ] E →L[ℝ] Biv) (f g : α → E)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (r : ℝ≥0∞) (hr1 : 1 ≤ r) (hr' : r ≠ ∞) :
    eLpNorm (fun x => w (f x) (f x) - w (g x) (g x)) r μ ≤
      ‖w‖₊ * eLpNorm (f - g) (2 * r) μ * (eLpNorm f (2 * r) μ + eLpNorm g (2 * r) μ) := by
  have hr0 : r ≠ 0 := by
    intro h; rw [h] at hr1; exact absurd hr1 (by simp)
  have : HolderTriple (2 * r) (2 * r) r := holderTriple_two_mul r hr'
  have hfg : AEStronglyMeasurable (f - g) μ := hf.sub hg
  have h1 : AEStronglyMeasurable (fun x => w ((f - g) x) (f x)) μ :=
    w.aestronglyMeasurable_comp₂ hfg hf
  have h2 : AEStronglyMeasurable (fun x => w (g x) ((f - g) x)) μ :=
    w.aestronglyMeasurable_comp₂ hg hfg
  have hdecomp : (fun x => w (f x) (f x) - w (g x) (g x))
      = (fun x => w ((f - g) x) (f x)) + fun x => w (g x) ((f - g) x) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    exact wedge_sub_eq w (f x) (g x)
  have hb1 : eLpNorm (fun x => w ((f - g) x) (f x)) r μ ≤
      ‖w‖₊ * eLpNorm (f - g) (2 * r) μ * eLpNorm f (2 * r) μ :=
    eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm hfg hf (fun x y => w x y) ‖w‖₊
      (Filter.Eventually.of_forall fun x => by
        simpa [mul_assoc] using w.le_opNorm₂ ((f - g) x) (f x))
  have hb2 : eLpNorm (fun x => w (g x) ((f - g) x)) r μ ≤
      ‖w‖₊ * eLpNorm g (2 * r) μ * eLpNorm (f - g) (2 * r) μ :=
    eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm hg hfg (fun x y => w x y) ‖w‖₊
      (Filter.Eventually.of_forall fun x => by
        simpa [mul_assoc] using w.le_opNorm₂ (g x) ((f - g) x))
  calc eLpNorm (fun x => w (f x) (f x) - w (g x) (g x)) r μ
      = eLpNorm ((fun x => w ((f - g) x) (f x)) + fun x => w (g x) ((f - g) x)) r μ := by
        rw [hdecomp]
    _ ≤ eLpNorm (fun x => w ((f - g) x) (f x)) r μ
          + eLpNorm (fun x => w (g x) ((f - g) x)) r μ := eLpNorm_add_le h1 h2 hr1
    _ ≤ ‖w‖₊ * eLpNorm (f - g) (2 * r) μ * eLpNorm f (2 * r) μ
          + ‖w‖₊ * eLpNorm g (2 * r) μ * eLpNorm (f - g) (2 * r) μ := add_le_add hb1 hb2
    _ = ‖w‖₊ * eLpNorm (f - g) (2 * r) μ * (eLpNorm f (2 * r) μ + eLpNorm g (2 * r) μ) := by
        ring

/-- **Palatini form (`prop:weak-palatini`, product estimate).**  For `p > 3/2` and
`p' = p/(p-1)`, the `L^{p'}` wedge error is controlled by the `L²`–`L⁶` interpolation of
the coframe error: with `θ = (2p−3)/(2p) > 0`,
`‖w f f − w g g‖_{p'} ≤ ‖w‖ ‖f − g‖₂^θ ‖f − g‖₆^{3/(2p)} (‖f‖_{2p'} + ‖g‖_{2p'})`
(all norms as `eLpNorm'` with real exponents; `‖·‖_{2p'}` written with the exponent
`2p/(p-1)`). -/
theorem eLpNorm_wedge_sub_le_interpolation (w : E →L[ℝ] E →L[ℝ] Biv) (f g : α → E)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (p : ℝ) (hp : 3 / 2 < p) :
    eLpNorm' (fun x => w (f x) (f x) - w (g x) (g x)) (p / (p - 1)) μ ≤
      ‖w‖₊ * ((eLpNorm' (f - g) 2 μ) ^ ((2 * p - 3) / (2 * p)) *
          (eLpNorm' (f - g) 6 μ) ^ (3 / (2 * p))) *
        (eLpNorm' f (2 * p / (p - 1)) μ + eLpNorm' g (2 * p / (p - 1)) μ) := by
  have hp1 : 1 < p := by linarith
  have hden : 0 < p - 1 := sub_pos.mpr hp1
  have hr_real : 1 ≤ p / (p - 1) := (le_div_iff₀ hden).2 (by linarith)
  set r : ℝ≥0∞ := ENNReal.ofReal (p / (p - 1)) with hr
  have hr1 : 1 ≤ r := by
    rw [hr, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr_real
  have hr0 : r ≠ 0 := by
    intro h; rw [h] at hr1; exact absurd hr1 (by simp)
  have hrtop : r ≠ ∞ := ENNReal.ofReal_ne_top
  have h2r : 2 * r = ENNReal.ofReal (2 * p / (p - 1)) := by
    rw [hr, mul_div_assoc, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have h2r0 : 2 * r ≠ 0 := mul_ne_zero (by norm_num) hr0
  have h2rtop : 2 * r ≠ ∞ := ENNReal.mul_ne_top (by simp) hrtop
  have hrtoReal : r.toReal = p / (p - 1) := by
    rw [hr, ENNReal.toReal_ofReal (by positivity)]
  have h2rtoReal : (2 * r).toReal = 2 * p / (p - 1) := by
    rw [h2r, ENNReal.toReal_ofReal (by positivity)]
  have hmain := eLpNorm_wedge_sub_le w f g hf hg r hr1 hrtop
  rw [eLpNorm_eq_eLpNorm' hr0 hrtop, eLpNorm_eq_eLpNorm' h2r0 h2rtop,
    eLpNorm_eq_eLpNorm' h2r0 h2rtop, eLpNorm_eq_eLpNorm' h2r0 h2rtop,
    hrtoReal, h2rtoReal] at hmain
  have hinterp := RenewalGeometry.FiniteMeasureL2L6Interpolation.palatini_eLpNorm'_interpolation
    (f - g) (hf.sub hg) p hp
  calc eLpNorm' (fun x => w (f x) (f x) - w (g x) (g x)) (p / (p - 1)) μ
      ≤ ‖w‖₊ * eLpNorm' (f - g) (2 * p / (p - 1)) μ *
          (eLpNorm' f (2 * p / (p - 1)) μ + eLpNorm' g (2 * p / (p - 1)) μ) := hmain
    _ ≤ ‖w‖₊ * ((eLpNorm' (f - g) 2 μ) ^ ((2 * p - 3) / (2 * p)) *
          (eLpNorm' (f - g) 6 μ) ^ (3 / (2 * p))) *
          (eLpNorm' f (2 * p / (p - 1)) μ + eLpNorm' g (2 * p / (p - 1)) μ) := by
        gcongr

end RenewalGeometry.PalatiniWedgeHolder
