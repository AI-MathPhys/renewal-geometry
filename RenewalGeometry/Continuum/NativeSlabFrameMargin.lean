/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.AdaptedFrameOfMetric

/-!
# A globally smooth adapted frame agreeing with `frU` on a margin of the Lorentzian chart

Generic infrastructure for the slab theory data of a native model (bridge step P2 of
`thm:native-closure`, Einstein–Standard-Model action-closure manuscript).

The adapted frame `ActualJetFrame.frU g⁻¹` (lapse, shift, Cholesky factor of the induced spatial
inverse metric) is real-analytic on the open Lorentzian foliated chart `IsLorChart`, but it is
built from square roots and divisions and is not smooth on all of `ℝ^{4×4}`.  The theory data
`ActualJetSystem.SMData` of the slab model require globally smooth source functions
(`ActualJetSmooth.SMSmooth`).  We therefore replace every square root `√t` by `√(smax δ t)` and
every division by `g^{00}` by a division by `-smax δ (-g^{00})`, where `smax δ` is a smooth
function with `smax δ t ≥ δ/2` and `smax δ t = t` for `t ≥ δ`.

## Main results

* `smax`, `smax_ge`, `smax_eq`, `contDiff_smax` — the smooth lower cut-off.
* `frUs` — the smoothed frame; **`contDiff_frUs`**: globally `C^∞` for `δ > 0`.
* `Margin δ g⁻¹` — the four chart radicands are `≥ δ`; **`frUs_eq_frU`**: on the margin the
  smoothed frame is the adapted frame.
* **`exists_margin`** — every compact subset of the chart lies in some margin `δ > 0`.
-/

open Finset Set
open scoped ContDiff

namespace RenewalGeometry.SlabData

open ActualJetFrame

noncomputable section

/-! ### The smooth lower cut-off -/

/-- A smooth function with `smax δ t ≥ δ/2` everywhere and `smax δ t = t` for `t ≥ δ`. -/
def smax (δ t : ℝ) : ℝ := δ / 2 + (t - δ / 2) * Real.smoothTransition ((t - δ / 2) / (δ / 2))

theorem smax_ge {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : δ / 2 ≤ smax δ t := by
  unfold smax
  rcases le_or_gt t (δ / 2) with h | h
  · have : (t - δ / 2) / (δ / 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    rw [Real.smoothTransition.zero_of_nonpos this]; simp
  · have h1 := Real.smoothTransition.nonneg ((t - δ / 2) / (δ / 2))
    nlinarith

theorem smax_pos {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 < smax δ t :=
  lt_of_lt_of_le (by linarith) (smax_ge hδ t)

theorem smax_eq {δ t : ℝ} (hδ : 0 < δ) (ht : δ ≤ t) : smax δ t = t := by
  unfold smax
  have : 1 ≤ (t - δ / 2) / (δ / 2) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  rw [Real.smoothTransition.one_of_one_le this]; ring

theorem contDiff_smax (δ : ℝ) : ContDiff ℝ ∞ (smax δ) := by
  unfold smax
  have : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition ((t - δ / 2) / (δ / 2))) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  fun_prop

/-- The smoothed square root `√(smax δ t)`. -/
def ssqrt (δ t : ℝ) : ℝ := Real.sqrt (smax δ t)

theorem ssqrt_pos {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 < ssqrt δ t :=
  Real.sqrt_pos.mpr (smax_pos hδ t)

theorem contDiff_ssqrt {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ ∞ (ssqrt δ) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  exact (Real.contDiffAt_sqrt (smax_pos hδ t).ne').comp t (contDiff_smax δ).contDiffAt

theorem ssqrt_eq {δ t : ℝ} (hδ : 0 < δ) (ht : δ ≤ t) : ssqrt δ t = Real.sqrt t := by
  rw [ssqrt, smax_eq hδ ht]

/-! ### The smoothed frame -/

/-- The smoothed reciprocal of `g^{00}`. -/
def inv00 (δ : ℝ) (gi : IMet) : ℝ := (-smax δ (-gi 0 0))⁻¹

/-- The smoothed induced spatial inverse metric. -/
def hInvs (δ : ℝ) (gi : IMet) (i j : Fin 3) : ℝ :=
  gi i.succ j.succ - gi 0 i.succ * gi 0 j.succ * inv00 δ gi

def L00s (δ : ℝ) (gi : IMet) : ℝ := ssqrt δ (hInvs δ gi 0 0)
def L10s (δ : ℝ) (gi : IMet) : ℝ := hInvs δ gi 1 0 / L00s δ gi
def L20s (δ : ℝ) (gi : IMet) : ℝ := hInvs δ gi 2 0 / L00s δ gi
def L11s (δ : ℝ) (gi : IMet) : ℝ := ssqrt δ (hInvs δ gi 1 1 - L10s δ gi ^ 2)
def L21s (δ : ℝ) (gi : IMet) : ℝ := (hInvs δ gi 2 1 - L20s δ gi * L10s δ gi) / L11s δ gi
def L22s (δ : ℝ) (gi : IMet) : ℝ := ssqrt δ (hInvs δ gi 2 2 - L20s δ gi ^ 2 - L21s δ gi ^ 2)

/-- The smoothed Cholesky matrix. -/
def Lmats (δ : ℝ) (gi : IMet) : Fin 3 → Fin 3 → ℝ :=
  ![![L00s δ gi, 0, 0], ![L10s δ gi, L11s δ gi, 0], ![L20s δ gi, L21s δ gi, L22s δ gi]]

/-- The smoothed lapse. -/
def lapses (δ : ℝ) (gi : IMet) : ℝ := (ssqrt δ (-gi 0 0))⁻¹

/-- The smoothed shift. -/
def shifts (δ : ℝ) (gi : IMet) (j : Fin 3) : ℝ := -(gi 0 j.succ) * inv00 δ gi

/-- **The smoothed adapted frame** (the formulas of `frU` with the smoothed operations). -/
def frUs (δ : ℝ) (gi : IMet) (A μ : Fin 4) : ℝ :=
  Fin.cases (Fin.cases (lapses δ gi)⁻¹ (fun j => -(shifts δ gi j / lapses δ gi)) μ)
    (fun a => Fin.cases 0 (fun j => Lmats δ gi j a) μ) A

/-- **The margin** of the Lorentzian chart: the four chart radicands are at least `δ`. -/
def Margin (δ : ℝ) (gi : IMet) : Prop :=
  δ ≤ -gi 0 0 ∧ δ ≤ hInv gi 0 0 ∧ δ ≤ hInv gi 1 1 - L10 gi ^ 2 ∧
    δ ≤ hInv gi 2 2 - L20 gi ^ 2 - L21 gi ^ 2

theorem Margin.isLorChart {δ : ℝ} (hδ : 0 < δ) {gi : IMet} (h : Margin δ gi) : IsLorChart gi :=
  ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2.1], by linarith [h.2.2.2]⟩

theorem inv00_eq {δ : ℝ} (hδ : 0 < δ) {gi : IMet} (h : Margin δ gi) : inv00 δ gi = (gi 0 0)⁻¹ := by
  unfold inv00; rw [smax_eq hδ h.1, neg_neg]

theorem hInvs_eq {δ : ℝ} (hδ : 0 < δ) {gi : IMet} (h : Margin δ gi) (i j : Fin 3) :
    hInvs δ gi i j = hInv gi i j := by
  unfold hInvs hInv; rw [inv00_eq hδ h, div_eq_mul_inv]

theorem L00s_eq {δ : ℝ} (hδ : 0 < δ) {gi : IMet} (h : Margin δ gi) : L00s δ gi = L00 gi := by
  unfold L00s L00; rw [hInvs_eq hδ h, ssqrt_eq hδ h.2.1]

theorem L10s_eq {δ : ℝ} (hδ : 0 < δ) {gi : IMet} (h : Margin δ gi) : L10s δ gi = L10 gi := by
  unfold L10s L10; rw [hInvs_eq hδ h, L00s_eq hδ h]

theorem L20s_eq {δ : ℝ} (hδ : 0 < δ) {gi : IMet} (h : Margin δ gi) : L20s δ gi = L20 gi := by
  unfold L20s L20; rw [hInvs_eq hδ h, L00s_eq hδ h]

theorem L11s_eq {δ : ℝ} (hδ : 0 < δ) {gi : IMet} (h : Margin δ gi) : L11s δ gi = L11 gi := by
  unfold L11s L11; rw [hInvs_eq hδ h, L10s_eq hδ h, ssqrt_eq hδ h.2.2.1]

theorem L21s_eq {δ : ℝ} (hδ : 0 < δ) {gi : IMet} (h : Margin δ gi) : L21s δ gi = L21 gi := by
  unfold L21s L21; rw [hInvs_eq hδ h, L20s_eq hδ h, L10s_eq hδ h, L11s_eq hδ h]

theorem L22s_eq {δ : ℝ} (hδ : 0 < δ) {gi : IMet} (h : Margin δ gi) : L22s δ gi = L22 gi := by
  unfold L22s L22; rw [hInvs_eq hδ h, L20s_eq hδ h, L21s_eq hδ h, ssqrt_eq hδ h.2.2.2]

theorem Lmats_eq {δ : ℝ} (hδ : 0 < δ) {gi : IMet} (h : Margin δ gi) : Lmats δ gi = Lmat gi := by
  unfold Lmats Lmat
  rw [L00s_eq hδ h, L10s_eq hδ h, L20s_eq hδ h, L11s_eq hδ h, L21s_eq hδ h, L22s_eq hδ h]

theorem lapses_eq {δ : ℝ} (hδ : 0 < δ) {gi : IMet} (h : Margin δ gi) : lapses δ gi = lapse gi := by
  unfold lapses lapse; rw [ssqrt_eq hδ h.1]

theorem shifts_eq {δ : ℝ} (hδ : 0 < δ) {gi : IMet} (h : Margin δ gi) (j : Fin 3) :
    shifts δ gi j = shift gi j := by
  unfold shifts shift; rw [inv00_eq hδ h, div_eq_mul_inv]

/-- **On the margin the smoothed frame is the adapted frame.** -/
theorem frUs_eq_frU {δ : ℝ} (hδ : 0 < δ) {gi : IMet} (h : Margin δ gi) (A μ : Fin 4) :
    frUs δ gi A μ = frU gi A μ := by
  unfold frUs frU
  simp only [Lmats_eq hδ h, lapses_eq hδ h, shifts_eq hδ h]

/-! ### Smoothness -/

section Smooth

variable {δ : ℝ} (hδ : 0 < δ)
include hδ

theorem contDiff_inv00 : ContDiff ℝ ∞ (inv00 δ) := by
  unfold inv00
  have h1 : ContDiff ℝ ∞ (fun gi : IMet => smax δ (-gi 0 0)) :=
    (contDiff_smax δ).comp (by fun_prop)
  exact h1.neg.inv fun gi => by have := smax_pos hδ (-gi 0 0); linarith

theorem contDiff_hInvs (i j : Fin 3) : ContDiff ℝ ∞ (fun gi => hInvs δ gi i j) := by
  unfold hInvs
  have := contDiff_inv00 hδ
  fun_prop

theorem contDiff_ssqrt_comp {f : IMet → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun gi => ssqrt δ (f gi)) := (contDiff_ssqrt hδ).comp hf

theorem contDiff_L00s : ContDiff ℝ ∞ (L00s δ) :=
  contDiff_ssqrt_comp hδ (contDiff_hInvs hδ 0 0)

theorem contDiff_L10s : ContDiff ℝ ∞ (L10s δ) :=
  (contDiff_hInvs hδ 1 0).div (contDiff_L00s hδ) fun _ => (ssqrt_pos hδ _).ne'

theorem contDiff_L20s : ContDiff ℝ ∞ (L20s δ) :=
  (contDiff_hInvs hδ 2 0).div (contDiff_L00s hδ) fun _ => (ssqrt_pos hδ _).ne'

theorem contDiff_L11s : ContDiff ℝ ∞ (L11s δ) :=
  contDiff_ssqrt_comp hδ ((contDiff_hInvs hδ 1 1).sub ((contDiff_L10s hδ).pow 2))

theorem contDiff_L21s : ContDiff ℝ ∞ (L21s δ) :=
  ((contDiff_hInvs hδ 2 1).sub ((contDiff_L20s hδ).mul (contDiff_L10s hδ))).div
    (contDiff_L11s hδ) fun _ => (ssqrt_pos hδ _).ne'

theorem contDiff_L22s : ContDiff ℝ ∞ (L22s δ) :=
  contDiff_ssqrt_comp hδ (((contDiff_hInvs hδ 2 2).sub ((contDiff_L20s hδ).pow 2)).sub
    ((contDiff_L21s hδ).pow 2))

theorem contDiff_Lmats (j a : Fin 3) : ContDiff ℝ ∞ (fun gi => Lmats δ gi j a) := by
  fin_cases j <;> fin_cases a <;> simp only [Lmats] <;>
    first
    | exact contDiff_const
    | exact contDiff_L00s hδ
    | exact contDiff_L10s hδ
    | exact contDiff_L20s hδ
    | exact contDiff_L11s hδ
    | exact contDiff_L21s hδ
    | exact contDiff_L22s hδ

theorem contDiff_lapses : ContDiff ℝ ∞ (lapses δ) :=
  (contDiff_ssqrt_comp hδ (f := fun gi : IMet => -gi 0 0) (by fun_prop)).inv
    fun _ => (ssqrt_pos hδ _).ne'

theorem lapses_pos (gi : IMet) : 0 < lapses δ gi := inv_pos.mpr (ssqrt_pos hδ _)

theorem contDiff_shifts (j : Fin 3) : ContDiff ℝ ∞ (fun gi => shifts δ gi j) := by
  unfold shifts
  have := contDiff_inv00 hδ
  fun_prop

/-- **The smoothed frame is globally smooth.** -/
theorem contDiff_frUs (A μ : Fin 4) : ContDiff ℝ ∞ (fun gi => frUs δ gi A μ) := by
  have hN := contDiff_lapses hδ
  have hN0 : ∀ gi, lapses δ gi ≠ 0 := fun gi => (lapses_pos hδ gi).ne'
  induction A using Fin.cases with
  | zero =>
    induction μ using Fin.cases with
    | zero => exact hN.inv hN0
    | succ j => exact ((contDiff_shifts hδ j).div hN hN0).neg
  | succ a =>
    induction μ using Fin.cases with
    | zero => exact contDiff_const
    | succ j => exact contDiff_Lmats hδ j a

end Smooth

/-! ### Compact subsets of the chart lie in a margin -/

/-- The smallest chart radicand. -/
def radMin (gi : IMet) : ℝ :=
  min (min (-gi 0 0) (hInv gi 0 0)) (min (hInv gi 1 1 - L10 gi ^ 2)
    (hInv gi 2 2 - L20 gi ^ 2 - L21 gi ^ 2))

theorem continuousAt_radMin {gi : IMet} (h : IsLorChart gi) : ContinuousAt radMin gi := by
  have hc : Continuous (fun gi : IMet => gi 0 0) :=
    (continuous_apply (0 : Fin 4)).comp (continuous_apply (0 : Fin 4))
  have hc00 : ContinuousAt (fun gi : IMet => -gi 0 0) gi := hc.neg.continuousAt
  have hc0 : ContinuousAt (fun gi : IMet => hInv gi 0 0) gi :=
    (contDiffAt_hInv 0 0 h.1.ne).continuousAt
  have hc1 : ContinuousAt (fun gi : IMet => hInv gi 1 1 - L10 gi ^ 2) gi :=
    ((contDiffAt_hInv 1 1 h.1.ne).sub ((contDiffAt_L10 h).pow 2)).continuousAt
  have hc2 : ContinuousAt (fun gi : IMet => hInv gi 2 2 - L20 gi ^ 2 - L21 gi ^ 2) gi :=
    (((contDiffAt_hInv 2 2 h.1.ne).sub ((contDiffAt_L20 h).pow 2)).sub
      ((contDiffAt_L21 h).pow 2)).continuousAt
  exact (hc00.min hc0).min (hc1.min hc2)

theorem radMin_pos {gi : IMet} (h : IsLorChart gi) : 0 < radMin gi := by
  unfold radMin
  have := h.1; have := h.2.1; have := h.2.2.1; have := h.2.2.2
  simp only [lt_min_iff]
  refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem margin_of_radMin {δ : ℝ} {gi : IMet} (h : δ ≤ radMin gi) : Margin δ gi := by
  unfold radMin at h
  simp only [le_min_iff] at h
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

/-- **Every compact subset of the Lorentzian chart lies in a margin.** -/
theorem exists_margin {Kg : Set IMet} (hK : IsCompact Kg) (hchart : ∀ gi ∈ Kg, IsLorChart gi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ gi ∈ Kg, Margin δ gi := by
  rcases Kg.eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun gi hg => by simp [he] at hg⟩
  have hcont : ContinuousOn radMin Kg := fun gi hg =>
    (continuousAt_radMin (hchart gi hg)).continuousWithinAt
  obtain ⟨g0, hg0, hmin⟩ := hK.exists_isMinOn hne hcont
  exact ⟨radMin g0, radMin_pos (hchart g0 hg0), fun gi hg => margin_of_radMin (hmin hg)⟩

end

end RenewalGeometry.SlabData
