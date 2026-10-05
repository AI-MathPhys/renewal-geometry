/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ActualJetWriterRows

/-!
# The adapted frame as a real-analytic function of the metric (`prop:actual-jet-writer`)

Einstein–Standard-Model action-closure manuscript, `prop:actual-jet-writer` (open clause (c) of
the ledger note: "the fixed smooth frame choice as a function of the metric, so that the
frame-derivative jets and the coefficient maps are functions of the actual-jet state").

On the Lorentzian foliated chart (inverse metric with `g^{00} < 0` and positive-definite induced
spatial inverse metric `h^{ij} = g^{ij} - g^{0i}g^{0j}/g^{00}`) the adapted frame
`e_0 = N⁻¹(∂_t - βʲ∂_j)`, `e_a = e_aʲ∂_j` is fixed by
* lapse `N = (-g^{00})^{-1/2}`, shift `βʲ = -g^{0j}/g^{00}`;
* spatial frame `e_aʲ = L_{ja}` with `L` the Cholesky factor of `h` (`L Lᵀ = h`, `L` lower
  triangular with positive diagonal), given by explicit square-root formulas.

## Main results

* `IsLorChart`, `isOpen_isLorChart`: the open chart (leading-minor radicands positive).
* **`frameOf_adapted`**: the frame is adapted to (orthonormal for) the inverse metric,
  `g^{μν} = -e_0^μe_0^ν + Σ_a e_a^μe_a^ν` — `ActualJetWriter.AdaptedFrame.IsAdapted`.
* **`contDiffAt_frU`**: every frame component `e_A{}^μ` is a real-analytic (`C^ω`) function of
  the inverse metric on the chart; hence (`frameJet`) the frame-derivative jets
  `∂_γe_A{}^μ = D(e_A{}^μ)(g^{-1})[∂_γg^{-1}]` are determined by the metric 1-jet.
* `minkInv_isLorChart`, `frameOf_minkInv`: non-vacuity (Minkowski, flat frame).
-/

open Finset
open scoped ContDiff

namespace RenewalGeometry.ActualJetFrame

open ActualJetWriter

noncomputable section

set_option linter.unusedSectionVars false

/-- Inverse metrics (components `g^{μν}`). -/
abbrev IMet := Fin 4 → Fin 4 → ℝ

/-- The induced spatial inverse metric `h^{ij} = g^{ij} - g^{0i}g^{0j}/g^{00}`. -/
def hInv (gi : IMet) (i j : Fin 3) : ℝ := gi i.succ j.succ - gi 0 i.succ * gi 0 j.succ / gi 0 0

/-- Cholesky entries of `h` (`L Lᵀ = h`). -/
def L00 (gi : IMet) : ℝ := Real.sqrt (hInv gi 0 0)
def L10 (gi : IMet) : ℝ := hInv gi 1 0 / L00 gi
def L20 (gi : IMet) : ℝ := hInv gi 2 0 / L00 gi
def L11 (gi : IMet) : ℝ := Real.sqrt (hInv gi 1 1 - L10 gi ^ 2)
def L21 (gi : IMet) : ℝ := (hInv gi 2 1 - L20 gi * L10 gi) / L11 gi
def L22 (gi : IMet) : ℝ := Real.sqrt (hInv gi 2 2 - L20 gi ^ 2 - L21 gi ^ 2)

/-- The Cholesky factor as a matrix (`L j a`, lower triangular). -/
def Lmat (gi : IMet) : Fin 3 → Fin 3 → ℝ :=
  ![![L00 gi, 0, 0], ![L10 gi, L11 gi, 0], ![L20 gi, L21 gi, L22 gi]]

/-- The Lorentzian foliated chart: `g^{00} < 0` and the three Cholesky radicands positive. -/
def IsLorChart (gi : IMet) : Prop :=
  gi 0 0 < 0 ∧ 0 < hInv gi 0 0 ∧ 0 < hInv gi 1 1 - L10 gi ^ 2 ∧
    0 < hInv gi 2 2 - L20 gi ^ 2 - L21 gi ^ 2

/-- The lapse `N = (-g^{00})^{-1/2}`. -/
def lapse (gi : IMet) : ℝ := (Real.sqrt (-gi 0 0))⁻¹

/-- The shift `βʲ = -g^{0j}/g^{00}`. -/
def shift (gi : IMet) (j : Fin 3) : ℝ := -(gi 0 j.succ) / gi 0 0

theorem lapse_pos {gi : IMet} (h : IsLorChart gi) : 0 < lapse gi := by
  unfold lapse
  have : 0 < -gi 0 0 := by linarith [h.1]
  positivity

/-- The adapted frame of a metric on the chart: `e_aʲ = L_{ja}`. -/
def frameOf (gi : IMet) (h : IsLorChart gi) : AdaptedFrame :=
  ⟨lapse gi, shift gi, fun a j => Lmat gi j a, lapse_pos h⟩

/-- The frame components as a total function of the inverse metric (the formulas of `frameOf`,
used for smoothness and derivative jets). -/
def frU (gi : IMet) (A μ : Fin 4) : ℝ :=
  Fin.cases (Fin.cases (lapse gi)⁻¹ (fun j => -(shift gi j / lapse gi)) μ)
    (fun a => Fin.cases 0 (fun j => Lmat gi j a) μ) A

theorem frU_eq {gi : IMet} (h : IsLorChart gi) (A μ : Fin 4) :
    frU gi A μ = (frameOf gi h).fr A μ := rfl

/-! ### The Cholesky identity -/

theorem L00_sq {gi : IMet} (h : IsLorChart gi) : L00 gi ^ 2 = hInv gi 0 0 :=
  Real.sq_sqrt h.2.1.le

theorem L11_sq {gi : IMet} (h : IsLorChart gi) : L11 gi ^ 2 = hInv gi 1 1 - L10 gi ^ 2 :=
  Real.sq_sqrt h.2.2.1.le

theorem L22_sq {gi : IMet} (h : IsLorChart gi) :
    L22 gi ^ 2 = hInv gi 2 2 - L20 gi ^ 2 - L21 gi ^ 2 :=
  Real.sq_sqrt h.2.2.2.le

theorem L00_pos {gi : IMet} (h : IsLorChart gi) : 0 < L00 gi := Real.sqrt_pos.mpr h.2.1

theorem L11_pos {gi : IMet} (h : IsLorChart gi) : 0 < L11 gi := Real.sqrt_pos.mpr h.2.2.1

theorem hInv_symm {gi : IMet} (hs : ∀ μ ν, gi μ ν = gi ν μ) (i j : Fin 3) :
    hInv gi i j = hInv gi j i := by
  unfold hInv; rw [hs i.succ j.succ]; ring

/-- **`L Lᵀ = h`**: `Σ_a L_{ia} L_{ja} = h^{ij}`. -/
theorem chol_eq {gi : IMet} (hs : ∀ μ ν, gi μ ν = gi ν μ) (h : IsLorChart gi) (i j : Fin 3) :
    ∑ a, Lmat gi i a * Lmat gi j a = hInv gi i j := by
  have h0 := L00_pos h
  have h1 := L11_pos h
  have s0 := L00_sq h
  have s1 := L11_sq h
  have s2 := L22_sq h
  have e10 : L10 gi * L00 gi = hInv gi 1 0 := by unfold L10; field_simp
  have e20 : L20 gi * L00 gi = hInv gi 2 0 := by unfold L20; field_simp
  have e21 : L21 gi * L11 gi = hInv gi 2 1 - L20 gi * L10 gi := by unfold L21; field_simp
  have hs10 := hInv_symm hs 1 0
  have hs20 := hInv_symm hs 2 0
  have hs21 := hInv_symm hs 2 1
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp only [Lmat, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, mul_zero, zero_mul, add_zero]
  · linear_combination s0
  · linear_combination e10 + hs10
  · linear_combination e20 + hs20
  · linear_combination e10
  · linear_combination s1
  · linear_combination e21 + hs21
  · linear_combination e20
  · linear_combination e21
  · linear_combination s2

/-! ### Adaptation -/

/-- **The frame of a metric is adapted to it**: `g^{μν} = -e_0^μe_0^ν + Σ_a e_a^μe_a^ν`. -/
theorem frameOf_adapted {gi : IMet} (hs : ∀ μ ν, gi μ ν = gi ν μ) (h : IsLorChart gi) :
    (frameOf gi h).IsAdapted gi := by
  have hg0 : gi 0 0 < 0 := h.1
  have hg0' : gi 0 0 ≠ 0 := hg0.ne
  have hN0 := lapse_pos h
  have hNinv : (lapse gi)⁻¹ ^ 2 = -gi 0 0 := by
    unfold lapse; rw [inv_inv, Real.sq_sqrt (by linarith)]
  have hβ : ∀ j : Fin 3, -((lapse gi)⁻¹ * -(shift gi j / lapse gi)) = gi 0 j.succ := by
    intro j
    have : -((lapse gi)⁻¹ * -(shift gi j / lapse gi)) = shift gi j * (lapse gi)⁻¹ ^ 2 := by
      field_simp
    rw [this, hNinv]
    unfold shift
    field_simp
  intro μ ν
  induction μ using Fin.cases with
  | zero =>
    induction ν using Fin.cases with
    | zero =>
      simp only [AdaptedFrame.fr_zero_zero, AdaptedFrame.fr_succ_zero, mul_zero,
        Finset.sum_const_zero, add_zero, frameOf]
      rw [← sq, hNinv, neg_neg]
    | succ j =>
      simp only [AdaptedFrame.fr_zero_zero, AdaptedFrame.fr_zero_succ, AdaptedFrame.fr_succ_zero,
        zero_mul, Finset.sum_const_zero, add_zero, frameOf]
      exact (hβ j).symm
  | succ i =>
    induction ν using Fin.cases with
    | zero =>
      simp only [AdaptedFrame.fr_zero_zero, AdaptedFrame.fr_zero_succ, AdaptedFrame.fr_succ_zero,
        mul_zero, Finset.sum_const_zero, add_zero, frameOf]
      rw [hs, mul_comm]
      exact (hβ i).symm
    | succ j =>
      simp only [AdaptedFrame.fr_zero_succ, AdaptedFrame.fr_succ_succ, frameOf]
      rw [chol_eq hs h i j]
      have : -(-(shift gi i / lapse gi) * -(shift gi j / lapse gi)) =
          -(shift gi i * shift gi j) * (lapse gi)⁻¹ ^ 2 := by field_simp
      rw [this, hNinv]
      unfold hInv shift
      field_simp
      ring

/-! ### Openness and analyticity -/

theorem contDiffAt_hInv (i j : Fin 3) {gi : IMet} (h : gi 0 0 ≠ 0) :
    ContDiffAt ℝ ω (fun gi : IMet => hInv gi i j) gi := by
  unfold hInv
  fun_prop (disch := assumption)

theorem contDiffAt_L00 {gi : IMet} (h : IsLorChart gi) : ContDiffAt ℝ ω L00 gi := by
  unfold L00
  exact (Real.contDiffAt_sqrt h.2.1.ne').comp gi (contDiffAt_hInv 0 0 h.1.ne)

theorem contDiffAt_L10 {gi : IMet} (h : IsLorChart gi) : ContDiffAt ℝ ω L10 gi := by
  unfold L10
  exact (contDiffAt_hInv 1 0 h.1.ne).div (contDiffAt_L00 h) (L00_pos h).ne'

theorem contDiffAt_L20 {gi : IMet} (h : IsLorChart gi) : ContDiffAt ℝ ω L20 gi := by
  unfold L20
  exact (contDiffAt_hInv 2 0 h.1.ne).div (contDiffAt_L00 h) (L00_pos h).ne'

theorem contDiffAt_L11 {gi : IMet} (h : IsLorChart gi) : ContDiffAt ℝ ω L11 gi := by
  unfold L11
  exact (Real.contDiffAt_sqrt h.2.2.1.ne').comp gi
    ((contDiffAt_hInv 1 1 h.1.ne).sub ((contDiffAt_L10 h).pow 2))

theorem contDiffAt_L21 {gi : IMet} (h : IsLorChart gi) : ContDiffAt ℝ ω L21 gi := by
  unfold L21
  exact ((contDiffAt_hInv 2 1 h.1.ne).sub ((contDiffAt_L20 h).mul (contDiffAt_L10 h))).div
    (contDiffAt_L11 h) (L11_pos h).ne'

theorem contDiffAt_L22 {gi : IMet} (h : IsLorChart gi) : ContDiffAt ℝ ω L22 gi := by
  unfold L22
  exact (Real.contDiffAt_sqrt h.2.2.2.ne').comp gi
    (((contDiffAt_hInv 2 2 h.1.ne).sub ((contDiffAt_L20 h).pow 2)).sub ((contDiffAt_L21 h).pow 2))

/-- The chart is open. -/
theorem isOpen_isLorChart : IsOpen {gi : IMet | IsLorChart gi} := by
  rw [isOpen_iff_mem_nhds]
  intro gi hgi
  have hc00 : ContinuousAt (fun gi : IMet => gi 0 0) gi :=
    ((continuous_apply 0).comp (continuous_apply (0 : Fin 4))).continuousAt
  have hc0 : ContinuousAt (fun gi : IMet => hInv gi 0 0) gi :=
    (contDiffAt_hInv 0 0 hgi.1.ne).continuousAt
  have hc1 : ContinuousAt (fun gi : IMet => hInv gi 1 1 - L10 gi ^ 2) gi :=
    ((contDiffAt_hInv 1 1 hgi.1.ne).sub ((contDiffAt_L10 hgi).pow 2)).continuousAt
  have hc2 : ContinuousAt (fun gi : IMet => hInv gi 2 2 - L20 gi ^ 2 - L21 gi ^ 2) gi :=
    (((contDiffAt_hInv 2 2 hgi.1.ne).sub ((contDiffAt_L20 hgi).pow 2)).sub
      ((contDiffAt_L21 hgi).pow 2)).continuousAt
  have h0 : ∀ᶠ g' in nhds gi, g' 0 0 < 0 := hc00.eventually (gt_mem_nhds hgi.1)
  have h00 : ∀ᶠ g' in nhds gi, 0 < hInv g' 0 0 := hc0.eventually (lt_mem_nhds hgi.2.1)
  have h1 : ∀ᶠ g' in nhds gi, 0 < hInv g' 1 1 - L10 g' ^ 2 :=
    hc1.eventually (lt_mem_nhds hgi.2.2.1)
  have h2 : ∀ᶠ g' in nhds gi, 0 < hInv g' 2 2 - L20 g' ^ 2 - L21 g' ^ 2 :=
    hc2.eventually (lt_mem_nhds hgi.2.2.2)
  filter_upwards [h0, h00, h1, h2] with g' a b c e
  exact ⟨a, b, c, e⟩

theorem contDiffAt_Lmat {gi : IMet} (h : IsLorChart gi) (j a : Fin 3) :
    ContDiffAt ℝ ω (fun gi => Lmat gi j a) gi := by
  fin_cases j <;> fin_cases a <;> simp only [Lmat] <;>
    first
    | exact contDiffAt_const
    | exact contDiffAt_L00 h
    | exact contDiffAt_L10 h
    | exact contDiffAt_L20 h
    | exact contDiffAt_L11 h
    | exact contDiffAt_L21 h
    | exact contDiffAt_L22 h

theorem contDiffAt_lapse {gi : IMet} (h : IsLorChart gi) : ContDiffAt ℝ ω lapse gi := by
  unfold lapse
  have hpos : 0 < -gi 0 0 := by linarith [h.1]
  have hs : ContDiffAt ℝ ω (fun gi : IMet => Real.sqrt (-gi 0 0)) gi :=
    (Real.contDiffAt_sqrt hpos.ne').comp gi (by fun_prop)
  exact hs.inv (Real.sqrt_pos.mpr hpos).ne'

theorem contDiffAt_shift {gi : IMet} (h : IsLorChart gi) (j : Fin 3) :
    ContDiffAt ℝ ω (fun gi => shift gi j) gi := by
  unfold shift
  have := h.1.ne
  fun_prop (disch := assumption)

/-- **The adapted frame is a real-analytic function of the inverse metric** on the chart. -/
theorem contDiffAt_frU {gi : IMet} (h : IsLorChart gi) (A μ : Fin 4) :
    ContDiffAt ℝ ω (fun gi => frU gi A μ) gi := by
  have hN := contDiffAt_lapse h
  have hN0 := (lapse_pos h).ne'
  induction A using Fin.cases with
  | zero =>
    induction μ using Fin.cases with
    | zero => exact hN.inv hN0
    | succ j => exact ((contDiffAt_shift h j).div hN hN0).neg
  | succ a =>
    induction μ using Fin.cases with
    | zero => exact contDiffAt_const
    | succ j => exact contDiffAt_Lmat h j a

theorem analyticAt_frU {gi : IMet} (h : IsLorChart gi) (A μ : Fin 4) :
    AnalyticAt ℝ (fun gi => frU gi A μ) gi := (contDiffAt_frU h A μ).analyticAt

/-- **The frame-derivative jets of the metric frame**: for an inverse-metric 1-jet
`(g^{-1}, ∂_γg^{-1})`, `∂_γe_A{}^μ = D(e_A{}^μ)(g^{-1})[∂_γg^{-1}]` — the frame jets entering the
rows of `ActualJetWriterRows` are functions of the metric 1-jet. -/
def frameJet (gi : IMet) (dgi : Fin 4 → IMet) (γ A μ : Fin 4) : ℝ :=
  fderiv ℝ (fun gi => frU gi A μ) gi (dgi γ)

/-- The chain rule: along a smooth curve of inverse metrics in the chart, the frame jet is the
derivative of the frame component. -/
theorem hasDerivAt_frU_comp {gi : ℝ → IMet} {t : ℝ} {dgi : IMet} (hgi : HasDerivAt gi dgi t)
    (h : IsLorChart (gi t)) (A μ : Fin 4) :
    HasDerivAt (fun s => frU (gi s) A μ)
      (fderiv ℝ (fun gi => frU gi A μ) (gi t) dgi) t := by
  have hd := ((contDiffAt_frU h A μ).differentiableAt (by simp)).hasFDerivAt
  exact hd.comp_hasDerivAt t hgi

/-! ### Non-vacuity -/

theorem minkInv_symm : ∀ μ ν, minkInv μ ν = minkInv ν μ := by
  intro μ ν; unfold minkInv; by_cases h : μ = ν
  · subst h; rfl
  · simp [h, Ne.symm h]

theorem minkInv_isLorChart : IsLorChart minkInv := by
  refine ⟨by simp [minkInv], ?_, ?_, ?_⟩ <;>
    simp [hInv, minkInv, L10, L20, L21, L11, L00]

/-- The Minkowski frame is the flat frame. -/
theorem frameOf_minkInv : (frameOf minkInv minkInv_isLorChart).N = 1 ∧
    (∀ j, (frameOf minkInv minkInv_isLorChart).β j = 0) := by
  refine ⟨?_, fun j => ?_⟩
  · simp [frameOf, lapse, minkInv]
  · simp [frameOf, shift, minkInv, (Fin.succ_ne_zero j).symm]

end

end RenewalGeometry.ActualJetFrame
