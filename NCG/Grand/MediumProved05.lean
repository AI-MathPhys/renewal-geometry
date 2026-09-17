/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.EasyExact02

/-!
# Medium exact records, batch 05 (Gran-Tensor manuscript)

Exact formalizations of the following manuscript records (SMST cluster:
Gibbs incidence, Duhamel leakage/variance/head-transport, split-clock
acquisition, low island, positive-time semigroup floor, Markov entrance):

* `lem:SMST-split-clock-trapezoid` — the sharp split-clock trapezoidal bound
  (DMC.3): `0 ≤ Trap_m(x,y) - ∫₀ᵃ f_{x,y} ≤ (h/2)|e^{-ay}-e^{-ax}| ≤ h/2`
  with the uniform constant `h/2` attained in the limit `x = 0`, `y → ∞`.
* `thm:SMST-split-clock-target` — the endpoint-sensitive finite target
  approximation (DMC.5–DMC.7): the quadrature error Gram is dominated by
  `(h²/4)·D_end ⪯ (h²/4)·V*V`, the second-order bound with the
  `(H-λ)²`-weight and coefficient `ah²/12`, and the sharpness of the
  spectrum-free coefficient `1/2`.
* `thm:SMST-Gibbs-incidence-obstruction` — Gibbs incidence (HIT.13–HIT.16):
  injectivity of the Gibbs divided-difference map modulo `ℝI`, the
  Hilbert–Schmidt variance bound, the exact pinching variational identity
  for `inf‖D-[h,K]-cI‖²`, and the Cauchy–Schwarz witness floor.
* `thm:SMST-Duhamel-leakage` — the exact right-clock leakage formula
  (DHI.7–DHI.9): commutator form of the fibre residual, the range
  criterion, the rank identity, and the two reduction clauses.
* `thm:SMST-Duhamel-variance` — the matrix-valued right-energy variance
  (DHI.16–DHI.22): spectral-measure variance identity, the HS commutator
  trace identity, the off-diagonal coherence expansion, the calibrated
  multiplier's Lipschitz-below constant, and the lower certificate.
* `thm:SMST-Duhamel-head-transport` — support-stable finite Duhamel head
  (DHI.23–DHI.26): the head/tail Loewner sandwich, the polynomial tail
  weight, continuity of the residual section, and the transport defects.
* `thm:SMST-mixed-clock-interval` — target-metric interval and cofinal
  landing (DMC.17–DMC.21) with the explicit asymmetric enclosure and the
  cofinal-limit clause.
* `thm:SMST-physical-low-island` — the physical generalized low island
  (DMC.22–DMC.27): projection Pythagoras, the principal-angle distance,
  the low-island bounds, and the complete weighted absorption Gram.
* `thm:SMST-positive-time-semigroup-floor` — the source-local semigroup
  floor `G_t ⪰ e^{-2tE*}G_0` and the collar modulus (PT.2–PT.4).
* `thm:SMST-Markov-entrance-amplitude` — the exact Markov
  entrance-amplitude formula (PT.6–PT.7) on a finite reversible chain.

Rendering conventions are described in the docstring of each section.
-/

open Matrix Finset
open NCG.SourceCoercivityInfluence NCG.GeometricThresholdBank NCG.PsdBlockSchur
open scoped ComplexOrder

-- decidability/fintype instances enter only through the spectral support calculus in proofs
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace NCG

namespace SMST05

/-! ### `lem:SMST-split-clock-trapezoid` — Sharp split-clock trapezoidal bound

Rendering: the kernel `f_{x,y}(s) = e^{-(a-s)x-sy}`, the trapezoid weights
`ω₀ = ω_m = 1/2`, `ω_j = 1` (reusing `ClockPacket.omega`), and the calibrated
step `m·h = a` are literal.  The three inequalities of (DMC.3) are proved for
all `x, y ≥ 0`, and the sharpness clause is rendered as the exact limit
`Trap_m(0,y) - ∫₀ᵃ f_{0,y} → h/2` as `y → ∞`, together with the ε-form
`∀ ε > 0, ∃ y ≥ 0` with error above `h/2 - ε`.  The section also proves the
composite second-order remainder bound `Trap - ∫ ≤ (ah²/12)(x-y)²` consumed
by `thm:SMST-split-clock-target`. -/

section Trapezoid

/-- The split-clock kernel `f_{x,y}(s) = e^{-(a-s)x - sy}` (DMC.3). -/
noncomputable def clockKernel (a x y s : ℝ) : ℝ := Real.exp (-((a - s) * x) - s * y)

/-- The kernel in affine-exponent normal form. -/
theorem clockKernel_eq (a x y s : ℝ) :
    clockKernel a x y s = Real.exp ((x - y) * s - a * x) := by
  unfold clockKernel
  congr 1
  ring

/-- The kernel is continuous in the clock variable. -/
theorem clockKernel_continuous (a x y : ℝ) : Continuous (clockKernel a x y) := by
  unfold clockKernel
  fun_prop

/-- The kernel is positive. -/
theorem clockKernel_pos (a x y s : ℝ) : 0 < clockKernel a x y s := Real.exp_pos _

/-- The kernel at the left endpoint is `e^{-ax}`. -/
theorem clockKernel_zero (a x y : ℝ) : clockKernel a x y 0 = Real.exp (-(a * x)) := by
  unfold clockKernel
  norm_num

/-- The kernel at the right endpoint is `e^{-ay}`. -/
theorem clockKernel_endpoint (a x y : ℝ) : clockKernel a x y a = Real.exp (-(a * y)) := by
  unfold clockKernel
  norm_num

/-- The kernel is bounded by one for nonnegative data. -/
theorem clockKernel_le_one {a x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hs : 0 ≤ s)
    (hsa : s ≤ a) : clockKernel a x y s ≤ 1 := by
  unfold clockKernel
  rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The trapezoid value `Trap_m(x,y) = h∑ ω_j f(jh)` (DMC.3). -/
noncomputable def trapSum (a h : ℝ) (m : ℕ) (x y : ℝ) : ℝ :=
  h * ∑ j ∈ Finset.range (m + 1), ClockPacket.omega m j * clockKernel a x y ((j : ℝ) * h)

/-- Chord domination on one panel: the integral of the convex kernel lies
below its trapezoid panel. -/
theorem integral_le_panel (a x y u h : ℝ) (hh : 0 < h) :
    ∫ s in u..(u + h), clockKernel a x y s
      ≤ h / 2 * (clockKernel a x y u + clockKernel a x y (u + h)) := by
  have hne : h ≠ 0 := ne_of_gt hh
  set C1 := clockKernel a x y u with hC1
  set C2 := clockKernel a x y (u + h) with hC2
  have hchord : ∀ s ∈ Set.Icc u (u + h),
      clockKernel a x y s ≤ C1 + (s - u) * (C2 - C1) / h := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    set θ := (u + h - s) / h with hθ
    have hθ0 : 0 ≤ θ := by
      apply div_nonneg _ hh.le
      linarith
    have hθ1 : 0 ≤ 1 - θ := by
      rw [hθ, sub_nonneg, div_le_one hh]
      linarith
    have hθsum : θ + (1 - θ) = 1 := by ring
    have hcx := convexOn_exp.2 (Set.mem_univ ((x - y) * u - a * x))
      (Set.mem_univ ((x - y) * (u + h) - a * x)) hθ0 hθ1 hθsum
    have harg : θ • ((x - y) * u - a * x) + (1 - θ) • ((x - y) * (u + h) - a * x)
        = (x - y) * s - a * x := by
      simp only [smul_eq_mul, hθ]
      field_simp
      ring
    rw [harg] at hcx
    have hcomb : θ • Real.exp ((x - y) * u - a * x)
        + (1 - θ) • Real.exp ((x - y) * (u + h) - a * x)
        = C1 + (s - u) * (C2 - C1) / h := by
      simp only [smul_eq_mul, hθ, hC1, hC2, clockKernel_eq]
      field_simp
      ring
    rw [hcomb] at hcx
    rw [clockKernel_eq]
    exact hcx
  have hle : ∫ s in u..(u + h), clockKernel a x y s
      ≤ ∫ s in u..(u + h), (C1 + (s - u) * (C2 - C1) / h) := by
    apply intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (by linarith)
      ((clockKernel_continuous a x y).intervalIntegrable u (u + h))
      (Continuous.intervalIntegrable (by fun_prop) u (u + h))
    exact hchord
  have hval : ∫ s in u..(u + h), (C1 + (s - u) * (C2 - C1) / h)
      = h / 2 * (C1 + C2) := by
    have hF : ∀ s ∈ Set.uIcc u (u + h),
        HasDerivAt (fun s : ℝ => C1 * s + (s - u) * (s - u) * (C2 - C1) / (2 * h))
          (C1 + (s - u) * (C2 - C1) / h) s := by
      intro s _
      have hd1 : HasDerivAt (fun s : ℝ => C1 * s) C1 s := by
        simpa using (hasDerivAt_id s).const_mul C1
      have hbase : HasDerivAt (fun s : ℝ => s - u) 1 s := (hasDerivAt_id s).sub_const u
      have hd2 : HasDerivAt (fun s : ℝ => (s - u) * (s - u)) (2 * (s - u)) s := by
        have hm := hbase.mul hbase
        rw [show (1 : ℝ) * (s - u) + (s - u) * 1 = 2 * (s - u) by ring] at hm
        exact hm
      have hd3 : HasDerivAt (fun s : ℝ => (s - u) * (s - u) * (C2 - C1) / (2 * h))
          ((s - u) * (C2 - C1) / h) s := by
        have hq := (hd2.mul_const (C2 - C1)).div_const (2 * h)
        rw [show 2 * (s - u) * (C2 - C1) / (2 * h) = (s - u) * (C2 - C1) / h by
          rw [mul_assoc, mul_div_mul_left _ _ (two_ne_zero (α := ℝ))]] at hq
        exact hq
      exact hd1.add hd3
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      (Continuous.intervalIntegrable (by fun_prop) u (u + h))]
    field_simp
    ring
  calc ∫ s in u..(u + h), clockKernel a x y s
      ≤ ∫ s in u..(u + h), (C1 + (s - u) * (C2 - C1) / h) := hle
    _ = h / 2 * (C1 + C2) := hval

/-- Endpoint floor on one panel: the integral dominates the smaller endpoint. -/
theorem panel_min_le_integral (a x y u h : ℝ) (hh : 0 < h) :
    h * min (clockKernel a x y u) (clockKernel a x y (u + h))
      ≤ ∫ s in u..(u + h), clockKernel a x y s := by
  have hpt : ∀ s ∈ Set.Icc u (u + h),
      min (clockKernel a x y u) (clockKernel a x y (u + h)) ≤ clockKernel a x y s := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    rcases le_total 0 (x - y) with hk | hk
    · refine (min_le_left _ _).trans ?_
      simp only [clockKernel_eq]
      apply Real.exp_le_exp.mpr
      nlinarith
    · refine (min_le_right _ _).trans ?_
      simp only [clockKernel_eq]
      apply Real.exp_le_exp.mpr
      nlinarith
  have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (by linarith : u ≤ u + h) intervalIntegrable_const
    ((clockKernel_continuous a x y).intervalIntegrable u (u + h)) hpt
  rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hmono
  exact hmono

/-- One-panel trapezoid error upper bound by the endpoint oscillation. -/
theorem panel_error_le (a x y u h : ℝ) (hh : 0 < h) :
    h / 2 * (clockKernel a x y u + clockKernel a x y (u + h))
        - ∫ s in u..(u + h), clockKernel a x y s
      ≤ h / 2 * |clockKernel a x y (u + h) - clockKernel a x y u| := by
  have hmin := panel_min_le_integral a x y u h hh
  rcases le_total (clockKernel a x y u) (clockKernel a x y (u + h)) with hc | hc
  · rw [min_eq_left hc] at hmin
    rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [min_eq_right hc] at hmin
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- The trapezoid value is the sum of its panels. -/
theorem trapSum_eq_panels (a h : ℝ) (m : ℕ) (x y : ℝ) (hm : m ≠ 0) :
    trapSum a h m x y
      = ∑ j ∈ Finset.range m, h / 2
          * (clockKernel a x y ((j : ℝ) * h) + clockKernel a x y ((j : ℝ) * h + h)) := by
  set f : ℕ → ℝ := fun j => clockKernel a x y ((j : ℝ) * h) with hf
  have hterm : ∀ j ∈ Finset.range (m + 1),
      ClockPacket.omega m j * f j
        = f j - (if j = 0 then (1 / 2 : ℝ) * f j else 0)
            - (if j = m then (1 / 2 : ℝ) * f j else 0) := by
    intro j _
    unfold ClockPacket.omega
    rcases eq_or_ne j 0 with rfl | h0
    · rw [ite_eq_left (Or.inl rfl), ite_eq_left rfl, ite_eq_right (Ne.symm hm)]
      ring
    · rcases eq_or_ne j m with rfl | h1
      · rw [ite_eq_left (Or.inr rfl), ite_eq_right h0, ite_eq_left rfl]
        ring
      · rw [ite_eq_right (by tauto), ite_eq_right h0, ite_eq_right h1]
        ring
  have e0 : ∑ j ∈ Finset.range (m + 1), (if j = 0 then (1 / 2 : ℝ) * f j else 0)
      = (1 / 2) * f 0 := by
    rw [Finset.sum_ite_eq' (Finset.range (m + 1)) 0 (fun j => (1 / 2 : ℝ) * f j),
      ite_eq_left (Finset.mem_range.mpr (Nat.succ_pos m))]
  have em : ∑ j ∈ Finset.range (m + 1), (if j = m then (1 / 2 : ℝ) * f j else 0)
      = (1 / 2) * f m := by
    rw [Finset.sum_ite_eq' (Finset.range (m + 1)) m (fun j => (1 / 2 : ℝ) * f j),
      ite_eq_left (Finset.mem_range.mpr (Nat.lt_succ_self m))]
  have hsplit : ∑ j ∈ Finset.range (m + 1), ClockPacket.omega m j * f j
      = (∑ j ∈ Finset.range (m + 1), f j) - (1 / 2) * f 0 - (1 / 2) * f m := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_sub_distrib, e0, em]
  have hsucc : ∀ j : ℕ, f (j + 1) = clockKernel a x y ((j : ℝ) * h + h) := by
    intro j
    rw [hf]
    push_cast
    ring_nf
  have h2 : ∑ j ∈ Finset.range m, f j = (∑ j ∈ Finset.range (m + 1), f j) - f m := by
    rw [Finset.sum_range_succ]
    ring
  have h3 : ∑ j ∈ Finset.range m, f (j + 1)
      = (∑ j ∈ Finset.range (m + 1), f j) - f 0 := by
    rw [Finset.sum_range_succ' f m]
    ring
  have hpanels : ∑ j ∈ Finset.range m,
      h / 2 * (clockKernel a x y ((j : ℝ) * h) + clockKernel a x y ((j : ℝ) * h + h))
      = h * ((∑ j ∈ Finset.range (m + 1), f j) - (1 / 2) * f 0 - (1 / 2) * f m) := by
    have hterm2 : ∀ j ∈ Finset.range m,
        h / 2 * (clockKernel a x y ((j : ℝ) * h) + clockKernel a x y ((j : ℝ) * h + h))
          = h / 2 * (f j + f (j + 1)) := by
      intro j _
      rw [hsucc j, hf]
    rw [Finset.sum_congr rfl hterm2]
    calc ∑ j ∈ Finset.range m, h / 2 * (f j + f (j + 1))
        = h / 2 * ((∑ j ∈ Finset.range m, f j) + ∑ j ∈ Finset.range m, f (j + 1)) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
      _ = h * ((∑ j ∈ Finset.range (m + 1), f j) - (1 / 2) * f 0 - (1 / 2) * f m) := by
          rw [h2, h3]
          ring
  unfold trapSum
  rw [hsplit, hpanels]

/-- The exact integral splits into adjacent panels. -/
theorem integral_eq_panels (a h : ℝ) (m : ℕ) (x y : ℝ) (hcal : (m : ℝ) * h = a) :
    ∫ s in (0 : ℝ)..a, clockKernel a x y s
      = ∑ j ∈ Finset.range m,
          ∫ s in ((j : ℝ) * h)..((j : ℝ) * h + h), clockKernel a x y s := by
  have key := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
    (a := fun j : ℕ => (j : ℝ) * h) (n := m)
    (fun k _ => (clockKernel_continuous a x y).intervalIntegrable _ _)
  rw [show ((0 : ℕ) : ℝ) * h = 0 by norm_num, hcal] at key
  rw [← key]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  push_cast
  ring

/-- **`lem:SMST-split-clock-trapezoid` (DMC.3)**: the sharp split-clock
trapezoidal bound `0 ≤ Trap_m(x,y) - ∫₀ᵃ f ≤ (h/2)|e^{-ay}-e^{-ax}| ≤ h/2`
for all `x, y ≥ 0` under the calibration `m·h = a`. -/
theorem split_clock_trapezoid (a h : ℝ) (m : ℕ) (x y : ℝ) (ha : 0 < a) (hm : m ≠ 0)
    (hcal : (m : ℝ) * h = a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ trapSum a h m x y - ∫ s in (0 : ℝ)..a, clockKernel a x y s ∧
    trapSum a h m x y - ∫ s in (0 : ℝ)..a, clockKernel a x y s
      ≤ h / 2 * |Real.exp (-(a * y)) - Real.exp (-(a * x))| ∧
    h / 2 * |Real.exp (-(a * y)) - Real.exp (-(a * x))| ≤ h / 2 := by
  have hh : 0 < h := by
    have hm' : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    nlinarith
  set f : ℕ → ℝ := fun j => clockKernel a x y ((j : ℝ) * h) with hf
  have hsucc : ∀ j : ℕ, f (j + 1) = clockKernel a x y ((j : ℝ) * h + h) := by
    intro j
    rw [hf]
    push_cast
    ring_nf
  have hdiff : trapSum a h m x y - ∫ s in (0 : ℝ)..a, clockKernel a x y s
      = ∑ j ∈ Finset.range m,
          (h / 2 * (clockKernel a x y ((j : ℝ) * h) + clockKernel a x y ((j : ℝ) * h + h))
            - ∫ s in ((j : ℝ) * h)..((j : ℝ) * h + h), clockKernel a x y s) := by
    rw [trapSum_eq_panels a h m x y hm, integral_eq_panels a h m x y hcal,
      ← Finset.sum_sub_distrib]
  refine ⟨?_, ?_, ?_⟩
  · rw [hdiff]
    refine Finset.sum_nonneg fun j _ => ?_
    have := integral_le_panel a x y ((j : ℝ) * h) h hh
    linarith
  · rw [hdiff]
    have hup : ∀ j ∈ Finset.range m,
        h / 2 * (clockKernel a x y ((j : ℝ) * h) + clockKernel a x y ((j : ℝ) * h + h))
            - (∫ s in ((j : ℝ) * h)..((j : ℝ) * h + h), clockKernel a x y s)
          ≤ h / 2 * |f (j + 1) - f j| := by
      intro j _
      have := panel_error_le a x y ((j : ℝ) * h) h hh
      rw [hsucc j, hf]
      exact this
    refine (Finset.sum_le_sum hup).trans ?_
    have hfm : f m = Real.exp (-(a * y)) := by
      rw [hf]
      simp only
      rw [hcal, clockKernel_endpoint]
    have hf0 : f 0 = Real.exp (-(a * x)) := by
      rw [hf]
      simp only [Nat.cast_zero, zero_mul, clockKernel_zero]
    rcases le_total 0 (x - y) with hk | hk
    · -- increasing kernel: absolute values telescope upward
      have hmono : ∀ j : ℕ, f j ≤ f (j + 1) := by
        intro j
        rw [hf]
        simp only [clockKernel_eq]
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith
      have habs : ∑ j ∈ Finset.range m, h / 2 * |f (j + 1) - f j|
          = h / 2 * ∑ j ∈ Finset.range m, (f (j + 1) - f j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [abs_of_nonneg (by linarith [hmono j])]
      rw [habs, Finset.sum_range_sub f m, hfm, hf0]
      refine le_of_eq ?_
      rw [abs_of_nonneg (by
        apply sub_nonneg.mpr
        apply Real.exp_le_exp.mpr
        nlinarith)]
    · -- decreasing kernel: absolute values telescope downward
      have hmono : ∀ j : ℕ, f (j + 1) ≤ f j := by
        intro j
        rw [hf]
        simp only [clockKernel_eq]
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith
      have habs : ∑ j ∈ Finset.range m, h / 2 * |f (j + 1) - f j|
          = h / 2 * ∑ j ∈ Finset.range m, (f j - f (j + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [abs_of_nonpos (by linarith [hmono j]), neg_sub]
      have hsum : ∑ j ∈ Finset.range m, (f j - f (j + 1)) = f 0 - f m := by
        have hneg := Finset.sum_range_sub (fun j => -f j) m
        simp only [neg_sub_neg] at hneg
        exact hneg
      rw [habs, hsum, hfm, hf0]
      refine le_of_eq ?_
      rw [abs_of_nonpos (by
        apply sub_nonpos.mpr
        apply Real.exp_le_exp.mpr
        nlinarith)]
      ring
  · have h1 : Real.exp (-(a * y)) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
      apply Real.exp_le_exp.mpr
      nlinarith
    have h2 : Real.exp (-(a * x)) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
      apply Real.exp_le_exp.mpr
      nlinarith
    have h3 : 0 < Real.exp (-(a * y)) := Real.exp_pos _
    have h4 : 0 < Real.exp (-(a * x)) := Real.exp_pos _
    have habs : |Real.exp (-(a * y)) - Real.exp (-(a * x))| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    nlinarith

/-- The integral of the pure right-decay kernel tends to zero at large
right energy. -/
theorem integral_clockKernel_decay (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun y => ∫ s in (0 : ℝ)..a, clockKernel a 0 y s)
      Filter.atTop (nhds 0) := by
  have hval : ∀ y : ℝ, 0 < y →
      (∫ s in (0 : ℝ)..a, clockKernel a 0 y s) = (1 - Real.exp (-(a * y))) / y := by
    intro y hy
    have hyne : y ≠ 0 := ne_of_gt hy
    have hF : ∀ s ∈ Set.uIcc (0 : ℝ) a,
        HasDerivAt (fun s : ℝ => -Real.exp (-(y * s)) / y) (clockKernel a 0 y s) s := by
      intro s _
      have hinner : HasDerivAt (fun s : ℝ => -(y * s)) (-(y * 1)) s :=
        ((hasDerivAt_id s).const_mul y).neg
      have houter := hinner.exp
      have hd := (houter.neg).div_const y
      have hraw : HasDerivAt (fun s : ℝ => -Real.exp (-(y * s)) / y)
          (-(Real.exp (-(y * s)) * -(y * 1)) / y) s := hd
      rw [show -(Real.exp (-(y * s)) * -(y * 1)) / y = Real.exp (-(y * s)) by
        field_simp] at hraw
      rw [show clockKernel a 0 y s = Real.exp (-(y * s)) by
        rw [clockKernel_eq]; congr 1; ring]
      exact hraw
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      ((clockKernel_continuous a 0 y).intervalIntegrable 0 a)]
    rw [show -(y * (0 : ℝ)) = 0 by ring, Real.exp_zero]
    field_simp
    rw [show y * a = a * y by ring]
    ring
  have hub : ∀ᶠ y in Filter.atTop,
      (∫ s in (0 : ℝ)..a, clockKernel a 0 y s) ≤ 1 / y := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with y hy
    rw [hval y hy]
    have h1 : 0 < Real.exp (-(a * y)) := Real.exp_pos _
    gcongr
    linarith
  have hlb : ∀ᶠ y in Filter.atTop,
      (0 : ℝ) ≤ ∫ s in (0 : ℝ)..a, clockKernel a 0 y s := by
    filter_upwards with y
    apply intervalIntegral.integral_nonneg ha.le
    intro s _
    exact (clockKernel_pos a 0 y s).le
  have hinv : Filter.Tendsto (fun y : ℝ => 1 / y) Filter.atTop (nhds 0) := by
    simpa using tendsto_inv_atTop_zero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv hlb hub

/-- The trapezoid value of the pure right-decay kernel tends to the
half-weighted left endpoint `h/2`. -/
theorem trapSum_decay_tendsto (a h : ℝ) (m : ℕ) (_hm : m ≠ 0) (hh : 0 < h) :
    Filter.Tendsto (fun y => trapSum a h m 0 y) Filter.atTop (nhds (h / 2)) := by
  have hterm : ∀ j ∈ Finset.range (m + 1),
      Filter.Tendsto (fun y => ClockPacket.omega m j * clockKernel a 0 y ((j : ℝ) * h))
        Filter.atTop (nhds (if j = 0 then ClockPacket.omega m 0 else 0)) := by
    intro j _
    rcases eq_or_ne j 0 with rfl | hj
    · rw [ite_eq_left rfl]
      have hfun : (fun y => ClockPacket.omega m 0 * clockKernel a 0 y (((0 : ℕ) : ℝ) * h))
          = fun _ => ClockPacket.omega m 0 := by
        funext y
        rw [show (((0 : ℕ) : ℝ) * h) = 0 by norm_num, clockKernel_zero]
        norm_num
      rw [hfun]
      exact tendsto_const_nhds
    · rw [ite_eq_right hj]
      have hjh : 0 < (j : ℝ) * h := by
        have : 0 < (j : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hj
        positivity
      have hfun : (fun y => ClockPacket.omega m j * clockKernel a 0 y ((j : ℝ) * h))
          = fun y => ClockPacket.omega m j * Real.exp (-((j : ℝ) * h * y)) := by
        funext y
        rw [clockKernel_eq]
        congr 2
        ring
      rw [hfun]
      have hexp : Filter.Tendsto (fun y => Real.exp (-((j : ℝ) * h * y)))
          Filter.atTop (nhds 0) := by
        apply Real.tendsto_exp_atBot.comp
        apply Filter.tendsto_neg_atBot_iff.mpr
        exact Filter.Tendsto.const_mul_atTop hjh Filter.tendsto_id
      have := hexp.const_mul (ClockPacket.omega m j)
      simpa using this
  have hsum := tendsto_finsetSum (Finset.range (m + 1)) hterm
  have hlim : ∑ j ∈ Finset.range (m + 1), (if j = 0 then ClockPacket.omega m 0 else 0)
      = 1 / 2 := by
    rw [Finset.sum_ite_eq' (Finset.range (m + 1)) 0 (fun _ => ClockPacket.omega m 0),
      ite_eq_left (Finset.mem_range.mpr (Nat.succ_pos m))]
    unfold ClockPacket.omega
    rw [ite_eq_left (Or.inl rfl)]
  rw [hlim] at hsum
  have hfin := hsum.const_mul h
  rw [show h * (1 / 2 : ℝ) = h / 2 by ring] at hfin
  unfold trapSum
  exact hfin

/-- The trapezoid error attains its uniform bound `h/2` in the limit
`x = 0`, `y → ∞` (sharpness of the constant in DMC.3). -/
theorem split_clock_error_tendsto (a h : ℝ) (m : ℕ) (ha : 0 < a) (hm : m ≠ 0)
    (hcal : (m : ℝ) * h = a) :
    Filter.Tendsto
      (fun y => trapSum a h m 0 y - ∫ s in (0 : ℝ)..a, clockKernel a 0 y s)
      Filter.atTop (nhds (h / 2)) := by
  have hh : 0 < h := by
    have hm' : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    nlinarith
  have := (trapSum_decay_tendsto a h m hm hh).sub (integral_clockKernel_decay a ha)
  simpa using this

/-- **Sharpness clause of `lem:SMST-split-clock-trapezoid`**: the constant
`h/2` is sharp uniformly over `x, y ≥ 0` — no smaller constant bounds the
trapezoid error for all admissible data. -/
theorem split_clock_constant_sharp (a h : ℝ) (m : ℕ) (ha : 0 < a) (hm : m ≠ 0)
    (hcal : (m : ℝ) * h = a) :
    ∀ ε > 0, ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧
      h / 2 - ε < trapSum a h m x y - ∫ s in (0 : ℝ)..a, clockKernel a x y s := by
  intro ε hε
  have hev := (split_clock_error_tendsto a h m ha hm hcal).eventually
    (lt_mem_nhds (show h / 2 - ε < h / 2 by linarith))
  obtain ⟨y, hy1, hy2⟩ := (hev.and (Filter.eventually_ge_atTop (0 : ℝ))).exists
  exact ⟨0, y, le_refl 0, hy2, hy1⟩

/-! #### Second-order trapezoid remainder (consumed by DMC.7) -/

/-- The core inequality `t(1+eᵗ)/2 - (eᵗ-1) ≤ t³eᵗ/12` for `t ≥ 0`,
by two rounds of derivative monotonicity. -/
theorem psi_le_cubic {t : ℝ} (ht : 0 ≤ t) :
    t * (1 + Real.exp t) / 2 - (Real.exp t - 1) ≤ t * t * t * Real.exp t / 12 := by
  set g1 : ℝ → ℝ := fun t =>
    (t * t / 4 + t * t * t / 12) * Real.exp t - 1 / 2 + Real.exp t / 2
      - t * Real.exp t / 2 with hg1def
  set g : ℝ → ℝ := fun t =>
    t * t * t * Real.exp t / 12 - (t * (1 + Real.exp t) / 2 - (Real.exp t - 1)) with hgdef
  have hg1deriv : ∀ s : ℝ,
      HasDerivAt g1 ((s * s / 2 + s * s * s / 12) * Real.exp s) s := by
    intro s
    have htt : HasDerivAt (fun t : ℝ => t * t) (1 * s + s * 1) s :=
      (hasDerivAt_id s).mul (hasDerivAt_id s)
    have httt : HasDerivAt (fun t : ℝ => t * t * t) ((1 * s + s * 1) * s + s * s * 1) s :=
      htt.mul (hasDerivAt_id s)
    have hpoly := (htt.div_const 4).add (httt.div_const 12)
    have hexp := Real.hasDerivAt_exp s
    have hte : HasDerivAt (fun t : ℝ => t * Real.exp t)
        (1 * Real.exp s + s * Real.exp s) s := (hasDerivAt_id s).mul hexp
    have hall : HasDerivAt g1
        (((1 * s + s * 1) / 4 + ((1 * s + s * 1) * s + s * s * 1) / 12) * Real.exp s
          + (s * s / 4 + s * s * s / 12) * Real.exp s + Real.exp s / 2
          - (1 * Real.exp s + s * Real.exp s) / 2) s :=
      (((hpoly.mul hexp).sub_const (1 / 2 : ℝ)).add (hexp.div_const 2)).sub
        (hte.div_const 2)
    rw [show ((1 * s + s * 1) / 4 + ((1 * s + s * 1) * s + s * s * 1) / 12) * Real.exp s
          + (s * s / 4 + s * s * s / 12) * Real.exp s + Real.exp s / 2
          - (1 * Real.exp s + s * Real.exp s) / 2
        = (s * s / 2 + s * s * s / 12) * Real.exp s by ring] at hall
    exact hall
  have hgderiv : ∀ s : ℝ, HasDerivAt g (g1 s) s := by
    intro s
    have htt : HasDerivAt (fun t : ℝ => t * t) (1 * s + s * 1) s :=
      (hasDerivAt_id s).mul (hasDerivAt_id s)
    have httt : HasDerivAt (fun t : ℝ => t * t * t) ((1 * s + s * 1) * s + s * s * 1) s :=
      htt.mul (hasDerivAt_id s)
    have hexp := Real.hasDerivAt_exp s
    have hpe : HasDerivAt (fun t : ℝ => 1 + Real.exp t) (0 + Real.exp s) s :=
      (hasDerivAt_const s (1 : ℝ)).add hexp
    have hA := (httt.mul hexp).div_const 12
    have hB := ((hasDerivAt_id s).mul hpe).div_const 2
    have hC := hexp.sub_const (1 : ℝ)
    have hall : HasDerivAt g
        ((((1 * s + s * 1) * s + s * s * 1) * Real.exp s + s * s * s * Real.exp s) / 12
          - ((1 * (1 + Real.exp s) + s * (0 + Real.exp s)) / 2 - Real.exp s)) s :=
      hA.sub (hB.sub hC)
    rw [show (((1 * s + s * 1) * s + s * s * 1) * Real.exp s + s * s * s * Real.exp s) / 12
          - ((1 * (1 + Real.exp s) + s * (0 + Real.exp s)) / 2 - Real.exp s)
        = g1 s by rw [hg1def]; ring] at hall
    exact hall
  have hg1mono : MonotoneOn g1 (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun s _ => (hg1deriv s).differentiableAt.continuousAt.continuousWithinAt)
      (fun s _ => (hg1deriv s).differentiableAt.differentiableWithinAt)
    intro s hs
    rw [(hg1deriv s).deriv]
    rw [interior_Ici] at hs
    have hs' : (0 : ℝ) < s := hs
    positivity
  have hg1zero : g1 0 = 0 := by
    rw [hg1def]
    norm_num
  have hg1nonneg : ∀ s : ℝ, 0 ≤ s → 0 ≤ g1 s := by
    intro s hs
    have := hg1mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs
    rw [hg1zero] at this
    exact this
  have hgmono : MonotoneOn g (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun s _ => (hgderiv s).differentiableAt.continuousAt.continuousWithinAt)
      (fun s _ => (hgderiv s).differentiableAt.differentiableWithinAt)
    intro s hs
    rw [(hgderiv s).deriv]
    rw [interior_Ici] at hs
    exact hg1nonneg s hs.le
  have hgzero : g 0 = 0 := by
    rw [hgdef]
    norm_num
  have := hgmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  rw [hgzero, hgdef] at this
  simp only at this
  linarith

/-- One-panel exponential trapezoid bound, positive-slope case. -/
theorem panel_scalar_core {fu k h : ℝ} (hfu : 0 < fu) (hk : 0 < k) (hh : 0 < h) :
    h * (fu + fu * Real.exp (k * h)) / 2 - (fu * Real.exp (k * h) - fu) / k
      ≤ h * h * h * (k * k) / 12 * (fu * Real.exp (k * h)) := by
  have hpsi := psi_le_cubic (show 0 ≤ k * h by positivity)
  have e1 : h * (fu + fu * Real.exp (k * h)) / 2 - (fu * Real.exp (k * h) - fu) / k
      = fu / k * ((k * h) * (1 + Real.exp (k * h)) / 2 - (Real.exp (k * h) - 1)) := by
    field_simp
  have e2 : h * h * h * (k * k) / 12 * (fu * Real.exp (k * h))
      = fu / k * ((k * h) * (k * h) * (k * h) * Real.exp (k * h) / 12) := by
    field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hpsi (by positivity)

/-- One-panel exponential trapezoid bound, both slope signs. -/
theorem panel_scalar {fu k h : ℝ} (hfu : 0 < fu) (hk : k ≠ 0) (hh : 0 < h) :
    h * (fu + fu * Real.exp (k * h)) / 2 - (fu * Real.exp (k * h) - fu) / k
      ≤ h * h * h * (k * k) / 12 * max fu (fu * Real.exp (k * h)) := by
  rcases hk.lt_or_gt with hneg | hpos
  · have hcore := panel_scalar_core (fu := fu * Real.exp (k * h)) (k := -k) (h := h)
      (by positivity) (by linarith) hh
    have hcancel : fu * Real.exp (k * h) * Real.exp (-k * h) = fu := by
      rw [mul_assoc, ← Real.exp_add, show k * h + -k * h = 0 by ring, Real.exp_zero,
        mul_one]
    rw [hcancel] at hcore
    have hEle : fu * Real.exp (k * h) ≤ fu := by
      have : Real.exp (k * h) ≤ 1 := by
        rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
        apply Real.exp_le_exp.mpr
        nlinarith
      nlinarith
    rw [max_eq_left hEle]
    calc h * (fu + fu * Real.exp (k * h)) / 2 - (fu * Real.exp (k * h) - fu) / k
        = h * (fu * Real.exp (k * h) + fu) / 2 - (fu - fu * Real.exp (k * h)) / -k := by
          ring
      _ ≤ h * h * h * (-k * -k) / 12 * fu := hcore
      _ = h * h * h * (k * k) / 12 * fu := by ring
  · have hcore := panel_scalar_core hfu hpos hh
    have hEge : fu ≤ fu * Real.exp (k * h) := by
      have : (1 : ℝ) ≤ Real.exp (k * h) := by
        rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
        apply Real.exp_le_exp.mpr
        nlinarith
      nlinarith
    rw [max_eq_right hEge]
    exact hcore

/-- One-panel second-order trapezoid remainder for the split-clock kernel. -/
theorem panel_error_second_order (a x y u h : ℝ) (hh : 0 < h)
    (hu1 : clockKernel a x y u ≤ 1) (hv1 : clockKernel a x y (u + h) ≤ 1) :
    h / 2 * (clockKernel a x y u + clockKernel a x y (u + h))
        - ∫ s in u..(u + h), clockKernel a x y s
      ≤ h * h * h * ((x - y) * (x - y)) / 12 := by
  rcases eq_or_ne (x - y) 0 with hk | hk
  · -- constant kernel: exact quadrature
    have hconstf : ∀ s : ℝ, clockKernel a x y s = Real.exp (-(a * x)) := by
      intro s
      rw [clockKernel_eq, hk]
      norm_num
    have hint : ∫ s in u..(u + h), clockKernel a x y s = h * Real.exp (-(a * x)) := by
      rw [show (fun s : ℝ => clockKernel a x y s) = fun _ : ℝ => Real.exp (-(a * x)) from
        funext hconstf]
      rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left]
    rw [hint, hconstf u, hconstf (u + h), hk]
    ring_nf
    positivity
  · have hfu : 0 < clockKernel a x y u := clockKernel_pos a x y u
    have hE : clockKernel a x y (u + h)
        = clockKernel a x y u * Real.exp ((x - y) * h) := by
      rw [clockKernel_eq, clockKernel_eq, ← Real.exp_add]
      congr 1
      ring
    have hint : ∫ s in u..(u + h), clockKernel a x y s
        = (clockKernel a x y (u + h) - clockKernel a x y u) / (x - y) := by
      have hF : ∀ s ∈ Set.uIcc u (u + h),
          HasDerivAt (fun s : ℝ => Real.exp ((x - y) * s - a * x) / (x - y))
            (clockKernel a x y s) s := by
        intro s _
        have hinner : HasDerivAt (fun s : ℝ => (x - y) * s - a * x) ((x - y) * 1) s :=
          ((hasDerivAt_id s).const_mul (x - y)).sub_const (a * x)
        have hd : HasDerivAt (fun s : ℝ => Real.exp ((x - y) * s - a * x) / (x - y))
            (Real.exp ((x - y) * s - a * x) * ((x - y) * 1) / (x - y)) s :=
          (hinner.exp).div_const (x - y)
        rw [show Real.exp ((x - y) * s - a * x) * ((x - y) * 1) / (x - y)
            = clockKernel a x y s by rw [clockKernel_eq]; field_simp] at hd
        exact hd
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
        ((clockKernel_continuous a x y).intervalIntegrable u (u + h))]
      rw [div_sub_div_same, clockKernel_eq, clockKernel_eq]
    have hcore := panel_scalar (fu := clockKernel a x y u) (k := x - y) (h := h) hfu hk hh
    rw [← hE] at hcore
    have hmax : max (clockKernel a x y u) (clockKernel a x y (u + h)) ≤ 1 :=
      max_le hu1 hv1
    calc h / 2 * (clockKernel a x y u + clockKernel a x y (u + h))
          - ∫ s in u..(u + h), clockKernel a x y s
        = h * (clockKernel a x y u + clockKernel a x y (u + h)) / 2
          - (clockKernel a x y (u + h) - clockKernel a x y u) / (x - y) := by
          rw [hint]
          ring
      _ ≤ h * h * h * ((x - y) * (x - y)) / 12
          * max (clockKernel a x y u) (clockKernel a x y (u + h)) := hcore
      _ ≤ h * h * h * ((x - y) * (x - y)) / 12 := by
          have hc : (0 : ℝ) ≤ h * h * h * ((x - y) * (x - y)) / 12 :=
            div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hh.le hh.le) hh.le)
              (mul_self_nonneg _)) (by norm_num)
          have hmm := mul_le_mul_of_nonneg_left hmax hc
          rw [mul_one] at hmm
          exact hmm

/-- **Composite second-order remainder** (proof step for DMC.7):
`Trap_m(x,y) - ∫₀ᵃ f ≤ (ah²/12)(x-y)²` for `x, y ≥ 0`. -/
theorem trap_error_second_order (a h : ℝ) (m : ℕ) (x y : ℝ) (ha : 0 < a) (hm : m ≠ 0)
    (hcal : (m : ℝ) * h = a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    trapSum a h m x y - ∫ s in (0 : ℝ)..a, clockKernel a x y s
      ≤ a * (h * h) * ((x - y) * (x - y)) / 12 := by
  have hh : 0 < h := by
    have hm' : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    nlinarith
  have hdiff : trapSum a h m x y - ∫ s in (0 : ℝ)..a, clockKernel a x y s
      = ∑ j ∈ Finset.range m,
          (h / 2 * (clockKernel a x y ((j : ℝ) * h) + clockKernel a x y ((j : ℝ) * h + h))
            - ∫ s in ((j : ℝ) * h)..((j : ℝ) * h + h), clockKernel a x y s) := by
    rw [trapSum_eq_panels a h m x y hm, integral_eq_panels a h m x y hcal,
      ← Finset.sum_sub_distrib]
  rw [hdiff]
  have hbound : ∀ j ∈ Finset.range m,
      h / 2 * (clockKernel a x y ((j : ℝ) * h) + clockKernel a x y ((j : ℝ) * h + h))
          - (∫ s in ((j : ℝ) * h)..((j : ℝ) * h + h), clockKernel a x y s)
        ≤ h * h * h * ((x - y) * (x - y)) / 12 := by
    intro j hj
    have hjm : (j : ℝ) + 1 ≤ (m : ℝ) := by
      have := Finset.mem_range.mp hj
      exact_mod_cast this
    apply panel_error_second_order a x y ((j : ℝ) * h) h hh
    · apply clockKernel_le_one hx hy (by positivity)
      nlinarith
    · apply clockKernel_le_one hx hy (by positivity)
      nlinarith
  refine (Finset.sum_le_sum hbound).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc (m : ℝ) * (h * h * h * ((x - y) * (x - y)) / 12)
      = ((m : ℝ) * h) * (h * h) * ((x - y) * (x - y)) / 12 := by ring
    _ = a * (h * h) * ((x - y) * (x - y)) / 12 := by rw [hcal]

end Trapezoid

/-! ### Shared spectral toolkit

Sandwich and quadratic-form lemmas for `spectralFunction`, reused by the
Gibbs-incidence, Duhamel, split-clock and positive-time records below. -/

section MatrixTools

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Explicit sandwich form of the spectral calculus. -/
theorem spectralFunction_sandwich {S : Matrix n n ℂ} (hS : S.IsHermitian) (f : ℝ → ℝ) :
    spectralFunction hS f
      = (hS.eigenvectorUnitary : Matrix n n ℂ)
        * diagonal (fun i => (f (hS.eigenvalues i) : ℂ))
        * (hS.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  unfold spectralFunction
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rfl

/-- A spectral function is Hermitian. -/
theorem spectralFunction_isHermitian {S : Matrix n n ℂ} (hS : S.IsHermitian) (f : ℝ → ℝ) :
    (spectralFunction hS f).IsHermitian := by
  have h : (spectralFunction hS f)ᴴ = spectralFunction hS f := by
    rw [spectralFunction_sandwich, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, diagonal_conjTranspose]
    have hdiag : star (fun i => (f (hS.eigenvalues i) : ℂ))
        = fun i => (f (hS.eigenvalues i) : ℂ) := by
      funext i
      exact Complex.conj_ofReal _
    rw [hdiag, Matrix.mul_assoc]
  exact h

/-- The squared eigencoordinate weights of a vector. -/
noncomputable def eigWeight {S : Matrix n n ℂ} (hS : S.IsHermitian) (v : n → ℂ) (i : n) :
    ℝ :=
  Complex.normSq (((hS.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ v) i)

/-- Eigencoordinate weights are nonnegative. -/
theorem eigWeight_nonneg {S : Matrix n n ℂ} (hS : S.IsHermitian) (v : n → ℂ) (i : n) :
    0 ≤ eigWeight hS v i := Complex.normSq_nonneg _

/-- Quadratic form of a spectral function in eigencoordinates:
`⟨v, f(S)v⟩ = ∑ᵢ f(λᵢ)|wᵢ|²` with `w = U*v`. -/
theorem dotProduct_spectralFunction {S : Matrix n n ℂ} (hS : S.IsHermitian) (f : ℝ → ℝ)
    (v : n → ℂ) :
    star v ⬝ᵥ (spectralFunction hS f *ᵥ v)
      = ((∑ i, f (hS.eigenvalues i) * eigWeight hS v i : ℝ) : ℂ) := by
  have h1 : spectralFunction hS f *ᵥ v
      = (hS.eigenvectorUnitary : Matrix n n ℂ)
          *ᵥ (diagonal (fun i => (f (hS.eigenvalues i) : ℂ))
            *ᵥ ((hS.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ v)) := by
    rw [spectralFunction_sandwich, ← mulVec_mulVec, ← mulVec_mulVec]
  rw [h1, dotProduct_mulVec]
  have h2 : star v ᵥ* (hS.eigenvectorUnitary : Matrix n n ℂ)
      = star ((hS.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ v) := by
    rw [star_mulVec, conjTranspose_conjTranspose]
  rw [h2]
  unfold dotProduct eigWeight
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal, Pi.star_apply]
  calc star (((hS.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ v) i)
        * ((f (hS.eigenvalues i) : ℂ) * ((hS.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ v) i)
      = (f (hS.eigenvalues i) : ℂ)
        * (((hS.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ v) i
          * star (((hS.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ v) i)) := by ring
    _ = (f (hS.eigenvalues i) : ℂ)
        * ((Complex.normSq (((hS.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ v) i) : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj]
    _ = ((f (hS.eigenvalues i)
        * Complex.normSq (((hS.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ v) i) : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul]

/-- Compression of a quadratic form through a source map. -/
theorem dotProduct_compress {k e : Type*} [Fintype k] [Fintype e] (Ψ : Matrix k e ℂ)
    (A : Matrix k k ℂ) (x : e → ℂ) :
    star x ⬝ᵥ ((Ψᴴ * A * Ψ) *ᵥ x) = star (Ψ *ᵥ x) ⬝ᵥ (A *ᵥ (Ψ *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

/-- A Hermitian compression is Hermitian. -/
theorem compress_isHermitian {k e : Type*} [Fintype k] [Fintype e] (Ψ : Matrix k e ℂ)
    {A : Matrix k k ℂ} (hA : A.IsHermitian) : (Ψᴴ * A * Ψ).IsHermitian := by
  have h : (Ψᴴ * A * Ψ)ᴴ = Ψᴴ * A * Ψ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hA.eq,
      Matrix.mul_assoc]
  exact h

/-- Finite Jensen floor for the exponential: mean energy at most `E` forces
the delayed mass to dominate `e^{-2tE}` times the base mass. -/
theorem exp_jensen_floor {ι : Type*} [Fintype ι] (c μ : ι → ℝ) (E t : ℝ)
    (hc : ∀ i, 0 ≤ c i) (ht : 0 ≤ t)
    (hmean : ∑ i, μ i * c i ≤ E * ∑ i, c i) :
    Real.exp (-(2 * t) * E) * ∑ i, c i ≤ ∑ i, Real.exp (-(2 * t) * μ i) * c i := by
  rcases eq_or_lt_of_le (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hc i) with hC0 | hCpos
  · have hall : ∀ i ∈ Finset.univ, c i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hc j).mp hC0.symm
    have hz : ∑ i, Real.exp (-(2 * t) * μ i) * c i = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hall i hi, mul_zero]
    rw [hz, ← hC0, mul_zero]
  · set C := ∑ i, c i with hC
    have hCne : C ≠ 0 := ne_of_gt hCpos
    set w := fun i => c i / C with hwdef
    have hw0 : ∀ i ∈ Finset.univ, 0 ≤ w i := fun i _ => div_nonneg (hc i) hCpos.le
    have hw1 : ∑ i, w i = 1 := by
      rw [hwdef]
      rw [← Finset.sum_div, ← hC, div_self hCne]
    have hjen := convexOn_exp.map_sum_le (t := Finset.univ)
      (p := fun i => -(2 * t) * μ i) hw0 hw1 (fun i _ => Set.mem_univ _)
    have hargs : ∑ i, w i • (-(2 * t) * μ i) = -(2 * t) * ((∑ i, μ i * c i) / C) := by
      rw [show -(2 * t) * ((∑ i, μ i * c i) / C) = ∑ i, -(2 * t) / C * (μ i * c i) by
        rw [← Finset.mul_sum]; ring]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hwdef, smul_eq_mul]
      ring
    have hmean' : -(2 * t) * E ≤ -(2 * t) * ((∑ i, μ i * c i) / C) := by
      have hdiv : (∑ i, μ i * c i) / C ≤ E := by
        rw [div_le_iff₀ hCpos]
        rw [hC]
        exact hmean
      nlinarith
    have hrhs : ∑ i, w i • Real.exp (-(2 * t) * μ i)
        = (∑ i, Real.exp (-(2 * t) * μ i) * c i) / C := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hwdef, smul_eq_mul]
      ring
    rw [hargs, hrhs] at hjen
    have hfloor : Real.exp (-(2 * t) * E)
        ≤ (∑ i, Real.exp (-(2 * t) * μ i) * c i) / C :=
      (Real.exp_le_exp.mpr hmean').trans hjen
    calc Real.exp (-(2 * t) * E) * C
        ≤ ((∑ i, Real.exp (-(2 * t) * μ i) * c i) / C) * C :=
          mul_le_mul_of_nonneg_right hfloor hCpos.le
      _ = ∑ i, Real.exp (-(2 * t) * μ i) * c i := by
          field_simp

end MatrixTools

/-! ### `thm:SMST-positive-time-semigroup-floor` — Semigroup floor and collar

Rendering: `H = H* ⪰ 0` is a finite Hermitian matrix with nonnegative
eigenvalues, the semigroup `P_t = e^{-tH}` is the spectral-calculus
exponential `ClockPacket.semi hH (-t)` (identified with the power-series
matrix exponential by `semigroup_is_exp`), `Ψ` is a finite source bank, and
`G₀ = Ψ*Ψ`, `K = Ψ*HΨ`, `G_t = Ψ*e^{-2tH}Ψ` are the literal (PT.1) data.
(PT.3) is proved via the finite Jensen floor for each coefficient vector,
and (PT.4) via the scalar bound `(e^{-tμ}-e^{-sμ})² ≤ |t-s|μ` in the
spectral calculus. -/

section SemigroupFloor

variable {k e : Type*} [Fintype k] [Fintype e] [DecidableEq k]
variable {H : Matrix k k ℂ}

/-- The base source Gram `G₀ = Ψ*Ψ` (PT.1). -/
def gramBase (Ψ : Matrix k e ℂ) : Matrix e e ℂ := Ψᴴ * Ψ

/-- The source-local energy row `K = Ψ*HΨ` (PT.1). -/
def energyRow (H : Matrix k k ℂ) (Ψ : Matrix k e ℂ) : Matrix e e ℂ := Ψᴴ * H * Ψ

/-- The delayed source Gram `G_t = Ψ*e^{-2tH}Ψ` (PT.1). -/
noncomputable def delayedGram (hH : H.IsHermitian) (Ψ : Matrix k e ℂ) (t : ℝ) :
    Matrix e e ℂ :=
  Ψᴴ * ClockPacket.semi hH (-(2 * t)) * Ψ

/-- The delayed semigroup is the power-series matrix exponential:
`P_t = e^{-tH}` literally. -/
theorem semigroup_is_exp (hH : H.IsHermitian) (t : ℝ) :
    ClockPacket.semi hH (-t) = NormedSpace.exp ((-t) • H) :=
  ClockPacket.semi_eq_exp hH (-t)

/-- **`thm:SMST-positive-time-semigroup-floor` (PT.2 ⟹ PT.3)**: if
`K ⪯ E⋆G₀` then `G_t ⪰ e^{-2tE⋆}G₀` for every `t ≥ 0`. -/
theorem semigroup_floor (hH : H.IsHermitian) (Ψ : Matrix k e ℂ) (Estar t : ℝ)
    (ht : 0 ≤ t)
    (hrow : ((Estar : ℂ) • gramBase Ψ - energyRow H Ψ).PosSemidef) :
    (delayedGram hH Ψ t
      - ((Real.exp (-(2 * t * Estar)) : ℝ) : ℂ) • gramBase Ψ).PosSemidef := by
  have hGspec : gramBase Ψ = Ψᴴ * spectralFunction hH (fun _ => 1) * Ψ := by
    unfold gramBase
    rw [spectralFunction_const, Complex.ofReal_one, one_smul, Matrix.mul_one]
  have hKspec : energyRow H Ψ = Ψᴴ * spectralFunction hH id * Ψ := by
    unfold energyRow
    rw [spectralFunction_id]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- Hermitian part
    have h1 : (delayedGram hH Ψ t).IsHermitian :=
      compress_isHermitian Ψ (spectralFunction_isHermitian hH _)
    have h2 : (gramBase Ψ).IsHermitian := by
      rw [hGspec]
      exact compress_isHermitian Ψ (spectralFunction_isHermitian hH _)
    have h3 : (((Real.exp (-(2 * t * Estar)) : ℝ) : ℂ) • gramBase Ψ)ᴴ
        = ((Real.exp (-(2 * t * Estar)) : ℝ) : ℂ) • gramBase Ψ := by
      rw [conjTranspose_smul, h2.eq, Complex.star_def, Complex.conj_ofReal]
    have h4 : (delayedGram hH Ψ t
        - ((Real.exp (-(2 * t * Estar)) : ℝ) : ℂ) • gramBase Ψ)ᴴ
        = delayedGram hH Ψ t - ((Real.exp (-(2 * t * Estar)) : ℝ) : ℂ) • gramBase Ψ := by
      rw [conjTranspose_sub, h1.eq, h3]
    exact h4
  · intro x
    have hformG : star x ⬝ᵥ (gramBase Ψ *ᵥ x)
        = ((∑ i, 1 * eigWeight hH (Ψ *ᵥ x) i : ℝ) : ℂ) := by
      rw [hGspec, dotProduct_compress, dotProduct_spectralFunction]
    have hformK : star x ⬝ᵥ (energyRow H Ψ *ᵥ x)
        = ((∑ i, hH.eigenvalues i * eigWeight hH (Ψ *ᵥ x) i : ℝ) : ℂ) := by
      rw [hKspec, dotProduct_compress, dotProduct_spectralFunction]
      rfl
    have hformT : star x ⬝ᵥ (delayedGram hH Ψ t *ᵥ x)
        = ((∑ i, Real.exp (-(2 * t) * hH.eigenvalues i)
            * eigWeight hH (Ψ *ᵥ x) i : ℝ) : ℂ) := by
      unfold delayedGram ClockPacket.semi
      rw [dotProduct_compress, dotProduct_spectralFunction]
    -- extract the real mean-energy inequality from PT.2
    have hrow2 := hrow.dotProduct_mulVec_nonneg x
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      hformG, hformK, smul_eq_mul] at hrow2
    have hcast : (Estar : ℂ) * ((∑ i, 1 * eigWeight hH (Ψ *ᵥ x) i : ℝ) : ℂ)
        - ((∑ i, hH.eigenvalues i * eigWeight hH (Ψ *ᵥ x) i : ℝ) : ℂ)
        = ((Estar * (∑ i, 1 * eigWeight hH (Ψ *ᵥ x) i)
            - ∑ i, hH.eigenvalues i * eigWeight hH (Ψ *ᵥ x) i : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast] at hrow2
    have hone : ∑ i, 1 * eigWeight hH (Ψ *ᵥ x) i = ∑ i, eigWeight hH (Ψ *ᵥ x) i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [one_mul]
    have hmean : ∑ i, hH.eigenvalues i * eigWeight hH (Ψ *ᵥ x) i
        ≤ Estar * ∑ i, eigWeight hH (Ψ *ᵥ x) i := by
      have hre := (Complex.zero_le_real).mp hrow2
      rw [hone] at hre
      linarith
    have hjen := exp_jensen_floor (fun i => eigWeight hH (Ψ *ᵥ x) i) hH.eigenvalues
      Estar t (fun i => eigWeight_nonneg hH _ i) ht hmean
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      hformG, hformT, smul_eq_mul]
    have hcast2 : ((∑ i, Real.exp (-(2 * t) * hH.eigenvalues i)
          * eigWeight hH (Ψ *ᵥ x) i : ℝ) : ℂ)
        - ((Real.exp (-(2 * t * Estar)) : ℝ) : ℂ)
          * ((∑ i, 1 * eigWeight hH (Ψ *ᵥ x) i : ℝ) : ℂ)
        = (((∑ i, Real.exp (-(2 * t) * hH.eigenvalues i) * eigWeight hH (Ψ *ᵥ x) i)
            - Real.exp (-(2 * t * Estar))
              * (∑ i, 1 * eigWeight hH (Ψ *ᵥ x) i) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast2]
    apply Complex.zero_le_real.mpr
    rw [hone, show -(2 * t * Estar) = -(2 * t) * Estar by ring]
    linarith

/-- Scalar collar bound: `(e^{-tμ} - e^{-sμ})² ≤ |t-s|·μ` for `t, s, μ ≥ 0`. -/
theorem exp_collar_sq_le {t s μ : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hμ : 0 ≤ μ) :
    (Real.exp (-(t * μ)) - Real.exp (-(s * μ))) ^ 2 ≤ |t - s| * μ := by
  have key : ∀ p q : ℝ, 0 ≤ p → p ≤ q →
      (Real.exp (-(q * μ)) - Real.exp (-(p * μ))) ^ 2 ≤ (q - p) * μ := by
    intro p q hp hpq
    set d := Real.exp (-(p * μ)) - Real.exp (-(q * μ)) with hd
    have hd0 : 0 ≤ d := by
      rw [hd, sub_nonneg]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hd1 : d ≤ 1 := by
      have h1 : Real.exp (-(p * μ)) ≤ 1 := by
        rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
        apply Real.exp_le_exp.mpr
        nlinarith
      have h2 : 0 < Real.exp (-(q * μ)) := Real.exp_pos _
      rw [hd]
      linarith
    have hdD : d ≤ (q - p) * μ := by
      have hsplit : d = Real.exp (-(p * μ)) * (1 - Real.exp (-((q - p) * μ))) := by
        rw [hd, mul_sub, mul_one, ← Real.exp_add]
        congr 2
        ring
      have hexp1 : Real.exp (-(p * μ)) ≤ 1 := by
        rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
        apply Real.exp_le_exp.mpr
        nlinarith
      have hlin : 1 - Real.exp (-((q - p) * μ)) ≤ (q - p) * μ := by
        have := Real.add_one_le_exp (-((q - p) * μ))
        linarith
      have hnn : 0 ≤ 1 - Real.exp (-((q - p) * μ)) := by
        have h2 : Real.exp (-((q - p) * μ)) ≤ 1 := by
          rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
          apply Real.exp_le_exp.mpr
          nlinarith
        linarith
      calc d = Real.exp (-(p * μ)) * (1 - Real.exp (-((q - p) * μ))) := hsplit
        _ ≤ 1 * (1 - Real.exp (-((q - p) * μ))) :=
            mul_le_mul_of_nonneg_right hexp1 hnn
        _ = 1 - Real.exp (-((q - p) * μ)) := one_mul _
        _ ≤ (q - p) * μ := hlin
    have hsq : (Real.exp (-(q * μ)) - Real.exp (-(p * μ))) ^ 2 = d * d := by
      rw [hd]
      ring
    rw [hsq]
    nlinarith
  rcases le_total s t with hst | hst
  · rw [abs_of_nonneg (by linarith)]
    exact key s t hs hst
  · rw [abs_of_nonpos (by linarith)]
    have hkey := key t s ht hst
    calc (Real.exp (-(t * μ)) - Real.exp (-(s * μ))) ^ 2
        = (Real.exp (-(s * μ)) - Real.exp (-(t * μ))) ^ 2 := by ring
      _ ≤ (s - t) * μ := hkey
      _ = -(t - s) * μ := by ring

/-- **`thm:SMST-positive-time-semigroup-floor` (PT.4)**: the collar modulus
`(P_tΨ - P_sΨ)*(P_tΨ - P_sΨ) ⪯ |t-s|·K` for `t, s ≥ 0` and `H ⪰ 0`. -/
theorem semigroup_collar (hH : H.IsHermitian) (hpos : ∀ i, 0 ≤ hH.eigenvalues i)
    (Ψ : Matrix k e ℂ) (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    (((|t - s| : ℝ) : ℂ) • energyRow H Ψ
      - (ClockPacket.semi hH (-t) * Ψ - ClockPacket.semi hH (-s) * Ψ)ᴴ
        * (ClockPacket.semi hH (-t) * Ψ - ClockPacket.semi hH (-s) * Ψ)).PosSemidef := by
  have hdiff : ClockPacket.semi hH (-t) * Ψ - ClockPacket.semi hH (-s) * Ψ
      = spectralFunction hH (fun μ => Real.exp (-t * μ) - Real.exp (-s * μ)) * Ψ := by
    unfold ClockPacket.semi
    rw [spectralFunction_sub, Matrix.sub_mul]
  have hgram : (spectralFunction hH (fun μ => Real.exp (-t * μ) - Real.exp (-s * μ)) * Ψ)ᴴ
      * (spectralFunction hH (fun μ => Real.exp (-t * μ) - Real.exp (-s * μ)) * Ψ)
      = Ψᴴ * spectralFunction hH (fun μ =>
          (Real.exp (-t * μ) - Real.exp (-s * μ)) * (Real.exp (-t * μ) - Real.exp (-s * μ)))
        * Ψ := by
    rw [conjTranspose_mul, (spectralFunction_isHermitian hH _).eq, Matrix.mul_assoc,
      ← Matrix.mul_assoc (spectralFunction hH _), spectralFunction_mul]
    simp only [Matrix.mul_assoc]
  have hsmul : ((|t - s| : ℝ) : ℂ) • energyRow H Ψ
      = Ψᴴ * spectralFunction hH (fun μ => |t - s| * id μ) * Ψ := by
    unfold energyRow
    rw [spectralFunction_smul, spectralFunction_id, Matrix.mul_smul, Matrix.smul_mul]
  rw [hdiff, hgram, hsmul, ← Matrix.sub_mul, ← Matrix.mul_sub, ← spectralFunction_sub]
  apply Matrix.PosSemidef.conjTranspose_mul_mul_same
  apply spectralFunction_posSemidef
  intro i
  have hμ := hpos i
  have hkey := exp_collar_sq_le ht hs hμ
  simp only [id]
  have hrw : Real.exp (-t * hH.eigenvalues i) = Real.exp (-(t * hH.eigenvalues i)) := by
    rw [neg_mul]
  have hrw2 : Real.exp (-s * hH.eigenvalues i) = Real.exp (-(s * hH.eigenvalues i)) := by
    rw [neg_mul]
  rw [hrw, hrw2]
  nlinarith [sq_nonneg (Real.exp (-(t * hH.eigenvalues i))
    - Real.exp (-(s * hH.eigenvalues i)))]

end SemigroupFloor


end SMST05

end NCG
