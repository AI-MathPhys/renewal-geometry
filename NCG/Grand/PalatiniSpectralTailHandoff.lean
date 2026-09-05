/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Palatini spectral-tail handoff

Standalone, content-named proof of `thm:SMFS-Palatini-tail`: the sharp
Hilbert-scale Pythagoras estimate, its convergence consequence, and the unit
escaping-variation witness.
-/

open Finset Filter Topology

noncomputable section

namespace NCG
namespace PalatiniSpectralTailHandoff

variable (lam : ℕ → ℝ) (sigma : ℝ)

/-- The determining screen `P_Λ`. -/
def screen (Lam : ℝ) (r : ℕ → ℝ) : ℕ → ℝ :=
  fun i => if lam i ≤ Lam then r i else 0

/-- The escaping spectral tail `(I-P_Λ)r`. -/
def tail (Lam : ℝ) (r : ℕ → ℝ) : ℕ → ℝ :=
  fun i => if lam i ≤ Lam then 0 else r i

/-- The base Hilbert norm in spectral coordinates. -/
def vNorm (r : ℕ → ℝ) : ℝ := Real.sqrt (∑' i, r i ^ 2)

/-- The squared positive-regularity norm. -/
def vSigmaSq (r : ℕ → ℝ) : ℝ :=
  ∑' i, (1 + lam i) ^ sigma * r i ^ 2

theorem sq_split (Lam : ℝ) (r : ℕ → ℝ) (i : ℕ) :
    r i ^ 2 = screen lam Lam r i ^ 2 + tail lam Lam r i ^ 2 := by
  unfold screen tail
  split_ifs <;> ring

theorem screen_sq_le (Lam : ℝ) (r : ℕ → ℝ) (i : ℕ) :
    screen lam Lam r i ^ 2 ≤ r i ^ 2 := by
  unfold screen
  split_ifs
  · exact le_rfl
  · simpa using sq_nonneg (r i)

theorem tail_sq_le (Lam : ℝ) (r : ℕ → ℝ) (i : ℕ) :
    tail lam Lam r i ^ 2 ≤ r i ^ 2 := by
  unfold tail
  split_ifs
  · simpa using sq_nonneg (r i)
  · exact le_rfl

theorem one_le_weight (hlam : ∀ i, 0 ≤ lam i) (hs : 0 ≤ sigma) (i : ℕ) :
    (1 : ℝ) ≤ (1 + lam i) ^ sigma := by
  calc
    (1 : ℝ) = 1 ^ sigma := (Real.one_rpow _).symm
    _ ≤ (1 + lam i) ^ sigma :=
      Real.rpow_le_rpow zero_le_one (by linarith [hlam i]) hs

theorem summable_sq_of_weighted
    (hlam : ∀ i, 0 ≤ lam i) (hs : 0 ≤ sigma)
    {r : ℕ → ℝ} (h : Summable fun i => (1 + lam i) ^ sigma * r i ^ 2) :
    Summable fun i => r i ^ 2 := by
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) h
  nlinarith [one_le_weight lam sigma hlam hs i, sq_nonneg (r i)]

/-- **FS.48.** A finite determining-screen bound and a uniform positive
Hilbert-scale bound control the complete assembled residual. -/
theorem spectral_tail_bound
    (hlam : ∀ i, 0 ≤ lam i) (hs : 0 < sigma)
    {Lam M48 eps : ℝ} (hLam : 0 ≤ Lam) (r : ℕ → ℝ)
    (hsum : Summable fun i => (1 + lam i) ^ sigma * r i ^ 2)
    (hM : Real.sqrt (vSigmaSq lam sigma r) ≤ M48)
    (heps : vNorm (screen lam Lam r) ≤ eps) :
    vNorm r ≤ Real.sqrt (eps ^ 2 + (1 + Lam) ^ (-sigma) * M48 ^ 2) := by
  have hr2 : Summable fun i => r i ^ 2 :=
    summable_sq_of_weighted lam sigma hlam hs.le hsum
  have hscr : Summable fun i => screen lam Lam r i ^ 2 :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _)
      (screen_sq_le lam Lam r) hr2
  have htl : Summable fun i => tail lam Lam r i ^ 2 :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _)
      (tail_sq_le lam Lam r) hr2
  have hsplit : (∑' i, r i ^ 2) =
      (∑' i, screen lam Lam r i ^ 2) + ∑' i, tail lam Lam r i ^ 2 := by
    rw [← hscr.tsum_add htl]
    exact tsum_congr (sq_split lam Lam r)
  have hwpos : (0 : ℝ) < (1 + Lam) ^ sigma :=
    Real.rpow_pos_of_pos (by linarith) sigma
  have hneg : (1 + Lam : ℝ) ^ (-sigma) = ((1 + Lam) ^ sigma)⁻¹ :=
    Real.rpow_neg (by linarith) sigma
  have hnegpos : (0 : ℝ) < (1 + Lam) ^ (-sigma) := by
    rw [hneg]
    exact inv_pos.mpr hwpos
  have htailb : ∀ i, tail lam Lam r i ^ 2 ≤
      (1 + Lam) ^ (-sigma) * ((1 + lam i) ^ sigma * r i ^ 2) := by
    intro i
    unfold tail
    split_ifs with h
    · simpa using mul_nonneg hnegpos.le
        (mul_nonneg
          (Real.rpow_nonneg (x := 1 + lam i) (by linarith [hlam i]) sigma)
          (sq_nonneg (r i)))
    · push Not at h
      have hbase : (1 + Lam : ℝ) ^ sigma ≤ (1 + lam i) ^ sigma :=
        Real.rpow_le_rpow (by linarith) (by linarith) hs.le
      have h1 : (1 : ℝ) ≤
          (1 + Lam) ^ (-sigma) * (1 + lam i) ^ sigma := by
        rw [hneg, inv_mul_eq_div, le_div_iff₀ hwpos, one_mul]
        exact hbase
      nlinarith [sq_nonneg (r i)]
  have htailsum : (∑' i, tail lam Lam r i ^ 2) ≤
      (1 + Lam) ^ (-sigma) * vSigmaSq lam sigma r := by
    calc
      (∑' i, tail lam Lam r i ^ 2) ≤
          ∑' i, (1 + Lam) ^ (-sigma) *
            ((1 + lam i) ^ sigma * r i ^ 2) :=
        htl.tsum_le_tsum htailb (hsum.mul_left _)
      _ = (1 + Lam) ^ (-sigma) * vSigmaSq lam sigma r := by
        rw [vSigmaSq, tsum_mul_left]
  have hSnn : 0 ≤ vSigmaSq lam sigma r :=
    tsum_nonneg fun i => mul_nonneg
      (Real.rpow_pos_of_pos (by linarith [hlam i]) sigma).le (sq_nonneg _)
  have hM0 : 0 ≤ M48 := le_trans (Real.sqrt_nonneg _) hM
  have hM2 : vSigmaSq lam sigma r ≤ M48 ^ 2 := by
    nlinarith [Real.sq_sqrt hSnn, Real.sqrt_nonneg (vSigmaSq lam sigma r)]
  have hscrnn : 0 ≤ ∑' i, screen lam Lam r i ^ 2 :=
    tsum_nonneg fun i => sq_nonneg _
  have heps0 : 0 ≤ eps := le_trans (Real.sqrt_nonneg _) heps
  have heps2 : (∑' i, screen lam Lam r i ^ 2) ≤ eps ^ 2 := by
    have h := heps
    unfold vNorm at h
    nlinarith [Real.sq_sqrt hscrnn,
      Real.sqrt_nonneg (∑' i, screen lam Lam r i ^ 2)]
  have hfinal : (∑' i, r i ^ 2) ≤
      eps ^ 2 + (1 + Lam) ^ (-sigma) * M48 ^ 2 := by
    have h3 : (1 + Lam) ^ (-sigma) * vSigmaSq lam sigma r ≤
        (1 + Lam) ^ (-sigma) * M48 ^ 2 :=
      mul_le_mul_of_nonneg_left hM2 hnegpos.le
    linarith [hsplit, htailsum, heps2]
  unfold vNorm
  exact Real.sqrt_le_sqrt hfinal

/-- Vanishing screen error and exhausting spectral cutoff force the complete
assembled Palatini residual to vanish. -/
theorem spectral_tail_convergence
    (hlam : ∀ i, 0 ≤ lam i) (hs : 0 < sigma)
    {M48 : ℝ} (r : ℕ → ℕ → ℝ) (eps Lams : ℕ → ℝ)
    (hLam0 : ∀ n, 0 ≤ Lams n)
    (hsum : ∀ n, Summable fun i => (1 + lam i) ^ sigma * r n i ^ 2)
    (hM : ∀ n, Real.sqrt (vSigmaSq lam sigma (r n)) ≤ M48)
    (heps : ∀ n, vNorm (screen lam (Lams n) (r n)) ≤ eps n)
    (heps0 : Tendsto eps atTop (nhds 0))
    (hLamtop : Tendsto Lams atTop atTop) :
    Tendsto (fun n => vNorm (r n)) atTop (nhds 0) := by
  have hb : ∀ n, vNorm (r n) ≤
      Real.sqrt (eps n ^ 2 + (1 + Lams n) ^ (-sigma) * M48 ^ 2) :=
    fun n => spectral_tail_bound lam sigma hlam hs (hLam0 n)
      (r n) (hsum n) (hM n) (heps n)
  have hc : Tendsto (fun n => (1 + Lams n) ^ (-sigma)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n => 1 + Lams n) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 hLamtop
    exact (tendsto_rpow_neg_atTop hs).comp h1
  have hinner : Tendsto
      (fun n => eps n ^ 2 + (1 + Lams n) ^ (-sigma) * M48 ^ 2)
      atTop (nhds 0) := by
    have h1 := heps0.pow 2
    have h2 := hc.mul_const (M48 ^ 2)
    simpa using h1.add h2
  have hsq : Tendsto
      (fun n => Real.sqrt
        (eps n ^ 2 + (1 + Lams n) ^ (-sigma) * M48 ^ 2))
      atTop (nhds 0) := by
    simpa using hinner.sqrt
  exact squeeze_zero (fun n => Real.sqrt_nonneg _) hb hsq

/-- **FS.49.** Failure of complete residual convergence despite vanishing
screened residuals returns unit variations beyond growing screens with a
uniform positive pairing. -/
theorem escaping_variation_witness
    (r : ℕ → ℕ → ℝ) (Lams : ℕ → ℝ)
    (hr2 : ∀ n, Summable fun i => r n i ^ 2)
    (hscr : Tendsto (fun n => vNorm (screen lam (Lams n) (r n)))
      atTop (nhds 0))
    (hfail : ¬ Tendsto (fun n => vNorm (r n)) atTop (nhds 0)) :
    ∃ epsStar > (0 : ℝ), ∃ᶠ n in atTop, ∃ v : ℕ → ℝ,
      vNorm v = 1 ∧ (∀ i, lam i ≤ Lams n → v i = 0) ∧
        epsStar ≤ ∑' i, r n i * v i := by
  rw [Metric.tendsto_atTop] at hfail
  push Not at hfail
  obtain ⟨eps0, heps0, hfr⟩ := hfail
  have hfreq : ∃ᶠ n in atTop, eps0 ≤ vNorm (r n) := by
    rw [frequently_atTop]
    intro N
    obtain ⟨n, hn, hd⟩ := hfr N
    refine ⟨n, hn, ?_⟩
    rw [Real.dist_0_eq_abs] at hd
    unfold vNorm at hd
    rw [abs_of_nonneg (Real.sqrt_nonneg _)] at hd
    exact hd
  have hev : ∀ᶠ n in atTop,
      vNorm (screen lam (Lams n) (r n)) < eps0 / 2 :=
    hscr.eventually_lt_const (by positivity)
  refine ⟨eps0 / 2, by positivity, ?_⟩
  refine (hfreq.and_eventually hev).mono ?_
  rintro n ⟨h1, h2⟩
  have hscrsum : Summable fun i => screen lam (Lams n) (r n) i ^ 2 :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _)
      (screen_sq_le lam (Lams n) (r n)) (hr2 n)
  have htlsum : Summable fun i => tail lam (Lams n) (r n) i ^ 2 :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _)
      (tail_sq_le lam (Lams n) (r n)) (hr2 n)
  set S : ℝ := ∑' i, tail lam (Lams n) (r n) i ^ 2 with hSdef
  set sS : ℝ := ∑' i, screen lam (Lams n) (r n) i ^ 2 with hsSdef
  have hSnn : 0 ≤ S := tsum_nonneg fun i => sq_nonneg _
  have hsSnn : 0 ≤ sS := tsum_nonneg fun i => sq_nonneg _
  have hsplit : (∑' i, r n i ^ 2) = sS + S := by
    rw [hSdef, hsSdef, ← hscrsum.tsum_add htlsum]
    exact tsum_congr (sq_split lam (Lams n) (r n))
  have hlow : eps0 ^ 2 ≤ sS + S := by
    have h := h1
    unfold vNorm at h
    rw [hsplit] at h
    nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ sS + S)]
  have hup : sS < eps0 ^ 2 / 4 := by
    have h := h2
    unfold vNorm at h
    nlinarith [Real.sq_sqrt hsSnn, Real.sqrt_nonneg sS]
  have hS34 : eps0 ^ 2 / 4 ≤ S := by linarith
  set c : ℝ := Real.sqrt S with hcdef
  have hclow : eps0 / 2 ≤ c := by
    rw [hcdef]
    rw [show eps0 / 2 = Real.sqrt ((eps0 / 2) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hcpos : 0 < c := lt_of_lt_of_le (by positivity) hclow
  have hcsq : c ^ 2 = S := Real.sq_sqrt hSnn
  refine ⟨fun i => c⁻¹ * tail lam (Lams n) (r n) i, ?_, ?_, ?_⟩
  · unfold vNorm
    have hcongr :
        (∑' i, (c⁻¹ * tail lam (Lams n) (r n) i) ^ 2) = c⁻¹ ^ 2 * S := by
      rw [hSdef, ← tsum_mul_left]
      exact tsum_congr fun i => by ring
    rw [hcongr, ← hcsq]
    rw [show c⁻¹ ^ 2 * c ^ 2 = 1 by field_simp]
    exact Real.sqrt_one
  · intro i hi
    change c⁻¹ * (if lam i ≤ Lams n then 0 else r n i) = 0
    rw [if_pos hi, mul_zero]
  · have hpt : ∀ i, r n i * (c⁻¹ * tail lam (Lams n) (r n) i) =
        c⁻¹ * tail lam (Lams n) (r n) i ^ 2 := by
      intro i
      unfold tail
      split_ifs <;> ring
    calc
      eps0 / 2 ≤ c := hclow
      _ = c⁻¹ * S := by rw [← hcsq]; field_simp
      _ = ∑' i, c⁻¹ * tail lam (Lams n) (r n) i ^ 2 := by
        rw [hSdef, tsum_mul_left]
      _ = ∑' i, r n i * (c⁻¹ * tail lam (Lams n) (r n) i) :=
        (tsum_congr hpt).symm

end PalatiniSpectralTailHandoff
end NCG
