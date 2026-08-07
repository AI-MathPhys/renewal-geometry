/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Operational Sobolev, Poincaré, and Weyl bounds
  (`thm:operational-Sobolev-Weyl`, Gran-Tensor manuscript)

* `holder_l2_l6_cube`: the weighted `L² ≤ V^{2/3}·L⁶` Hölder
  step, stated cubed to stay polynomial —
  `(Σ μf²)³ ≤ (Σ μf⁶)·(Σ μ)²` (double Cauchy–Schwarz);
* `poincare_from_sobolev_cube`: the boxed Poincaré constant —
  the Sobolev bound `Σμf⁶ ≤ (C_S·ℰ)³` and the volume bound
  `Σμ ≤ V` chain to `(Σμf²)³ ≤ (C_S·ℰ)³·V²`, the cubed form of
  `‖f‖² ≤ C_P·ℰ` with `C_P = C_S·V^{2/3}`;
* `spectral_tail_bound`: the boxed compact-screen estimate in
  the diagonal spectral rendering — the mass of `f` above
  spectral level `R` is at most `R⁻¹` times the Dirichlet
  energy, `Σ_{λᵢ>R} μᵢfᵢ² ≤ R⁻¹·Σ λᵢμᵢfᵢ²`;
* `poincare_floor_positive`: the boxed spectral floor
  `I_*²/(128·D_*·V_*^{2/3}) > 0`.

Rendering disclosed: the discrete co-area/cut-inequality
derivation of the `L⁶` Sobolev bound itself (with the constant
`C_S = 128 D_*/I_*²`) and the Weyl eigenvalue-packing count
`N_X(R) ≤ 1 + 4e^{3/2}V_*(C_S R)^{3/2}` are the manuscript's
isoperimetric layer; the Hölder chain, the Poincaré constant
bookkeeping, the spectral tail bound, and the floor positivity
are proved here.
-/

namespace NCG

variable {ι : Type*} [Fintype ι]

/-- Weighted `L² ≤ V^{2/3}·L⁶` Hölder step, cubed:
`(Σ μf²)³ ≤ (Σ μf⁶)·(Σ μ)²` — by double Cauchy–Schwarz. -/
theorem holder_l2_l6_cube (μ f : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    (∑ i, μ i * f i ^ 2) ^ 3
      ≤ (∑ i, μ i * f i ^ 6) * (∑ i, μ i) ^ 2 := by
  set g : ι → ℝ := fun i => Real.sqrt (μ i) with hg
  have hg2 : ∀ i, g i ^ 2 = μ i := fun i => Real.sq_sqrt (hμ i)
  have hcs1 : (∑ i, μ i * f i ^ 2) ^ 2
      ≤ (∑ i, μ i * f i ^ 4) * (∑ i, μ i) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => g i * f i ^ 2) g
    calc (∑ i, μ i * f i ^ 2) ^ 2
        = (∑ i, (g i * f i ^ 2) * g i) ^ 2 := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show (g i * f i ^ 2) * g i
            = g i ^ 2 * f i ^ 2 by ring, hg2]
      _ ≤ (∑ i, (g i * f i ^ 2) ^ 2) * (∑ i, g i ^ 2) := h
      _ = (∑ i, μ i * f i ^ 4) * (∑ i, μ i) := by
          congr 1
          · refine Finset.sum_congr rfl fun i _ => ?_
            rw [show (g i * f i ^ 2) ^ 2
              = g i ^ 2 * f i ^ 4 by ring, hg2]
          · exact Finset.sum_congr rfl fun i _ => hg2 i
  have hcs2 : (∑ i, μ i * f i ^ 4) ^ 2
      ≤ (∑ i, μ i * f i ^ 6) * (∑ i, μ i * f i ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => g i * f i ^ 3) (fun i => g i * f i)
    calc (∑ i, μ i * f i ^ 4) ^ 2
        = (∑ i, (g i * f i ^ 3) * (g i * f i)) ^ 2 := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show (g i * f i ^ 3) * (g i * f i)
            = g i ^ 2 * f i ^ 4 by ring, hg2]
      _ ≤ (∑ i, (g i * f i ^ 3) ^ 2)
          * (∑ i, (g i * f i) ^ 2) := h
      _ = (∑ i, μ i * f i ^ 6) * (∑ i, μ i * f i ^ 2) := by
          congr 1
          · refine Finset.sum_congr rfl fun i _ => ?_
            rw [show (g i * f i ^ 3) ^ 2
              = g i ^ 2 * f i ^ 6 by ring, hg2]
          · refine Finset.sum_congr rfl fun i _ => ?_
            rw [show (g i * f i) ^ 2
              = g i ^ 2 * f i ^ 2 by ring, hg2]
  have ha : 0 ≤ ∑ i, μ i * f i ^ 2 :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (hμ i) (by positivity)
  have hc : 0 ≤ ∑ i, μ i * f i ^ 6 :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (hμ i) (by positivity)
  have hV : 0 ≤ ∑ i, μ i := Finset.sum_nonneg fun i _ => hμ i
  have hsq : ((∑ i, μ i * f i ^ 2) ^ 2) ^ 2
      ≤ ((∑ i, μ i * f i ^ 4) * (∑ i, μ i)) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) hcs1 2
  have hchain : (∑ i, μ i * f i ^ 2) ^ 4
      ≤ ((∑ i, μ i * f i ^ 6) * (∑ i, μ i * f i ^ 2))
        * (∑ i, μ i) ^ 2 := by
    have hstep : ((∑ i, μ i * f i ^ 4) * (∑ i, μ i)) ^ 2
        = (∑ i, μ i * f i ^ 4) ^ 2 * (∑ i, μ i) ^ 2 := by
      ring
    have hstep2 : (∑ i, μ i * f i ^ 4) ^ 2 * (∑ i, μ i) ^ 2
        ≤ ((∑ i, μ i * f i ^ 6) * (∑ i, μ i * f i ^ 2))
          * (∑ i, μ i) ^ 2 :=
      mul_le_mul_of_nonneg_right hcs2 (sq_nonneg _)
    calc (∑ i, μ i * f i ^ 2) ^ 4
        = ((∑ i, μ i * f i ^ 2) ^ 2) ^ 2 := by ring
      _ ≤ ((∑ i, μ i * f i ^ 4) * (∑ i, μ i)) ^ 2 := hsq
      _ = (∑ i, μ i * f i ^ 4) ^ 2 * (∑ i, μ i) ^ 2 := hstep
      _ ≤ _ := hstep2
  rcases ha.eq_or_lt with ha0 | hapos
  · rw [← ha0]
    simpa using mul_nonneg hc (sq_nonneg (∑ i, μ i))
  · nlinarith [hchain, hapos]

/-- Boxed Poincaré chaining (cubed form): Sobolev
`Σμf⁶ ≤ (C_S·ℰ)³` and volume `Σμ ≤ V` give
`(Σμf²)³ ≤ (C_S·ℰ)³·V²` — i.e. `C_P = C_S·V^{2/3}`. -/
theorem poincare_from_sobolev_cube (μ f : ι → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (CS E V : ℝ) (hV : 0 ≤ V)
    (hsob : ∑ i, μ i * f i ^ 6 ≤ (CS * E) ^ 3)
    (hvol : ∑ i, μ i ≤ V) :
    (∑ i, μ i * f i ^ 2) ^ 3 ≤ (CS * E) ^ 3 * V ^ 2 := by
  refine le_trans (holder_l2_l6_cube μ f hμ) ?_
  have hμsum : 0 ≤ ∑ i, μ i :=
    Finset.sum_nonneg fun i _ => hμ i
  have hsq : (∑ i, μ i) ^ 2 ≤ V ^ 2 := by nlinarith
  have hc : 0 ≤ ∑ i, μ i * f i ^ 6 :=
    Finset.sum_nonneg fun i _ => by
      have := hμ i
      positivity
  nlinarith [sq_nonneg V]

/-- Boxed compact-screen tail bound (diagonal spectral
rendering): the spectral mass above level `R` is dominated by
`R⁻¹` times the Dirichlet energy. -/
theorem spectral_tail_bound (μ f lam : ι → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hlam : ∀ i, 0 ≤ lam i) (R : ℝ)
    (hR : 0 < R) :
    ∑ i ∈ Finset.univ.filter (fun i => R < lam i),
        μ i * f i ^ 2
      ≤ R⁻¹ * ∑ i, lam i * (μ i * f i ^ 2) := by
  have hstep : ∑ i ∈ Finset.univ.filter (fun i => R < lam i),
      μ i * f i ^ 2
      ≤ ∑ i ∈ Finset.univ.filter (fun i => R < lam i),
        R⁻¹ * (lam i * (μ i * f i ^ 2)) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hRi : R < lam i := (Finset.mem_filter.mp hi).2
    have hμf : 0 ≤ μ i * f i ^ 2 := by
      have := hμ i
      positivity
    calc μ i * f i ^ 2
        = R⁻¹ * (R * (μ i * f i ^ 2)) := by
          field_simp
      _ ≤ R⁻¹ * (lam i * (μ i * f i ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_
            (inv_nonneg.mpr hR.le)
          exact mul_le_mul_of_nonneg_right hRi.le hμf
  refine le_trans hstep ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hR.le)
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _) fun i _ _ => ?_
  have := hμ i
  have := hlam i
  positivity

/-- Boxed spectral floor positivity:
`I_*²/(128·D_*·V_*^{2/3}) > 0`. -/
theorem poincare_floor_positive (Istar Dstar Vstar : ℝ)
    (hI : 0 < Istar) (hD : 0 < Dstar) (hV : 0 < Vstar) :
    0 < Istar ^ 2 / (128 * Dstar * Vstar ^ ((2 : ℝ) / 3)) := by
  have hrpow : 0 < Vstar ^ ((2 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hV _
  positivity

end NCG
