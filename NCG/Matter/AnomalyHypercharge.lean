/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Hypercharge ratios, anomaly cancellation, and normalisations
(SM_emergence, Phase 1)

* `hypercharge_ratios` — `theorem:conditional-hypercharge-ratios`:
  gauge-invariant Yukawa incidences, the mixed `SU(2)²U(1)` anomaly
  equation `3Y_Q + Y_L = 0`, and sterile neutrality `Y_ν = 0` force
  `Y_L = -Y_H`, `Y_Q = Y_H/3`, and all derived charges;
  `hypercharge_values` gives the standard panel at `Y_H = 1/2`;
* `anomaly_cancellation` — `corollary:explicit-anomaly-cancellation`:
  the `SU(3)²U(1)`, `SU(2)²U(1)`, mixed gravitational, and cubic
  abelian anomaly equations all hold on the derived charges (physlib
  proves the same conditions in its AnomalyCancellation framework);
* `predictive_gauge_normalisation` —
  `thm:predictive-gauge-normalisation-updated`: `g² I = 2` gives
  `g² = 2/I` and `1/g² = I/2`;
* `one_lapse_reference` — `thm:one-lapse-reference-consolidated`:
  `ε² = 4·log 3·ℓ²` gives `M_ref = 1/ε = M_Pl/√(4 log 3)`;
* `portal_multiplicity_criticality` —
  `thm:portal-multiplicity-criticality-updated`: the effective
  charge `q(1 - C_F/M)` at `C_F = 15/4`: repelling `-7/8` for one
  portal, stabilizing `+1/16` for two, and
  `q_eff = √2/16 > 0` at the canonical critical charge `q² = 2`.
-/

namespace NCG

/-! ## Hypercharge ratios and anomaly cancellation -/

/-- `theorem:conditional-hypercharge-ratios-and-normalisation`: the
Yukawa incidences `Y_u = Y_Q + Y_H`, `Y_d = Y_Q - Y_H`,
`Y_e = Y_L - Y_H`, `Y_ν = Y_L + Y_H`, sterile neutrality `Y_ν = 0`,
and the `SU(2)²U(1)` anomaly `3Y_Q + Y_L = 0` force the ratios
`Y_L = -Y_H` and `Y_Q = Y_H/3`. -/
theorem hypercharge_ratios (YH YQ YL Yu Yd Ye Ynu : ℚ)
    (hu : Yu = YQ + YH) (hd : Yd = YQ - YH)
    (he : Ye = YL - YH) (hnu : Ynu = YL + YH)
    (hsterile : Ynu = 0) (hsu2 : 3 * YQ + YL = 0) :
    YL = -YH ∧ YQ = YH / 3 ∧ Yu = YH / 3 + YH ∧
    Yd = YH / 3 - YH ∧ Ye = -2 * YH := by
  have hL : YL = -YH := by linarith [hnu, hsterile]
  have hQ : YQ = YH / 3 := by linarith [hsu2, hL]
  exact ⟨hL, hQ, by rw [hu, hQ], by rw [hd, hQ],
    by rw [he, hL]; ring⟩

/-- The standard hypercharge panel at the normalisation `Y_H = 1/2`:
`(Y_Q, Y_u, Y_d, Y_L, Y_e, Y_ν) = (1/6, 2/3, -1/3, -1/2, -1, 0)`. -/
theorem hypercharge_values :
    ((1:ℚ)/2) / 3 = 1/6 ∧ (1:ℚ)/6 + 1/2 = 2/3 ∧
    (1:ℚ)/6 - 1/2 = -(1/3) ∧ -((1:ℚ)/2) = -(1/2) ∧
    -((1:ℚ)/2) - 1/2 = -1 ∧ -((1:ℚ)/2) + 1/2 = 0 := by
  norm_num

/-- `corollary:explicit-anomaly-cancellation`: on the derived
charges, the `SU(3)²U(1)`, `SU(2)²U(1)`, mixed gravitational, and
cubic abelian anomaly equations hold identically for one
generation. -/
theorem anomaly_cancellation (YH : ℚ) :
    let YQ := YH / 3
    let YL := -YH
    let Yu := YQ + YH
    let Yd := YQ - YH
    let Ye := YL - YH
    let Ynu := YL + YH
    2 * YQ - Yu - Yd = 0 ∧
    3 * YQ + YL = 0 ∧
    6 * YQ - 3 * Yu - 3 * Yd + 2 * YL - Ye - Ynu = 0 ∧
    6 * YQ ^ 3 - 3 * Yu ^ 3 - 3 * Yd ^ 3 + 2 * YL ^ 3
      - Ye ^ 3 - Ynu ^ 3 = 0 := by
  refine ⟨by ring, by ring, by ring, by ring⟩

/-! ## `thm:predictive-gauge-normalisation-updated` -/

/-- `thm:predictive-gauge-normalisation-updated`: the absolute
one-lapse normalisation `g_a² I_a = 2` determines the couplings:
`g_a² = 2/I_a` and `1/g_a² = I_a/2`. -/
theorem predictive_gauge_normalisation (g2 I : ℝ) (hI : I ≠ 0)
    (hg : g2 * I = 2) :
    g2 = 2 / I ∧ 1 / g2 = I / 2 := by
  have hg2 : g2 = 2 / I := by
    field_simp
    linarith
  refine ⟨hg2, ?_⟩
  rw [hg2]
  have h2 : (2:ℝ) / I ≠ 0 := by
    rw [hg2] at hg
    intro h
    rw [h] at hg
    norm_num at hg
  field_simp

/-! ## `thm:one-lapse-reference-consolidated` -/

/-- `thm:one-lapse-reference-consolidated`: with the calibration
`ε = √(4 log 3)·ℓ_Pl` (i.e. `ε² = 4 log 3 · ℓ²`) and
`M_Pl = 1/ℓ`, the one-lapse reference energy is
`M_ref = 1/ε = M_Pl/√(4 log 3)`. -/
theorem one_lapse_reference (ell : ℝ) (hell : 0 < ell) :
    (Real.sqrt (4 * Real.log 3) * ell) ^ 2
      = 4 * Real.log 3 * ell ^ 2 ∧
    1 / (Real.sqrt (4 * Real.log 3) * ell)
      = (1 / ell) / Real.sqrt (4 * Real.log 3) := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hpos : 0 < 4 * Real.log 3 := by linarith
  constructor
  · rw [mul_pow, Real.sq_sqrt hpos.le]
  · have hs : Real.sqrt (4 * Real.log 3) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hpos)
    field_simp

/-! ## `thm:portal-multiplicity-criticality-updated` -/

/-- `thm:portal-multiplicity-criticality-updated`: with the adjoint
Casimir weight `C_F = 15/4`, the traceless-adjoint criticality
formula `q_eff = q(1 - C_F/M)` on `M = 2p` weak components gives the
repelling ratio `-7/8` for one right portal and the stabilizing
`+1/16` for two; at the canonical critical charge `q² = 2` the
stable effective charge is `q_eff = √2/16 > 0`. -/
theorem portal_multiplicity_criticality :
    (1 - (15:ℝ)/4 / (2 * 1) = -(7/8)) ∧
    (1 - (15:ℝ)/4 / (2 * 2) = 1/16) ∧
    (Real.sqrt 2 * (1 - (15:ℝ)/4 / (2 * 2)) = Real.sqrt 2 / 16) ∧
    0 < Real.sqrt 2 / 16 := by
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨by norm_num, by norm_num, ?_, by positivity⟩
  rw [show (1 - (15:ℝ)/4 / (2 * 2)) = 1/16 by norm_num]
  ring

end NCG
