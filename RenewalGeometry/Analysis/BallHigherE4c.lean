/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallHigherE4b

/-!
# The `H⁴` a-priori bound for lifted Coulomb gauges by absorption
  (stage D2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `sum_ddgQ_le` — the second derivatives of the right-hand side `U M + 2 Σ D B + Σ D V D` of the
  gauge equation in `L²`, with the fourth derivatives of `û` entering only through
  `‖∂²D‖_{L⁴}` multiplied by `δ`;
* `hM4_le` — **the `H⁴` bound**: universal threshold `θ`, and for every `H₃, b` a bound `K₄` with
  `‖û‖_{H⁴} ≤ K₄` whenever `‖D‖_{L⁴} ≤ θ` and `‖û‖_{H³} ≤ H₃`.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.HigherE4

open SobolevOpen BallReg BallAlg SobAlg HigherNorms HigherIdent HigherLeibniz HigherE3

set_option linter.unusedSectionVars false

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m : ℕ}

section E4

variable {Bf : CriticalGauge.MConn m} {hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j)}
  {uh : MatSob c r 10 m} {b δ CS cv : ℝ}

theorem sum_ddgQ_le (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) {H P1 P2 Y Y2 : ℝ}
    (hH1 : hM 1 (by norm_num) uh ≤ H) (hH2 : hM 2 (by norm_num) uh ≤ H)
    (hP1 : ∀ ν μ, mN 2 (derM ν (gD Bf hB uh μ)) ≤ P1)
    (hP2 : ∀ l ν μ, mN 2 (derM l (derM ν (gD Bf hB uh μ))) ≤ P2)
    (hY : ∀ ν μ, mN 4 (derM ν (gD Bf hB uh μ)) ≤ Y)
    (hY2 : ∀ l ν μ, mN 4 (derM l (derM ν (gD Bf hB uh μ))) ≤ Y2) :
    ∑ ν, ∑ l, mN 2 (derM l (derM ν (gQ Bf hB uh))) ≤
      16 * ((3 * (H * b) + cv * (2 * (m : ℝ) ^ 2) * b) +
        2 * (4 * (P2 * b + 2 * (P1 * b) + cv * δ * b)) +
        4 * ctB CS b δ (2 * (m : ℝ) ^ 2) Y Y2) := by
  unfold gQ
  rw [two_mul]
  have key : ∀ ν l, mN 2 (derM l (derM ν (rhoM (gU uh) * gM (c := c) (r := r) Bf hB +
      ((∑ μ, rhoM (gD Bf hB uh μ) * rhoM (gB (c := c) (r := r) Bf hB μ)) +
        ∑ μ, rhoM (gD Bf hB uh μ) * rhoM (gB (c := c) (r := r) Bf hB μ)) +
      ∑ μ, rhoM (gD Bf hB uh μ) * rhoM (gV uh) * rhoM (gD Bf hB uh μ)))) ≤
      (3 * (H * b) + cv * (2 * (m : ℝ) ^ 2) * b) +
        2 * (4 * (P2 * b + 2 * (P1 * b) + cv * δ * b)) +
        4 * ctB CS b δ (2 * (m : ℝ) ^ 2) Y Y2 := by
    intro ν l
    rw [map_add, map_add, map_add, map_add, map_add, map_add]
    have ha := mN_ddUM_le hK hS hH1 hH2 l ν
    have hb := mN_ddS1_le hK hS hP1 hP2 l ν
    have hc : mN 2 (derM l (derM ν (∑ μ, rhoM (gD Bf hB uh μ) * rhoM (gV uh) *
        rhoM (gD Bf hB uh μ)))) ≤ 4 * ctB CS b δ (2 * (m : ℝ) ^ 2) Y Y2 := by
      rw [map_sum, map_sum]
      refine (mN_sum_le (by norm_num) _ _).trans ?_
      calc _ ≤ ∑ _μ : Fin 4, ctB CS b δ (2 * (m : ℝ) ^ 2) Y Y2 :=
            Finset.sum_le_sum fun μ _ => mN_ddDVD_le hK hS hY hY2 l ν μ
        _ = _ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast; ring
    refine ((mN_add_le (by norm_num) _ _).trans (add_le_add ((mN_add_le (by norm_num) _ _).trans
      (add_le_add ha ((mN_add_le (by norm_num) _ _).trans (add_le_add hb hb)))) hc)).trans
      (le_of_eq (by ring))
  calc _ ≤ ∑ _ν : Fin 4, ∑ _l : Fin 4, ((3 * (H * b) + cv * (2 * (m : ℝ) ^ 2) * b) +
        2 * (4 * (P2 * b + 2 * (P1 * b) + cv * δ * b)) + 4 * ctB CS b δ (2 * (m : ℝ) ^ 2) Y Y2) :=
        Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun l _ => key ν l
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast
        ring

theorem ctB_mono {CS b δ δ' Ub Y : ℝ} (hCS : 0 ≤ CS) (hb : 0 ≤ b) (hδ : 0 ≤ δ) (hδδ : δ ≤ δ')
    (hUb : 0 ≤ Ub) (hY : 0 ≤ Y) : ctB CS b δ Ub Y 0 ≤ ctB CS b δ' Ub Y 0 := by
  have hδ' : 0 ≤ δ' := hδ.trans hδδ
  unfold ctB qb
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  gcongr

set_option maxHeartbeats 1000000 in
/-- **The `H⁴` bound by absorption.** -/
theorem hM4_le (hK : SobConsts c r m CS cv) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ ∀ H3 b : ℝ, ∃ K4 : ℝ, ∀ {Bf : CriticalGauge.MConn m}
      {hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j)} {uh : MatSob c r 10 m} {δ : ℝ},
      HSet Bf hB uh b δ → δ ≤ θ → hM 3 (by norm_num) uh ≤ H3 → hM 4 (by norm_num) uh ≤ K4 := by
  obtain ⟨CN, hCN0, hCN⟩ := neumann_est_matrix (c := c) (r := r) (m := m) 2 8 (by norm_num)
    (by norm_num)
  set Ub : ℝ := 2 * (m : ℝ) ^ 2 with hUb
  have hUb0 : 0 ≤ Ub := by positivity
  have hCS := hK.CS0
  have hcv := hK.cv0
  set G : ℝ := CN * (64 * (2 * Ub + 12 * CS)) * (4 * CS) with hG
  have hG0 : 0 ≤ G := by positivity
  refine ⟨1 / (2 * G + 2), by positivity, ?_, fun H3 b => ?_⟩
  · rw [div_le_one (by positivity)]; linarith
  set P1 : ℝ := H3 + (H3 + cv * Ub) * b with hP1def
  set P2 : ℝ := H3 + (H3 + 2 * H3 + cv * Ub) * b with hP2def
  set Y : ℝ := CS * (P1 + 4 * P2) with hYdef
  set Y20 : ℝ := CS * (P2 + 4 * ((H3 + 3 * H3 + 3 * H3 + cv * Ub) * b)) with hY20def
  refine ⟨2 * CN * ((Ub * (cv * b) + 2 * (4 * (cv * 1 * b)) + 4 * (1 * Ub * 1)) +
    4 * ((H3 * b + cv * Ub * b) + 2 * (4 * (P1 * b + cv * 1 * b)) +
      4 * (2 * Ub * 1 * Y + 1 * (CS * (1 * 1 + 4 * (Y * 1 + 1 * Y))) + 1 * (b * Ub) * 1)) +
    16 * ((3 * (H3 * b) + cv * Ub * b) + 2 * (4 * (P2 * b + 2 * (P1 * b) + cv * 1 * b)) +
      4 * ctB CS b 1 Ub Y 0) +
    64 * (2 * Ub * 1 + 12 * CS * 1 * 1) * Y20 + cv * Ub), fun {Bf hB uh δ} hS hδθ hH3 => ?_⟩
  have hδ0 := hS.δ0
  have hb0 := hS.b0
  have hδ1 : δ ≤ 1 := hδθ.trans (by rw [div_le_one (by positivity)]; linarith)
  have hx0 : 0 ≤ hM 4 (by norm_num) uh := hM_nonneg _ _ _
  have hh2 : hM 2 (by norm_num) uh ≤ H3 := (h2_le_h3 uh).trans hH3
  have hh1 : hM 1 (by norm_num) uh ≤ H3 := (h1_le_h2 uh).trans hh2
  have hH30 : 0 ≤ H3 := (hM_nonneg _ _ _).trans hH3
  have hP1 : ∀ ν μ, mN 2 (derM ν (gD Bf hB uh μ)) ≤ P1 := fun ν μ =>
    (mN_dgD_two hK hS ν μ).trans (by rw [hP1def]; gcongr)
  have hP2 : ∀ l ν μ, mN 2 (derM l (derM ν (gD Bf hB uh μ))) ≤ P2 := fun l ν μ =>
    (mN_ddgD_two hK hS l ν μ).trans (by rw [hP2def]; gcongr)
  have hY : ∀ ν μ, mN 4 (derM ν (gD Bf hB uh μ)) ≤ Y := fun ν μ =>
    (mN4_dgD hK hS ν μ).trans (by rw [hYdef, hP1def, hP2def]; gcongr)
  have hY2 : ∀ l ν μ, mN 4 (derM l (derM ν (gD Bf hB uh μ))) ≤
      Y20 + 4 * CS * hM 4 (by norm_num) uh := by
    intro l ν μ
    refine (mN4_ddgD hK hS l ν μ).trans (le_of_le_of_eq ?_ (show CS * (P2 + 4 * (hM 4
      (by norm_num) uh + (H3 + 3 * H3 + 3 * H3 + cv * Ub) * b)) = Y20 + 4 * CS * hM 4
      (by norm_num) uh by rw [hY20def]; ring))
    rw [hP2def]
    gcongr
  have hY0 : 0 ≤ Y := by rw [hYdef, hP1def, hP2def]; positivity
  have hY200 : 0 ≤ Y20 := by rw [hY20def, hP2def]; positivity
  -- the pieces
  have hS1 := sum_mN_derM_gQ_le hK hS hh1 hP1 hY
  have hSS := sum_ddgQ_le hK hS hh1 hh2 hP1 hP2 hY hY2
  rw [ctB_affine] at hSS
  have hQ2 := mN_gQ_le hK hS
  have hN := hCN uh hS.neum
  rw [hS.lap] at hN
  have h2Q : hM 2 (by norm_num) (gQ Bf hB uh) ≤ mN 2 (gQ Bf hB uh) +
      (∑ ν, mN 2 (derM ν (gQ Bf hB uh)) + ∑ ν, ∑ l, mN 2 (derM l (derM ν (gQ Bf hB uh)))) := by
    have h1 := hM_succ_le 1 (by norm_num) (gQ Bf hB uh)
    have h2 : ∀ ν, hM 1 (by norm_num) (derM ν (gQ Bf hB uh)) ≤ mN 2 (derM ν (gQ Bf hB uh)) +
        ∑ l, mN 2 (derM l (derM ν (gQ Bf hB uh))) := by
      intro ν
      have := hM_succ_le 0 (by norm_num) (derM ν (gQ Bf hB uh))
      rw [Finset.sum_congr rfl fun l _ => hM_zero _ _] at this
      exact this
    refine h1.trans (add_le_add le_rfl ((Finset.sum_le_sum fun ν _ => h2 ν).trans
      (le_of_eq ?_)))
    rw [Finset.sum_add_distrib]
  have huh := mN_uh_two hK hS
  -- the absorption
  set s4 : ℝ := 2 * Ub * δ + 12 * CS * δ * δ with hs4
  have hs40 : 0 ≤ s4 := by positivity
  have hαle : CN * (64 * s4) * (4 * CS) ≤ 1 / 2 := by
    have h1 : s4 ≤ (2 * Ub + 12 * CS) * δ := by
      rw [hs4]; nlinarith [mul_le_mul_of_nonneg_left hδ1 (by positivity : 0 ≤ 12 * CS * δ)]
    have h2 : CN * (64 * s4) * (4 * CS) ≤ G * δ := by
      rw [hG]
      calc CN * (64 * s4) * (4 * CS) ≤ CN * (64 * ((2 * Ub + 12 * CS) * δ)) * (4 * CS) := by
            gcongr
        _ = CN * (64 * (2 * Ub + 12 * CS)) * (4 * CS) * δ := by ring
    have h3 : G * δ ≤ G * (1 / (2 * G + 2)) := mul_le_mul_of_nonneg_left hδθ hG0
    have h4 : G * (1 / (2 * G + 2)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  set x := hM 4 (by norm_num) uh with hx
  set Q2 : ℝ := Ub * (cv * b) + 2 * (4 * (cv * δ * b)) + 4 * (δ * Ub * δ) with hQ2def
  set B1 : ℝ := 4 * ((H3 * b + cv * Ub * b) + 2 * (4 * (P1 * b + cv * δ * b)) +
      4 * (2 * Ub * δ * Y + δ * (CS * (δ * δ + 4 * (Y * δ + δ * Y))) + δ * (b * Ub) * δ))
    with hB1def
  set A2 : ℝ := 16 * ((3 * (H3 * b) + cv * Ub * b) + 2 * (4 * (P2 * b + 2 * (P1 * b) + cv * δ * b)) +
      4 * ctB CS b δ Ub Y 0) with hA2def
  have hSS' : ∑ ν, ∑ l, mN 2 (derM l (derM ν (gQ Bf hB uh))) ≤
      A2 + 64 * s4 * Y20 + (64 * s4 * (4 * CS)) * x := by
    refine hSS.trans (le_of_eq ?_)
    rw [hA2def, hs4, hUb]; ring
  have hmain : x ≤ CN * (Q2 + B1 + A2 + 64 * s4 * Y20 + cv * Ub) +
      (CN * (64 * s4) * (4 * CS)) * x := by
    have hQ2' : mN 2 (gQ Bf hB uh) ≤ Q2 := by rw [hQ2def, hUb]; exact hQ2
    have hS1' : ∑ ν, mN 2 (derM ν (gQ Bf hB uh)) ≤ B1 := by rw [hB1def, hUb]; exact hS1
    have := hN.trans (mul_le_mul_of_nonneg_left (add_le_add (h2Q.trans (add_le_add hQ2'
      (add_le_add hS1' hSS'))) huh) hCN0)
    calc x ≤ CN * (Q2 + (B1 + (A2 + 64 * s4 * Y20 + 64 * s4 * (4 * CS) * x)) +
          cv * (2 * (m : ℝ) ^ 2)) := this
      _ = _ := by rw [hUb]; ring
  have habs : (CN * (64 * s4) * (4 * CS)) * x ≤ 1 / 2 * x := mul_le_mul_of_nonneg_right hαle hx0
  have hfin : x ≤ 2 * CN * (Q2 + B1 + A2 + 64 * s4 * Y20 + cv * Ub) := by linarith
  refine hfin.trans ?_
  have hct := ctB_mono (Ub := Ub) (Y := Y) hCS hb0 hδ0 hδ1 hUb0 hY0
  rw [hQ2def, hB1def, hA2def, hs4]
  gcongr

end E4

end RenewalGeometry.BallAnalysis.HigherE4
