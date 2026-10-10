/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallHigherLeibniz

/-!
# The `H²` and `H³` a-priori bounds for lifted Coulomb gauges
  (stage D2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

For a lifted unitary Neumann gauge `û` solving the gauge equation
`Δû = U M + 2 Σ D_μ B_μ + Σ D_μ V D_μ` (`HSet`), with `‖D_μ‖_{L⁴} ≤ δ` and `L^∞` bounds `b` on the
smooth connection:

* `SobConsts` — the universal constants (critical Sobolev `C_S`, Lebesgue comparisons `c_v`);
* `hM2_le` — **the `H²` bound** `‖û‖_{H²} ≤ C_N (c_v U_b b + 8 c_v δ b + 4 U_b δ² + c_v U_b)`
  (no smallness needed: the right-hand side is in `L²` by Hölder);
* `sum_mN_derM_gQ_le` and `hM3_le` — **the `H³` bound by absorption**: the critical terms
  `∂D V D`, `D ∂V D`, `D V ∂D` are bounded by `δ`-small multiples of `‖û‖_{H³}` (critical
  Sobolev `H¹ ⊂ L⁴`, the splitting `∂V = D^* + B^* V`), with universal coefficients.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.HigherE3

open SobolevOpen BallReg BallAlg SobAlg HigherNorms HigherIdent HigherLeibniz

set_option linter.unusedSectionVars false

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m : ℕ}

/-! ### Universal constants -/

/-- The universal constants of the critical estimates on the ball. -/
structure SobConsts (c : Fin 4 → ℝ) (r : ℝ) [Fact (0 < r)] (m : ℕ) (CS cv : ℝ) : Prop where
  CS0 : 0 ≤ CS
  cv0 : 0 ≤ cv
  sob : ∀ {s : ℕ} [Fact (3 ≤ s)] (X : MatSob c r (s + 1) m),
    mN 4 X ≤ CS * (mN 2 X + ∑ ν, mN 2 (derM ν X))
  l24 : ∀ {s : ℕ} [Fact (3 ≤ s)] (X : MatSob c r s m), mN 2 X ≤ cv * mN 4 X
  l4i : ∀ {s : ℕ} [Fact (3 ≤ s)] (X : MatSob c r s m), mN 4 X ≤ cv * mN ⊤ X
  l2i : ∀ {s : ℕ} [Fact (3 ≤ s)] (X : MatSob c r s m), mN 2 X ≤ cv * mN ⊤ X

theorem exists_sobConsts : ∃ CS cv : ℝ, SobConsts c r m CS cv := by
  obtain ⟨CS, hCS0, hCS⟩ := mN_four_le (c := c) (r := r) (m := m)
  obtain ⟨c1, hc1, h1⟩ := mN_le_mN (c := c) (r := r) (m := m) (p := 2) (q := 4) (by norm_num)
    (by norm_num)
  obtain ⟨c2, hc2, h2⟩ := mN_le_mN (c := c) (r := r) (m := m) (p := 4) (q := ⊤) (by norm_num)
    le_top
  obtain ⟨c3, hc3, h3⟩ := mN_le_mN (c := c) (r := r) (m := m) (p := 2) (q := ⊤) (by norm_num)
    le_top
  refine ⟨CS, c1 + c2 + c3, ⟨hCS0, by positivity, hCS, fun X => ?_, fun X => ?_, fun X => ?_⟩⟩
  · exact (h1 X).trans (mul_le_mul_of_nonneg_right (by linarith) (mN_nonneg _ _))
  · exact (h2 X).trans (mul_le_mul_of_nonneg_right (by linarith) (mN_nonneg _ _))
  · exact (h3 X).trans (mul_le_mul_of_nonneg_right (by linarith) (mN_nonneg _ _))

/-! ### The setting -/

/-- **The setting of the higher a-priori bounds**: a unitary Neumann lift `û ∈ H^{10}` solving
the gauge equation, with covariant derivative `‖D_μ‖_{L⁴} ≤ δ` and smooth-connection bounds `b`. -/
structure HSet (Bf : CriticalGauge.MConn m) (hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j))
    (uh : MatSob c r 10 m) (b δ : ℝ) : Prop where
  unit : uh * star uh = 1
  neum : IsNeumM (restrM (by norm_num : 5 ≤ 10) uh)
  lap : lapM (s := 8) uh = gQ Bf hB uh
  D4 : ∀ μ, mN 4 (gD Bf hB uh μ) ≤ δ
  bb : BBounds (c := c) (r := r) Bf hB b
  b0 : 0 ≤ b
  δ0 : 0 ≤ δ

section Bounds

variable {Bf : CriticalGauge.MConn m} {hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j)}
  {uh : MatSob c r 10 m} {b δ CS cv : ℝ}

theorem mN_gU_top (hS : HSet Bf hB uh b δ) : mN ⊤ (gU uh) ≤ 2 * (m : ℝ) ^ 2 := by
  have h : gU uh * star (gU uh) = 1 := by rw [← gV_eq]; exact gU_mul_gV hS.unit
  exact mN_top_le_of_unitary h

theorem mN_gV_top (hS : HSet Bf hB uh b δ) : mN ⊤ (gV uh) ≤ 2 * (m : ℝ) ^ 2 := by
  rw [gV_eq, mN_star]; exact mN_gU_top hS

theorem mN_uh_two (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) :
    mN 2 uh ≤ cv * (2 * (m : ℝ) ^ 2) :=
  (hK.l2i uh).trans (mul_le_mul_of_nonneg_left (mN_top_le_of_unitary hS.unit) hK.cv0)

theorem mN_gD_two (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) (μ : Fin 4) :
    mN 2 (gD Bf hB uh μ) ≤ cv * δ :=
  (hK.l24 _).trans (mul_le_mul_of_nonneg_left (hS.D4 μ) hK.cv0)

theorem mN_gU_two (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) :
    mN 2 (gU uh) ≤ cv * (2 * (m : ℝ) ^ 2) :=
  (hK.l2i _).trans (mul_le_mul_of_nonneg_left (mN_gU_top hS) hK.cv0)

theorem mN_dgU_two (ν : Fin 4) : mN 2 (derM ν (gU uh)) ≤ hM 1 (by norm_num) uh := by
  rw [gU, derM_rhoM, mN_rhoM]; exact mN_d1_le uh ν

theorem mN_ddgU_two (l ν : Fin 4) : mN 2 (derM l (derM ν (gU uh))) ≤ hM 2 (by norm_num) uh := by
  rw [gU, derM_rhoM, derM_rhoM, mN_rhoM]; exact mN_d2_le uh l ν

theorem mN_dddgU_two (k l ν : Fin 4) :
    mN 2 (derM k (derM l (derM ν (gU uh)))) ≤ hM 3 (by norm_num) uh := by
  rw [gU, derM_rhoM, derM_rhoM, derM_rhoM, mN_rhoM]; exact mN_d3_le uh k l ν

/-- `‖∂_ν D_μ‖_{L²} ≤ ‖û‖_{H²} + (‖û‖_{H¹} + c_v U_b) b`. -/
theorem mN_dgD_two (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) (ν μ : Fin 4) :
    mN 2 (derM ν (gD Bf hB uh μ)) ≤
      hM 2 (by norm_num) uh + (hM 1 (by norm_num) uh + cv * (2 * (m : ℝ) ^ 2)) * b := by
  rw [gD, map_sub]
  refine (mN_sub_le (by norm_num) _ _).trans ?_
  have h1 := mN_d2_le uh ν μ
  have h2 := mN_derM_mul_le_2i ν (gU uh) (gB (c := c) (r := r) Bf hB μ)
  have h3 := mN_dgU_two (uh := uh) ν
  have h4 := mN_gU_two hK hS
  have hb1 := hS.bb.B μ
  have hb2 := hS.bb.dB ν μ
  have := mN_nonneg ⊤ (gB (c := c) (r := r) Bf hB μ)
  have := mN_nonneg ⊤ (derM ν (gB (c := c) (r := r) Bf hB μ))
  have := mN_nonneg 2 (gU uh)
  have := mN_nonneg 2 (derM ν (gU uh))
  have := hS.b0
  have := hK.cv0
  nlinarith [mul_le_mul h3 hb1 (mN_nonneg _ _) (hM_nonneg _ _ _),
    mul_le_mul h4 hb2 (mN_nonneg _ _) (by positivity : 0 ≤ cv * (2 * (m : ℝ) ^ 2))]

/-- `‖∂_l ∂_ν D_μ‖_{L²} ≤ ‖û‖_{H³} + (‖û‖_{H²} + 2‖û‖_{H¹} + c_v U_b) b`. -/
theorem mN_ddgD_two (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) (l ν μ : Fin 4) :
    mN 2 (derM l (derM ν (gD Bf hB uh μ))) ≤ hM 3 (by norm_num) uh +
      (hM 2 (by norm_num) uh + 2 * hM 1 (by norm_num) uh + cv * (2 * (m : ℝ) ^ 2)) * b := by
  rw [gD, map_sub, map_sub, derM_mul, map_add]
  refine (mN_sub_le (by norm_num) _ _).trans ?_
  have h1 := mN_d3_le uh l ν μ
  have ha := mN_derM_mul_le_2i (s := 7) l (derM ν (gU uh)) (rhoM (gB (c := c) (r := r) Bf hB μ))
  have hb := mN_derM_mul_le_2i (s := 7) l (rhoM (s := 8) (gU uh))
    (derM (s := 8) ν (gB (c := c) (r := r) Bf hB μ))
  have e1 : mN ⊤ (rhoM (gB (c := c) (r := r) Bf hB μ)) ≤ b := by
    rw [mN_rhoM]; exact hS.bb.B μ
  have e2 : mN ⊤ (derM l (rhoM (gB (c := c) (r := r) Bf hB μ))) ≤ b := by
    rw [derM_rhoM, mN_rhoM]; exact hS.bb.dB l μ
  have e3 : mN ⊤ (derM ν (gB (c := c) (r := r) Bf hB μ)) ≤ b := hS.bb.dB ν μ
  have e4 : mN ⊤ (derM l (derM ν (gB (c := c) (r := r) Bf hB μ))) ≤ b := hS.bb.ddB l ν μ
  have f1 := mN_ddgU_two (uh := uh) l ν
  have f2 := mN_dgU_two (uh := uh) ν
  have f3 : mN 2 (derM l (rhoM (gU uh))) ≤ hM 1 (by norm_num) uh := by
    rw [derM_rhoM, mN_rhoM]; exact mN_dgU_two l
  have f4 : mN 2 (rhoM (gU uh)) ≤ cv * (2 * (m : ℝ) ^ 2) := by
    rw [mN_rhoM]; exact mN_gU_two hK hS
  have g1 := mul_le_mul f1 e1 (mN_nonneg _ _) (hM_nonneg _ _ _)
  have g2 := mul_le_mul f2 e2 (mN_nonneg _ _) (hM_nonneg _ _ _)
  have g3 := mul_le_mul f3 e3 (mN_nonneg _ _) (hM_nonneg _ _ _)
  have g4 := mul_le_mul f4 e4 (mN_nonneg _ _) (by have := hK.cv0; positivity)
  have hsum := (mN_add_le (p := 2) (by norm_num) (derM l (derM ν (gU uh) * rhoM (gB (c := c) (r := r) Bf hB μ)))
    (derM l (rhoM (gU uh) * derM ν (gB (c := c) (r := r) Bf hB μ))))
  linarith

/-- **Critical Sobolev for the first derivatives of `D`.** -/
theorem mN4_dgD (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) (ν μ : Fin 4) :
    mN 4 (derM ν (gD Bf hB uh μ)) ≤ CS * ((hM 2 (by norm_num) uh +
      (hM 1 (by norm_num) uh + cv * (2 * (m : ℝ) ^ 2)) * b) + 4 * (hM 3 (by norm_num) uh +
      (hM 2 (by norm_num) uh + 2 * hM 1 (by norm_num) uh + cv * (2 * (m : ℝ) ^ 2)) * b)) := by
  refine (hK.sob (derM ν (gD Bf hB uh μ))).trans ?_
  refine mul_le_mul_of_nonneg_left (add_le_add (mN_dgD_two hK hS ν μ) ?_) hK.CS0
  calc ∑ l, mN 2 (derM l (derM ν (gD Bf hB uh μ)))
      ≤ ∑ _l : Fin 4, (hM 3 (by norm_num) uh +
          (hM 2 (by norm_num) uh + 2 * hM 1 (by norm_num) uh + cv * (2 * (m : ℝ) ^ 2)) * b) :=
        Finset.sum_le_sum fun l _ => mN_ddgD_two hK hS l ν μ
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast
        ring

end Bounds

/-! ### Product bounds -/

section Products

variable {s : ℕ} [Fact (3 ≤ s)]

/-- Derivative of a triple product: the outer factors in `L⁴`, the middle one in `L^∞`, except
for the middle derivative which is left as is. -/
theorem mN_derM_mul3_le (ν : Fin 4) (X Y Z : MatSob c r (s + 1) m) :
    mN 2 (derM ν (X * Y * Z)) ≤ mN 4 (derM ν X) * mN ⊤ Y * mN 4 Z +
      mN 2 (rhoM X * derM ν Y * rhoM Z) + mN 4 X * mN ⊤ Y * mN 4 (derM ν Z) := by
  rw [derM_mul, derM_mul, add_mul, map_mul]
  have h1 := mN_mul3_le (derM ν X) (rhoM Y) (rhoM Z)
  have h3 := mN_mul3_le (rhoM X) (rhoM Y) (derM ν Z)
  rw [mN_rhoM, mN_rhoM] at h1
  rw [mN_rhoM, mN_rhoM] at h3
  have hs1 := mN_add_le (p := 2) (by norm_num) (derM ν X * rhoM Y * rhoM Z + rhoM X * derM ν Y * rhoM Z)
    (rhoM X * rhoM Y * derM ν Z)
  have hs2 := mN_add_le (p := 2) (by norm_num) (derM ν X * rhoM Y * rhoM Z)
    (rhoM X * derM ν Y * rhoM Z)
  linarith

/-- **The quartic term by critical Sobolev**: `‖X W^* Z‖_{L²} ≤ ‖X‖_{L⁴} ‖W^* Z‖_{L⁴}` and
`‖W^* Z‖_{L⁴} ≤ C_S ‖W^* Z‖_{H¹}`. -/
theorem mN_mul_star_mul_le {CS cv : ℝ} (hK : SobConsts c r m CS cv) (X W Z : MatSob c r (s + 1) m) :
    mN 2 (X * star W * Z) ≤ mN 4 X * (CS * (mN 4 W * mN 4 Z +
      ∑ l, (mN 4 (derM l W) * mN 4 Z + mN 4 W * mN 4 (derM l Z)))) := by
  rw [mul_assoc]
  refine (mN_mul_le_44 _ _).trans (mul_le_mul_of_nonneg_left ?_ (mN_nonneg _ _))
  refine (hK.sob (star W * Z)).trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hK.CS0)
  · exact (mN_mul_le_44 _ _).trans (le_of_eq (by rw [mN_star]))
  · refine Finset.sum_le_sum fun l _ => (mN_derM_mul_le_44 l _ _).trans (le_of_eq ?_)
    rw [derM_star, mN_star, mN_star]

end Products

/-! ### The `H²` bound -/

section E2

variable {Bf : CriticalGauge.MConn m} {hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j)}
  {uh : MatSob c r 10 m} {b δ CS cv : ℝ}

theorem mN_gQ_le (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) :
    mN 2 (gQ Bf hB uh) ≤ 2 * (m : ℝ) ^ 2 * (cv * b) + 2 * (4 * (cv * δ * b)) +
      4 * (δ * (2 * (m : ℝ) ^ 2) * δ) := by
  unfold gQ
  rw [two_mul]
  have hU := mN_gU_top hS
  have hV := mN_gV_top hS
  have h1 : mN 2 (rhoM (gU uh) * gM (c := c) (r := r) Bf hB) ≤ 2 * (m : ℝ) ^ 2 * (cv * b) := by
    refine (mN_mul_le_inf2 _ _).trans ?_
    rw [mN_rhoM]
    exact mul_le_mul hU ((hK.l2i _).trans (mul_le_mul_of_nonneg_left hS.bb.M hK.cv0))
      (mN_nonneg _ _) (by positivity)
  have h2 : mN 2 (∑ μ, rhoM (gD Bf hB uh μ) * rhoM (gB (c := c) (r := r) Bf hB μ)) ≤
      4 * (cv * δ * b) := by
    refine (mN_sum_le (by norm_num) _ _).trans ?_
    calc ∑ μ, mN 2 (rhoM (gD Bf hB uh μ) * rhoM (gB (c := c) (r := r) Bf hB μ))
        ≤ ∑ _μ : Fin 4, cv * δ * b := by
          refine Finset.sum_le_sum fun μ _ => (mN_mul_le_2inf _ _).trans ?_
          rw [mN_rhoM, mN_rhoM]
          exact mul_le_mul (mN_gD_two hK hS μ) (hS.bb.B μ) (mN_nonneg _ _)
            (mul_nonneg hK.cv0 hS.δ0)
      _ = 4 * (cv * δ * b) := by simp
  have h3 : mN 2 (∑ μ, rhoM (gD Bf hB uh μ) * rhoM (gV uh) * rhoM (gD Bf hB uh μ)) ≤
      4 * (δ * (2 * (m : ℝ) ^ 2) * δ) := by
    refine (mN_sum_le (by norm_num) _ _).trans ?_
    calc ∑ μ, mN 2 (rhoM (gD Bf hB uh μ) * rhoM (gV uh) * rhoM (gD Bf hB uh μ))
        ≤ ∑ _μ : Fin 4, δ * (2 * (m : ℝ) ^ 2) * δ := by
          refine Finset.sum_le_sum fun μ _ => (mN_mul3_le _ _ _).trans ?_
          rw [mN_rhoM, mN_rhoM]
          have := hS.D4 μ
          exact mul_le_mul (mul_le_mul this hV (mN_nonneg _ _) hS.δ0) this (mN_nonneg _ _)
            (by have := hS.δ0; positivity)
      _ = 4 * (δ * (2 * (m : ℝ) ^ 2) * δ) := by simp
  refine ((mN_add_le (by norm_num) _ _).trans (add_le_add ((mN_add_le (by norm_num) _ _).trans
    (add_le_add h1 ((mN_add_le (by norm_num) _ _).trans (add_le_add h2 h2)))) h3)).trans
    (le_of_eq (by ring))

/-- **The `H²` bound** (no smallness needed). -/
theorem hM2_le (hK : SobConsts c r m CS cv) :
    ∃ CN : ℝ, 0 ≤ CN ∧ ∀ {Bf : CriticalGauge.MConn m}
      {hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j)} {uh : MatSob c r 10 m} {b δ : ℝ},
      HSet Bf hB uh b δ → hM 2 (by norm_num) uh ≤ CN * ((2 * (m : ℝ) ^ 2 * (cv * b) +
        2 * (4 * (cv * δ * b)) + 4 * (δ * (2 * (m : ℝ) ^ 2) * δ)) + cv * (2 * (m : ℝ) ^ 2)) := by
  obtain ⟨CN, hCN0, hCN⟩ := neumann_est_matrix (c := c) (r := r) (m := m) 0 8 (by norm_num)
    (by norm_num)
  refine ⟨CN, hCN0, fun {Bf hB uh b δ} hS => ?_⟩
  have h := hCN uh hS.neum
  rw [hM_zero, hS.lap] at h
  refine h.trans (mul_le_mul_of_nonneg_left (add_le_add (mN_gQ_le hK hS) (mN_uh_two hK hS)) hCN0)

end E2

/-! ### The first derivatives of the right-hand side -/

section E3

variable {Bf : CriticalGauge.MConn m} {hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j)}
  {uh : MatSob c r 10 m} {b δ CS cv : ℝ}

theorem mN_derM_UM_le (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) {H : ℝ}
    (hH : hM 1 (by norm_num) uh ≤ H) (ν : Fin 4) :
    mN 2 (derM ν (rhoM (gU uh) * gM (c := c) (r := r) Bf hB)) ≤
      H * b + cv * (2 * (m : ℝ) ^ 2) * b := by
  refine (mN_derM_mul_le_2i (s := 7) ν (rhoM (s := 8) (gU uh)) _).trans ?_
  rw [derM_rhoM, mN_rhoM, mN_rhoM]
  have h1 := (mN_dgU_two (uh := uh) ν).trans hH
  have h2 := mN_gU_two hK hS
  have := hS.b0
  exact add_le_add (mul_le_mul h1 hS.bb.M (mN_nonneg _ _) ((hM_nonneg _ _ _).trans hH))
    (mul_le_mul h2 (hS.bb.dM ν) (mN_nonneg _ _) (by have := hK.cv0; positivity))

theorem mN_derM_S1_le (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) {P : ℝ}
    (hP : ∀ ν μ, mN 2 (derM ν (gD Bf hB uh μ)) ≤ P) (ν : Fin 4) :
    mN 2 (derM ν (∑ μ, rhoM (gD Bf hB uh μ) * rhoM (gB (c := c) (r := r) Bf hB μ))) ≤
      4 * (P * b + cv * δ * b) := by
  rw [map_sum]
  refine (mN_sum_le (by norm_num) _ _).trans ?_
  calc ∑ μ, mN 2 (derM ν (rhoM (gD Bf hB uh μ) * rhoM (gB (c := c) (r := r) Bf hB μ)))
      ≤ ∑ _μ : Fin 4, (P * b + cv * δ * b) := by
        refine Finset.sum_le_sum fun μ _ => ?_
        refine (mN_derM_mul_le_2i (s := 7) ν (rhoM (s := 8) (gD Bf hB uh μ)) _).trans ?_
        rw [derM_rhoM, derM_rhoM, mN_rhoM, mN_rhoM, mN_rhoM, mN_rhoM]
        have := hS.b0
        exact add_le_add (mul_le_mul (hP ν μ) (hS.bb.B μ) (mN_nonneg _ _)
          ((mN_nonneg _ _).trans (hP ν μ)))
          (mul_le_mul (mN_gD_two hK hS μ) (hS.bb.dB ν μ) (mN_nonneg _ _)
            (mul_nonneg hK.cv0 hS.δ0))
    _ = 4 * (P * b + cv * δ * b) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring

theorem mN_derM_DVD_le (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) {Y : ℝ}
    (hY : ∀ l μ, mN 4 (derM l (gD Bf hB uh μ)) ≤ Y) (ν μ : Fin 4) :
    mN 2 (derM ν (rhoM (gD Bf hB uh μ) * rhoM (gV uh) * rhoM (gD Bf hB uh μ))) ≤
      2 * (2 * (m : ℝ) ^ 2) * δ * Y + δ * (CS * (δ * δ + 4 * (Y * δ + δ * Y))) +
        δ * (b * (2 * (m : ℝ) ^ 2)) * δ := by
  have hV := mN_gV_top hS
  have hD := hS.D4
  have hδ := hS.δ0
  have hY0 : 0 ≤ Y := (mN_nonneg _ _).trans (hY 0 0)
  refine (mN_derM_mul3_le (s := 7) ν (rhoM (s := 8) (gD Bf hB uh μ)) (rhoM (s := 8) (gV uh))
    (rhoM (s := 8) (gD Bf hB uh μ))).trans ?_
  rw [derM_rhoM, derM_rhoM]
  repeat rw [mN_rhoM]
  rw [derM_gV, map_add, map_mul, rhoM_star, rhoM_star, mul_add, add_mul]
  have t1 : mN 4 (derM ν (gD Bf hB uh μ)) * mN ⊤ (gV uh) * mN 4 (gD Bf hB uh μ) ≤
      Y * (2 * (m : ℝ) ^ 2) * δ :=
    mul_le_mul (mul_le_mul (hY ν μ) hV (mN_nonneg _ _) hY0) (hD μ) (mN_nonneg _ _)
      (by positivity)
  have t3 : mN 4 (gD Bf hB uh μ) * mN ⊤ (gV uh) * mN 4 (derM ν (gD Bf hB uh μ)) ≤
      δ * (2 * (m : ℝ) ^ 2) * Y :=
    mul_le_mul (mul_le_mul (hD μ) hV (mN_nonneg _ _) hδ) (hY ν μ) (mN_nonneg _ _)
      (by positivity)
  have t2a := mN_mul_star_mul_le (s := 6) hK (rhoM (rhoM (gD Bf hB uh μ)))
    (rhoM (rhoM (gD Bf hB uh ν))) (rhoM (rhoM (gD Bf hB uh μ)))
  simp only [derM_rhoM] at t2a
  rw [mN_rhoM, mN_rhoM, mN_rhoM, mN_rhoM] at t2a
  have hsum : ∑ l, (mN 4 (rhoM (rhoM (derM l (gD Bf hB uh ν)))) * mN 4 (gD Bf hB uh μ) +
      mN 4 (gD Bf hB uh ν) * mN 4 (rhoM (rhoM (derM l (gD Bf hB uh μ))))) ≤
      4 * (Y * δ + δ * Y) := by
    calc _ ≤ ∑ _l : Fin 4, (Y * δ + δ * Y) := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [mN_rhoM, mN_rhoM, mN_rhoM, mN_rhoM]
          exact add_le_add (mul_le_mul (hY l ν) (hD μ) (mN_nonneg _ _) hY0)
            (mul_le_mul (hD ν) (hY l μ) (mN_nonneg _ _) hδ)
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast
          ring
  have t2a' : mN 2 (rhoM (rhoM (gD Bf hB uh μ)) * star (rhoM (rhoM (gD Bf hB uh ν))) *
      rhoM (rhoM (gD Bf hB uh μ))) ≤ δ * (CS * (δ * δ + 4 * (Y * δ + δ * Y))) := by
    refine t2a.trans (mul_le_mul (hD μ) (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul (hD ν) (hD μ) (mN_nonneg _ _) hδ) hsum) hK.CS0) (by
        have := hK.CS0
        have : 0 ≤ ∑ l, (mN 4 (rhoM (rhoM (derM l (gD Bf hB uh ν)))) * mN 4 (gD Bf hB uh μ) +
          mN 4 (gD Bf hB uh ν) * mN 4 (rhoM (rhoM (derM l (gD Bf hB uh μ))))) :=
          Finset.sum_nonneg fun l _ => add_nonneg (mul_nonneg (mN_nonneg _ _) (mN_nonneg _ _))
            (mul_nonneg (mN_nonneg _ _) (mN_nonneg _ _))
        exact mul_nonneg hK.CS0 (add_nonneg (mul_nonneg (mN_nonneg _ _) (mN_nonneg _ _)) this))
      hδ)
  have t2b : mN 2 (rhoM (rhoM (gD Bf hB uh μ)) * (star (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν))) *
      rhoM (rhoM (gV uh))) * rhoM (rhoM (gD Bf hB uh μ))) ≤ δ * (b * (2 * (m : ℝ) ^ 2)) * δ := by
    refine (mN_mul3_le _ _ _).trans ?_
    rw [mN_rhoM, mN_rhoM]
    have hBV : mN ⊤ (star (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν))) * rhoM (rhoM (gV uh))) ≤
        b * (2 * (m : ℝ) ^ 2) := by
      refine (mN_mul_le_infinf _ _).trans ?_
      rw [mN_star, mN_rhoM, mN_rhoM, mN_rhoM, mN_rhoM]
      exact mul_le_mul (hS.bb.B ν) hV (mN_nonneg _ _) hS.b0
    exact mul_le_mul (mul_le_mul (hD μ) hBV (mN_nonneg _ _) hδ) (hD μ) (mN_nonneg _ _)
      (by have := hS.b0; positivity)
  have hmid := mN_add_le (p := 2) (by norm_num)
    (rhoM (rhoM (gD Bf hB uh μ)) * star (rhoM (rhoM (gD Bf hB uh ν))) * rhoM (rhoM (gD Bf hB uh μ)))
    (rhoM (rhoM (gD Bf hB uh μ)) * (star (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν))) *
      rhoM (rhoM (gV uh))) * rhoM (rhoM (gD Bf hB uh μ)))
  refine (add_le_add (add_le_add t1 (hmid.trans (add_le_add t2a' t2b))) t3).trans
    (le_of_eq (by ring))


theorem sum_mN_derM_gQ_le (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) {H P Y : ℝ}
    (hH : hM 1 (by norm_num) uh ≤ H) (hP : ∀ ν μ, mN 2 (derM ν (gD Bf hB uh μ)) ≤ P)
    (hY : ∀ l μ, mN 4 (derM l (gD Bf hB uh μ)) ≤ Y) :
    ∑ ν, mN 2 (derM ν (gQ Bf hB uh)) ≤
      4 * ((H * b + cv * (2 * (m : ℝ) ^ 2) * b) + 2 * (4 * (P * b + cv * δ * b)) +
        4 * (2 * (2 * (m : ℝ) ^ 2) * δ * Y + δ * (CS * (δ * δ + 4 * (Y * δ + δ * Y))) +
          δ * (b * (2 * (m : ℝ) ^ 2)) * δ)) := by
  unfold gQ
  rw [two_mul]
  calc ∑ ν, mN 2 (derM ν (rhoM (gU uh) * gM (c := c) (r := r) Bf hB +
        ((∑ μ, rhoM (gD Bf hB uh μ) * rhoM (gB (c := c) (r := r) Bf hB μ)) +
          ∑ μ, rhoM (gD Bf hB uh μ) * rhoM (gB (c := c) (r := r) Bf hB μ)) +
        ∑ μ, rhoM (gD Bf hB uh μ) * rhoM (gV uh) * rhoM (gD Bf hB uh μ)))
      ≤ ∑ _ν : Fin 4, ((H * b + cv * (2 * (m : ℝ) ^ 2) * b) + 2 * (4 * (P * b + cv * δ * b)) +
        4 * (2 * (2 * (m : ℝ) ^ 2) * δ * Y + δ * (CS * (δ * δ + 4 * (Y * δ + δ * Y))) +
          δ * (b * (2 * (m : ℝ) ^ 2)) * δ)) := by
        refine Finset.sum_le_sum fun ν _ => ?_
        rw [map_add, map_add, map_add]
        have ha := mN_derM_UM_le hK hS hH ν
        have hb := mN_derM_S1_le hK hS hP ν
        have hc : mN 2 (derM ν (∑ μ, rhoM (gD Bf hB uh μ) * rhoM (gV uh) *
            rhoM (gD Bf hB uh μ))) ≤ 4 * (2 * (2 * (m : ℝ) ^ 2) * δ * Y +
              δ * (CS * (δ * δ + 4 * (Y * δ + δ * Y))) + δ * (b * (2 * (m : ℝ) ^ 2)) * δ) := by
          rw [map_sum]
          refine (mN_sum_le (by norm_num) _ _).trans ?_
          calc _ ≤ ∑ _μ : Fin 4, (2 * (2 * (m : ℝ) ^ 2) * δ * Y +
                δ * (CS * (δ * δ + 4 * (Y * δ + δ * Y))) + δ * (b * (2 * (m : ℝ) ^ 2)) * δ) :=
                Finset.sum_le_sum fun μ _ => mN_derM_DVD_le hK hS hY ν μ
            _ = _ := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                push_cast; ring
        refine ((mN_add_le (by norm_num) _ _).trans (add_le_add ((mN_add_le (by norm_num) _ _).trans
          (add_le_add ha ((mN_add_le (by norm_num) _ _).trans (add_le_add hb hb)))) hc)).trans
          (le_of_eq (by ring))
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast
        ring

/-- **The `H³` bound by absorption**: there are a universal threshold `θ ∈ (0, 1]` and, for
every `H₂, b`, a bound `K₃` such that `‖û‖_{H³} ≤ K₃` whenever `δ ≤ θ` and `‖û‖_{H²} ≤ H₂`. -/
theorem hM3_le (hK : SobConsts c r m CS cv) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ ∀ H2 b : ℝ, ∃ K3 : ℝ, ∀ {Bf : CriticalGauge.MConn m}
      {hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j)} {uh : MatSob c r 10 m} {δ : ℝ},
      HSet Bf hB uh b δ → δ ≤ θ → hM 2 (by norm_num) uh ≤ H2 → hM 3 (by norm_num) uh ≤ K3 := by
  obtain ⟨CN, hCN0, hCN⟩ := neumann_est_matrix (c := c) (r := r) (m := m) 1 8 (by norm_num)
    (by norm_num)
  set Ub : ℝ := 2 * (m : ℝ) ^ 2 with hUb
  have hUb0 : 0 ≤ Ub := by positivity
  have hCS := hK.CS0
  have hcv := hK.cv0
  set G : ℝ := CN * (16 * (2 * Ub + 8 * CS)) * (4 * CS) with hG
  have hG0 : 0 ≤ G := by positivity
  refine ⟨1 / (2 * G + 2), by positivity, ?_, fun H2 b => ?_⟩
  · rw [div_le_one (by positivity)]; linarith
  set P : ℝ := H2 + (H2 + cv * Ub) * b with hPdef
  set Y0 : ℝ := CS * (P + 4 * ((H2 + 2 * H2 + cv * Ub) * b)) with hY0def
  -- the bound with `δ` replaced by `1`
  refine ⟨2 * CN * ((Ub * (cv * b) + 2 * (4 * (cv * 1 * b)) + 4 * (1 * Ub * 1)) +
    4 * ((H2 * b + cv * Ub * b) + 2 * (4 * (P * b + cv * 1 * b)) +
      4 * (1 * (CS * (1 * 1)) + 1 * (b * Ub) * 1)) +
    16 * (2 * Ub * 1 + 8 * CS * 1 * 1) * Y0 + cv * Ub), fun {Bf hB uh δ} hS hδθ hH2 => ?_⟩
  have hδ0 := hS.δ0
  have hb0 := hS.b0
  have hδ1 : δ ≤ 1 := hδθ.trans (by rw [div_le_one (by positivity)]; linarith)
  set x := hM 3 (by norm_num) uh with hx
  have hx0 : 0 ≤ x := hM_nonneg _ _ _
  have hh1 : hM 1 (by norm_num) uh ≤ H2 := (h1_le_h2 uh).trans hH2
  have hH20 : 0 ≤ H2 := (hM_nonneg _ _ _).trans hH2
  have hP : ∀ ν μ, mN 2 (derM ν (gD Bf hB uh μ)) ≤ P := fun ν μ =>
    (mN_dgD_two hK hS ν μ).trans (by rw [hPdef]; gcongr)
  have hY : ∀ l μ, mN 4 (derM l (gD Bf hB uh μ)) ≤ Y0 + 4 * CS * x := by
    intro l μ
    refine (mN4_dgD hK hS l μ).trans (le_of_le_of_eq ?_ (show CS * (P + 4 * (x + (H2 + 2 * H2 +
      cv * Ub) * b)) = Y0 + 4 * CS * x by rw [hY0def]; ring))
    rw [hPdef]
    gcongr
  have hsum := sum_mN_derM_gQ_le hK hS hh1 hP hY
  have hQ2 := mN_gQ_le hK hS
  have hN := hCN uh hS.neum
  rw [hS.lap] at hN
  have h1Q : hM 1 (by norm_num) (gQ Bf hB uh) ≤
      mN 2 (gQ Bf hB uh) + ∑ ν, mN 2 (derM ν (gQ Bf hB uh)) := by
    have := hM_succ_le 0 (by norm_num) (gQ Bf hB uh)
    rw [Finset.sum_congr rfl fun ν _ => hM_zero _ _] at this
    exact this
  have huh := mN_uh_two hK hS
  -- the absorption
  set α : ℝ := 16 * (2 * Ub * δ + 8 * CS * δ * δ) with hα
  have hα0 : 0 ≤ α := by positivity
  have hαle : CN * α * (4 * CS) ≤ 1 / 2 := by
    have h1 : α ≤ 16 * (2 * Ub + 8 * CS) * δ := by
      rw [hα]; nlinarith [mul_le_mul_of_nonneg_left hδ1 (by positivity : 0 ≤ 8 * CS * δ)]
    have h2 : CN * α * (4 * CS) ≤ G * δ := by
      rw [hG]
      calc CN * α * (4 * CS) ≤ CN * (16 * (2 * Ub + 8 * CS) * δ) * (4 * CS) := by gcongr
        _ = CN * (16 * (2 * Ub + 8 * CS)) * (4 * CS) * δ := by ring
    have h3 : G * δ ≤ G * (1 / (2 * G + 2)) := mul_le_mul_of_nonneg_left hδθ hG0
    have h4 : G * (1 / (2 * G + 2)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  set Sc : ℝ := 4 * ((H2 * b + cv * Ub * b) + 2 * (4 * (P * b + cv * δ * b)) +
      4 * (δ * (CS * (δ * δ)) + δ * (b * Ub) * δ)) with hSc
  have hsum' : ∑ ν, mN 2 (derM ν (gQ Bf hB uh)) ≤ Sc + α * Y0 + (α * (4 * CS)) * x := by
    refine hsum.trans (le_of_eq ?_)
    rw [hSc, hα, hUb]; ring
  set Q2 : ℝ := Ub * (cv * b) + 2 * (4 * (cv * δ * b)) + 4 * (δ * Ub * δ) with hQ2def
  have hQ2' : mN 2 (gQ Bf hB uh) ≤ Q2 := by rw [hQ2def, hUb]; exact hQ2
  have hmain : x ≤ CN * (Q2 + Sc + α * Y0 + cv * Ub) + (CN * α * (4 * CS)) * x := by
    have := hN.trans (mul_le_mul_of_nonneg_left (add_le_add (h1Q.trans (add_le_add hQ2' hsum'))
      huh) hCN0)
    calc x ≤ CN * (Q2 + (Sc + α * Y0 + α * (4 * CS) * x) + cv * (2 * (m : ℝ) ^ 2)) := this
      _ = _ := by rw [hUb]; ring
  have habs : (CN * α * (4 * CS)) * x ≤ 1 / 2 * x := mul_le_mul_of_nonneg_right hαle hx0
  have hfin : x ≤ 2 * CN * (Q2 + Sc + α * Y0 + cv * Ub) := by linarith
  refine hfin.trans ?_
  have hY00 : 0 ≤ Y0 := by rw [hY0def, hPdef]; positivity
  rw [hQ2def, hSc, hα]
  gcongr


end E3

end RenewalGeometry.BallAnalysis.HigherE3
