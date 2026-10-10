/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallHigherE4c

/-!
# The `H⁵` and `H⁶` a-priori bounds for lifted Coulomb gauges (Banach algebra levels)
  (stage D2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

Once `‖û‖_{H⁴}` is bounded, the covariant derivative `D = ∂û - U B` is bounded in `H³`, which is
a Banach algebra on the four-dimensional ball (`SobAlg`), so the right-hand side of the gauge
equation is bounded in `H³` and the Neumann estimate gives `H⁵`; one more round gives `H⁶`.

* `hM_restrM'`, `hM_star`, `norm_restrM_le_hM` — jet seminorms of restrictions and adjoints;
* `norm_restrM_gQ_le` — the algebra norm of the right-hand side at level `t ∈ {3, 4}`;
* `hM5_le`, `hM6_le` — the `H⁵` and `H⁶` bounds.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.HigherE56

open SobolevOpen BallReg BallAlg SobAlg HigherNorms HigherIdent HigherLeibniz HigherE3 HigherE4

set_option linter.unusedSectionVars false

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m : ℕ}

/-! ### Jet seminorms of restrictions and adjoints -/

section Jet

variable {s : ℕ} [Fact (3 ≤ s)]

theorem hM_restrM' {s' : ℕ} [Fact (3 ≤ s')] (h : s' ≤ s) (K : ℕ) (hK : K ≤ s')
    (X : MatSob c r s m) : hM K hK (restrM h X) = hM K (hK.trans h) X :=
  (rfl : hM K hK (restrM h X) = hM K (hK.trans h) X).trans (Eq.refl _)

theorem hS_neg (K : ℕ) (hK : K ≤ s) (F : SobAlg c r s) : hS K hK (-F) = hS K hK F := by
  unfold hS
  refine Finset.sum_congr rfl fun w _ => ?_
  have : restrL c r hK (jet (-F)) = -restrL c r hK (jet F) := by
    rw [← map_neg]; rfl
  rw [this]
  exact norm_neg _

theorem hM_star (K : ℕ) (hK : K ≤ s) (X : MatSob c r s m) : hM K hK (star X) = hM K hK X := by
  unfold hM
  simp only [Matrix.star_apply, Cx.star_re', Cx.star_im', hS_neg]
  rw [Finset.sum_comm]

theorem norm_restrM_le_hM {s' : ℕ} [Fact (3 ≤ s')] (h : s' ≤ s) (X : MatSob c r s m) :
    ‖restrM h X‖ ≤ (m : ℝ) * Kal c r s' * hM s' h X := by
  have := norm_le_hM (restrM h X)
  rwa [hM_restrM'] at this

end Jet

/-! ### The right-hand side in the Banach algebra -/

section Algebra

variable {Bf : CriticalGauge.MConn m} {hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j)}

theorem restrM_rhoM {s s' : ℕ} [Fact (3 ≤ s)] [Fact (3 ≤ s')] (h : s' ≤ s)
    (X : MatSob c r (s + 1) m) : restrM h (rhoM X) = restrM (h.trans (Nat.le_succ s)) X := by
  rw [rhoM_eq_restrM, restrM_restrM]

theorem norm_derM_le_hM {s : ℕ} [Fact (3 ≤ s)] (μ : Fin 4) (X : MatSob c r (s + 1) m) :
    ‖derM μ X‖ ≤ (m : ℝ) * Kal c r s * hM (s + 1) le_rfl X := by
  refine (norm_le_hM (derM μ X)).trans ?_
  have hK := (Kal_pos c r s).le
  exact mul_le_mul_of_nonneg_left (hM_derM_le s le_rfl μ X) (by positivity)

/-- **The right-hand side of the gauge equation in the algebra `H^t`**, `t ≤ 4`. -/
theorem norm_restrM_gQ_le (t : ℕ) [Fact (3 ≤ t)] [Fact (3 ≤ t + 1)] (ht : t ≤ 4)
    (uh : MatSob c r 10 m) {β : ℝ} (hβ0 : 0 ≤ β)
    (hBn : ∀ μ, ‖restrM (by omega : t ≤ 9) (gB (c := c) (r := r) Bf hB μ)‖ ≤ β)
    (hMn : ‖restrM (by omega : t ≤ 8) (gM (c := c) (r := r) Bf hB)‖ ≤ β) :
    ‖restrM (by omega : t ≤ 8) (gQ Bf hB uh)‖ ≤
      ((m : ℝ) * Kal c r t * hM t (by omega) uh) * β +
      2 * (4 * ((((m : ℝ) * Kal c r t * hM (t + 1) (by omega) uh) +
        ((m : ℝ) * Kal c r t * hM t (by omega) uh) * β) * β)) +
      4 * (((((m : ℝ) * Kal c r t * hM (t + 1) (by omega) uh) +
        ((m : ℝ) * Kal c r t * hM t (by omega) uh) * β) *
        ((m : ℝ) * Kal c r t * hM t (by omega) uh)) *
        (((m : ℝ) * Kal c r t * hM (t + 1) (by omega) uh) +
        ((m : ℝ) * Kal c r t * hM t (by omega) uh) * β)) := by
  set a := (m : ℝ) * Kal c r t * hM t (by omega) uh with ha
  set a1 := (m : ℝ) * Kal c r t * hM (t + 1) (by omega) uh with ha1
  have hK0 := (Kal_pos c r t).le
  have ha0 : 0 ≤ a := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hK0) (hM_nonneg _ _ _)
  have ha10 : 0 ≤ a1 := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hK0) (hM_nonneg _ _ _)
  -- the factors
  have hU : ‖restrM (by omega : t ≤ 10) uh‖ ≤ a := norm_restrM_le_hM _ uh
  have hV : ‖star (restrM (by omega : t ≤ 10) uh)‖ ≤ a := by
    have := norm_le_hM (star (restrM (by omega : t ≤ 10) uh))
    rw [hM_star, hM_restrM'] at this
    exact this
  have hD : ∀ μ, ‖restrM (by omega : t ≤ 9) (gD Bf hB uh μ)‖ ≤ a1 + a * β := by
    intro μ
    rw [gD, map_sub, map_mul, restrM_derM, gU, restrM_rhoM]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_derM_le_hM μ _).trans
      (le_of_eq (by rw [hM_restrM']))) ((norm_mul_le _ _).trans
        (mul_le_mul hU (hBn μ) (norm_nonneg _) ha0)))
  unfold gQ
  rw [two_mul, map_add, map_add, map_add, map_mul, map_sum, map_sum]
  simp only [map_mul, restrM_rhoM, gU, gV, restrM_star]
  have hq0 : 0 ≤ a1 + a * β := add_nonneg ha10 (mul_nonneg ha0 hβ0)
  have key : ∀ (S : Fin 4 → MatSob c r t m) (q : ℝ), (∀ μ, ‖S μ‖ ≤ q) → ‖∑ μ, S μ‖ ≤ 4 * q := by
    intro S q hS
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_sum fun μ (_ : μ ∈ Finset.univ) => hS μ
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    exact this
  have hterm : ∀ μ, ‖restrM (by omega : t ≤ 9) (gD Bf hB uh μ) *
      restrM (by omega : t ≤ 9) (gB (c := c) (r := r) Bf hB μ)‖ ≤ (a1 + a * β) * β :=
    fun μ => (norm_mul_le _ _).trans (mul_le_mul (hD μ) (hBn μ) (norm_nonneg _) hq0)
  have hterm2 : ∀ μ, ‖restrM (by omega : t ≤ 9) (gD Bf hB uh μ) *
      star (restrM (by omega : t ≤ 10) uh) * restrM (by omega : t ≤ 9) (gD Bf hB uh μ)‖ ≤
      (a1 + a * β) * a * (a1 + a * β) :=
    fun μ => (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul (hD μ) hV
      (norm_nonneg _) hq0)) (hD μ) (norm_nonneg _) (mul_nonneg hq0 ha0))
  have h1 := (norm_mul_le _ _).trans (mul_le_mul hU hMn (norm_nonneg _) ha0)
  have h2 := key _ _ hterm
  have h3 := key _ _ hterm2
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1
    ((norm_add_le _ _).trans (add_le_add h2 h2)))) h3) |>.trans (le_of_eq (by ring))

end Algebra

/-! ### The `H⁵` and `H⁶` bounds -/

section Top

variable {CS cv : ℝ}

/-- The polynomial majorant of `norm_restrM_gQ_le` with the jet seminorms replaced by `H`. -/
def qA (K β H : ℝ) : ℝ :=
  (K * H) * β + 2 * (4 * ((K * H + (K * H) * β) * β)) +
    4 * (((K * H + (K * H) * β) * (K * H)) * (K * H + (K * H) * β))

theorem qA_ge {K β H x y : ℝ} (hβ : 0 ≤ β) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x ≤ K * H)
    (hy : y ≤ K * H) :
    x * β + 2 * (4 * ((y + x * β) * β)) + 4 * (((y + x * β) * x) * (y + x * β)) ≤ qA K β H := by
  unfold qA
  have hX : 0 ≤ K * H := hx0.trans hx
  have h1 : x * β ≤ K * H * β := mul_le_mul_of_nonneg_right hx hβ
  have hz : y + x * β ≤ K * H + K * H * β := add_le_add hy h1
  have hz0 : 0 ≤ y + x * β := add_nonneg hy0 (mul_nonneg hx0 hβ)
  have h2 : (y + x * β) * β ≤ (K * H + K * H * β) * β := mul_le_mul_of_nonneg_right hz hβ
  have h3 : (y + x * β) * x ≤ (K * H + K * H * β) * (K * H) := mul_le_mul hz hx hx0 (hz0.trans hz)
  have h4 : ((y + x * β) * x) * (y + x * β) ≤ ((K * H + K * H * β) * (K * H)) *
      (K * H + K * H * β) := mul_le_mul h3 hz hz0 (mul_nonneg (hz0.trans hz) hX)
  linarith

set_option maxHeartbeats 800000 in
/-- **The level-`t` bound** (`t ∈ {3,4}`): `‖û‖_{H^{t+2}} ≤ C_N (C_t q_A(‖û‖_{H^{t+1}}) + c_v U_b)`. -/
theorem hM_top_le (t : ℕ) [Fact (3 ≤ t)] [Fact (3 ≤ t + 1)] (ht : t ≤ 4)
    (hK : SobConsts c r m CS cv) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β H : ℝ), 0 ≤ β → ∀ {Bf : CriticalGauge.MConn m}
      {hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j)} {uh : MatSob c r 10 m} {b δ : ℝ},
      HSet Bf hB uh b δ →
      (∀ μ, ‖restrM (by omega : t ≤ 9) (gB (c := c) (r := r) Bf hB μ)‖ ≤ β) →
      ‖restrM (by omega : t ≤ 8) (gM (c := c) (r := r) Bf hB)‖ ≤ β →
      hM (t + 1) (by omega) uh ≤ H →
      hM (t + 2) (by omega) uh ≤ C * (qA ((m : ℝ) * Kal c r t) β H + cv * (2 * (m : ℝ) ^ 2)) := by
  obtain ⟨CN, hCN0, hCN⟩ := neumann_est_matrix (c := c) (r := r) (m := m) t 8 (by norm_num)
    (by omega)
  obtain ⟨Ct, hCt0, hCt⟩ := hM_le_norm (c := c) (r := r) (m := m) (s := t) t le_rfl
  refine ⟨CN * max Ct 1, by positivity, fun β H hβ {Bf hB uh b δ} hS hBn hMn hH => ?_⟩
  have hN := hCN uh hS.neum
  rw [hS.lap] at hN
  have hK0 := (Kal_pos c r t).le
  have hmK : 0 ≤ (m : ℝ) * Kal c r t := mul_nonneg (Nat.cast_nonneg _) hK0
  have hht : hM t (by omega) uh ≤ hM (t + 1) (by omega) uh := hM_mono t (by omega) uh
  have hQ := norm_restrM_gQ_le (Bf := Bf) (hB := hB) t ht uh hβ hBn hMn
  have hQ' : ‖restrM (by omega : t ≤ 8) (gQ Bf hB uh)‖ ≤ qA ((m : ℝ) * Kal c r t) β H := by
    refine hQ.trans ?_
    have h0 : 0 ≤ hM t (by omega : t ≤ 10) uh := hM_nonneg _ _ _
    have h1 : (m : ℝ) * Kal c r t * hM t (by omega) uh ≤ (m : ℝ) * Kal c r t * H :=
      mul_le_mul_of_nonneg_left (hht.trans hH) hmK
    have h2 : (m : ℝ) * Kal c r t * hM (t + 1) (by omega) uh ≤ (m : ℝ) * Kal c r t * H :=
      mul_le_mul_of_nonneg_left hH hmK
    have h3 : 0 ≤ (m : ℝ) * Kal c r t * hM t (by omega) uh := mul_nonneg hmK h0
    have h4 : 0 ≤ (m : ℝ) * Kal c r t * hM (t + 1) (by omega) uh := mul_nonneg hmK (hM_nonneg _ _ _)
    exact qA_ge hβ h3 h4 h1 h2
  have hl : hM t (by omega) (gQ Bf hB uh) ≤ Ct * qA ((m : ℝ) * Kal c r t) β H := by
    have := hCt (restrM (by omega : t ≤ 8) (gQ Bf hB uh))
    rw [hM_restrM'] at this
    exact this.trans (mul_le_mul_of_nonneg_left hQ' hCt0)
  have hqA0 : 0 ≤ qA ((m : ℝ) * Kal c r t) β H := by
    refine le_trans ?_ hQ'
    exact norm_nonneg _
  have huh := mN_uh_two hK hS
  have hcv0 : 0 ≤ cv * (2 * (m : ℝ) ^ 2) := mul_nonneg hK.cv0 (by positivity)
  have hsum : hM t (by omega) (gQ Bf hB uh) + mN 2 uh ≤
      max Ct 1 * (qA ((m : ℝ) * Kal c r t) β H + cv * (2 * (m : ℝ) ^ 2)) :=
    calc hM t (by omega) (gQ Bf hB uh) + mN 2 uh
        ≤ Ct * qA ((m : ℝ) * Kal c r t) β H + cv * (2 * (m : ℝ) ^ 2) := add_le_add hl huh
      _ ≤ max Ct 1 * qA ((m : ℝ) * Kal c r t) β H + max Ct 1 * (cv * (2 * (m : ℝ) ^ 2)) :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hqA0)
            (le_mul_of_one_le_left hcv0 (le_max_right _ _))
      _ = _ := by ring
  exact hN.trans ((mul_le_mul_of_nonneg_left hsum hCN0).trans (le_of_eq (by ring)))

end Top

end RenewalGeometry.BallAnalysis.HigherE56
