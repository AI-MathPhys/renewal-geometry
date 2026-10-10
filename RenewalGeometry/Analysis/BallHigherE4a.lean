/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallHigherE3

/-!
# Second-derivative product bounds for the `H⁴` a-priori bound of lifted Coulomb gauges
  (stage D2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `qq` — the quartic bound `‖X‖_{L⁴} C_S ‖W^* Z‖_{H¹}`-majorant;
* `mN_derM_mul_star_mul_le` — derivative of a product `X W^* Z` of three critical factors;
* `mN_mul_mul_star_mul_le` — the product `X (K W^*) Z` with a bounded factor `K`;
* `mN_dddgD_two`, `mN4_ddgD` — third derivatives of the covariant derivative `D` in `L²` and
  second derivatives in `L⁴` (critical Sobolev).
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.HigherE4

open SobolevOpen BallReg BallAlg SobAlg HigherNorms HigherIdent HigherLeibniz HigherE3

set_option linter.unusedSectionVars false

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m : ℕ}

/-- `mN_rhoM` as a propositional (non-`rfl`) rewrite rule, safe for `simp`. -/
theorem mN_rhoM' {s : ℕ} [Fact (3 ≤ s)] (p : ℝ≥0∞) (X : MatSob c r (s + 1) m) :
    mN p (rhoM X) = mN p X :=
  (mN_rhoM p X).trans (Eq.refl _)

/-! ### Quartic products -/

section Products

variable {s : ℕ} [Fact (3 ≤ s)]

/-- The majorant `‖X‖_{L⁴} · C_S (‖W‖_{L⁴}‖Z‖_{L⁴} + Σ_k (‖∂_kW‖_{L⁴}‖Z‖_{L⁴} + ‖W‖_{L⁴}‖∂_kZ‖_{L⁴}))`. -/
def qq (CS : ℝ) (X : MatSob c r (s + 1) m) (W Z : MatSob c r (s + 1) m) : ℝ :=
  mN 4 X * (CS * (mN 4 W * mN 4 Z + ∑ k, (mN 4 (derM k W) * mN 4 Z + mN 4 W * mN 4 (derM k Z))))

theorem qq_rhoM (CS : ℝ) (X W Z : MatSob c r (s + 2) m) :
    qq CS (rhoM X) (rhoM W) (rhoM Z) = mN 4 X * (CS * (mN 4 W * mN 4 Z +
      ∑ k, (mN 4 (derM k W) * mN 4 Z + mN 4 W * mN 4 (derM k Z)))) := by
  unfold qq
  simp only [derM_rhoM]
  rw [mN_rhoM, mN_rhoM, mN_rhoM, Finset.sum_congr rfl fun k _ => by rw [mN_rhoM, mN_rhoM]]

/-- **Derivative of a product of three critical factors** `X W^* Z`. -/
theorem mN_derM_mul_star_mul_le {CS cv : ℝ} (hK : SobConsts c r m CS cv) (l : Fin 4)
    (X W Z : MatSob c r (s + 2) m) :
    mN 2 (derM l (X * star W * Z)) ≤ qq CS (derM l X) (rhoM W) (rhoM Z) +
      qq CS (rhoM X) (derM l W) (rhoM Z) + qq CS (rhoM X) (rhoM W) (derM l Z) := by
  rw [derM_mul, derM_mul, derM_star, add_mul, map_mul, rhoM_star]
  have h1 := mN_mul_star_mul_le hK (derM l X) (rhoM W) (rhoM Z)
  have h2 := mN_mul_star_mul_le hK (rhoM X) (derM l W) (rhoM Z)
  have h3 := mN_mul_star_mul_le hK (rhoM X) (rhoM W) (derM l Z)
  have hs1 := mN_add_le (p := 2) (by norm_num)
    (derM l X * star (rhoM W) * rhoM Z + rhoM X * star (derM l W) * rhoM Z)
    (rhoM X * star (rhoM W) * derM l Z)
  have hs2 := mN_add_le (p := 2) (by norm_num) (derM l X * star (rhoM W) * rhoM Z)
    (rhoM X * star (derM l W) * rhoM Z)
  unfold qq
  linarith

/-- **A bounded factor before a critical quartic product**:
`‖X K W^* Z‖_{L²} ≤ ‖X‖_{L⁴} ‖K‖_{L^∞} C_S ‖W^* Z‖_{H¹}`. -/
theorem mN_mul_mul_star_mul_le {CS cv : ℝ} (hK : SobConsts c r m CS cv)
    (X K W Z : MatSob c r (s + 1) m) :
    mN 2 (X * (K * star W) * Z) ≤ mN 4 X * mN ⊤ K * (CS * (mN 4 W * mN 4 Z +
      ∑ k, (mN 4 (derM k W) * mN 4 Z + mN 4 W * mN 4 (derM k Z)))) := by
  rw [show X * (K * star W) * Z = X * (K * (star W * Z)) by noncomm_ring, mul_assoc]
  refine (mN_mul_le_44 _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ((mN_mul_le_inf4 _ _).trans
    (mul_le_mul_of_nonneg_left ?_ (mN_nonneg _ _))) (mN_nonneg _ _)
  refine (hK.sob (star W * Z)).trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hK.CS0)
  · exact (mN_mul_le_44 _ _).trans (le_of_eq (by rw [mN_star]))
  · refine Finset.sum_le_sum fun k _ => (mN_derM_mul_le_44 k _ _).trans (le_of_eq ?_)
    rw [derM_star, mN_star, mN_star]

end Products

theorem pm {x y X Y : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x ≤ X) (hy : y ≤ Y) : x * y ≤ X * Y :=
  mul_le_mul hx hy hy0 (hx0.trans hx)

/-! ### Third derivatives of `D` -/

section Third

variable {Bf : CriticalGauge.MConn m} {hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j)}
  {uh : MatSob c r 10 m} {b δ CS cv : ℝ}

/-- `‖∂_k ∂_l ∂_ν D_μ‖_{L²} ≤ ‖û‖_{H⁴} + (‖û‖_{H³} + 3‖û‖_{H²} + 3‖û‖_{H¹} + c_v U_b) b`. -/
theorem mN_dddgD_two (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) (k l ν μ : Fin 4) :
    mN 2 (derM k (derM l (derM ν (gD Bf hB uh μ)))) ≤ hM 4 (by norm_num) uh +
      (hM 3 (by norm_num) uh + 3 * hM 2 (by norm_num) uh + 3 * hM 1 (by norm_num) uh +
        cv * (2 * (m : ℝ) ^ 2)) * b := by
  have hb0 := hS.b0
  rw [gD, map_sub, map_sub, map_sub]
  refine (mN_sub_le (by norm_num) _ _).trans ?_
  have h0 := mN_d4_le uh k l ν μ
  rw [derM_mul, map_add, map_add, derM_mul, derM_mul, map_add, map_add]
  -- the four products
  have p1 := mN_derM_mul_le_2i (s := 6) k (derM l (derM ν (gU uh))) (rhoM (rhoM (gB (c := c) (r := r) Bf hB μ)))
  have p2 := mN_derM_mul_le_2i (s := 6) k (rhoM (derM ν (gU uh))) (derM l (rhoM (gB (c := c) (r := r) Bf hB μ)))
  have p3 := mN_derM_mul_le_2i (s := 6) k (derM l (rhoM (gU uh))) (rhoM (derM ν (gB (c := c) (r := r) Bf hB μ)))
  have p4 := mN_derM_mul_le_2i (s := 6) k (rhoM (rhoM (gU uh))) (derM l (derM ν (gB (c := c) (r := r) Bf hB μ)))
  have u3 := mN_dddgU_two (uh := uh) k l ν
  have u2 := mN_ddgU_two (uh := uh) l ν
  have u2' := mN_ddgU_two (uh := uh) k ν
  have u2'' := mN_ddgU_two (uh := uh) k l
  have u1 := mN_dgU_two (uh := uh) ν
  have u1' := mN_dgU_two (uh := uh) l
  have u1'' := mN_dgU_two (uh := uh) k
  have u0 := mN_gU_two hK hS
  have q1 := pm (mN_nonneg _ _) (mN_nonneg _ _) u3 (hS.bb.B μ)
  have q2 := pm (mN_nonneg _ _) (mN_nonneg _ _) u2 (hS.bb.dB k μ)
  have q3 := pm (mN_nonneg _ _) (mN_nonneg _ _) u2' (hS.bb.dB l μ)
  have q4 := pm (mN_nonneg _ _) (mN_nonneg _ _) u1 (hS.bb.ddB k l μ)
  have q5 := pm (mN_nonneg _ _) (mN_nonneg _ _) u2'' (hS.bb.dB ν μ)
  have q6 := pm (mN_nonneg _ _) (mN_nonneg _ _) u1' (hS.bb.ddB k ν μ)
  have q7 := pm (mN_nonneg _ _) (mN_nonneg _ _) u1'' (hS.bb.ddB l ν μ)
  have q8 := pm (mN_nonneg _ _) (mN_nonneg _ _) u0 (hS.bb.dddB k l ν μ)
  have hs1 := mN_add_le (p := 2) (by norm_num)
    (derM k (derM l (derM ν (gU uh)) * rhoM (rhoM (gB (c := c) (r := r) Bf hB μ))) + derM k (rhoM (derM ν (gU uh)) *
      derM l (rhoM (gB (c := c) (r := r) Bf hB μ))))
    (derM k (derM l (rhoM (gU uh)) * rhoM (derM ν (gB (c := c) (r := r) Bf hB μ))) + derM k (rhoM (rhoM (gU uh)) *
      derM l (derM ν (gB (c := c) (r := r) Bf hB μ))))
  have hs2 := mN_add_le (p := 2) (by norm_num) (derM k (derM l (derM ν (gU uh)) * rhoM (rhoM (gB (c := c) (r := r) Bf hB μ))))
    (derM k (rhoM (derM ν (gU uh)) * derM l (rhoM (gB (c := c) (r := r) Bf hB μ))))
  have hs3 := mN_add_le (p := 2) (by norm_num) (derM k (derM l (rhoM (gU uh)) * rhoM (derM ν (gB (c := c) (r := r) Bf hB μ))))
    (derM k (rhoM (rhoM (gU uh)) * derM l (derM ν (gB (c := c) (r := r) Bf hB μ))))
  simp only [derM_rhoM] at p1 p2 p3 p4 hs1 hs2 hs3 ⊢
  repeat rw [mN_rhoM] at p1
  repeat rw [mN_rhoM] at p2
  repeat rw [mN_rhoM] at p3
  repeat rw [mN_rhoM] at p4
  linarith

theorem mN4_ddgD (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) (l ν μ : Fin 4) :
    mN 4 (derM l (derM ν (gD Bf hB uh μ))) ≤ CS * ((hM 3 (by norm_num) uh +
      (hM 2 (by norm_num) uh + 2 * hM 1 (by norm_num) uh + cv * (2 * (m : ℝ) ^ 2)) * b) +
      4 * (hM 4 (by norm_num) uh + (hM 3 (by norm_num) uh + 3 * hM 2 (by norm_num) uh +
        3 * hM 1 (by norm_num) uh + cv * (2 * (m : ℝ) ^ 2)) * b)) := by
  refine (hK.sob (derM l (derM ν (gD Bf hB uh μ)))).trans ?_
  refine mul_le_mul_of_nonneg_left (add_le_add (mN_ddgD_two hK hS l ν μ) ?_) hK.CS0
  calc ∑ k, mN 2 (derM k (derM l (derM ν (gD Bf hB uh μ))))
      ≤ ∑ _k : Fin 4, (hM 4 (by norm_num) uh + (hM 3 (by norm_num) uh +
          3 * hM 2 (by norm_num) uh + 3 * hM 1 (by norm_num) uh + cv * (2 * (m : ℝ) ^ 2)) * b) :=
        Finset.sum_le_sum fun k _ => mN_dddgD_two hK hS k l ν μ
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast
        ring

end Third

end RenewalGeometry.BallAnalysis.HigherE4
