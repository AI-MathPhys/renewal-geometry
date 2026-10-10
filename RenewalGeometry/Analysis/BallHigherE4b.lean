/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallHigherE4a

/-!
# Second derivatives of the quadratic term `D V D` of the gauge equation
  (stage D2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `derM_DVD` — `∂_ν(D V D) = ∂D V D + D D_ν^* D + D (B_ν^* V) D + D V ∂D`;
* `mN_ddDVD_le` — the `L²` norm of `∂_l ∂_ν (D_μ V D_μ)` is bounded by an expression in which
  the second derivatives of `D` (hence `‖û‖_{H⁴}`) appear only with a factor `δ`
  (`‖D‖_{L⁴} ≤ δ`), so that they can be absorbed.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.HigherE4

open SobolevOpen BallReg BallAlg SobAlg HigherNorms HigherIdent HigherLeibniz HigherE3

set_option linter.unusedSectionVars false

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m : ℕ}

section DVD

variable {Bf : CriticalGauge.MConn m} {hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j)}
  {uh : MatSob c r 10 m} {b δ CS cv : ℝ}

theorem derM_rhoM_rhoM_gV (l : Fin 4) :
    derM l (rhoM (rhoM (gV uh))) = star (rhoM (rhoM (rhoM (gD Bf hB uh l)))) +
      star (rhoM (rhoM (rhoM (gB (c := c) (r := r) Bf hB l)))) * rhoM (rhoM (rhoM (gV uh))) := by
  rw [derM_rhoM, derM_rhoM, derM_gV (Bf := Bf) (hB := hB), map_add, map_add, map_mul, map_mul,
    rhoM_star, rhoM_star, rhoM_star, rhoM_star]

theorem derM_DVD (ν μ : Fin 4) :
    derM ν (rhoM (gD Bf hB uh μ) * rhoM (gV uh) * rhoM (gD Bf hB uh μ)) =
      derM ν (rhoM (gD Bf hB uh μ)) * rhoM (rhoM (gV uh)) * rhoM (rhoM (gD Bf hB uh μ)) +
      rhoM (rhoM (gD Bf hB uh μ)) * star (rhoM (rhoM (gD Bf hB uh ν))) *
        rhoM (rhoM (gD Bf hB uh μ)) +
      rhoM (rhoM (gD Bf hB uh μ)) * (star (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν))) *
        rhoM (rhoM (gV uh))) * rhoM (rhoM (gD Bf hB uh μ)) +
      rhoM (rhoM (gD Bf hB uh μ)) * rhoM (rhoM (gV uh)) * derM ν (rhoM (gD Bf hB uh μ)) := by
  rw [derM_mul, derM_mul, derM_rhoM (X := gV uh), derM_gV (Bf := Bf) (hB := hB), map_add, map_mul,
    rhoM_star, rhoM_star, map_mul, add_mul, mul_add, add_mul]
  abel

theorem c1_le (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) {Y Y2 : ℝ}
    (hY : ∀ ν μ, mN 4 (derM ν (gD Bf hB uh μ)) ≤ Y)
    (hY2 : ∀ l ν μ, mN 4 (derM l (derM ν (gD Bf hB uh μ))) ≤ Y2) (l ν μ : Fin 4) :
    mN 2 (derM l (derM ν (rhoM (gD Bf hB uh μ)) * rhoM (rhoM (gV uh)) *
      rhoM (rhoM (gD Bf hB uh μ)))) ≤
      Y2 * (2 * (m : ℝ) ^ 2) * δ + (Y * (CS * (δ * δ + ∑ _k : Fin 4, (Y * δ + δ * Y))) +
        Y * (b * (2 * (m : ℝ) ^ 2)) * δ) + Y * (2 * (m : ℝ) ^ 2) * Y := by
  have hV := mN_gV_top hS
  have hD := hS.D4
  have hδ := hS.δ0
  have hb := hS.b0
  have hY0 : 0 ≤ Y := (mN_nonneg _ _).trans (hY 0 0)
  have hCS := hK.CS0
  refine (mN_derM_mul3_le (s := 6) l (derM ν (rhoM (gD Bf hB uh μ))) (rhoM (rhoM (gV uh)))
    (rhoM (rhoM (gD Bf hB uh μ)))).trans ?_
  rw [derM_rhoM_rhoM_gV (Bf := Bf) (hB := hB), mul_add, add_mul]
  have m1 := mN_mul_star_mul_le (s := 5) hK (rhoM (derM ν (rhoM (gD Bf hB uh μ))))
    (rhoM (rhoM (rhoM (gD Bf hB uh l)))) (rhoM (rhoM (rhoM (gD Bf hB uh μ))))
  have m2 := mN_mul3_le (rhoM (derM ν (rhoM (gD Bf hB uh μ))))
    (star (rhoM (rhoM (rhoM (gB (c := c) (r := r) Bf hB l)))) * rhoM (rhoM (rhoM (gV uh))))
    (rhoM (rhoM (rhoM (gD Bf hB uh μ))))
  have hadd := mN_add_le (p := 2) (by norm_num)
    (rhoM (derM ν (rhoM (gD Bf hB uh μ))) * star (rhoM (rhoM (rhoM (gD Bf hB uh l)))) *
      rhoM (rhoM (rhoM (gD Bf hB uh μ))))
    (rhoM (derM ν (rhoM (gD Bf hB uh μ))) *
      (star (rhoM (rhoM (rhoM (gB (c := c) (r := r) Bf hB l)))) * rhoM (rhoM (rhoM (gV uh)))) *
      rhoM (rhoM (rhoM (gD Bf hB uh μ))))
  have hBV : mN ⊤ (star (rhoM (rhoM (rhoM (gB (c := c) (r := r) Bf hB l)))) *
      rhoM (rhoM (rhoM (gV uh)))) ≤ b * (2 * (m : ℝ) ^ 2) := by
    refine (mN_mul_le_infinf _ _).trans ?_
    simp only [mN_star, mN_rhoM']
    exact pm (mN_nonneg _ _) (mN_nonneg _ _) (hS.bb.B l) hV
  simp only [derM_rhoM, mN_rhoM'] at m1 m2 hadd hBV ⊢
  have e1 := pm (mul_nonneg (mN_nonneg _ _) (mN_nonneg _ _)) (mN_nonneg _ _)
    (pm (mN_nonneg _ _) (mN_nonneg _ _) (hY2 l ν μ) hV) (hD μ)
  have e4 := pm (mul_nonneg (mN_nonneg _ _) (mN_nonneg _ _)) (mN_nonneg _ _)
    (pm (mN_nonneg _ _) (mN_nonneg _ _) (hY ν μ) hV) (hY l μ)
  have e3 := pm (mul_nonneg (mN_nonneg _ _) (mN_nonneg _ _)) (mN_nonneg _ _)
    (pm (mN_nonneg _ _) (mN_nonneg _ _) (hY ν μ) hBV) (hD μ)
  have e2 : mN 4 (derM ν (gD Bf hB uh μ)) * (CS * (mN 4 (gD Bf hB uh l) * mN 4 (gD Bf hB uh μ) +
      ∑ k, (mN 4 (derM k (gD Bf hB uh l)) * mN 4 (gD Bf hB uh μ) +
        mN 4 (gD Bf hB uh l) * mN 4 (derM k (gD Bf hB uh μ))))) ≤
      Y * (CS * (δ * δ + ∑ _k : Fin 4, (Y * δ + δ * Y))) := by
    refine pm (mN_nonneg _ _) (mul_nonneg hCS (add_nonneg (mul_nonneg (mN_nonneg _ _)
      (mN_nonneg _ _)) (Finset.sum_nonneg fun k _ => add_nonneg (mul_nonneg (mN_nonneg _ _)
        (mN_nonneg _ _)) (mul_nonneg (mN_nonneg _ _) (mN_nonneg _ _))))) (hY ν μ)
      (mul_le_mul_of_nonneg_left (add_le_add (pm (mN_nonneg _ _) (mN_nonneg _ _) (hD l) (hD μ))
        (Finset.sum_le_sum fun k _ => add_le_add (pm (mN_nonneg _ _) (mN_nonneg _ _) (hY k l)
          (hD μ)) (pm (mN_nonneg _ _) (mN_nonneg _ _) (hD l) (hY k μ)))) hCS)
  linarith

/-- The common majorant `C_S (‖W‖‖Z‖ + Σ_k (‖∂W‖‖Z‖ + ‖W‖‖∂Z‖))` with numeric bounds. -/
def qb (CS w dw z dz : ℝ) : ℝ := CS * (w * z + ∑ _k : Fin 4, (dw * z + w * dz))

theorem c2a_le (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) {Y Y2 : ℝ}
    (hY : ∀ ν μ, mN 4 (derM ν (gD Bf hB uh μ)) ≤ Y)
    (hY2 : ∀ l ν μ, mN 4 (derM l (derM ν (gD Bf hB uh μ))) ≤ Y2) (l ν μ : Fin 4) :
    mN 2 (derM l (rhoM (rhoM (gD Bf hB uh μ)) * star (rhoM (rhoM (gD Bf hB uh ν))) *
      rhoM (rhoM (gD Bf hB uh μ)))) ≤
      Y * qb CS δ Y δ Y + δ * qb CS Y Y2 δ Y + δ * qb CS δ Y Y Y2 := by
  have hD := hS.D4
  have hδ := hS.δ0
  have hY0 : 0 ≤ Y := (mN_nonneg _ _).trans (hY 0 0)
  have hCS := hK.CS0
  have h := mN_derM_mul_star_mul_le (s := 5) hK l (rhoM (rhoM (gD Bf hB uh μ)))
    (rhoM (rhoM (gD Bf hB uh ν))) (rhoM (rhoM (gD Bf hB uh μ)))
  unfold qq at h
  simp only [derM_rhoM, mN_rhoM'] at h ⊢
  refine h.trans ?_
  unfold qb
  have n := fun (X : MatSob c r 9 m) => mN_nonneg (c := c) (r := r) (s := 9) 4 X
  have n8 := fun (X : MatSob c r 8 m) => mN_nonneg (c := c) (r := r) (s := 8) 4 X
  have n7 := fun (X : MatSob c r 7 m) => mN_nonneg (c := c) (r := r) (s := 7) 4 X
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact pm (n8 _) (mul_nonneg hCS (add_nonneg (mul_nonneg (n _) (n _)) (Finset.sum_nonneg
      fun k _ => add_nonneg (mul_nonneg (n8 _) (n _)) (mul_nonneg (n _) (n8 _))))) (hY l μ)
      (mul_le_mul_of_nonneg_left (add_le_add (pm (n _) (n _) (hD ν) (hD μ))
        (Finset.sum_le_sum fun k _ => add_le_add (pm (n8 _) (n _) (hY k ν) (hD μ))
          (pm (n _) (n8 _) (hD ν) (hY k μ)))) hCS)
  · exact pm (n _) (mul_nonneg hCS (add_nonneg (mul_nonneg (n8 _) (n _)) (Finset.sum_nonneg
      fun k _ => add_nonneg (mul_nonneg (n7 _) (n _)) (mul_nonneg (n8 _) (n8 _))))) (hD μ)
      (mul_le_mul_of_nonneg_left (add_le_add (pm (n8 _) (n _) (hY l ν) (hD μ))
        (Finset.sum_le_sum fun k _ => add_le_add (pm (n7 _) (n _) (hY2 k l ν) (hD μ))
          (pm (n8 _) (n8 _) (hY l ν) (hY k μ)))) hCS)
  · exact pm (n _) (mul_nonneg hCS (add_nonneg (mul_nonneg (n _) (n8 _)) (Finset.sum_nonneg
      fun k _ => add_nonneg (mul_nonneg (n8 _) (n8 _)) (mul_nonneg (n _) (n7 _))))) (hD μ)
      (mul_le_mul_of_nonneg_left (add_le_add (pm (n _) (n8 _) (hD ν) (hY l μ))
        (Finset.sum_le_sum fun k _ => add_le_add (pm (n8 _) (n8 _) (hY k ν) (hY l μ))
          (pm (n _) (n7 _) (hD ν) (hY2 k l μ)))) hCS)

theorem c2b_le (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) {Y : ℝ}
    (hY : ∀ ν μ, mN 4 (derM ν (gD Bf hB uh μ)) ≤ Y) (l ν μ : Fin 4) :
    mN 2 (derM l (rhoM (rhoM (gD Bf hB uh μ)) * (star (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν))) *
      rhoM (rhoM (gV uh))) * rhoM (rhoM (gD Bf hB uh μ)))) ≤
      Y * (b * (2 * (m : ℝ) ^ 2)) * δ + ((δ * (b * (2 * (m : ℝ) ^ 2)) * δ +
        δ * b * qb CS δ Y δ Y) + δ * (b * (b * (2 * (m : ℝ) ^ 2))) * δ) +
      δ * (b * (2 * (m : ℝ) ^ 2)) * Y := by
  have hV := mN_gV_top hS
  have hD := hS.D4
  have hδ := hS.δ0
  have hb := hS.b0
  have hY0 : 0 ≤ Y := (mN_nonneg _ _).trans (hY 0 0)
  have hCS := hK.CS0
  refine (mN_derM_mul3_le (s := 6) l (rhoM (rhoM (gD Bf hB uh μ)))
    (star (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν))) * rhoM (rhoM (gV uh)))
    (rhoM (rhoM (gD Bf hB uh μ)))).trans ?_
  rw [derM_mul, derM_star, derM_rhoM_rhoM_gV (Bf := Bf) (hB := hB)]
  have eq : ∀ X A1 A2 A3 A4 : MatSob c r 6 m, X * (A1 + A2 * (A3 + A4)) * X =
      X * A1 * X + X * (A2 * A3) * X + X * (A2 * A4) * X := fun X A1 A2 A3 A4 => by noncomm_ring
  rw [eq]
  have hK1 : mN ⊤ (star (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν))) * rhoM (rhoM (gV uh))) ≤
      b * (2 * (m : ℝ) ^ 2) := by
    refine (mN_mul_le_infinf _ _).trans ?_
    simp only [mN_star, mN_rhoM']
    exact pm (mN_nonneg _ _) (mN_nonneg _ _) (hS.bb.B ν) hV
  have m1 := mN_mul3_le (rhoM (rhoM (rhoM (gD Bf hB uh μ))))
    (star (derM l (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν)))) * rhoM (rhoM (rhoM (gV uh))))
    (rhoM (rhoM (rhoM (gD Bf hB uh μ))))
  have m2 := mN_mul_mul_star_mul_le (s := 5) hK (rhoM (rhoM (rhoM (gD Bf hB uh μ))))
    (rhoM (star (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν)))))
    (rhoM (rhoM (rhoM (gD Bf hB uh l)))) (rhoM (rhoM (rhoM (gD Bf hB uh μ))))
  have m3 := mN_mul3_le (rhoM (rhoM (rhoM (gD Bf hB uh μ))))
    (rhoM (star (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν)))) *
      (star (rhoM (rhoM (rhoM (gB (c := c) (r := r) Bf hB l)))) * rhoM (rhoM (rhoM (gV uh)))))
    (rhoM (rhoM (rhoM (gD Bf hB uh μ))))
  have k1 : mN ⊤ (star (derM l (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν)))) *
      rhoM (rhoM (rhoM (gV uh)))) ≤ b * (2 * (m : ℝ) ^ 2) := by
    refine (mN_mul_le_infinf _ _).trans ?_
    simp only [mN_star, mN_rhoM', derM_rhoM]
    exact pm (mN_nonneg _ _) (mN_nonneg _ _) (hS.bb.dB l ν) hV
  have k3 : mN ⊤ (rhoM (star (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν)))) *
      (star (rhoM (rhoM (rhoM (gB (c := c) (r := r) Bf hB l)))) * rhoM (rhoM (rhoM (gV uh))))) ≤
      b * (b * (2 * (m : ℝ) ^ 2)) := by
    refine (mN_mul_le_infinf _ _).trans ?_
    refine pm (mN_nonneg _ _) (mN_nonneg _ _) ?_ ((mN_mul_le_infinf _ _).trans ?_)
    · rw [rhoM_star]; simp only [mN_star, mN_rhoM']; exact hS.bb.B ν
    · simp only [mN_star, mN_rhoM']
      exact pm (mN_nonneg _ _) (mN_nonneg _ _) (hS.bb.B l) hV
  have hK2 : mN ⊤ (rhoM (star (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν))))) ≤ b := by
    rw [rhoM_star]; simp only [mN_star, mN_rhoM']; exact hS.bb.B ν
  have hadd1 := mN_add_le (p := 2) (by norm_num)
    (rhoM (rhoM (rhoM (gD Bf hB uh μ))) * (star (derM l (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν)))) *
      rhoM (rhoM (rhoM (gV uh)))) * rhoM (rhoM (rhoM (gD Bf hB uh μ))) +
      rhoM (rhoM (rhoM (gD Bf hB uh μ))) * (rhoM (star (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν)))) *
        star (rhoM (rhoM (rhoM (gD Bf hB uh l))))) * rhoM (rhoM (rhoM (gD Bf hB uh μ))))
    (rhoM (rhoM (rhoM (gD Bf hB uh μ))) * (rhoM (star (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν)))) *
      (star (rhoM (rhoM (rhoM (gB (c := c) (r := r) Bf hB l)))) * rhoM (rhoM (rhoM (gV uh))))) *
      rhoM (rhoM (rhoM (gD Bf hB uh μ))))
  have hadd2 := mN_add_le (p := 2) (by norm_num)
    (rhoM (rhoM (rhoM (gD Bf hB uh μ))) * (star (derM l (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν)))) *
      rhoM (rhoM (rhoM (gV uh)))) * rhoM (rhoM (rhoM (gD Bf hB uh μ))))
    (rhoM (rhoM (rhoM (gD Bf hB uh μ))) * (rhoM (star (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν)))) *
      star (rhoM (rhoM (rhoM (gD Bf hB uh l))))) * rhoM (rhoM (rhoM (gD Bf hB uh μ))))
  simp only [derM_rhoM, mN_rhoM'] at m1 m2 m3 hadd1 hadd2 k1 hK2 ⊢
  have e1 := pm (mul_nonneg (mN_nonneg _ _) (mN_nonneg _ _)) (mN_nonneg _ _)
    (pm (mN_nonneg _ _) (mN_nonneg _ _) (hY l μ) hK1) (hD μ)
  have e5 := pm (mul_nonneg (mN_nonneg _ _) (mN_nonneg _ _)) (mN_nonneg _ _)
    (pm (mN_nonneg _ _) (mN_nonneg _ _) (hD μ) hK1) (hY l μ)
  have e2 := pm (mul_nonneg (mN_nonneg _ _) (mN_nonneg _ _)) (mN_nonneg _ _)
    (pm (mN_nonneg _ _) (mN_nonneg _ _) (hD μ) k1) (hD μ)
  have e4 := pm (mul_nonneg (mN_nonneg _ _) (mN_nonneg _ _)) (mN_nonneg _ _)
    (pm (mN_nonneg _ _) (mN_nonneg _ _) (hD μ) k3) (hD μ)
  have n := fun (Z : MatSob c r 9 m) => mN_nonneg (c := c) (r := r) (s := 9) 4 Z
  have n8 := fun (Z : MatSob c r 8 m) => mN_nonneg (c := c) (r := r) (s := 8) 4 Z
  have e3 : mN 4 (gD Bf hB uh μ) * mN ⊤ (star (rhoM (rhoM (gB (c := c) (r := r) Bf hB ν)))) *
      (CS * (mN 4 (gD Bf hB uh l) * mN 4 (gD Bf hB uh μ) + ∑ k, (mN 4 (derM k (gD Bf hB uh l)) *
        mN 4 (gD Bf hB uh μ) + mN 4 (gD Bf hB uh l) * mN 4 (derM k (gD Bf hB uh μ))))) ≤
      δ * b * qb CS δ Y δ Y := by
    unfold qb
    exact pm (mul_nonneg (n _) (mN_nonneg _ _)) (mul_nonneg hCS (add_nonneg (mul_nonneg (n _) (n _))
      (Finset.sum_nonneg fun k _ => add_nonneg (mul_nonneg (n8 _) (n _)) (mul_nonneg (n _)
        (n8 _))))) (pm (n _) (mN_nonneg _ _) (hD μ) hK2)
      (mul_le_mul_of_nonneg_left (add_le_add (pm (n _) (n _) (hD l) (hD μ))
        (Finset.sum_le_sum fun k _ => add_le_add (pm (n8 _) (n _) (hY k l) (hD μ))
          (pm (n _) (n8 _) (hD l) (hY k μ)))) hCS)
  linarith

theorem c3_le (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) {Y Y2 : ℝ}
    (hY : ∀ ν μ, mN 4 (derM ν (gD Bf hB uh μ)) ≤ Y)
    (hY2 : ∀ l ν μ, mN 4 (derM l (derM ν (gD Bf hB uh μ))) ≤ Y2) (l ν μ : Fin 4) :
    mN 2 (derM l (rhoM (rhoM (gD Bf hB uh μ)) * rhoM (rhoM (gV uh)) *
      derM ν (rhoM (gD Bf hB uh μ)))) ≤
      Y * (2 * (m : ℝ) ^ 2) * Y + (δ * qb CS δ Y Y Y2 + δ * (b * (2 * (m : ℝ) ^ 2)) * Y) +
        δ * (2 * (m : ℝ) ^ 2) * Y2 := by
  have hV := mN_gV_top hS
  have hD := hS.D4
  have hδ := hS.δ0
  have hb := hS.b0
  have hY0 : 0 ≤ Y := (mN_nonneg _ _).trans (hY 0 0)
  have hCS := hK.CS0
  refine (mN_derM_mul3_le (s := 6) l (rhoM (rhoM (gD Bf hB uh μ))) (rhoM (rhoM (gV uh)))
    (derM ν (rhoM (gD Bf hB uh μ)))).trans ?_
  rw [derM_rhoM_rhoM_gV (Bf := Bf) (hB := hB), mul_add, add_mul]
  have m1 := mN_mul_star_mul_le (s := 5) hK (rhoM (rhoM (rhoM (gD Bf hB uh μ))))
    (rhoM (rhoM (rhoM (gD Bf hB uh l)))) (rhoM (derM ν (rhoM (gD Bf hB uh μ))))
  have m2 := mN_mul3_le (rhoM (rhoM (rhoM (gD Bf hB uh μ))))
    (star (rhoM (rhoM (rhoM (gB (c := c) (r := r) Bf hB l)))) * rhoM (rhoM (rhoM (gV uh))))
    (rhoM (derM ν (rhoM (gD Bf hB uh μ))))
  have hadd := mN_add_le (p := 2) (by norm_num)
    (rhoM (rhoM (rhoM (gD Bf hB uh μ))) * star (rhoM (rhoM (rhoM (gD Bf hB uh l)))) *
      rhoM (derM ν (rhoM (gD Bf hB uh μ))))
    (rhoM (rhoM (rhoM (gD Bf hB uh μ))) *
      (star (rhoM (rhoM (rhoM (gB (c := c) (r := r) Bf hB l)))) * rhoM (rhoM (rhoM (gV uh)))) *
      rhoM (derM ν (rhoM (gD Bf hB uh μ))))
  have hBV : mN ⊤ (star (rhoM (rhoM (rhoM (gB (c := c) (r := r) Bf hB l)))) *
      rhoM (rhoM (rhoM (gV uh)))) ≤ b * (2 * (m : ℝ) ^ 2) := by
    refine (mN_mul_le_infinf _ _).trans ?_
    simp only [mN_star, mN_rhoM']
    exact pm (mN_nonneg _ _) (mN_nonneg _ _) (hS.bb.B l) hV
  simp only [derM_rhoM, mN_rhoM'] at m1 m2 hadd hBV ⊢
  have n := fun (Z : MatSob c r 9 m) => mN_nonneg (c := c) (r := r) (s := 9) 4 Z
  have n8 := fun (Z : MatSob c r 8 m) => mN_nonneg (c := c) (r := r) (s := 8) 4 Z
  have n7 := fun (Z : MatSob c r 7 m) => mN_nonneg (c := c) (r := r) (s := 7) 4 Z
  have e1 := pm (mul_nonneg (mN_nonneg _ _) (mN_nonneg _ _)) (mN_nonneg _ _)
    (pm (mN_nonneg _ _) (mN_nonneg _ _) (hY l μ) hV) (hY ν μ)
  have e4 := pm (mul_nonneg (mN_nonneg _ _) (mN_nonneg _ _)) (mN_nonneg _ _)
    (pm (mN_nonneg _ _) (mN_nonneg _ _) (hD μ) hV) (hY2 l ν μ)
  have e3 := pm (mul_nonneg (mN_nonneg _ _) (mN_nonneg _ _)) (mN_nonneg _ _)
    (pm (mN_nonneg _ _) (mN_nonneg _ _) (hD μ) hBV) (hY ν μ)
  have e2 : mN 4 (gD Bf hB uh μ) * (CS * (mN 4 (gD Bf hB uh l) * mN 4 (derM ν (gD Bf hB uh μ)) +
      ∑ k, (mN 4 (derM k (gD Bf hB uh l)) * mN 4 (derM ν (gD Bf hB uh μ)) +
        mN 4 (gD Bf hB uh l) * mN 4 (derM k (derM ν (gD Bf hB uh μ)))))) ≤
      δ * qb CS δ Y Y Y2 := by
    unfold qb
    exact pm (n _) (mul_nonneg hCS (add_nonneg (mul_nonneg (n _) (n8 _))
      (Finset.sum_nonneg fun k _ => add_nonneg (mul_nonneg (n8 _) (n8 _)) (mul_nonneg (n _)
        (n7 _))))) (hD μ)
      (mul_le_mul_of_nonneg_left (add_le_add (pm (n _) (n8 _) (hD l) (hY ν μ))
        (Finset.sum_le_sum fun k _ => add_le_add (pm (n8 _) (n8 _) (hY k l) (hY ν μ))
          (pm (n _) (n7 _) (hD l) (hY2 k ν μ)))) hCS)
  linarith

/-- The majorant of `‖∂_l ∂_ν (D_μ V D_μ)‖_{L²}`. -/
def ctB (CS b δ Ub Y Y2 : ℝ) : ℝ :=
  (Y2 * Ub * δ + (Y * (CS * (δ * δ + ∑ _k : Fin 4, (Y * δ + δ * Y))) + Y * (b * Ub) * δ) +
      Y * Ub * Y) +
    (Y * qb CS δ Y δ Y + δ * qb CS Y Y2 δ Y + δ * qb CS δ Y Y Y2) +
    (Y * (b * Ub) * δ + ((δ * (b * Ub) * δ + δ * b * qb CS δ Y δ Y) + δ * (b * (b * Ub)) * δ) +
      δ * (b * Ub) * Y) +
    (Y * Ub * Y + (δ * qb CS δ Y Y Y2 + δ * (b * Ub) * Y) + δ * Ub * Y2)

theorem ctB_affine (CS b δ Ub Y Y2 : ℝ) :
    ctB CS b δ Ub Y Y2 = ctB CS b δ Ub Y 0 + (2 * Ub * δ + 12 * CS * δ * δ) * Y2 := by
  unfold ctB qb
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem mN_ddDVD_le (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) {Y Y2 : ℝ}
    (hY : ∀ ν μ, mN 4 (derM ν (gD Bf hB uh μ)) ≤ Y)
    (hY2 : ∀ l ν μ, mN 4 (derM l (derM ν (gD Bf hB uh μ))) ≤ Y2) (l ν μ : Fin 4) :
    mN 2 (derM l (derM ν (rhoM (gD Bf hB uh μ) * rhoM (gV uh) * rhoM (gD Bf hB uh μ)))) ≤
      ctB CS b δ (2 * (m : ℝ) ^ 2) Y Y2 := by
  rw [derM_DVD, map_add, map_add, map_add]
  have h1 := c1_le hK hS hY hY2 l ν μ
  have h2 := c2a_le hK hS hY hY2 l ν μ
  have h3 := c2b_le hK hS hY l ν μ
  have h4 := c3_le hK hS hY hY2 l ν μ
  refine ((mN_add_le (by norm_num) _ _).trans (add_le_add ((mN_add_le (by norm_num) _ _).trans
    (add_le_add ((mN_add_le (by norm_num) _ _).trans (add_le_add h1 h2)) h3)) h4)).trans ?_
  unfold ctB
  have hδ := hS.δ0
  have hY0 : 0 ≤ Y := (mN_nonneg _ _).trans (hY 0 0)
  have hCS := hK.CS0
  have : 0 ≤ δ * qb CS δ Y δ Y := by unfold qb; positivity
  linarith

theorem mN_ddUM_le (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) {H : ℝ}
    (hH1 : hM 1 (by norm_num) uh ≤ H) (hH2 : hM 2 (by norm_num) uh ≤ H) (l ν : Fin 4) :
    mN 2 (derM l (derM ν (rhoM (gU uh) * gM (c := c) (r := r) Bf hB))) ≤
      3 * (H * b) + cv * (2 * (m : ℝ) ^ 2) * b := by
  have hb := hS.b0
  rw [derM_mul, map_add]
  have p1 := mN_derM_mul_le_2i (s := 6) l (derM ν (rhoM (gU uh))) (rhoM (gM (c := c) (r := r) Bf hB))
  have p2 := mN_derM_mul_le_2i (s := 6) l (rhoM (rhoM (gU uh))) (derM ν (gM (c := c) (r := r) Bf hB))
  have hs := mN_add_le (p := 2) (by norm_num)
    (derM l (derM ν (rhoM (gU uh)) * rhoM (gM (c := c) (r := r) Bf hB)))
    (derM l (rhoM (rhoM (gU uh)) * derM ν (gM (c := c) (r := r) Bf hB)))
  simp only [derM_rhoM, mN_rhoM'] at p1 p2 hs ⊢
  have u2 := (mN_ddgU_two (uh := uh) l ν).trans hH2
  have u1 := (mN_dgU_two (uh := uh) ν).trans hH1
  have u1' := (mN_dgU_two (uh := uh) l).trans hH1
  have u0 := mN_gU_two hK hS
  have q1 := pm (mN_nonneg _ _) (mN_nonneg _ _) u2 hS.bb.M
  have q2 := pm (mN_nonneg _ _) (mN_nonneg _ _) u1 (hS.bb.dM l)
  have q3 := pm (mN_nonneg _ _) (mN_nonneg _ _) u1' (hS.bb.dM ν)
  have q4 := pm (mN_nonneg _ _) (mN_nonneg _ _) u0 (hS.bb.ddM l ν)
  linarith

theorem mN_ddS1_le (hK : SobConsts c r m CS cv) (hS : HSet Bf hB uh b δ) {P1 P2 : ℝ}
    (hP1 : ∀ ν μ, mN 2 (derM ν (gD Bf hB uh μ)) ≤ P1)
    (hP2 : ∀ l ν μ, mN 2 (derM l (derM ν (gD Bf hB uh μ))) ≤ P2) (l ν : Fin 4) :
    mN 2 (derM l (derM ν (∑ μ, rhoM (gD Bf hB uh μ) * rhoM (gB (c := c) (r := r) Bf hB μ)))) ≤
      4 * (P2 * b + 2 * (P1 * b) + cv * δ * b) := by
  have hb := hS.b0
  rw [map_sum, map_sum]
  refine (mN_sum_le (by norm_num) _ _).trans ?_
  calc ∑ μ, mN 2 (derM l (derM ν (rhoM (gD Bf hB uh μ) * rhoM (gB (c := c) (r := r) Bf hB μ))))
      ≤ ∑ _μ : Fin 4, (P2 * b + 2 * (P1 * b) + cv * δ * b) := by
        refine Finset.sum_le_sum fun μ _ => ?_
        rw [derM_mul, map_add]
        have p1 := mN_derM_mul_le_2i (s := 6) l (derM ν (rhoM (gD Bf hB uh μ)))
          (rhoM (rhoM (gB (c := c) (r := r) Bf hB μ)))
        have p2 := mN_derM_mul_le_2i (s := 6) l (rhoM (rhoM (gD Bf hB uh μ)))
          (derM ν (rhoM (gB (c := c) (r := r) Bf hB μ)))
        have hs := mN_add_le (p := 2) (by norm_num)
          (derM l (derM ν (rhoM (gD Bf hB uh μ)) * rhoM (rhoM (gB (c := c) (r := r) Bf hB μ))))
          (derM l (rhoM (rhoM (gD Bf hB uh μ)) * derM ν (rhoM (gB (c := c) (r := r) Bf hB μ))))
        simp only [derM_rhoM, mN_rhoM'] at p1 p2 hs ⊢
        have q1 := pm (mN_nonneg _ _) (mN_nonneg _ _) (hP2 l ν μ) (hS.bb.B μ)
        have q2 := pm (mN_nonneg _ _) (mN_nonneg _ _) (hP1 ν μ) (hS.bb.dB l μ)
        have q3 := pm (mN_nonneg _ _) (mN_nonneg _ _) (hP1 l μ) (hS.bb.dB ν μ)
        have q4 := pm (mN_nonneg _ _) (mN_nonneg _ _) (mN_gD_two hK hS μ) (hS.bb.ddB l ν μ)
        linarith
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast
        ring

end DVD

end RenewalGeometry.BallAnalysis.HigherE4
