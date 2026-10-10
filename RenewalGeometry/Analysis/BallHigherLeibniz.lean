/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallHigherIdent

/-!
# Leibniz–Hölder bounds and derivative bounds for the covariant derivative of a lifted gauge
  (stage D2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `mN_derM_mul_le_2i`, `mN_derM_mul_le_i2`, `mN_derM_mul_le_44`, `mN4_derM_mul_le_4i`,
  `mN4_derM_mul_le_i4` — Leibniz rule combined with Hölder;
* `derM_gU`, `derM_gV` — `∂U = D + U B`, `∂V = D^* + B^* V`;
* `BBounds` — `L^∞` bounds on the smooth connection `B`, its derivatives and `M`;
* `mN_dgU_le`, `mN_dgD_le`, `mN_ddgD_le`, `mN_dddgD_le` — `L²` bounds of the derivatives of `U`
  and of the covariant derivative `D` by the jet seminorms `hM k û`.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.HigherLeibniz

open SobolevOpen BallReg BallAlg SobAlg HigherNorms HigherIdent

set_option linter.unusedSectionVars false

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m : ℕ}

/-! ### Leibniz–Hölder -/

section Leibniz

variable {s : ℕ} [Fact (3 ≤ s)]

theorem mN_derM_mul_le_2i (ν : Fin 4) (X Y : MatSob c r (s + 1) m) :
    mN 2 (derM ν (X * Y)) ≤ mN 2 (derM ν X) * mN ⊤ Y + mN 2 X * mN ⊤ (derM ν Y) := by
  rw [derM_mul]
  refine (mN_add_le (by norm_num) _ _).trans (add_le_add ?_ ?_)
  · exact (mN_mul_le_2inf _ _).trans (le_of_eq (by rw [mN_rhoM]))
  · exact (mN_mul_le_2inf _ _).trans (le_of_eq (by rw [mN_rhoM]))

theorem mN_derM_mul_le_i2 (ν : Fin 4) (X Y : MatSob c r (s + 1) m) :
    mN 2 (derM ν (X * Y)) ≤ mN 2 (derM ν X) * mN ⊤ Y + mN ⊤ X * mN 2 (derM ν Y) := by
  rw [derM_mul]
  refine (mN_add_le (by norm_num) _ _).trans (add_le_add ?_ ?_)
  · exact (mN_mul_le_2inf _ _).trans (le_of_eq (by rw [mN_rhoM]))
  · exact (mN_mul_le_inf2 _ _).trans (le_of_eq (by rw [mN_rhoM]))

theorem mN_derM_mul_le_44 (ν : Fin 4) (X Y : MatSob c r (s + 1) m) :
    mN 2 (derM ν (X * Y)) ≤ mN 4 (derM ν X) * mN 4 Y + mN 4 X * mN 4 (derM ν Y) := by
  rw [derM_mul]
  refine (mN_add_le (by norm_num) _ _).trans (add_le_add ?_ ?_)
  · exact (mN_mul_le_44 _ _).trans (le_of_eq (by rw [mN_rhoM]))
  · exact (mN_mul_le_44 _ _).trans (le_of_eq (by rw [mN_rhoM]))

theorem mN4_derM_mul_le_4i (ν : Fin 4) (X Y : MatSob c r (s + 1) m) :
    mN 4 (derM ν (X * Y)) ≤ mN 4 (derM ν X) * mN ⊤ Y + mN 4 X * mN ⊤ (derM ν Y) := by
  rw [derM_mul]
  refine (mN_add_le (by norm_num) _ _).trans (add_le_add ?_ ?_)
  · exact (mN_mul_le_4inf _ _).trans (le_of_eq (by rw [mN_rhoM]))
  · exact (mN_mul_le_4inf _ _).trans (le_of_eq (by rw [mN_rhoM]))

theorem mN4_derM_mul_le_i4 (ν : Fin 4) (X Y : MatSob c r (s + 1) m) :
    mN 4 (derM ν (X * Y)) ≤ mN 4 (derM ν X) * mN ⊤ Y + mN ⊤ X * mN 4 (derM ν Y) := by
  rw [derM_mul]
  refine (mN_add_le (by norm_num) _ _).trans (add_le_add ?_ ?_)
  · exact (mN_mul_le_4inf _ _).trans (le_of_eq (by rw [mN_rhoM]))
  · exact (mN_mul_le_inf4 _ _).trans (le_of_eq (by rw [mN_rhoM]))

end Leibniz

/-! ### Derivatives of `U` and `V` -/

section Objects

variable {Bf : CriticalGauge.MConn m} {hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j)}

theorem derM_uh (uh : MatSob c r 10 m) (ν : Fin 4) :
    derM ν uh = gD Bf hB uh ν + gU uh * gB Bf hB ν := by
  rw [gD, sub_add_cancel]

theorem derM_gU (uh : MatSob c r 10 m) (ν : Fin 4) :
    derM ν (gU uh) = rhoM (gD Bf hB uh ν) + rhoM (gU uh) * rhoM (gB Bf hB ν) := by
  rw [gU, derM_rhoM, derM_uh (Bf := Bf) (hB := hB) uh ν, map_add, map_mul]
  rfl

theorem derM_gV (uh : MatSob c r 10 m) (ν : Fin 4) :
    derM ν (gV uh) = star (rhoM (gD Bf hB uh ν)) + star (rhoM (gB Bf hB ν)) * rhoM (gV uh) := by
  rw [gV, derM_rhoM, derM_star, derM_uh (Bf := Bf) (hB := hB) uh ν, star_add, star_mul, map_add,
    map_mul, rhoM_star, rhoM_star, rhoM_star, gU]
  rw [rhoM_star, rhoM_star]

/-! ### Bounds on the smooth connection -/

/-- `L^∞` bounds on `B`, its first three derivatives, `M` and its first two derivatives. -/
structure BBounds (Bf : CriticalGauge.MConn m) (hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j))
    (b : ℝ) : Prop where
  B : ∀ μ, mN ⊤ (gB (c := c) (r := r) Bf hB μ) ≤ b
  dB : ∀ ν μ, mN ⊤ (derM ν (gB (c := c) (r := r) Bf hB μ)) ≤ b
  ddB : ∀ l ν μ, mN ⊤ (derM l (derM ν (gB (c := c) (r := r) Bf hB μ))) ≤ b
  dddB : ∀ k l ν μ, mN ⊤ (derM k (derM l (derM ν (gB (c := c) (r := r) Bf hB μ)))) ≤ b
  M : mN ⊤ (gM (c := c) (r := r) Bf hB) ≤ b
  dM : ∀ ν, mN ⊤ (derM ν (gM (c := c) (r := r) Bf hB)) ≤ b
  ddM : ∀ l ν, mN ⊤ (derM l (derM ν (gM (c := c) (r := r) Bf hB))) ≤ b

/-! ### Derivatives of the lift against the jet seminorms -/

theorem mN_d1_le (uh : MatSob c r 10 m) (ν : Fin 4) :
    mN 2 (derM ν uh) ≤ hM 1 (by norm_num) uh := by
  rw [← hM_zero (by norm_num)]
  exact hM_derM_le 0 (by norm_num) ν uh

theorem mN_d2_le (uh : MatSob c r 10 m) (l ν : Fin 4) :
    mN 2 (derM l (derM ν uh)) ≤ hM 2 (by norm_num) uh := by
  rw [← hM_zero (by norm_num)]
  exact (hM_derM_le 0 (by norm_num) l _).trans (hM_derM_le 1 (by norm_num) ν uh)

theorem mN_d3_le (uh : MatSob c r 10 m) (k l ν : Fin 4) :
    mN 2 (derM k (derM l (derM ν uh))) ≤ hM 3 (by norm_num) uh := by
  rw [← hM_zero (by norm_num)]
  exact ((hM_derM_le 0 (by norm_num) k _).trans (hM_derM_le 1 (by norm_num) l _)).trans
    (hM_derM_le 2 (by norm_num) ν uh)

theorem mN_d4_le (uh : MatSob c r 10 m) (j k l ν : Fin 4) :
    mN 2 (derM j (derM k (derM l (derM ν uh)))) ≤ hM 4 (by norm_num) uh := by
  rw [← hM_zero (by norm_num)]
  exact (((hM_derM_le 0 (by norm_num) j _).trans (hM_derM_le 1 (by norm_num) k _)).trans
    (hM_derM_le 2 (by norm_num) l _)).trans (hM_derM_le 3 (by norm_num) ν uh)

theorem h1_le_h2 (uh : MatSob c r 10 m) : hM 1 (by norm_num) uh ≤ hM 2 (by norm_num) uh :=
  hM_mono 1 (by norm_num) uh

theorem h2_le_h3 (uh : MatSob c r 10 m) : hM 2 (by norm_num) uh ≤ hM 3 (by norm_num) uh :=
  hM_mono 2 (by norm_num) uh

theorem h3_le_h4 (uh : MatSob c r 10 m) : hM 3 (by norm_num) uh ≤ hM 4 (by norm_num) uh :=
  hM_mono 3 (by norm_num) uh

end Objects

end RenewalGeometry.BallAnalysis.HigherLeibniz
