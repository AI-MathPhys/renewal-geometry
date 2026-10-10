/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallHigherNorms

/-!
# The gauge equation of a lifted Coulomb state in covariant-derivative form
  (stage D2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

For a Coulomb gauge state `(u, a)` of a smooth connection `B_f` (`u u^* = 1`, `u·B = Σ_b a^b e_b`,
`Σ_μ ∂_μ a_μ = 0`) and a lift `û ∈ H^{10}` of `u`, with `U = û`, `V = û^*`, `B = B_f` at level
`9` and the covariant derivative `D_μ = ∂_μ û - U B_μ`:

* `gU_mul_gV`, `gV_mul_gU` — `U V = V U = 1`;
* `gD_eq_neg` — `D_μ = -A_μ U` with `A = û·B` the gauge-transformed connection; its restriction to
  level `4` is `-(Σ_b a_μ^b e_b) u` (`restrM_gD`), so `‖D_μ‖_{L⁴} ≤ 2m² ‖a_μ‖_{L⁴}` (`mN_gD_le`);
* `lapM_eq_gQ` — **the gauge equation in covariant form**
  `Δû = U M + 2 Σ_μ D_μ B_μ + Σ_μ D_μ V D_μ`, `M = Σ_μ (B_μ B_μ + ∂_μ B_μ)`.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.HigherIdent

open SobolevOpen BallReg BallAlg SobAlg HigherNorms

set_option linter.unusedSectionVars false

instance instFact6 : Fact (3 ≤ 6) := ⟨by norm_num⟩
instance instFact7 : Fact (3 ≤ 7) := ⟨by norm_num⟩
instance instFact8 : Fact (3 ≤ 8) := ⟨by norm_num⟩
instance instFact9 : Fact (3 ≤ 9) := ⟨by norm_num⟩
instance instFact10 : Fact (3 ≤ 10) := ⟨by norm_num⟩

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m d : ℕ}

/-! ### Restrictions are injective -/

theorem evM_restrM {s s' : ℕ} [Fact (3 ≤ s)] [Fact (3 ≤ s')] (h : s' ≤ s) (X : MatSob c r s m) :
    evM (restrM h X) = evM X := by
  funext x
  ext i j
  simp only [evM_apply, evC, restrM_apply, fn_restrS]

theorem restrM_injective {s s' : ℕ} [Fact (3 ≤ s)] [Fact (3 ≤ s')] (h : s' ≤ s) :
    Function.Injective (restrM (c := c) (r := r) (m := m) h) := by
  intro X Y hXY
  refine ext_evM ?_
  rw [← evM_restrM h X, ← evM_restrM h Y, hXY]

/-! ### The lifted objects -/

section Objects

variable (Bf : CriticalGauge.MConn m) (hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j))

/-- `U = û` at level `9`. -/
def gU (uh : MatSob c r 10 m) : MatSob c r 9 m := rhoM uh

/-- `V = û^*` at level `9`. -/
def gV (uh : MatSob c r 10 m) : MatSob c r 9 m := rhoM (star uh)

/-- `B` at level `9`. -/
def gB (μ : Fin 4) : MatSob c r 9 m := matOfSmooth 9 (Bf μ) (hB μ)

/-- The covariant derivative `D_μ = ∂_μ û - U B_μ`. -/
def gD (uh : MatSob c r 10 m) (μ : Fin 4) : MatSob c r 9 m := derM μ uh - gU uh * gB Bf hB μ

/-- The gauge-transformed connection `A = û·B` at level `9`. -/
def gA (uh : MatSob c r 10 m) (μ : Fin 4) : MatSob c r 9 m := actM uh (star uh) (gB Bf hB) μ

/-- `M = Σ_μ (B_μ B_μ + ∂_μ B_μ)` at level `8`. -/
def gM : MatSob c r 8 m :=
  ∑ μ, (rhoM (gB (c := c) (r := r) Bf hB μ) * rhoM (gB (c := c) (r := r) Bf hB μ) +
    derM μ (gB (c := c) (r := r) Bf hB μ))

/-- The right-hand side `U M + 2 Σ D_μ B_μ + Σ D_μ V D_μ` of the gauge equation. -/
def gQ (uh : MatSob c r 10 m) : MatSob c r 8 m :=
  rhoM (gU uh) * gM Bf hB + 2 * ∑ μ, rhoM (gD Bf hB uh μ) * rhoM (gB Bf hB μ) +
    ∑ μ, rhoM (gD Bf hB uh μ) * rhoM (gV uh) * rhoM (gD Bf hB uh μ)

variable {Bf hB}

theorem gV_eq (uh : MatSob c r 10 m) : gV uh = star (gU uh) := rhoM_star uh

/-- **Unitarity of the lift.** -/
theorem lift_unitary {u : MatSob c r 5 m} (hu : u * star u = 1) {uh : MatSob c r 10 m}
    (hlift : restrM (by norm_num : 5 ≤ 10) uh = u) : uh * star uh = 1 := by
  refine restrM_injective (by norm_num : 5 ≤ 10) ?_
  rw [map_mul, restrM_star, hlift, hu, map_one]

theorem gU_mul_gV {uh : MatSob c r 10 m} (huh : uh * star uh = 1) : gU uh * gV uh = 1 := by
  rw [gU, gV, ← map_mul, huh, map_one]

theorem gV_mul_gU {uh : MatSob c r 10 m} (huh : uh * star uh = 1) : gV uh * gU uh = 1 := by
  have : star uh * uh = 1 := mul_eq_one_comm.mp huh
  rw [gU, gV, ← map_mul, this, map_one]

theorem gD_eq_neg {uh : MatSob c r 10 m} (huh : uh * star uh = 1) (μ : Fin 4) :
    gD Bf hB uh μ = -(gA Bf hB uh μ * gU uh) := by
  have h := derM_eq_of_actM huh (gB Bf hB) μ
  simp only [gD, gA, gU]
  rw [h]
  abel

theorem gA_eq_neg {uh : MatSob c r 10 m} (huh : uh * star uh = 1) (μ : Fin 4) :
    gA Bf hB uh μ = -(gD Bf hB uh μ * gV uh) := by
  rw [gD_eq_neg huh, neg_mul, neg_neg, mul_assoc, gU_mul_gV huh, mul_one]

variable (L : LieBasis m d)

theorem restrM_gA {u : MatSob c r 5 m} {a : Fin 4 → Fin d → SobAlg c r 4}
    (hact : ∀ μ, actM u (star u) (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) μ =
      embX L (a μ))
    {uh : MatSob c r 10 m} (hlift : restrM (by norm_num : 5 ≤ 10) uh = u) (μ : Fin 4) :
    restrM (by norm_num : 4 ≤ 9) (gA Bf hB uh μ) = embX L (a μ) := by
  have hl' : restrM (Nat.succ_le_succ (by norm_num : 4 ≤ 9)) uh = u := hlift
  have hB' : (fun κ => restrM (by norm_num : 4 ≤ 9) (gB (c := c) (r := r) Bf hB κ)) =
      fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ) :=
    funext fun κ => restrM_matOfSmooth _ _
  rw [gA, restrM_actM, restrM_star, hl', hB', hact μ]

theorem sum_derM_gA {u : MatSob c r 5 m} {a : Fin 4 → Fin d → SobAlg c r 4}
    (hact : ∀ μ, actM u (star u) (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) μ =
      embX L (a μ)) (hcoul : coulF L (a, 0) = 0)
    {uh : MatSob c r 10 m} (hlift : restrM (by norm_num : 5 ≤ 10) uh = u) :
    ∑ μ, derM μ (gA Bf hB uh μ) = 0 := by
  refine restrM_injective (by norm_num : 3 ≤ 8) ?_
  rw [map_sum, map_zero]
  simp only [restrM_derM]
  rw [← AssemblyTools.sum_derM_embX_eq_zero L hcoul]
  exact Finset.sum_congr rfl fun μ _ => congrArg (derM μ) (restrM_gA L hact hlift μ)

/-- **The gauge equation in covariant form** `Δû = U M + 2 Σ D_μ B_μ + Σ D_μ V D_μ`. -/
theorem lapM_eq_gQ {u : MatSob c r 5 m} {a : Fin 4 → Fin d → SobAlg c r 4}
    (hu : u * star u = 1)
    (hact : ∀ μ, actM u (star u) (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) μ =
      embX L (a μ)) (hcoul : coulF L (a, 0) = 0)
    {uh : MatSob c r 10 m} (hlift : restrM (by norm_num : 5 ≤ 10) uh = u) :
    lapM (s := 8) uh = gQ Bf hB uh := by
  have huh := lift_unitary hu hlift
  have h := lapM_actM huh (gB Bf hB) (sum_derM_gA L hact hcoul hlift)
  rw [h]
  have e1 : ∀ μ, rhoM (actM uh (star uh) (gB Bf hB) μ) * rhoM (rhoM uh) =
      -rhoM (gD Bf hB uh μ) := by
    intro μ
    rw [← map_mul, show actM uh (star uh) (gB Bf hB) μ * rhoM uh = gA Bf hB uh μ * gU uh from rfl,
      gD_eq_neg huh μ, map_neg, neg_neg]
  have e2 : ∀ μ, rhoM (actM uh (star uh) (gB Bf hB) μ) =
      -(rhoM (gD Bf hB uh μ) * rhoM (gV uh)) := by
    intro μ
    rw [show actM uh (star uh) (gB Bf hB) μ = gA Bf hB uh μ from rfl, gA_eq_neg huh μ, map_neg,
      map_mul]
  have e3 : ∀ μ, rhoM (actM uh (star uh) (gB Bf hB) μ) * rhoM (actM uh (star uh) (gB Bf hB) μ) *
      rhoM (rhoM uh) = rhoM (gD Bf hB uh μ) * rhoM (gV uh) * rhoM (gD Bf hB uh μ) := by
    intro μ
    rw [mul_assoc, e1 μ, e2 μ]
    noncomm_ring
  simp only [e3]
  have e4 : ∀ μ, rhoM (actM uh (star uh) (gB Bf hB) μ) * rhoM (rhoM uh) * rhoM (gB Bf hB μ) =
      -(rhoM (gD Bf hB uh μ) * rhoM (gB Bf hB μ)) := by
    intro μ
    rw [e1 μ, neg_mul]
  simp only [e4, Finset.sum_neg_distrib, mul_neg, sub_neg_eq_add]
  rfl

/-! ### Smallness of the covariant derivative -/

theorem restrM_gD {u : MatSob c r 5 m} {a : Fin 4 → Fin d → SobAlg c r 4}
    (hu : u * star u = 1)
    (hact : ∀ μ, actM u (star u) (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) μ =
      embX L (a μ))
    {uh : MatSob c r 10 m} (hlift : restrM (by norm_num : 5 ≤ 10) uh = u) (μ : Fin 4) :
    restrM (by norm_num : 4 ≤ 9) (gD Bf hB uh μ) = -(embX L (a μ) * rhoM u) := by
  have huh := lift_unitary hu hlift
  have hU : restrM (by norm_num : 4 ≤ 9) (gU uh) = rhoM u := by
    rw [gU, rhoM_eq_restrM, restrM_restrM, rhoM_eq_restrM, ← hlift, restrM_restrM]
  rw [gD_eq_neg huh, map_neg, map_mul, restrM_gA L hact hlift, hU]

theorem mN_gD_le {u : MatSob c r 5 m} {a : Fin 4 → Fin d → SobAlg c r 4}
    (hu : u * star u = 1)
    (hact : ∀ μ, actM u (star u) (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) μ =
      embX L (a μ))
    {uh : MatSob c r 10 m} (hlift : restrM (by norm_num : 5 ≤ 10) uh = u) (μ : Fin 4) :
    mN 4 (gD Bf hB uh μ) ≤ mN 4 (embX L (a μ)) * (2 * (m : ℝ) ^ 2) := by
  rw [← mN_restrM (by norm_num : 4 ≤ 9), restrM_gD L hu hact hlift μ, mN_neg]
  refine (mN_mul_le_4inf _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (mN_nonneg _ _)
  rw [mN_rhoM]
  exact mN_top_le_of_unitary hu

end Objects

end RenewalGeometry.BallAnalysis.HigherIdent
