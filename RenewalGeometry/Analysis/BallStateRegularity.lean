/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallNeumannLift

/-!
# Regularity of Coulomb gauges of smooth connections: lifts to every `H^s(B)`
  (stages D2/D4 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `restrM` — restriction `H^s(B, M_m(ℂ)) → H^{s'}(B, M_m(ℂ))` (`s' ≤ s`) as a ring homomorphism;
  naturality: `restrM_star`, `restrM_derM`, `restrM_restrM`, `restrM_matOfSmooth`,
  `restrM_actM`;
* `exists_lift_neumannM` — a Neumann matrix field `u ∈ H⁵` whose Laplacian is the restriction of
  an `H^k` field is the restriction of an `H^{k+2}` field;
* `coulomb_gauge_lift` (**main result**): a unitary Neumann gauge `u ∈ H⁵(B, M_m(ℂ))` such that
  `u·B_f` is Coulomb, `B_f` a smooth connection, is the restriction of an element of
  `H^{j+5}(B, M_m(ℂ))` for every `j` (elliptic bootstrap with the gauge equation `lapM_actM`).
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

instance fact_three_le_add_three (j : ℕ) : Fact (3 ≤ j + 3) := ⟨by omega⟩
instance fact_three_le_add_four (j : ℕ) : Fact (3 ≤ j + 4) := ⟨by omega⟩
instance fact_three_le_add_five (j : ℕ) : Fact (3 ≤ j + 5) := ⟨by omega⟩
instance fact_three_le_add_six (j : ℕ) : Fact (3 ≤ j + 6) := ⟨by omega⟩

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m : ℕ}

/-! ### Restrictions -/

section Restrictions

variable {s s' s'' : ℕ} [Fact (3 ≤ s)] [Fact (3 ≤ s')] [Fact (3 ≤ s'')]

theorem restrS_restrS (h1 : s' ≤ s) (h2 : s'' ≤ s') (F : SobAlg c r s) :
    restrS h2 (restrS h1 F) = restrS (h2.trans h1) F :=
  ext_fn EventuallyEq.rfl

theorem restrS_self (F : SobAlg c r s) : restrS (le_refl s) F = F := ext_fn EventuallyEq.rfl

theorem derS_restrS_gen (i : Fin 4) (h : s' ≤ s) (F : SobAlg c r (s + 1)) :
    derS i (restrS (Nat.succ_le_succ h) F) = restrS h (derS i F) := by
  apply ext_fn
  have h1 := weak_derS (c := c) (r := r) i (restrS (Nat.succ_le_succ h) F)
  have h2 := weak_derS (c := c) (r := r) i F
  rw [fn_restrS] at h1
  have := weakR_ae_eq (isOpen_euclBall c r) h1 h2 (memLp_fn _) (memLp_fn _)
  rw [EventuallyEq, ae_restrict_iff' (measurableSet_euclBall c r)]
  filter_upwards [this] with x hx hxB
  rw [hx hxB, fn_restrS]

/-- Restriction of matrix fields as a ring homomorphism. -/
def restrM (h : s' ≤ s) : MatSob c r s m →+* MatSob c r s' m :=
  (Cx.mapRingHom (restrHom h)).mapMatrix

theorem restrM_apply (h : s' ≤ s) (X : MatSob c r s m) (i j : Fin m) :
    restrM h X i j = ⟨restrS h (X i j).re, restrS h (X i j).im⟩ := rfl

theorem rhoM_eq_restrM (X : MatSob c r (s + 1) m) : rhoM X = restrM (Nat.le_succ s) X := rfl

theorem restrM_restrM (h1 : s' ≤ s) (h2 : s'' ≤ s') (X : MatSob c r s m) :
    restrM h2 (restrM h1 X) = restrM (h2.trans h1) X := by
  ext i j
  · exact restrS_restrS h1 h2 _
  · exact restrS_restrS h1 h2 _

theorem restrM_self (X : MatSob c r s m) : restrM (le_refl s) X = X := by
  ext i j
  · exact restrS_self _
  · exact restrS_self _

theorem restrM_star (h : s' ≤ s) (X : MatSob c r s m) : restrM h (star X) = star (restrM h X) := by
  ext i j <;> simp [restrM_apply, Matrix.star_apply]

theorem restrM_derM (μ : Fin 4) (h : s' ≤ s) (X : MatSob c r (s + 1) m) :
    restrM h (derM μ X) = derM μ (restrM (Nat.succ_le_succ h) X) := by
  ext i j
  · exact (derS_restrS_gen μ h _).symm
  · exact (derS_restrS_gen μ h _).symm

theorem restrM_matOfSmooth (h : s' ≤ s) {F : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hF : ∀ i j, ContDiff ℝ ∞ (fun x => F x i j)) :
    restrM h (matOfSmooth (c := c) (r := r) s F hF) = matOfSmooth s' F hF := by
  ext i j <;> rfl

theorem restrM_actM (h : s' ≤ s) (u v : MatSob c r (s + 1) m) (B : Fin 4 → MatSob c r s m)
    (μ : Fin 4) :
    restrM h (actM u v B μ) = actM (restrM (Nat.succ_le_succ h) u) (restrM (Nat.succ_le_succ h) v)
      (fun κ => restrM h (B κ)) μ := by
  simp only [actM, map_sub, map_mul, restrM_derM, rhoM_eq_restrM, restrM_restrM]

end Restrictions

/-! ### Neumann lifts of matrix fields -/

theorem isNeumannS_re {u : MatSob c r 5 m} (hu : IsNeumM u) (i j : Fin m) :
    IsNeumannS (u i j).re := by
  have h := ((mem_tanM.mp hu) i j).1
  exact mem_tanSub.mp h

theorem isNeumannS_im {u : MatSob c r 5 m} (hu : IsNeumM u) (i j : Fin m) :
    IsNeumannS (u i j).im := by
  have h := ((mem_tanM.mp hu) i j).2
  exact mem_tanSub.mp h

theorem lapM_re (u : MatSob c r 5 m) (i j : Fin m) : (lapM (s := 3) u i j).re = lapS (u i j).re := by
  simp only [lapM, lapS, Matrix.sum_apply, Cx.sum_re, derM_apply]

theorem lapM_im (u : MatSob c r 5 m) (i j : Fin m) : (lapM (s := 3) u i j).im = lapS (u i j).im := by
  simp only [lapM, lapS, Matrix.sum_apply, Cx.sum_im, derM_apply]

/-- **Neumann lift of matrix fields.** -/
theorem exists_lift_neumannM (k : ℕ) {u : MatSob c r 5 m} (hu : IsNeumM u)
    {Q : MatSob c r (k + 3) m} (hQ : lapM (s := 3) u = restrM (by omega) Q) :
    ∃ u' : MatSob c r (k + 5) m, restrM (by omega) u' = u := by
  have hre : ∀ i j, ∃ X : SobAlg c r (k + 5), restrS (by omega) X = (u i j).re := by
    intro i j
    have hk : MemHk (euclBall c r) (k + 3) (fn (lapS (u i j).re)) := by
      rw [← lapM_re, hQ, restrM_apply]
      exact memHk_fn _
    exact exists_lift_neumannS (k := k + 3) (by omega) (isNeumannS_re hu i j) hk
  have him : ∀ i j, ∃ X : SobAlg c r (k + 5), restrS (by omega) X = (u i j).im := by
    intro i j
    have hk : MemHk (euclBall c r) (k + 3) (fn (lapS (u i j).im)) := by
      rw [← lapM_im, hQ, restrM_apply]
      exact memHk_fn _
    exact exists_lift_neumannS (k := k + 3) (by omega) (isNeumannS_im hu i j) hk
  choose R hR using hre
  choose I hI using him
  refine ⟨Matrix.of fun i j => ⟨R i j, I i j⟩, ?_⟩
  ext i j
  · exact hR i j
  · exact hI i j

end RenewalGeometry.BallAnalysis.BallAlg

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m : ℕ}

/-- **Coulomb gauges of smooth connections are smooth up to the boundary** (in the Sobolev sense):
a unitary Neumann gauge `u ∈ H⁵(B, M_m(ℂ))` such that `u·B_f` is Coulomb, `B_f` smooth, is the
restriction of an element of `H^{j+5}(B, M_m(ℂ))` for every `j`. -/
theorem coulomb_gauge_lift {Bf : (Fin 4) → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    (hB : ∀ μ i j, ContDiff ℝ ∞ (fun x => Bf μ x i j)) {u : MatSob c r 5 m}
    (huu : u * star u = 1) (hN : IsNeumM u)
    (hcoul : ∑ μ, derM μ (actM u (star u) (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) μ)
      = 0) :
    ∀ j : ℕ, ∃ uj : MatSob c r (j + 5) m, restrM (by omega) uj = u := by
  intro j
  induction j with
  | zero => exact ⟨u, restrM_self u⟩
  | succ j ih =>
    obtain ⟨uj, huj⟩ := ih
    set Bb : Fin 4 → MatSob c r (j + 4) m := fun κ => matOfSmooth (j + 4) (Bf κ) (hB κ)
    set dB : Fin 4 → MatSob c r (j + 4) m := fun κ => derM κ (matOfSmooth (j + 5) (Bf κ) (hB κ))
    set P : MatSob c r (j + 4) m := rhoM uj
    set a : Fin 4 → MatSob c r (j + 4) m := fun κ => actM uj (star uj) Bb κ
    set Q : MatSob c r (j + 4) m := P * ∑ κ, (Bb κ * Bb κ + dB κ) - 2 * ∑ κ, a κ * P * Bb κ +
      ∑ κ, a κ * a κ * P
    have hlap := lapM_actM (s := 3) huu (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ))
      hcoul
    have hQ : lapM (s := 3) u = restrM (by omega) Q := by
      rw [hlap]
      have hu3 : rhoM (rhoM u) = restrM (s := j + 4) (s' := 3) (by omega) P := by
        simp only [P, rhoM_eq_restrM, restrM_restrM, ← huj]
      have hu4 : ∀ κ, rhoM (actM u (star u) (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ)
          (hB κ)) κ) = restrM (s := j + 4) (s' := 3) (by omega) (a κ) := by
        intro κ
        simp only [a, Bb, rhoM_eq_restrM, restrM_actM, restrM_matOfSmooth, restrM_star,
          restrM_restrM, ← huj]
      have hB3 : ∀ κ, rhoM (matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) =
          restrM (s := j + 4) (s' := 3) (by omega) (Bb κ) := by
        intro κ
        simp only [Bb, rhoM_eq_restrM, restrM_matOfSmooth]
      have hdB : ∀ κ, derM κ (matOfSmooth (c := c) (r := r) 4 (Bf κ) (hB κ)) =
          restrM (s := j + 4) (s' := 3) (by omega) (dB κ) := by
        intro κ
        simp only [dB, restrM_derM, restrM_matOfSmooth]
      simp only [Q, map_add, map_sub, map_mul, map_sum, map_ofNat, hu3, hu4, hB3, hdB]
    obtain ⟨u', hu'⟩ := exists_lift_neumannM (k := j + 1) hN hQ
    exact ⟨u', hu'⟩

end RenewalGeometry.BallAnalysis.BallAlg
