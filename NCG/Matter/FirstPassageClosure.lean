/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# First-passage reachability closure and the critical four-state rule
  (`prop:first-passage-reachability-closure`,
   `thm:explicit-conserved-critical-rule`, SM_emergence)

* `first_passage_reachability` — for an irreducible kernel on a
  finite state space, every ordered pair of distinct states is
  connected by a positive-probability *first-passage* path (positive
  steps, no intermediate visit to the target): truncate a minimal
  positive path at its first visit.  Hence the support graph of
  nonzero first-passage channels is complete;
* `critical_offspring_row_sum` / `critical_offspring_meanfield` —
  for the scalar mean offspring matrix `M = (J₄ - I₄)/3` of the
  conserved critical rule: `M·𝟙 = 𝟙` (criticality, `𝔼ᵢZ = 1`) and
  `M·v = -v/3` on the mean-zero sector, so
  `spec(M) = {1, -1/3, -1/3, -1/3}` and the genealogy is
  irreducible and critical.
-/

namespace NCG

/-- `prop:first-passage-reachability-closure`: an irreducible finite
kernel connects every ordered pair of distinct states by a positive
first-passage path — a positive-step path from `x` to `y` that does
not visit `y` at any intermediate time. -/
theorem first_passage_reachability {X : Type*}
    (P : X → X → ℝ)
    (hirr : ∀ x y : X, x ≠ y → ∃ (m : ℕ) (p : ℕ → X), 0 < m
      ∧ p 0 = x ∧ p m = y ∧ ∀ i < m, 0 < P (p i) (p (i + 1)))
    (x y : X) (hxy : x ≠ y) :
    ∃ (m : ℕ) (p : ℕ → X), 0 < m ∧ p 0 = x ∧ p m = y
      ∧ (∀ i < m, 0 < P (p i) (p (i + 1)))
      ∧ ∀ r, 0 < r → r < m → p r ≠ y := by
  classical
  set Q : ℕ → Prop := fun m => ∃ p : ℕ → X, 0 < m ∧ p 0 = x
    ∧ p m = y ∧ ∀ i < m, 0 < P (p i) (p (i + 1)) with hQdef
  have hQ : ∃ m, Q m := hirr x y hxy
  obtain ⟨p, hm, hp0, hpm, hstep⟩ := Nat.find_spec hQ
  refine ⟨Nat.find hQ, p, hm, hp0, hpm, hstep, ?_⟩
  intro r hr0 hrm hry
  have hQr : Q r :=
    ⟨p, hr0, hp0, hry, fun i hi => hstep i (lt_trans hi hrm)⟩
  exact Nat.find_min hQ hrm hQr

/-- The scalar mean offspring matrix of the conserved critical rule:
`M = (J₄ - I₄)/3`. -/
noncomputable def criticalOffspring : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 3 : ℝ) • (Matrix.of (fun _ _ => 1) - 1)

/-- Criticality: the mean total offspring is one in every state,
`M·𝟙 = 𝟙` — the Perron eigenvalue is `1`. -/
theorem critical_offspring_row_sum :
    criticalOffspring.mulVec (fun _ => 1) = fun _ => 1 := by
  funext i
  fin_cases i <;>
    norm_num [criticalOffspring, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Matrix.one_apply, Fin.ext_iff]

/-- The mean-zero sector is a `(-1/3)`-eigenspace: `M·v = -v/3`
whenever `Σv = 0`, giving `spec(M) = {1, -1/3, -1/3, -1/3}`. -/
theorem critical_offspring_meanfield (v : Fin 4 → ℝ)
    (hv : ∑ i, v i = 0) :
    criticalOffspring.mulVec v = fun i => -(1 / 3) * v i := by
  funext i
  have hsum : v 0 + v 1 + v 2 + v 3 = 0 := by
    rw [← hv, Fin.sum_univ_four]
  simp only [criticalOffspring, Matrix.smul_mulVec,
    Matrix.sub_mulVec, Matrix.one_mulVec, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]
  rw [show (Matrix.of fun _ _ => (1 : ℝ)).mulVec v i
      = v 0 + v 1 + v 2 + v 3 from by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four], hsum]
  ring

end NCG
