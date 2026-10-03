/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.FiniteGibbsActionGap
import RenewalGeometry.StatMech.AcceptedActionInformationPythagoras

/-!
# The finite Gibbs/KL certificate on the full probability simplex
  (`cor:supp-gibbs-gap`, `eq:supp-gibbs-gap`, `eq:main-gibbs-row`;
  emergent-spacetime manuscript)

For a finite reference row `p_θ(y) > 0` and a same-history cost `c_θ(y)`, the Gibbs row
`q*_θ = p_θ e^{-η c_θ} / Σ_z p_θ(z) e^{-η c_θ(z)}` (`gibbsRow`) is the unique minimizer of the
entropy-proximal objective `Obj(q) = Σ_y q(y) c_θ(y) + η⁻¹ D_KL(q ‖ p_θ)` over **all**
probability rows `q` (zero entries allowed, with the convention `0 log 0 = 0`, which
`finiteKL` implements since `Real.log 0 = 0`), and the row variational gap of an accepted row
is exactly `η⁻¹ D_KL(K^acc(·|θ) ‖ q*_θ)`.

* `entropyProximalObjective_gap_of_nonneg`: the manuscript's identity
  `Obj(q) = η⁻¹ D_KL(q ‖ q*) − η⁻¹ log Z` for every probability row `q ≥ 0`
  (terms with `q(y) = 0` vanish on both sides);
* `finite_gibbs_simplex_gap`: the corollary — `q*` is a strictly positive probability row,
  `Obj(q) − Obj(q*) = η⁻¹ D_KL(q ‖ q*)`, `Obj(q*) ≤ Obj(q)`, with equality iff `q = q*`, and
  `q*` is the unique minimizer of `Obj` over the simplex.

Unlike `finite_gibbs_action_gap_exact`, the reference row need not be normalised and the
competitor rows may vanish.
-/

open Finset

namespace RenewalGeometry
namespace FiniteGibbsSimplex

variable {Y : Type*} [Fintype Y]

/-- Per-coordinate log-likelihood identity for the Gibbs tilt, valid also where `q y = 0`. -/
lemma mul_log_ratio_gibbsRow [Nonempty Y] (q p c : Y → ℝ) (η : ℝ)
    (hq : ∀ y, 0 ≤ q y) (hp : ∀ y, 0 < p y) (y : Y) :
    q y * Real.log (q y / gibbsRow p c η y)
      = q y * Real.log (q y / p y) + η * (q y * c y)
          + q y * Real.log (gibbsPartition p c η) := by
  rcases (hq y).lt_or_eq with h | h
  · have hZ := (gibbsRow_probability p c η hp).1
    have he : 0 < p y * Real.exp (-η * c y) := mul_pos (hp y) (Real.exp_pos _)
    unfold gibbsRow
    rw [Real.log_div h.ne' (div_pos he hZ).ne', Real.log_div he.ne' hZ.ne',
      Real.log_mul (hp y).ne' (Real.exp_pos _).ne', Real.log_exp,
      Real.log_div h.ne' (hp y).ne']
    ring
  · rw [← h]
    simp

/-- **The entropy-proximal identity on the full simplex**: for every probability row
`q ≥ 0`, `Obj(q) = η⁻¹ D_KL(q ‖ q*) − η⁻¹ log Z`. -/
theorem entropyProximalObjective_gap_of_nonneg [Nonempty Y]
    (q p c : Y → ℝ) (η : ℝ) (hη : 0 < η) (hq : ∀ y, 0 ≤ q y) (hp : ∀ y, 0 < p y)
    (hqsum : ∑ y, q y = 1) :
    entropyProximalObjective q p c η
      = η⁻¹ * finiteKL q (gibbsRow p c η) - η⁻¹ * Real.log (gibbsPartition p c η) := by
  have hKL : finiteKL q (gibbsRow p c η)
      = finiteKL q p + η * (∑ y, q y * c y) + Real.log (gibbsPartition p c η) := by
    unfold finiteKL
    rw [Finset.sum_congr rfl fun y _ => mul_log_ratio_gibbsRow q p c η hq hp y,
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      hqsum, one_mul]
  unfold entropyProximalObjective
  rw [hKL]
  field_simp
  ring

/-- **`cor:supp-gibbs-gap`** (finite Gibbs/KL certificate on the full probability simplex).
For a strictly positive finite reference row `p` (not necessarily normalised), any cost `c`
and `η > 0`, the Gibbs row `q* = gibbsRow p c η` is a strictly positive probability row; for
every probability row `q ≥ 0` (zeros allowed) the row variational gap is exactly
`Obj(q) − Obj(q*) = η⁻¹ D_KL(q ‖ q*)`, `Obj(q*) ≤ Obj(q)` with equality iff `q = q*`; and
`q*` is the unique minimizer of `Obj` over the simplex. -/
theorem finite_gibbs_simplex_gap [Nonempty Y]
    (p c : Y → ℝ) (η : ℝ) (hp : ∀ y, 0 < p y) (hη : 0 < η) :
    let qstar := gibbsRow p c η
    (∀ y, 0 < qstar y) ∧ (∑ y, qstar y = 1)
    ∧ (∀ q : Y → ℝ, (∀ y, 0 ≤ q y) → (∑ y, q y = 1) →
        entropyProximalObjective q p c η - entropyProximalObjective qstar p c η
            = η⁻¹ * finiteKL q qstar
        ∧ entropyProximalObjective qstar p c η ≤ entropyProximalObjective q p c η
        ∧ (entropyProximalObjective q p c η = entropyProximalObjective qstar p c η
            ↔ q = qstar))
    ∧ (∀ q : Y → ℝ, (∀ y, 0 ≤ q y) → (∑ y, q y = 1) →
        ((∀ q' : Y → ℝ, (∀ y, 0 ≤ q' y) → (∑ y, q' y = 1) →
            entropyProximalObjective q p c η ≤ entropyProximalObjective q' p c η)
          ↔ q = qstar)) := by
  dsimp only
  have hqs := gibbsRow_probability p c η hp
  have hgap : ∀ q : Y → ℝ, (∀ y, 0 ≤ q y) → (∑ y, q y = 1) →
      entropyProximalObjective q p c η - entropyProximalObjective (gibbsRow p c η) p c η
        = η⁻¹ * finiteKL q (gibbsRow p c η) := by
    intro q hq hqsum
    have h1 := entropyProximalObjective_gap_of_nonneg q p c η hη hq hp hqsum
    have h2 := entropyProximalObjective_gap_of_nonneg (gibbsRow p c η) p c η hη
      (fun y => (hqs.2.1 y).le) hp hqs.2.2
    have hself : finiteKL (gibbsRow p c η) (gibbsRow p c η) = 0 :=
      ((AcceptedActionInformationPythagoras.finiteKL_nonneg_eq_iff_of_nonnegative _ _
        (fun y => (hqs.2.1 y).le) hqs.2.1 hqs.2.2 hqs.2.2).2).mpr rfl
    rw [h1, h2, hself]
    ring
  have hKL := fun q (hq : ∀ y, 0 ≤ q y) (hqsum : ∑ y, q y = 1) =>
    AcceptedActionInformationPythagoras.finiteKL_nonneg_eq_iff_of_nonnegative q
      (gibbsRow p c η) hq hqs.2.1 hqsum hqs.2.2
  have hηi : 0 < η⁻¹ := inv_pos.mpr hη
  have hmain : ∀ q : Y → ℝ, (∀ y, 0 ≤ q y) → (∑ y, q y = 1) →
      entropyProximalObjective q p c η - entropyProximalObjective (gibbsRow p c η) p c η
            = η⁻¹ * finiteKL q (gibbsRow p c η)
        ∧ entropyProximalObjective (gibbsRow p c η) p c η ≤ entropyProximalObjective q p c η
        ∧ (entropyProximalObjective q p c η
              = entropyProximalObjective (gibbsRow p c η) p c η ↔ q = gibbsRow p c η) := by
    intro q hq hqsum
    have hg := hgap q hq hqsum
    have hk := hKL q hq hqsum
    refine ⟨hg, ?_, ?_⟩
    · have := mul_nonneg hηi.le hk.1
      linarith
    · constructor
      · intro heq
        have h0 : η⁻¹ * finiteKL q (gibbsRow p c η) = 0 := by linarith
        exact hk.2.mp ((mul_eq_zero.mp h0).resolve_left hηi.ne')
      · rintro rfl
        rfl
  refine ⟨hqs.2.1, hqs.2.2, hmain, ?_⟩
  intro q hq hqsum
  constructor
  · intro hmin
    have h1 := hmin (gibbsRow p c η) (fun y => (hqs.2.1 y).le) hqs.2.2
    have h2 := (hmain q hq hqsum).2.1
    exact (hmain q hq hqsum).2.2.mp (le_antisymm h1 h2)
  · rintro rfl q' hq' hq'sum
    exact (hmain q' hq' hq'sum).2.1

/-- Non-vacuity: a two-point reference row with a zero-entry competitor row. -/
example : entropyProximalObjective (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
      (fun _ => 1 / 2) (fun i => if i = 0 then 0 else 1) 1
    - entropyProximalObjective (gibbsRow (fun _ : Fin 2 => (1 / 2 : ℝ))
        (fun i => if i = 0 then 0 else 1) 1) (fun _ => 1 / 2) (fun i => if i = 0 then 0 else 1) 1
    = 1⁻¹ * finiteKL (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
        (gibbsRow (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun i => if i = 0 then 0 else 1) 1) :=
  ((finite_gibbs_simplex_gap (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun i => if i = 0 then 0 else 1) 1
    (fun _ => by norm_num) one_pos).2.2.1 _ (fun i => by fin_cases i <;> simp)
    (by simp)).1

end FiniteGibbsSimplex
end RenewalGeometry
