/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StatMech.HistoryEntropyEnergyEstimate

/-!
# History-level entropy--energy estimate with vanishing proposal rows
(`lem:supp-entropy-energy`, `eq:supp-entropy-energy`; emergent-spacetime manuscript)

This file removes the full-support restriction of `HistoryEntropyEnergyEstimate.lean`.  The
stage reference rows `p_j(x, ·)` are finite proposal rows that may vanish off their proposal
sets (`0 ≤ p_j`, `Σ_y p_j(x,y) = 1`), the costs `E_j` are arbitrary real functions, and the
complete path law `ℙ` (any law on `Fin M → X`, memory allowed, same initial value `x₀` by
construction) is assumed absolutely continuous with respect to the accepted product law `ℚ`
(`ℙ(ω) > 0 → ℚ(ω) > 0`), as in the manuscript.  The partition functions `Z_j` are positive
only along `ℚ`-charged histories; elsewhere `Q_j` is the zero row (`x / 0 = 0`), which is
harmless since those histories carry no `ℙ`-mass.

* `finiteKL_nonneg_of_absCont`: Gibbs' inequality `D(ℙ ‖ r) ≥ 0` for `ℙ ≥ 0`, `Σ ℙ = 1`,
  `r ≥ 0`, `Σ r ≤ 1` and `ℙ ≪ r` (sums over `supp ℙ`; `0 log 0 = 0`).
* `acceptedRow_pos_of_acceptedPathLaw_pos`: along a `ℚ`-charged history every accepted factor,
  hence every proposal weight `p_j(x_j, x_{j+1})` and every partition function `Z_j(x_j)`, is
  positive.
* `finiteKL_acceptedPathLaw_absCont`: the exact path-level identity
  `ε D(ℙ‖ℚ) = ε D(ℙ‖ℙ_ref) + 𝔼_ℙ E + ε 𝔼_ℙ Σ_j log Z_j(x_j)` under `ℙ ≪ ℚ`.
* `entropy_energy_estimate_absCont` (**`eq:supp-entropy-energy`**): if each relevant row
  (each row `x_j` visited by a `ℙ`-charged history) contains a proposal `y` with
  `E_j(x_j, y) ≤ e_j` and weight `p_j(x_j, y) ≥ p_{*,j} > 0`, then
  `𝔼_ℙ Σ_j E_j ≤ Σ_j e_j + ε [Σ_j log(1/p_{*,j}) + D_KL(ℙ‖ℚ)]`.

Disclosed scoping (as in the parent file): the stage rows and costs are functions of the
current state (the product structure of `ℚ` stated in the lemma); the proposal-floor
hypothesis is only used at one low-cost candidate per relevant row (weaker than "every
proposal weight is at least `p_{*,j}`"); nonnegativity of the costs is not needed.
-/

open Finset Real

namespace RenewalGeometry
namespace HistoryEntropyEnergy

variable {X : Type*} [Fintype X]

/-- Pointwise Gibbs bound `P - r ≤ P log(P/r)` for `P, r ≥ 0` with `P > 0 → r > 0`. -/
theorem sub_le_mul_log_div_of_absCont {P r : ℝ} (hP : 0 ≤ P) (hr : 0 ≤ r)
    (hac : 0 < P → 0 < r) : P - r ≤ P * Real.log (P / r) := by
  rcases hP.lt_or_eq with h | h
  · have hr' := hac h
    have h1 := Real.log_le_sub_one_of_pos (div_pos hr' h)
    have h2 : Real.log (P / r) = -Real.log (r / P) := by
      rw [← Real.log_inv, inv_div]
    rw [h2]
    have h3 : P * Real.log (r / P) ≤ P * (r / P - 1) := mul_le_mul_of_nonneg_left h1 h.le
    have h4 : P * (r / P - 1) = r - P := by field_simp
    linarith
  · rw [← h]
    simp [hr]

/-- **Gibbs' inequality under absolute continuity**: for a probability row `ℙ ≥ 0` and a
sub-probability row `r ≥ 0` with `ℙ ≪ r`, `D_KL(ℙ ‖ r) ≥ 0` (the reference may vanish off
`supp ℙ`). -/
theorem finiteKL_nonneg_of_absCont {Ω : Type*} [Fintype Ω] (P r : Ω → ℝ)
    (hP : ∀ u, 0 ≤ P u) (hr : ∀ u, 0 ≤ r u) (hPsum : ∑ u, P u = 1) (hrsum : ∑ u, r u ≤ 1)
    (hac : ∀ u, 0 < P u → 0 < r u) : 0 ≤ finiteKL P r := by
  unfold finiteKL
  have h := Finset.sum_le_sum fun u (_ : u ∈ (univ : Finset Ω)) =>
    sub_le_mul_log_div_of_absCont (hP u) (hr u) (hac u)
  rw [Finset.sum_sub_distrib, hPsum] at h
  linarith

omit [Fintype X] in
theorem markovLaw_nonneg {M : ℕ} (x₀ : X) (r : ℕ → X → X → ℝ) (hr : ∀ j x y, 0 ≤ r j x y)
    (ω : Fin M → X) : 0 ≤ markovLaw x₀ r ω :=
  Finset.prod_nonneg fun _ _ => hr _ _ _

theorem stageZ_nonneg (p E : ℕ → X → X → ℝ) (ε : ℝ) (hp : ∀ j x y, 0 ≤ p j x y) (j : ℕ)
    (x : X) : 0 ≤ stageZ p E ε j x := by
  unfold stageZ gibbsPartition
  exact Finset.sum_nonneg fun y _ => mul_nonneg (hp j x y) (Real.exp_pos _).le

theorem acceptedRow_nonneg (p E : ℕ → X → X → ℝ) (ε : ℝ) (hp : ∀ j x y, 0 ≤ p j x y)
    (j : ℕ) (x y : X) : 0 ≤ acceptedRow p E ε j x y := by
  unfold acceptedRow gibbsRow
  exact div_nonneg (mul_nonneg (hp j x y) (Real.exp_pos _).le) (stageZ_nonneg p E ε hp j x)

/-- Along a `ℚ`-charged history every accepted factor is positive; hence the proposal weight
and the partition function of every visited stage are positive. -/
theorem acceptedRow_pos_of_acceptedPathLaw_pos {M : ℕ} (x₀ : X) (p E : ℕ → X → X → ℝ)
    (ε : ℝ) (hp : ∀ j x y, 0 ≤ p j x y) (ω : Fin M → X)
    (hQ : 0 < acceptedPathLaw x₀ p E ε ω) (j : Fin M) :
    0 < p j (prevState x₀ ω j) (ω j) ∧ 0 < stageZ p E ε j (prevState x₀ ω j) := by
  have hne : acceptedRow p E ε j (prevState x₀ ω j) (ω j) ≠ 0 := by
    intro h0
    have : acceptedPathLaw x₀ p E ε ω = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) h0
    linarith
  have hZ0 := stageZ_nonneg p E ε hp j (prevState x₀ ω j)
  have hp0 := hp j (prevState x₀ ω j) (ω j)
  unfold acceptedRow gibbsRow at hne
  have hZne : stageZ p E ε j (prevState x₀ ω j) ≠ 0 := by
    intro h; apply hne; unfold stageZ at h; rw [h, div_zero]
  have hpne : p j (prevState x₀ ω j) (ω j) ≠ 0 := by
    intro h; apply hne; rw [h, zero_mul, zero_div]
  exact ⟨lt_of_le_of_ne hp0 (Ne.symm hpne), lt_of_le_of_ne hZ0 (Ne.symm hZne)⟩

/-- `log ℚ(ω) = log ℙ_ref(ω) − E(ω)/ε − Σ_j log Z_j(x_j)` along a `ℚ`-charged history. -/
theorem log_acceptedPathLaw_of_pos {M : ℕ} (x₀ : X) (p E : ℕ → X → X → ℝ) (ε : ℝ)
    (hp : ∀ j x y, 0 ≤ p j x y) (ω : Fin M → X) (hQ : 0 < acceptedPathLaw x₀ p E ε ω) :
    Real.log (acceptedPathLaw x₀ p E ε ω)
      = Real.log (markovLaw x₀ p ω) - pathCost x₀ E ω / ε
        - ∑ j : Fin M, Real.log (stageZ p E ε j (prevState x₀ ω j)) := by
  have hpos := acceptedRow_pos_of_acceptedPathLaw_pos x₀ p E ε hp ω hQ
  unfold acceptedPathLaw markovLaw pathCost
  rw [Real.log_prod (fun j _ => ?_), Real.log_prod (fun j _ => (hpos j).1.ne'),
    Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  · refine Finset.sum_congr rfl fun j _ => ?_
    unfold acceptedRow gibbsRow
    have hZ : 0 < stageZ p E ε j (prevState x₀ ω j) := (hpos j).2
    have he : 0 < p j (prevState x₀ ω j) (ω j) * Real.exp (-ε⁻¹ * E j (prevState x₀ ω j) (ω j)) :=
      mul_pos (hpos j).1 (Real.exp_pos _)
    unfold stageZ at hZ
    rw [Real.log_div he.ne' hZ.ne', Real.log_mul (hpos j).1.ne' (Real.exp_pos _).ne',
      Real.log_exp]
    unfold stageZ
    ring
  · have h := hpos j
    unfold acceptedRow gibbsRow
    unfold stageZ at h
    exact (div_pos (mul_pos h.1 (Real.exp_pos _)) h.2).ne'

/-- **Exact path-level identity under `ℙ ≪ ℚ`**:
`ε D(ℙ‖ℚ) = ε D(ℙ‖ℙ_ref) + 𝔼_ℙ E + ε 𝔼_ℙ Σ_j log Z_j(x_j)`. -/
theorem finiteKL_acceptedPathLaw_absCont {M : ℕ} (x₀ : X) (p E : ℕ → X → X → ℝ) (ε : ℝ)
    (hε : ε ≠ 0) (hp : ∀ j x y, 0 ≤ p j x y) (P : (Fin M → X) → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (hac : ∀ ω, 0 < P ω → 0 < acceptedPathLaw x₀ p E ε ω) :
    ε * finiteKL P (acceptedPathLaw x₀ p E ε)
      = ε * finiteKL P (markovLaw x₀ p) + ∑ ω, P ω * pathCost x₀ E ω
        + ε * ∑ ω, P ω * ∑ j : Fin M, Real.log (stageZ p E ε j (prevState x₀ ω j)) := by
  unfold finiteKL
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rcases (hP ω).lt_or_eq with h | h
  · have hQ := hac ω h
    have hpos : 0 < markovLaw x₀ p ω := by
      unfold markovLaw
      exact Finset.prod_pos fun j _ =>
        (acceptedRow_pos_of_acceptedPathLaw_pos x₀ p E ε hp ω hQ j).1
    rw [Real.log_div h.ne' hQ.ne', Real.log_div h.ne' hpos.ne',
      log_acceptedPathLaw_of_pos x₀ p E ε hp ω hQ]
    field_simp
    ring
  · rw [← h]
    simp

/-- The candidate bound `−log Z_j(x) ≤ log(1/p_{*,j}) + e_j/ε` from one proposal `y` with
`E_j(x,y) ≤ e_j` and `p_j(x,y) ≥ p_{*,j} > 0`, for nonnegative proposal rows. -/
theorem neg_log_stageZ_le_of_nonneg (p E : ℕ → X → X → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hp : ∀ j x y, 0 ≤ p j x y) (j : ℕ) (x : X) (e pstar : ℝ) (hpstar : 0 < pstar)
    (hcand : ∃ y, E j x y ≤ e ∧ pstar ≤ p j x y) :
    -Real.log (stageZ p E ε j x) ≤ Real.log (1 / pstar) + e / ε := by
  obtain ⟨y, hEy, hpy⟩ := hcand
  have hZ : pstar * Real.exp (-(e / ε)) ≤ stageZ p E ε j x := by
    unfold stageZ gibbsPartition
    calc pstar * Real.exp (-(e / ε)) ≤ p j x y * Real.exp (-ε⁻¹ * E j x y) := by
          refine mul_le_mul hpy ?_ (Real.exp_pos _).le (hp j x y)
          apply Real.exp_le_exp.mpr
          rw [neg_mul, neg_le_neg_iff, inv_mul_eq_div]
          exact div_le_div_of_nonneg_right hEy hε.le
      _ ≤ ∑ y', p j x y' * Real.exp (-ε⁻¹ * E j x y') :=
          Finset.single_le_sum (f := fun y' => p j x y' * Real.exp (-ε⁻¹ * E j x y'))
            (fun y' _ => mul_nonneg (hp j x y') (Real.exp_pos _).le) (Finset.mem_univ y)
  have hlog := Real.log_le_log (mul_pos hpstar (Real.exp_pos _)) hZ
  rw [Real.log_mul hpstar.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  rw [one_div, Real.log_inv]
  linarith

/-- **`eq:supp-entropy-energy`** (`lem:supp-entropy-energy`, faithful form).  Stage
proposal rows `p_j(x, ·) ≥ 0` summing to one (zeros allowed), arbitrary costs `E_j`,
accepted rows `Q_j = p_j e^{−E_j/ε}/Z_j` with product law `ℚ`, and any complete path law
`ℙ ≪ ℚ` on `Fin M → X` (memory allowed, same initial value `x₀`).  If each relevant row —
every row `x_j` visited by a `ℙ`-charged history — contains a proposal `y` with cost
`E_j(x_j,y) ≤ e_j` and weight `p_j(x_j,y) ≥ p_{*,j} > 0`, then
`𝔼_ℙ Σ_j E_j ≤ Σ_j e_j + ε [Σ_j log(1/p_{*,j}) + D_KL(ℙ‖ℚ)]`. -/
theorem entropy_energy_estimate_absCont {M : ℕ} (x₀ : X) (p E : ℕ → X → X → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hp : ∀ j x y, 0 ≤ p j x y) (hpsum : ∀ j x, ∑ y, p j x y = 1)
    (P : (Fin M → X) → ℝ) (hP : ∀ ω, 0 ≤ P ω) (hPsum : ∑ ω, P ω = 1)
    (hac : ∀ ω, 0 < P ω → 0 < acceptedPathLaw x₀ p E ε ω)
    (e pstar : ℕ → ℝ) (hpstar : ∀ j : Fin M, 0 < pstar j)
    (hcand : ∀ ω, 0 < P ω → ∀ j : Fin M,
      ∃ y, E j (prevState x₀ ω j) y ≤ e j ∧ pstar j ≤ p j (prevState x₀ ω j) y) :
    ∑ ω, P ω * pathCost x₀ E ω
      ≤ ∑ j : Fin M, e j
        + ε * (∑ j : Fin M, Real.log (1 / pstar j) + finiteKL P (acceptedPathLaw x₀ p E ε)) := by
  have hid := finiteKL_acceptedPathLaw_absCont x₀ p E ε hε.ne' hp P hP hac
  have hgibbs : 0 ≤ finiteKL P (markovLaw x₀ p) := by
    refine finiteKL_nonneg_of_absCont P (markovLaw x₀ p) hP (markovLaw_nonneg x₀ p hp) hPsum
      (markovLaw_sum_one M x₀ p hpsum).le fun ω hω => ?_
    unfold markovLaw
    exact Finset.prod_pos fun j _ =>
      (acceptedRow_pos_of_acceptedPathLaw_pos x₀ p E ε hp ω (hac ω hω) j).1
  have hZ : -∑ ω, P ω * ∑ j : Fin M, Real.log (stageZ p E ε j (prevState x₀ ω j))
      ≤ ∑ j : Fin M, (Real.log (1 / pstar j) + e j / ε) := by
    have h1 : -∑ ω, P ω * ∑ j : Fin M, Real.log (stageZ p E ε j (prevState x₀ ω j))
        ≤ ∑ ω, P ω * ∑ j : Fin M, (Real.log (1 / pstar j) + e j / ε) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun ω _ => ?_
      rcases (hP ω).lt_or_eq with hω | hω
      · rw [← mul_neg]
        refine mul_le_mul_of_nonneg_left ?_ (hP ω)
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_le_sum fun j _ =>
          neg_log_stageZ_le_of_nonneg p E ε hε hp j _ (e j) (pstar j) (hpstar j)
            (hcand ω hω j)
      · rw [← hω]; simp
    rwa [← Finset.sum_mul, hPsum, one_mul] at h1
  have hεK : ε * ∑ j : Fin M, (Real.log (1 / pstar j) + e j / ε)
      = ∑ j : Fin M, e j + ε * ∑ j : Fin M, Real.log (1 / pstar j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
    ring
  have hmain : ∑ ω, P ω * pathCost x₀ E ω
      ≤ ε * finiteKL P (acceptedPathLaw x₀ p E ε)
        + ε * ∑ j : Fin M, (Real.log (1 / pstar j) + e j / ε) := by
    have := mul_le_mul_of_nonneg_left hZ hε.le
    nlinarith [hid, hgibbs, this, hε]
  linarith [hmain, hεK]

/-- Non-vacuity: a two-state chain whose proposal rows vanish off the diagonal (so the
full-support version does not apply), with `ℙ = ℚ`. -/
example :
    let p : ℕ → Fin 2 → Fin 2 → ℝ := fun _ x y => if x = y then 1 else 0
    let Q : (Fin 1 → Fin 2) → ℝ := acceptedPathLaw (M := 1) 0 p (fun _ _ _ => 0) 1
    (∃ j x y, p j x y = 0) ∧
      ∑ ω, Q ω * pathCost 0 (fun _ _ _ => (0 : ℝ)) ω
        ≤ ∑ _j : Fin 1, (0 : ℝ) + 1 * (∑ _j : Fin 1, Real.log (1 / 1) + finiteKL Q Q) := by
  intro p Q
  have hp : ∀ j x y, 0 ≤ p j x y := fun j x y => by
    simp only [p]; split_ifs <;> norm_num
  have hpsum : ∀ j x, ∑ y, p j x y = 1 := fun j x => by simp [p]
  have hQ : ∀ ω, 0 ≤ Q ω := fun ω => markovLaw_nonneg 0 _ (acceptedRow_nonneg p _ 1 hp) ω
  have hQsum : ∑ ω, Q ω = 1 := markovLaw_sum_one 1 0 _ fun j x => by
    unfold acceptedRow gibbsRow
    rw [← Finset.sum_div]
    exact div_self (by simp [p])
  refine ⟨⟨0, 0, 1, by simp [p]⟩, ?_⟩
  exact entropy_energy_estimate_absCont (M := 1) (0 : Fin 2) p (fun _ _ _ => 0) 1 one_pos hp
    hpsum Q hQ hQsum (fun _ h => h) (fun _ => 0) (fun _ => 1) (fun _ => one_pos)
    (fun ω _ j => ⟨prevState 0 ω j, le_rfl, by simp [p]⟩)

end HistoryEntropyEnergy
end RenewalGeometry
