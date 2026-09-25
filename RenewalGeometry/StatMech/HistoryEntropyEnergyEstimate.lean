/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.FiniteGibbsActionGap
import RenewalGeometry.StatMech.AcceptedActionInformationPythagoras

/-!
# History-level entropy--energy estimate
(`lem:supp-entropy-energy`, `eq:supp-entropy-energy`; emergent-spacetime manuscript)

Finite horizon `M`, finite state space `X`, fixed initial value `x₀`.  Paths are
`ω : Fin M → X` (the states `x₁, …, x_M`); `prevState x₀ ω j` is `x_j` and `ω j`
is `x_{j+1}`.  A family of stage rows `r j x ·` defines the Markov path law
`markovLaw x₀ r ω = ∏_j r j x_j x_{j+1}` (`markovLaw_sum_one`: it is a probability
row whenever every stage row is).

At stage `j` the reference proposal row `p j x ·` and the cost `E j x ·` define the
accepted Gibbs row `Q_j(x, ·) = p_j(x,·) e^{−E_j(x,·)/ε}/Z_j(x)` (`gibbsRow`
of `RenewalGeometry.Action.FiniteGibbsActionGap` with `η = ε⁻¹`); `ℚ` is the product
(Markov) law of these accepted rows (`acceptedPathLaw`) and `ℙ` is any path law on
`Fin M → X` (memoryful, same initial value by construction, `ℙ ≪ ℚ` automatically
since `ℚ > 0`).

* `log_acceptedPathLaw`: `log ℚ(ω) = log ℙ_ref(ω) − E(ω)/ε − Σ_j log Z_j(x_j)` with
  `ℙ_ref = markovLaw x₀ p` and `E(ω) = Σ_j E_j(x_j, x_{j+1})`.
* `finiteKL_acceptedPathLaw`: the exact path-level identity
  `ε D(ℙ‖ℚ) = ε D(ℙ‖ℙ_ref) + 𝔼_ℙ E + ε 𝔼_ℙ Σ_j log Z_j(x_j)`.
* `entropy_energy_estimate` (**`eq:supp-entropy-energy`**): if at every stage and
  source state there is a proposal `y` with `E_j(x,y) ≤ e_j` and `p_j(x,y) ≥ p_{*,j}`,
  then `𝔼_ℙ Σ_j E_j ≤ Σ_j e_j + ε [Σ_j log(1/p_{*,j}) + D(ℙ‖ℚ)]`.

The paper's proof integrates the per-stage identity over history prefixes and
invokes the chain rule for path relative entropy; here the same identity is
obtained directly at the path level from `log ℚ = log ℙ_ref − E/ε − Σ log Z_j`
and Gibbs' inequality `D(ℙ‖ℙ_ref) ≥ 0`.  Disclosed scoping: the reference rows and
costs are functions of the current state (the product/Markov structure of `ℚ`
stated in the lemma); the proposal-floor hypothesis is only required at one
low-cost candidate per row, which is weaker than the paper's "every proposal
weight is at least `p_{*,j}`"; nonnegativity of the costs is not needed.
-/

open Finset Real

namespace RenewalGeometry
namespace HistoryEntropyEnergy

variable {X : Type*} [Fintype X]

/-- The state `x_j` preceding the transition `j` along the path `ω = (x₁, …, x_M)`
with initial value `x₀`. -/
def prevState {M : ℕ} (x₀ : X) (ω : Fin M → X) (j : Fin M) : X :=
  Fin.cons (α := fun _ => X) x₀ ω (Fin.castSucc j)

@[simp] theorem prevState_cons_zero {M : ℕ} (x₀ x₁ : X) (ω : Fin M → X) :
    prevState x₀ (Fin.cons (α := fun _ => X) x₁ ω) 0 = x₀ := by
  simp [prevState]

theorem prevState_cons_succ {M : ℕ} (x₀ x₁ : X) (ω : Fin M → X) (j : Fin M) :
    prevState x₀ (Fin.cons (α := fun _ => X) x₁ ω) j.succ = prevState x₁ ω j := by
  unfold prevState
  rw [← Fin.succ_castSucc, Fin.cons_succ]

/-- The Markov path law `∏_{j<M} r_j(x_j, x_{j+1})` of stage rows `r`. -/
noncomputable def markovLaw {M : ℕ} (x₀ : X) (r : ℕ → X → X → ℝ) (ω : Fin M → X) : ℝ :=
  ∏ j : Fin M, r j (prevState x₀ ω j) (ω j)

theorem markovLaw_cons {M : ℕ} (x₀ x₁ : X) (r : ℕ → X → X → ℝ) (ω : Fin M → X) :
    markovLaw x₀ r (Fin.cons (α := fun _ => X) x₁ ω)
      = r 0 x₀ x₁ * markovLaw x₁ (fun j => r (j + 1)) ω := by
  unfold markovLaw
  rw [Fin.prod_univ_succ]
  congr 1

/-- A Markov path law built from probability rows is a probability row on paths. -/
theorem markovLaw_sum_one (M : ℕ) (x₀ : X) (r : ℕ → X → X → ℝ)
    (hr : ∀ j x, ∑ y, r j x y = 1) :
    ∑ ω : Fin M → X, markovLaw x₀ r ω = 1 := by
  induction M generalizing x₀ r with
  | zero => simp [markovLaw]
  | succ M ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (M + 1) => X)).sum_comp (markovLaw x₀ r),
      Fintype.sum_prod_type]
    calc ∑ x₁, ∑ ω : Fin M → X, markovLaw x₀ r (Fin.cons (α := fun _ => X) x₁ ω)
        = ∑ x₁, r 0 x₀ x₁ * ∑ ω : Fin M → X, markovLaw x₁ (fun j => r (j + 1)) ω := by
          refine Finset.sum_congr rfl fun x₁ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ω _ => ?_
          exact markovLaw_cons x₀ x₁ r ω
      _ = ∑ x₁, r 0 x₀ x₁ := by
          refine Finset.sum_congr rfl fun x₁ _ => ?_
          rw [ih x₁ (fun j => r (j + 1)) (fun j x => hr (j + 1) x), mul_one]
      _ = 1 := hr 0 x₀

theorem markovLaw_pos {M : ℕ} (x₀ : X) (r : ℕ → X → X → ℝ) (hr : ∀ j x y, 0 < r j x y)
    (ω : Fin M → X) : 0 < markovLaw x₀ r ω :=
  Finset.prod_pos fun j _ => hr _ _ _

theorem log_markovLaw {M : ℕ} (x₀ : X) (r : ℕ → X → X → ℝ) (hr : ∀ j x y, 0 < r j x y)
    (ω : Fin M → X) :
    Real.log (markovLaw x₀ r ω) = ∑ j : Fin M, Real.log (r j (prevState x₀ ω j) (ω j)) := by
  unfold markovLaw
  exact Real.log_prod fun j _ => (hr _ _ _).ne'

/-! ### Accepted Gibbs rows and their product law -/

/-- The stage partition function `Z_j(x) = Σ_y p_j(x,y) e^{−E_j(x,y)/ε}`. -/
noncomputable def stageZ (p E : ℕ → X → X → ℝ) (ε : ℝ) (j : ℕ) (x : X) : ℝ :=
  gibbsPartition (p j x) (E j x) ε⁻¹

/-- The accepted row `Q_j(x, y) = p_j(x,y) e^{−E_j(x,y)/ε}/Z_j(x)`. -/
noncomputable def acceptedRow (p E : ℕ → X → X → ℝ) (ε : ℝ) (j : ℕ) (x y : X) : ℝ :=
  gibbsRow (p j x) (E j x) ε⁻¹ y

/-- The accepted product law `ℚ = ∏_j Q_j(x_j, x_{j+1})`. -/
noncomputable def acceptedPathLaw {M : ℕ} (x₀ : X) (p E : ℕ → X → X → ℝ) (ε : ℝ)
    (ω : Fin M → X) : ℝ :=
  markovLaw x₀ (acceptedRow p E ε) ω

/-- The total path cost `E(ω) = Σ_j E_j(x_j, x_{j+1})`. -/
noncomputable def pathCost {M : ℕ} (x₀ : X) (E : ℕ → X → X → ℝ) (ω : Fin M → X) : ℝ :=
  ∑ j : Fin M, E j (prevState x₀ ω j) (ω j)

variable [Nonempty X]

theorem stageZ_pos (p E : ℕ → X → X → ℝ) (ε : ℝ) (hp : ∀ j x y, 0 < p j x y) (j : ℕ)
    (x : X) : 0 < stageZ p E ε j x :=
  (gibbsRow_probability (p j x) (E j x) ε⁻¹ (hp j x)).1

theorem acceptedRow_pos (p E : ℕ → X → X → ℝ) (ε : ℝ) (hp : ∀ j x y, 0 < p j x y)
    (j : ℕ) (x y : X) : 0 < acceptedRow p E ε j x y :=
  (gibbsRow_probability (p j x) (E j x) ε⁻¹ (hp j x)).2.1 y

theorem acceptedRow_sum_one (p E : ℕ → X → X → ℝ) (ε : ℝ) (hp : ∀ j x y, 0 < p j x y)
    (j : ℕ) (x : X) : ∑ y, acceptedRow p E ε j x y = 1 :=
  (gibbsRow_probability (p j x) (E j x) ε⁻¹ (hp j x)).2.2

/-- `log Q_j(x,y) = log p_j(x,y) − E_j(x,y)/ε − log Z_j(x)`. -/
theorem log_acceptedRow (p E : ℕ → X → X → ℝ) (ε : ℝ) (hp : ∀ j x y, 0 < p j x y)
    (j : ℕ) (x y : X) :
    Real.log (acceptedRow p E ε j x y)
      = Real.log (p j x y) - E j x y / ε - Real.log (stageZ p E ε j x) := by
  unfold acceptedRow stageZ gibbsRow
  have hZ := (gibbsRow_probability (p j x) (E j x) ε⁻¹ (hp j x)).1
  rw [Real.log_div (mul_pos (hp j x y) (Real.exp_pos _)).ne' hZ.ne',
    Real.log_mul (hp j x y).ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- `log ℚ(ω) = log ℙ_ref(ω) − E(ω)/ε − Σ_j log Z_j(x_j)`. -/
theorem log_acceptedPathLaw {M : ℕ} (x₀ : X) (p E : ℕ → X → X → ℝ) (ε : ℝ)
    (hp : ∀ j x y, 0 < p j x y) (ω : Fin M → X) :
    Real.log (acceptedPathLaw x₀ p E ε ω)
      = Real.log (markovLaw x₀ p ω) - pathCost x₀ E ω / ε
        - ∑ j : Fin M, Real.log (stageZ p E ε j (prevState x₀ ω j)) := by
  unfold acceptedPathLaw pathCost
  rw [log_markovLaw x₀ _ (acceptedRow_pos p E ε hp) ω, log_markovLaw x₀ p hp ω,
    Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => log_acceptedRow p E ε hp j _ _

/-- `Σ_ω ℙ(ω) log(ℙ(ω)/q(ω)) = Σ_ω ℙ(ω) (log ℙ(ω) − log q(ω))` for `ℙ ≥ 0`, `q > 0`
(terms with `ℙ(ω) = 0` vanish on both sides). -/
theorem finiteKL_eq_sum_log_sub {Ω : Type*} [Fintype Ω] (P q : Ω → ℝ) (hP : ∀ u, 0 ≤ P u)
    (hq : ∀ u, 0 < q u) :
    finiteKL P q = ∑ u, P u * (Real.log (P u) - Real.log (q u)) := by
  unfold finiteKL
  refine Finset.sum_congr rfl fun u _ => ?_
  rcases (hP u).lt_or_eq with h | h
  · rw [Real.log_div h.ne' (hq u).ne']
  · rw [← h]; simp

/-- Exact path-level identity:
`ε D(ℙ‖ℚ) = ε D(ℙ‖ℙ_ref) + 𝔼_ℙ E + ε 𝔼_ℙ Σ_j log Z_j(x_j)`. -/
theorem finiteKL_acceptedPathLaw {M : ℕ} (x₀ : X) (p E : ℕ → X → X → ℝ) (ε : ℝ)
    (hε : ε ≠ 0) (hp : ∀ j x y, 0 < p j x y) (P : (Fin M → X) → ℝ) (hP : ∀ ω, 0 ≤ P ω) :
    ε * finiteKL P (acceptedPathLaw x₀ p E ε)
      = ε * finiteKL P (markovLaw x₀ p) + ∑ ω, P ω * pathCost x₀ E ω
        + ε * ∑ ω, P ω * ∑ j : Fin M, Real.log (stageZ p E ε j (prevState x₀ ω j)) := by
  have h1 := finiteKL_eq_sum_log_sub P (acceptedPathLaw x₀ p E ε) hP
    (fun ω => (markovLaw_pos x₀ _ (acceptedRow_pos p E ε hp) ω : 0 < acceptedPathLaw x₀ p E ε ω))
  have h2 := finiteKL_eq_sum_log_sub P (markovLaw x₀ p) hP (markovLaw_pos x₀ p hp)
  rw [h1, h2, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [log_acceptedPathLaw x₀ p E ε hp ω]
  field_simp
  ring

/-- The candidate bound `Z_j(x) ≥ p_{*,j} e^{−e_j/ε}`, hence
`−log Z_j(x) ≤ log(1/p_{*,j}) + e_j/ε`, from one proposal `y` with `E_j(x,y) ≤ e_j` and
`p_j(x,y) ≥ p_{*,j} > 0`. -/
theorem neg_log_stageZ_le (p E : ℕ → X → X → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hp : ∀ j x y, 0 < p j x y) (j : ℕ) (x : X) (e pstar : ℝ) (hpstar : 0 < pstar)
    (hcand : ∃ y, E j x y ≤ e ∧ pstar ≤ p j x y) :
    -Real.log (stageZ p E ε j x) ≤ Real.log (1 / pstar) + e / ε := by
  obtain ⟨y, hEy, hpy⟩ := hcand
  have hZ : pstar * Real.exp (-(e / ε)) ≤ stageZ p E ε j x := by
    unfold stageZ gibbsPartition
    calc pstar * Real.exp (-(e / ε)) ≤ p j x y * Real.exp (-ε⁻¹ * E j x y) := by
          refine mul_le_mul hpy ?_ (Real.exp_pos _).le (hp j x y).le
          apply Real.exp_le_exp.mpr
          rw [neg_mul, neg_le_neg_iff, inv_mul_eq_div]
          exact div_le_div_of_nonneg_right hEy hε.le
      _ ≤ ∑ y', p j x y' * Real.exp (-ε⁻¹ * E j x y') :=
          Finset.single_le_sum (f := fun y' => p j x y' * Real.exp (-ε⁻¹ * E j x y'))
            (fun y' _ => (mul_pos (hp j x y') (Real.exp_pos _)).le) (Finset.mem_univ y)
  have hlog := Real.log_le_log (mul_pos hpstar (Real.exp_pos _)) hZ
  rw [Real.log_mul hpstar.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  rw [one_div, Real.log_inv]
  linarith

/-- **`eq:supp-entropy-energy`** (`lem:supp-entropy-energy`): for any path law `ℙ`
on `Fin M → X` (same initial value `x₀`, memory allowed), with accepted product law
`ℚ`, if at every stage `j` and source state `x` some proposal `y` has cost
`E_j(x,y) ≤ e_j` and weight `p_j(x,y) ≥ p_{*,j} > 0`, then
`𝔼_ℙ Σ_j E_j ≤ Σ_j e_j + ε [Σ_j log(1/p_{*,j}) + D_KL(ℙ‖ℚ)]`. -/
theorem entropy_energy_estimate {M : ℕ} (x₀ : X) (p E : ℕ → X → X → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hp : ∀ j x y, 0 < p j x y) (hpsum : ∀ j x, ∑ y, p j x y = 1)
    (P : (Fin M → X) → ℝ) (hP : ∀ ω, 0 ≤ P ω) (hPsum : ∑ ω, P ω = 1)
    (e pstar : ℕ → ℝ) (hpstar : ∀ j : Fin M, 0 < pstar j)
    (hcand : ∀ (j : Fin M) (x : X), ∃ y, E j x y ≤ e j ∧ pstar j ≤ p j x y) :
    ∑ ω, P ω * pathCost x₀ E ω
      ≤ ∑ j : Fin M, e j
        + ε * (∑ j : Fin M, Real.log (1 / pstar j) + finiteKL P (acceptedPathLaw x₀ p E ε)) := by
  have hid := finiteKL_acceptedPathLaw x₀ p E ε hε.ne' hp P hP
  have hgibbs : 0 ≤ finiteKL P (markovLaw x₀ p) :=
    (AcceptedActionInformationPythagoras.finiteKL_nonneg_eq_iff_of_nonnegative P
      (markovLaw x₀ p) hP (markovLaw_pos x₀ p hp) hPsum (markovLaw_sum_one M x₀ p hpsum)).1
  -- the partition-function term
  have hZ : -∑ ω, P ω * ∑ j : Fin M, Real.log (stageZ p E ε j (prevState x₀ ω j))
      ≤ ∑ j : Fin M, (Real.log (1 / pstar j) + e j / ε) := by
    have h1 : -∑ ω, P ω * ∑ j : Fin M, Real.log (stageZ p E ε j (prevState x₀ ω j))
        ≤ ∑ ω, P ω * ∑ j : Fin M, (Real.log (1 / pstar j) + e j / ε) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun ω _ => ?_
      rw [← mul_neg]
      refine mul_le_mul_of_nonneg_left ?_ (hP ω)
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun j _ =>
        neg_log_stageZ_le p E ε hε hp j _ (e j) (pstar j) (hpstar j) (hcand j _)
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

end HistoryEntropyEnergy
end RenewalGeometry
