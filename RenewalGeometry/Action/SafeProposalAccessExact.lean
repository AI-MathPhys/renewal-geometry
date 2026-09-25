/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.FiniteGibbsActionGap

/-!
# Finite proposal-access certificate
(`prop:main-safe-access`, `eq:main-safe-proposal-bounds`, `eq:main-safe-retry-bound`,
`eq:supp-safe-retry-cap`; emergent-spacetime manuscript)

At a stage with finite proposal row `p` on a finite alphabet `U`, admissible set
`𝒢 ⊆ U`, cost `0 ≤ E ≤ c` on `𝒢`, temperature `ε > 0`, and the actual selection rule
`a = 1_𝒢 exp(−E/ε)`, write `Z = Σ_u p(u) a(u)` and `Q(u) = p(u) a(u)/Z`.

* `safeNormalizer_bounds`: **`eq:main-safe-proposal-bounds`** (first display)
  `μ e^{−c/ε} ≤ Z ≤ p(𝒢)` whenever `p(𝒢) ≥ μ`;
* `finiteKL_ge_neg_log_mass`: for every probability row `Q ≪ p` supported on `𝒢`,
  `D_KL(Q‖p) ≥ −log p(𝒢)` (the exact identity `D_KL(Q‖p) = D_KL(Q‖p_𝒢) − log p(𝒢)`
  of the proof, in inequality form), and `safeAcceptedRow_finiteKL_ge`: the second
  display of `eq:main-safe-proposal-bounds` for the accepted row;
* `retry_failure_bound`: **`eq:main-safe-retry-bound`**: with a genuine reset between
  retries (the failure events of the `R_j` attempts at stage `j` are independent, each
  of probability at most `1 − Z_j`), the probability that some stage `j < J` fails is at
  most `Σ_j exp(−R_j Z_j)`, and `retry_failure_bound_of_floor` substitutes the
  supported lower bound `Z_j ≥ μ_j e^{−c_j/ε_j}`;
* `retry_cap_sufficient`: the sufficient finite cap `eq:supp-safe-retry-cap`,
  `R_j ≥ μ_j^{−1} e^{c_j/ε_j} log(J/δ)` gives total failure at most `δ`;
* `ae_eventually_no_failure`: the first Borel–Cantelli lemma: if the failure
  probabilities along a countable refinement are summable, then almost surely only
  finitely many refinements fail (no independence between refinements needed).

Not formalised: the inheritance of the pathwise curvature and action-test estimates
of `thm:main-gowdy-regulator` by successful histories (that theorem is not in the
library); the Borel–Cantelli clause is stated for an abstract family of failure events.
-/

namespace RenewalGeometry.SafeProposalAccess

open Finset MeasureTheory ProbabilityTheory

variable {U : Type*} [Fintype U] [DecidableEq U]

/-! ### The stage bounds `eq:main-safe-proposal-bounds` -/

/-- The actual selection rule `1_𝒢(u) exp(−E(u)/ε)` (`prop:main-safe-access`). -/
noncomputable def safeAcceptance (G : Finset U) (E : U → ℝ) (ε : ℝ) (u : U) : ℝ :=
  if u ∈ G then Real.exp (-E u / ε) else 0

/-- The total acceptance `Z = Σ_u p(u) a(u)`. -/
noncomputable def safeNormalizer (p : U → ℝ) (G : Finset U) (E : U → ℝ) (ε : ℝ) : ℝ :=
  ∑ u, p u * safeAcceptance G E ε u

/-- The accepted row `Q(u) = p(u) a(u)/Z`. -/
noncomputable def safeAcceptedRow (p : U → ℝ) (G : Finset U) (E : U → ℝ) (ε : ℝ) (u : U) : ℝ :=
  p u * safeAcceptance G E ε u / safeNormalizer p G E ε

/-- The measured mass `p(𝒢) = Σ_{u ∈ 𝒢} p(u)` of the admissible set. -/
def proposalMass (p : U → ℝ) (G : Finset U) : ℝ := ∑ u ∈ G, p u

/-- `Z = Σ_{u ∈ 𝒢} p(u) e^{−E(u)/ε}`. -/
theorem safeNormalizer_eq_sum_mem (p : U → ℝ) (G : Finset U) (E : U → ℝ) (ε : ℝ) :
    safeNormalizer p G E ε = ∑ u ∈ G, p u * Real.exp (-E u / ε) := by
  unfold safeNormalizer safeAcceptance
  rw [← sum_ite_mem_eq G (fun u => p u * Real.exp (-E u / ε))]
  apply sum_congr rfl
  intro u _
  split_ifs <;> simp

/-- **`eq:main-safe-proposal-bounds`** (first display, `prop:main-safe-access`): if
`p(𝒢) ≥ μ` and `0 ≤ E ≤ c` on `𝒢` with `ε > 0`, then `μ e^{−c/ε} ≤ Z ≤ p(𝒢)`. -/
theorem safeNormalizer_bounds (p : U → ℝ) (G : Finset U) (E : U → ℝ) (ε c μ : ℝ)
    (hp : ∀ u, 0 ≤ p u) (hε : 0 < ε) (hE : ∀ u ∈ G, 0 ≤ E u ∧ E u ≤ c)
    (hμ : μ ≤ proposalMass p G) :
    μ * Real.exp (-c / ε) ≤ safeNormalizer p G E ε ∧
      safeNormalizer p G E ε ≤ proposalMass p G := by
  rw [safeNormalizer_eq_sum_mem]
  unfold proposalMass
  constructor
  · calc μ * Real.exp (-c / ε) ≤ (∑ u ∈ G, p u) * Real.exp (-c / ε) := by
          exact mul_le_mul_of_nonneg_right hμ (Real.exp_pos _).le
      _ = ∑ u ∈ G, p u * Real.exp (-c / ε) := by rw [sum_mul]
      _ ≤ ∑ u ∈ G, p u * Real.exp (-E u / ε) := by
          apply sum_le_sum
          intro u hu
          apply mul_le_mul_of_nonneg_left _ (hp u)
          apply Real.exp_le_exp.mpr
          have := (hE u hu).2
          rw [div_le_div_iff_of_pos_right hε]
          linarith
  · apply sum_le_sum
    intro u hu
    have h1 : Real.exp (-E u / ε) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := (hE u hu).1
      apply div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
    calc p u * Real.exp (-E u / ε) ≤ p u * 1 := mul_le_mul_of_nonneg_left h1 (hp u)
      _ = p u := mul_one _

/-- Per-term bound for the relative entropy against the renormalised row `p_𝒢 = p/p(𝒢)`:
`Q log(Q/p) ≥ Q − p/p(𝒢) − Q log p(𝒢)` (for `Q ≥ 0`, `Q > 0 → p > 0`, `p ≥ 0`,
`p(𝒢) > 0`). -/
theorem term_bound (Q p m : ℝ) (hQ : 0 ≤ Q) (hp : 0 ≤ p) (hQp : 0 < Q → 0 < p) (hm : 0 < m) :
    Q - p / m - Q * Real.log m ≤ Q * Real.log (Q / p) := by
  rcases hQ.lt_or_eq with hQpos | hQ0
  · have hppos := hQp hQpos
    have hx : 0 < Q * m / p := by positivity
    have h1 := Real.one_sub_inv_le_log_of_pos hx
    have h2 : Real.log (Q * m / p) = Real.log (Q / p) + Real.log m := by
      rw [show Q * m / p = Q / p * m by ring, Real.log_mul (div_pos hQpos hppos).ne' hm.ne']
    rw [h2] at h1
    have h3 : (Q * m / p)⁻¹ = p / (Q * m) := by rw [inv_div]
    rw [h3] at h1
    have h4 : Q * (1 - p / (Q * m)) = Q - p / m := by field_simp
    have h5 : Q * (1 - p / (Q * m)) ≤ Q * (Real.log (Q / p) + Real.log m) :=
      mul_le_mul_of_nonneg_left h1 hQpos.le
    rw [h4] at h5
    linarith
  · rw [← hQ0]
    simp only [zero_sub, zero_mul, sub_zero]
    have : 0 ≤ p / m := div_nonneg hp hm.le
    linarith

/-- **`eq:main-safe-proposal-bounds`** (second display, general form): for every
probability row `Q` supported on `𝒢` and absolutely continuous with respect to `p`
(`Q(u) > 0 → p(u) > 0`), `D_KL(Q‖p) ≥ −log p(𝒢)`, where `finiteKL Q p = Σ_u Q log(Q/p)`.
This is the exact identity `D_KL(Q‖p) = D_KL(Q‖p_𝒢) − log p(𝒢)` of the proof combined
with Gibbs' inequality `D_KL(Q‖p_𝒢) ≥ 0`. -/
theorem finiteKL_ge_neg_log_mass (Q p : U → ℝ) (G : Finset U) (hQ : ∀ u, 0 ≤ Q u)
    (hQsum : ∑ u, Q u = 1) (hQsupp : ∀ u, u ∉ G → Q u = 0) (hp : ∀ u, 0 ≤ p u)
    (hQp : ∀ u, 0 < Q u → 0 < p u) (hmass : 0 < proposalMass p G) :
    -Real.log (proposalMass p G) ≤ finiteKL Q p := by
  unfold finiteKL
  have hsub : G ⊆ (univ : Finset U) := subset_univ G
  have hQG : ∑ u ∈ G, Q u = 1 := by
    rw [← hQsum]
    exact sum_subset hsub (fun u _ hu => hQsupp u hu)
  have hKL : ∑ u, Q u * Real.log (Q u / p u) = ∑ u ∈ G, Q u * Real.log (Q u / p u) := by
    symm
    exact sum_subset hsub (fun u _ hu => by rw [hQsupp u hu]; simp)
  rw [hKL]
  have hterm : ∀ u ∈ G, Q u - p u / proposalMass p G - Q u * Real.log (proposalMass p G)
      ≤ Q u * Real.log (Q u / p u) :=
    fun u _ => term_bound (Q u) (p u) _ (hQ u) (hp u) (hQp u) hmass
  have hsum := sum_le_sum hterm
  rw [sum_sub_distrib, sum_sub_distrib, hQG, ← sum_div, ← sum_mul, hQG] at hsum
  have hpm : ∑ i ∈ G, p i = proposalMass p G := rfl
  rw [hpm, div_self hmass.ne'] at hsum
  linarith

/-- The accepted row is a probability row supported on `𝒢`, absolutely continuous
with respect to `p`, when `Z > 0`. -/
theorem safeAcceptedRow_probability (p : U → ℝ) (G : Finset U) (E : U → ℝ) (ε : ℝ)
    (hp : ∀ u, 0 ≤ p u) (hZ : 0 < safeNormalizer p G E ε) :
    (∀ u, 0 ≤ safeAcceptedRow p G E ε u) ∧ (∑ u, safeAcceptedRow p G E ε u = 1) ∧
      (∀ u, u ∉ G → safeAcceptedRow p G E ε u = 0) ∧
      (∀ u, 0 < safeAcceptedRow p G E ε u → 0 < p u) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    unfold safeAcceptedRow safeAcceptance
    apply div_nonneg _ hZ.le
    apply mul_nonneg (hp u)
    split_ifs <;> positivity
  · unfold safeAcceptedRow
    rw [← sum_div]
    exact div_self hZ.ne'
  · intro u hu
    unfold safeAcceptedRow safeAcceptance
    simp [hu]
  · intro u hu
    unfold safeAcceptedRow at hu
    have := (div_pos_iff_of_pos_right hZ).mp hu
    rcases (hp u).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at this
      exact absurd this (lt_irrefl _)

/-- **`eq:main-safe-proposal-bounds`** (second display, `prop:main-safe-access`): the
accepted row of the actual rule satisfies `D_KL(Q‖p) ≥ −log p(𝒢)`. -/
theorem safeAcceptedRow_finiteKL_ge (p : U → ℝ) (G : Finset U) (E : U → ℝ) (ε : ℝ)
    (hp : ∀ u, 0 ≤ p u) (hZ : 0 < safeNormalizer p G E ε) (hmass : 0 < proposalMass p G) :
    -Real.log (proposalMass p G) ≤ finiteKL (safeAcceptedRow p G E ε) p := by
  obtain ⟨h1, h2, h3, h4⟩ := safeAcceptedRow_probability p G E ε hp hZ
  exact finiteKL_ge_neg_log_mass _ p G h1 h2 h3 hp h4 hmass

/-- The normaliser is positive under the floor `μ > 0` (so the accepted row exists);
`μ = 0` precludes an accepted row altogether. -/
theorem safeNormalizer_pos (p : U → ℝ) (G : Finset U) (E : U → ℝ) (ε c μ : ℝ)
    (hp : ∀ u, 0 ≤ p u) (hε : 0 < ε) (hE : ∀ u ∈ G, 0 ≤ E u ∧ E u ≤ c)
    (hμ : μ ≤ proposalMass p G) (hμpos : 0 < μ) : 0 < safeNormalizer p G E ε :=
  lt_of_lt_of_le (by positivity) (safeNormalizer_bounds p G E ε c μ hp hε hE hμ).1

/-! ### The retry bound `eq:main-safe-retry-bound` -/

/-- `(1 − Z)^R ≤ exp(−R Z)` for `Z ≤ 1`. -/
theorem one_sub_pow_le_exp (Z : ℝ) (hZ1 : Z ≤ 1) (R : ℕ) :
    (1 - Z) ^ R ≤ Real.exp (-(R : ℝ) * Z) := by
  have h : 1 - Z ≤ Real.exp (-Z) := by
    have := Real.add_one_le_exp (-Z)
    linarith
  calc (1 - Z) ^ R ≤ Real.exp (-Z) ^ R := pow_le_pow_left₀ (by linarith) h R
    _ = Real.exp (-(R : ℝ) * Z) := by rw [← Real.exp_nat_mul]; ring_nf

/-- The failure probability of `R` independent reset attempts, each failing with
probability at most `1 − Z`, is at most `(1 − Z)^R ≤ exp(−R Z)`. -/
theorem stage_failure_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : ℕ → Set Ω) (hind : iIndepSet F μ) (Z : ℝ) (hZ0 : 0 ≤ Z) (hZ1 : Z ≤ 1)
    (hfail : ∀ i, μ (F i) ≤ ENNReal.ofReal (1 - Z)) (R : ℕ) :
    μ (⋂ i ∈ range R, F i) ≤ ENNReal.ofReal (Real.exp (-(R : ℝ) * Z)) := by
  rw [hind.meas_biInter (range R)]
  calc ∏ i ∈ range R, μ (F i) ≤ ∏ i ∈ range R, ENNReal.ofReal (1 - Z) :=
        prod_le_prod' (fun i _ => hfail i)
    _ = ENNReal.ofReal ((1 - Z) ^ R) := by
        rw [prod_const, card_range, ENNReal.ofReal_pow (by linarith)]
    _ ≤ ENNReal.ofReal (Real.exp (-(R : ℝ) * Z)) :=
        ENNReal.ofReal_le_ofReal (one_sub_pow_le_exp Z hZ1 R)

/-- **`eq:main-safe-retry-bound`** (`prop:main-safe-access`): with a genuine reset to the
same source between retries — the failure events `F j i` of the attempts `i` at stage `j`
are independent with `μ(F j i) ≤ 1 − Z_j` — and caps `R_j`, the probability that some
stage `j < J` fails (all its `R_j` attempts fail) is at most `Σ_{j<J} exp(−R_j Z_j)`. -/
theorem retry_failure_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (J : ℕ)
    (R : ℕ → ℕ) (F : ℕ → ℕ → Set Ω) (hind : ∀ j, iIndepSet (F j) μ) (Z : ℕ → ℝ)
    (hZ0 : ∀ j, 0 ≤ Z j) (hZ1 : ∀ j, Z j ≤ 1)
    (hfail : ∀ j i, μ (F j i) ≤ ENNReal.ofReal (1 - Z j)) :
    μ (⋃ j ∈ range J, ⋂ i ∈ range (R j), F j i)
      ≤ ENNReal.ofReal (∑ j ∈ range J, Real.exp (-(R j : ℝ) * Z j)) := by
  calc μ (⋃ j ∈ range J, ⋂ i ∈ range (R j), F j i)
      ≤ ∑ j ∈ range J, μ (⋂ i ∈ range (R j), F j i) := measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ range J, ENNReal.ofReal (Real.exp (-(R j : ℝ) * Z j)) :=
        sum_le_sum (fun j _ => stage_failure_le μ (F j) (hind j) (Z j) (hZ0 j) (hZ1 j)
          (hfail j) (R j))
    _ = ENNReal.ofReal (∑ j ∈ range J, Real.exp (-(R j : ℝ) * Z j)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => (Real.exp_pos _).le)]

/-- **`eq:main-safe-retry-bound`** with the supported lower bound: if each attempt at
stage `j` succeeds with probability at least the floor `μ_j e^{−c_j/ε_j}` (i.e. fails
with probability at most `1 − μ_j e^{−c_j/ε_j}`, with `μ_j ≤ 1`), then
`Pr(some stage fails) ≤ Σ_j exp[−R_j μ_j e^{−c_j/ε_j}]`. -/
theorem retry_failure_bound_of_floor {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (J : ℕ)
    (R : ℕ → ℕ) (F : ℕ → ℕ → Set Ω) (hind : ∀ j, iIndepSet (F j) μ) (μs c ε : ℕ → ℝ)
    (hμ0 : ∀ j, 0 ≤ μs j) (hμ1 : ∀ j, μs j ≤ 1) (hε : ∀ j, 0 < ε j) (hc : ∀ j, 0 ≤ c j)
    (hfail : ∀ j i, μ (F j i) ≤ ENNReal.ofReal (1 - μs j * Real.exp (-c j / ε j))) :
    μ (⋃ j ∈ range J, ⋂ i ∈ range (R j), F j i)
      ≤ ENNReal.ofReal (∑ j ∈ range J, Real.exp (-(R j : ℝ) * (μs j * Real.exp (-c j / ε j)))) := by
  refine retry_failure_bound μ J R F hind (fun j => μs j * Real.exp (-c j / ε j))
    (fun j => by have := hμ0 j; positivity) (fun j => ?_) hfail
  have h1 : Real.exp (-c j / ε j) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hc j]) (hε j).le
  calc μs j * Real.exp (-c j / ε j) ≤ 1 * 1 :=
        mul_le_mul (hμ1 j) h1 (Real.exp_pos _).le zero_le_one
    _ = 1 := one_mul _

/-- The sufficient finite cap `eq:supp-safe-retry-cap`: for `J` stages and total failure
target `0 < δ < 1`, if `R_j ≥ μ_j^{−1} e^{c_j/ε_j} log(J/δ)` for all `j < J` (with
`μ_j > 0`), then `Σ_{j<J} exp[−R_j μ_j e^{−c_j/ε_j}] ≤ δ`. -/
theorem retry_cap_sufficient (J : ℕ) (hJ : 0 < J) (R : ℕ → ℕ) (μs c ε : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hμ : ∀ j, 0 < μs j)
    (hR : ∀ j < J, (μs j)⁻¹ * Real.exp (c j / ε j) * Real.log (J / δ) ≤ (R j : ℝ)) :
    ∑ j ∈ range J, Real.exp (-(R j : ℝ) * (μs j * Real.exp (-c j / ε j))) ≤ δ := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hterm : ∀ j ∈ range J,
      Real.exp (-(R j : ℝ) * (μs j * Real.exp (-c j / ε j))) ≤ δ / J := by
    intro j hj
    have hj' := mem_range.mp hj
    have hμj := hμ j
    have hepos := Real.exp_pos (c j / ε j)
    have key : Real.log (J / δ) ≤ (R j : ℝ) * (μs j * Real.exp (-c j / ε j)) := by
      have h := hR j hj'
      have hexp : Real.exp (-c j / ε j) = (Real.exp (c j / ε j))⁻¹ := by
        rw [← Real.exp_neg]; congr 1; ring
      rw [hexp]
      have hprod : (μs j)⁻¹ * Real.exp (c j / ε j) * Real.log (J / δ)
          * (μs j * (Real.exp (c j / ε j))⁻¹) = Real.log (J / δ) := by
        field_simp
      calc Real.log (J / δ)
          = (μs j)⁻¹ * Real.exp (c j / ε j) * Real.log (J / δ)
            * (μs j * (Real.exp (c j / ε j))⁻¹) := hprod.symm
        _ ≤ (R j : ℝ) * (μs j * (Real.exp (c j / ε j))⁻¹) :=
            mul_le_mul_of_nonneg_right h (by positivity)
    calc Real.exp (-(R j : ℝ) * (μs j * Real.exp (-c j / ε j)))
        ≤ Real.exp (-Real.log (J / δ)) := by
          apply Real.exp_le_exp.mpr; linarith
      _ = δ / J := by
          rw [Real.exp_neg, Real.exp_log (div_pos hJpos hδ), inv_div]
  calc ∑ j ∈ range J, Real.exp (-(R j : ℝ) * (μs j * Real.exp (-c j / ε j)))
      ≤ ∑ j ∈ range J, δ / J := sum_le_sum hterm
    _ = δ := by rw [sum_const, card_range, nsmul_eq_mul]; field_simp

/-! ### Borel–Cantelli along refinements -/

/-- The first Borel–Cantelli lemma (`prop:main-safe-access`, last sentence): if the
failure probabilities along a countable refinement are summable, then almost surely
only finitely many refinements fail, i.e. the conclusions hold on every sufficiently
fine successful refinement; no independence between refinements is used. -/
theorem ae_eventually_no_failure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Fail : ℕ → Set Ω) (hsum : ∑' n, μ (Fail n) ≠ ⊤) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop, ω ∉ Fail n := by
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_limsup_atTop_eq_zero hsum)
  intro ω hω
  rw [Filter.mem_limsup_iff_frequently_mem, Filter.frequently_atTop]
  simpa [Filter.not_eventually, Filter.frequently_atTop] using hω

end RenewalGeometry.SafeProposalAccess
