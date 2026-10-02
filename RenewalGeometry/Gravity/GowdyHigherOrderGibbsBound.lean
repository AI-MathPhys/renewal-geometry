/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.FiniteGibbsActionGap

/-!
# The path Gibbs entropy–energy bound of a finite positive offset/acceptance realization
  (`eq:supp-gowdy-gibbs-bound`; part of (G4) of `thm:main-gowdy-regulator`; emergent-spacetime
  supplement)

A finite positive realization of the Gowdy offsets gives each stage `j` (given the past) a finite
proposal row `p_j(·)` containing the zero offset, and accepts with probability `exp(-E_j/ε)` for a
nonnegative deviation cost `E_j` vanishing at the zero offset.  The declared accepted history law
is the product of the conditional Gibbs rows
`Q(ω) = ∏_j p_j(ω) e^{-E_j(ω)/ε} / Z_j(ω)`, and the zero offset gives `Z_j ≥ p_{*,j}` (the
reference mass of the zero offset).

* `finiteKL_nonneg_of_prob`: Gibbs' inequality for a nonnegative probability row against a
  strictly positive one (zero masses allowed in the first row).
* `normalizer_ge_zero_offset`: `Z_j = Σ_u p_j(u) e^{-E_j(u)/ε} ≥ p_j(0)` when `E_j ≥ 0` and
  `E_j(0) = 0`.
* `path_gibbs_bound` (**`eq:supp-gowdy-gibbs-bound`**): for every observed history law `P` on a
  finite history space, `𝔼_P Σ_j E_j ≤ ε [K_path + Σ_j log(1/p_{*,j})]`, where
  `K_path = D_KL(P ‖ Q)` is the (chain-rule) relative entropy of the observed history law against
  the declared accepted law.
-/

open Finset
open scoped BigOperators

namespace RenewalGeometry.GowdyStaggered.GibbsPath

variable {Ω : Type*} [Fintype Ω]

/-- **Gibbs' inequality** `D_KL(P ‖ R) ≥ 0` for a nonnegative probability row `P` (zero masses
allowed) against a strictly positive probability row `R`. -/
theorem finiteKL_nonneg_of_prob (P R : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (hR : ∀ ω, 0 < R ω)
    (hPs : ∑ ω, P ω = 1) (hRs : ∑ ω, R ω = 1) : 0 ≤ finiteKL P R := by
  unfold finiteKL
  have hterm : ∀ ω, P ω - R ω ≤ P ω * Real.log (P ω / R ω) := by
    intro ω
    rcases (hP ω).eq_or_lt with h | h
    · rw [← h]; simp [(hR ω).le]
    · have hl := Real.log_le_sub_one_of_pos (div_pos (hR ω) h)
      have e : Real.log (P ω / R ω) = -Real.log (R ω / P ω) := by
        rw [← Real.log_inv, inv_div]
      rw [e]
      have : P ω * (R ω / P ω - 1) = R ω - P ω := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hl h.le]
  calc (0 : ℝ) = ∑ ω, (P ω - R ω) := by rw [Finset.sum_sub_distrib, hPs, hRs, sub_self]
    _ ≤ _ := Finset.sum_le_sum fun ω _ => hterm ω

/-- The acceptance normalizer of a stage dominates the proposal mass of the zero offset. -/
theorem normalizer_ge_zero_offset {U : Type*} [Fintype U] (p E : U → ℝ) (u₀ : U) {ε : ℝ}
    (hp : ∀ u, 0 ≤ p u) (hE0 : E u₀ = 0) :
    p u₀ ≤ ∑ u, p u * Real.exp (-E u / ε) := by
  have h := Finset.single_le_sum (f := fun u => p u * Real.exp (-E u / ε))
    (fun u _ => mul_nonneg (hp u) (Real.exp_pos _).le) (mem_univ u₀)
  simpa [hE0] using h

/-- **The path Gibbs entropy–energy bound `eq:supp-gowdy-gibbs-bound`.**  Let the declared
accepted history law be the product of conditional Gibbs rows,
`Q(ω) = ∏_j p_j(ω) e^{-E_j(ω)/ε} / Z_j(ω)`, with reference proposal law `∏_j p_j(ω)` a probability
row, positive normalizers `Z_j ≥ p_{*,j} > 0`, and let `P` be any observed history law.  Then
`𝔼_P Σ_j E_j ≤ ε [D_KL(P ‖ Q) + Σ_j log(1/p_{*,j})]`. -/
theorem path_gibbs_bound {J : ℕ} (P Q : Ω → ℝ) (pr E Zs : Fin J → Ω → ℝ) (pstar : Fin J → ℝ)
    {ε : ℝ} (hε : 0 < ε) (hP : ∀ ω, 0 ≤ P ω) (hPs : ∑ ω, P ω = 1)
    (hpr : ∀ j ω, 0 < pr j ω) (hprs : ∑ ω, ∏ j, pr j ω = 1)
    (hpstar : ∀ j, 0 < pstar j) (hZ : ∀ j ω, pstar j ≤ Zs j ω)
    (hQ : ∀ ω, Q ω = ∏ j, (pr j ω * Real.exp (-E j ω / ε) / Zs j ω)) :
    ∑ ω, P ω * ∑ j, E j ω ≤ ε * (finiteKL P Q + ∑ j, Real.log (1 / pstar j)) := by
  set Pref : Ω → ℝ := fun ω => ∏ j, pr j ω
  have hPref : ∀ ω, 0 < Pref ω := fun ω => Finset.prod_pos fun j _ => hpr j ω
  have hZpos : ∀ j ω, 0 < Zs j ω := fun j ω => (hpstar j).trans_le (hZ j ω)
  have hQ' : ∀ ω, Q ω = Pref ω * Real.exp (-(∑ j, E j ω) / ε) / ∏ j, Zs j ω := by
    intro ω
    rw [hQ, Finset.prod_div_distrib, Finset.prod_mul_distrib, ← Real.exp_sum]
    congr 3
    rw [← Finset.sum_div, ← Finset.sum_neg_distrib]
  have hQpos : ∀ ω, 0 < Q ω := fun ω => by
    rw [hQ']; exact div_pos (mul_pos (hPref ω) (Real.exp_pos _))
      (Finset.prod_pos fun j _ => hZpos j ω)
  -- termwise identity `P log(P/Q) = P log(P/Pref) + P ΣE/ε + P Σ log Z`
  have hterm : ∀ ω, P ω * Real.log (P ω / Q ω) = P ω * Real.log (P ω / Pref ω) +
      P ω * (∑ j, E j ω) / ε + P ω * ∑ j, Real.log (Zs j ω) := by
    intro ω
    rcases (hP ω).eq_or_lt with h | h
    · rw [← h]; simp
    · have hr : P ω / Q ω = P ω / Pref ω * Real.exp ((∑ j, E j ω) / ε) * ∏ j, Zs j ω := by
        have hprod : 0 < ∏ j, Zs j ω := Finset.prod_pos fun j _ => hZpos j ω
        have hPr := hPref ω
        rw [hQ', neg_div, Real.exp_neg]
        field_simp
      rw [hr, Real.log_mul (mul_pos (div_pos h (hPref ω)) (Real.exp_pos _)).ne'
          (Finset.prod_pos fun j _ => hZpos j ω).ne',
        Real.log_mul (div_pos h (hPref ω)).ne' (Real.exp_pos _).ne', Real.log_exp,
        Real.log_prod (fun j _ => (hZpos j ω).ne')]
      ring
  have hKL : finiteKL P Q = finiteKL P Pref + (∑ ω, P ω * ∑ j, E j ω) / ε +
      ∑ ω, P ω * ∑ j, Real.log (Zs j ω) := by
    unfold finiteKL
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_div]
  have hKL0 : 0 ≤ finiteKL P Pref := finiteKL_nonneg_of_prob P Pref hP hPref hPs hprs
  have hlogZ : ∑ ω, P ω * ∑ j, Real.log (1 / pstar j) ≥ -∑ ω, P ω * ∑ j, Real.log (Zs j ω) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun ω _ => ?_
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (hP ω)
    rw [one_div, Real.log_inv, neg_le_neg_iff]
    exact Real.log_le_log (hpstar j) (hZ j ω)
  have hconst : ∑ ω, P ω * ∑ j, Real.log (1 / pstar j) = ∑ j, Real.log (1 / pstar j) := by
    rw [← Finset.sum_mul, hPs, one_mul]
  rw [hconst] at hlogZ
  have : (∑ ω, P ω * ∑ j, E j ω) / ε ≤ finiteKL P Q + ∑ j, Real.log (1 / pstar j) := by
    linarith
  rwa [div_le_iff₀ hε, mul_comm] at this

/-- Non-vacuity: a one-stage, one-history realization (only the zero offset) satisfies the
hypotheses of `path_gibbs_bound`. -/
example : ∑ ω : Fin 1, (1 : ℝ) * ∑ j : Fin 1, (0 : ℝ) ≤
    1 * (finiteKL (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 1) + ∑ j : Fin 1, Real.log (1 / 1)) :=
  path_gibbs_bound (Ω := Fin 1) (J := 1) (fun _ => 1) (fun _ => 1) (fun _ _ => 1) (fun _ _ => 0)
    (fun _ _ => 1) (fun _ => 1) one_pos (fun _ => zero_le_one) (by simp) (fun _ _ => one_pos)
    (by simp) (fun _ => one_pos) (fun _ _ => le_rfl) (fun _ => by simp)

end RenewalGeometry.GowdyStaggered.GibbsPath
