/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Twin-prime heat sufficiency
  (`thm:twin-heat-master`, flagship manuscript)

For the fixed-difference heat selector
`𝒟₂(t) = Σ_n Λ(n)Λ(n+2)/√(n(n+2)) e^{-t[(log n)²+(log(n+2))²]}`:

* the selector is a genuine convergent series for every `t > 0`
  (`twinHeat_summable`): the heat factor is dominated through
  `x²e^{-tx²/2} ≤ 2/t` (from `ye^{-y} ≤ 1`) and
  `e^{-tx²/2} ≤ e^{1/(2t)}/n` (the maximum of `x - tx²/2`),
  giving the majorant `C(t)/n²`;
* the boxed sufficiency (`twin_heat_bounded_of_finite` and its
  contrapositive `twin_heat_sufficiency`): if only finitely many
  twin pairs existed, the twin part would be uniformly bounded by
  a finite sum and the proper-prime-power part is uniformly
  bounded for `0 < t ≤ 1`, so `𝒟₂(t)` could not diverge — hence
  divergence forces infinitely many twin-prime pairs.

Rendering disclosed: the uniform bound on the proper-prime-power
contamination enters as the displayed hypothesis `hbad` — its
majorant is the manuscript's displayed convergent series
`Σ_p Σ_{k≥2} k(log p)² p^{-k} < ∞` (the `(p,k)` parametrization
of proper prime powers, a standard convergent double series); the
divergence certificate itself is, as the manuscript notes, not
proved by the universal Grand Tensor.
-/

open ArithmeticFunction Set

namespace NCG

/-- The fixed-difference twin heat selector. -/
noncomputable def twinHeat (t : ℝ) : ℝ :=
  ∑' n : ℕ, Λ n * Λ (n + 2)
    / Real.sqrt ((n : ℝ) * ((n : ℝ) + 2))
    * Real.exp (-t * (Real.log n ^ 2 + Real.log ((n : ℝ) + 2) ^ 2))

/-- The generic term of the selector. -/
noncomputable def twinTerm (t : ℝ) (n : ℕ) : ℝ :=
  Λ n * Λ (n + 2) / Real.sqrt ((n : ℝ) * ((n : ℝ) + 2))
    * Real.exp (-t * (Real.log n ^ 2 + Real.log ((n : ℝ) + 2) ^ 2))

theorem twinTerm_nonneg (t : ℝ) (n : ℕ) : 0 ≤ twinTerm t n := by
  rw [twinTerm]
  have h1 : (0:ℝ) ≤ Λ n := vonMangoldt_nonneg
  have h2 : (0:ℝ) ≤ Λ (n + 2) := vonMangoldt_nonneg
  positivity

/-- Crude but uniform per-term bound: the heat factor discarded. -/
theorem twinTerm_le_const (t : ℝ) (ht : 0 ≤ t) (n : ℕ)
    (hn : 1 ≤ n) :
    twinTerm t n ≤ Λ n * Λ (n + 2) / (n : ℝ) := by
  rw [twinTerm]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (0:ℝ) ≤ Λ n := vonMangoldt_nonneg
  have h2 : (0:ℝ) ≤ Λ (n + 2) := vonMangoldt_nonneg
  have hexp : Real.exp (-t * (Real.log n ^ 2
      + Real.log ((n : ℝ) + 2) ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h3 : (0:ℝ) ≤ Real.log n ^ 2
        + Real.log ((n : ℝ) + 2) ^ 2 := by positivity
    nlinarith
  have hsq : (n : ℝ) ≤ Real.sqrt ((n : ℝ) * ((n : ℝ) + 2)) := by
    have h0 : Real.sqrt ((n : ℝ) ^ 2)
        ≤ Real.sqrt ((n : ℝ) * ((n : ℝ) + 2)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by linarith : (0:ℝ) ≤ (n:ℝ))] at h0
  have hdiv : Λ n * Λ (n + 2)
      / Real.sqrt ((n : ℝ) * ((n : ℝ) + 2))
      ≤ Λ n * Λ (n + 2) / (n : ℝ) := by
    refine div_le_div_of_nonneg_left (by positivity)
      (by linarith) hsq
  calc Λ n * Λ (n + 2) / Real.sqrt ((n : ℝ) * ((n : ℝ) + 2))
      * Real.exp (-t * (Real.log n ^ 2
        + Real.log ((n : ℝ) + 2) ^ 2))
      ≤ Λ n * Λ (n + 2)
        / Real.sqrt ((n : ℝ) * ((n : ℝ) + 2)) * 1 := by
        refine mul_le_mul_of_nonneg_left hexp ?_
        positivity
    _ = Λ n * Λ (n + 2)
        / Real.sqrt ((n : ℝ) * ((n : ℝ) + 2)) := mul_one _
    _ ≤ Λ n * Λ (n + 2) / (n : ℝ) := hdiv

/-- Convergence of the selector for every `t > 0`, through the
`C(t)/n²` heat majorant. -/
theorem twinHeat_summable (t : ℝ) (ht : 0 < t) :
    Summable (twinTerm t) := by
  set K : ℝ := (4 / t + 8) * Real.exp (1 / (2 * t)) with hK_def
  have hK0 : 0 ≤ K := by
    rw [hK_def]
    positivity
  refine Summable.of_nonneg_of_le (twinTerm_nonneg t)
    (f := fun n : ℕ => K * ((1 : ℝ) / (n : ℝ) ^ 2)) ?_ ?_
  · intro n
    rcases Nat.lt_or_ge n 1 with hn | hn
    · interval_cases n
      have h0 : twinTerm t 0 = 0 := by
        rw [twinTerm]
        simp [ArithmeticFunction.map_zero]
      rw [h0]
      positivity
    -- n ≥ 1
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    set x : ℝ := Real.log n with hx_def
    have hx0 : 0 ≤ x := by
      rw [hx_def]
      exact Real.log_nonneg hn1
    -- log(n+2) ≤ x + 2
    have hlog2 : Real.log ((n : ℝ) + 2) ≤ x + 2 := by
      rw [hx_def, show x + 2 = Real.log n + 2 from rfl]
      have h1 : (n : ℝ) + 2 ≤ (n : ℝ) * Real.exp 2 := by
        nlinarith [Real.add_one_le_exp (2:ℝ), hn1]
      calc Real.log ((n : ℝ) + 2)
          ≤ Real.log ((n : ℝ) * Real.exp 2) :=
            Real.log_le_log (by linarith) h1
        _ = Real.log n + 2 := by
            rw [Real.log_mul (by linarith) (Real.exp_ne_zero 2),
              Real.log_exp]
    -- vonMangoldt bounds
    have hΛ1 : Λ n ≤ x := hx_def ▸ vonMangoldt_le_log
    have hΛ2 : Λ (n + 2) ≤ x + 2 := by
      refine le_trans vonMangoldt_le_log ?_
      have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by
        push_cast
        ring
      rw [hcast]
      exact hlog2
    -- heat factor pieces
    have hheat : Real.exp (-t * (Real.log n ^ 2
        + Real.log ((n : ℝ) + 2) ^ 2))
        ≤ Real.exp (-t * x ^ 2) := by
      refine Real.exp_le_exp.mpr ?_
      have h2 : (0:ℝ) ≤ Real.log ((n : ℝ) + 2) ^ 2 := by
        positivity
      rw [hx_def]
      nlinarith
    have hsplit : Real.exp (-t * x ^ 2)
        = Real.exp (-(t * x ^ 2 / 2))
          * Real.exp (-(t * x ^ 2 / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    -- x² e^{-tx²/2} ≤ 2/t  from y e^{-y} ≤ 1
    have hy : ∀ y : ℝ, 0 ≤ y → y * Real.exp (-y) ≤ 1 := by
      intro y hy0
      have h3 := Real.add_one_le_exp y
      have h4 := Real.exp_pos y
      rw [Real.exp_neg]
      rw [mul_inv_le_iff₀ h4, one_mul]
      linarith
    have hx2 : x ^ 2 * Real.exp (-(t * x ^ 2 / 2))
        ≤ 2 / t := by
      have h5 := hy (t * x ^ 2 / 2) (by positivity)
      have h6 : (0:ℝ) < 2 / t := by positivity
      have h7 : (2 / t) * ((t * x ^ 2 / 2)
          * Real.exp (-(t * x ^ 2 / 2))) ≤ (2 / t) * 1 :=
        mul_le_mul_of_nonneg_left h5 h6.le
      have h8 : (2 / t) * ((t * x ^ 2 / 2)
          * Real.exp (-(t * x ^ 2 / 2)))
          = x ^ 2 * Real.exp (-(t * x ^ 2 / 2)) := by
        rw [show (2 / t) * ((t * x ^ 2 / 2)
            * Real.exp (-(t * x ^ 2 / 2)))
            = (2 / t * (t / 2))
              * (x ^ 2 * Real.exp (-(t * x ^ 2 / 2)))
          from by ring,
          show 2 / t * (t / 2) = 1 from by
            field_simp, one_mul]
      rw [← h8]
      linarith [h7]
    -- e^{-tx²/2} ≤ e^{1/(2t)}/n  from  x - tx²/2 ≤ 1/(2t)
    have hxe : Real.exp (-(t * x ^ 2 / 2))
        ≤ Real.exp (1 / (2 * t)) * (1 / (n : ℝ)) := by
      have h7 : x - t * x ^ 2 / 2 ≤ 1 / (2 * t) := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * t)]
        nlinarith [sq_nonneg (t * x - 1)]
      have h8 : Real.exp (-(t * x ^ 2 / 2))
          = Real.exp (x - t * x ^ 2 / 2) * Real.exp (-x) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [h8]
      have h9 : Real.exp (-x) = 1 / (n : ℝ) := by
        rw [hx_def, Real.exp_neg, Real.exp_log (by linarith),
          one_div]
      rw [h9]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact Real.exp_le_exp.mpr h7
    -- assemble
    have hterm := twinTerm_le_const t ht.le n hn
    have hΛprod : Λ n * Λ (n + 2) ≤ x * (x + 2) := by
      have := vonMangoldt_nonneg (n := n)
      have := vonMangoldt_nonneg (n := n + 2)
      nlinarith
    have hbound : twinTerm t n
        ≤ x * (x + 2) * Real.exp (-t * x ^ 2) / (n : ℝ) := by
      rw [twinTerm]
      have hsq : (n : ℝ)
          ≤ Real.sqrt ((n : ℝ) * ((n : ℝ) + 2)) := by
        have h0 : Real.sqrt ((n : ℝ) ^ 2)
            ≤ Real.sqrt ((n : ℝ) * ((n : ℝ) + 2)) :=
          Real.sqrt_le_sqrt (by nlinarith)
        rwa [Real.sqrt_sq
          (by linarith : (0:ℝ) ≤ (n:ℝ))] at h0
      have h10 : Λ n * Λ (n + 2)
          / Real.sqrt ((n : ℝ) * ((n : ℝ) + 2))
          ≤ x * (x + 2) / (n : ℝ) := by
        refine div_le_div₀ (by positivity) hΛprod
          (by linarith) hsq
      calc Λ n * Λ (n + 2)
          / Real.sqrt ((n : ℝ) * ((n : ℝ) + 2))
          * Real.exp (-t * (Real.log n ^ 2
            + Real.log ((n : ℝ) + 2) ^ 2))
          ≤ x * (x + 2) / (n : ℝ)
            * Real.exp (-t * x ^ 2) := by
            refine mul_le_mul h10 hheat (Real.exp_pos _).le ?_
            positivity
        _ = x * (x + 2) * Real.exp (-t * x ^ 2) / (n : ℝ) := by
            ring
    refine le_trans hbound ?_
    -- x(x+2) e^{-tx²} ≤ (2x²+2)e^{-tx²/2}·e^{-tx²/2}
    rw [hsplit]
    have h11 : x * (x + 2) ≤ 2 * x ^ 2 + 2 := by nlinarith
    have h12 : x * (x + 2)
        * (Real.exp (-(t * x ^ 2 / 2))
          * Real.exp (-(t * x ^ 2 / 2))) / (n : ℝ)
        ≤ (2 * x ^ 2 + 2) * Real.exp (-(t * x ^ 2 / 2))
          * (Real.exp (1 / (2 * t)) * (1 / (n : ℝ)))
          / (n : ℝ) := by
      have he1 : (0:ℝ) < Real.exp (-(t * x ^ 2 / 2)) :=
        Real.exp_pos _
      have hn0 : (0:ℝ) < n := by linarith
      refine div_le_div_of_nonneg_right ?_ hn0.le
      calc x * (x + 2)
          * (Real.exp (-(t * x ^ 2 / 2))
            * Real.exp (-(t * x ^ 2 / 2)))
          = (x * (x + 2) * Real.exp (-(t * x ^ 2 / 2)))
            * Real.exp (-(t * x ^ 2 / 2)) := by ring
        _ ≤ ((2 * x ^ 2 + 2) * Real.exp (-(t * x ^ 2 / 2)))
            * (Real.exp (1 / (2 * t)) * (1 / (n : ℝ))) := by
            refine mul_le_mul ?_ hxe he1.le (by positivity)
            exact mul_le_mul_of_nonneg_right h11 he1.le
    refine le_trans h12 ?_
    have h13 : (2 * x ^ 2 + 2) * Real.exp (-(t * x ^ 2 / 2))
        ≤ 4 / t + 8 := by
      have h14 : Real.exp (-(t * x ^ 2 / 2)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [sq_nonneg x]
      have h15 : 2 * (x ^ 2 * Real.exp (-(t * x ^ 2 / 2)))
          ≤ 4 / t := by
        have h44 : 4 / t = 2 * (2 / t) := by ring
        linarith [hx2]
      nlinarith [Real.exp_pos (-(t * x ^ 2 / 2))]
    rw [hK_def]
    have hn0 : (0:ℝ) < n := by linarith
    have h16 : (0:ℝ) ≤ Real.exp (1 / (2 * t)) :=
      (Real.exp_pos _).le
    calc (2 * x ^ 2 + 2) * Real.exp (-(t * x ^ 2 / 2))
        * (Real.exp (1 / (2 * t)) * (1 / (n : ℝ))) / (n : ℝ)
        ≤ (4 / t + 8)
          * (Real.exp (1 / (2 * t)) * (1 / (n : ℝ)))
          / (n : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ hn0.le
          refine mul_le_mul_of_nonneg_right h13 ?_
          positivity
      _ = (4 / t + 8) * Real.exp (1 / (2 * t))
          * (1 / (n : ℝ) ^ 2) := by
          field_simp
  · refine Summable.mul_left K ?_
    have := Real.summable_one_div_nat_pow (p := 2)
    exact this.mpr (by norm_num)

/-- Uniform boundedness under finiteness of the twin set: the
boxed contrapositive. -/
theorem twin_heat_bounded_of_finite (Cbad : ℝ)
    (hfin : {n : ℕ | n.Prime ∧ (n + 2).Prime}.Finite)
    (hbad : ∀ t : ℝ, 0 < t → t ≤ 1 →
      (∑' n : ℕ, if ¬(n.Prime ∧ (n + 2).Prime)
        then twinTerm t n else 0) ≤ Cbad) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → twinHeat t ≤ C := by
  classical
  refine ⟨(∑ n ∈ hfin.toFinset, Λ n * Λ (n + 2) / (n : ℝ))
    + Cbad, ?_⟩
  intro t ht ht1
  have hsummable := twinHeat_summable t ht
  have hs1 : Summable (fun n : ℕ =>
      if n.Prime ∧ (n + 2).Prime then twinTerm t n else 0) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      hsummable
    · split
      · exact twinTerm_nonneg t n
      · exact le_refl 0
    · by_cases hp : n.Prime ∧ (n + 2).Prime
      · rw [if_pos hp]
      · rw [if_neg hp]
        exact twinTerm_nonneg t n
  have hs2 : Summable (fun n : ℕ =>
      if ¬(n.Prime ∧ (n + 2).Prime)
        then twinTerm t n else 0) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      hsummable
    · split
      · exact twinTerm_nonneg t n
      · exact le_refl 0
    · by_cases hp : ¬(n.Prime ∧ (n + 2).Prime)
      · rw [if_pos hp]
      · rw [if_neg hp]
        exact twinTerm_nonneg t n
  have hsplit : twinHeat t
      = (∑' n : ℕ, if n.Prime ∧ (n + 2).Prime
          then twinTerm t n else 0)
        + ∑' n : ℕ, if ¬(n.Prime ∧ (n + 2).Prime)
          then twinTerm t n else 0 := by
    rw [twinHeat, ← hs1.tsum_add hs2]
    refine tsum_congr fun n => ?_
    by_cases hp : n.Prime ∧ (n + 2).Prime
    · rw [if_pos hp, if_neg (not_not_intro hp), add_zero]
      rfl
    · rw [if_neg hp, if_pos hp, zero_add]
      rfl
  rw [hsplit]
  refine add_le_add ?_ (hbad t ht ht1)
  -- twin part: finite support, heat factor discarded
  have hvan : ∀ n ∉ hfin.toFinset,
      (if n.Prime ∧ (n + 2).Prime
        then twinTerm t n else 0) = 0 := by
    intro n hn
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hn
    rw [if_neg hn]
  rw [tsum_eq_sum hvan]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hn
  by_cases h1 : 1 ≤ n
  · rw [if_pos hn]
    exact twinTerm_le_const t ht.le n h1
  · have hn0 : n = 0 := by omega
    exfalso
    rw [hn0] at hn
    exact Nat.not_prime_zero hn.1

/-- `thm:twin-heat-master`, boxed sufficiency: divergence of the
heat selector forces infinitely many twin-prime pairs. -/
theorem twin_heat_sufficiency (Cbad : ℝ)
    (hbad : ∀ t : ℝ, 0 < t → t ≤ 1 →
      (∑' n : ℕ, if ¬(n.Prime ∧ (n + 2).Prime)
        then twinTerm t n else 0) ≤ Cbad)
    (hdiv : ∀ C : ℝ, ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ C < twinHeat t) :
    {n : ℕ | n.Prime ∧ (n + 2).Prime}.Infinite := by
  rw [← Set.not_finite]
  intro hfin
  obtain ⟨C, hC⟩ := twin_heat_bounded_of_finite Cbad hfin hbad
  obtain ⟨t, ht, ht1, hgt⟩ := hdiv C
  exact absurd (hC t ht ht1) (not_le.mpr hgt)

end NCG
