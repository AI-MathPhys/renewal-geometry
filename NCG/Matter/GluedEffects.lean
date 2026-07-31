/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The glued effect family and its maximum-entropy selection
  (`thm:glued-effect-family`, SM_emergence)

The `Aut(G₂)`-covariant conserved diagonal effects are constant on
the two port orbits of each vertex stabiliser, giving the
two-parameter family; cell-marginal compatibility (or maximum
entropy) selects the uniform point:

* `interface_orbit_normalization` / `private_orbit_normalization` —
  orbit-constant allocations on the five (resp. three) ports sum to
  one, giving `a_I + 4a_L = 1` and `2b_N + b_F = 1`;
* `glued_effect_selection` — cell-marginal equality forces
  `a_I = a_L = 1/5`, `b_N = b_F = 1/3`;
* `tangent_log_inequality` / `entropy_le_log_card` /
  `entropy_eq_log_card_iff` — the finite maximum-entropy principle:
  `Σ -p log p ≤ log n` with equality exactly at the uniform
  distribution — so the selected point is the maximum-entropy
  allocation on every port set.

The identification of the stabiliser port orbits (two orbits of
sizes `1+4` at an interface vertex, `2+1` at a private vertex) is
the declared graph-theoretic input.
-/

namespace NCG

open Real

/-- Interface-stabiliser normalization: an orbit-constant allocation
on the `1 + 4` port orbits sums to one iff `a_I + 4a_L = 1`. -/
theorem interface_orbit_normalization {aI aL : ℝ}
    (alloc : Fin 5 → ℝ)
    (h0 : alloc 0 = aI) (hleg : ∀ i : Fin 5, i ≠ 0 → alloc i = aL)
    (hsum : ∑ i, alloc i = 1) : aI + 4 * aL = 1 := by
  rw [Fin.sum_univ_five, h0, hleg 1 (by decide), hleg 2 (by decide),
    hleg 3 (by decide), hleg 4 (by decide)] at hsum
  linarith

/-- Private-stabiliser normalization: an orbit-constant allocation
on the `2 + 1` port orbits sums to one iff `2b_N + b_F = 1`. -/
theorem private_orbit_normalization {bN bF : ℝ}
    (alloc : Fin 3 → ℝ)
    (h0 : alloc 0 = bN) (h1 : alloc 1 = bN) (h2 : alloc 2 = bF)
    (hsum : ∑ i, alloc i = 1) : 2 * bN + bF = 1 := by
  rw [Fin.sum_univ_three, h0, h1, h2] at hsum
  linarith

/-- `thm:glued-effect-family` (selection): cell-marginal equality
pins the two-parameter family at the uniform point. -/
theorem glued_effect_selection {aI aL bN bF : ℝ}
    (hA : aI + 4 * aL = 1) (hB : 2 * bN + bF = 1)
    (hAeq : aI = aL) (hBeq : bN = bF) :
    aI = 1 / 5 ∧ aL = 1 / 5 ∧ bN = 1 / 3 ∧ bF = 1 / 3 := by
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Tangent inequality for the entropy kernel: for `c > 0` and
`x ≥ 0`, `-x log x ≤ -x log c + c - x`, strictly unless `x = c`. -/
theorem tangent_log_inequality {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) :
    Real.negMulLog x ≤ -(x * Real.log c) + c - x := by
  rcases eq_or_lt_of_le hx with h0 | h0
  · rw [← h0, Real.negMulLog_zero]
    simp
    linarith
  · rw [Real.negMulLog]
    have hlog : Real.log (c / x) ≤ c / x - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hsplit : Real.log (c / x) = Real.log c - Real.log x :=
      Real.log_div hc.ne' h0.ne'
    rw [hsplit] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hx
    have hxne : x ≠ 0 := h0.ne'
    calc -x * Real.log x
        = x * (Real.log c - Real.log x) - x * Real.log c := by ring
    _ ≤ x * (c / x - 1) - x * Real.log c := by linarith [hmul]
    _ = -(x * Real.log c) + c - x := by
          field_simp
          ring

/-- Strictness of the tangent inequality away from `x = c`. -/
theorem tangent_log_strict {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c)
    (hne : x ≠ c) :
    Real.negMulLog x < -(x * Real.log c) + c - x := by
  rcases eq_or_lt_of_le hx with h0 | h0
  · rw [← h0, Real.negMulLog_zero]
    have : (0 : ℝ) ≠ c := by rw [← h0] at hne; exact hne
    simp
    linarith [hc]
  · rw [Real.negMulLog]
    have hratio : c / x ≠ 1 := by
      intro h
      apply hne
      field_simp at h
      linarith
    have hlog : Real.log (c / x) < c / x - 1 :=
      Real.log_lt_sub_one_of_pos (by positivity) hratio
    have hsplit : Real.log (c / x) = Real.log c - Real.log x :=
      Real.log_div hc.ne' h0.ne'
    rw [hsplit] at hlog
    have hmul := mul_lt_mul_of_pos_left hlog h0
    calc -x * Real.log x
        = x * (Real.log c - Real.log x) - x * Real.log c := by ring
    _ < x * (c / x - 1) - x * Real.log c := by linarith [hmul]
    _ = -(x * Real.log c) + c - x := by
          field_simp
          ring

/-- `thm:glued-effect-family` (maximum entropy, bound): on a finite
simplex the Shannon entropy is at most `log n`. -/
theorem entropy_le_log_card {I : Type*} [Fintype I]
    (hcard : 0 < Fintype.card I) (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, Real.negMulLog (p i)) ≤ Real.log (Fintype.card I) := by
  set n : ℝ := (Fintype.card I : ℝ) with hn
  have hnpos : (0 : ℝ) < n := by
    rw [hn]
    exact_mod_cast hcard
  have hpt : ∀ i, Real.negMulLog (p i)
      ≤ -(p i * Real.log (1 / n)) + 1 / n - p i := fun i =>
    tangent_log_inequality (hp i) (by positivity)
  calc (∑ i, Real.negMulLog (p i))
      ≤ ∑ i, (-(p i * Real.log (1 / n)) + 1 / n - p i) :=
        Finset.sum_le_sum fun i _ => hpt i
  _ = -(Real.log (1 / n)) * (∑ i, p i)
        + n * (1 / n) - ∑ i, p i := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        rw [show (∑ i, -(p i * Real.log (1 / n)))
          = -(Real.log (1 / n)) * ∑ i, p i from by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn]
  _ = Real.log n := by
        rw [hsum, Real.log_div one_ne_zero hnpos.ne', Real.log_one]
        field_simp
        ring

/-- `thm:glued-effect-family` (maximum entropy, uniqueness): the
entropy attains `log n` only at the uniform distribution. -/
theorem entropy_eq_log_card_only_uniform {I : Type*} [Fintype I]
    (hcard : 0 < Fintype.card I) (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hmax : (∑ i, Real.negMulLog (p i))
      = Real.log (Fintype.card I)) :
    ∀ i, p i = 1 / (Fintype.card I) := by
  set n : ℝ := (Fintype.card I : ℝ) with hn
  have hnpos : (0 : ℝ) < n := by
    rw [hn]
    exact_mod_cast hcard
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ := hcon
  -- strict inequality at `j`, tangent bound elsewhere
  have hstrict := tangent_log_strict (hp j) (by positivity : (0:ℝ) < 1/n)
    (by rw [hn] at hj ⊢; exact hj)
  have hsum_lt : (∑ i, Real.negMulLog (p i))
      < ∑ i, (-(p i * Real.log (1 / n)) + 1 / n - p i) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact tangent_log_inequality (hp i) (by positivity)
    · exact ⟨j, Finset.mem_univ j, hstrict⟩
  have heval : (∑ i, (-(p i * Real.log (1 / n)) + 1 / n - p i))
      = Real.log n := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [show (∑ i, -(p i * Real.log (1 / n)))
      = -(Real.log (1 / n)) * ∑ i, p i from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum,
      Real.log_div one_ne_zero hnpos.ne', Real.log_one]
    field_simp
    ring
  rw [heval] at hsum_lt
  rw [hmax] at hsum_lt
  exact lt_irrefl _ hsum_lt

end NCG
