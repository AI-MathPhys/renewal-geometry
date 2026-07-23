/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The access functional and its odd fixed points

This file proves the access-selection cluster of the manuscript:

* **Proposition `prop:additive-access-main`** (additive access functional):
  among the three elementary ways of spending a signed budget `e^B` over
  `m` axes, the factored allocation has constant logarithmic access
  (`NCG.factored_access_const`), the replicated allocation runs away
  linearly (`NCG.replicated_access_tendsto_atTop`), and the additive
  allocation has the finite interior optimum
  `∏ Wᵢ ≤ (e^B/m)^m` attained at the isotropic allocation
  (`NCG.additive_allocation_le`, `NCG.additive_allocation_eq`) — the
  maximal logarithmic access is `Acc_m(B) = m(B − log m)`.

* **Lemma `lem:odd-access-fixed-points`**: the access self-consistency
  equation `d = argmax_m Acc_m(d·log 2)` has, among odd positive
  integers, exactly the solutions `d = 1` and `d = 3`
  (`NCG.odd_access_fixed_points`).  In fact every rank `d ≥ 5` — odd or
  not — fails to be a fixed point (`NCG.not_accessFixedPoint_of_five_le`,
  which is also the growth half of
  Proposition `prop:decimation-cannot-access`).

* **Theorem `thm:conditional-access-3plus1`**: under the access
  self-consistency principle, the only spatially nondegenerate odd
  fixed point is `d = 3` (`NCG.conditional_access_selection`).
-/

namespace NCG

open Real Finset

/-- The **additive access functional** `Acc_m(B) = m(B − log m)`
(Proposition `prop:additive-access-main`). -/
noncomputable def accessFn (B : ℝ) (m : ℕ) : ℝ := m * (B - Real.log m)

/-- **Access comparison by rational ratios**: for a budget `log x`,
`Acc_a ≤ Acc_b` reduces to the rational inequality
`x^a·b^b ≤ x^b·a^a`. -/
theorem accessFn_le_accessFn {x : ℝ} (hx : 0 < x) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (h : x ^ a * (b : ℝ) ^ b ≤ x ^ b * (a : ℝ) ^ a) :
    accessFn (Real.log x) a ≤ accessFn (Real.log x) b := by
  have ha' : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hb' : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hxa : (0:ℝ) < x ^ a := pow_pos hx a
  have hxb : (0:ℝ) < x ^ b := pow_pos hx b
  have haa : (0:ℝ) < (a:ℝ) ^ a := pow_pos ha' a
  have hbb : (0:ℝ) < (b:ℝ) ^ b := pow_pos hb' b
  have hlog := Real.log_le_log (by positivity) h
  rw [Real.log_mul hxa.ne' hbb.ne', Real.log_mul hxb.ne' haa.ne',
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  unfold accessFn
  nlinarith [hlog]

/-- Strict version of the ratio comparison. -/
theorem accessFn_lt_accessFn {x : ℝ} (hx : 0 < x) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (h : x ^ a * (b : ℝ) ^ b < x ^ b * (a : ℝ) ^ a) :
    accessFn (Real.log x) a < accessFn (Real.log x) b := by
  have ha' : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hb' : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hxa : (0:ℝ) < x ^ a := pow_pos hx a
  have hxb : (0:ℝ) < x ^ b := pow_pos hx b
  have haa : (0:ℝ) < (a:ℝ) ^ a := pow_pos ha' a
  have hbb : (0:ℝ) < (b:ℝ) ^ b := pow_pos hb' b
  have hlog := Real.log_lt_log (by positivity) h
  rw [Real.log_mul hxa.ne' hbb.ne', Real.log_mul hxb.ne' haa.ne',
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  unfold accessFn
  nlinarith [hlog]

/-- **Access self-consistency** (Principle
`prin:access-self-consistency`): the realised rank `d` maximises the
access functional at its own signed budget `B = d·log 2`. -/
def IsAccessFixedPoint (d : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    accessFn (d * Real.log 2) m ≤ accessFn (d * Real.log 2) d

/-- `d = 1` is an access fixed point: with budget `log 2`, every
allocation over `m ≥ 2` axes has nonpositive access. -/
theorem isAccessFixedPoint_one : IsAccessFixedPoint 1 := by
  intro m hm
  have hcast : ((1:ℕ):ℝ) * Real.log 2 = Real.log 2 := by norm_num
  rw [hcast]
  have hval : accessFn (Real.log 2) 1 = Real.log 2 := by
    simp [accessFn]
  rcases eq_or_lt_of_le hm with h1 | h2
  · rw [← h1]
  · have hm2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast h2
    have hle : Real.log 2 ≤ Real.log m :=
      Real.log_le_log (by norm_num) hm2
    have h2' : accessFn (Real.log 2) m ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have h3 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [hval]
    linarith

/-- `d = 3` is an access fixed point: with budget `3·log 2 = log 8` the
integer maximiser of `m ↦ m(log 8 − log m)` is `m = 3` (the continuous
optimum is `8/e ≈ 2.94`). -/
theorem isAccessFixedPoint_three : IsAccessFixedPoint 3 := by
  intro m hm
  have hcast : ((3:ℕ):ℝ) * Real.log 2 = Real.log 8 := by
    rw [show (8:ℝ) = 2 ^ (3:ℕ) by norm_num, Real.log_pow]
  rw [hcast]
  rcases le_or_gt m 7 with hm7 | hm8
  · interval_cases m
    · exact accessFn_le_accessFn (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
    · exact accessFn_le_accessFn (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
    · exact le_refl _
    · exact accessFn_le_accessFn (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
    · exact accessFn_le_accessFn (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
    · exact accessFn_le_accessFn (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
    · exact accessFn_le_accessFn (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
  · have hm8' : (8:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm8
    have h1 : Real.log 8 ≤ Real.log m :=
      Real.log_le_log (by norm_num) hm8'
    have h2 : accessFn (Real.log 8) m ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have h3 : Real.log 3 < Real.log 8 :=
      Real.log_lt_log (by norm_num) (by norm_num)
    have h4 : (0:ℝ) < accessFn (Real.log 8) 3 := by
      unfold accessFn
      push_cast
      nlinarith
    linarith

/-- Auxiliary growth bound: `2m + 5 ≤ 2^{m+1}` from `m = 3` on. -/
theorem two_mul_add_five_le_two_pow {m : ℕ} (hm : 3 ≤ m) :
    2 * m + 5 ≤ 2 ^ (m + 1) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have h2 : 2 ^ (n + 1) + 2 ≤ 2 ^ (n + 2) := by
        have : (2:ℕ) ≤ 2 ^ (n + 1) := Nat.one_lt_two_pow_iff.mpr (by omega)
        calc 2 ^ (n + 1) + 2 ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := by omega
          _ = 2 ^ (n + 2) := by ring
      omega

/-- Auxiliary growth bound: `(e+2)² ≤ 2^{e+1}` from `e = 5` on. -/
theorem sq_add_two_le_two_pow {e : ℕ} (he : 5 ≤ e) :
    (e + 2) ^ 2 ≤ 2 ^ (e + 1) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hlin : 2 * n + 5 ≤ 2 ^ (n + 1) :=
        two_mul_add_five_le_two_pow (by omega)
      have hexp : 2 ^ (n + 2) = 2 ^ (n + 1) + 2 ^ (n + 1) := by ring
      nlinarith

/-- **No rank `d ≥ 5` is an access fixed point** (the refutation half of
Lemma `lem:odd-access-fixed-points`, and the growth half of Proposition
`prop:decimation-cannot-access`): at budget `d·log 2` the allocation over
`m = 2^{d−2}` axes strictly beats the diagonal `m = d`. -/
theorem not_accessFixedPoint_of_five_le {d : ℕ} (hd : 5 ≤ d) :
    ¬IsAccessFixedPoint d := by
  intro hfix
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have he3 : 3 ≤ e := by omega
  have hwitness := hfix (2 ^ e) Nat.one_le_two_pow
  -- the witness access is `2^{e+1}·log 2`
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hw : accessFn ((e + 2 : ℕ) * Real.log 2) (2 ^ e)
      = 2 ^ (e + 1) * Real.log 2 := by
    unfold accessFn
    rw [show (((2:ℕ) ^ e : ℕ) : ℝ) = (2:ℝ) ^ e by push_cast; ring,
      Real.log_pow]
    push_cast
    ring
  -- the diagonal access is strictly below `(e+2)²·log 2 ≤ 2^{e+1}·log 2`
  have hlogd : (0:ℝ) < Real.log ((e:ℝ) + 2) := by
    apply Real.log_pos
    have : (3:ℝ) ≤ (e:ℝ) := by exact_mod_cast he3
    linarith
  have hdiag : accessFn ((e + 2 : ℕ) * Real.log 2) (e + 2)
      < ((e:ℝ) + 2) ^ 2 * Real.log 2 := by
    unfold accessFn
    push_cast
    nlinarith
  rcases lt_or_ge e 5 with he5 | he5
  · -- `d = 5` and `d = 6`: explicit rational witness comparisons
    interval_cases e
    · -- `d = 5`: `32^5·8^8 < 32^8·5^5`
      have h32 : ((5:ℕ):ℝ) * Real.log 2 = Real.log 32 := by
        rw [show (32:ℝ) = 2 ^ (5:ℕ) by norm_num, Real.log_pow]
      have hlt : accessFn (Real.log 32) 5 < accessFn (Real.log 32) 8 :=
        accessFn_lt_accessFn (by norm_num) (by norm_num) (by norm_num)
          (by norm_num)
      have hwitness' := hfix 8 (by norm_num)
      rw [show ((3:ℕ) + 2) = 5 from rfl, h32] at hwitness'
      exact absurd hwitness' (not_le.mpr hlt)
    · -- `d = 6`: `64^6·16^16 < 64^16·6^6`
      have h64 : ((6:ℕ):ℝ) * Real.log 2 = Real.log 64 := by
        rw [show (64:ℝ) = 2 ^ (6:ℕ) by norm_num, Real.log_pow]
      have hlt : accessFn (Real.log 64) 6 < accessFn (Real.log 64) 16 :=
        accessFn_lt_accessFn (by norm_num) (by norm_num) (by norm_num)
          (by norm_num)
      have hwitness' := hfix 16 (by norm_num)
      rw [show ((4:ℕ) + 2) = 6 from rfl, h64] at hwitness'
      exact absurd hwitness' (not_le.mpr hlt)
  · -- `d ≥ 7`: the witness `m = 2^{d−2}` wins via `(e+2)² ≤ 2^{e+1}`
    have hsq : ((e:ℝ) + 2) ^ 2 ≤ (2:ℝ) ^ (e + 1) := by
      have h := sq_add_two_le_two_pow he5
      have h' : (((e + 2) ^ 2 : ℕ) : ℝ) ≤ ((2 ^ (e + 1) : ℕ) : ℝ) := by
        exact_mod_cast h
      push_cast at h'
      linarith
    have : accessFn ((e + 2 : ℕ) * Real.log 2) (e + 2)
        < accessFn ((e + 2 : ℕ) * Real.log 2) (2 ^ e) := by
      rw [hw]
      nlinarith [hdiag, mul_le_mul_of_nonneg_right hsq hlog2.le]
    exact absurd hwitness (not_le.mpr this)

/-- **Lemma `lem:odd-access-fixed-points`**: among odd positive ranks,
the access self-consistency equation has exactly the solutions `d = 1`
and `d = 3`. -/
theorem odd_access_fixed_points {d : ℕ} (hodd : Odd d) (hpos : 0 < d) :
    IsAccessFixedPoint d ↔ d = 1 ∨ d = 3 := by
  constructor
  · intro hfix
    by_contra hne
    push Not at hne
    have hd5 : 5 ≤ d := by
      obtain ⟨k, rfl⟩ := hodd
      omega
    exact not_accessFixedPoint_of_five_le hd5 hfix
  · rintro (rfl | rfl)
    · exact isAccessFixedPoint_one
    · exact isAccessFixedPoint_three

/-- **Theorem `thm:conditional-access-3plus1`** (conditional access
selection): a primitive (odd-rank) access-self-consistent endpoint that
is spatially nondegenerate (`d ≠ 1`) is exactly the `3+1` endpoint. -/
theorem conditional_access_selection {d : ℕ} (hodd : Odd d) (hpos : 0 < d)
    (hfix : IsAccessFixedPoint d) (hnondeg : d ≠ 1) : d = 3 :=
  ((odd_access_fixed_points hodd hpos).mp hfix).resolve_left hnondeg

/-! ### The three allocation modes (Proposition `prop:additive-access-main`) -/

/-- **Factored allocation has constant access**: if `∏ Wᵢ = e^B` then the
logarithmic access is `B`, independent of `m`. -/
theorem factored_access_const {m : ℕ} (B : ℝ) (W : Fin m → ℝ)
    (hprod : ∏ i, W i = Real.exp B) :
    Real.log (∏ i, W i) = B := by
  rw [hprod, Real.log_exp]

/-- **Replicated allocation runs away**: the access `m·B` of the
replicated allocation tends to infinity with `m` for any positive
budget. -/
theorem replicated_access_tendsto_atTop {B : ℝ} (hB : 0 < B) :
    Filter.Tendsto (fun m : ℕ => (m:ℝ) * B) Filter.atTop Filter.atTop :=
  Filter.Tendsto.atTop_mul_const hB tendsto_natCast_atTop_atTop

/-- **The additive allocation optimum** (AM–GM): under the additive
budget constraint the access product is maximised by the isotropic
allocation, `∏ Wᵢ ≤ ((∑ Wᵢ)/m)^m`.  Taking `∑ Wᵢ = e^B` and logarithms
gives the maximal access `Acc_m(B) = m(B − log m)` of Proposition
`prop:additive-access-main`. -/
theorem additive_allocation_le {m : ℕ} (hm : 0 < m) (W : Fin m → ℝ)
    (hW : ∀ i, 0 ≤ W i) :
    ∏ i, W i ≤ ((∑ i, W i) / m) ^ m := by
  have hm' : ((m:ℕ):ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ => 1 / (m:ℝ)) W (fun i _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        field_simp)
    (fun i _ => hW i)
  have hA : ∑ i, (1 / (m:ℝ)) * W i = (∑ i, W i) / m := by
    rw [← Finset.mul_sum]
    ring
  have hprodpow : (∏ i, W i ^ (1 / (m:ℝ))) ^ m = ∏ i, W i := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_natCast (W i ^ (1 / (m:ℝ))) m,
      ← Real.rpow_mul (hW i)]
    rw [one_div, inv_mul_cancel₀ hm', Real.rpow_one]
  calc ∏ i, W i = (∏ i, W i ^ (1 / (m:ℝ))) ^ m := hprodpow.symm
    _ ≤ ((∑ i, W i) / m) ^ m := by
        apply pow_le_pow_left₀
          (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hW i) _)
        rw [← hA]
        exact h

/-- The additive optimum is attained at the isotropic allocation. -/
theorem additive_allocation_eq {m : ℕ} (S : ℝ) :
    ∏ _i : Fin m, (S / m) = (S / m) ^ m := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end NCG
