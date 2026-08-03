/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Binary-Goldbach heat sufficiency
  (`thm:Goldbach-heat-master`, flagship manuscript)

For the finite heat selector
`𝓗_N(t) = Σ_{0<m<N} Λ(m)Λ(N-m)/√(m(N-m)) e^{-t[(log m)²+(log(N-m))²]}`:

* the endpoint-packing estimate: for any `S ⊆ (0,N)`,
  `Σ_{m∈S} 1/√(m(N-m)) ≤ 6√|S|/√N`
  (`sum_inv_sqrt_pair_le`), from the `K`-smallest rearrangement
  bound `Σ_{m∈S} 1/√m ≤ 2√|S|` (`sum_inv_sqrt_le`, by removing
  the maximum and telescoping `1/√K ≤ 2(√K - √(K-1))`);
* the proper-prime-power count: at most `(√N+1)(log₂N+1)` proper
  prime powers lie in `(0,N)` (`proper_prime_pow_card_le`, by the
  injection `m = p^k ↦ (p,k)` with `p ≤ √N`, `k ≤ log₂ N`);
* the contamination bound (`goldbach_heat_contamination`): pairs
  with a proper-prime-power summand contribute at most
  `(log N)²·6·√(2(√N+1)(log₂N+1))/√N`;
* the boxed sufficiency (`goldbach_heat_sufficiency`): a lower
  bound `𝓗_N(t) ≥ c` exceeding the contamination forces a
  representation of `N` with both summands prime.

Rendering disclosed: the crude prime-power count carries an extra
half power of `log N` against the manuscript's Chebyshev-type
`O(√N)`, so the contamination reads `O(N^{-1/4}(log N)^{5/2})`
rather than `O(N^{-1/4}(log N)²)`; the box is otherwise exact and
the sufficiency clause is unaffected, since the contamination
still tends to zero.
-/

open Finset ArithmeticFunction

namespace NCG

/-- The binary-Goldbach heat selector (a finite sum). -/
noncomputable def goldbachHeat (N : ℕ) (t : ℝ) : ℝ :=
  ∑ m ∈ Finset.Ioo 0 N,
    Λ m * Λ (N - m) / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
      * Real.exp (-t * (Real.log m ^ 2
        + Real.log ((N : ℝ) - m) ^ 2))

/-- The contaminated pairs: at least one summand is a proper
prime power. -/
noncomputable def goldbachBad (N : ℕ) : Finset ℕ :=
  (Finset.Ioo 0 N).filter fun m =>
    (IsPrimePow m ∧ ¬ m.Prime)
      ∨ (IsPrimePow (N - m) ∧ ¬ (N - m).Prime)

/-- Rearrangement bound: any `K` distinct positive integers give
`Σ 1/√m ≤ 2√K`. -/
theorem sum_inv_sqrt_le (K : ℕ) :
    ∀ S : Finset ℕ, 0 ∉ S → S.card = K →
      ∑ m ∈ S, 1 / Real.sqrt m ≤ 2 * Real.sqrt K := by
  induction K with
  | zero =>
      intro S _ hc
      rw [Finset.card_eq_zero.mp hc]
      simp
  | succ n ih =>
      intro S h0 hc
      have hne : S.Nonempty := by
        rw [← Finset.card_pos, hc]
        omega
      set m₀ := S.max' hne with hm₀_def
      have hm₀ : m₀ ∈ S := S.max'_mem hne
      have hsub : S ⊆ Finset.Icc 1 m₀ := by
        intro x hx
        rw [Finset.mem_Icc]
        refine ⟨?_, S.le_max' x hx⟩
        rcases Nat.eq_zero_or_pos x with h | h
        · exact absurd (h ▸ hx) h0
        · omega
      have hcard : n + 1 ≤ m₀ := by
        have h1 := Finset.card_le_card hsub
        rw [hc, Nat.card_Icc] at h1
        omega
      have hstep := ih (S.erase m₀)
        (fun h => h0 (Finset.mem_of_mem_erase h))
        (by rw [Finset.card_erase_of_mem hm₀, hc]; rfl)
      rw [← Finset.sum_erase_add S _ hm₀]
      have h1 : 1 / Real.sqrt m₀
          ≤ 1 / Real.sqrt ((n : ℝ) + 1) := by
        refine one_div_le_one_div_of_le
          (Real.sqrt_pos.mpr (by positivity)) ?_
        refine Real.sqrt_le_sqrt ?_
        exact_mod_cast hcard
      have hposn1 : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) :=
        Real.sqrt_pos.mpr (by positivity)
      have hsqn := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ n)
      have hsqn1 := Real.sq_sqrt
        (by positivity : (0:ℝ) ≤ (n : ℝ) + 1)
      have h2 : 1 / Real.sqrt ((n : ℝ) + 1)
          ≤ 2 * Real.sqrt ((n : ℝ) + 1)
            - 2 * Real.sqrt (n : ℝ) := by
        rw [div_le_iff₀ hposn1]
        nlinarith [Real.sqrt_nonneg (n : ℝ),
          Real.sqrt_nonneg ((n : ℝ) + 1),
          sq_nonneg (Real.sqrt (n : ℝ)
            - Real.sqrt ((n : ℝ) + 1))]
      have hfin : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by
        push_cast
        ring
      rw [hfin]
      calc ∑ m ∈ S.erase m₀, 1 / Real.sqrt m
            + 1 / Real.sqrt m₀
          ≤ 2 * Real.sqrt (n : ℝ)
            + 1 / Real.sqrt ((n : ℝ) + 1) :=
            add_le_add hstep h1
        _ ≤ 2 * Real.sqrt ((n : ℝ) + 1) := by linarith

/-- Endpoint-packing estimate for the Goldbach kernel. -/
theorem sum_inv_sqrt_pair_le (N : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioo 0 N) :
    ∑ m ∈ S, 1 / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
      ≤ 6 * Real.sqrt S.card / Real.sqrt N := by
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · have hSempty : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have h1 := hS hx
      rw [hN0] at h1
      simp at h1
    rw [hSempty]
    simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  set B : ℝ := 1 / Real.sqrt ((N : ℝ) / 2) with hB_def
  have hB0 : 0 ≤ B := by positivity
  have hkernel : ∀ m ∈ S,
      (1 : ℝ) ≤ m ∧ (m : ℝ) < N := by
    intro m hm
    have h1 := Finset.mem_Ioo.mp (hS hm)
    constructor
    · exact_mod_cast h1.1
    · exact_mod_cast h1.2
  -- split at N/2
  rw [← Finset.sum_filter_add_sum_filter_not S
    (fun m => 2 * m ≤ N)]
  set S₁ := S.filter (fun m => 2 * m ≤ N) with hS₁
  set S₂ := S.filter (fun m => ¬ 2 * m ≤ N) with hS₂
  -- lower half
  have hb₁ : ∑ m ∈ S₁, 1 / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
      ≤ B * (2 * Real.sqrt S.card) := by
    have hterm : ∀ m ∈ S₁,
        1 / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
        ≤ B * (1 / Real.sqrt m) := by
      intro m hm
      have hmf := Finset.mem_filter.mp hm
      obtain ⟨hm1, hmN⟩ := hkernel m hmf.1
      have hm2 : (2 : ℝ) * m ≤ N := by exact_mod_cast hmf.2
      have hlow : (N : ℝ) / 2 ≤ (N : ℝ) - m := by linarith
      have h2 : Real.sqrt ((m : ℝ) * ((N : ℝ) / 2))
          ≤ Real.sqrt ((m : ℝ) * ((N : ℝ) - m)) :=
        Real.sqrt_le_sqrt
          (mul_le_mul_of_nonneg_left hlow (by linarith))
      have h3 : (0 : ℝ)
          < Real.sqrt ((m : ℝ) * ((N : ℝ) / 2)) :=
        Real.sqrt_pos.mpr (by positivity)
      refine le_trans (one_div_le_one_div_of_le h3 h2) ?_
      rw [Real.sqrt_mul (by linarith), hB_def,
        ← one_div_mul_one_div]
      rw [mul_comm]
    calc ∑ m ∈ S₁, 1 / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
        ≤ ∑ m ∈ S₁, B * (1 / Real.sqrt m) :=
          Finset.sum_le_sum hterm
      _ = B * ∑ m ∈ S₁, 1 / Real.sqrt m := by
          rw [Finset.mul_sum]
      _ ≤ B * (2 * Real.sqrt S₁.card) := by
          refine mul_le_mul_of_nonneg_left ?_ hB0
          refine sum_inv_sqrt_le S₁.card S₁ ?_ rfl
          intro h0
          have := (hkernel 0 (Finset.filter_subset _ _ h0)).1
          norm_num at this
      _ ≤ B * (2 * Real.sqrt S.card) := by
          refine mul_le_mul_of_nonneg_left ?_ hB0
          have h4 : (S₁.card : ℝ) ≤ S.card := by
            exact_mod_cast Finset.card_filter_le _ _
          nlinarith [Real.sqrt_le_sqrt h4,
            Real.sqrt_nonneg (S₁.card : ℝ)]
  -- upper half, reindexed by m ↦ N - m
  have hb₂ : ∑ m ∈ S₂, 1 / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
      ≤ B * (2 * Real.sqrt S.card) := by
    have hterm : ∀ m ∈ S₂,
        1 / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
        ≤ B * (1 / Real.sqrt ((N - m : ℕ) : ℝ)) := by
      intro m hm
      have hmf := Finset.mem_filter.mp hm
      obtain ⟨hm1, hmN⟩ := hkernel m hmf.1
      have hm2 : ¬ (2 * m ≤ N) := hmf.2
      have hmhalf : (N : ℝ) / 2 ≤ m := by
        have h5 : N < 2 * m := lt_of_not_ge hm2
        have h6 : (N : ℝ) < 2 * m := by exact_mod_cast h5
        linarith
      have hcast : ((N - m : ℕ) : ℝ) = (N : ℝ) - m := by
        have h7 := Finset.mem_Ioo.mp (hS hmf.1)
        exact_mod_cast Nat.cast_sub h7.2.le
      have hNm : (0 : ℝ) < (N : ℝ) - m := by linarith
      have h2 : Real.sqrt (((N : ℝ) / 2) * ((N : ℝ) - m))
          ≤ Real.sqrt ((m : ℝ) * ((N : ℝ) - m)) :=
        Real.sqrt_le_sqrt
          (mul_le_mul_of_nonneg_right hmhalf hNm.le)
      have h3 : (0 : ℝ)
          < Real.sqrt (((N : ℝ) / 2) * ((N : ℝ) - m)) :=
        Real.sqrt_pos.mpr (by positivity)
      refine le_trans (one_div_le_one_div_of_le h3 h2) ?_
      rw [Real.sqrt_mul (by positivity), hB_def,
        ← one_div_mul_one_div, hcast]
    calc ∑ m ∈ S₂, 1 / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
        ≤ ∑ m ∈ S₂, B * (1 / Real.sqrt ((N - m : ℕ) : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = B * ∑ m ∈ S₂, 1 / Real.sqrt ((N - m : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ B * (2 * Real.sqrt S.card) := by
          refine mul_le_mul_of_nonneg_left ?_ hB0
          have hinj : Set.InjOn (fun m => N - m) S₂ := by
            intro a ha b hb hab
            have haIoo := Finset.mem_Ioo.mp
              (hS (Finset.filter_subset _ _ ha))
            have hbIoo := Finset.mem_Ioo.mp
              (hS (Finset.filter_subset _ _ hb))
            simp only at hab
            omega
          have himg := Finset.sum_image
            (f := fun x : ℕ => 1 / Real.sqrt (x : ℝ))
            (g := fun m => N - m) (s := S₂) hinj
          rw [← himg]
          have h0img : 0 ∉ S₂.image (fun m => N - m) := by
            intro h0
            obtain ⟨m, hm, hm0⟩ := Finset.mem_image.mp h0
            have := Finset.mem_Ioo.mp
              (hS (Finset.filter_subset _ _ hm))
            omega
          have hcardimg := Finset.card_image_of_injOn hinj
          refine le_trans (sum_inv_sqrt_le _ _ h0img rfl) ?_
          rw [hcardimg]
          have h4 : (S₂.card : ℝ) ≤ S.card := by
            exact_mod_cast Finset.card_filter_le _ _
          nlinarith [Real.sqrt_le_sqrt h4,
            Real.sqrt_nonneg (S₂.card : ℝ)]
  -- combine and compare constants
  have hfinal : B * (2 * Real.sqrt S.card)
      + B * (2 * Real.sqrt S.card)
      ≤ 6 * Real.sqrt S.card / Real.sqrt N := by
    have h16 : (4 : ℝ) * Real.sqrt N = Real.sqrt (16 * N) := by
      rw [show (16 : ℝ) * N = 4 ^ 2 * N by ring,
        Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num)]
    have h18 : (6 : ℝ) * Real.sqrt ((N : ℝ) / 2)
        = Real.sqrt (18 * N) := by
      rw [show (18 : ℝ) * N = 6 ^ 2 * ((N : ℝ) / 2) by ring,
        Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num)]
    have hcmp : Real.sqrt (16 * (N : ℝ))
        ≤ Real.sqrt (18 * N) :=
      Real.sqrt_le_sqrt (by linarith)
    have hB6 : 4 * B ≤ 6 / Real.sqrt N := by
      rw [hB_def, mul_one_div, div_le_div_iff₀
        (Real.sqrt_pos.mpr (by positivity))
        (Real.sqrt_pos.mpr hNr)]
      calc 4 * Real.sqrt N = Real.sqrt (16 * N) := h16
        _ ≤ Real.sqrt (18 * N) := hcmp
        _ = 6 * Real.sqrt ((N : ℝ) / 2) := h18.symm
    have hs0 : (0 : ℝ) ≤ Real.sqrt S.card :=
      Real.sqrt_nonneg _
    calc B * (2 * Real.sqrt S.card)
        + B * (2 * Real.sqrt S.card)
        = (4 * B) * Real.sqrt S.card := by ring
      _ ≤ (6 / Real.sqrt N) * Real.sqrt S.card :=
          mul_le_mul_of_nonneg_right hB6 hs0
      _ = 6 * Real.sqrt S.card / Real.sqrt N := by ring
  linarith [hb₁, hb₂]

/-- Proper-prime-power count in `(0,N)`, by the injection
`m = p^k ↦ (p,k)`. -/
theorem proper_prime_pow_card_le (N : ℕ) :
    ((Finset.Ioo 0 N).filter
      (fun m => IsPrimePow m ∧ ¬ m.Prime)).card
      ≤ (Nat.sqrt N + 1) * (Nat.log 2 N + 1) := by
  classical
  refine le_trans (Finset.card_le_card_of_injOn
    (t := (Finset.Icc 0 (Nat.sqrt N))
      ×ˢ (Finset.Icc 0 (Nat.log 2 N)))
    (fun m : ℕ =>
      (Nat.minFac m, Nat.factorization m (Nat.minFac m)))
    ?_ ?_)
    (by rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc]; simp)
  · intro m hm
    have h2 := Finset.mem_filter.mp hm
    have hmIoo := Finset.mem_Ioo.mp h2.1
    have hpp : IsPrimePow m := h2.2.1
    have hnp : ¬ m.Prime := h2.2.2
    have hm1 : m ≠ 1 := hpp.one_lt.ne'
    have hp : m.minFac.Prime := Nat.minFac_prime hm1
    have hpk : m.minFac ^ m.factorization m.minFac = m :=
      hpp.minFac_pow_factorization_eq
    have hk2 : 2 ≤ m.factorization m.minFac := by
      rcases Nat.lt_or_ge (m.factorization m.minFac) 2
        with hk | hk
      · have hcase : m.factorization m.minFac = 0
            ∨ m.factorization m.minFac = 1 := by omega
        rcases hcase with h | h
        · rw [h, pow_zero] at hpk
          exact absurd hpk.symm hm1
        · rw [h, pow_one] at hpk
          exact absurd (hpk ▸ hp) hnp
      · exact hk
    simp only [Finset.coe_product, Set.mem_prod,
      Finset.mem_coe, Finset.mem_Icc]
    refine ⟨⟨Nat.zero_le _, ?_⟩, Nat.zero_le _, ?_⟩
    · refine Nat.le_sqrt.mpr ?_
      calc m.minFac * m.minFac = m.minFac ^ 2 := (sq _).symm
        _ ≤ m.minFac ^ m.factorization m.minFac :=
          Nat.pow_le_pow_right hp.one_lt.le hk2
        _ = m := hpk
        _ ≤ N := hmIoo.2.le
    · refine (Nat.le_log_iff_pow_le (by norm_num) ?_).mpr ?_
      · omega
      · calc 2 ^ m.factorization m.minFac
            ≤ m.minFac ^ m.factorization m.minFac :=
            Nat.pow_le_pow_left hp.two_le _
          _ = m := hpk
          _ ≤ N := hmIoo.2.le
  · intro m₁ h₁ m₂ h₂ heq
    have hpp₁ : IsPrimePow m₁ := (Finset.mem_filter.mp h₁).2.1
    have hpp₂ : IsPrimePow m₂ := (Finset.mem_filter.mp h₂).2.1
    have e₁ := hpp₁.minFac_pow_factorization_eq
    have e₂ := hpp₂.minFac_pow_factorization_eq
    rw [Prod.mk.injEq] at heq
    rw [← e₁, ← e₂, heq.2, heq.1]

/-- Count of contaminated pairs. -/
theorem goldbachBad_card_le (N : ℕ) :
    (goldbachBad N).card
      ≤ 2 * ((Nat.sqrt N + 1) * (Nat.log 2 N + 1)) := by
  classical
  rw [goldbachBad, Finset.filter_or]
  refine le_trans (Finset.card_union_le _ _) ?_
  have hA := proper_prime_pow_card_le N
  have hB : ((Finset.Ioo 0 N).filter
      (fun m => IsPrimePow (N - m) ∧ ¬ (N - m).Prime)).card
      ≤ (Nat.sqrt N + 1) * (Nat.log 2 N + 1) := by
    refine le_trans (Finset.card_le_card_of_injOn
      (fun m => N - m) ?_ ?_) hA
    · intro m hm
      have h2 := Finset.mem_filter.mp hm
      have hmIoo := Finset.mem_Ioo.mp h2.1
      refine Finset.mem_filter.mpr ⟨?_, h2.2⟩
      simp only [Finset.mem_Ioo]
      have h3 := h2.2.1.one_lt
      obtain ⟨hm0, hmN⟩ := hmIoo
      omega
    · intro a ha b hb hab
      have haIoo := Finset.mem_Ioo.mp
        (Finset.mem_filter.mp ha).1
      have hbIoo := Finset.mem_Ioo.mp
        (Finset.mem_filter.mp hb).1
      simp only at hab
      omega
  omega

/-- The contamination bound: contaminated pairs contribute at
most `(log N)²·6·√(2(√N+1)(log₂N+1))/√N`. -/
theorem goldbach_heat_contamination (N : ℕ) (t : ℝ)
    (ht : 0 ≤ t) :
    ∑ m ∈ goldbachBad N,
      Λ m * Λ (N - m) / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
        * Real.exp (-t * (Real.log m ^ 2
          + Real.log ((N : ℝ) - m) ^ 2))
      ≤ Real.log N ^ 2
        * (6 * Real.sqrt (2 * ((Nat.sqrt N + 1)
            * (Nat.log 2 N + 1))) / Real.sqrt N) := by
  classical
  have hsub : goldbachBad N ⊆ Finset.Ioo 0 N :=
    Finset.filter_subset _ _
  have hterm : ∀ m ∈ goldbachBad N,
      Λ m * Λ (N - m) / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
        * Real.exp (-t * (Real.log m ^ 2
          + Real.log ((N : ℝ) - m) ^ 2))
      ≤ Real.log N ^ 2
        * (1 / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))) := by
    intro m hm
    have hmIoo := Finset.mem_Ioo.mp (hsub hm)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmIoo.1
    have hmN : (m : ℝ) < N := by exact_mod_cast hmIoo.2
    have hNm1 : (1 : ℝ) ≤ (N : ℝ) - m := by
      have h1 : (m : ℝ) + 1 ≤ N := by exact_mod_cast hmIoo.2
      linarith
    have hsq : (0 : ℝ)
        < Real.sqrt ((m : ℝ) * ((N : ℝ) - m)) :=
      Real.sqrt_pos.mpr (by nlinarith)
    have hcast : ((N - m : ℕ) : ℝ) = (N : ℝ) - m := by
      exact_mod_cast Nat.cast_sub hmIoo.2.le
    have hΛ1 : Λ m ≤ Real.log N := by
      refine le_trans vonMangoldt_le_log ?_
      refine Real.log_le_log (by linarith) ?_
      linarith
    have hΛ2 : Λ (N - m) ≤ Real.log N := by
      refine le_trans vonMangoldt_le_log ?_
      rw [hcast]
      refine Real.log_le_log (by linarith) ?_
      linarith
    have hexp : Real.exp (-t * (Real.log m ^ 2
        + Real.log ((N : ℝ) - m) ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h2 : (0 : ℝ) ≤ Real.log m ^ 2
          + Real.log ((N : ℝ) - m) ^ 2 := by positivity
      nlinarith
    have hΛ1n : (0 : ℝ) ≤ Λ m := vonMangoldt_nonneg
    have hΛ2n : (0 : ℝ) ≤ Λ (N - m) := vonMangoldt_nonneg
    calc Λ m * Λ (N - m)
          / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
          * Real.exp (-t * (Real.log m ^ 2
            + Real.log ((N : ℝ) - m) ^ 2))
        ≤ Λ m * Λ (N - m)
          / Real.sqrt ((m : ℝ) * ((N : ℝ) - m)) * 1 := by
          refine mul_le_mul_of_nonneg_left hexp ?_
          positivity
      _ = Λ m * Λ (N - m)
          / Real.sqrt ((m : ℝ) * ((N : ℝ) - m)) :=
          mul_one _
      _ ≤ Real.log N * Real.log N
          / Real.sqrt ((m : ℝ) * ((N : ℝ) - m)) := by
          gcongr
      _ = Real.log N ^ 2
          * (1 / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))) := by
          rw [pow_two]
          ring
  calc ∑ m ∈ goldbachBad N,
      Λ m * Λ (N - m) / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
        * Real.exp (-t * (Real.log m ^ 2
          + Real.log ((N : ℝ) - m) ^ 2))
      ≤ ∑ m ∈ goldbachBad N, Real.log N ^ 2
          * (1 / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))) :=
        Finset.sum_le_sum hterm
    _ = Real.log N ^ 2 * ∑ m ∈ goldbachBad N,
          1 / Real.sqrt ((m : ℝ) * ((N : ℝ) - m)) := by
        rw [Finset.mul_sum]
    _ ≤ Real.log N ^ 2
        * (6 * Real.sqrt (goldbachBad N).card
          / Real.sqrt N) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact sum_inv_sqrt_pair_le N _ hsub
    _ ≤ Real.log N ^ 2
        * (6 * Real.sqrt (2 * ((Nat.sqrt N + 1)
            * (Nat.log 2 N + 1))) / Real.sqrt N) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h1 : ((goldbachBad N).card : ℝ)
            ≤ 2 * (((Nat.sqrt N : ℝ) + 1)
              * ((Nat.log 2 N : ℝ) + 1)) := by
          exact_mod_cast goldbachBad_card_le N
        gcongr

/-- `thm:Goldbach-heat-master`, boxed sufficiency: a heat value
exceeding the contamination forces a two-prime representation. -/
theorem goldbach_heat_sufficiency (N : ℕ) (t c : ℝ)
    (ht : 0 ≤ t)
    (hc : Real.log N ^ 2
      * (6 * Real.sqrt (2 * ((Nat.sqrt N + 1)
          * (Nat.log 2 N + 1))) / Real.sqrt N) < c)
    (hheat : c ≤ goldbachHeat N t) :
    ∃ m, 0 < m ∧ m < N ∧ m.Prime ∧ (N - m).Prime := by
  classical
  by_contra hno
  have hno' : ∀ m, 0 < m → m < N →
      ¬ (m.Prime ∧ (N - m).Prime) := by
    intro m h1 h2 h3
    exact hno ⟨m, h1, h2, h3.1, h3.2⟩
  have hzero : ∀ m ∈ Finset.Ioo 0 N, m ∉ goldbachBad N →
      Λ m * Λ (N - m) / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
        * Real.exp (-t * (Real.log m ^ 2
          + Real.log ((N : ℝ) - m) ^ 2)) = 0 := by
    intro m hm hbad
    have hmIoo := Finset.mem_Ioo.mp hm
    have hnb : ¬ ((IsPrimePow m ∧ ¬ m.Prime)
        ∨ (IsPrimePow (N - m) ∧ ¬ (N - m).Prime)) := by
      intro h
      exact hbad (Finset.mem_filter.mpr ⟨hm, h⟩)
    by_cases hΛ1 : Λ m = 0
    · rw [hΛ1]
      simp
    by_cases hΛ2 : Λ (N - m) = 0
    · rw [hΛ2]
      simp
    have hpp1 : IsPrimePow m := vonMangoldt_ne_zero_iff.mp hΛ1
    have hpp2 : IsPrimePow (N - m) :=
      vonMangoldt_ne_zero_iff.mp hΛ2
    have hp1 : m.Prime := by
      by_contra hnp
      exact hnb (Or.inl ⟨hpp1, hnp⟩)
    have hp2 : (N - m).Prime := by
      by_contra hnp
      exact hnb (Or.inr ⟨hpp2, hnp⟩)
    exact absurd ⟨hp1, hp2⟩ (hno' m hmIoo.1 hmIoo.2)
  have hsum : goldbachHeat N t
      = ∑ m ∈ goldbachBad N,
          Λ m * Λ (N - m)
            / Real.sqrt ((m : ℝ) * ((N : ℝ) - m))
            * Real.exp (-t * (Real.log m ^ 2
              + Real.log ((N : ℝ) - m) ^ 2)) :=
    (Finset.sum_subset (Finset.filter_subset _ _) hzero).symm
  have hcontam := goldbach_heat_contamination N t ht
  rw [hsum] at hheat
  linarith

end NCG
