/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.CWLaplace

/-!
# Hypergeometric structure of Curie–Weiss cylinder probabilities

Supporting layer for `thm:cw-spontaneous-orientation`: the
probability of a fixed pattern on `r` marked cells decomposes over
magnetization fibres with the exchangeable hypergeometric weight

`hyp(k) = (k)_j (N−k)_{r−j} / (N)_r`,

which is within `2r²/(N−r)` of the Bernoulli product
`p_k^j q_k^{r−j}`, uniformly in `k`.
-/

namespace NCG.Upstream

open Finset Real Nat

/-! ## The counting identity -/

theorem hyp_count_identity {N r j k : ℕ} (hjr : j ≤ r) (hrN : r ≤ N)
    (hjk : j ≤ k) (hkN : k ≤ N) :
    (N - r).choose (k - j) * N.descFactorial r
      = N.choose k
        * (k.descFactorial j * (N - k).descFactorial (r - j)) := by
  by_cases hcase : k - j ≤ N - r
  · have hA : 0 < (k - j)! * ((N - r) - (k - j))! :=
      Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    refine Nat.eq_of_mul_eq_mul_right hA ?_
    have h1 : (N - r).choose (k - j) * (k - j)!
        * ((N - r) - (k - j))! = (N - r)! :=
      Nat.choose_mul_factorial_mul_factorial hcase
    have h2 : (N - r)! * N.descFactorial r = N ! :=
      Nat.factorial_mul_descFactorial hrN
    have h3 : (k - j)! * k.descFactorial j = k ! :=
      Nat.factorial_mul_descFactorial hjk
    have h4 : ((N - k) - (r - j))! * (N - k).descFactorial (r - j)
        = (N - k)! :=
      Nat.factorial_mul_descFactorial (by omega)
    have h5 : N.choose k * k ! * (N - k)! = N ! :=
      Nat.choose_mul_factorial_mul_factorial hkN
    have hsub : (N - r) - (k - j) = (N - k) - (r - j) := by omega
    have hL : (N - r).choose (k - j) * N.descFactorial r
        * ((k - j)! * ((N - r) - (k - j))!) = N ! := by
      calc (N - r).choose (k - j) * N.descFactorial r
            * ((k - j)! * ((N - r) - (k - j))!)
          = ((N - r).choose (k - j) * (k - j)!
              * ((N - r) - (k - j))!) * N.descFactorial r := by
            ring
        _ = (N - r)! * N.descFactorial r := by rw [h1]
        _ = N ! := h2
    have hR : N.choose k
        * (k.descFactorial j * (N - k).descFactorial (r - j))
        * ((k - j)! * ((N - r) - (k - j))!) = N ! := by
      calc N.choose k
            * (k.descFactorial j * (N - k).descFactorial (r - j))
            * ((k - j)! * ((N - r) - (k - j))!)
          = N.choose k * (((k - j)! * k.descFactorial j)
            * ((((N - k) - (r - j))!)
              * (N - k).descFactorial (r - j))) := by
            rw [hsub]
            ring
        _ = N.choose k * (k ! * (N - k)!) := by rw [h3, h4]
        _ = N ! := by rw [← h5]; ring
    rw [hL, hR]
  · push_neg at hcase
    have hz1 : (N - r).choose (k - j) = 0 :=
      Nat.choose_eq_zero_of_lt hcase
    have hz2 : (N - k).descFactorial (r - j) = 0 := by
      rw [Nat.descFactorial_eq_zero_iff_lt]
      omega
    rw [hz1, hz2]
    ring

/-! ## The real hypergeometric weight -/

/-- `hyp(k) = (k)_j (N−k)_{r−j} / (N)_r`. -/
noncomputable def hypWeight (N r j k : ℕ) : ℝ :=
  (k.descFactorial j : ℝ) * ((N - k).descFactorial (r - j) : ℝ)
    / (N.descFactorial r : ℝ)

theorem hypWeight_nonneg (N r j k : ℕ) : 0 ≤ hypWeight N r j k := by
  unfold hypWeight
  positivity

theorem hypWeight_mul_choose {N r j k : ℕ} (hjr : j ≤ r)
    (hrN : r ≤ N) (hjk : j ≤ k) (hkN : k ≤ N) :
    hypWeight N r j k * (N.choose k : ℝ)
      = ((N - r).choose (k - j) : ℝ) := by
  have hpos : 0 < (N.descFactorial r : ℝ) :=
    Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr hrN)
  have hid := hyp_count_identity hjr hrN hjk hkN
  have hid' : (((N - r).choose (k - j) * N.descFactorial r : ℕ) : ℝ)
      = ((N.choose k
        * (k.descFactorial j * (N - k).descFactorial (r - j)) : ℕ)
          : ℝ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℝ)) hid
  push_cast at hid'
  unfold hypWeight
  field_simp
  linarith [hid']

/-- The hypergeometric weight vanishes below the pattern count. -/
theorem hypWeight_eq_zero_of_lt {N r j k : ℕ} (hkj : k < j) :
    hypWeight N r j k = 0 := by
  unfold hypWeight
  rw [Nat.descFactorial_eq_zero_iff_lt.mpr hkj]
  simp

/-- The hypergeometric weight vanishes above the window. -/
theorem hypWeight_eq_zero_of_gt {N r j k : ℕ} (hjr : j ≤ r)
    (hkN : k ≤ N) (hgt : N - r + j < k) :
    hypWeight N r j k = 0 := by
  unfold hypWeight
  rw [show (N - k).descFactorial (r - j) = 0 from
    Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
  simp

/-! ## Product form and the uniform Bernoulli approximation -/

/-- Difference of products of `[0,1]` factors. -/
theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ s, f i ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ i ∈ s, g i ∈ Set.Icc (0 : ℝ) 1) :
    |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Finset.sum_insert ha]
    have hfa := hf a (Finset.mem_insert_self a s)
    have hga := hg a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, f i ∈ Set.Icc (0 : ℝ) 1 :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, g i ∈ Set.Icc (0 : ℝ) 1 :=
      fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have ihs := ih hfs hgs
    have hPf : ∏ i ∈ s, f i ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact Finset.prod_nonneg fun i hi => (hfs i hi).1
      · exact Finset.prod_le_one
          (fun i hi => (hfs i hi).1) (fun i hi => (hfs i hi).2)
    have hPg : ∏ i ∈ s, g i ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact Finset.prod_nonneg fun i hi => (hgs i hi).1
      · exact Finset.prod_le_one
          (fun i hi => (hgs i hi).1) (fun i hi => (hgs i hi).2)
    have hkey : |f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i|
        ≤ |f a - g a| * (∏ i ∈ s, f i)
          + g a * |∏ i ∈ s, f i - ∏ i ∈ s, g i| := by
      have hsplit : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
          = (f a - g a) * (∏ i ∈ s, f i)
            + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by
        ring
      rw [hsplit]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hPf.1,
        abs_of_nonneg hga.1]
    refine le_trans hkey ?_
    have h1 : |f a - g a| * (∏ i ∈ s, f i) ≤ |f a - g a| :=
      mul_le_of_le_one_right (abs_nonneg _) hPf.2
    have h2 : g a * |∏ i ∈ s, f i - ∏ i ∈ s, g i|
        ≤ ∑ i ∈ s, |f i - g i| := by
      calc g a * |∏ i ∈ s, f i - ∏ i ∈ s, g i|
          ≤ 1 * |∏ i ∈ s, f i - ∏ i ∈ s, g i| :=
            mul_le_mul_of_nonneg_right hga.2 (abs_nonneg _)
        _ = |∏ i ∈ s, f i - ∏ i ∈ s, g i| := one_mul _
        _ ≤ ∑ i ∈ s, |f i - g i| := ihs
    linarith

/-- The product form of the hypergeometric weight. -/
theorem hypWeight_eq_prod {N r j k : ℕ} (hjr : j ≤ r) (hrN : r ≤ N)
    (hjk : j ≤ k) (hkN : k ≤ N) :
    hypWeight N r j k
      = (∏ i ∈ Finset.range j, ((k : ℝ) - i) / ((N : ℝ) - i))
        * ∏ i ∈ Finset.range (r - j),
          (((N : ℝ) - k) - i) / (((N : ℝ) - j) - i) := by
  have hNr : N.descFactorial r
      = N.descFactorial j * (N - j).descFactorial (r - j) := by
    have h := Nat.descFactorial_mul_descFactorial (n := N) hjr
    rw [← h]
    ring
  have hcast : ∀ (n m : ℕ),
      ((n.descFactorial m : ℕ) : ℝ)
        = ∏ i ∈ Finset.range m, ((n : ℝ) - i) := by
    intro n m
    rcases Nat.lt_or_ge n.succ m with hmn | hmn
    · have hz : n.descFactorial m = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [hz, Nat.cast_zero, eq_comm]
      refine Finset.prod_eq_zero
        (Finset.mem_range.mpr (show n < m by omega)) ?_
      rw [sub_self]
    · rw [Nat.descFactorial_eq_prod_range]
      push_cast
      refine Finset.prod_congr rfl fun i hi => ?_
      have h9 : i < m := Finset.mem_range.mp hi
      rw [Nat.cast_sub (by omega)]
  have hNj0 : ∀ i ∈ Finset.range j, ((N : ℝ) - i) ≠ 0 := by
    intro i hi
    have hi' : i < j := Finset.mem_range.mp hi
    have : (i : ℝ) < N := by
      exact_mod_cast lt_of_lt_of_le (lt_of_lt_of_le hi' hjr) hrN
    linarith
  have hNjr0 : ∀ i ∈ Finset.range (r - j),
      (((N : ℝ) - j) - i) ≠ 0 := by
    intro i hi
    have hi' : i < r - j := Finset.mem_range.mp hi
    have h1 : (j : ℝ) + i < N := by
      have : j + i < r := by omega
      have h2 : ((j + i : ℕ) : ℝ) < r := by exact_mod_cast this
      have h3 : (r : ℝ) ≤ N := by exact_mod_cast hrN
      push_cast at h2
      linarith
    linarith
  unfold hypWeight
  rw [hNr]
  push_cast
  rw [hcast k j, hcast N j, hcast (N - j) (r - j),
    hcast (N - k) (r - j)]
  rw [Nat.cast_sub (le_trans hjr hrN), Nat.cast_sub hkN]
  have hd1 : (∏ i ∈ Finset.range j, ((N : ℝ) - i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hNj0
  have hd2 : (∏ i ∈ Finset.range (r - j), (((N : ℝ) - j) - i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hNjr0
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
  field_simp

set_option maxHeartbeats 800000 in
-- the two product blocks make unification in this proof heavy
/-- Uniform Bernoulli approximation of the hypergeometric weight:
`|hyp(k) − p_k^j q_k^{r−j}| ≤ 2r²/(N−r)`. -/
theorem hypWeight_approx {N r j k : ℕ} (hjr : j ≤ r) (hjk : j ≤ k)
    (hkN : k ≤ N) (hrN : 2 * r < N) :
    |hypWeight N r j k
      - ((k : ℝ) / N) ^ j * (((N : ℝ) - k) / N) ^ (r - j)|
    ≤ 2 * (r : ℝ) ^ 2 / ((N : ℝ) - r) := by
  have hrN' : r ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by
    have h0 : 0 < N := by omega
    exact_mod_cast h0
  have hrRN : (r : ℝ) < N := by
    have h0 : r < N := by omega
    exact_mod_cast h0
  have hNr0 : (0 : ℝ) < (N : ℝ) - r := by linarith
  have hkR : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hjR : (j : ℝ) ≤ r := by exact_mod_cast hjr
  have hjkR : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have hr2 : (0 : ℝ) ≤ 2 * (r : ℝ) ^ 2 / ((N : ℝ) - r) := by
    positivity
  by_cases hwin : r - j ≤ N - k
  · -- main regime: all factors lie in [0,1]
    rw [hypWeight_eq_prod hjr hrN' hjk hkN]
    have hwinR : (r : ℝ) - j ≤ (N : ℝ) - k := by
      have h1 : ((r - j : ℕ) : ℝ) ≤ ((N - k : ℕ) : ℝ) := by
        exact_mod_cast hwin
      rw [Nat.cast_sub hjr, Nat.cast_sub hkN] at h1
      exact h1
    set A : ℝ := ∏ i ∈ Finset.range j, ((k : ℝ) - i) / ((N : ℝ) - i)
      with hA_def
    set B : ℝ := ∏ i ∈ Finset.range (r - j),
      (((N : ℝ) - k) - i) / (((N : ℝ) - j) - i) with hB_def
    set a : ℝ := ((k : ℝ) / N) ^ j with ha_def
    set b : ℝ := (((N : ℝ) - k) / N) ^ (r - j) with hb_def
    -- factor bounds, first block
    have hf1 : ∀ i ∈ Finset.range j,
        ((k : ℝ) - i) / ((N : ℝ) - i) ∈ Set.Icc (0 : ℝ) 1 := by
      intro i hi
      have hi' : i < j := Finset.mem_range.mp hi
      have hik : (i : ℝ) < k := by
        exact_mod_cast lt_of_lt_of_le hi' hjk
      have hiN : (i : ℝ) < N := by linarith
      constructor
      · have h2 : (0 : ℝ) < (N : ℝ) - i := by linarith
        have h3 : (0 : ℝ) ≤ (k : ℝ) - i := by linarith
        positivity
      · rw [div_le_one (by linarith)]
        linarith
    have hg1 : ((k : ℝ) / N) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · rw [div_le_one hN0]
        exact hkR
    have hf2 : ∀ i ∈ Finset.range (r - j),
        (((N : ℝ) - k) - i) / (((N : ℝ) - j) - i)
          ∈ Set.Icc (0 : ℝ) 1 := by
      intro i hi
      have hi' : i < r - j := Finset.mem_range.mp hi
      have hiR : (i : ℝ) < (r : ℝ) - j := by
        have h4 : ((i : ℕ) : ℝ) < ((r - j : ℕ) : ℝ) := by
          exact_mod_cast hi'
        rwa [Nat.cast_sub hjr] at h4
      have hnum : (0 : ℝ) < ((N : ℝ) - k) - i := by
        linarith [hwinR]
      have hden : (0 : ℝ) < ((N : ℝ) - j) - i := by
        linarith
      constructor
      · positivity
      · rw [div_le_one hden]
        linarith
    have hg2 : (((N : ℝ) - k) / N) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · have : (0 : ℝ) ≤ (N : ℝ) - k := by linarith
        positivity
      · rw [div_le_one hN0]
        linarith
    -- per-factor errors
    have herr1 : ∀ i ∈ Finset.range j,
        |((k : ℝ) - i) / ((N : ℝ) - i) - (k : ℝ) / N|
          ≤ (r : ℝ) / ((N : ℝ) - r) := by
      intro i hi
      have hi' : i < j := Finset.mem_range.mp hi
      have hiR : (i : ℝ) < j := by exact_mod_cast hi'
      have hiN : (0 : ℝ) < (N : ℝ) - i := by linarith
      rw [div_sub_div _ _ hiN.ne' hN0.ne', abs_div]
      have h7 : (i : ℝ) ≤ r := by linarith
      have h8 : (N : ℝ) - r ≤ (N : ℝ) - i := by linarith
      have h9 : (0 : ℝ) ≤ (N : ℝ) - k := by linarith
      have hnum : |((k : ℝ) - i) * N - ((N : ℝ) - i) * k|
          = i * ((N : ℝ) - k) := by
        rw [show ((k : ℝ) - i) * N - ((N : ℝ) - i) * k
            = -((i : ℝ) * ((N : ℝ) - k)) from by ring, abs_neg]
        rw [abs_of_nonneg (by positivity)]
      rw [hnum, abs_of_pos (by positivity : (0:ℝ) < ((N:ℝ)-i) * N)]
      rw [div_le_div_iff₀ (by positivity) hNr0]
      have hk0R : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have h10 : (i : ℝ) * ((N : ℝ) - k) ≤ (r : ℝ) * N := by
        nlinarith [mul_nonneg (sub_nonneg.mpr h7) h9,
          mul_nonneg (by positivity : (0:ℝ) ≤ (r:ℝ)) hk0R]
      nlinarith [h10, hNr0, hN0,
        mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ (r:ℝ))
          hN0.le) (sub_nonneg.mpr h8)]
    have herr2 : ∀ i ∈ Finset.range (r - j),
        |(((N : ℝ) - k) - i) / (((N : ℝ) - j) - i)
          - ((N : ℝ) - k) / N| ≤ 2 * (r : ℝ) / ((N : ℝ) - r) := by
      intro i hi
      have hi' : i < r - j := Finset.mem_range.mp hi
      have hiR : (i : ℝ) < (r : ℝ) - j := by
        have h4 : ((i : ℕ) : ℝ) < ((r - j : ℕ) : ℝ) := by
          exact_mod_cast hi'
        rwa [Nat.cast_sub hjr] at h4
      have hden : (0 : ℝ) < ((N : ℝ) - j) - i := by linarith
      rw [div_sub_div _ _ hden.ne' hN0.ne', abs_div]
      have h7 : (i : ℝ) ≤ r := by linarith
      have h8 : (j : ℝ) + i ≤ r := by linarith
      have h6 : (0 : ℝ) ≤ (N : ℝ) - k := by linarith
      have h9 : (N : ℝ) - k ≤ N := by
        have hk0R : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith
      have hji0 : (0 : ℝ) ≤ (j : ℝ) + i := by positivity
      have hnum : |(((N : ℝ) - k) - i) * N
          - (((N : ℝ) - j) - i) * ((N : ℝ) - k)|
          ≤ 2 * (r : ℝ) * N := by
        rw [show (((N : ℝ) - k) - i) * N
            - (((N : ℝ) - j) - i) * ((N : ℝ) - k)
            = -((i : ℝ) * N) + ((N : ℝ) - k) * ((j : ℝ) + i)
            from by ring]
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_neg, abs_of_nonneg (by positivity),
          abs_of_nonneg (mul_nonneg h6 hji0)]
        have h11 : (i : ℝ) * N ≤ (r : ℝ) * N :=
          mul_le_mul_of_nonneg_right h7 hN0.le
        have h12 : ((N : ℝ) - k) * ((j : ℝ) + i)
            ≤ (N : ℝ) * r := by
          nlinarith [mul_nonneg h6 hji0,
            mul_nonneg (sub_nonneg.mpr h9) hji0,
            mul_nonneg hN0.le (sub_nonneg.mpr h8)]
        nlinarith [h11, h12]
      rw [abs_of_pos (by positivity : (0:ℝ) < (((N:ℝ)-j)-i) * N)]
      have hden2 : (N : ℝ) - r ≤ ((N : ℝ) - j) - i := by linarith
      rw [div_le_div_iff₀ (by positivity) hNr0]
      calc |(((N : ℝ) - k) - i) * N
            - (((N : ℝ) - j) - i) * ((N : ℝ) - k)|
            * ((N : ℝ) - r)
          ≤ (2 * (r : ℝ) * N) * ((N : ℝ) - r) :=
            mul_le_mul_of_nonneg_right hnum hNr0.le
        _ ≤ 2 * (r : ℝ) * ((((N : ℝ) - j) - i) * N) := by
            nlinarith [hden2, hN0, hden,
              mul_nonneg (mul_nonneg
                (by positivity : (0:ℝ) ≤ 2 * (r:ℝ)) hN0.le)
                (sub_nonneg.mpr hden2)]
    -- assemble
    have hAmem : A ∈ Set.Icc (0 : ℝ) 1 := by
      rw [hA_def]
      constructor
      · exact Finset.prod_nonneg fun i hi => (hf1 i hi).1
      · exact Finset.prod_le_one (fun i hi => (hf1 i hi).1)
          (fun i hi => (hf1 i hi).2)
    have hamem : a ∈ Set.Icc (0 : ℝ) 1 := by
      rw [ha_def]
      constructor
      · positivity
      · exact pow_le_one₀ hg1.1 hg1.2
    have hbmem : b ∈ Set.Icc (0 : ℝ) 1 := by
      rw [hb_def]
      constructor
      · exact pow_nonneg hg2.1 _
      · exact pow_le_one₀ hg2.1 hg2.2
    have hBmem : B ∈ Set.Icc (0 : ℝ) 1 := by
      rw [hB_def]
      constructor
      · exact Finset.prod_nonneg fun i hi => (hf2 i hi).1
      · exact Finset.prod_le_one (fun i hi => (hf2 i hi).1)
          (fun i hi => (hf2 i hi).2)
    have hAa : |A - a| ≤ (j : ℝ) * ((r : ℝ) / ((N : ℝ) - r)) := by
      have h10 : a = ∏ _i ∈ Finset.range j, (k : ℝ) / N := by
        rw [ha_def, Finset.prod_const, Finset.card_range]
      rw [h10]
      refine le_trans (abs_prod_sub_prod_le _ _ _ hf1
        (fun i hi => hg1)) ?_
      calc ∑ i ∈ Finset.range j,
            |((k : ℝ) - i) / ((N : ℝ) - i) - (k : ℝ) / N|
          ≤ ∑ _i ∈ Finset.range j, (r : ℝ) / ((N : ℝ) - r) :=
            Finset.sum_le_sum herr1
        _ = (j : ℝ) * ((r : ℝ) / ((N : ℝ) - r)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hBb : |B - b|
        ≤ ((r : ℝ) - j) * (2 * (r : ℝ) / ((N : ℝ) - r)) := by
      have h11 : b = ∏ _i ∈ Finset.range (r - j),
          ((N : ℝ) - k) / N := by
        rw [hb_def, Finset.prod_const, Finset.card_range]
      rw [h11]
      refine le_trans (abs_prod_sub_prod_le _ _ _ hf2
        (fun i hi => hg2)) ?_
      calc ∑ i ∈ Finset.range (r - j),
            |(((N : ℝ) - k) - i) / (((N : ℝ) - j) - i)
              - ((N : ℝ) - k) / N|
          ≤ ∑ _i ∈ Finset.range (r - j),
            2 * (r : ℝ) / ((N : ℝ) - r) :=
            Finset.sum_le_sum herr2
        _ = ((r : ℝ) - j) * (2 * (r : ℝ) / ((N : ℝ) - r)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              Nat.cast_sub hjr]
    have hsplit : |A * B - a * b|
        ≤ |A - a| + |B - b| := by
      have h12 : A * B - a * b = (A - a) * B + a * (B - b) := by
        ring
      rw [h12]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hamem.1]
      have h13 : |A - a| * |B| ≤ |A - a| := by
        refine mul_le_of_le_one_right (abs_nonneg _) ?_
        rw [abs_of_nonneg hBmem.1]
        exact hBmem.2
      have h14 : a * |B - b| ≤ |B - b| := by
        refine mul_le_of_le_one_left (abs_nonneg _) hamem.2
      linarith
    refine le_trans hsplit ?_
    have hj0 : (0 : ℝ) ≤ j := by positivity
    calc |A - a| + |B - b|
        ≤ (j : ℝ) * ((r : ℝ) / ((N : ℝ) - r))
          + ((r : ℝ) - j) * (2 * (r : ℝ) / ((N : ℝ) - r)) := by
          linarith [hAa, hBb]
      _ ≤ 2 * (r : ℝ) ^ 2 / ((N : ℝ) - r) := by
          have hcombine : (j : ℝ) * ((r : ℝ) / ((N : ℝ) - r))
              + ((r : ℝ) - j) * (2 * (r : ℝ) / ((N : ℝ) - r))
              = ((j : ℝ) * r + ((r : ℝ) - j) * (2 * r))
                / ((N : ℝ) - r) := by
            field_simp
          rw [hcombine]
          refine (div_le_div_iff_of_pos_right hNr0).mpr ?_
          nlinarith [hj0, hjR,
            mul_nonneg hj0 (by positivity : (0:ℝ) ≤ (r:ℝ))]
  · -- degenerate regime: the weight vanishes and `q < r/N`
    push_neg at hwin
    have hz : hypWeight N r j k = 0 := by
      unfold hypWeight
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr hwin]
      simp
    rw [hz, zero_sub, abs_neg]
    have hr1 : 1 ≤ r := by omega
    have hr1R : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have hkR0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hq0 : (0 : ℝ) ≤ ((N : ℝ) - k) / N := by
      have h1 : (0 : ℝ) ≤ (N : ℝ) - k := by linarith
      positivity
    have hq1 : ((N : ℝ) - k) / N ≤ 1 := by
      rw [div_le_one hN0]
      linarith
    have hp1 : ((k : ℝ) / N) ^ j ≤ 1 := by
      refine pow_le_one₀ (by positivity) ?_
      rw [div_le_one hN0]
      exact hkR
    have hqpow : (((N : ℝ) - k) / N) ^ (r - j)
        ≤ ((N : ℝ) - k) / N :=
      pow_le_of_le_one hq0 hq1 (by omega)
    have hNkR : (N : ℝ) - k < r := by
      have h1 : ((N - k : ℕ) : ℝ) < ((r - j : ℕ) : ℝ) := by
        exact_mod_cast hwin
      rw [Nat.cast_sub hkN, Nat.cast_sub hjr] at h1
      have h2 : (0 : ℝ) ≤ (j : ℝ) := by positivity
      linarith
    have habs : |((k : ℝ) / N) ^ j
        * (((N : ℝ) - k) / N) ^ (r - j)|
        ≤ ((N : ℝ) - k) / N := by
      rw [abs_of_nonneg (mul_nonneg
        (pow_nonneg (by positivity) _) (pow_nonneg hq0 _))]
      calc ((k : ℝ) / N) ^ j * (((N : ℝ) - k) / N) ^ (r - j)
          ≤ 1 * (((N : ℝ) - k) / N) ^ (r - j) :=
            mul_le_mul_of_nonneg_right hp1 (pow_nonneg hq0 _)
        _ = (((N : ℝ) - k) / N) ^ (r - j) := one_mul _
        _ ≤ ((N : ℝ) - k) / N := hqpow
    refine le_trans habs ?_
    rw [div_le_div_iff₀ hN0 hNr0]
    have hstep1 : ((N : ℝ) - k) * ((N : ℝ) - r)
        ≤ (r : ℝ) * ((N : ℝ) - r) :=
      mul_le_mul_of_nonneg_right hNkR.le hNr0.le
    have hstep2 : (r : ℝ) * ((N : ℝ) - r) ≤ (r : ℝ) * N :=
      mul_le_mul_of_nonneg_left (by linarith)
        (by positivity : (0:ℝ) ≤ (r:ℝ))
    have hstep3 : (r : ℝ) * N ≤ 2 * (r : ℝ) ^ 2 * N :=
      mul_le_mul_of_nonneg_right
        (by nlinarith [hr1R] : (r : ℝ) ≤ 2 * (r : ℝ) ^ 2) hN0.le
    linarith

end NCG.Upstream
