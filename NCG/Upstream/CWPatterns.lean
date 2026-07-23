/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.CWHypergeom

/-!
# Cylinder probabilities decompose hypergeometrically over
magnetization fibres

For `N = r + t` cells, the Curie–Weiss probability that the `r`
marked cells show the pattern `b` equals
`∑ₖ hyp(k) · μ_N(count = k)` — exact exchangeability at every finite
size, for every field.
-/

namespace NCG.Upstream

open Finset Real

/-- Splitting a configuration into its marked and bulk parts. -/
def splitEquiv (r t : ℕ) :
    (Fin (r + t) → Bool) ≃ (Fin r → Bool) × (Fin t → Bool) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

theorem splitEquiv_symm_castAdd (r t : ℕ) (a : Fin r → Bool)
    (c : Fin t → Bool) (i : Fin r) :
    (splitEquiv r t).symm (a, c) (Fin.castAdd t i) = a i := by
  unfold splitEquiv
  simp [Equiv.sumArrowEquivProdArrow]

theorem splitEquiv_symm_natAdd (r t : ℕ) (a : Fin r → Bool)
    (c : Fin t → Bool) (i : Fin t) :
    (splitEquiv r t).symm (a, c) (Fin.natAdd r i) = c i := by
  unfold splitEquiv
  simp [Equiv.sumArrowEquivProdArrow]

theorem countTrue_eq_sum (N : ℕ) (η : Fin N → Bool) :
    countTrue N η = ∑ i, if η i = true then 1 else 0 := by
  unfold countTrue
  rw [Finset.card_filter]

theorem countTrue_split (r t : ℕ) (a : Fin r → Bool)
    (c : Fin t → Bool) :
    countTrue (r + t) ((splitEquiv r t).symm (a, c))
      = countTrue r a + countTrue t c := by
  rw [countTrue_eq_sum, countTrue_eq_sum, countTrue_eq_sum]
  rw [← Fintype.sum_equiv finSumFinEquiv
    (fun s => if (splitEquiv r t).symm (a, c) (finSumFinEquiv s)
      = true then 1 else 0)
    (fun idx => if (splitEquiv r t).symm (a, c) idx = true
      then 1 else 0) (fun s => rfl)]
  rw [Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show finSumFinEquiv (Sum.inl i) = Fin.castAdd t i from by
      simp]
    rw [splitEquiv_symm_castAdd]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show finSumFinEquiv (Sum.inr i) = Fin.natAdd r i from by
      simp]
    rw [splitEquiv_symm_natAdd]

theorem pattern_iff (r t : ℕ) (a b : Fin r → Bool)
    (c : Fin t → Bool) :
    (∀ i : Fin r,
      (splitEquiv r t).symm (a, c) (Fin.castAdd t i) = b i)
      ↔ a = b := by
  constructor
  · intro hp
    funext i
    rw [← splitEquiv_symm_castAdd r t a c i]
    exact hp i
  · intro hab i
    rw [splitEquiv_symm_castAdd, hab]

/-- **Exchangeability**: the cylinder probability of a pattern `b`
decomposes over magnetization fibres with the hypergeometric
weight, at every size and field. -/
theorem cw_pattern_decomposition (lam h : ℝ) (r t : ℕ)
    (hrt : 0 < r + t) (b : Fin r → Bool) :
    ∑ η ∈ Finset.univ.filter (fun η : Fin (r + t) → Bool =>
        ∀ i : Fin r, η (Fin.castAdd t i) = b i),
      cwMeasure (r + t) lam h η
    = ∑ k ∈ Finset.range (r + t + 1),
        hypWeight (r + t) r (countTrue r b) k
        * ∑ η ∈ Finset.univ.filter
            (fun η : Fin (r + t) → Bool =>
              countTrue (r + t) η = k),
          cwMeasure (r + t) lam h η := by
  set N : ℕ := r + t with hN_def
  set j : ℕ := countTrue r b with hj_def
  have hjr : j ≤ r := countTrue_le r b
  set W : ℕ → ℝ := fun k => Real.exp ((N : ℝ)
    * (cwPressure lam h (mGrid N k) - cwEntropy (mGrid N k)))
    with hW_def
  have hw : ∀ η : Fin N → Bool, cwWeight N lam h η
      = W (countTrue N η) := by
    intro η
    rw [hW_def]
    change cwWeight N lam h η = Real.exp ((N : ℝ)
      * (cwPressure lam h (mGrid N (countTrue N η))
        - cwEntropy (mGrid N (countTrue N η))))
    unfold cwWeight
    rw [magSum_eq_countTrue, ← weight_exponent_eq hrt lam h]
  -- express both sides over weights
  have hZ := cwPartition_pos N lam h
  -- left side numerator
  have hLHS : ∑ η ∈ Finset.univ.filter
      (fun η : Fin N → Bool =>
        ∀ i : Fin r, η (Fin.castAdd t i) = b i),
      cwMeasure N lam h η
      = (∑ l ∈ Finset.range (t + 1),
          (t.choose l : ℝ) * W (j + l)) / cwPartition N lam h := by
    unfold cwMeasure
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_filter]
    rw [Finset.sum_congr rfl fun η _ => by rw [hw η]]
    rw [← Equiv.sum_comp (splitEquiv r t).symm
      (fun η => if (∀ i : Fin r, η (Fin.castAdd t i) = b i)
        then W (countTrue N η) else 0)]
    rw [Fintype.sum_prod_type]
    have hinner : ∀ a : Fin r → Bool,
        (∑ c : Fin t → Bool,
          if (∀ i : Fin r, (splitEquiv r t).symm (a, c)
              (Fin.castAdd t i) = b i)
          then W (countTrue N ((splitEquiv r t).symm (a, c)))
          else 0)
        = if a = b then
            ∑ c : Fin t → Bool, W (j + countTrue t c) else 0 := by
      intro a
      by_cases hab : a = b
      · rw [if_pos hab]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [if_pos ((pattern_iff r t a b c).mpr hab)]
        rw [countTrue_split, hab, ← hj_def]
      · rw [if_neg hab]
        refine Finset.sum_eq_zero fun c _ => ?_
        rw [if_neg (fun hp => hab ((pattern_iff r t a b c).mp hp))]
    rw [Finset.sum_congr rfl fun a _ => hinner a]
    rw [Finset.sum_ite_eq' Finset.univ b
      (fun _ => ∑ c : Fin t → Bool, W (j + countTrue t c))]
    rw [if_pos (Finset.mem_univ b)]
    exact sum_count_fiber t (fun l => W (j + l))
  -- right side numerator
  have hRHS : ∑ k ∈ Finset.range (N + 1),
      hypWeight N r j k
      * ∑ η ∈ Finset.univ.filter
          (fun η : Fin N → Bool => countTrue N η = k),
        cwMeasure N lam h η
      = (∑ k ∈ Finset.range (N + 1),
          hypWeight N r j k * ((N.choose k : ℝ) * W k))
        / cwPartition N lam h := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    unfold cwMeasure
    rw [← Finset.sum_div]
    rw [Finset.sum_congr rfl fun η hη => by rw [hw η]]
    rw [Finset.sum_congr rfl (fun η hη => by
      rw [(Finset.mem_filter.mp hη).2])]
    rw [Finset.sum_const, card_countTrue_fiber, nsmul_eq_mul]
    ring
  rw [hLHS, hRHS]
  congr 1
  -- the numerators agree: reindex over the shifted window
  have hvanish : ∀ k ∈ Finset.range (N + 1),
      k ∉ Finset.Ico j (j + t + 1)
      → hypWeight N r j k * ((N.choose k : ℝ) * W k) = 0 := by
    intro k hk hnot
    rw [Finset.mem_Ico] at hnot
    push Not at hnot
    rcases lt_or_ge k j with hlt | hge
    · rw [hypWeight_eq_zero_of_lt hlt, zero_mul]
    · have hgt : j + t + 1 ≤ k := hnot hge
      have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [hypWeight_eq_zero_of_gt hjr hkN (by omega), zero_mul]
  have hsub : Finset.Ico j (j + t + 1) ⊆ Finset.range (N + 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_subset hsub (fun k hk hnot =>
    hvanish k hk hnot)]
  rw [Finset.sum_Ico_eq_sum_range]
  rw [show j + t + 1 - j = t + 1 from by omega]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlt : l ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have hchoose := hypWeight_mul_choose (N := N) (r := r) (j := j)
    (k := j + l) hjr (by omega) (by omega) (by omega)
  rw [show N - r = t from by omega] at hchoose
  rw [show j + l - j = l from by omega] at hchoose
  calc (t.choose l : ℝ) * W (j + l)
      = (hypWeight N r j (j + l) * (N.choose (j + l) : ℝ))
        * W (j + l) := by rw [hchoose]
    _ = hypWeight N r j (j + l)
        * ((N.choose (j + l) : ℝ) * W (j + l)) := by ring

end NCG.Upstream
