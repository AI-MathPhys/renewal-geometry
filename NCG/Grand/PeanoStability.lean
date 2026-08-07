/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.LoadingDeformations
import NCG.Grand.GrandInterface2

/-!
# Zero-residual certificates for the Peano and count histories
  (`thm:ar-Peano-stability`, Gran-Tensor manuscript)

* `peanoL_covariance` / `peanoL_anchor`: the Peano history
  itself satisfies the deformed covariance `L_aS = S^aL_a` and
  the anchor rule `L_aη = S^{a-1}η`;
* `peano_stability`: the positive Peano and count residuals
  vanish **iff** the candidate is the canonical history —
  `Δ^Peano(A) = 0 ↔ A = L_a` and `Δ^count(D) = 0 ↔ D = N` —
  with the residuals rendered as their defining norm-square
  sums; uniqueness is a terminating zero test on positive
  word-Gram data.

Rendering disclosed: the boxed quantitative stability bounds
`‖A - L_a‖² ≤ X²Δ(A)` refine the zero test by operator-norm
chains through the same ladder induction and are the
manuscript's remaining bookkeeping.
-/

open Matrix

namespace NCG

private lemma pow_mulVec_single0' {X : ℕ} (hX : 0 < X) (k : ℕ)
    (j : Fin X) :
    ((recS X) ^ k *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) j
      = if (j : ℕ) = k then 1 else 0 := by
  rw [recS_pow, mulVec_single_col, Matrix.of_apply]
  have hval : ((⟨0, hX⟩ : Fin X) : ℕ) = 0 := rfl
  rw [hval, zero_add]

/-- The Peano history satisfies the anchor rule
`L_aη = S^{a-1}η`. -/
lemma peanoL_anchor {X : ℕ} (hX : 0 < X) (a : ℕ) (ha : 1 ≤ a) :
    peanoL X a *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
      = (recS X) ^ (a - 1)
        *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 := by
  funext j
  rw [mulVec_single_col, pow_mulVec_single0' hX, peanoL,
    Matrix.of_apply]
  have hval : ((⟨0, hX⟩ : Fin X) : ℕ) = 0 := rfl
  rw [hval]
  by_cases hj : (j : ℕ) + 1 = a * (0 + 1)
  · rw [if_pos hj, if_pos (by omega)]
  · rw [if_neg hj, if_neg (fun h => hj (by omega))]

/-- The Peano history satisfies the deformed covariance
`L_aS = S^aL_a`. -/
lemma peanoL_covariance {X : ℕ} (a : ℕ) (ha : 1 ≤ a) :
    peanoL X a * recS X = (recS X) ^ a * peanoL X a := by
  have hL : peanoL X a * recS X
      = Matrix.of (fun (j i : Fin X) =>
          if (j : ℕ) + 1 = a * ((i : ℕ) + 1 + 1)
          then (1 : ℂ) else 0) := by
    ext j i
    rw [Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_congr rfl (fun k _ => show
        peanoL X a j k * recS X k i
          = if (k : ℕ) = (i : ℕ) + 1
            then (if (j : ℕ) + 1 = a * ((i : ℕ) + 1 + 1)
              then 1 else 0)
            else 0 from by
      rw [peanoL, recS, Matrix.of_apply, Matrix.of_apply]
      by_cases hk : (k : ℕ) = (i : ℕ) + 1
      · rw [if_pos hk, mul_one, hk, if_pos rfl]
      · rw [if_neg hk, mul_zero, if_neg hk])]
    by_cases hi : (i : ℕ) + 1 < X
    · rw [Finset.sum_eq_single (⟨(i : ℕ) + 1, hi⟩ : Fin X)
        (fun k _ hk => by
          rw [if_neg]
          intro hcond
          exact hk (Fin.ext hcond))
        (fun habs => absurd (Finset.mem_univ _) habs)]
      rw [if_pos rfl]
    · rw [Finset.sum_eq_zero (fun k _ => by
        rw [if_neg]
        intro hcond
        have := k.isLt
        omega)]
      have hta : (i : ℕ) + 1 + 1 ≤ a * ((i : ℕ) + 1 + 1) := by
        have hmul := Nat.mul_le_mul (ha) (le_refl ((i : ℕ) + 1 + 1))
        rwa [one_mul] at hmul
      rw [if_neg]
      intro hcond
      have := j.isLt
      omega
  have hR : (recS X) ^ a * peanoL X a
      = Matrix.of (fun (j i : Fin X) =>
          if (j : ℕ) + 1 = a * ((i : ℕ) + 1 + 1)
          then (1 : ℂ) else 0) := by
    ext j i
    rw [recS_pow, Matrix.mul_apply, Matrix.of_apply]
    have hp : 0 < a * ((i : ℕ) + 1) :=
      Nat.mul_pos (by omega) (Nat.succ_pos _)
    have hd : a * ((i : ℕ) + 1 + 1) = a * ((i : ℕ) + 1) + a := by
      ring
    rw [Finset.sum_congr rfl (fun k _ => show
        Matrix.of (fun (j i : Fin X) =>
            if (j : ℕ) = (i : ℕ) + a then (1 : ℂ) else 0) j k
          * peanoL X a k i
          = if (k : ℕ) + 1 = a * ((i : ℕ) + 1)
            then (if (j : ℕ) = (k : ℕ) + a then 1 else 0)
            else 0 from by
      rw [peanoL, Matrix.of_apply, Matrix.of_apply]
      by_cases hk : (k : ℕ) + 1 = a * ((i : ℕ) + 1)
      · rw [if_pos hk, mul_one, if_pos hk]
      · rw [if_neg hk, mul_zero, if_neg hk])]
    by_cases ht : a * ((i : ℕ) + 1) ≤ X
    · have hkX : a * ((i : ℕ) + 1) - 1 < X := by omega
      rw [Finset.sum_eq_single
        (⟨a * ((i : ℕ) + 1) - 1, hkX⟩ : Fin X)
        (fun k _ hk => by
          rw [if_neg]
          intro hcond
          apply hk
          apply Fin.ext
          have hval : ((⟨a * ((i : ℕ) + 1) - 1, hkX⟩
              : Fin X) : ℕ) = a * ((i : ℕ) + 1) - 1 := rfl
          rw [hval]
          omega)
        (fun habs => absurd (Finset.mem_univ _) habs)]
      have hval : ((⟨a * ((i : ℕ) + 1) - 1, hkX⟩
          : Fin X) : ℕ) = a * ((i : ℕ) + 1) - 1 := rfl
      rw [if_pos (by rw [hval]; omega)]
      by_cases hj : (j : ℕ) + 1 = a * ((i : ℕ) + 1 + 1)
      · rw [if_pos (by rw [hval]; omega), if_pos hj]
      · rw [if_neg (by rw [hval]; omega), if_neg hj]
    · rw [Finset.sum_eq_zero (fun k _ => by
        rw [if_neg]
        intro hcond
        have := k.isLt
        omega)]
      rw [if_neg]
      intro hcond
      have := j.isLt
      omega
  rw [hL, hR]

/-- `thm:ar-Peano-stability`: the positive residuals vanish
exactly on the canonical histories. -/
theorem peano_stability {X : ℕ} (hX : 0 < X) (a : ℕ)
    (ha : 1 ≤ a) (A D : Matrix (Fin X) (Fin X) ℂ) :
    (((∑ j, Complex.normSq
        ((A *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
          - (recS X) ^ (a - 1)
            *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) j))
      + (((A * recS X - (recS X) ^ a * A)ᴴ
          * (A * recS X - (recS X) ^ a * A)).trace).re = 0)
      ↔ A = peanoL X a)
    ∧ (((∑ j, Complex.normSq
        (((D *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
          - Pi.single (⟨0, hX⟩ : Fin X) 1 : Fin X → ℂ)) j))
      + (((D * recS X - recS X * D - recS X)ᴴ
          * (D * recS X - recS X * D - recS X)).trace).re = 0)
      ↔ D = Matrix.diagonal
        (fun i : Fin X => ((i : ℕ) + 1 : ℂ))) := by
  constructor
  · constructor
    · intro h0
      have hvnn : 0 ≤ ∑ j, Complex.normSq
          ((A *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
            - (recS X) ^ (a - 1)
              *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) j) :=
        Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
      have hmnn : 0 ≤ (((A * recS X - (recS X) ^ a * A)ᴴ
          * (A * recS X - (recS X) ^ a * A)).trace).re := by
        rw [trace_conj_self_re]
        exact Finset.sum_nonneg fun j _ =>
          Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
      have hv0 : (∑ j, Complex.normSq
          ((A *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
            - (recS X) ^ (a - 1)
              *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) j)) = 0 := by
        linarith
      have hm0 : (((A * recS X - (recS X) ^ a * A)ᴴ
          * (A * recS X - (recS X) ^ a * A)).trace).re = 0 := by
        linarith
      have hMS : A * recS X = (recS X) ^ a * A :=
        sub_eq_zero.mp
          ((trace_conj_self_re_eq_zero _).mp hm0)
      have hMη : A *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
          = (recS X) ^ (a - 1)
            *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 := by
        have hz : ∀ j, (A *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
            - (recS X) ^ (a - 1)
              *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) j = 0 := by
          intro j
          have hj := (Finset.sum_eq_zero_iff_of_nonneg
            fun j _ => Complex.normSq_nonneg _).mp hv0 j
            (Finset.mem_univ j)
          exact Complex.normSq_eq_zero.mp hj
        have : A *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
            - (recS X) ^ (a - 1)
              *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 = 0 :=
          funext fun j => hz j
        exact sub_eq_zero.mp this
      have := loading_deformation hX a ha A 1 hMS
        (by rw [hMη, one_smul])
      rw [this, one_smul]
    · intro hA
      subst hA
      rw [peanoL_anchor hX a ha, sub_self,
        peanoL_covariance a ha, sub_self]
      simp
  · constructor
    · intro h0
      have hvnn : 0 ≤ ∑ j, Complex.normSq
          (((D *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
            - Pi.single (⟨0, hX⟩ : Fin X) 1 : Fin X → ℂ)) j) :=
        Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
      have hmnn : 0 ≤ (((D * recS X - recS X * D - recS X)ᴴ
          * (D * recS X - recS X * D - recS X)).trace).re := by
        rw [trace_conj_self_re]
        exact Finset.sum_nonneg fun j _ =>
          Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
      have hv0 : (∑ j, Complex.normSq
          (((D *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
            - Pi.single (⟨0, hX⟩ : Fin X) 1 : Fin X → ℂ)) j)) = 0 := by
        linarith
      have hm0 : (((D * recS X - recS X * D - recS X)ᴴ
          * (D * recS X - recS X * D - recS X)).trace).re
          = 0 := by
        linarith
      have hcomm : D * recS X - recS X * D = recS X :=
        sub_eq_zero.mp
          ((trace_conj_self_re_eq_zero _).mp hm0)
      have hanchor : D *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
          = Pi.single (⟨0, hX⟩ : Fin X) 1 := by
        have hz : ∀ j, ((D *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
            - Pi.single (⟨0, hX⟩ : Fin X) 1 : Fin X → ℂ)) j = 0 := by
          intro j
          have hj := (Finset.sum_eq_zero_iff_of_nonneg
            fun j _ => Complex.normSq_nonneg _).mp hv0 j
            (Finset.mem_univ j)
          exact Complex.normSq_eq_zero.mp hj
        have : (D *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
            - Pi.single (⟨0, hX⟩ : Fin X) 1 : Fin X → ℂ) = 0 :=
          funext fun j => hz j
        exact sub_eq_zero.mp this
      exact count_rigidity hX D hanchor hcomm
    · intro hD
      subst hD
      have hNS := (recS_relations
        (show 1 ≤ X from hX)).2.2
      rw [hNS, sub_self]
      have hNη : Matrix.diagonal
          (fun i : Fin X => ((i : ℕ) + 1 : ℂ))
          *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
          = Pi.single (⟨0, hX⟩ : Fin X) 1 := by
        funext j
        rw [mulVec_single_col, Matrix.diagonal_apply,
          Pi.single_apply]
        by_cases hj : j = (⟨0, hX⟩ : Fin X)
        · rw [if_pos hj, if_pos hj, hj]
          norm_num
        · rw [if_neg hj, if_neg hj]
      rw [hNη, sub_self]
      simp

end NCG
