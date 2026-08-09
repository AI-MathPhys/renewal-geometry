/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteEulerFactorization
import NCG.Grand.LoadingDeformations

/-!
# complete scalar-loading classification

This file closes the bookkeeping clauses left after the operator rigidity
theorems: coefficient multiplicativity, cutoff stabilization, and the exact
weighted finite Euler product.
-/

open Matrix
open scoped Function

namespace NCG

/-- Equality of scalar Peano histories below cutoff detects equality of their
scalars. -/
lemma smul_peano_injective {X n : ℕ} (hX : 0 < X) (hn : 1 ≤ n)
    (hnX : n ≤ X) {a b : ℂ}
    (h : a • peanoL X n = b • peanoL X n) : a = b := by
  let j : Fin X := ⟨n - 1, by omega⟩
  let i : Fin X := ⟨0, hX⟩
  have hij := congrArg (fun A : Matrix (Fin X) (Fin X) ℂ => A j i) h
  have hpred : n - 1 + 1 = n := by omega
  simpa [j, i, peanoL, hpred] using hij

/-- The scalar coefficients forced by natural Peano loadings are
multiplicative whenever the operator product survives the cutoff. -/
theorem loading_coefficients_multiplicative {X : ℕ} (hX : 0 < X)
    (c : ℕ → ℂ)
    (h1 : c 1 • peanoL X 1 = 1)
    (hmul : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a * b ≤ X →
      (c a • peanoL X a) * (c b • peanoL X b) =
        c (a * b) • peanoL X (a * b)) :
    c 1 = 1 ∧ ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a * b ≤ X →
      c (a * b) = c a * c b := by
  constructor
  · apply smul_peano_injective hX (n := 1) (by omega) (by omega)
    simpa only [one_smul, peanoL_one] using h1
  · intro a b ha hb habX
    have h := hmul a b ha hb habX
    rw [Matrix.smul_mul, Matrix.mul_smul, peano_product a b ha hb,
      ← mul_smul] at h
    exact (smul_peano_injective hX (Nat.mul_pos ha hb) habX h).symm

/-- Cutoff compatibility identifies every finite coefficient with the value
at its smallest admissible cutoff. -/
theorem cutoff_coefficients_stabilize (cX : ℕ → ℕ → ℂ)
    (hcompat : ∀ n X Y : ℕ, n ≤ X → X ≤ Y → cX X n = cX Y n) :
    let c : ℕ → ℂ := fun n => cX n n
    ∀ n X : ℕ, n ≤ X → cX X n = c n := by
  dsimp only
  intro n X hnX
  exact (hcompat n n X (le_refl n) hnX).symm

/-- Stabilized positive-index coefficients are completely multiplicative on
the positive natural-number monoid. -/
theorem stabilized_coefficients_completely_multiplicative
    (cX : ℕ → ℕ → ℂ)
    (hcompat : ∀ n X Y : ℕ, n ≤ X → X ≤ Y → cX X n = cX Y n)
    (hone : ∀ X : ℕ, 0 < X → cX X 1 = 1)
    (hmul : ∀ X a b : ℕ, 0 < X → 1 ≤ a → 1 ≤ b → a * b ≤ X →
      cX X (a * b) = cX X a * cX X b) :
    let c : ℕ → ℂ := fun n => cX n n
    c 1 = 1 ∧ ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → c (a * b) = c a * c b := by
  dsimp only
  constructor
  · exact hone 1 (by omega)
  · intro a b ha hb
    have habpos : 0 < a * b := Nat.mul_pos ha hb
    have haab : a ≤ a * b := by nlinarith
    have hbab : b ≤ a * b := by nlinarith
    calc
      cX (a * b) (a * b) = cX (a * b) a * cX (a * b) b :=
        hmul (a * b) a b habpos ha hb (le_refl _)
      _ = cX a a * cX b b := by
        rw [hcompat a a (a * b) (le_refl a) haab,
          hcompat b b (a * b) (le_refl b) hbab]

/-- A completely multiplicative coefficient takes finite products to finite
products. -/
lemma complete_mul_finset_prod (c : ℕ → ℂ) (hc1 : c 1 = 1)
    (hcmul : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → c (a * b) = c a * c b)
    (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) :
    c (∏ n ∈ s, n) = ∏ n ∈ s, c n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hc1
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        hcmul a (∏ n ∈ s, n) (hs a (Finset.mem_insert_self _ _))
          (Finset.one_le_prod fun n hn => hs n (Finset.mem_insert_of_mem hn)),
        ih (fun n hn => hs n (Finset.mem_insert_of_mem hn))]

lemma weighted_peano_pairwise {X : ℕ} (c : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) :
    (s : Set ℕ).Pairwise (Commute on fun n => c n • peanoL X n) := by
  intro a ha b hb hab
  dsimp only [Function.onFun]
  exact ((peano_commute (hs a ha) (hs b hb)).smul_left _).smul_right _

/-- Product of scalar-weighted Peano histories. -/
lemma noncommProd_weighted_peano {X : ℕ} (c : ℕ → ℂ) (hc1 : c 1 = 1)
    (hcmul : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → c (a * b) = c a * c b)
    (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) :
    s.noncommProd (fun n => c n • peanoL X n)
      (weighted_peano_pairwise c s hs) =
      c (∏ n ∈ s, n) • peanoL X (∏ n ∈ s, n) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.noncommProd_empty, Finset.prod_empty, hc1,
      peanoL_one, one_smul]
  | @insert a s ha ih =>
      rw [Finset.noncommProd_insert_of_notMem s a _ _ ha,
        Finset.prod_insert ha,
        ih (fun n hn => hs n (Finset.mem_insert_of_mem hn)),
        Matrix.smul_mul, Matrix.mul_smul, ← mul_smul,
        peano_product a (∏ n ∈ s, n)
          (hs a (Finset.mem_insert_self _ _))
          (Finset.one_le_prod fun n hn => hs n (Finset.mem_insert_of_mem hn)),
        hcmul a (∏ n ∈ s, n)
          (hs a (Finset.mem_insert_self _ _))
          (Finset.one_le_prod fun n hn => hs n (Finset.mem_insert_of_mem hn))]

noncomputable def weightedZeta (X : ℕ) (c : ℕ → ℂ) :
    Matrix (Fin X) (Fin X) ℂ :=
  ∑ n ∈ Finset.Icc 1 X, c n • peanoL X n

noncomputable def weightedMoebius (X : ℕ) (c : ℕ → ℂ) :
    Matrix (Fin X) (Fin X) ℂ :=
  ∑ n ∈ Finset.Icc 1 X,
    (((ArithmeticFunction.moebius n : ℤ) : ℂ) * c n) • peanoL X n

lemma zeta_anchor_ones {X : ℕ} (hX : 0 < X) :
    zetaX X *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 = fun _ => (1 : ℂ) := by
  funext j
  simp only [zetaX, Matrix.mulVec, dotProduct,
    Matrix.of_apply, Pi.single_apply]
  rw [Finset.sum_eq_single (⟨0, hX⟩ : Fin X)]
  · rw [if_pos rfl, mul_one,
      if_pos (show (((⟨0, hX⟩ : Fin X) : ℕ) + 1) ∣
        (j : ℕ) + 1 from by simp)]
  · intro k hk hne
    rw [if_neg (fun h => hne h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma weightedZeta_anchor {X : ℕ} (hX : 0 < X) (c : ℕ → ℂ) :
    weightedZeta X c *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 =
      fun j : Fin X => c ((j : ℕ) + 1) := by
  funext j
  let n := (j : ℕ) + 1
  have hn : 1 ≤ n := by omega
  have hnX : n ≤ X := by omega
  rw [weightedZeta, Matrix.sum_mulVec, Finset.sum_apply,
    Finset.sum_eq_single n]
  · rw [Matrix.smul_mulVec, Pi.smul_apply,
      peano_anchor_apply hX n hn j, if_pos rfl, smul_eq_mul, mul_one]
  · intro a haI hne
    rw [Matrix.smul_mulVec, Pi.smul_apply,
      peano_anchor_apply hX a (Finset.mem_Icc.mp haI).1 j,
      if_neg hne, smul_zero]
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨hn, hnX⟩) h

/-- Complete multiplicativity is exactly the diagonal intertwining relation
for a weighted multiplication history. -/
lemma weighted_peano_diag_intertwine {X a : ℕ} (c : ℕ → ℂ)
    (ha : 1 ≤ a)
    (hcmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → c (m * n) = c m * c n) :
    (c a • peanoL X a) * diagFn X c = diagFn X c * peanoL X a := by
  ext j i
  simp only [Matrix.smul_apply, smul_eq_mul,
    diagFn, peanoL, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.of_apply]
  by_cases hji : (j : ℕ) + 1 = a * ((i : ℕ) + 1)
  · rw [hji, hcmul a ((i : ℕ) + 1) ha (by omega)]
    ring
  · simp only [if_neg hji]
    ring

lemma weightedMoebius_diag_intertwine {X : ℕ} (c : ℕ → ℂ)
    (hcmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → c (m * n) = c m * c n) :
    weightedMoebius X c * diagFn X c =
      diagFn X c *
        (∑ n ∈ Finset.Icc 1 X,
          ((ArithmeticFunction.moebius n : ℤ) : ℂ) • peanoL X n) := by
  rw [weightedMoebius, Matrix.sum_mul, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  rw [Matrix.smul_mul, Matrix.mul_smul]
  rw [← smul_smul, ← Matrix.smul_mul,
    weighted_peano_diag_intertwine c hn1 hcmul]

/-- The weighted Möbius history is the full two-sided inverse of the weighted
zeta history. -/
theorem weighted_moebius_inverse {X : ℕ} (hX : 0 < X) (c : ℕ → ℂ)
    (hc1 : c 1 = 1)
    (hcmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → c (m * n) = c m * c n) :
    weightedMoebius X c * weightedZeta X c = 1 ∧
      weightedZeta X c * weightedMoebius X c = 1 := by
  let M0 : Matrix (Fin X) (Fin X) ℂ :=
    ∑ n ∈ Finset.Icc 1 X,
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) • peanoL X n
  let D := diagFn X c
  let η : Fin X → ℂ := Pi.single (⟨0, hX⟩ : Fin X) 1
  have hZa : weightedZeta X c *ᵥ η = D *ᵥ (zetaX X *ᵥ η) := by
    rw [weightedZeta_anchor hX, zeta_anchor_ones hX]
    funext j
    dsimp only [D]
    simp only [diagFn, Matrix.mulVec, dotProduct, Matrix.diagonal_apply,
      mul_one]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]
    · intro k hk hne
      rw [if_neg (Ne.symm hne)]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hMa : (weightedMoebius X c * weightedZeta X c) *ᵥ η = η := by
    rw [← Matrix.mulVec_mulVec, hZa, Matrix.mulVec_mulVec,
      weightedMoebius_diag_intertwine c hcmul]
    change (D * M0) *ᵥ (zetaX X *ᵥ η) = η
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc,
      (finite_moebius_matrix_inverse hX).1, Matrix.mul_one]
    funext j
    simp only [D, η, diagFn, Matrix.mulVec, dotProduct,
      Matrix.diagonal_apply, Pi.single_apply]
    rw [Finset.sum_eq_single (⟨0, hX⟩ : Fin X)]
    · by_cases hj : j = (⟨0, hX⟩ : Fin X)
      · subst j
        rw [if_pos rfl, if_pos rfl, mul_one, hc1]
      · rw [if_neg hj, if_neg hj, zero_mul]
    · intro k hk hne
      rw [if_neg hne, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hMcomm : ∀ b : ℕ, 1 ≤ b →
      weightedMoebius X c * peanoL X b =
        peanoL X b * weightedMoebius X c := by
    intro b hb
    exact arithmeticHistory_commutes_peano b hb
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ) * c n)
  have hZcomm : ∀ b : ℕ, 1 ≤ b →
      weightedZeta X c * peanoL X b =
        peanoL X b * weightedZeta X c := by
    intro b hb
    exact arithmeticHistory_commutes_peano b hb c
  have hMZcomm : ∀ b : ℕ, 1 ≤ b →
      (weightedMoebius X c * weightedZeta X c) * peanoL X b =
        peanoL X b * (weightedMoebius X c * weightedZeta X c) := by
    intro b hb
    calc
      _ = weightedMoebius X c * (weightedZeta X c * peanoL X b) :=
        Matrix.mul_assoc _ _ _
      _ = weightedMoebius X c * (peanoL X b * weightedZeta X c) := by
        rw [hZcomm b hb]
      _ = (weightedMoebius X c * peanoL X b) * weightedZeta X c := by
        rw [Matrix.mul_assoc]
      _ = (peanoL X b * weightedMoebius X c) * weightedZeta X c := by
        rw [hMcomm b hb]
      _ = _ := Matrix.mul_assoc _ _ _
  have hright : weightedMoebius X c * weightedZeta X c = 1 :=
    eq_of_peano_anchor_of_commutes hX _ 1 hMZcomm
      (fun _ _ => by simp) (by simpa only [Matrix.one_mulVec] using hMa)
  have hcomm : weightedMoebius X c * weightedZeta X c =
      weightedZeta X c * weightedMoebius X c := by
    rw [weightedMoebius, weightedZeta, Matrix.sum_mul, Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Matrix.smul_mul, Matrix.mul_smul]
    exact congrArg (fun A => (((ArithmeticFunction.moebius n : ℤ) : ℂ) * c n) • A)
      (arithmeticHistory_commutes_peano n (Finset.mem_Icc.mp hn).1 c).symm
  exact ⟨hright, hcomm ▸ hright⟩

lemma prime_subset_moebius_sum_complex (X n : ℕ) (hn : 1 ≤ n)
    (hnX : n ≤ X) :
    ∑ t ∈ (primesUpTo X).powerset,
      ((((-1 : ℤ) ^ t.card : ℤ) : ℂ) *
        (if (∏ p ∈ t, p) = n then 1 else 0)) =
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) := by
  have hcast := congrArg (Int.castRingHom ℂ)
    (prime_subset_moebius_sum X n hn hnX)
  have hcast_apply : ∀ z : ℤ,
      (Int.castRingHom ℂ) z = (z : ℂ) := fun z => rfl
  simp only [map_sum, map_mul, apply_ite] at hcast
  simpa only [hcast_apply, Int.cast_one, Int.cast_zero, mul_ite] using hcast

lemma prime_subset_weighted_moebius_sum (X n : ℕ) (hn : 1 ≤ n)
    (hnX : n ≤ X) (c : ℕ → ℂ) :
    ∑ t ∈ (primesUpTo X).powerset,
      ((((-1 : ℤ) ^ t.card : ℤ) : ℂ) * c (∏ p ∈ t, p) *
        (if (∏ p ∈ t, p) = n then 1 else 0)) =
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) * c n := by
  calc
    _ = c n * ∑ t ∈ (primesUpTo X).powerset,
        ((((-1 : ℤ) ^ t.card : ℤ) : ℂ) *
          (if (∏ p ∈ t, p) = n then 1 else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      by_cases htn : (∏ p ∈ t, p) = n
      · rw [if_pos htn, htn]
        ring
      · rw [if_neg htn]
        ring
    _ = c n * ((ArithmeticFunction.moebius n : ℤ) : ℂ) := by
      rw [prime_subset_moebius_sum_complex X n hn hnX]
    _ = _ := by ring

/-- The product of the weighted squarefree local factors is the weighted
Möbius history. -/
theorem finite_weighted_prime_moebius_product {X : ℕ} (hX : 0 < X)
    (c : ℕ → ℂ) (hc1 : c 1 = 1)
    (hcmul : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → c (a * b) = c a * c b) :
    (primesUpTo X).noncommProd (fun p => 1 - c p • peanoL X p)
      (one_sub_pairwise_of_commute_all (primesUpTo X)
        (fun p => c p • peanoL X p)
        (fun _ _ => (peano_commute_all (X := X)).smul_left _ |>.smul_right _)) =
      weightedMoebius X c := by
  classical
  let Q : Matrix (Fin X) (Fin X) ℂ :=
    (primesUpTo X).noncommProd (fun p => 1 - c p • peanoL X p)
      (one_sub_pairwise_of_commute_all (primesUpTo X)
        (fun p => c p • peanoL X p)
        (fun a b => (peano_commute_all (X := X)).smul_left _ |>.smul_right _))
  let M := weightedMoebius X c
  have hQexp : Q = ∑ t ∈ (primesUpTo X).powerset,
      (-1 : ℤ) ^ t.card •
        (c (∏ p ∈ t, p) • peanoL X (∏ p ∈ t, p)) := by
    dsimp only [Q]
    calc
      _ = ∑ t ∈ (primesUpTo X).powerset,
          (-1 : ℤ) ^ t.card •
            t.noncommProd (fun p => c p • peanoL X p)
              (pairwise_of_commute_all t
                (fun p => c p • peanoL X p)
                (fun a b => ((peano_commute_all (X := X)).smul_left _).smul_right _)) :=
        noncommProd_one_sub_expansion (primesUpTo X)
          (fun p => c p • peanoL X p)
          (fun a b => ((peano_commute_all (X := X)).smul_left _).smul_right _)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [noncommProd_weighted_peano c hc1 hcmul]
        intro p hp
        exact ((Finset.mem_filter.mp
          (Finset.mem_powerset.mp ht hp)).2).one_le
  have hQcomm : ∀ b : ℕ, 1 ≤ b →
      Q * peanoL X b = peanoL X b * Q := by
    intro b hb
    dsimp only [Q]
    exact (Finset.noncommProd_commute (primesUpTo X)
      (fun p => 1 - c p • peanoL X p) _ (peanoL X b)
      (fun p hp =>
        (Commute.one_right _).sub_right
          ((peano_commute hb
            ((Finset.mem_filter.mp hp).2).one_le).smul_right _))).symm.eq
  have hMcomm : ∀ b : ℕ, 1 ≤ b →
      M * peanoL X b = peanoL X b * M := by
    intro b hb
    exact arithmeticHistory_commutes_peano b hb
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ) * c n)
  have hanchor : Q *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 =
      M *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 := by
    funext j
    let n := (j : ℕ) + 1
    have hn : 1 ≤ n := by omega
    have hnX : n ≤ X := by omega
    have hQj : (Q *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) j =
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) * c n := by
      rw [hQexp, Matrix.sum_mulVec, Finset.sum_apply]
      have hterm : ∀ t ∈ (primesUpTo X).powerset,
          (((-1 : ℤ) ^ t.card •
              (c (∏ p ∈ t, p) • peanoL X (∏ p ∈ t, p))) *ᵥ
              Pi.single (⟨0, hX⟩ : Fin X) 1) j =
            ((((-1 : ℤ) ^ t.card : ℤ) : ℂ) * c (∏ p ∈ t, p) *
              if (∏ p ∈ t, p) = n then 1 else 0) := by
        intro t ht
        have htpos : 1 ≤ ∏ p ∈ t, p :=
          Finset.one_le_prod fun p hp =>
            ((Finset.mem_filter.mp
              (Finset.mem_powerset.mp ht hp)).2).one_le
        rw [Matrix.smul_mulVec, Pi.smul_apply,
          Matrix.smul_mulVec, Pi.smul_apply,
          peano_anchor_apply hX _ htpos j]
        simp only [zsmul_eq_mul, smul_eq_mul]
        dsimp only [n]
        ring
      rw [Finset.sum_congr rfl hterm,
        prime_subset_weighted_moebius_sum X n hn hnX c]
    have hMj : (M *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) j =
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) * c n := by
      dsimp only [M, weightedMoebius]
      rw [Matrix.sum_mulVec, Finset.sum_apply,
        Finset.sum_eq_single n]
      · rw [Matrix.smul_mulVec, Pi.smul_apply,
          peano_anchor_apply hX n hn j, if_pos rfl, smul_eq_mul, mul_one]
      · intro a haI hne
        rw [Matrix.smul_mulVec, Pi.smul_apply,
          peano_anchor_apply hX a (Finset.mem_Icc.mp haI).1 j,
          if_neg hne, smul_zero]
      · intro h
        exact absurd (Finset.mem_Icc.mpr ⟨hn, hnX⟩) h
    exact hQj.trans hMj.symm
  exact eq_of_peano_anchor_of_commutes hX Q M hQcomm hMcomm hanchor

lemma weighted_prime_factor_nilpotent {X p : ℕ} (hX : 0 < X)
    (hp : p.Prime) (z : ℂ) :
    (z • peanoL X p) ^ X = 0 := by
  rw [smul_pow, (ar_finite_euler hX).2.1 p hp.two_le, smul_zero]

lemma weighted_prime_factor_inverse_eq_geom {X p : ℕ} (hX : 0 < X)
    (hp : p.Prime) (z : ℂ) :
    (1 - z • peanoL X p)⁻¹ =
      ∑ k ∈ Finset.range X, (z • peanoL X p) ^ k := by
  apply Matrix.inv_eq_right_inv
  exact ((ar_finite_euler hX).1 (z • peanoL X p) X
    (weighted_prime_factor_nilpotent hX hp z)).1

/-- Exact weighted Euler product for every completely multiplicative positive
coefficient family. -/
theorem finite_weighted_euler_product {X : ℕ} (hX : 0 < X)
    (c : ℕ → ℂ) (hc1 : c 1 = 1)
    (hcmul : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → c (a * b) = c a * c b) :
    (primesUpTo X).noncommProd
        (fun p => (1 - c p • peanoL X p)⁻¹)
        (by
          intro a ha b hb _hab
          have hpa : a.Prime := (Finset.mem_filter.mp ha).2
          have hpb : b.Prime := (Finset.mem_filter.mp hb).2
          dsimp only [Function.onFun]
          rw [weighted_prime_factor_inverse_eq_geom hX hpa,
            weighted_prime_factor_inverse_eq_geom hX hpb]
          exact truncatedGeom_commute _ _ X
            (((peano_commute hpa.one_le hpb.one_le).smul_left _).smul_right _)) =
      weightedZeta X c := by
  classical
  let S := primesUpTo X
  let N : ℕ → Matrix (Fin X) (Fin X) ℂ := fun p => c p • peanoL X p
  let q : ℕ → Matrix (Fin X) (Fin X) ℂ := fun p => 1 - N p
  let g : ℕ → Matrix (Fin X) (Fin X) ℂ := fun p =>
    ∑ k ∈ Finset.range X, (N p) ^ k
  have hp : ∀ p ∈ S, p.Prime := by
    intro p hpS
    exact (Finset.mem_filter.mp hpS).2
  have hNN : ∀ a b : ℕ, Commute (N a) (N b) := by
    intro a b
    exact ((peano_commute_all (X := X)).smul_left _).smul_right _
  have hqq : (S : Set ℕ).Pairwise (Commute on q) :=
    one_sub_pairwise_of_commute_all S N hNN
  have hgg : (S : Set ℕ).Pairwise (Commute on g) := by
    intro a ha b hb hab
    exact truncatedGeom_commute _ _ X (hNN a b)
  have hgq : (S : Set ℕ).Pairwise fun a b => Commute (g a) (q b) := by
    intro a ha b hb hab
    have hgb : Commute (g a) (N b) :=
      truncatedGeom_commute_right _ _ X (hNN a b)
    exact (Commute.one_right _).sub_right hgb
  have hlocal : ∀ p ∈ S, q p * g p = 1 := by
    intro p hpS
    exact ((ar_finite_euler hX).1 (N p) X
      (weighted_prime_factor_nilpotent hX (hp p hpS) (c p))).1
  have hQE : S.noncommProd q hqq * S.noncommProd g hgg = 1 := by
    rw [← Finset.noncommProd_mul_distrib q g hqq hgg hgq]
    calc
      S.noncommProd (q * g)
          (Finset.noncommProd_mul_distrib_aux hqq hgg hgq) =
          S.noncommProd (fun _ => 1)
            (pairwise_of_commute_all S (fun _ =>
              (1 : Matrix (Fin X) (Fin X) ℂ)) fun _ _ => Commute.refl 1) := by
            apply Finset.noncommProd_congr rfl
            intro p hpS
            exact hlocal p hpS
      _ = 1 := by
        rw [Finset.noncommProd_eq_pow_card _ _ _ 1 (fun _ _ => rfl), one_pow]
  have hQZ : S.noncommProd q hqq * weightedZeta X c = 1 := by
    change (primesUpTo X).noncommProd
      (fun p => 1 - c p • peanoL X p) _ * weightedZeta X c = 1
    rw [finite_weighted_prime_moebius_product hX c hc1 hcmul]
    exact (weighted_moebius_inverse hX c hc1 hcmul).1
  have hGZ : S.noncommProd g hgg = weightedZeta X c :=
    Matrix.right_inv_eq_right_inv hQE hQZ
  calc
    (primesUpTo X).noncommProd
        (fun p => (1 - c p • peanoL X p)⁻¹) _ =
        S.noncommProd g hgg := by
      apply Finset.noncommProd_congr rfl
      intro p hpS
      apply Matrix.inv_eq_right_inv
      exact hlocal p hpS
    _ = weightedZeta X c := hGZ

/-- Converse construction: every completely multiplicative scalar family
produces natural multiplicative Peano loadings with the required anchor. -/
theorem scalar_peano_loading_converse {X : ℕ} (hX : 0 < X)
    (c : ℕ → ℂ)
    (hcmul : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → c (a * b) = c a * c b)
    (a : ℕ) (ha : 1 ≤ a) :
    ((c a • peanoL X a) * recS X =
        (recS X) ^ a * (c a • peanoL X a)) ∧
    ((c a • peanoL X a) *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 =
        c a • ((recS X) ^ (a - 1) *ᵥ
          Pi.single (⟨0, hX⟩ : Fin X) 1)) ∧
    (∀ b : ℕ, 1 ≤ b →
      (c a • peanoL X a) * (c b • peanoL X b) =
        c (a * b) • peanoL X (a * b)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, peanoL_covariance a ha]
  · rw [Matrix.smul_mulVec, peanoL_anchor hX a ha]
  · intro b hb
    rw [Matrix.smul_mul, Matrix.mul_smul, ← mul_smul,
      peano_product a b ha hb, hcmul a b ha hb]

/-- Unit prime parameters recover the deterministic unweighted zeta history. -/
theorem prime_normalization_recovers_zeta {X : ℕ} (hX : 0 < X)
    (c : ℕ → ℂ) (hc1 : c 1 = 1)
    (hcmul : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → c (a * b) = c a * c b)
    (hprime : ∀ p : ℕ, p.Prime → p ≤ X → c p = 1) :
    weightedZeta X c = zetaX X := by
  rw [← finite_weighted_euler_product hX c hc1 hcmul,
    ← finite_euler_matrix_product hX]
  apply Finset.noncommProd_congr rfl
  intro p hp
  have hp' := (Finset.mem_filter.mp hp)
  rw [hprime p hp'.2 (Finset.mem_Icc.mp hp'.1).2, one_smul]

/-- Conversely, equality with the deterministic zeta history fixes every
surviving coefficient (and hence every surviving prime parameter) to one. -/
theorem zeta_equality_forces_normalization {X : ℕ} (hX : 0 < X)
    (c : ℕ → ℂ) (hZ : weightedZeta X c = zetaX X) :
    ∀ n : ℕ, 1 ≤ n → n ≤ X → c n = 1 := by
  intro n hn hnX
  let j : Fin X := ⟨n - 1, by omega⟩
  have ha := congrArg
    (fun A : Matrix (Fin X) (Fin X) ℂ =>
      (A *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) j) hZ
  rw [weightedZeta_anchor hX, zeta_anchor_ones hX] at ha
  simpa [j, show n - 1 + 1 = n by omega] using ha

end NCG
