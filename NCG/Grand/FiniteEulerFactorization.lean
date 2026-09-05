/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteEulerMatrixConsequences
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Data.Nat.Squarefree

/-!
# Finite Euler factorization

Finite noncommutative Euler products for truncated Peano histories, including
the Möbius factorization, terminating local inverses, and the exact
prime-power expansion of the Euler logarithm.
-/

open Matrix
open scoped Function

namespace NCG

def primesUpTo (X : ℕ) : Finset ℕ :=
  (Finset.Icc 2 X).filter Nat.Prime

lemma peano_commute {X a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Commute (peanoL X a) (peanoL X b) := by
  rw [Commute]
  exact (peano_product a b ha hb).trans <|
    (Nat.mul_comm a b ▸ (peano_product b a hb ha).symm)

lemma peanoL_one (X : ℕ) : peanoL X 1 = 1 := by
  ext i j
  simp [peanoL, Matrix.one_apply, Fin.ext_iff]

lemma peano_pairwise {X : ℕ} (s : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) :
    (s : Set ℕ).Pairwise (Commute on peanoL X) := by
  intro a ha b hb _
  exact peano_commute (hs a ha) (hs b hb)

lemma noncommProd_peano_eq_peano_prod {X : ℕ} (s : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) :
    s.noncommProd (peanoL X)
      (peano_pairwise s hs) =
      peanoL X (∏ n ∈ s, n) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.noncommProd_empty, Finset.prod_empty, peanoL_one]
  | @insert a s ha ih =>
      rw [Finset.noncommProd_insert_of_notMem s a (peanoL X) _ ha,
        Finset.prod_insert ha,
        ih (fun n hn => hs n (Finset.mem_insert_of_mem hn)),
        peano_product a (∏ n ∈ s, n) (hs a (Finset.mem_insert_self _ _))]
      exact Finset.one_le_prod fun n hn => hs n (Finset.mem_insert_of_mem hn)

lemma pairwise_of_commute_all {R ι : Type*} [Ring R]
    (s : Finset ι) (f : ι → R) (hcomm : ∀ a b, Commute (f a) (f b)) :
    (s : Set ι).Pairwise (Commute on f) := by
  intro a _ b _ _
  exact hcomm a b

lemma one_sub_pairwise_of_commute_all {R ι : Type*} [Ring R]
    (s : Finset ι) (f : ι → R) (hcomm : ∀ a b, Commute (f a) (f b)) :
    (s : Set ι).Pairwise (Commute on fun i => 1 - f i) := by
  intro a _ b _ _
  exact (Commute.one_left _).sub_left
    ((Commute.one_right _).sub_right (hcomm a b))

/-- Inclusion-exclusion expansion of a commuting noncommutative product. -/
lemma noncommProd_one_sub_expansion {R ι : Type*} [Ring R]
    (s : Finset ι) (f : ι → R)
    (hcomm : ∀ a b, Commute (f a) (f b)) :
    s.noncommProd (fun i => 1 - f i)
      (one_sub_pairwise_of_commute_all s f hcomm) =
      ∑ t ∈ s.powerset,
        (-1 : ℤ) ^ t.card •
          t.noncommProd f (pairwise_of_commute_all t f hcomm) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.noncommProd_empty, Finset.powerset_empty,
        Finset.sum_singleton, Finset.card_empty, pow_zero, one_smul,
        Finset.noncommProd_empty]
  | @insert a s ha ih =>
      rw [Finset.noncommProd_insert_of_notMem s a _ _ ha,
        Finset.powerset_insert,
        Finset.sum_union]
      · rw [Finset.sum_image]
        · rw [ih, sub_mul, one_mul, Finset.mul_sum]
          have hterm : ∀ t ∈ s.powerset,
              (-1 : ℤ) ^ (insert a t).card •
                  (insert a t).noncommProd f
                    (pairwise_of_commute_all (insert a t) f hcomm) =
                -(f a * ((-1 : ℤ) ^ t.card •
                  t.noncommProd f (pairwise_of_commute_all t f hcomm))) := by
            intro t ht
            have hat : a ∉ t := fun hat =>
              ha (Finset.mem_powerset.mp ht hat)
            rw [Finset.card_insert_of_notMem hat, pow_succ,
              Finset.noncommProd_insert_of_notMem t a f _ hat]
            simp
            change (((-1 : R) ^ t.card) *
                (f a * t.noncommProd f
                  (pairwise_of_commute_all t f hcomm))) =
              f a * (((-1 : R) ^ t.card) *
                t.noncommProd f (pairwise_of_commute_all t f hcomm))
            have hc : Commute ((-1 : R) ^ t.card) (f a) :=
              ((Commute.one_left (f a)).neg_left).pow_left _
            calc
              ((-1 : R) ^ t.card) *
                    (f a * t.noncommProd f
                      (pairwise_of_commute_all t f hcomm)) =
                  (((-1 : R) ^ t.card) * f a) *
                    t.noncommProd f
                      (pairwise_of_commute_all t f hcomm) := by
                        rw [mul_assoc]
              _ = (f a * ((-1 : R) ^ t.card)) *
                    t.noncommProd f
                      (pairwise_of_commute_all t f hcomm) := by
                        rw [hc.eq]
              _ = f a * (((-1 : R) ^ t.card) *
                    t.noncommProd f
                      (pairwise_of_commute_all t f hcomm)) := by
                        rw [mul_assoc]
          rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
          abel
        · intro t ht u hu htu
          have hat : a ∉ t := fun hat =>
            ha (Finset.mem_powerset.mp ht hat)
          have hau : a ∉ u := fun hau =>
            ha (Finset.mem_powerset.mp hu hau)
          simpa [Finset.erase_insert, hat, hau] using
            congrArg (fun v : Finset ι => v.erase a) htu
      · exact Finset.disjoint_left.2 fun t ht hti => by
          rw [Finset.mem_image] at hti
          obtain ⟨u, hu, rfl⟩ := hti
          exact ha (Finset.mem_powerset.mp ht (Finset.mem_insert_self _ _))

lemma prime_subset_moebius_sum (X n : ℕ) (hn : 1 ≤ n) (hnX : n ≤ X) :
    ∑ t ∈ (primesUpTo X).powerset,
      ((-1 : ℤ) ^ t.card) * (if (∏ p ∈ t, p) = n then 1 else 0) =
        ArithmeticFunction.moebius n := by
  classical
  by_cases hsq : Squarefree n
  · let t0 := n.primeFactors
    have ht0 : t0 ∈ (primesUpTo X).powerset := by
      rw [Finset.mem_powerset]
      intro p hp
      have hpf := Nat.mem_primeFactors.mp hp
      have hpX : p ≤ X :=
        (Nat.le_of_dvd (by omega) hpf.2.1).trans hnX
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨hpf.1.two_le, hpX⟩, hpf.1⟩
    rw [Finset.sum_eq_single t0]
    · rw [if_pos (Nat.prod_primeFactors_of_squarefree hsq)]
      have hcard : t0.card = ArithmeticFunction.cardFactors n := by
        rw [ArithmeticFunction.cardFactors_apply]
        exact List.toFinset_card_of_nodup hsq.nodup_primeFactorsList
      rw [hcard, mul_one, ArithmeticFunction.moebius_apply_of_squarefree hsq]
    · intro t ht hne
      have hprime : ∀ p ∈ t, p.Prime := by
        intro p hp
        exact (Finset.mem_filter.mp
          (Finset.mem_powerset.mp ht hp)).2
      rw [if_neg]
      · simp
      · intro hprod
        apply hne
        dsimp [t0]
        rw [← hprod]
        exact (Nat.primeFactors_prod hprime).symm
    · intro ht
      exact absurd ht0 ht
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    apply Finset.sum_eq_zero
    intro t ht
    rw [if_neg]
    · simp
    · intro hprod
      apply hsq
      rw [← hprod]
      apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro p hp q hq hpq
        change IsRelPrime p q
        rw [← Nat.coprime_iff_isRelPrime]
        have hpp : p.Prime := (Finset.mem_filter.mp
          (Finset.mem_powerset.mp ht hp)).2
        have hqp : q.Prime := (Finset.mem_filter.mp
          (Finset.mem_powerset.mp ht hq)).2
        exact (Nat.coprime_primes hpp hqp).mpr hpq
      · intro p hp
        exact ((Finset.mem_filter.mp
          (Finset.mem_powerset.mp ht hp)).2).squarefree

lemma peano_commute_all {X a b : ℕ} :
    Commute (peanoL X a) (peanoL X b) := by
  by_cases ha : a = 0
  · subst a
    have hzero : peanoL X 0 = 0 := by
      ext i j
      simp [peanoL]
    rw [hzero]
    exact Commute.zero_left _
  by_cases hb : b = 0
  · subst b
    have hzero : peanoL X 0 = 0 := by
      ext i j
      simp [peanoL]
    rw [hzero]
    exact Commute.zero_right _
  exact peano_commute (Nat.one_le_iff_ne_zero.mpr ha)
    (Nat.one_le_iff_ne_zero.mpr hb)

lemma peano_anchor_apply {X : ℕ} (hX : 0 < X) (a : ℕ)
    (ha : 1 ≤ a) (j : Fin X) :
    (peanoL X a *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) j =
      if a = (j : ℕ) + 1 then 1 else 0 := by
  rw [mulVec_single_col, peanoL, Matrix.of_apply]
  simp only [mul_one]
  by_cases h : a = (j : ℕ) + 1
  · rw [if_pos h, if_pos]
    omega
  · rw [if_neg h, if_neg]
    omega

/-- The product of the finite prime factors is exactly the full Möbius
history. -/
theorem finite_prime_mobius_product {X : ℕ} (hX : 0 < X) :
    (primesUpTo X).noncommProd (fun p => 1 - peanoL X p)
      (one_sub_pairwise_of_commute_all (primesUpTo X) (peanoL X)
        fun a b => peano_commute_all) =
      ∑ a ∈ Finset.Icc 1 X,
        ((ArithmeticFunction.moebius a : ℤ) : ℂ) • peanoL X a := by
  let Q : Matrix (Fin X) (Fin X) ℂ :=
    (primesUpTo X).noncommProd (fun p => 1 - peanoL X p)
      (one_sub_pairwise_of_commute_all (primesUpTo X) (peanoL X)
        fun a b => peano_commute_all)
  let M : Matrix (Fin X) (Fin X) ℂ :=
    ∑ a ∈ Finset.Icc 1 X,
      ((ArithmeticFunction.moebius a : ℤ) : ℂ) • peanoL X a
  have hQexp : Q = ∑ t ∈ (primesUpTo X).powerset,
      (-1 : ℤ) ^ t.card • peanoL X (∏ p ∈ t, p) := by
    dsimp only [Q]
    calc
      _ = ∑ t ∈ (primesUpTo X).powerset,
          (-1 : ℤ) ^ t.card •
            t.noncommProd (peanoL X)
              (pairwise_of_commute_all t (peanoL X)
                (fun a b => peano_commute_all)) :=
        noncommProd_one_sub_expansion (primesUpTo X) (peanoL X)
          (fun a b => peano_commute_all)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [noncommProd_peano_eq_peano_prod]
        intro p hp
        exact ((Finset.mem_filter.mp
          (Finset.mem_powerset.mp ht hp)).2).one_le
  have hQcomm : ∀ b : ℕ, 1 ≤ b →
      Q * peanoL X b = peanoL X b * Q := by
    intro b hb
    rw [hQexp, Matrix.sum_mul, Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Matrix.smul_mul, Matrix.mul_smul]
    rw [(peano_commute_all (X := X)).eq]
  have hMcomm : ∀ b : ℕ, 1 ≤ b →
      M * peanoL X b = peanoL X b * M := by
    intro b hb
    exact arithmeticHistory_commutes_peano b hb
      (fun a => ((ArithmeticFunction.moebius a : ℤ) : ℂ))
  have hanchor : Q *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 =
      M *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 := by
    funext j
    let n := (j : ℕ) + 1
    have hn : 1 ≤ n := by omega
    have hnX : n ≤ X := by omega
    have hQj : (Q *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) j =
        (ArithmeticFunction.moebius n : ℂ) := by
      rw [hQexp, Matrix.sum_mulVec, Finset.sum_apply]
      have hterm : ∀ t ∈ (primesUpTo X).powerset,
          (((-1 : ℤ) ^ t.card • peanoL X (∏ p ∈ t, p)) *ᵥ
              Pi.single (⟨0, hX⟩ : Fin X) 1) j =
            ((((-1 : ℤ) ^ t.card : ℤ) : ℂ) *
              if (∏ p ∈ t, p) = n then 1 else 0) := by
        intro t ht
        have htpos : 1 ≤ ∏ p ∈ t, p :=
          Finset.one_le_prod fun p hp =>
            ((Finset.mem_filter.mp
              (Finset.mem_powerset.mp ht hp)).2).one_le
        rw [Matrix.smul_mulVec, Pi.smul_apply,
          peano_anchor_apply hX _ htpos j]
        simp only [zsmul_eq_mul]
        rfl
      rw [Finset.sum_congr rfl hterm]
      have hcast := congrArg (Int.castRingHom ℂ)
        (prime_subset_moebius_sum X n hn hnX)
      have hcast_apply : ∀ z : ℤ,
          (Int.castRingHom ℂ) z = (z : ℂ) := fun z => rfl
      simp only [map_sum, map_mul, apply_ite] at hcast
      simpa only [hcast_apply, Int.cast_one, Int.cast_zero, mul_ite] using hcast
    have hMj : (M *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1) j =
        (ArithmeticFunction.moebius n : ℂ) := by
      dsimp only [M]
      rw [Matrix.sum_mulVec, Finset.sum_apply]
      rw [Finset.sum_eq_single n]
      · rw [Matrix.smul_mulVec, Pi.smul_apply,
          peano_anchor_apply hX n hn j, if_pos rfl]
        simp
      · intro a haI hne
        rw [Matrix.smul_mulVec, Pi.smul_apply,
          peano_anchor_apply hX a (Finset.mem_Icc.mp haI).1 j,
          if_neg hne]
        simp
      · intro hnmem
        exact absurd (Finset.mem_Icc.mpr ⟨hn, hnX⟩) hnmem
    exact hQj.trans hMj.symm
  exact eq_of_peano_anchor_of_commutes hX Q M hQcomm hMcomm hanchor

/-- Truncated geometric series preserve commutation. -/
lemma truncatedGeom_commute {R : Type*} [Ring R] (A B : R) (m : ℕ)
    (h : Commute A B) :
    Commute (∑ k ∈ Finset.range m, A ^ k)
      (∑ l ∈ Finset.range m, B ^ l) := by
  exact Commute.sum_left _ _ _ fun k _ =>
    Commute.sum_right _ _ _ fun l _ =>
      (h.pow_left k).pow_right l

/-- A truncated geometric series in one element commutes with any element
commuting with its generator. -/
lemma truncatedGeom_commute_right {R : Type*} [Ring R] (A B : R) (m : ℕ)
    (h : Commute A B) :
    Commute (∑ k ∈ Finset.range m, A ^ k) B := by
  exact Commute.sum_left _ _ _ fun k _ => h.pow_left k

/-- Each local prime inverse is exactly its terminating geometric series. -/
lemma prime_factor_inverse_eq_geom {X p : ℕ} (hX : 0 < X)
    (hp : p.Prime) :
    (1 - peanoL X p)⁻¹ =
      ∑ k ∈ Finset.range X, peanoL X p ^ k := by
  apply Matrix.inv_eq_right_inv
  exact ((ar_finite_euler hX).1 (peanoL X p) X
    ((ar_finite_euler hX).2.1 p hp.two_le)).1

/-- Exact finite Euler product: the product of the local prime inverses is
the divisor-incidence matrix.  All products are finite, and every inverse is
the terminating nilpotent geometric series. -/
theorem finite_euler_matrix_product {X : ℕ} (hX : 0 < X) :
    (primesUpTo X).noncommProd
        (fun p => (1 - peanoL X p)⁻¹)
        (by
          intro a ha b hb hab
          have hpa : a.Prime := (Finset.mem_filter.mp ha).2
          have hpb : b.Prime := (Finset.mem_filter.mp hb).2
          dsimp only [Function.onFun]
          rw [prime_factor_inverse_eq_geom hX hpa,
            prime_factor_inverse_eq_geom hX hpb]
          exact truncatedGeom_commute _ _ X
            (peano_commute hpa.one_le hpb.one_le)) = zetaX X := by
  classical
  let S := primesUpTo X
  let q : ℕ → Matrix (Fin X) (Fin X) ℂ := fun p => 1 - peanoL X p
  let g : ℕ → Matrix (Fin X) (Fin X) ℂ := fun p =>
    ∑ k ∈ Finset.range X, peanoL X p ^ k
  have hp : ∀ p ∈ S, p.Prime := by
    intro p hpS
    exact (Finset.mem_filter.mp hpS).2
  have hqq : (S : Set ℕ).Pairwise (Commute on q) := by
    intro a ha b hb hab
    exact (Commute.one_left _).sub_left
      ((Commute.one_right _).sub_right
        (peano_commute (hp a ha).one_le (hp b hb).one_le))
  have hgg : (S : Set ℕ).Pairwise (Commute on g) := by
    intro a ha b hb hab
    exact truncatedGeom_commute _ _ X
      (peano_commute (hp a ha).one_le (hp b hb).one_le)
  have hgq : (S : Set ℕ).Pairwise fun a b => Commute (g a) (q b) := by
    intro a ha b hb hab
    have hgb : Commute (g a) (peanoL X b) :=
      truncatedGeom_commute_right _ _ X
        (peano_commute (hp a ha).one_le (hp b hb).one_le)
    exact (Commute.one_right _).sub_right hgb
  have hlocal : ∀ p ∈ S, q p * g p = 1 := by
    intro p hpS
    exact ((ar_finite_euler hX).1 (peanoL X p) X
      ((ar_finite_euler hX).2.1 p (hp p hpS).two_le)).1
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
  have hQZ : S.noncommProd q hqq * zetaX X = 1 := by
    change (primesUpTo X).noncommProd (fun p => 1 - peanoL X p) _ *
      zetaX X = 1
    rw [finite_prime_mobius_product hX]
    exact (finite_moebius_matrix_inverse hX).1
  have hGZ : S.noncommProd g hgg = zetaX X :=
    Matrix.right_inv_eq_right_inv hQE hQZ
  calc
    (primesUpTo X).noncommProd
        (fun p => (1 - peanoL X p)⁻¹) _ =
        S.noncommProd g hgg := by
      apply Finset.noncommProd_congr rfl
      intro p hpS
      apply Matrix.inv_eq_right_inv
      exact hlocal p hpS
    _ = zetaX X := hGZ

/-- The finite set of prime/exponent pairs whose prime power survives the
cutoff.  Exponents and primes are explicitly bounded so the sum is literal. -/
def primePowerPairs (X : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 X).product (Finset.Icc 2 X)).filter fun kp =>
    kp.2.Prime ∧ kp.2 ^ kp.1 ≤ X

/-- On a genuine prime power the von Mangoldt/logarithm coefficient is the
reciprocal exponent. -/
lemma vonMangoldt_div_log_prime_pow {p k : ℕ} (hp : p.Prime)
    (hk : k ≠ 0) :
    ArithmeticFunction.vonMangoldt (p ^ k) / Real.log (p ^ k) =
      1 / (k : ℝ) := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp, Real.log_pow]
  have hpLog : Real.log p ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  field_simp

/-- Exact terminating prime-power expansion of the finite Euler logarithm. -/
theorem finite_euler_log_prime_power_expansion (X : ℕ) :
    logZop X =
      ∑ kp ∈ primePowerPairs X,
        (((1 / (kp.1 : ℝ) : ℝ) : ℂ) • peanoL X (kp.2 ^ kp.1)) := by
  classical
  let F : ℕ → Matrix (Fin X) (Fin X) ℂ := fun n =>
    ((ArithmeticFunction.vonMangoldt n / Real.log n : ℝ) : ℂ) • peanoL X n
  let G : ℕ × ℕ → Matrix (Fin X) (Fin X) ℂ := fun kp =>
    (((1 / (kp.1 : ℝ) : ℝ) : ℂ) • peanoL X (kp.2 ^ kp.1))
  rw [logZop]
  change (∑ n ∈ Finset.Icc 2 X, F n) = ∑ kp ∈ primePowerPairs X, G kp
  calc
    (∑ n ∈ Finset.Icc 2 X, F n) =
        ∑ n ∈ (Finset.Icc 2 X).filter IsPrimePow, F n := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro n hnI hnfilter
      have hpp : ¬ IsPrimePow n := by
        intro h
        exact hnfilter (Finset.mem_filter.mpr ⟨hnI, h⟩)
      dsimp only [F]
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
      simp
    _ = ∑ kp ∈ primePowerPairs X, G kp := by
      symm
      refine Finset.sum_bij (fun kp _ => kp.2 ^ kp.1) ?_ ?_ ?_ ?_
      · intro kp hkp
        rcases kp with ⟨k, p⟩
        have hkp' := Finset.mem_filter.mp hkp
        have hbase := Finset.mem_product.mp hkp'.1
        have hkI := Finset.mem_Icc.mp hbase.1
        have hpI := Finset.mem_Icc.mp hbase.2
        have hkpos : 1 ≤ k := by simpa using hkI.1
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨?_, hkp'.2.2⟩, ?_⟩
        · exact hkp'.2.1.two_le.trans
            (le_self_pow hkp'.2.1.one_le (Nat.ne_of_gt hkpos))
        · rw [isPrimePow_nat_iff]
          exact ⟨p, k, hkp'.2.1, hkpos, rfl⟩
      · intro kp₁ hkp₁ kp₂ hkp₂ heq
        rcases kp₁ with ⟨k₁, p₁⟩
        rcases kp₂ with ⟨k₂, p₂⟩
        have hkp₁' := Finset.mem_filter.mp hkp₁
        have hkp₂' := Finset.mem_filter.mp hkp₂
        have hbase₁ := Finset.mem_product.mp hkp₁'.1
        have hbase₂ := Finset.mem_product.mp hkp₂'.1
        have hk₁ := (Finset.mem_Icc.mp hbase₁.1).1
        have hk₂ := (Finset.mem_Icc.mp hbase₂.1).1
        have hk₁' : 1 ≤ k₁ := by simpa using hk₁
        have hk₂' : 1 ≤ k₂ := by simpa using hk₂
        have hpair := hkp₁'.2.1.pow_inj' hkp₂'.2.1
          (Nat.ne_of_gt hk₁') (Nat.ne_of_gt hk₂') heq
        exact Prod.ext hpair.2 hpair.1
      · intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc] at hn
        rw [isPrimePow_nat_iff] at hn
        obtain ⟨p, k, hp, hk, rfl⟩ := hn.2
        have hp_le_pow : p ≤ p ^ k := le_self_pow hp.one_le hk.ne'
        have hkX : k ≤ X := by
          exact (Nat.le_of_lt Nat.lt_two_pow_self).trans
            ((Nat.pow_le_pow_left hp.two_le k).trans hn.1.2)
        have hpX : p ≤ X := hp_le_pow.trans hn.1.2
        refine ⟨(k, p), ?_, rfl⟩
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨hk, hkX⟩,
            Finset.mem_Icc.mpr ⟨hp.two_le, hpX⟩⟩,
          ⟨hp, hn.1.2⟩⟩
      · intro kp hkp
        rcases kp with ⟨k, p⟩
        have hkp' := Finset.mem_filter.mp hkp
        have hbase := Finset.mem_product.mp hkp'.1
        have hk := (Finset.mem_Icc.mp hbase.1).1
        have hk' : 1 ≤ k := by simpa using hk
        have hp' : p.Prime := by simpa using hkp'.2.1
        dsimp only [G, F]
        rw [Nat.cast_pow]
        rw [vonMangoldt_div_log_prime_pow hp' (Nat.ne_of_gt hk')]

end NCG
