/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The Cramér lower bound: tilted change of measure
  (missing large-deviations machinery; `thm:deficiency-rate-function`,
   GR_emergence)

The matching lower half of the finite-alphabet Cramér principle:

* `path_prod_factorization` — the inhomogeneous product formula
  `Σ_ω Π_i F_i(ω_i) = Π_i (Σ_a F_i(a))`;
* `change_of_measure_bound` — on any event where `S_n ≤ s`, the
  original probability dominates
  `e^{-χs}·M(χ)ⁿ·(tilted probability)`;
* `tilted_second_moment` — under the tilted product law the centered
  record has second moment `n·v` (cross terms vanish);
* `tilted_chebyshev` — the finite Chebyshev bound;
* `cramer_lower_bound` — at an exposed point (`χ` with tilted mean
  `a`), `P(S_n ≥ n(a-δ)) ≥ ½·exp(-n(χ(a+δ) - Λ(χ)))` once
  `n ≥ 2v/δ²` — the exponential lower bound matching
  `NCG.cramer_upper_bound`.
-/

namespace NCG

/-- Inhomogeneous path-space factorization. -/
theorem path_prod_factorization {A : Type*} [Fintype A] (n : ℕ)
    (F : Fin n → A → ℝ) :
    (∑ ω : Fin n → A, ∏ i, F i (ω i)) = ∏ i, ∑ a, F i a := by
  classical
  induction n with
  | zero => simp
  | succ m ih =>
    have hsplit : (∑ ω : Fin (m + 1) → A, ∏ i, F i (ω i))
        = ∑ p : A × (Fin m → A),
            F 0 p.1 * ∏ i : Fin m, F i.succ (p.2 i) := by
      apply Fintype.sum_equiv (Fin.consEquiv fun _ => A).symm
      intro ω
      rw [Fin.prod_univ_succ]
      rfl
    rw [hsplit, Fintype.sum_prod_type]
    rw [show (∑ a : A, ∑ ω : Fin m → A,
          F 0 a * ∏ i : Fin m, F i.succ (ω i))
        = ∑ a : A, F 0 a * ∑ ω : Fin m → A,
            ∏ i : Fin m, F i.succ (ω i) from by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]]
    rw [← Finset.sum_mul, ih (fun i => F i.succ), Fin.prod_univ_succ]

/-- Change of measure: on an event with `S_n ≤ s`, the original
probability dominates the tilted probability at exponential cost. -/
theorem change_of_measure_bound {A : Type*} [Fintype A]
    (q : A → ℝ) (hq : ∀ a, 0 ≤ q a) (f : A → ℝ)
    (n : ℕ) (chi s : ℝ) (hchi : 0 ≤ chi)
    (hM : 0 < ∑ b, q b * Real.exp (chi * f b))
    (E : Set (Fin n → A)) [DecidablePred (· ∈ E)]
    (hE : ∀ ω ∈ E, (∑ k, f (ω k)) ≤ s) :
    Real.exp (-(chi * s)) * (∑ b, q b * Real.exp (chi * f b)) ^ n
        * (∑ ω ∈ Finset.univ.filter (· ∈ E),
            ∏ k, (q (ω k) * Real.exp (chi * f (ω k))
              / (∑ b, q b * Real.exp (chi * f b))))
      ≤ ∑ ω ∈ Finset.univ.filter (· ∈ E), ∏ k, q (ω k) := by
  classical
  set M : ℝ := ∑ b, q b * Real.exp (chi * f b) with hMdef
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω hω
  rw [Finset.mem_filter] at hω
  -- rewrite the tilted product
  have hprod : (∏ k, (q (ω k) * Real.exp (chi * f (ω k)) / M))
      = (∏ k, q (ω k)) * Real.exp (chi * ∑ k, f (ω k)) / M ^ n := by
    rw [show (fun k : Fin n => q (ω k) * Real.exp (chi * f (ω k)) / M)
      = fun k : Fin n => q (ω k) * Real.exp (chi * f (ω k)) * M⁻¹
      from by
        funext k
        rw [div_eq_mul_inv]]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, ← Real.exp_sum]
    rw [show (∑ k, chi * f (ω k)) = chi * ∑ k, f (ω k) from by
      rw [Finset.mul_sum]]
    rw [div_eq_mul_inv, inv_pow, Finset.card_univ, Fintype.card_fin]
  rw [hprod]
  have hMn : (0 : ℝ) < M ^ n := pow_pos hM n
  have hqprod : (0 : ℝ) ≤ ∏ k, q (ω k) :=
    Finset.prod_nonneg fun k _ => hq (ω k)
  calc Real.exp (-(chi * s)) * M ^ n
        * ((∏ k, q (ω k)) * Real.exp (chi * ∑ k, f (ω k)) / M ^ n)
      = (∏ k, q (ω k)) * (Real.exp (-(chi * s))
          * Real.exp (chi * ∑ k, f (ω k))) := by
        field_simp
  _ = (∏ k, q (ω k))
        * Real.exp (chi * (∑ k, f (ω k)) - chi * s) := by
        rw [← Real.exp_add, show -(chi * s)
            + chi * ∑ k, f (ω k)
          = chi * (∑ k, f (ω k)) - chi * s from by ring]
  _ ≤ (∏ k, q (ω k)) * 1 := by
        apply mul_le_mul_of_nonneg_left _ hqprod
        rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
        apply Real.exp_le_exp.mpr
        have := hE ω hω.2
        nlinarith [this, hchi]
  _ = ∏ k, q (ω k) := mul_one _

/-- Single-site marginal: under a product law, the expectation of a
one-site observable is the single-step expectation. -/
theorem path_expect_single {A : Type*} [Fintype A]
    {n : ℕ} (p : A → ℝ) (hsum : ∑ a, p a = 1) (g : A → ℝ)
    (j : Fin n) :
    (∑ ω : Fin n → A, (∏ k, p (ω k)) * g (ω j))
      = ∑ a, p a * g a := by
  classical
  have hpt : ∀ ω : Fin n → A,
      (∏ k, (if k = j then p (ω k) * g (ω k) else p (ω k)))
      = (∏ k, p (ω k)) * g (ω j) := by
    intro ω
    rw [← Finset.mul_prod_erase Finset.univ
      (fun k => if k = j then p (ω k) * g (ω k) else p (ω k))
      (Finset.mem_univ j), if_pos rfl]
    rw [← Finset.mul_prod_erase Finset.univ (fun k => p (ω k))
      (Finset.mem_univ j)]
    have herase : (∏ k ∈ Finset.univ.erase j,
        (if k = j then p (ω k) * g (ω k) else p (ω k)))
        = ∏ k ∈ Finset.univ.erase j, p (ω k) := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [if_neg (Finset.mem_erase.mp hk).1]
    rw [herase]
    ring
  rw [show (∑ ω : Fin n → A, (∏ k, p (ω k)) * g (ω j))
      = ∑ ω : Fin n → A,
        ∏ k, (if k = j then p (ω k) * g (ω k) else p (ω k)) from
    Finset.sum_congr rfl fun ω _ => (hpt ω).symm]
  rw [show (∑ ω : Fin n → A,
        ∏ k, (if k = j then p (ω k) * g (ω k) else p (ω k)))
      = ∏ i : Fin n, ∑ a, (if i = j then p a * g a else p a) from
    path_prod_factorization n
      (fun i a => if i = j then p a * g a else p a)]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun i => ∑ a, (if i = j then p a * g a else p a))
    (Finset.mem_univ j)]
  have hj : (∑ a, (if j = j then p a * g a else p a))
      = ∑ a, p a * g a := by
    apply Finset.sum_congr rfl
    intro a _
    rw [if_pos rfl]
  have hfac1 : ∀ i ∈ Finset.univ.erase j,
      (∑ a, (if i = j then p a * g a else p a)) = 1 := by
    intro i hi
    rw [show (∑ a, (if i = j then p a * g a else p a))
        = ∑ a, p a from Finset.sum_congr rfl fun a _ => by
      rw [if_neg (Finset.mem_erase.mp hi).1]]
    exact hsum
  have hrest : (∏ i ∈ Finset.univ.erase j,
      ∑ a, (if i = j then p a * g a else p a)) = 1 := by
    rw [Finset.prod_congr rfl hfac1]
    exact Finset.prod_const_one
  rw [hj, hrest, mul_one]

/-- Two-site marginal: under a product law, distinct sites are
independent. -/
theorem path_expect_pair {A : Type*} [Fintype A]
    {n : ℕ} (p : A → ℝ) (hsum : ∑ a, p a = 1) (g h : A → ℝ)
    {j k : Fin n} (hjk : j ≠ k) :
    (∑ ω : Fin n → A, (∏ i, p (ω i)) * (g (ω j) * h (ω k)))
      = (∑ a, p a * g a) * ∑ a, p a * h a := by
  classical
  have hkj1 : k ≠ j := fun hkj => hjk hkj.symm
  have hkmem : k ∈ Finset.univ.erase j :=
    Finset.mem_erase.mpr ⟨hkj1, Finset.mem_univ k⟩
  have hpt : ∀ ω : Fin n → A,
      (∏ i, (if i = j then p (ω i) * g (ω i)
        else if i = k then p (ω i) * h (ω i) else p (ω i)))
      = (∏ i, p (ω i)) * (g (ω j) * h (ω k)) := by
    intro ω
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => if i = j then p (ω i) * g (ω i)
        else if i = k then p (ω i) * h (ω i) else p (ω i))
      (Finset.mem_univ j), if_pos rfl]
    rw [← Finset.mul_prod_erase (Finset.univ.erase j)
      (fun i => if i = j then p (ω i) * g (ω i)
        else if i = k then p (ω i) * h (ω i) else p (ω i)) hkmem,
      if_neg hkj1, if_pos rfl]
    rw [← Finset.mul_prod_erase Finset.univ (fun i => p (ω i))
      (Finset.mem_univ j),
      ← Finset.mul_prod_erase (Finset.univ.erase j)
      (fun i => p (ω i)) hkmem]
    have herase : (∏ i ∈ (Finset.univ.erase j).erase k,
        (if i = j then p (ω i) * g (ω i)
          else if i = k then p (ω i) * h (ω i) else p (ω i)))
        = ∏ i ∈ (Finset.univ.erase j).erase k, p (ω i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hi1 := (Finset.mem_erase.mp hi).1
      have hi2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      rw [if_neg hi2, if_neg hi1]
    rw [herase]
    ring
  rw [show (∑ ω : Fin n → A, (∏ i, p (ω i)) * (g (ω j) * h (ω k)))
      = ∑ ω : Fin n → A,
        ∏ i, (if i = j then p (ω i) * g (ω i)
          else if i = k then p (ω i) * h (ω i) else p (ω i)) from
    Finset.sum_congr rfl fun ω _ => (hpt ω).symm]
  rw [show (∑ ω : Fin n → A,
        ∏ i, (if i = j then p (ω i) * g (ω i)
          else if i = k then p (ω i) * h (ω i) else p (ω i)))
      = ∏ i : Fin n, ∑ a, (if i = j then p a * g a
          else if i = k then p a * h a else p a) from
    path_prod_factorization n (fun i a => if i = j then p a * g a
      else if i = k then p a * h a else p a)]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun i => ∑ a, (if i = j then p a * g a
      else if i = k then p a * h a else p a))
    (Finset.mem_univ j)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase j)
    (fun i => ∑ a, (if i = j then p a * g a
      else if i = k then p a * h a else p a)) hkmem]
  have hj : (∑ a, (if j = j then p a * g a
      else if j = k then p a * h a else p a)) = ∑ a, p a * g a := by
    apply Finset.sum_congr rfl
    intro a _
    rw [if_pos rfl]
  have hk2 : (∑ a, (if k = j then p a * g a
      else if k = k then p a * h a else p a)) = ∑ a, p a * h a := by
    apply Finset.sum_congr rfl
    intro a _
    rw [if_neg hkj1, if_pos rfl]
  have hfac2 : ∀ i ∈ (Finset.univ.erase j).erase k,
      (∑ a, (if i = j then p a * g a
        else if i = k then p a * h a else p a)) = 1 := by
    intro i hi
    have hi1 := (Finset.mem_erase.mp hi).1
    have hi2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    rw [show (∑ a, (if i = j then p a * g a
        else if i = k then p a * h a else p a))
        = ∑ a, p a from Finset.sum_congr rfl fun a _ => by
      rw [if_neg hi2, if_neg hi1]]
    exact hsum
  have hrest : (∏ i ∈ (Finset.univ.erase j).erase k,
      ∑ a, (if i = j then p a * g a
        else if i = k then p a * h a else p a)) = 1 := by
    rw [Finset.prod_congr rfl hfac2]
    exact Finset.prod_const_one
  rw [hj, hk2, hrest, mul_one]

/-- Tilted second moment: the centered path record has second moment
`n·v` (cross terms vanish by independence). -/
theorem path_second_moment {A : Type*} [Fintype A]
    {n : ℕ} (p : A → ℝ) (hsum : ∑ a, p a = 1) (f : A → ℝ)
    (m : ℝ) (hm : ∑ a, p a * f a = m) :
    (∑ ω : Fin n → A, (∏ k, p (ω k))
        * ((∑ k, f (ω k)) - n * m) ^ 2)
      = n * ∑ a, p a * (f a - m) ^ 2 := by
  classical
  set g : A → ℝ := fun a => f a - m with hg
  have hgsum : (∑ a, p a * g a) = 0 := by
    rw [show (∑ a, p a * g a)
        = (∑ a, p a * f a) - m * ∑ a, p a from by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [hg]
      ring]
    rw [hm, hsum]
    ring
  have hcenter : ∀ ω : Fin n → A,
      (∑ k, f (ω k)) - n * m = ∑ k, g (ω k) := by
    intro ω
    rw [show (∑ k, g (ω k)) = ∑ k, (f (ω k) - m) from
      Finset.sum_congr rfl fun k _ => by rw [hg]]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hstep1 : (∑ ω : Fin n → A, (∏ k, p (ω k))
        * ((∑ k, f (ω k)) - n * m) ^ 2)
      = ∑ j : Fin n, ∑ k : Fin n, ∑ ω : Fin n → A,
          (∏ i, p (ω i)) * (g (ω j) * g (ω k)) := by
    rw [show (∑ ω : Fin n → A, (∏ k, p (ω k))
          * ((∑ k, f (ω k)) - n * m) ^ 2)
        = ∑ ω : Fin n → A, ∑ j : Fin n, ∑ k : Fin n,
            (∏ i, p (ω i)) * (g (ω j) * g (ω k)) from by
      apply Finset.sum_congr rfl
      intro ω _
      rw [hcenter ω, sq, Finset.sum_mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
  rw [hstep1]
  have hterm : ∀ j k : Fin n,
      (∑ ω : Fin n → A, (∏ i, p (ω i)) * (g (ω j) * g (ω k)))
      = if j = k then (∑ a, p a * (f a - m) ^ 2) else 0 := by
    intro j k
    by_cases hjk : j = k
    · rw [if_pos hjk, hjk]
      rw [path_expect_single p hsum (fun a => g a * g a) k]
      apply Finset.sum_congr rfl
      intro a _
      rw [hg]
      ring
    · rw [if_neg hjk, path_expect_pair p hsum g g hjk, hgsum,
        mul_zero]
  rw [Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl fun k _ => hterm j k)]
  have hrow : ∀ j : Fin n, (∑ k : Fin n,
      if j = k then (∑ a, p a * (f a - m) ^ 2) else 0)
      = ∑ a, p a * (f a - m) ^ 2 := by
    intro j
    rw [Finset.sum_ite_eq Finset.univ j
      (fun _ => ∑ a, p a * (f a - m) ^ 2)]
    simp
  rw [Finset.sum_congr rfl (fun j _ => hrow j)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- Finite Chebyshev bound for the tilted product law. -/
theorem path_chebyshev {A : Type*} [Fintype A]
    {n : ℕ} (hn : 0 < n) (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (f : A → ℝ) (m : ℝ)
    (hm : ∑ a, p a * f a = m) (delta : ℝ) (hdelta : 0 < delta) :
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → A =>
        (n : ℝ) * delta ≤ |(∑ k, f (ω k)) - n * m|),
      ∏ k, p (ω k))
      ≤ (n * ∑ a, p a * (f a - m) ^ 2) / ((n : ℝ) * delta) ^ 2 := by
  classical
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((n : ℝ) * delta) ^ 2)]
  rw [← path_second_moment p hsum f m hm]
  calc (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → A =>
        (n : ℝ) * delta ≤ |(∑ k, f (ω k)) - n * m|),
      ∏ k, p (ω k)) * ((n : ℝ) * delta) ^ 2
      = ∑ ω ∈ Finset.univ.filter (fun ω : Fin n → A =>
          (n : ℝ) * delta ≤ |(∑ k, f (ω k)) - n * m|),
        (∏ k, p (ω k)) * ((n : ℝ) * delta) ^ 2 := by
        rw [Finset.sum_mul]
  _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin n → A =>
        (n : ℝ) * delta ≤ |(∑ k, f (ω k)) - n * m|),
      (∏ k, p (ω k)) * ((∑ k, f (ω k)) - n * m) ^ 2 := by
        apply Finset.sum_le_sum
        intro ω hω
        rw [Finset.mem_filter] at hω
        apply mul_le_mul_of_nonneg_left _
          (Finset.prod_nonneg fun k _ => hp (ω k))
        have habs := hω.2
        calc ((n : ℝ) * delta) ^ 2
            ≤ |(∑ k, f (ω k)) - n * m| ^ 2 := by
              apply pow_le_pow_left₀ (by positivity) habs
        _ = ((∑ k, f (ω k)) - n * m) ^ 2 := sq_abs _
  _ ≤ ∑ ω : Fin n → A,
      (∏ k, p (ω k)) * ((∑ k, f (ω k)) - n * m) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
        intro ω _ _
        apply mul_nonneg (Finset.prod_nonneg fun k _ => hp (ω k))
        positivity

/-- **Cramér lower bound** at an exposed point: if the tilt `χ`
centers the tilted law at `a` and `n` is large enough for the tilted
variance (`ṽ ≤ nδ²/2`), the upper-tail probability is bounded below
at the Legendre rate:
`P(S_n ≥ n(a-δ)) ≥ ½·exp(-n(χ(a+δ) - Λ(χ)))`. -/
theorem cramer_lower_bound {A : Type*} [Fintype A]
    (q : A → ℝ) (hq : ∀ a, 0 ≤ q a) (f : A → ℝ)
    {n : ℕ} (hn : 0 < n) (a chi delta : ℝ) (hchi : 0 ≤ chi)
    (hdelta : 0 < delta)
    (hM : 0 < ∑ b, q b * Real.exp (chi * f b))
    (hmean : (∑ b, (q b * Real.exp (chi * f b)
        / (∑ c, q c * Real.exp (chi * f c))) * f b) = a)
    (hvar : (∑ b, (q b * Real.exp (chi * f b)
        / (∑ c, q c * Real.exp (chi * f c))) * (f b - a) ^ 2)
      ≤ n * delta ^ 2 / 2) :
    (1 / 2) * Real.exp (-((n : ℝ) * (chi * (a + delta)
        - Real.log (∑ b, q b * Real.exp (chi * f b)))))
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin n → A =>
          (n : ℝ) * (a - delta) ≤ ∑ k, f (ω k)),
        ∏ k, q (ω k) := by
  classical
  set pt : A → ℝ := fun b => q b * Real.exp (chi * f b)
    / (∑ c, q c * Real.exp (chi * f c)) with hpt
  have hpt_nonneg : ∀ b, 0 ≤ pt b := by
    intro b
    rw [hpt]
    exact div_nonneg (mul_nonneg (hq b) (Real.exp_pos _).le) hM.le
  have hpt_sum : (∑ b, pt b) = 1 := by
    rw [hpt, ← Finset.sum_div, div_self hM.ne']
  -- total tilted mass on path space is one
  have htotal : (∑ ω : Fin n → A, ∏ k, pt (ω k)) = 1 := by
    rw [show (∑ ω : Fin n → A, ∏ k, pt (ω k))
        = ∏ _i : Fin n, ∑ b, pt b from
      path_prod_factorization n (fun _ => pt)]
    rw [Finset.prod_congr rfl (fun i _ => hpt_sum)]
    exact Finset.prod_const_one
  -- the bad event has tilted probability at most one half
  have hbad : (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → A =>
        (n : ℝ) * delta ≤ |(∑ k, f (ω k)) - n * a|),
      ∏ k, pt (ω k)) ≤ 1 / 2 := by
    calc (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → A =>
          (n : ℝ) * delta ≤ |(∑ k, f (ω k)) - n * a|),
        ∏ k, pt (ω k))
        ≤ (n * ∑ b, pt b * (f b - a) ^ 2) / ((n : ℝ) * delta) ^ 2 :=
          path_chebyshev hn pt hpt_nonneg hpt_sum f a hmean
            delta hdelta
    _ ≤ (n * (n * delta ^ 2 / 2)) / ((n : ℝ) * delta) ^ 2 := by
          gcongr
    _ = 1 / 2 := by
          have hnne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
          field_simp
  -- hence the good event carries at least one half
  have hgood : (1 : ℝ) / 2 ≤ ∑ ω ∈ Finset.univ.filter
      (fun ω : Fin n → A =>
        ¬ ((n : ℝ) * delta ≤ |(∑ k, f (ω k)) - n * a|)),
      ∏ k, pt (ω k) := by
    have hpart := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Fin n → A))
      (fun ω => (n : ℝ) * delta ≤ |(∑ k, f (ω k)) - n * a|)
      (fun ω => ∏ k, pt (ω k))
    rw [htotal] at hpart
    linarith [hbad, hpart]
  -- change of measure on the good event
  set Egood : Set (Fin n → A) := {ω |
    ¬ ((n : ℝ) * delta ≤ |(∑ k, f (ω k)) - n * a|)} with hEgood
  haveI : DecidablePred (· ∈ Egood) := fun ω =>
    Classical.dec _
  have hEbound : ∀ ω ∈ Egood,
      (∑ k, f (ω k)) ≤ (n : ℝ) * (a + delta) := by
    intro ω hω
    rw [hEgood, Set.mem_setOf_eq, not_le] at hω
    have := abs_lt.mp hω
    nlinarith [this.2]
  have hchange := change_of_measure_bound q hq f n chi
    ((n : ℝ) * (a + delta)) hchi hM Egood hEbound
  -- identify the two filters
  have hfilter_eq : Finset.univ.filter (· ∈ Egood)
      = Finset.univ.filter (fun ω : Fin n → A =>
        ¬ ((n : ℝ) * delta ≤ |(∑ k, f (ω k)) - n * a|)) := by
    apply Finset.filter_congr
    intro ω _
    rw [hEgood]
    rfl
  rw [hfilter_eq] at hchange
  -- the good event sits inside the target tail
  have hsubset : Finset.univ.filter (fun ω : Fin n → A =>
        ¬ ((n : ℝ) * delta ≤ |(∑ k, f (ω k)) - n * a|))
      ⊆ Finset.univ.filter (fun ω : Fin n → A =>
        (n : ℝ) * (a - delta) ≤ ∑ k, f (ω k)) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    refine ⟨hω.1, ?_⟩
    have h2 := hω.2
    rw [not_le] at h2
    have habs := abs_lt.mp h2
    nlinarith [habs.1]
  have hmono : (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → A =>
        ¬ ((n : ℝ) * delta ≤ |(∑ k, f (ω k)) - n * a|)),
      ∏ k, q (ω k))
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin n → A =>
        (n : ℝ) * (a - delta) ≤ ∑ k, f (ω k)),
      ∏ k, q (ω k) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro ω _ _
    exact Finset.prod_nonneg fun k _ => hq (ω k)
  -- assemble
  have hexp_id : Real.exp (-((n : ℝ) * (chi * (a + delta)
        - Real.log (∑ b, q b * Real.exp (chi * f b)))))
      = Real.exp (-(chi * ((n : ℝ) * (a + delta))))
        * (∑ b, q b * Real.exp (chi * f b)) ^ n := by
    rw [show (∑ b, q b * Real.exp (chi * f b)) ^ n
        = Real.exp ((n : ℝ)
            * Real.log (∑ b, q b * Real.exp (chi * f b))) from by
      rw [Real.exp_nat_mul, Real.exp_log hM]]
    rw [← Real.exp_add]
    congr 1
    ring
  calc (1 / 2) * Real.exp (-((n : ℝ) * (chi * (a + delta)
        - Real.log (∑ b, q b * Real.exp (chi * f b)))))
      = Real.exp (-(chi * ((n : ℝ) * (a + delta))))
          * (∑ b, q b * Real.exp (chi * f b)) ^ n * (1 / 2) := by
        rw [hexp_id]
        ring
  _ ≤ Real.exp (-(chi * ((n : ℝ) * (a + delta))))
        * (∑ b, q b * Real.exp (chi * f b)) ^ n
        * (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → A =>
            ¬ ((n : ℝ) * delta ≤ |(∑ k, f (ω k)) - n * a|)),
          ∏ k, pt (ω k)) := by
        apply mul_le_mul_of_nonneg_left hgood
        positivity
  _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin n → A =>
        ¬ ((n : ℝ) * delta ≤ |(∑ k, f (ω k)) - n * a|)),
      ∏ k, q (ω k) := hchange
  _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin n → A =>
        (n : ℝ) * (a - delta) ≤ ∑ k, f (ω k)),
      ∏ k, q (ω k) := hmono

end NCG
