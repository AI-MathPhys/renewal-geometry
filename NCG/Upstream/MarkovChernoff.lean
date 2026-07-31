/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.PerronPressure

/-!
# The Markov-renewal Chernoff bound at the Perron pressure
  (missing large-deviations machinery; `thm:deficiency-rate-function`,
   GR_emergence)

The Markov-renewal extension of the Cramér upper bound: additive
edge records of a finite nonnegative kernel decay at the tilted
Perron pressure `log pRad(Q_χ)`:

* `pathSum_eq_rowSum` — the path expansion of matrix powers
  (pinned-start recursion);
* `markov_chernoff_core` — the non-asymptotic bound
  `P(S_n ≥ na) ≤ e^{-χna}·entrySum(Q_χⁿ)`;
* `markov_chernoff_pressure` — the eventual Legendre form: for every
  `ε > 0`, eventually
  `P(S_n ≥ na) ≤ exp(-n(χa - log pRad(Q_χ) - ε))` — the
  Gärtner–Ellis upper bound at the Gelfand–Fekete pressure of the
  tilted kernel, the pressure used by `thm:matrix-renewal-dictionary`
  and the Gallavotti–Cohen symmetry.
-/

namespace NCG

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The pinned-start path sum of a kernel. -/
noncomputable def pathSum (Q : Matrix V V ℝ) : ℕ → V → ℝ
  | 0, _ => 1
  | n + 1, x => ∑ z, Q x z * pathSum Q n z

omit [Nonempty V] in
/-- The path sum equals the row sum of the matrix power. -/
theorem pathSum_eq_rowSum (Q : Matrix V V ℝ) :
    ∀ (n : ℕ) (x : V), pathSum Q n x = ∑ y, (Q ^ n) x y := by
  intro n
  induction n with
  | zero =>
    intro x
    simp [pathSum, Matrix.one_apply]
  | succ m ih =>
    intro x
    rw [show pathSum Q (m + 1) x
        = ∑ z, Q x z * pathSum Q m z from rfl]
    rw [Finset.sum_congr rfl (fun z _ => by rw [ih z])]
    rw [show (Q ^ (m + 1)) = Q * Q ^ m from pow_succ' Q m]
    rw [show (∑ y, (Q * Q ^ m) x y)
        = ∑ y, ∑ z, Q x z * (Q ^ m) z y from
      Finset.sum_congr rfl fun y _ => Matrix.mul_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.mul_sum]

/-- The full vertex path of a pinned start and successor chain. -/
def fullPath {n : ℕ} (x : V) (ω : Fin n → V) : Fin (n + 1) → V :=
  Fin.cons x ω

omit [DecidableEq V] [Nonempty V] in
/-- The tilted-path expansion: summing the tilted edge weights over
pinned-start paths gives the tilted path sum. -/
theorem tilted_path_expansion (Qt : Matrix V V ℝ) (n : ℕ) (x : V) :
    (∑ ω : Fin n → V,
      ∏ i : Fin n, Qt (fullPath x ω i.castSucc) (fullPath x ω i.succ))
      = pathSum Qt n x := by
  induction n generalizing x with
  | zero => simp [pathSum]
  | succ m ih =>
    have hsplit : (∑ ω : Fin (m + 1) → V, ∏ i : Fin (m + 1),
          Qt (fullPath x ω i.castSucc) (fullPath x ω i.succ))
        = ∑ p : V × (Fin m → V),
            Qt x p.1 * ∏ i : Fin m,
              Qt (fullPath p.1 p.2 i.castSucc)
                (fullPath p.1 p.2 i.succ) := by
      apply Fintype.sum_equiv (Fin.consEquiv fun _ => V).symm
      intro ω
      change (∏ i : Fin (m + 1),
          Qt (fullPath x ω i.castSucc) (fullPath x ω i.succ))
        = Qt x (ω 0) * ∏ i : Fin m,
            Qt (fullPath (ω 0) (Fin.tail ω) i.castSucc)
              (fullPath (ω 0) (Fin.tail ω) i.succ)
      simp only [fullPath]
      rw [Fin.cons_self_tail, Fin.prod_univ_succ]
      congr 1
    rw [hsplit, Fintype.sum_prod_type]
    rw [show pathSum Qt (m + 1) x
        = ∑ z, Qt x z * pathSum Qt m z from rfl]
    apply Finset.sum_congr rfl
    intro z _
    rw [← ih z, Finset.mul_sum]

omit [Nonempty V] in
/-- `thm:deficiency-rate-function` (Markov core bound): the
tilted-kernel Chernoff inequality — the additive edge record of a
nonnegative kernel with sub-probability initial weights satisfies
`P(S_n ≥ na) ≤ e^{-χna}·entrySum(Q_χⁿ)` with
`Q_χ(x,y) = Q(x,y)e^{χf(x,y)}`. -/
theorem markov_chernoff_core (Q : Matrix V V ℝ)
    (hQ : EntryNonneg Q) (f : V → V → ℝ) (mu : V → ℝ)
    (_hmu0 : ∀ x, 0 ≤ mu x) (hmu1 : ∀ x, mu x ≤ 1)
    (n : ℕ) (a chi : ℝ) (hchi : 0 ≤ chi) :
    (∑ P ∈ Finset.univ.filter
        (fun P : V × (Fin n → V) => (n : ℝ) * a
          ≤ ∑ i : Fin n, f (fullPath P.1 P.2 i.castSucc)
              (fullPath P.1 P.2 i.succ)),
      mu P.1 * ∏ i : Fin n,
        Q (fullPath P.1 P.2 i.castSucc) (fullPath P.1 P.2 i.succ))
      ≤ Real.exp (-(chi * ((n : ℝ) * a)))
        * entrySum ((Matrix.of fun x y =>
            Q x y * Real.exp (chi * f x y)) ^ n) := by
  classical
  set Qt : Matrix V V ℝ :=
    Matrix.of fun x y => Q x y * Real.exp (chi * f x y) with hQt
  -- entrySum of the power as a path sum
  have hentry : entrySum (Qt ^ n)
      = ∑ x, pathSum Qt n x := by
    unfold entrySum
    apply Finset.sum_congr rfl
    intro x _
    rw [pathSum_eq_rowSum]
  rw [hentry, Finset.mul_sum]
  have hRHS : (∑ P : V × (Fin n → V),
        Real.exp (-(chi * ((n : ℝ) * a)))
          * ∏ i : Fin n, Qt (fullPath P.1 P.2 i.castSucc)
              (fullPath P.1 P.2 i.succ))
      = ∑ x, Real.exp (-(chi * ((n : ℝ) * a)))
          * pathSum Qt n x := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.mul_sum, tilted_path_expansion Qt n x]
  rw [← hRHS]
  -- pointwise Chernoff comparison
  calc (∑ P ∈ Finset.univ.filter
        (fun P : V × (Fin n → V) => (n : ℝ) * a
          ≤ ∑ i : Fin n, f (fullPath P.1 P.2 i.castSucc)
              (fullPath P.1 P.2 i.succ)),
      mu P.1 * ∏ i : Fin n,
        Q (fullPath P.1 P.2 i.castSucc) (fullPath P.1 P.2 i.succ))
      ≤ ∑ P ∈ Finset.univ.filter
          (fun P : V × (Fin n → V) => (n : ℝ) * a
            ≤ ∑ i : Fin n, f (fullPath P.1 P.2 i.castSucc)
                (fullPath P.1 P.2 i.succ)),
        Real.exp (-(chi * ((n : ℝ) * a)))
          * ∏ i : Fin n, Qt (fullPath P.1 P.2 i.castSucc)
              (fullPath P.1 P.2 i.succ) := by
        apply Finset.sum_le_sum
        intro P hP
        rw [Finset.mem_filter] at hP
        have hprodQt : (∏ i : Fin n,
            Qt (fullPath P.1 P.2 i.castSucc) (fullPath P.1 P.2 i.succ))
            = (∏ i : Fin n, Q (fullPath P.1 P.2 i.castSucc)
                (fullPath P.1 P.2 i.succ))
              * Real.exp (chi * ∑ i : Fin n,
                  f (fullPath P.1 P.2 i.castSucc)
                    (fullPath P.1 P.2 i.succ)) := by
          rw [hQt]
          rw [show (∏ i : Fin n, (Matrix.of fun x y =>
              Q x y * Real.exp (chi * f x y))
                (fullPath P.1 P.2 i.castSucc)
                (fullPath P.1 P.2 i.succ))
            = ∏ i : Fin n, (Q (fullPath P.1 P.2 i.castSucc)
                (fullPath P.1 P.2 i.succ)
              * Real.exp (chi * f (fullPath P.1 P.2 i.castSucc)
                  (fullPath P.1 P.2 i.succ))) from
            Finset.prod_congr rfl fun i _ => rfl]
          rw [Finset.prod_mul_distrib, ← Real.exp_sum]
          congr 1
          rw [Finset.mul_sum]
        rw [hprodQt]
        have hQprod : (0 : ℝ) ≤ ∏ i : Fin n,
            Q (fullPath P.1 P.2 i.castSucc)
              (fullPath P.1 P.2 i.succ) :=
          Finset.prod_nonneg fun i _ => hQ _ _
        calc mu P.1 * ∏ i : Fin n,
            Q (fullPath P.1 P.2 i.castSucc) (fullPath P.1 P.2 i.succ)
            ≤ 1 * ∏ i : Fin n,
              Q (fullPath P.1 P.2 i.castSucc)
                (fullPath P.1 P.2 i.succ) := by
              apply mul_le_mul_of_nonneg_right (hmu1 P.1) hQprod
        _ = (∏ i : Fin n, Q (fullPath P.1 P.2 i.castSucc)
              (fullPath P.1 P.2 i.succ)) := one_mul _
        _ ≤ Real.exp (-(chi * ((n : ℝ) * a)))
              * ((∏ i : Fin n, Q (fullPath P.1 P.2 i.castSucc)
                  (fullPath P.1 P.2 i.succ))
                * Real.exp (chi * ∑ i : Fin n,
                    f (fullPath P.1 P.2 i.castSucc)
                      (fullPath P.1 P.2 i.succ))) := by
              rw [show Real.exp (-(chi * ((n : ℝ) * a)))
                    * ((∏ i : Fin n, Q (fullPath P.1 P.2 i.castSucc)
                        (fullPath P.1 P.2 i.succ))
                      * Real.exp (chi * ∑ i : Fin n,
                          f (fullPath P.1 P.2 i.castSucc)
                            (fullPath P.1 P.2 i.succ)))
                  = (∏ i : Fin n, Q (fullPath P.1 P.2 i.castSucc)
                      (fullPath P.1 P.2 i.succ))
                    * (Real.exp (-(chi * ((n : ℝ) * a)))
                      * Real.exp (chi * ∑ i : Fin n,
                          f (fullPath P.1 P.2 i.castSucc)
                            (fullPath P.1 P.2 i.succ))) from by ring]
              nth_rewrite 1 [show (∏ i : Fin n,
                  Q (fullPath P.1 P.2 i.castSucc)
                    (fullPath P.1 P.2 i.succ))
                = (∏ i : Fin n, Q (fullPath P.1 P.2 i.castSucc)
                    (fullPath P.1 P.2 i.succ)) * 1 from
                (mul_one _).symm]
              apply mul_le_mul_of_nonneg_left _ hQprod
              rw [← Real.exp_add,
                show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
              apply Real.exp_le_exp.mpr
              have := hP.2
              nlinarith [hP.2, hchi]
  _ ≤ ∑ P : V × (Fin n → V),
        Real.exp (-(chi * ((n : ℝ) * a)))
          * ∏ i : Fin n, Qt (fullPath P.1 P.2 i.castSucc)
              (fullPath P.1 P.2 i.succ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
        intro P _ _
        apply mul_nonneg (Real.exp_pos _).le
        apply Finset.prod_nonneg
        intro i _
        rw [hQt]
        exact mul_nonneg (hQ _ _) (Real.exp_pos _).le

/-- `thm:deficiency-rate-function` (Markov pressure form): the tail
of the Markov-renewal edge record eventually decays at the Legendre
rate of the tilted Perron pressure `log pRad(Q_χ)` — the
Gärtner–Ellis upper bound for the matrix-renewal deficiency
current. -/
theorem markov_chernoff_pressure (Q : Matrix V V ℝ)
    (hQ : EntryNonneg Q) (f : V → V → ℝ) (mu : V → ℝ)
    (hmu0 : ∀ x, 0 ≤ mu x) (hmu1 : ∀ x, mu x ≤ 1)
    (a chi : ℝ) (hchi : 0 ≤ chi)
    (hwt : HasDiagWitness (Matrix.of fun x y =>
      Q x y * Real.exp (chi * f x y)))
    (hpos : ∀ k : ℕ, 0 < entrySum ((Matrix.of fun x y =>
      Q x y * Real.exp (chi * f x y)) ^ k))
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (∑ P ∈ Finset.univ.filter
          (fun P : V × (Fin n → V) => (n : ℝ) * a
            ≤ ∑ i : Fin n, f (fullPath P.1 P.2 i.castSucc)
                (fullPath P.1 P.2 i.succ)),
        mu P.1 * ∏ i : Fin n,
          Q (fullPath P.1 P.2 i.castSucc) (fullPath P.1 P.2 i.succ))
        ≤ Real.exp (-((n : ℝ) * (chi * a
            - Real.log (pRad (Matrix.of fun x y =>
                Q x y * Real.exp (chi * f x y))) - eps))) := by
  classical
  set Qt : Matrix V V ℝ :=
    Matrix.of fun x y => Q x y * Real.exp (chi * f x y) with hQt
  have hQtnn : EntryNonneg Qt := fun x y =>
    mul_nonneg (hQ x y) (Real.exp_pos _).le
  have htends := tendsto_growthSeq hQtnn hwt
  have hev1 : ∀ᶠ k : ℕ in Filter.atTop,
      growthSeq Qt k / k < Real.log (pRad Qt) + eps :=
    htends.eventually_lt_const (by linarith)
  filter_upwards [hev1, Filter.eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast hn1
  -- entrySum bound from the Fekete sequence
  have hentry_le : entrySum (Qt ^ n)
      ≤ Real.exp ((n : ℝ) * (Real.log (pRad Qt) + eps)) := by
    have hgs : growthSeq Qt n < (n : ℝ)
        * (Real.log (pRad Qt) + eps) := by
      have := hn
      rw [div_lt_iff₀ hnR] at this
      linarith [this]
    have hexp : entrySum (Qt ^ n) = Real.exp (growthSeq Qt n) := by
      rw [growthSeq, Real.exp_log (hpos n)]
    rw [hexp]
    exact (Real.exp_le_exp.mpr hgs.le)
  calc (∑ P ∈ Finset.univ.filter
        (fun P : V × (Fin n → V) => (n : ℝ) * a
          ≤ ∑ i : Fin n, f (fullPath P.1 P.2 i.castSucc)
              (fullPath P.1 P.2 i.succ)),
      mu P.1 * ∏ i : Fin n,
        Q (fullPath P.1 P.2 i.castSucc) (fullPath P.1 P.2 i.succ))
      ≤ Real.exp (-(chi * ((n : ℝ) * a))) * entrySum (Qt ^ n) :=
        markov_chernoff_core Q hQ f mu hmu0 hmu1 n a chi hchi
  _ ≤ Real.exp (-(chi * ((n : ℝ) * a)))
        * Real.exp ((n : ℝ) * (Real.log (pRad Qt) + eps)) := by
        apply mul_le_mul_of_nonneg_left hentry_le (Real.exp_pos _).le
  _ = Real.exp (-((n : ℝ) * (chi * a
        - Real.log (pRad Qt) - eps))) := by
        rw [← Real.exp_add]
        congr 1
        ring

end NCG
