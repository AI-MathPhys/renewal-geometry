/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The stationary exchange theorem and the detailed-balance counterexample

Covers `thm:stationary-exchange` and
`prop:detailed-balance-not-torsion` from `manuscripts/lorentzian_emergence/lorentzian_emergence.tex`.

For a primitive Markov kernel on a finite set of resolved diamond
records that is covariant under the history-exchange involution, the
unique stationary law is exchange invariant; consequently every
exchange-odd translational defect observable has vanishing stationary
mean, and the translational plaquette defect reduces to its `O(h³)`
remainder (`stationary_exchange_closure`).

Uniqueness of the stationary law for a strictly positive stochastic
kernel is proved by the Markov/Dobrushin `L¹`-contraction argument:
writing the difference of two stationary laws as `y = y₊ − y₋` with
equal masses `τ`, each one-step image loses at least `2δτ` of
`L¹`-mass per target state (`δ` the minimal kernel entry), which is
inconsistent with stationarity unless `τ = 0`.

The 2-state counterexample shows that ordinary one-step detailed
balance does **not** provide the exchange invariance: the kernel
`P = [[3/4,1/4],[1/2,1/2]]` with `π = (2/3,1/3)` is primitive and
reversible, yet the stationary mean of the exchange-odd observable
`d(±) = ±v` is `v/3 ≠ 0`.
-/

namespace NCG

open Finset

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## Iterated kernels -/

/-- The `k`-step iterate of a Markov kernel. -/
def kernelPow (P : D → D → ℝ) : ℕ → D → D → ℝ
  | 0 => fun a b => if a = b then 1 else 0
  | k + 1 => fun a b => ∑ c, P a c * kernelPow P k c b

@[simp]
theorem kernelPow_one {P : D → D → ℝ} (a b : D) :
    kernelPow P 1 a b = P a b := by
  simp [kernelPow, mul_ite]

theorem kernelPow_rowSum {P : D → D → ℝ}
    (hrow : ∀ a, ∑ b, P a b = 1) :
    ∀ (k : ℕ) (a : D), ∑ b, kernelPow P k a b = 1 := by
  intro k
  induction k with
  | zero =>
    intro a
    simp [kernelPow]
  | succ n ih =>
    intro a
    unfold kernelPow
    rw [Finset.sum_comm]
    have h1 : ∀ c ∈ Finset.univ,
        (∑ b, P a c * kernelPow P n c b) = P a c := by
      intro c _
      rw [← Finset.mul_sum, ih c, mul_one]
    rw [Finset.sum_congr rfl h1]
    exact hrow a

theorem kernelPow_stationary {P : D → D → ℝ} {π : D → ℝ}
    (hπ : ∀ b, ∑ a, π a * P a b = π b) :
    ∀ (k : ℕ) (b : D), ∑ a, π a * kernelPow P k a b = π b := by
  intro k
  induction k with
  | zero =>
    intro b
    simp [kernelPow]
  | succ n ih =>
    intro b
    unfold kernelPow
    have h1 : ∀ a ∈ Finset.univ,
        π a * (∑ c, P a c * kernelPow P n c b)
        = ∑ c, π a * P a c * kernelPow P n c b := by
      intro a _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    have h2 : ∀ c ∈ Finset.univ,
        (∑ a, π a * P a c * kernelPow P n c b)
        = π c * kernelPow P n c b := by
      intro c _
      rw [← Finset.sum_mul, hπ c]
    rw [Finset.sum_congr rfl h2]
    exact ih b

/-! ## Uniqueness of the stationary law for positive kernels -/

/-- A strictly positive stochastic kernel has at most one stationary
signed law of total mass one (Markov/Dobrushin `L¹`-contraction). -/
theorem stationary_unique_of_pos {Q : D → D → ℝ}
    (hpos : ∀ a b, 0 < Q a b) (hrow : ∀ a, ∑ b, Q a b = 1)
    {π π' : D → ℝ}
    (hπ1 : ∑ a, π a = 1) (hπ'1 : ∑ a, π' a = 1)
    (hπ : ∀ b, ∑ a, π a * Q a b = π b)
    (hπ' : ∀ b, ∑ a, π' a * Q a b = π' b) :
    π = π' := by
  classical
  by_contra hne
  set y : D → ℝ := fun a => π a - π' a with hy
  have hyne : ∃ a, y a ≠ 0 := by
    by_contra hall
    refine hne (funext fun a => ?_)
    have h0 : ¬ y a ≠ 0 := fun h => hall ⟨a, h⟩
    have h1 : y a = 0 := not_not.mp h0
    simp only [hy] at h1
    linarith
  have habs : ∀ a, |y a| = max (y a) 0 + max (-y a) 0 := by
    intro a
    rcases le_total 0 (y a) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), add_zero,
        abs_of_nonneg h]
    · rw [max_eq_right h, max_eq_left (by linarith), zero_add,
        abs_of_nonpos h]
  have hsplit : ∀ a, y a = max (y a) 0 - max (-y a) 0 := by
    intro a
    rcases le_total 0 (y a) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), sub_zero]
    · rw [max_eq_right h, max_eq_left (by linarith), zero_sub, neg_neg]
  set τ : ℝ := ∑ a, max (y a) 0 with hτ
  have hsum0 : ∑ a, y a = 0 := by
    have h1 : ∑ a, y a = (∑ a, π a) - ∑ a, π' a := by
      rw [← Finset.sum_sub_distrib]
    rw [h1, hπ1, hπ'1, sub_self]
  have hτm : ∑ a, max (-y a) 0 = τ := by
    have h2 : ∑ a, (max (y a) 0 - max (-y a) 0) = 0 := by
      rw [Finset.sum_congr rfl fun a _ => (hsplit a).symm]
      exact hsum0
    rw [Finset.sum_sub_distrib] at h2
    simp only [← hτ] at h2
    linarith
  have hτ0 : 0 ≤ τ := Finset.sum_nonneg fun a _ => le_max_right _ _
  have hτpos : 0 < τ := by
    rcases lt_or_eq_of_le hτ0 with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha⟩ := hyne
      have hyp0 : ∀ b ∈ Finset.univ, max (y b) 0 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          fun b _ => le_max_right _ _).mp h.symm
      have hym0 : ∀ b ∈ Finset.univ, max (-y b) 0 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          fun b _ => le_max_right _ _).mp (by rw [hτm]; exact h.symm)
      have h3 := habs a
      rw [hyp0 a (Finset.mem_univ a), hym0 a (Finset.mem_univ a),
        add_zero] at h3
      exact ha (abs_eq_zero.mp h3)
  -- the minimal kernel entry
  have hDne : (Finset.univ : Finset D).Nonempty := by
    rcases (Finset.univ : Finset D).eq_empty_or_nonempty with h | h
    · exfalso
      rw [h, Finset.sum_empty] at hπ1
      exact one_ne_zero hπ1.symm
    · exact h
  obtain ⟨p₀, -, hp₀⟩ := Finset.exists_min_image
    ((Finset.univ : Finset D) ×ˢ (Finset.univ : Finset D))
    (fun p => Q p.1 p.2) (hDne.product hDne)
  have hδpos : 0 < Q p₀.1 p₀.2 := hpos _ _
  have hδle : ∀ a b, Q p₀.1 p₀.2 ≤ Q a b := by
    intro a b
    exact hp₀ (a, b) (Finset.mem_product.mpr
      ⟨Finset.mem_univ a, Finset.mem_univ b⟩)
  set δ : ℝ := Q p₀.1 p₀.2 with hδ
  -- stationarity of the difference
  have hystat : ∀ b, ∑ a, y a * Q a b = y b := by
    intro b
    have h4 : (∑ a, y a * Q a b)
        = (∑ a, π a * Q a b) - ∑ a, π' a * Q a b := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [hy]
      ring
    rw [h4, hπ b, hπ' b]
  -- per-target decomposition and mass loss
  have hXY : ∀ b, y b
      = (∑ a, max (y a) 0 * Q a b) - ∑ a, max (-y a) 0 * Q a b := by
    intro b
    rw [← hystat b, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← sub_mul, ← hsplit a]
  have hXbound : ∀ b, δ * τ ≤ ∑ a, max (y a) 0 * Q a b := by
    intro b
    calc δ * τ = ∑ a, max (y a) 0 * δ := by
          rw [← Finset.sum_mul]
          simp only [← hτ]
          ring
      _ ≤ ∑ a, max (y a) 0 * Q a b :=
          Finset.sum_le_sum fun a _ =>
            mul_le_mul_of_nonneg_left (hδle a b) (le_max_right _ _)
  have hYbound : ∀ b, δ * τ ≤ ∑ a, max (-y a) 0 * Q a b := by
    intro b
    calc δ * τ = ∑ a, max (-y a) 0 * δ := by
          rw [← Finset.sum_mul, hτm]
          ring
      _ ≤ ∑ a, max (-y a) 0 * Q a b :=
          Finset.sum_le_sum fun a _ =>
            mul_le_mul_of_nonneg_left (hδle a b) (le_max_right _ _)
  have hkey : ∀ b, |y b|
      ≤ (∑ a, max (y a) 0 * Q a b) + (∑ a, max (-y a) 0 * Q a b)
        - 2 * (δ * τ) := by
    intro b
    have h5 := hXY b
    have h6 : |y b| = (∑ a, max (y a) 0 * Q a b)
        + (∑ a, max (-y a) 0 * Q a b)
        - 2 * min (∑ a, max (y a) 0 * Q a b)
            (∑ a, max (-y a) 0 * Q a b) := by
      rcases le_total (∑ a, max (y a) 0 * Q a b)
        (∑ a, max (-y a) 0 * Q a b) with h | h
      · rw [h5, abs_of_nonpos (by linarith), min_eq_left h]
        ring
      · rw [h5, abs_of_nonneg (by linarith), min_eq_right h]
        ring
    rw [h6]
    have h7 := le_min (hXbound b) (hYbound b)
    linarith
  -- summing the estimate over the target state
  have hsum1 : ∑ b, ∑ a, max (y a) 0 * Q a b = τ := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => by
      rw [← Finset.mul_sum, hrow a, mul_one]]
  have hsum2 : ∑ b, ∑ a, max (-y a) 0 * Q a b = τ := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => by
      rw [← Finset.mul_sum, hrow a, mul_one]]
    exact hτm
  have habs_sum : ∑ b, |y b| = 2 * τ := by
    rw [Finset.sum_congr rfl fun b _ => habs b,
      Finset.sum_add_distrib, hτm]
    simp only [← hτ]
    ring
  have h8 : ∑ b, |y b|
      ≤ (∑ b, ∑ a, max (y a) 0 * Q a b)
        + (∑ b, ∑ a, max (-y a) 0 * Q a b)
        - (Fintype.card D : ℝ) * (2 * (δ * τ)) := by
    have h9 := Finset.sum_le_sum
      fun b (_ : b ∈ Finset.univ) => hkey b
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h9
    exact h9
  rw [habs_sum, hsum1, hsum2] at h8
  have hcard : 0 < (Fintype.card D : ℝ) := by
    have h10 : 0 < Fintype.card D := Fintype.card_pos_iff.mpr
      ⟨hDne.choose⟩
    exact_mod_cast h10
  nlinarith [mul_pos (mul_pos hcard hδpos) hτpos]

/-! ## The stationary exchange theorem (`thm:stationary-exchange`) -/

section Exchange

variable {P : D → D → ℝ} {s : D → D} {π : D → ℝ} {m : ℕ}

/-- **Theorem `thm:stationary-exchange` (exchange invariance)**: the
stationary law of a primitive exchange-covariant diamond kernel is
exchange invariant. -/
theorem stationary_exchange_invariant (hs : Function.Involutive s)
    (hrow : ∀ a, ∑ b, P a b = 1)
    (hcov : ∀ a b, P (s a) (s b) = P a b)
    (hprim : ∀ a b, 0 < kernelPow P m a b)
    (hπ1 : ∑ a, π a = 1)
    (hπ : ∀ b, ∑ a, π a * P a b = π b) :
    ∀ a, π (s a) = π a := by
  have hπs1 : ∑ a, π (s a) = 1 := by
    rw [← hπ1]
    exact Fintype.sum_equiv hs.toPerm _ _ fun a => rfl
  have hπsstat : ∀ b, ∑ a, π (s a) * P a b = π (s b) := by
    intro b
    have h1 : (∑ a, π (s a) * P a b) = ∑ a, π a * P (s a) b := by
      refine Fintype.sum_equiv hs.toPerm _ _ fun a => ?_
      simp only [Function.Involutive.coe_toPerm]
      rw [hs a]
    rw [h1]
    have h2 : ∀ a ∈ Finset.univ, π a * P (s a) b = π a * P a (s b) := by
      intro a _
      congr 1
      conv_lhs => rw [show b = s (s b) from (hs b).symm]
      exact hcov a (s b)
    rw [Finset.sum_congr rfl h2]
    exact hπ (s b)
  have hu := stationary_unique_of_pos (Q := kernelPow P m) hprim
    (kernelPow_rowSum hrow m) hπs1 hπ1
    (kernelPow_stationary hπsstat m) (kernelPow_stationary hπ m)
  intro a
  exact congrFun hu a

/-- **Theorem `thm:stationary-exchange` (vanishing odd mean)**: every
exchange-odd translational defect observable has zero stationary
mean. -/
theorem stationary_exchange_mean_zero {V : Type*} [AddCommGroup V]
    [Module ℝ V] (hs : Function.Involutive s)
    (hrow : ∀ a, ∑ b, P a b = 1)
    (hcov : ∀ a b, P (s a) (s b) = P a b)
    (hprim : ∀ a b, 0 < kernelPow P m a b)
    (hπ1 : ∑ a, π a = 1)
    (hπ : ∀ b, ∑ a, π a * P a b = π b)
    (dtr : D → V) (hodd : ∀ a, dtr (s a) = -dtr a) :
    ∑ a, π a • dtr a = 0 := by
  have hinv := stationary_exchange_invariant hs hrow hcov hprim hπ1 hπ
  have h1 : (∑ a, π a • dtr a) = ∑ a, π (s a) • dtr (s a) := by
    refine Fintype.sum_equiv hs.toPerm _ _ fun a => ?_
    simp only [Function.Involutive.coe_toPerm]
    rw [hs a]
  have h2 : (∑ a, π (s a) • dtr (s a)) = -∑ a, π a • dtr a := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => by
      rw [hinv a, hodd a, smul_neg]
  have h3 : (∑ a, π a • dtr a) = -∑ a, π a • dtr a := h1.trans h2
  have h4 : (∑ a, π a • dtr a) + ∑ a, π a • dtr a = 0 := by
    nth_rewrite 2 [h3]
    exact add_neg_cancel _
  have h5 : (∑ a, π a • dtr a)
      = ((1 : ℝ) / 2) • ((∑ a, π a • dtr a) + ∑ a, π a • dtr a) := by
    rw [← two_smul ℝ, smul_smul]
    norm_num
  rw [h5, h4, smul_zero]

/-- **Theorem `thm:stationary-exchange` (plaquette closure)**: with
the `h²`-coefficient of the translational plaquette defect equal to
the stationary mean of an exchange-odd defect record, the defect is
exactly its `O(h³)` remainder. -/
theorem stationary_exchange_closure {V : Type*} [AddCommGroup V]
    [Module ℝ V] (hs : Function.Involutive s)
    (hrow : ∀ a, ∑ b, P a b = 1)
    (hcov : ∀ a b, P (s a) (s b) = P a b)
    (hprim : ∀ a b, 0 < kernelPow P m a b)
    (hπ1 : ∑ a, π a = 1)
    (hπ : ∀ b, ∑ a, π a * P a b = π b)
    (dtr : D → V) (hodd : ∀ a, dtr (s a) = -dtr a)
    (defect : ℝ → V) (C : ℝ → V)
    (hexp : ∀ h : ℝ,
      defect h = h ^ 2 • (∑ a, π a • dtr a) + h ^ 3 • C h) :
    ∀ h : ℝ, defect h = h ^ 3 • C h := by
  intro h
  rw [hexp h, stationary_exchange_mean_zero hs hrow hcov hprim hπ1 hπ
    dtr hodd, smul_zero, zero_add]

end Exchange

/-! ## The detailed-balance counterexample
(`prop:detailed-balance-not-torsion`) -/

/-- **Proposition `prop:detailed-balance-not-torsion`**: there is a
primitive, reversible (detailed-balance) two-state diamond kernel
whose stationary law is *not* exchange invariant: the stationary mean
of the exchange-odd observable `d(±) = ±v` is nonzero.  One-step
detailed balance therefore does not imply torsion freedom. -/
theorem detailed_balance_not_torsion :
    ∃ (P : Bool → Bool → ℝ) (π : Bool → ℝ),
      (∀ a b, 0 < P a b)
      ∧ (∀ a, ∑ b, P a b = 1)
      ∧ (∀ a, 0 < π a) ∧ (∑ a, π a = 1)
      ∧ (∀ b, ∑ a, π a * P a b = π b)
      ∧ (∀ a b, π a * P a b = π b * P b a)
      ∧ ¬ (∀ a b, P (!a) (!b) = P a b)
      ∧ ∀ (V : Type*) [AddCommGroup V] [Module ℝ V]
          [NoZeroSMulDivisors ℝ V] (v : V), v ≠ 0 →
          (∑ a, π a • (cond a v (-v))) ≠ 0 := by
  refine ⟨fun a b => if a then (if b then 3/4 else 1/4) else 1/2,
    fun a => if a then 2/3 else 1/3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    cases a <;> cases b <;> norm_num
  · intro a
    rw [Fintype.sum_bool]
    cases a <;> norm_num
  · intro a
    cases a <;> norm_num
  · rw [Fintype.sum_bool]
    norm_num
  · intro b
    rw [Fintype.sum_bool]
    cases b <;> norm_num
  · intro a b
    cases a <;> cases b <;> norm_num
  · intro h
    have h1 := h true true
    norm_num at h1
  · intro V _ _ _ v hv
    rw [Fintype.sum_bool]
    have hπf : (if false = true then (2/3 : ℝ) else 1/3) = 1/3 := by
      norm_num
    simp only [cond_true, cond_false, hπf, if_true]
    have h2 : (2/3 : ℝ) • v + (1/3 : ℝ) • (-v) = ((1:ℝ)/3) • v := by
      rw [smul_neg, ← sub_eq_add_neg, ← sub_smul]
      norm_num
    rw [h2]
    exact smul_ne_zero (by norm_num) hv

/-! ## Mixing-gap stability of exchange closure (`thm:approx-exchange`) -/

section ApproxExchange

variable {P : D → D → ℝ} {s : D → D} {π : D → ℝ}

/-- **Theorem `thm:approx-exchange` (invariance defect)**: if the
kernel `ε`-almost commutes with the exchange permutation at the
stationary law, and the kernel contracts zero-mass signed vectors in
`ℓ¹` with gap `λ`, then the stationary law is `ε/λ`-almost exchange
invariant. -/
theorem approx_exchange_invariant (hs : Function.Involutive s)
    {eps lam : ℝ} (hlam : 0 < lam)
    (hπ : ∀ b, ∑ a, π a * P a b = π b)
    (hcomm : ∑ b, |(∑ a, π (s a) * P a b) - ∑ a, π a * P a (s b)|
      ≤ eps)
    (hgap : ∀ μ : D → ℝ, (∑ a, μ a) = 0 →
      ∑ b, |∑ a, μ a * P a b| ≤ (1 - lam) * ∑ a, |μ a|) :
    ∑ a, |π (s a) - π a| ≤ eps / lam := by
  set μ : D → ℝ := fun a => π (s a) - π a with hμ
  have hμ0 : (∑ a, μ a) = 0 := by
    simp only [hμ]
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ a, π (s a) = ∑ a, π a :=
      Fintype.sum_equiv hs.toPerm _ _ fun a => rfl
    rw [h1, sub_self]
  -- the one-step image of μ differs from μ by the commutator defect
  have hkey : ∀ b, (∑ a, μ a * P a b) - μ b
      = (∑ a, π (s a) * P a b) - ∑ a, π a * P a (s b) := by
    intro b
    have h2 := hπ (s b)
    have h3 := hπ b
    have h4 : (∑ a, μ a * P a b)
        = (∑ a, π (s a) * P a b) - ∑ a, π a * P a b := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [hμ]
      ring
    simp only [hμ]
    rw [h4, h3, ← h2]
    ring
  -- the ℓ¹ bootstrap
  have h5 : ∀ b, |μ b|
      ≤ |(∑ a, μ a * P a b) - μ b| + |∑ a, μ a * P a b| := by
    intro b
    calc |μ b| = |(∑ a, μ a * P a b)
        - ((∑ a, μ a * P a b) - μ b)| := by ring_nf
      _ ≤ |∑ a, μ a * P a b| + |(∑ a, μ a * P a b) - μ b| :=
          abs_sub _ _
      _ = |(∑ a, μ a * P a b) - μ b| + |∑ a, μ a * P a b| := by
          ring
  have h6 := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => h5 b
  rw [Finset.sum_add_distrib] at h6
  have h7 : ∑ b, |(∑ a, μ a * P a b) - μ b| ≤ eps := by
    calc ∑ b, |(∑ a, μ a * P a b) - μ b|
        = ∑ b, |(∑ a, π (s a) * P a b) - ∑ a, π a * P a (s b)| :=
          Finset.sum_congr rfl fun b _ => by rw [hkey b]
      _ ≤ eps := hcomm
  have h8 := hgap μ hμ0
  have h9 : (1 - lam) * ∑ a, |μ a|
      = (∑ a, |μ a|) - lam * ∑ a, |μ a| := by ring
  rw [h9] at h8
  have h10 : lam * ∑ a, |μ a| ≤ eps := by linarith
  rw [le_div_iff₀ hlam]
  linarith [h10]

/-- **Theorem `thm:approx-exchange` (odd means)**: every bounded
exchange-odd observable has stationary mean at most
`ε‖d‖_∞/(2λ)`. -/
theorem approx_exchange_odd_mean (hs : Function.Involutive s)
    {eps lam : ℝ} (hlam : 0 < lam)
    (hπ : ∀ b, ∑ a, π a * P a b = π b)
    (hcomm : ∑ b, |(∑ a, π (s a) * P a b) - ∑ a, π a * P a (s b)|
      ≤ eps)
    (hgap : ∀ μ : D → ℝ, (∑ a, μ a) = 0 →
      ∑ b, |∑ a, μ a * P a b| ≤ (1 - lam) * ∑ a, |μ a|)
    (d : D → ℝ) (hodd : ∀ a, d (s a) = -d a)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ a, |d a| ≤ M) :
    |∑ a, π a * d a| ≤ eps * M / (2 * lam) := by
  have hinv := approx_exchange_invariant hs hlam hπ hcomm hgap
  -- exchange antisymmetry of the mean
  have h1 : (∑ a, π (s a) * d a) = -∑ a, π a * d a := by
    have h2 : (∑ a, π (s a) * d a) = ∑ a, π a * d (s a) := by
      refine Fintype.sum_equiv hs.toPerm _ _ fun a => ?_
      simp only [Function.Involutive.coe_toPerm]
      rw [hs a]
    rw [h2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hodd a]
    ring
  -- doubling
  have h3 : (∑ a, (π a - π (s a)) * d a)
      = 2 * ∑ a, π a * d a := by
    have h3a : (∑ a, (π a - π (s a)) * d a)
        = (∑ a, π a * d a) - ∑ a, π (s a) * d a := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [h3a, h1]
    ring
  have h4 : 2 * |∑ a, π a * d a|
      ≤ (∑ a, |π (s a) - π a|) * M := by
    calc 2 * |∑ a, π a * d a| = |2 * ∑ a, π a * d a| := by
          rw [abs_mul, abs_of_pos (show (0:ℝ) < 2 by norm_num)]
      _ = |∑ a, (π a - π (s a)) * d a| := by rw [← h3]
      _ ≤ ∑ a, |(π a - π (s a)) * d a| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, |π (s a) - π a| * M := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [abs_mul, abs_sub_comm]
          exact mul_le_mul_of_nonneg_left (hM a) (abs_nonneg _)
      _ = (∑ a, |π (s a) - π a|) * M := (Finset.sum_mul _ _ _).symm
  have h5 : (∑ a, |π (s a) - π a|) * M ≤ (eps / lam) * M :=
    mul_le_mul_of_nonneg_right hinv hM0
  have heq : eps * M / (2 * lam) = eps / lam * M / 2 := by
    field_simp
  rw [heq]
  linarith

end ApproxExchange

end NCG
