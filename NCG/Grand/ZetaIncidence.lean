/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RecordChain

/-!
# The zeta history as the divisibility incidence operator
  (`thm:ar-zeta-incidence`, Gran-Tensor manuscript)

* `zeta_incidence`: the zeta history `𝖹_X = Σ_{a ≤ X} L_a` is
  the unit-coefficient divisibility incidence matrix — the
  boxed corner rule `P_m 𝖹 P_b = E_{m,b}` iff `b ∣ m` (else
  `0`) holds, `𝖹` is unitriangular (unit diagonal, vanishing
  above the divisibility order), and `𝖹 - I` is nilpotent, so
  `𝖹⁻¹` and `log 𝖹` are terminating polynomials.

Rendering disclosed: uniqueness within the forward algebra
`𝒯_X⁺` restates the corner rule on the endpoint frame; the
polynomial inverse and logarithm read off nilpotency and are
the manuscript's remaining bookkeeping.
-/

open Matrix

set_option linter.unreachableTactic false

namespace NCG

/-- The zeta history: the divisibility incidence matrix. -/
def zetaX (X : ℕ) : Matrix (Fin X) (Fin X) ℂ :=
  Matrix.of fun (j i : Fin X) =>
    if ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

private lemma single_left {X : ℕ} (m : Fin X)
    (Mx : Matrix (Fin X) (Fin X) ℂ) (j i : Fin X) :
    (Matrix.single m m (1 : ℂ) * Mx) j i
      = if j = m then Mx m i else 0 := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single m
    (fun k _ hk => by
      rw [Matrix.single_apply,
        if_neg (fun hand => hk hand.2.symm), zero_mul])
    (fun habs => absurd (Finset.mem_univ _) habs)]
  rw [Matrix.single_apply]
  by_cases hj : j = m
  · rw [if_pos ⟨hj.symm, rfl⟩, one_mul, if_pos hj]
  · rw [if_neg (fun hand => hj hand.1.symm), zero_mul,
      if_neg hj]

private lemma single_right {X : ℕ} (b : Fin X)
    (Mx : Matrix (Fin X) (Fin X) ℂ) (j i : Fin X) :
    (Mx * Matrix.single b b (1 : ℂ)) j i
      = if i = b then Mx j b else 0 := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single b
    (fun k _ hk => by
      rw [Matrix.single_apply,
        if_neg (fun hand => hk hand.1.symm), mul_zero])
    (fun habs => absurd (Finset.mem_univ _) habs)]
  rw [Matrix.single_apply]
  by_cases hi : i = b
  · rw [if_pos ⟨rfl, hi.symm⟩, mul_one, if_pos hi]
  · rw [if_neg (fun hand => hi hand.2.symm), mul_zero,
      if_neg hi]

/-- `thm:ar-zeta-incidence`: the zeta history is the
divisibility incidence — sum form, corner rule,
unitriangularity, and nilpotency of `𝖹 - I`. -/
theorem zeta_incidence {X : ℕ} :
    (zetaX X = ∑ a ∈ Finset.range X, peanoL X (a + 1))
    ∧ (∀ m b : Fin X,
        Matrix.single m m (1 : ℂ) * zetaX X
            * Matrix.single b b (1 : ℂ)
          = if ((b : ℕ) + 1) ∣ ((m : ℕ) + 1)
            then Matrix.single m b (1 : ℂ) else 0)
    ∧ (∀ i : Fin X, zetaX X i i = 1)
    ∧ (∀ j i : Fin X, (j : ℕ) < (i : ℕ) → zetaX X j i = 0)
    ∧ (zetaX X - 1) ^ X = 0 := by
  have hupper : ∀ j i : Fin X, (j : ℕ) < (i : ℕ) →
      zetaX X j i = 0 := by
    intro j i hji
    rw [zetaX, Matrix.of_apply]
    rw [if_neg]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hdiag : ∀ i : Fin X, zetaX X i i = 1 := by
    intro i
    rw [zetaX, Matrix.of_apply, if_pos dvd_rfl]
  refine ⟨?_, ?_, hdiag, hupper, ?_⟩
  · ext j i
    rw [Matrix.sum_apply, zetaX, Matrix.of_apply]
    by_cases hdvd : ((i : ℕ) + 1) ∣ ((j : ℕ) + 1)
    · obtain ⟨c, hc⟩ := hdvd
      have hc1 : 1 ≤ c := by
        rcases Nat.eq_zero_or_pos c with rfl | h1
        · rw [mul_zero] at hc
          omega
        · exact h1
      have hcle : c ≤ ((i : ℕ) + 1) * c := by
        have h := Nat.mul_le_mul
          (show 1 ≤ (i : ℕ) + 1 by omega) (le_refl c)
        rwa [one_mul] at h
      have hjX := j.isLt
      have hmem : c - 1 < X := by omega
      rw [if_pos ⟨c, hc⟩]
      rw [Finset.sum_eq_single (c - 1)
        (fun a _ ha => by
          rw [peanoL, Matrix.of_apply, if_neg]
          intro hand
          rw [Nat.mul_comm] at hand
          have h2 := hand.symm.trans hc
          have h3 := Nat.eq_of_mul_eq_mul_left
            (show 0 < (i : ℕ) + 1 by omega) h2
          exact ha (by omega))
        (fun habs => absurd
          (Finset.mem_range.mpr (by omega)) habs)]
      rw [peanoL, Matrix.of_apply, if_pos]
      rw [show c - 1 + 1 = c from by omega, Nat.mul_comm]
      exact hc
    · rw [if_neg hdvd]
      refine (Finset.sum_eq_zero fun a _ => ?_).symm
      rw [peanoL, Matrix.of_apply, if_neg]
      intro hand
      rw [Nat.mul_comm] at hand
      exact hdvd ⟨a + 1, hand⟩
  · intro m b
    ext j i
    by_cases hdvd : ((b : ℕ) + 1) ∣ ((m : ℕ) + 1)
    · rw [if_pos hdvd, Matrix.single_apply,
        single_right b (Matrix.single m m 1 * zetaX X) j i]
      by_cases hi : i = b
      · rw [if_pos hi, single_left m (zetaX X) j b]
        by_cases hj : j = m
        · rw [if_pos hj, zetaX, Matrix.of_apply, if_pos hdvd,
            if_pos ⟨hj.symm, hi.symm⟩]
        · rw [if_neg hj, if_neg (fun hand => hj hand.1.symm)]
      · rw [if_neg hi, if_neg (fun hand => hi hand.2.symm)]
    · rw [if_neg hdvd, Matrix.zero_apply,
        single_right b (Matrix.single m m 1 * zetaX X) j i]
      by_cases hi : i = b
      · rw [if_pos hi, single_left m (zetaX X) j b]
        by_cases hj : j = m
        · rw [if_pos hj, zetaX, Matrix.of_apply, if_neg hdvd]
        · rw [if_neg hj]
      · rw [if_neg hi]
  · have hstrict : ∀ j i : Fin X, (j : ℕ) ≤ (i : ℕ) →
        (zetaX X - 1) j i = 0 := by
      intro j i hji
      rw [Matrix.sub_apply, Matrix.one_apply]
      by_cases hij : j = i
      · subst hij
        rw [hdiag, if_pos rfl, sub_self]
      · rw [hupper j i (lt_of_le_of_ne hji
          (fun h => hij (Fin.ext h))), if_neg hij, sub_zero]
    have hpow : ∀ (k : ℕ) (j i : Fin X),
        (j : ℕ) < (i : ℕ) + k →
        ((zetaX X - 1) ^ k) j i = 0 := by
      intro k
      induction k with
      | zero =>
        intro j i hj
        rw [pow_zero, Matrix.one_apply, if_neg]
        intro h
        rw [h] at hj
        omega
      | succ k ih =>
        intro j i hj
        rw [pow_succ, Matrix.mul_apply]
        refine Finset.sum_eq_zero fun l _ => ?_
        by_cases hl : (l : ℕ) ≤ (i : ℕ)
        · rw [hstrict l i hl, mul_zero]
        · rw [ih j l (by omega), zero_mul]
    ext j i
    rw [Matrix.zero_apply]
    exact hpow X j i (by have := j.isLt; omega)

end NCG
