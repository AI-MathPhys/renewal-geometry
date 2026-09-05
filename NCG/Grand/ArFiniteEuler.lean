/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ArDerivedPacket
import NCG.Grand.ZetaIncidence

/-!
# Finite Euler logarithm, von Mangoldt commutator, and Möbius
  inverse (`thm:ar-finite-Euler`, Gran-Tensor manuscript)

* `ar_finite_euler`: each Euler factor `(I - L_p)⁻¹` is its
  terminating geometric series (two-sided inverse from
  nilpotency); the prime multiplication histories are nilpotent
  (`L_p^X = 0`); the boxed von Mangoldt anchor column
  `[H_X, log 𝖹_X] η^rec = Σ Λ(n) e_n`; and the boxed Möbius
  anchor column `(Σ μ(a) L_a)(𝖹_X η^rec) = η^rec`.

Rendering disclosed: the full matrix Euler product and the
matrix Möbius identity `𝖹_X⁻¹ = Σ μ(n) L_n` are the
manuscript's unique-factorization packaging of the proved
factorwise inverses and the proved anchor columns; `log 𝖹_X` is
rendered by its terminating prime-power expansion `logZop`
(`ar_derived_packet`), and the Möbius column is proved through
`μ * ζ = 1` on divisor sums.
-/

open Matrix

namespace NCG

/-- `thm:ar-finite-Euler`. -/
theorem ar_finite_euler {X : ℕ} (hX : 0 < X) :
    -- (1) terminating geometric two-sided inverse
    (∀ {R : Type} [Ring R] (N : R) (m : ℕ), N ^ m = 0 →
      (1 - N) * (∑ k ∈ Finset.range m, N ^ k) = 1
        ∧ (∑ k ∈ Finset.range m, N ^ k) * (1 - N) = 1)
    -- (2) prime multiplication histories are nilpotent
    ∧ (∀ p : ℕ, 2 ≤ p → peanoL X p ^ X = 0)
    -- (3) the boxed von Mangoldt anchor column
    ∧ ((countLog X * logZop X - logZop X * countLog X)
        *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
        = fun i : Fin X =>
            (ArithmeticFunction.vonMangoldt ((i : ℕ) + 1) : ℂ))
    -- (4) the boxed Möbius anchor column
    ∧ ((∑ a ∈ Finset.Icc 1 X,
          ((ArithmeticFunction.moebius a : ℤ) : ℂ)
            • peanoL X a)
        *ᵥ (zetaX X *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1)
        = Pi.single (⟨0, hX⟩ : Fin X) 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R _ N m hm
    have hgeom : (∑ k ∈ Finset.range m, N ^ k) * (N - 1)
        = N ^ m - 1 := geom_sum_mul N m
    rw [hm, zero_sub] at hgeom
    have hright : (∑ k ∈ Finset.range m, N ^ k) * (1 - N)
        = 1 := by
      have hneg : (∑ k ∈ Finset.range m, N ^ k) * (1 - N)
          = -((∑ k ∈ Finset.range m, N ^ k) * (N - 1)) := by
        rw [← mul_neg, neg_sub]
      rw [hneg, hgeom, neg_neg]
    have hcommN : Commute N (∑ k ∈ Finset.range m, N ^ k) :=
      Commute.sum_right _ _ _ fun k _ =>
        (Commute.refl N).pow_right k
    have hcomm : (1 - N) * (∑ k ∈ Finset.range m, N ^ k)
        = (∑ k ∈ Finset.range m, N ^ k) * (1 - N) :=
      ((Commute.one_left _).sub_left hcommN).eq
    exact ⟨by rw [hcomm, hright], hright⟩
  · intro p hp
    have hone : peanoL X 1 = 1 := by
      ext j i
      simp [peanoL, Matrix.one_apply, Fin.ext_iff]
    have hpow : ∀ k : ℕ, peanoL X p ^ k = peanoL X (p ^ k) := by
      intro k
      induction k with
      | zero => rw [pow_zero, pow_zero, hone]
      | succ k ih =>
          rw [pow_succ, ih, pow_succ,
            peano_product (p ^ k) p
              (Nat.one_le_pow _ _ (by omega)) (by omega)]
    have hbig : X < p ^ X :=
      lt_of_lt_of_le Nat.lt_two_pow_self
        (Nat.pow_le_pow_left hp X)
    have hzero : peanoL X (p ^ X) = 0 := by
      ext j i
      simp only [peanoL, Matrix.of_apply, Matrix.zero_apply]
      rw [if_neg]
      intro hc
      have h1 : p ^ X ≤ p ^ X * ((i : ℕ) + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      have h2 : (j : ℕ) < X := j.isLt
      omega
    rw [hpow, hzero]
  · have h5 := (ar_derived_packet hX).2.2.2.2 (fun _ => 1)
    rw [show diagFn X (fun _ => 1) = 1 from by
        rw [diagFn]; exact Matrix.diagonal_one,
      Matrix.one_mulVec] at h5
    rw [h5]
    funext i
    rw [one_mul]
  · have hones : zetaX X *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
        = fun _ => (1 : ℂ) := by
      funext j
      simp only [zetaX, Matrix.mulVec, dotProduct,
        Matrix.of_apply, Pi.single_apply]
      rw [Finset.sum_eq_single (⟨0, hX⟩ : Fin X)]
      · rw [if_pos rfl, mul_one,
          if_pos (show ((⟨0, hX⟩ : Fin X) : ℕ) + 1
              ∣ (j : ℕ) + 1 from by simp)]
      · intro k _ hk
        rw [if_neg (fun hc : k = (⟨0, hX⟩ : Fin X) => hk hc),
          mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ _) hk
    rw [hones]
    funext j
    rw [Matrix.sum_mulVec, Finset.sum_apply]
    have hcol : ∀ a : ℕ, 1 ≤ a →
        (peanoL X a *ᵥ fun _ => (1 : ℂ)) j
          = if a ∣ (j : ℕ) + 1 then 1 else 0 := by
      intro a ha
      simp only [Matrix.mulVec, dotProduct, peanoL,
        Matrix.of_apply, mul_one]
      by_cases hdvd : a ∣ (j : ℕ) + 1
      · obtain ⟨c, hc⟩ := hdvd
        have hc0 : c ≠ 0 := by
          rintro rfl
          omega
        have hcle : c ≤ (j : ℕ) + 1 := by
          calc c ≤ a * c := Nat.le_mul_of_pos_left c (by omega)
            _ = (j : ℕ) + 1 := hc.symm
        have hlt : c - 1 < X := by
          have := j.isLt
          omega
        rw [Finset.sum_eq_single (⟨c - 1, hlt⟩ : Fin X)]
        · have hcond : (j : ℕ) + 1
              = a * (((⟨c - 1, hlt⟩ : Fin X) : ℕ) + 1) := by
            have hval : ((⟨c - 1, hlt⟩ : Fin X) : ℕ)
                = c - 1 := rfl
            rw [hval, show c - 1 + 1 = c from by omega]
            exact hc
          rw [if_pos hcond, if_pos ⟨c, hc⟩]
        · intro k _ hk
          rw [if_neg]
          intro hcc
          apply hk
          have hac : a * ((k : ℕ) + 1) = a * c :=
            hcc.symm.trans hc
          have := Nat.eq_of_mul_eq_mul_left
            (show 0 < a by omega) hac
          have hval : ((⟨c - 1, hlt⟩ : Fin X) : ℕ) = c - 1 :=
            rfl
          exact Fin.ext (by rw [hval]; omega)
        · intro hk
          exact absurd (Finset.mem_univ _) hk
      · rw [if_neg hdvd]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [if_neg]
        intro hcc
        exact hdvd ⟨(k : ℕ) + 1, hcc⟩
    have hterm : ∀ a ∈ Finset.Icc 1 X,
        ((((ArithmeticFunction.moebius a : ℤ) : ℂ)
            • peanoL X a) *ᵥ fun _ => (1 : ℂ)) j
          = ((ArithmeticFunction.moebius a : ℤ) : ℂ)
              * (if a ∣ (j : ℕ) + 1 then 1 else 0) := by
      intro a hai
      rw [Matrix.smul_mulVec, Pi.smul_apply,
        hcol a (Finset.mem_Icc.mp hai).1, smul_eq_mul]
    rw [Finset.sum_congr rfl hterm]
    have hset : (Finset.Icc 1 X).filter (· ∣ (j : ℕ) + 1)
        = ((j : ℕ) + 1).divisors := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_Icc,
        Nat.mem_divisors]
      constructor
      · rintro ⟨⟨h1, hX'⟩, hdvd⟩
        exact ⟨hdvd, by omega⟩
      · rintro ⟨hdvd, -⟩
        have h1 : 1 ≤ a :=
          Nat.pos_of_dvd_of_pos hdvd (by omega)
        have h2 : a ≤ (j : ℕ) + 1 :=
          Nat.le_of_dvd (by omega) hdvd
        have := j.isLt
        exact ⟨⟨h1, by omega⟩, hdvd⟩
    have hfilter : ∑ a ∈ Finset.Icc 1 X,
        ((ArithmeticFunction.moebius a : ℤ) : ℂ)
          * (if a ∣ (j : ℕ) + 1 then 1 else 0)
        = ∑ a ∈ ((j : ℕ) + 1).divisors,
            ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
      rw [show ∑ a ∈ Finset.Icc 1 X,
          ((ArithmeticFunction.moebius a : ℤ) : ℂ)
            * (if a ∣ (j : ℕ) + 1 then 1 else 0)
          = ∑ a ∈ Finset.Icc 1 X,
              (if a ∣ (j : ℕ) + 1 then
                ((ArithmeticFunction.moebius a : ℤ) : ℂ)
                else 0) from
        Finset.sum_congr rfl fun a _ => by
          by_cases hd : a ∣ (j : ℕ) + 1 <;> simp [hd]]
      rw [← Finset.sum_filter, hset]
    rw [hfilter]
    have hmoebZ : ∑ a ∈ ((j : ℕ) + 1).divisors,
        ArithmeticFunction.moebius a
        = if (j : ℕ) + 1 = 1 then 1 else 0 := by
      have h := congrArg
        (fun f : ArithmeticFunction ℤ => f ((j : ℕ) + 1))
        ArithmeticFunction.moebius_mul_coe_zeta
      rw [ArithmeticFunction.mul_apply,
        ArithmeticFunction.one_apply] at h
      have hstep : ∑ x ∈ ((j : ℕ) + 1).divisorsAntidiagonal,
          ArithmeticFunction.moebius x.1
            * (↑ArithmeticFunction.zeta
                : ArithmeticFunction ℤ) x.2
          = ∑ a ∈ ((j : ℕ) + 1).divisors,
              ArithmeticFunction.moebius a := by
        rw [Nat.sum_divisorsAntidiagonal (fun d e =>
          ArithmeticFunction.moebius d
            * (↑ArithmeticFunction.zeta
                : ArithmeticFunction ℤ) e)]
        refine Finset.sum_congr rfl fun d hd => ?_
        obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.mp hd
        have hq : ((j : ℕ) + 1) / d ≠ 0 := by
          have hdle := Nat.le_of_dvd (by omega) hdvd
          have hdpos := Nat.pos_of_dvd_of_pos hdvd (by omega)
          have := Nat.div_pos hdle hdpos
          omega
        rw [ArithmeticFunction.natCoe_apply,
          ArithmeticFunction.zeta_apply, if_neg hq]
        simp
      rw [hstep] at h
      exact h
    have hmoebC : ∑ a ∈ ((j : ℕ) + 1).divisors,
        ((ArithmeticFunction.moebius a : ℤ) : ℂ)
        = if (j : ℕ) + 1 = 1 then 1 else 0 := by
      calc ∑ a ∈ ((j : ℕ) + 1).divisors,
            ((ArithmeticFunction.moebius a : ℤ) : ℂ)
          = (((∑ a ∈ ((j : ℕ) + 1).divisors,
              ArithmeticFunction.moebius a : ℤ)) : ℂ) := by
            rw [Int.cast_sum]
        _ = (((if (j : ℕ) + 1 = 1 then 1 else 0 : ℤ)) : ℂ) := by
            rw [hmoebZ]
        _ = if (j : ℕ) + 1 = 1 then 1 else 0 := by
            split_ifs <;> simp
    rw [hmoebC, Pi.single_apply]
    by_cases hj : (j : ℕ) = 0
    · rw [if_pos (by omega), if_pos (Fin.ext (by simp [hj]))]
    · rw [if_neg (by omega),
        if_neg (fun hc : j = (⟨0, hX⟩ : Fin X) =>
          hj (by rw [hc]))]

end NCG
