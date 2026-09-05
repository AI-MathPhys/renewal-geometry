/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.FiniteFourierOverlapBessel

/-!
# Pair-quotient carry Bessel theorem

The quotient indices contribute affine frequency shifts to the continuous
carry transform.  Their slice energies are controlled by the same
floor-coincidence kernel, before finite Fourier overlap is assembled.
-/

open Finset intervalIntegral

namespace NCG
namespace PairQuotientCarryBessel

open ContinuousMultiplicationCarryBessel
open FiniteFourierOverlapBessel

noncomputable section

def affineCarryNatFrequency (q a b : ℕ)
    (r s : Fin (q - 1)) : ℕ :=
  a * ((s : ℕ) + 1) + b * ((r : ℕ) + 1) +
    carryFrequency q r s

def affineCarryFrequency (q a b : ℕ)
    (r s : Fin (q - 1)) : ℤ :=
  -(affineCarryNatFrequency q a b r s : ℤ)

def affineCarryTransform (q a b : ℕ)
    (f : Fin (q - 1) → ℂ) (θ : ℝ) (r : Fin (q - 1)) : ℂ :=
  finiteFrequencyTransform (affineCarryFrequency q a b) f θ r

def affineCarryCoincidenceKernel (q a b : ℕ)
    (s t : Fin (q - 1)) : ℕ :=
  finiteFrequencyCoincidenceKernel
    (affineCarryFrequency q a b) s t

theorem carryFrequency_mono_right (q : ℕ)
    (r s t : Fin (q - 1)) (hst : (s : ℕ) ≤ t) :
    carryFrequency q r s ≤ carryFrequency q r t := by
  unfold carryFrequency
  apply Nat.div_le_div_right
  gcongr

theorem affineCarry_equal_imp_carry_equal
    (q a b : ℕ) (r s t : Fin (q - 1))
    (hfreq : affineCarryFrequency q a b r s =
      affineCarryFrequency q a b r t) :
    carryFrequency q r s = carryFrequency q r t := by
  unfold affineCarryFrequency at hfreq
  have hnat :
      affineCarryNatFrequency q a b r s =
        affineCarryNatFrequency q a b r t := by
    exact_mod_cast neg_inj.mp hfreq
  unfold affineCarryNatFrequency at hnat
  by_cases hst : (s : ℕ) ≤ t
  · have hcarry := carryFrequency_mono_right q r s t hst
    have ha :
        a * ((s : ℕ) + 1) ≤ a * ((t : ℕ) + 1) := by
      gcongr
    omega
  · have hts : (t : ℕ) ≤ s := by omega
    have hcarry := carryFrequency_mono_right q r t s hts
    have ha :
        a * ((t : ℕ) + 1) ≤ a * ((s : ℕ) + 1) := by
      gcongr
    omega

theorem affineCarryCoincidenceKernel_le_carry
    (q a b : ℕ) (s t : Fin (q - 1)) :
    affineCarryCoincidenceKernel q a b s t ≤
      carryCoincidenceKernel q s t := by
  unfold affineCarryCoincidenceKernel
  unfold finiteFrequencyCoincidenceKernel
  unfold carryCoincidenceKernel
  apply Finset.card_le_card
  intro r hr
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact affineCarry_equal_imp_carry_equal q a b r s t
    (Finset.mem_filter.mp hr).2

theorem affineCarryCoincidenceKernel_rowSum_log
    (q a b : ℕ) (hq : 2 ≤ q) (s : Fin (q - 1)) :
    (∑ t, (affineCarryCoincidenceKernel q a b s t : ℝ)) ≤
      5 * q * Real.log (2 * q) := by
  calc
    (∑ t, (affineCarryCoincidenceKernel q a b s t : ℝ))
        ≤ ∑ t, (carryCoincidenceKernel q s t : ℝ) := by
      apply Finset.sum_le_sum
      intro t _
      exact_mod_cast affineCarryCoincidenceKernel_le_carry q a b s t
    _ ≤ 5 * q * Real.log (2 * q) :=
      carryCoincidenceKernel_rowSum_log q hq s

theorem affineCarryBessel (q a b : ℕ) (hq : 2 ≤ q)
    (f : Fin (q - 1) → ℂ) :
    (∫ θ in (0 : ℝ)..1,
      ∑ r, ‖affineCarryTransform q a b f θ r‖ ^ 2) ≤
      5 * q * Real.log (2 * q) * ∑ s, ‖f s‖ ^ 2 := by
  unfold affineCarryTransform
  rw [← finiteFrequencyEnergy_re_eq_normSqIntegral]
  exact finiteFrequencyEnergy_re_le_of_rowSum
    (affineCarryFrequency q a b) f
    (5 * q * Real.log (2 * q))
    (affineCarryCoincidenceKernel_rowSum_log q a b hq)

def pairCarrySlice (q a b : ℕ)
    (p f : Fin (q - 1) → ℂ) (θ : ℝ) : ℂ :=
  ∑ r, p r * affineCarryTransform q a b f θ r

theorem pairCarrySlice_pointwise_cauchy (q a b : ℕ)
    (p f : Fin (q - 1) → ℂ) (θ : ℝ) :
    ‖pairCarrySlice q a b p f θ‖ ^ 2 ≤
      (∑ r, ‖p r‖ ^ 2) *
        ∑ r, ‖affineCarryTransform q a b f θ r‖ ^ 2 := by
  unfold pairCarrySlice
  have htriangle :
      ‖∑ r, p r * affineCarryTransform q a b f θ r‖ ≤
        ∑ r, ‖p r‖ *
          ‖affineCarryTransform q a b f θ r‖ := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro r _
    rw [norm_mul]
  have hnonneg :
      0 ≤ ∑ r, ‖p r‖ *
        ‖affineCarryTransform q a b f θ r‖ := by
    positivity
  have hsquare :
      ‖∑ r, p r * affineCarryTransform q a b f θ r‖ ^ 2 ≤
        (∑ r, ‖p r‖ *
          ‖affineCarryTransform q a b f θ r‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hnonneg).2 htriangle
  exact hsquare.trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun r => ‖p r‖)
      (fun r => ‖affineCarryTransform q a b f θ r‖))

theorem pairCarrySlice_bessel (q a b : ℕ) (hq : 2 ≤ q)
    (p f : Fin (q - 1) → ℂ) :
    (∫ θ in (0 : ℝ)..1,
      ‖pairCarrySlice q a b p f θ‖ ^ 2) ≤
      5 * q * Real.log (2 * q) *
        (∑ r, ‖p r‖ ^ 2) * (∑ s, ‖f s‖ ^ 2) := by
  have hmono :
      (∫ θ in (0 : ℝ)..1,
        ‖pairCarrySlice q a b p f θ‖ ^ 2) ≤
        ∫ θ in (0 : ℝ)..1,
          (∑ r, ‖p r‖ ^ 2) *
            ∑ r, ‖affineCarryTransform q a b f θ r‖ ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply Continuous.intervalIntegrable
      unfold pairCarrySlice affineCarryTransform
      fun_prop
    · apply Continuous.intervalIntegrable
      unfold affineCarryTransform
      fun_prop
    · intro θ hθ
      exact pairCarrySlice_pointwise_cauchy q a b p f θ
  calc
    (∫ θ in (0 : ℝ)..1,
      ‖pairCarrySlice q a b p f θ‖ ^ 2)
        ≤ ∫ θ in (0 : ℝ)..1,
          (∑ r, ‖p r‖ ^ 2) *
            ∑ r, ‖affineCarryTransform q a b f θ r‖ ^ 2 := hmono
    _ = (∑ r, ‖p r‖ ^ 2) *
        ∫ θ in (0 : ℝ)..1,
          ∑ r, ‖affineCarryTransform q a b f θ r‖ ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (∑ r, ‖p r‖ ^ 2) *
        (5 * q * Real.log (2 * q) * ∑ s, ‖f s‖ ^ 2) := by
      gcongr
      exact affineCarryBessel q a b hq f
    _ = 5 * q * Real.log (2 * q) *
        (∑ r, ‖p r‖ ^ 2) * (∑ s, ‖f s‖ ^ 2) := by
      ring

def pairCarryFrequency (q a b : ℕ)
    (r s : Fin (q - 1)) : ℕ :=
  q * a * b + affineCarryNatFrequency q a b r s

def pairCarryFrequencyBound (A q : ℕ) : ℕ :=
  q * (A + 1) * (A + 1) +
    2 * (A + 1) * q + q + 1

theorem pairCarryFrequency_lt_bound
    (A q : ℕ) (hq : 2 ≤ q) (a b : Fin (A + 1))
    (r s : Fin (q - 1)) :
    pairCarryFrequency q a b r s <
      pairCarryFrequencyBound A q := by
  have ha : (a : ℕ) ≤ A := by omega
  have hb : (b : ℕ) ≤ A := by omega
  have hr : (r : ℕ) + 1 < q := by omega
  have hs : (s : ℕ) + 1 < q := by omega
  have hab :
      (a : ℕ) * (b : ℕ) <
        (A + 1) * (A + 1) := by
    nlinarith
  have has :
      (a : ℕ) * ((s : ℕ) + 1) ≤ (A + 1) * q := by
    nlinarith
  have hbr :
      (b : ℕ) * ((r : ℕ) + 1) ≤ (A + 1) * q := by
    nlinarith
  have hrs :
      ((r : ℕ) + 1) * ((s : ℕ) + 1) < q * q := by
    nlinarith
  have hcarry : carryFrequency q r s < q := by
    unfold carryFrequency
    exact (Nat.div_lt_iff_lt_mul (by omega)).2 (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hrs)
  unfold pairCarryFrequency affineCarryNatFrequency
  unfold pairCarryFrequencyBound
  nlinarith

def quotientShiftedCarrySlice (q a b : ℕ)
    (p f : Fin (q - 1) → ℂ) (θ : ℝ) : ℂ :=
  integerCircleCharacter (-(q * a * b : ℤ)) θ *
    pairCarrySlice q a b p f θ

def pairQuotientCarryTransform (A q : ℕ)
    (p f : Fin (A + 1) → Fin (q - 1) → ℂ)
    (θ : ℝ) : ℂ :=
  ∑ a : Fin (A + 1), ∑ b : Fin (A + 1),
    quotientShiftedCarrySlice q (a : ℕ) (b : ℕ)
      (p a) (f b) θ

def pairCarrySliceSpectrum (A q : ℕ)
    (p f : Fin (A + 1) → Fin (q - 1) → ℂ)
    (a b : Fin (A + 1))
    (n : Fin (pairCarryFrequencyBound A q)) : ℂ :=
  ∑ r, ∑ s,
    if pairCarryFrequency q a b r s = (n : ℕ)
    then p a r * f b s else 0

theorem integerCircleCharacter_add (m n : ℤ) (θ : ℝ) :
    integerCircleCharacter (m + n) θ =
      integerCircleCharacter m θ *
        integerCircleCharacter n θ := by
  unfold integerCircleCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem quotientShiftedCarrySlice_expansion
    (q a b : ℕ) (p f : Fin (q - 1) → ℂ) (θ : ℝ) :
    quotientShiftedCarrySlice q a b p f θ =
      ∑ r, ∑ s, p r * f s *
        integerCircleCharacter
          (-(pairCarryFrequency q a b r s : ℤ)) θ := by
  unfold quotientShiftedCarrySlice pairCarrySlice
  unfold affineCarryTransform finiteFrequencyTransform
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  unfold affineCarryFrequency
  have hfreq :
      -(q * a * b : ℤ) +
          -(affineCarryNatFrequency q a b r s : ℤ) =
        -(pairCarryFrequency q a b r s : ℤ) := by
    unfold pairCarryFrequency
    push_cast
    ring
  calc
    integerCircleCharacter (-(q * a * b : ℤ)) θ *
        (p r * (integerCircleCharacter
          (-(affineCarryNatFrequency q a b r s : ℤ)) θ * f s)) =
      p r * f s *
        (integerCircleCharacter (-(q * a * b : ℤ)) θ *
          integerCircleCharacter
            (-(affineCarryNatFrequency q a b r s : ℤ)) θ) := by
      ring
    _ = p r * f s *
        integerCircleCharacter
          (-(q * a * b : ℤ) +
            -(affineCarryNatFrequency q a b r s : ℤ)) θ := by
      rw [integerCircleCharacter_add]
    _ = p r * f s *
        integerCircleCharacter
          (-(pairCarryFrequency q a b r s : ℤ)) θ := by
      rw [hfreq]

theorem pairCarrySliceSpectrum_polynomial
    (A q : ℕ) (hq : 2 ≤ q)
    (p f : Fin (A + 1) → Fin (q - 1) → ℂ)
    (a b : Fin (A + 1)) (θ : ℝ) :
    finiteFourierPolynomial
        (pairCarrySliceSpectrum A q p f a b) θ =
      quotientShiftedCarrySlice q (a : ℕ) (b : ℕ)
        (p a) (f b) θ := by
  rw [quotientShiftedCarrySlice_expansion]
  unfold finiteFourierPolynomial pairCarrySliceSpectrum
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  let n0 : Fin (pairCarryFrequencyBound A q) :=
    ⟨pairCarryFrequency q a b r s,
      pairCarryFrequency_lt_bound A q hq a b r s⟩
  rw [Finset.sum_eq_single n0]
  · simp [n0]
  · intro n _ hn
    have hne :
        pairCarryFrequency q a b r s ≠ (n : ℕ) := by
      intro h
      apply hn
      apply Fin.ext
      exact h.symm
    simp [hne]
  · simp

def quotientSliceWidth (A q : ℕ) : ℕ :=
  (2 * A + 1) * q

def quotientSupportAt (A q n : ℕ) (a : Fin (A + 1)) :
    Finset (Fin (A + 1)) :=
  (Finset.univ : Finset (Fin (A + 1))).filter
    (fun b =>
      q * (a : ℕ) * (b : ℕ) ≤ n ∧
      n < q * (a : ℕ) * (b : ℕ) + quotientSliceWidth A q)

theorem quotientSupportAt_card_le (A q n : ℕ)
    (hq : 0 < q) (a : Fin (A + 1)) :
    (quotientSupportAt A q n a).card ≤
      if (a : ℕ) = 0 then A + 1
      else quotientSliceWidth A q / (q * (a : ℕ)) + 1 := by
  by_cases ha : (a : ℕ) = 0
  · rw [if_pos ha]
    simpa using (quotientSupportAt A q n a).card_le_univ
  · rw [if_neg ha]
    let S := quotientSupportAt A q n a
    by_cases hS : S.Nonempty
    · let b0 : Fin (A + 1) := S.min' hS
      have hb0 : b0 ∈ S := S.min'_mem hS
      have hmin : ∀ b ∈ S, (b0 : ℕ) ≤ b := by
        intro b hb
        exact S.min'_le b hb
      have hd : 0 < q * (a : ℕ) := Nat.mul_pos hq (Nat.pos_of_ne_zero ha)
      have hcard := Finset.card_le_card_of_injOn
        (s := S)
        (t := Finset.range
          (quotientSliceWidth A q / (q * (a : ℕ)) + 1))
        (fun b : Fin (A + 1) => (b : ℕ) - (b0 : ℕ))
        (by
          intro b hb
          have hbData := (Finset.mem_filter.mp hb).2
          have hb0Data := (Finset.mem_filter.mp hb0).2
          have hb0b := hmin b hb
          have hprodle :
              q * (a : ℕ) * (b0 : ℕ) ≤
                q * (a : ℕ) * (b : ℕ) := by
            gcongr
          have hdecomp :
              q * (a : ℕ) * (b : ℕ) =
                q * (a : ℕ) * (b0 : ℕ) +
                  q * (a : ℕ) * ((b : ℕ) - (b0 : ℕ)) := by
            rw [Nat.mul_sub_left_distrib]
            omega
          have hmul :
              q * (a : ℕ) * ((b : ℕ) - (b0 : ℕ)) <
                quotientSliceWidth A q := by
            rw [hdecomp] at hbData
            omega
          have hdiv :
              (b : ℕ) - (b0 : ℕ) ≤
                quotientSliceWidth A q / (q * (a : ℕ)) :=
            (Nat.le_div_iff_mul_le hd).2 (by
              rw [Nat.mul_comm]
              omega)
          simp
          omega)
        (by
          intro b₁ hb₁ b₂ hb₂ heq
          have h₁ := hmin b₁ hb₁
          have h₂ := hmin b₂ hb₂
          change (b0 : ℕ) ≤ (b₁ : ℕ) at h₁
          change (b0 : ℕ) ≤ (b₂ : ℕ) at h₂
          change (b₁ : ℕ) - (b0 : ℕ) =
            (b₂ : ℕ) - (b0 : ℕ) at heq
          apply Fin.ext
          omega)
      simpa [S] using hcard
    · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [S, hempty]

def quotientOverlapBound (A q : ℕ) : ℕ :=
  ∑ a : Fin (A + 1),
    if (a : ℕ) = 0 then A + 1
    else quotientSliceWidth A q / (q * (a : ℕ)) + 1

theorem affineCarryNatFrequency_lt_width
    (A q : ℕ) (hq : 2 ≤ q) (a b : Fin (A + 1))
    (r s : Fin (q - 1)) :
    affineCarryNatFrequency q a b r s <
      quotientSliceWidth A q := by
  have ha : (a : ℕ) ≤ A := by omega
  have hb : (b : ℕ) ≤ A := by omega
  have hr : (r : ℕ) + 1 < q := by omega
  have hs : (s : ℕ) + 1 < q := by omega
  have has :
      (a : ℕ) * ((s : ℕ) + 1) ≤ A * (q - 1) := by
    exact Nat.mul_le_mul ha (by omega)
  have hbr :
      (b : ℕ) * ((r : ℕ) + 1) ≤ A * (q - 1) := by
    exact Nat.mul_le_mul hb (by omega)
  have hrs :
      ((r : ℕ) + 1) * ((s : ℕ) + 1) < q * q := by
    nlinarith
  have hcarry : carryFrequency q r s < q := by
    unfold carryFrequency
    exact (Nat.div_lt_iff_lt_mul (by omega)).2 (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hrs)
  unfold affineCarryNatFrequency quotientSliceWidth
  nlinarith

theorem pairCarrySliceSpectrum_nonzero_exists
    (A q : ℕ)
    (p f : Fin (A + 1) → Fin (q - 1) → ℂ)
    (a b : Fin (A + 1))
    (n : Fin (pairCarryFrequencyBound A q))
    (hn : pairCarrySliceSpectrum A q p f a b n ≠ 0) :
    ∃ r s : Fin (q - 1),
      pairCarryFrequency q a b r s = (n : ℕ) := by
  by_contra hex
  push Not at hex
  apply hn
  unfold pairCarrySliceSpectrum
  apply Finset.sum_eq_zero
  intro r _
  apply Finset.sum_eq_zero
  intro s _
  simp [hex r s]

theorem pairCarrySliceSpectrum_support
    (A q : ℕ) (hq : 2 ≤ q)
    (p f : Fin (A + 1) → Fin (q - 1) → ℂ)
    (a b : Fin (A + 1))
    (n : Fin (pairCarryFrequencyBound A q))
    (hn : pairCarrySliceSpectrum A q p f a b n ≠ 0) :
    b ∈ quotientSupportAt A q (n : ℕ) a := by
  obtain ⟨r, s, hrs⟩ :=
    pairCarrySliceSpectrum_nonzero_exists A q p f a b n hn
  have hwidth :=
    affineCarryNatFrequency_lt_width A q hq a b r s
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  unfold pairCarryFrequency at hrs
  constructor <;> omega

theorem quotientSupportPairs_card
    (A q n : ℕ) :
    ((Finset.univ :
        Finset (Fin (A + 1) × Fin (A + 1))).filter
      (fun ab => ab.2 ∈ quotientSupportAt A q n ab.1)).card =
      ∑ a, (quotientSupportAt A q n a).card := by
  rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.card_eq_sum_ones]
  simp

theorem pairCarrySliceSpectrum_overlap
    (A q : ℕ) (hq : 2 ≤ q)
    (p f : Fin (A + 1) → Fin (q - 1) → ℂ)
    (n : Fin (pairCarryFrequencyBound A q)) :
    ((Finset.univ :
        Finset (Fin (A + 1) × Fin (A + 1))).filter
      (fun ab =>
        pairCarrySliceSpectrum A q p f ab.1 ab.2 n ≠ 0)).card ≤
      quotientOverlapBound A q := by
  let T :=
    (Finset.univ :
      Finset (Fin (A + 1) × Fin (A + 1))).filter
      (fun ab => ab.2 ∈ quotientSupportAt A q (n : ℕ) ab.1)
  have hsubset :
      (Finset.univ :
        Finset (Fin (A + 1) × Fin (A + 1))).filter
          (fun ab =>
            pairCarrySliceSpectrum A q p f ab.1 ab.2 n ≠ 0) ⊆ T := by
    intro ab hab
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact pairCarrySliceSpectrum_support A q hq p f
      ab.1 ab.2 n (Finset.mem_filter.mp hab).2
  calc
    ((Finset.univ :
        Finset (Fin (A + 1) × Fin (A + 1))).filter
      (fun ab =>
        pairCarrySliceSpectrum A q p f ab.1 ab.2 n ≠ 0)).card
        ≤ T.card := Finset.card_le_card hsubset
    _ = ∑ a, (quotientSupportAt A q (n : ℕ) a).card := by
      exact quotientSupportPairs_card A q (n : ℕ)
    _ ≤ quotientOverlapBound A q := by
      unfold quotientOverlapBound
      apply Finset.sum_le_sum
      intro a _
      exact quotientSupportAt_card_le A q (n : ℕ) (by omega) a

theorem quotientOverlapBound_le_harmonic
    (A q : ℕ) (hq : 1 ≤ q) :
    (quotientOverlapBound A q : ℝ) ≤
      (A + 1 : ℕ) + (2 * A + 1) * (harmonic A : ℝ) + A := by
  unfold quotientOverlapBound
  rw [Fin.sum_univ_succ]
  push_cast
  simp only [Fin.val_zero, if_pos, Fin.val_succ,
    Nat.succ_ne_zero, if_false]
  have hterm : ∀ i : Fin A,
      (((quotientSliceWidth A q /
          (q * ((i.succ : Fin (A + 1)) : ℕ)) + 1 : ℕ) : ℝ)) ≤
        (2 * A + 1) * ((((i : ℕ) + 1 : ℕ) : ℝ)⁻¹) + 1 := by
    intro i
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have hi0 : (((i : ℕ) + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    calc
      (((quotientSliceWidth A q /
          (q * ((i.succ : Fin (A + 1)) : ℕ)) + 1 : ℕ) : ℝ)) =
          ((quotientSliceWidth A q /
            (q * ((i : ℕ) + 1) : ℕ) : ℕ) : ℝ) + 1 := by
              simp
      _ ≤ (quotientSliceWidth A q : ℝ) /
            (q * ((i : ℕ) + 1) : ℕ) + 1 := by
              gcongr
              exact Nat.cast_div_le
      _ = (2 * A + 1) * ((((i : ℕ) + 1 : ℕ) : ℝ)⁻¹) + 1 := by
              unfold quotientSliceWidth
              push_cast
              field_simp
  calc
    (A : ℝ) + 1 +
        ∑ i : Fin A,
          (((quotientSliceWidth A q /
            (q * ((i : ℕ) + 1)) : ℕ) : ℝ) + 1)
        ≤ (A : ℝ) + 1 +
          ∑ i : Fin A,
            ((2 * A + 1) * ((((i : ℕ) + 1 : ℕ) : ℝ)⁻¹) + 1) := by
          have hs :
              (∑ i : Fin A,
                (((quotientSliceWidth A q /
                  (q * ((i : ℕ) + 1)) : ℕ) : ℝ) + 1)) ≤
                ∑ i : Fin A,
                  ((2 * A + 1) *
                    ((((i : ℕ) + 1 : ℕ) : ℝ)⁻¹) + 1) :=
            Finset.sum_le_sum fun i _ => by simpa using hterm i
          linarith
    _ = (A : ℝ) + 1 + (2 * A + 1) * (harmonic A : ℝ) + A := by
          have hfin :
              (∑ i : Fin A, ((((i : ℕ) + 1 : ℕ) : ℝ)⁻¹)) =
                ∑ i ∈ Finset.range A, ((((i + 1 : ℕ) : ℝ)⁻¹)) := by
            exact Fin.sum_univ_eq_sum_range
              (fun i => ((((i + 1 : ℕ) : ℝ)⁻¹))) A
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfin,
            ← realHarmonic_eq_sum]
          simp
          ring

theorem quotientOverlapBound_le_log
    (A q : ℕ) (hA : 1 ≤ A) (hq : 1 ≤ q) :
    (quotientOverlapBound A q : ℝ) ≤
      12 * A * Real.log (2 * A) := by
  have hoverlap := quotientOverlapBound_le_harmonic A q hq
  have hApos : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have htwoApos : (0 : ℝ) < (2 * A : ℕ) := by positivity
  have hlogMono :
      Real.log (A : ℝ) ≤ Real.log ((2 * A : ℕ) : ℝ) := by
    apply Real.log_le_log hApos
    exact_mod_cast (show A ≤ 2 * A by omega)
  have hlogLower :
      (2 / 3 : ℝ) ≤ Real.log ((2 * A : ℕ) : ℝ) := by
    have htwo : (2 : ℝ) ≤ ((2 * A : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_le_mul_left 2 hA)
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 2) htwo
    nlinarith [Real.log_two_gt_d9]
  have hH := harmonic_le_one_add_log A
  have hHlog :
      (harmonic A : ℝ) ≤
        1 + Real.log ((2 * A : ℕ) : ℝ) := by
    linarith
  have hAcast : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hlogNonneg :
      0 ≤ Real.log ((2 * A : ℕ) : ℝ) := by linarith
  calc
    (quotientOverlapBound A q : ℝ) ≤
        (A + 1 : ℕ) + (2 * A + 1) * (harmonic A : ℝ) + A :=
      hoverlap
    _ ≤ (A : ℝ) + 1 + (2 * A + 1) *
          (1 + Real.log ((2 * A : ℕ) : ℝ)) + A := by
      push_cast
      gcongr
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hHlog
    _ ≤ 12 * A * Real.log ((2 * A : ℕ) : ℝ) := by
      nlinarith [mul_nonneg hApos.le hlogNonneg]
    _ = 12 * A * Real.log (2 * A) := by
      congr 2
      norm_num

theorem integerCircleCharacter_norm (n : ℤ) (θ : ℝ) :
    ‖integerCircleCharacter n θ‖ = 1 := by
  unfold integerCircleCharacter
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

theorem quotientShiftedCarrySlice_norm
    (q a b : ℕ) (p f : Fin (q - 1) → ℂ) (θ : ℝ) :
    ‖quotientShiftedCarrySlice q a b p f θ‖ =
      ‖pairCarrySlice q a b p f θ‖ := by
  unfold quotientShiftedCarrySlice
  rw [norm_mul, integerCircleCharacter_norm, one_mul]

theorem quotientShiftedCarrySlice_energy
    (q a b : ℕ) (p f : Fin (q - 1) → ℂ) :
    (∫ θ in (0 : ℝ)..1,
      ‖quotientShiftedCarrySlice q a b p f θ‖ ^ 2) =
      ∫ θ in (0 : ℝ)..1,
        ‖pairCarrySlice q a b p f θ‖ ^ 2 := by
  apply intervalIntegral.integral_congr
  intro θ _
  change ‖quotientShiftedCarrySlice q a b p f θ‖ ^ 2 =
    ‖pairCarrySlice q a b p f θ‖ ^ 2
  rw [quotientShiftedCarrySlice_norm]

set_option maxHeartbeats 800000 in
-- Elaborating the dependent finite Fourier family and both integral rewrites
-- requires more than the default budget, although each constituent lemma is small.
theorem pairQuotientCarryTransform_overlapBessel
    (A q : ℕ) (hq : 2 ≤ q)
    (p f : Fin (A + 1) → Fin (q - 1) → ℂ) :
    (∫ θ in (0 : ℝ)..1,
      ‖pairQuotientCarryTransform A q p f θ‖ ^ 2) ≤
      quotientOverlapBound A q *
        ∑ ab : Fin (A + 1) × Fin (A + 1),
          ∫ θ in (0 : ℝ)..1,
            ‖quotientShiftedCarrySlice q (ab.1 : ℕ) (ab.2 : ℕ)
              (p ab.1) (f ab.2) θ‖ ^ 2 := by
  have hfourier :=
    finiteFourierFamily_overlapBessel
      (M := quotientOverlapBound A q)
      (fun ab : Fin (A + 1) × Fin (A + 1) =>
        pairCarrySliceSpectrum A q p f ab.1 ab.2)
      (pairCarrySliceSpectrum_overlap A q hq p f)
  calc
    (∫ θ in (0 : ℝ)..1,
      ‖pairQuotientCarryTransform A q p f θ‖ ^ 2) =
        ∫ θ in (0 : ℝ)..1,
          ‖∑ ab : Fin (A + 1) × Fin (A + 1),
            finiteFourierPolynomial
              (pairCarrySliceSpectrum A q p f ab.1 ab.2) θ‖ ^ 2 := by
          apply intervalIntegral.integral_congr
          intro θ _
          change
            ‖∑ a : Fin (A + 1), ∑ b : Fin (A + 1),
              quotientShiftedCarrySlice q (a : ℕ) (b : ℕ)
                (p a) (f b) θ‖ ^ 2 =
            ‖∑ ab : Fin (A + 1) × Fin (A + 1),
              finiteFourierPolynomial
                (pairCarrySliceSpectrum A q p f ab.1 ab.2) θ‖ ^ 2
          congr 2
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [pairCarrySliceSpectrum_polynomial A q hq p f a b θ]
    _ ≤ quotientOverlapBound A q *
        ∑ ab : Fin (A + 1) × Fin (A + 1),
          ∫ θ in (0 : ℝ)..1,
            ‖finiteFourierPolynomial
              (pairCarrySliceSpectrum A q p f ab.1 ab.2) θ‖ ^ 2 :=
      hfourier
    _ = quotientOverlapBound A q *
        ∑ ab : Fin (A + 1) × Fin (A + 1),
          ∫ θ in (0 : ℝ)..1,
            ‖quotientShiftedCarrySlice q (ab.1 : ℕ) (ab.2 : ℕ)
              (p ab.1) (f ab.2) θ‖ ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro ab _
      apply intervalIntegral.integral_congr
      intro θ _
      change
        ‖finiteFourierPolynomial
          (pairCarrySliceSpectrum A q p f ab.1 ab.2) θ‖ ^ 2 =
        ‖quotientShiftedCarrySlice q (ab.1 : ℕ) (ab.2 : ℕ)
          (p ab.1) (f ab.2) θ‖ ^ 2
      rw [pairCarrySliceSpectrum_polynomial A q hq p f]

theorem quotientShiftedCarrySlice_familyBessel
    (A q : ℕ) (hq : 2 ≤ q)
    (p f : Fin (A + 1) → Fin (q - 1) → ℂ) :
    (∑ ab : Fin (A + 1) × Fin (A + 1),
      ∫ θ in (0 : ℝ)..1,
        ‖quotientShiftedCarrySlice q (ab.1 : ℕ) (ab.2 : ℕ)
          (p ab.1) (f ab.2) θ‖ ^ 2) ≤
      5 * q * Real.log (2 * q) *
        (∑ a, ∑ r, ‖p a r‖ ^ 2) *
        (∑ b, ∑ s, ‖f b s‖ ^ 2) := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ a : Fin (A + 1), ∑ b : Fin (A + 1),
      ∫ θ in (0 : ℝ)..1,
        ‖quotientShiftedCarrySlice q (a : ℕ) (b : ℕ)
          (p a) (f b) θ‖ ^ 2) =
        ∑ a : Fin (A + 1), ∑ b : Fin (A + 1),
          ∫ θ in (0 : ℝ)..1,
            ‖pairCarrySlice q (a : ℕ) (b : ℕ)
              (p a) (f b) θ‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact quotientShiftedCarrySlice_energy q a b (p a) (f b)
    _ ≤ ∑ a : Fin (A + 1), ∑ b : Fin (A + 1),
        5 * q * Real.log (2 * q) *
          (∑ r, ‖p a r‖ ^ 2) * (∑ s, ‖f b s‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact pairCarrySlice_bessel q a b hq (p a) (f b)
    _ = 5 * q * Real.log (2 * q) *
        (∑ a, ∑ r, ‖p a r‖ ^ 2) *
        (∑ b, ∑ s, ‖f b s‖ ^ 2) := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- The explicit pair-quotient carry estimate from
`thm:ar-pair-quotient-Bessel`. -/
theorem pairQuotientCarryBessel
    (A q : ℕ) (hA : 1 ≤ A) (hq : 2 ≤ q)
    (p f : Fin (A + 1) → Fin (q - 1) → ℂ) :
    (∫ θ in (0 : ℝ)..1,
      ‖pairQuotientCarryTransform A q p f θ‖ ^ 2) ≤
      60 * A * Real.log (2 * A) * q * Real.log (2 * q) *
        (∑ a, ∑ r, ‖p a r‖ ^ 2) *
        (∑ b, ∑ s, ‖f b s‖ ^ 2) := by
  have hoverlap :=
    pairQuotientCarryTransform_overlapBessel A q hq p f
  have hfamily := quotientShiftedCarrySlice_familyBessel A q hq p f
  have hcount := quotientOverlapBound_le_log A q hA (by omega)
  have hlogq : (0 : ℝ) ≤ Real.log (2 * q) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * q by omega)
  have hp : 0 ≤ ∑ a, ∑ r, ‖p a r‖ ^ 2 := by positivity
  have hf : 0 ≤ ∑ b, ∑ s, ‖f b s‖ ^ 2 := by positivity
  calc
    (∫ θ in (0 : ℝ)..1,
      ‖pairQuotientCarryTransform A q p f θ‖ ^ 2)
        ≤ quotientOverlapBound A q *
          ∑ ab : Fin (A + 1) × Fin (A + 1),
            ∫ θ in (0 : ℝ)..1,
              ‖quotientShiftedCarrySlice q (ab.1 : ℕ) (ab.2 : ℕ)
                (p ab.1) (f ab.2) θ‖ ^ 2 := hoverlap
    _ ≤ quotientOverlapBound A q *
        (5 * q * Real.log (2 * q) *
          (∑ a, ∑ r, ‖p a r‖ ^ 2) *
          (∑ b, ∑ s, ‖f b s‖ ^ 2)) := by
      gcongr
    _ ≤ (12 * A * Real.log (2 * A)) *
        (5 * q * Real.log (2 * q) *
          (∑ a, ∑ r, ‖p a r‖ ^ 2) *
          (∑ b, ∑ s, ‖f b s‖ ^ 2)) := by
      gcongr
    _ = 60 * A * Real.log (2 * A) * q * Real.log (2 * q) *
        (∑ a, ∑ r, ‖p a r‖ ^ 2) *
        (∑ b, ∑ s, ‖f b s‖ ^ 2) := by ring

/-- Separable unit-modulus character, Mellin, conductor, or coherent-history
twists leave the pair-quotient estimate unchanged. -/
theorem pairQuotientCarryBessel_unitTwists
    (A q : ℕ) (hA : 1 ≤ A) (hq : 2 ≤ q)
    (p f u v : Fin (A + 1) → Fin (q - 1) → ℂ)
    (hu : ∀ a r, ‖u a r‖ = 1)
    (hv : ∀ b s, ‖v b s‖ = 1) :
    (∫ θ in (0 : ℝ)..1,
      ‖pairQuotientCarryTransform A q
        (fun a r => u a r * p a r)
        (fun b s => v b s * f b s) θ‖ ^ 2) ≤
      60 * A * Real.log (2 * A) * q * Real.log (2 * q) *
        (∑ a, ∑ r, ‖p a r‖ ^ 2) *
        (∑ b, ∑ s, ‖f b s‖ ^ 2) := by
  have hp :
      (∑ a, ∑ r, ‖u a r * p a r‖ ^ 2) =
        ∑ a, ∑ r, ‖p a r‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro r _
    rw [norm_mul, hu, one_mul]
  have hf :
      (∑ b, ∑ s, ‖v b s * f b s‖ ^ 2) =
        ∑ b, ∑ s, ‖f b s‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro s _
    rw [norm_mul, hv, one_mul]
  have hbase := pairQuotientCarryBessel A q hA hq
      (fun a r => u a r * p a r)
      (fun b s => v b s * f b s)
  rw [hp, hf] at hbase
  exact hbase

/-- Prime-modulus wrapper matching the arithmetic formulation of the
manuscript theorem. -/
theorem pairQuotientCarryBesselTheorem
    (A q : ℕ) (hA : 1 ≤ A) (hq : q.Prime)
    (p f : Fin (A + 1) → Fin (q - 1) → ℂ) :
    (∫ θ in (0 : ℝ)..1,
      ‖pairQuotientCarryTransform A q p f θ‖ ^ 2) ≤
      60 * A * Real.log (2 * A) * q * Real.log (2 * q) *
        (∑ a, ∑ r, ‖p a r‖ ^ 2) *
        (∑ b, ∑ s, ‖f b s‖ ^ 2) :=
  pairQuotientCarryBessel A q hA hq.two_le p f

end
end PairQuotientCarryBessel
end NCG
