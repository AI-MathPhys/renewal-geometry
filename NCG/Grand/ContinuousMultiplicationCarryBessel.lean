/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Arithmetic.AffineSelectors
import NCG.Flagship.YMTail
import NCG.Grand.ArCarryBessel

/-!
# Continuous multiplication-carry Bessel bound

This file constructs the multiplication-carry transform on the nonzero
residues, identifies its continuous phase energy with the exact
floor-coincidence Gram kernel, and supplies the finite Schur estimate used in
the manuscript.
-/

open Finset intervalIntegral

namespace NCG
namespace ContinuousMultiplicationCarryBessel

noncomputable section

/-- Integer circle character on the unit interval. -/
def integerCircleCharacter (n : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * n * θ)

theorem integerCircleCharacter_orthogonality (m n : ℤ) :
    (∫ θ in (0 : ℝ)..1,
      integerCircleCharacter m θ *
        star (integerCircleCharacter n θ)) =
      if m = n then 1 else 0 := by
  have hpoint : ∀ θ : ℝ,
      integerCircleCharacter m θ *
          star (integerCircleCharacter n θ) =
        integerCircleCharacter (m - n) θ := by
    intro θ
    unfold integerCircleCharacter
    change Complex.exp (2 * Real.pi * Complex.I * m * θ) *
        (starRingEnd ℂ) (Complex.exp
          (2 * Real.pi * Complex.I * n * θ)) = _
    rw [← Complex.exp_conj]
    simp only [map_mul, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I, map_intCast]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [intervalIntegral.integral_congr fun θ _ => hpoint θ]
  unfold integerCircleCharacter
  rw [NCG.AffineSelectors.selector_integral]
  by_cases hmn : m = n
  · rw [if_pos hmn, if_pos (sub_eq_zero.mpr hmn)]
  · rw [if_neg hmn, if_neg (sub_ne_zero.mpr hmn)]

/-- The integer carry frequency for nonzero representatives
from one through q minus one. -/
def carryFrequency (q : ℕ) (r s : Fin (q - 1)) : ℕ :=
  ((r : ℕ) + 1) * ((s : ℕ) + 1) / q

/-- The manuscript's negative multiplication-carry phase. -/
def carryPhase (q : ℕ) (r s : Fin (q - 1)) (θ : ℝ) : ℂ :=
  integerCircleCharacter (-(carryFrequency q r s : ℤ)) θ

/-- Continuous multiplication-carry transform on the nonzero residues. -/
def carryTransform (q : ℕ) (f : Fin (q - 1) → ℂ)
    (θ : ℝ) (r : Fin (q - 1)) : ℂ :=
  ∑ s, carryPhase q r s θ * f s

/-- Exact number of rows on which two columns have the same carry. -/
def carryCoincidenceKernel (q : ℕ) (s t : Fin (q - 1)) : ℕ :=
  ((Finset.univ : Finset (Fin (q - 1))).filter
    (fun r => carryFrequency q r s = carryFrequency q r t)).card

theorem carryCoincidenceKernel_symmetric (q : ℕ)
    (s t : Fin (q - 1)) :
    carryCoincidenceKernel q s t = carryCoincidenceKernel q t s := by
  unfold carryCoincidenceKernel
  congr 1
  ext r
  simp [eq_comm]

theorem carryCoincidenceKernel_nonnegative (q : ℕ)
    (s t : Fin (q - 1)) :
    0 ≤ (carryCoincidenceKernel q s t : ℝ) := by
  positivity

theorem equalCarry_mul_distance_lt (q : ℕ)
    (r s t : Fin (q - 1)) (hq : 0 < q)
    (hcarry : carryFrequency q r s = carryFrequency q r t) :
    ((r : ℕ) + 1) * Nat.dist (s : ℕ) t < q := by
  unfold carryFrequency at hcarry
  by_cases hst : (s : ℕ) ≤ t
  · have hloc := NCG.ar_carry_bessel.2.1 q
      ((r : ℕ) + 1) ((t : ℕ) + 1) ((s : ℕ) + 1)
      hq (by omega) hcarry.symm
    rw [Nat.dist_eq_sub_of_le hst]
    have hdiff :
        ((t : ℕ) + 1) - ((s : ℕ) + 1) =
          (t : ℕ) - s := by omega
    rw [hdiff] at hloc
    exact hloc
  · have hloc := NCG.ar_carry_bessel.2.1 q
      ((r : ℕ) + 1) ((s : ℕ) + 1) ((t : ℕ) + 1)
      hq (by omega) hcarry
    have hts : (t : ℕ) ≤ s := by omega
    rw [Nat.dist_eq_sub_of_le_right hts]
    have hdiff :
        ((s : ℕ) + 1) - ((t : ℕ) + 1) =
          (s : ℕ) - t := by omega
    rw [hdiff] at hloc
    exact hloc

theorem carryCoincidenceKernel_offDiagonal_bound (q : ℕ)
    (s t : Fin (q - 1)) (hq : 0 < q) (hst : s ≠ t) :
    carryCoincidenceKernel q s t ≤
      (q - 1) / Nat.dist (s : ℕ) t := by
  have hval : (s : ℕ) ≠ t := fun h => hst (Fin.ext h)
  have hd : 0 < Nat.dist (s : ℕ) t := Nat.dist_pos_of_ne hval
  unfold carryCoincidenceKernel
  have hcard := Finset.card_le_card_of_injOn
    (s := (Finset.univ : Finset (Fin (q - 1))).filter
      (fun r => carryFrequency q r s = carryFrequency q r t))
    (t := Finset.range ((q - 1) / Nat.dist (s : ℕ) t))
    (fun r : Fin (q - 1) => (r : ℕ))
    (by
      intro r hr
      have hcarry :
          carryFrequency q r s = carryFrequency q r t :=
        (Finset.mem_filter.mp hr).2
      have hloc := equalCarry_mul_distance_lt q r s t hq hcarry
      have hmul :
          ((r : ℕ) + 1) * Nat.dist (s : ℕ) t ≤ q - 1 := by
        omega
      have hquot :
          (r : ℕ) + 1 ≤
            (q - 1) / Nat.dist (s : ℕ) t :=
        (Nat.le_div_iff_mul_le hd).2 hmul
      simp
      omega)
    (by
      intro a ha b hb hab
      exact Fin.ext hab)
  simpa using hcard

theorem sum_left_inverse_distance (n : ℕ) (s : Fin n) :
    (∑ t ∈ (Finset.univ : Finset (Fin n)).filter
        (fun t : Fin n => (t : ℕ) < (s : ℕ)),
      (((s : ℕ) - t : ℕ) : ℝ)⁻¹) =
      ∑ i ∈ Finset.range (s : ℕ),
        (((i + 1 : ℕ) : ℝ)⁻¹) := by
  refine Finset.sum_bij
    (fun t _ => (s : ℕ) - (t : ℕ) - 1) ?_ ?_ ?_ ?_
  · intro t ht
    have hlt := (Finset.mem_filter.mp ht).2
    simp
    omega
  · intro t₁ ht₁ t₂ ht₂ heq
    have h₁ := (Finset.mem_filter.mp ht₁).2
    have h₂ := (Finset.mem_filter.mp ht₂).2
    apply Fin.ext
    omega
  · intro i hi
    have hi' : i < (s : ℕ) := Finset.mem_range.mp hi
    let t : Fin n :=
      ⟨(s : ℕ) - i - 1, by
        have hs := s.isLt
        omega⟩
    refine ⟨t, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by
        change (s : ℕ) - i - 1 < s
        omega⟩
    · change (s : ℕ) - ((s : ℕ) - i - 1) - 1 = i
      omega
  · intro t ht
    have hlt := (Finset.mem_filter.mp ht).2
    congr 2
    omega

theorem sum_right_inverse_distance (n : ℕ) (s : Fin n) :
    (∑ t ∈ (Finset.univ : Finset (Fin n)).filter
        (fun t : Fin n => (s : ℕ) < (t : ℕ)),
      (((t : ℕ) - s : ℕ) : ℝ)⁻¹) =
      ∑ i ∈ Finset.range (n - (s : ℕ) - 1),
        (((i + 1 : ℕ) : ℝ)⁻¹) := by
  refine Finset.sum_bij
    (fun t _ => (t : ℕ) - (s : ℕ) - 1) ?_ ?_ ?_ ?_
  · intro t ht
    have hlt := (Finset.mem_filter.mp ht).2
    have htN := t.isLt
    simp
    omega
  · intro t₁ ht₁ t₂ ht₂ heq
    have h₁ := (Finset.mem_filter.mp ht₁).2
    have h₂ := (Finset.mem_filter.mp ht₂).2
    apply Fin.ext
    omega
  · intro i hi
    have hi' : i < n - (s : ℕ) - 1 := Finset.mem_range.mp hi
    let t : Fin n :=
      ⟨(s : ℕ) + i + 1, by omega⟩
    refine ⟨t, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by
        change (s : ℕ) < (s : ℕ) + i + 1
        omega⟩
    · change (s : ℕ) + i + 1 - (s : ℕ) - 1 = i
      omega
  · intro t ht
    have hlt := (Finset.mem_filter.mp ht).2
    congr 2
    omega

theorem inverseDistanceSum_le_two_harmonicSum
    (n : ℕ) (s : Fin n) :
    (∑ t : Fin n,
      if t = s then 0
      else ((Nat.dist (s : ℕ) t : ℕ) : ℝ)⁻¹) ≤
      2 * ∑ i ∈ Finset.range n,
        (((i + 1 : ℕ) : ℝ)⁻¹) := by
  have hleft :
      (∑ t : Fin n,
        if (t : ℕ) < (s : ℕ)
        then ((((s : ℕ) - t : ℕ) : ℝ)⁻¹) else 0) =
        ∑ i ∈ Finset.range (s : ℕ),
          (((i + 1 : ℕ) : ℝ)⁻¹) := by
    rw [← Finset.sum_filter]
    exact sum_left_inverse_distance n s
  have hright :
      (∑ t : Fin n,
        if (s : ℕ) < (t : ℕ)
        then ((((t : ℕ) - s : ℕ) : ℝ)⁻¹) else 0) =
        ∑ i ∈ Finset.range (n - (s : ℕ) - 1),
          (((i + 1 : ℕ) : ℝ)⁻¹) := by
    rw [← Finset.sum_filter]
    exact sum_right_inverse_distance n s
  have hsplit :
      (∑ t : Fin n,
        if t = s then 0
        else ((Nat.dist (s : ℕ) t : ℕ) : ℝ)⁻¹) =
        (∑ t : Fin n,
          if (t : ℕ) < (s : ℕ)
          then ((((s : ℕ) - t : ℕ) : ℝ)⁻¹) else 0) +
        (∑ t : Fin n,
          if (s : ℕ) < (t : ℕ)
          then ((((t : ℕ) - s : ℕ) : ℝ)⁻¹) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hts : (t : ℕ) < s
    · have hne : t ≠ s := fun h => by subst t; omega
      rw [if_neg hne, if_pos hts, if_neg (by omega)]
      rw [Nat.dist_eq_sub_of_le_right (by omega)]
      simp
    · by_cases hst : (s : ℕ) < t
      · have hne : t ≠ s := fun h => by subst t; omega
        rw [if_neg hne, if_neg hts, if_pos hst]
        rw [Nat.dist_eq_sub_of_le (by omega)]
        simp
      · have heq : t = s := Fin.ext (by omega)
        rw [if_pos heq, if_neg hts, if_neg hst]
        simp
  have hleftBound :
      (∑ i ∈ Finset.range (s : ℕ),
        (((i + 1 : ℕ) : ℝ)⁻¹)) ≤
        ∑ i ∈ Finset.range n,
          (((i + 1 : ℕ) : ℝ)⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.le_of_lt s.isLt))
    intro i hi hnot
    positivity
  have hrightIndex : n - (s : ℕ) - 1 ≤ n := by omega
  have hrightBound :
      (∑ i ∈ Finset.range (n - (s : ℕ) - 1),
        (((i + 1 : ℕ) : ℝ)⁻¹)) ≤
        ∑ i ∈ Finset.range n,
          (((i + 1 : ℕ) : ℝ)⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono hrightIndex)
    intro i hi hnot
    positivity
  rw [hsplit, hleft, hright]
  nlinarith

theorem realHarmonic_eq_sum (n : ℕ) :
    (harmonic n : ℝ) =
      ∑ i ∈ Finset.range n,
        (((i + 1 : ℕ) : ℝ)⁻¹) := by
  unfold harmonic
  push_cast
  rfl

theorem carryCoincidenceKernel_diagonal (q : ℕ)
    (s : Fin (q - 1)) :
    carryCoincidenceKernel q s s = q - 1 := by
  simp [carryCoincidenceKernel]

theorem carryCoincidenceKernel_rowSum_harmonic
    (q : ℕ) (hq : 0 < q) (s : Fin (q - 1)) :
    (∑ t, (carryCoincidenceKernel q s t : ℝ)) ≤
      (q - 1 : ℕ) *
        (1 + 2 * (harmonic (q - 1) : ℝ)) := by
  have hterm : ∀ t : Fin (q - 1),
      (carryCoincidenceKernel q s t : ℝ) ≤
        (q - 1 : ℕ) *
          (if t = s then 1
          else ((Nat.dist (s : ℕ) t : ℕ) : ℝ)⁻¹) := by
    intro t
    by_cases hts : t = s
    · subst t
      rw [if_pos rfl, carryCoincidenceKernel_diagonal]
      norm_num
    · rw [if_neg hts]
      have hnat :=
        carryCoincidenceKernel_offDiagonal_bound q s t hq
          (Ne.symm hts)
      have hcast :
          (carryCoincidenceKernel q s t : ℝ) ≤
            (((q - 1) / Nat.dist (s : ℕ) t : ℕ) : ℝ) := by
        exact_mod_cast hnat
      calc
        (carryCoincidenceKernel q s t : ℝ)
            ≤ (((q - 1) / Nat.dist (s : ℕ) t : ℕ) : ℝ) :=
          hcast
        _ ≤ ((q - 1 : ℕ) : ℝ) /
              ((Nat.dist (s : ℕ) t : ℕ) : ℝ) :=
          Nat.cast_div_le
        _ = (q - 1 : ℕ) *
              ((Nat.dist (s : ℕ) t : ℕ) : ℝ)⁻¹ := by
          rw [div_eq_mul_inv]
  have hsumTerm :
      (∑ t, (carryCoincidenceKernel q s t : ℝ)) ≤
        ∑ t, (q - 1 : ℕ) *
          (if t = s then 1
          else ((Nat.dist (s : ℕ) t : ℕ) : ℝ)⁻¹) :=
    Finset.sum_le_sum fun t _ => hterm t
  have hsplit :
      (∑ t : Fin (q - 1),
        if t = s then (1 : ℝ)
        else ((Nat.dist (s : ℕ) t : ℕ) : ℝ)⁻¹) =
        1 + ∑ t : Fin (q - 1),
          if t = s then 0
          else ((Nat.dist (s : ℕ) t : ℕ) : ℝ)⁻¹ := by
    calc
      (∑ t : Fin (q - 1),
        if t = s then (1 : ℝ)
        else ((Nat.dist (s : ℕ) t : ℕ) : ℝ)⁻¹) =
          ∑ t : Fin (q - 1),
            ((if t = s then (1 : ℝ) else 0) +
              (if t = s then 0
              else ((Nat.dist (s : ℕ) t : ℕ) : ℝ)⁻¹)) := by
        apply Finset.sum_congr rfl
        intro t _
        by_cases hts : t = s <;> simp [hts]
      _ = (∑ t : Fin (q - 1),
            if t = s then (1 : ℝ) else 0) +
          ∑ t : Fin (q - 1),
            if t = s then 0
            else ((Nat.dist (s : ℕ) t : ℕ) : ℝ)⁻¹ := by
        rw [Finset.sum_add_distrib]
      _ = 1 + ∑ t : Fin (q - 1),
            if t = s then 0
            else ((Nat.dist (s : ℕ) t : ℕ) : ℝ)⁻¹ := by
        simp
  calc
    (∑ t, (carryCoincidenceKernel q s t : ℝ))
        ≤ ∑ t, (q - 1 : ℕ) *
            (if t = s then 1
            else ((Nat.dist (s : ℕ) t : ℕ) : ℝ)⁻¹) :=
      hsumTerm
    _ = (q - 1 : ℕ) *
        (∑ t : Fin (q - 1),
          if t = s then 1
          else ((Nat.dist (s : ℕ) t : ℕ) : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
    _ = (q - 1 : ℕ) *
        (1 + ∑ t : Fin (q - 1),
          if t = s then 0
          else ((Nat.dist (s : ℕ) t : ℕ) : ℝ)⁻¹) := by
      rw [hsplit]
    _ ≤ (q - 1 : ℕ) *
        (1 + 2 * (∑ i ∈ Finset.range (q - 1),
          (((i + 1 : ℕ) : ℝ)⁻¹))) := by
      gcongr
      exact inverseDistanceSum_le_two_harmonicSum (q - 1) s
    _ = (q - 1 : ℕ) *
        (1 + 2 * (harmonic (q - 1) : ℝ)) := by
      rw [realHarmonic_eq_sum]

theorem carryCoincidenceKernel_rowSum_log
    (q : ℕ) (hq : 2 ≤ q) (s : Fin (q - 1)) :
    (∑ t, (carryCoincidenceKernel q s t : ℝ)) ≤
      5 * q * Real.log (2 * q) := by
  have hrow :=
    carryCoincidenceKernel_rowSum_harmonic q (by omega) s
  have hH := harmonic_le_one_add_log (q - 1)
  have hqsubPos : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt hq)
  have hlogMono :
      Real.log ((q - 1 : ℕ) : ℝ) ≤
        Real.log ((2 * q : ℕ) : ℝ) := by
    apply Real.log_le_log hqsubPos
    exact_mod_cast (show q - 1 ≤ 2 * q by omega)
  have hlogFour : (1 : ℝ) ≤ Real.log 4 := by
    have hlogTwo := Real.log_two_gt_d9
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul
      (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    nlinarith
  have hfour : (4 : ℝ) ≤ (2 * q : ℕ) := by
    exact_mod_cast (Nat.mul_le_mul_left 2 hq)
  have hlogLower : (1 : ℝ) ≤ Real.log ((2 * q : ℕ) : ℝ) :=
    hlogFour.trans (Real.log_le_log (by norm_num) hfour)
  have hfactor :
      1 + 2 * (harmonic (q - 1) : ℝ) ≤
        5 * Real.log ((2 * q : ℕ) : ℝ) := by
    have hH' :
        (harmonic (q - 1) : ℝ) ≤
          1 + Real.log ((q - 1 : ℕ) : ℝ) := hH
    nlinarith
  have hfactorNonneg :
      0 ≤ 1 + 2 * (harmonic (q - 1) : ℝ) := by
    rw [realHarmonic_eq_sum]
    positivity
  calc
    (∑ t, (carryCoincidenceKernel q s t : ℝ))
        ≤ (q - 1 : ℕ) *
            (1 + 2 * (harmonic (q - 1) : ℝ)) := hrow
    _ ≤ q * (1 + 2 * (harmonic (q - 1) : ℝ)) := by
      gcongr
      · exact_mod_cast (Nat.sub_le q 1)
    _ ≤ q * (5 * Real.log ((2 * q : ℕ) : ℝ)) := by
      gcongr
    _ = 5 * q * Real.log (2 * q) := by
      push_cast
      ring

/-- Orthogonality converts the continuous energy exactly into the finite
selector sum. -/
theorem carryEnergy_eq_selectorSum (q : ℕ)
    (f : Fin (q - 1) → ℂ) :
    (∫ θ in (0 : ℝ)..1,
      ∑ r, carryTransform q f θ r *
        star (carryTransform q f θ r)) =
      ∑ r, ∑ s, ∑ t,
        if carryFrequency q r s = carryFrequency q r t
        then f s * star (f t) else 0 := by
  rw [intervalIntegral.integral_finsetSum fun r _ =>
    (Continuous.intervalIntegrable (by
      unfold carryTransform carryPhase integerCircleCharacter
      fun_prop) _ _)]
  apply Finset.sum_congr rfl
  intro r _
  unfold carryTransform
  change (∫ θ in (0 : ℝ)..1,
      (∑ s, carryPhase q r s θ * f s) *
        (starRingEnd ℂ) (∑ s, carryPhase q r s θ * f s)) =
    _
  rw [intervalIntegral.integral_congr fun θ _ => by
    rw [map_sum, Finset.sum_mul_sum]]
  rw [intervalIntegral.integral_finsetSum fun s _ =>
    (Continuous.intervalIntegrable (by
      unfold carryPhase integerCircleCharacter
      fun_prop) _ _)]
  apply Finset.sum_congr rfl
  intro s _
  rw [intervalIntegral.integral_finsetSum fun t _ =>
    (Continuous.intervalIntegrable (by
      unfold carryPhase integerCircleCharacter
      fun_prop) _ _)]
  apply Finset.sum_congr rfl
  intro t _
  have hpoint : ∀ θ : ℝ,
      (carryPhase q r s θ * f s) *
          (star (carryPhase q r t θ) * star (f t)) =
        (f s * star (f t)) *
          (carryPhase q r s θ * star (carryPhase q r t θ)) := by
    intro θ
    ring
  have hpoint' : ∀ θ : ℝ,
      (carryPhase q r s θ * f s) *
          (starRingEnd ℂ) (carryPhase q r t θ * f t) =
        (f s * star (f t)) *
          (carryPhase q r s θ * star (carryPhase q r t θ)) := by
    intro θ
    rw [map_mul]
    exact hpoint θ
  rw [intervalIntegral.integral_congr fun θ _ => hpoint' θ,
    intervalIntegral.integral_const_mul]
  unfold carryPhase
  rw [integerCircleCharacter_orthogonality]
  by_cases hfreq : carryFrequency q r s = carryFrequency q r t
  · rw [if_pos hfreq]
    have hneg :
        -(carryFrequency q r s : ℤ) =
          -(carryFrequency q r t : ℤ) := by
      exact congrArg (fun u : ℕ => -(u : ℤ)) hfreq
    rw [if_pos hneg, mul_one]
  · rw [if_neg hfreq]
    have hneg :
        -(carryFrequency q r s : ℤ) ≠
          -(carryFrequency q r t : ℤ) := by
      exact fun h => hfreq (by exact_mod_cast neg_inj.mp h)
    rw [if_neg hneg, mul_zero]

theorem carrySelectorSum_eq_kernelQuadratic (q : ℕ)
    (f : Fin (q - 1) → ℂ) :
    (∑ r, ∑ s, ∑ t,
        if carryFrequency q r s = carryFrequency q r t
        then f s * star (f t) else 0) =
      ∑ s, ∑ t,
        (carryCoincidenceKernel q s t : ℂ) *
          (f s * star (f t)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  unfold carryCoincidenceKernel
  rw [← Finset.sum_filter]
  simp

theorem carryEnergy_eq_kernelQuadratic (q : ℕ)
    (f : Fin (q - 1) → ℂ) :
    (∫ θ in (0 : ℝ)..1,
      ∑ r, carryTransform q f θ r *
        star (carryTransform q f θ r)) =
      ∑ s, ∑ t,
        (carryCoincidenceKernel q s t : ℂ) *
          (f s * star (f t)) :=
  (carryEnergy_eq_selectorSum q f).trans
    (carrySelectorSum_eq_kernelQuadratic q f)

/-- Finite Schur assembly: any uniform row-sum bound for the carry kernel
immediately bounds the exact continuous carry energy. -/
theorem carryEnergy_re_le_of_rowSum (q : ℕ)
    (f : Fin (q - 1) → ℂ) (C : ℝ)
    (hrow : ∀ s, ∑ t, (carryCoincidenceKernel q s t : ℝ) ≤ C) :
    ((∫ θ in (0 : ℝ)..1,
      ∑ r, carryTransform q f θ r *
        star (carryTransform q f θ r))).re ≤
      C * ∑ s, ‖f s‖ ^ 2 := by
  rw [carryEnergy_eq_kernelQuadratic]
  have hterm : ∀ s t : Fin (q - 1),
      (((carryCoincidenceKernel q s t : ℂ) *
          (f s * star (f t))).re) ≤
        (carryCoincidenceKernel q s t : ℝ) *
          (‖f s‖ * ‖f t‖) := by
    intro s t
    have hre : (f s * star (f t)).re ≤
        ‖f s * star (f t)‖ := Complex.re_le_norm _
    have hK : 0 ≤ (carryCoincidenceKernel q s t : ℝ) := by
      positivity
    simpa [Complex.mul_re, norm_mul] using
      (mul_le_mul_of_nonneg_left hre hK)
  have hsum :
      (∑ s, ∑ t,
          ((carryCoincidenceKernel q s t : ℂ) *
            (f s * star (f t))).re) ≤
        ∑ s, ∑ t,
          (carryCoincidenceKernel q s t : ℝ) *
            (‖f s‖ * ‖f t‖) :=
    Finset.sum_le_sum fun s _ =>
      Finset.sum_le_sum fun t _ => hterm s t
  have hschur := NCG.schur_test
    (fun s t : Fin (q - 1) =>
      (carryCoincidenceKernel q s t : ℝ))
    (fun _ : Fin (q - 1) => (1 : ℝ)) C
    (fun s t => by
      exact_mod_cast carryCoincidenceKernel_symmetric q s t)
    (fun s t => by positivity)
    (fun _ => by positivity)
    (fun s => by simpa using hrow s)
    (fun s : Fin (q - 1) => ‖f s‖)
  calc
    (∑ s, ∑ t,
        (carryCoincidenceKernel q s t : ℂ) *
          (f s * star (f t))).re
        = ∑ s, ∑ t,
            ((carryCoincidenceKernel q s t : ℂ) *
              (f s * star (f t))).re := by simp
    _ ≤ ∑ s, ∑ t,
        (carryCoincidenceKernel q s t : ℝ) *
          (‖f s‖ * ‖f t‖) := hsum
    _ = (fun s : Fin (q - 1) => ‖f s‖) ⬝ᵥ
          (Matrix.mulVec
            (fun s t : Fin (q - 1) =>
              (carryCoincidenceKernel q s t : ℝ))
            (fun s : Fin (q - 1) => ‖f s‖)) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ C * ((fun s : Fin (q - 1) => ‖f s‖) ⬝ᵥ
          (fun s : Fin (q - 1) => ‖f s‖)) := hschur
    _ = C * ∑ s, ‖f s‖ ^ 2 := by
      simp [dotProduct, pow_two]

/-- Complex-energy form of the concrete carry Bessel estimate. -/
theorem continuousMultiplicationCarryBessel_complexEnergy
    (q : ℕ) (hq : 2 ≤ q) (f : Fin (q - 1) → ℂ) :
    ((∫ θ in (0 : ℝ)..1,
      ∑ r, carryTransform q f θ r *
        star (carryTransform q f θ r))).re ≤
      5 * q * Real.log (2 * q) * ∑ s, ‖f s‖ ^ 2 := by
  exact carryEnergy_re_le_of_rowSum q f
    (5 * q * Real.log (2 * q))
    (carryCoincidenceKernel_rowSum_log q hq)

theorem carryEnergy_re_eq_normSqIntegral
    (q : ℕ) (f : Fin (q - 1) → ℂ) :
    ((∫ θ in (0 : ℝ)..1,
      ∑ r, carryTransform q f θ r *
        star (carryTransform q f θ r))).re =
      ∫ θ in (0 : ℝ)..1,
        ∑ r, ‖carryTransform q f θ r‖ ^ 2 := by
  have hpoint : ∀ θ : ℝ,
      (∑ r, carryTransform q f θ r *
        star (carryTransform q f θ r)) =
        ((∑ r, ‖carryTransform q f θ r‖ ^ 2 : ℝ) : ℂ) := by
    intro θ
    push_cast
    apply Finset.sum_congr rfl
    intro r _
    rw [show star (carryTransform q f θ r) =
        (starRingEnd ℂ) (carryTransform q f θ r) from rfl,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [intervalIntegral.integral_congr fun θ _ => hpoint θ,
    intervalIntegral.integral_ofReal]
  simp

/-- Concrete continuous Bessel estimate with an explicit absolute constant.
This is the boxed q log(2q) estimate of the manuscript, stated literally as
an integral of squared norms. -/
theorem continuousMultiplicationCarryBessel
    (q : ℕ) (hq : 2 ≤ q) (f : Fin (q - 1) → ℂ) :
    (∫ θ in (0 : ℝ)..1,
      ∑ r, ‖carryTransform q f θ r‖ ^ 2) ≤
      5 * q * Real.log (2 * q) * ∑ s, ‖f s‖ ^ 2 := by
  rw [← carryEnergy_re_eq_normSqIntegral]
  exact continuousMultiplicationCarryBessel_complexEnergy q hq f

theorem carryDiagonalContribution (q : ℕ)
    (f : Fin (q - 1) → ℂ) :
    (∑ s, (carryCoincidenceKernel q s s : ℝ) * ‖f s‖ ^ 2) =
      (q - 1 : ℕ) * ∑ s, ‖f s‖ ^ 2 := by
  simp_rw [carryCoincidenceKernel_diagonal]
  rw [Finset.mul_sum]

/-- Prime-modulus manuscript wrapper, including the exact diagonal
contribution which shows why a factor of order q is unavoidable. -/
theorem multiplicationCarryBesselTheorem
    (q : ℕ) (hq : Nat.Prime q) :
    (∀ f : Fin (q - 1) → ℂ,
      (∫ θ in (0 : ℝ)..1,
        ∑ r, ‖carryTransform q f θ r‖ ^ 2) ≤
        5 * q * Real.log (2 * q) * ∑ s, ‖f s‖ ^ 2)
    ∧ (∀ f : Fin (q - 1) → ℂ,
      (∑ s, (carryCoincidenceKernel q s s : ℝ) * ‖f s‖ ^ 2) =
        (q - 1 : ℕ) * ∑ s, ‖f s‖ ^ 2) := by
  constructor
  · intro f
    exact continuousMultiplicationCarryBessel q hq.two_le f
  · exact carryDiagonalContribution q

end
end ContinuousMultiplicationCarryBessel
end NCG
