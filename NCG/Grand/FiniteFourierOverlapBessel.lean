/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.ContinuousMultiplicationCarryBessel

/-!
# Finite Fourier overlap Bessel inequality

Parseval on finite trigonometric polynomials is combined with a sharp
frequency-overlap count.  This is the reusable analytic assembly needed for
the pair-quotient carry theorem.
-/

open Finset intervalIntegral

namespace NCG
namespace FiniteFourierOverlapBessel

open ContinuousMultiplicationCarryBessel

noncomputable section

def finiteFourierPolynomial {N : ℕ} (c : Fin N → ℂ) (θ : ℝ) : ℂ :=
  ∑ n, c n * integerCircleCharacter (-(n : ℤ)) θ

theorem finiteFourierPolynomial_complexParseval {N : ℕ}
    (c : Fin N → ℂ) :
    (∫ θ in (0 : ℝ)..1,
      finiteFourierPolynomial c θ *
        star (finiteFourierPolynomial c θ)) =
      ∑ n, c n * star (c n) := by
  unfold finiteFourierPolynomial
  change (∫ θ in (0 : ℝ)..1,
      (∑ n, c n * integerCircleCharacter (-(n : ℤ)) θ) *
        (starRingEnd ℂ)
          (∑ n, c n * integerCircleCharacter (-(n : ℤ)) θ)) = _
  rw [intervalIntegral.integral_congr fun θ _ => by
    rw [map_sum, Finset.sum_mul_sum]]
  rw [intervalIntegral.integral_finsetSum fun m _ =>
    (Continuous.intervalIntegrable (by
      unfold integerCircleCharacter
      fun_prop) _ _)]
  apply Finset.sum_congr rfl
  intro m _
  rw [intervalIntegral.integral_finsetSum fun n _ =>
    (Continuous.intervalIntegrable (by
      unfold integerCircleCharacter
      fun_prop) _ _)]
  have hpair : ∀ n : Fin N,
      (∫ θ in (0 : ℝ)..1,
        (c m * integerCircleCharacter (-(m : ℤ)) θ) *
          (starRingEnd ℂ)
            (c n * integerCircleCharacter (-(n : ℤ)) θ)) =
        if m = n then c m * star (c n) else 0 := by
    intro n
    have hpoint : ∀ θ : ℝ,
        (c m * integerCircleCharacter (-(m : ℤ)) θ) *
            (starRingEnd ℂ)
              (c n * integerCircleCharacter (-(n : ℤ)) θ) =
          (c m * star (c n)) *
            (integerCircleCharacter (-(m : ℤ)) θ *
              star (integerCircleCharacter (-(n : ℤ)) θ)) := by
      intro θ
      rw [show star (c n) = (starRingEnd ℂ) (c n) from rfl,
        show star (integerCircleCharacter (-(n : ℤ)) θ) =
          (starRingEnd ℂ)
            (integerCircleCharacter (-(n : ℤ)) θ) from rfl,
        map_mul]
      ring
    rw [intervalIntegral.integral_congr fun θ _ => hpoint θ,
      intervalIntegral.integral_const_mul,
      integerCircleCharacter_orthogonality]
    by_cases hmn : m = n
    · subst n
      simp
    · have hval : -(m : ℤ) ≠ -(n : ℤ) := by
        exact fun h => hmn (Fin.ext (by
          exact_mod_cast neg_inj.mp h))
      rw [if_neg hval, mul_zero, if_neg hmn]
  rw [Finset.sum_eq_single m]
  · rw [hpair m, if_pos rfl]
  · intro n _ hnm
    rw [hpair n, if_neg (Ne.symm hnm)]
  · simp

theorem finiteFourierPolynomial_parseval {N : ℕ}
    (c : Fin N → ℂ) :
    (∫ θ in (0 : ℝ)..1,
      ‖finiteFourierPolynomial c θ‖ ^ 2) =
      ∑ n, ‖c n‖ ^ 2 := by
  have hcomplex := finiteFourierPolynomial_complexParseval c
  have hleft : ∀ θ : ℝ,
      finiteFourierPolynomial c θ *
          star (finiteFourierPolynomial c θ) =
        ((‖finiteFourierPolynomial c θ‖ ^ 2 : ℝ) : ℂ) := by
    intro θ
    rw [show star (finiteFourierPolynomial c θ) =
        (starRingEnd ℂ) (finiteFourierPolynomial c θ) from rfl,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hright :
      (∑ n, c n * star (c n)) =
        ((∑ n, ‖c n‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro n _
    rw [show star (c n) = (starRingEnd ℂ) (c n) from rfl,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [intervalIntegral.integral_congr fun θ _ => hleft θ,
    intervalIntegral.integral_ofReal, hright] at hcomplex
  exact_mod_cast hcomplex

theorem coefficientOverlapBessel
    {J Ω : Type*} [Fintype J] [Fintype Ω]
    (c : J → Ω → ℂ) (M : ℕ)
    (hoverlap : ∀ ω,
      ((Finset.univ : Finset J).filter
        (fun j => c j ω ≠ 0)).card ≤ M) :
    (∑ ω, ‖∑ j, c j ω‖ ^ 2) ≤
      M * ∑ j, ∑ ω, ‖c j ω‖ ^ 2 := by
  have hfrequency : ∀ ω : Ω,
      ‖∑ j, c j ω‖ ^ 2 ≤
        M * ∑ j, ‖c j ω‖ ^ 2 := by
    intro ω
    let S := (Finset.univ : Finset J).filter
      (fun j => c j ω ≠ 0)
    have hsum : (∑ j, c j ω) = ∑ j ∈ S, c j ω := by
      symm
      exact Finset.sum_subset (Finset.filter_subset _ _) (by
        intro j _ hj
        simp only [S, Finset.mem_filter, Finset.mem_univ,
          true_and, not_ne_iff] at hj
        exact hj)
    rw [hsum]
    have htriangle : ‖∑ j ∈ S, c j ω‖ ≤
        ∑ j ∈ S, ‖c j ω‖ :=
      norm_sum_le _ _
    have hnonneg : 0 ≤ ∑ j ∈ S, ‖c j ω‖ := by positivity
    have hsquare :
        ‖∑ j ∈ S, c j ω‖ ^ 2 ≤
          (∑ j ∈ S, ‖c j ω‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hnonneg).2 htriangle
    have hcs :
        (∑ j ∈ S, ‖c j ω‖) ^ 2 ≤
          S.card * ∑ j ∈ S, ‖c j ω‖ ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq S
        (fun _ => (1 : ℝ)) (fun j => ‖c j ω‖)
    have hcard : (S.card : ℝ) ≤ M := by
      exact_mod_cast hoverlap ω
    calc
      ‖∑ j ∈ S, c j ω‖ ^ 2
          ≤ (∑ j ∈ S, ‖c j ω‖) ^ 2 := hsquare
      _ ≤ S.card * ∑ j ∈ S, ‖c j ω‖ ^ 2 := hcs
      _ ≤ M * ∑ j ∈ S, ‖c j ω‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ M * ∑ j, ‖c j ω‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) (by
              intro j hj hnot
              positivity))
          (by positivity)
  calc
    (∑ ω, ‖∑ j, c j ω‖ ^ 2)
        ≤ ∑ ω, M * ∑ j, ‖c j ω‖ ^ 2 :=
      Finset.sum_le_sum fun ω _ => hfrequency ω
    _ = M * ∑ j, ∑ ω, ‖c j ω‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]

theorem finiteFourierFamily_overlapBessel
    {J : Type*} [Fintype J] {N M : ℕ}
    (c : J → Fin N → ℂ)
    (hoverlap : ∀ n,
      ((Finset.univ : Finset J).filter
        (fun j => c j n ≠ 0)).card ≤ M) :
    (∫ θ in (0 : ℝ)..1,
      ‖∑ j, finiteFourierPolynomial (c j) θ‖ ^ 2) ≤
      M * ∑ j, ∫ θ in (0 : ℝ)..1,
        ‖finiteFourierPolynomial (c j) θ‖ ^ 2 := by
  have hpoly : ∀ θ : ℝ,
      (∑ j, finiteFourierPolynomial (c j) θ) =
        finiteFourierPolynomial (fun n => ∑ j, c j n) θ := by
    intro θ
    unfold finiteFourierPolynomial
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.sum_mul]
  rw [intervalIntegral.integral_congr fun θ _ => by rw [hpoly θ]]
  rw [finiteFourierPolynomial_parseval]
  have hcoeff := coefficientOverlapBessel c M hoverlap
  calc
    (∑ n, ‖∑ j, c j n‖ ^ 2)
        ≤ M * ∑ j, ∑ n, ‖c j n‖ ^ 2 := hcoeff
    _ = M * ∑ j, ∫ θ in (0 : ℝ)..1,
          ‖finiteFourierPolynomial (c j) θ‖ ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [finiteFourierPolynomial_parseval]

/-- Finite family of circle characters with row and column frequency data. -/
def finiteFrequencyTransform
    {R S : Type*} [Fintype S]
    (frequency : R → S → ℤ) (f : S → ℂ)
    (θ : ℝ) (r : R) : ℂ :=
  ∑ s, integerCircleCharacter (frequency r s) θ * f s

@[fun_prop]
theorem continuous_finiteFrequencyTransform
    {R S : Type*} [Fintype S]
    (frequency : R → S → ℤ) (f : S → ℂ) (r : R) :
    Continuous fun θ : ℝ =>
      finiteFrequencyTransform frequency f θ r := by
  unfold finiteFrequencyTransform integerCircleCharacter
  fun_prop

def finiteFrequencyCoincidenceKernel
    {R S : Type*} [Fintype R]
    (frequency : R → S → ℤ) (s t : S) : ℕ :=
  ((Finset.univ : Finset R).filter
    (fun r => frequency r s = frequency r t)).card

theorem finiteFrequencyCoincidenceKernel_symmetric
    {R S : Type*} [Fintype R]
    (frequency : R → S → ℤ) (s t : S) :
    finiteFrequencyCoincidenceKernel frequency s t =
      finiteFrequencyCoincidenceKernel frequency t s := by
  unfold finiteFrequencyCoincidenceKernel
  congr 1
  ext r
  simp [eq_comm]

theorem finiteFrequencyEnergy_eq_kernelQuadratic
    {R S : Type*} [Fintype R] [Fintype S]
    (frequency : R → S → ℤ) (f : S → ℂ) :
    (∫ θ in (0 : ℝ)..1,
      ∑ r, finiteFrequencyTransform frequency f θ r *
        star (finiteFrequencyTransform frequency f θ r)) =
      ∑ s, ∑ t,
        (finiteFrequencyCoincidenceKernel frequency s t : ℂ) *
          (f s * star (f t)) := by
  have hselector :
      (∫ θ in (0 : ℝ)..1,
        ∑ r, finiteFrequencyTransform frequency f θ r *
          star (finiteFrequencyTransform frequency f θ r)) =
        ∑ r, ∑ s, ∑ t,
          if frequency r s = frequency r t
          then f s * star (f t) else 0 := by
    rw [intervalIntegral.integral_finsetSum fun r _ =>
      (Continuous.intervalIntegrable (by
        unfold finiteFrequencyTransform integerCircleCharacter
        fun_prop) _ _)]
    apply Finset.sum_congr rfl
    intro r _
    unfold finiteFrequencyTransform
    change (∫ θ in (0 : ℝ)..1,
        (∑ s, integerCircleCharacter (frequency r s) θ * f s) *
          (starRingEnd ℂ)
            (∑ s, integerCircleCharacter (frequency r s) θ * f s)) = _
    rw [intervalIntegral.integral_congr fun θ _ => by
      rw [map_sum, Finset.sum_mul_sum]]
    rw [intervalIntegral.integral_finsetSum fun s _ =>
      (Continuous.intervalIntegrable (by
        unfold integerCircleCharacter
        fun_prop) _ _)]
    apply Finset.sum_congr rfl
    intro s _
    rw [intervalIntegral.integral_finsetSum fun t _ =>
      (Continuous.intervalIntegrable (by
        unfold integerCircleCharacter
        fun_prop) _ _)]
    apply Finset.sum_congr rfl
    intro t _
    have hpoint : ∀ θ : ℝ,
        (integerCircleCharacter (frequency r s) θ * f s) *
            (starRingEnd ℂ)
              (integerCircleCharacter (frequency r t) θ * f t) =
          (f s * star (f t)) *
            (integerCircleCharacter (frequency r s) θ *
              star (integerCircleCharacter (frequency r t) θ)) := by
      intro θ
      rw [show star (f t) = (starRingEnd ℂ) (f t) from rfl,
        show star (integerCircleCharacter (frequency r t) θ) =
          (starRingEnd ℂ)
            (integerCircleCharacter (frequency r t) θ) from rfl,
        map_mul]
      ring
    rw [intervalIntegral.integral_congr fun θ _ => hpoint θ,
      intervalIntegral.integral_const_mul,
      integerCircleCharacter_orthogonality]
    by_cases hfreq : frequency r s = frequency r t
    · simp [hfreq]
    · simp [hfreq]
  rw [hselector]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  unfold finiteFrequencyCoincidenceKernel
  rw [← Finset.sum_filter]
  simp

theorem finiteFrequencyEnergy_re_le_of_rowSum
    {R S : Type*} [Fintype R] [Fintype S]
    (frequency : R → S → ℤ) (f : S → ℂ) (C : ℝ)
    (hrow : ∀ s,
      ∑ t, (finiteFrequencyCoincidenceKernel frequency s t : ℝ) ≤ C) :
    ((∫ θ in (0 : ℝ)..1,
      ∑ r, finiteFrequencyTransform frequency f θ r *
        star (finiteFrequencyTransform frequency f θ r))).re ≤
      C * ∑ s, ‖f s‖ ^ 2 := by
  rw [finiteFrequencyEnergy_eq_kernelQuadratic]
  have hterm : ∀ s t : S,
      (((finiteFrequencyCoincidenceKernel frequency s t : ℂ) *
          (f s * star (f t))).re) ≤
        (finiteFrequencyCoincidenceKernel frequency s t : ℝ) *
          (‖f s‖ * ‖f t‖) := by
    intro s t
    have hre : (f s * star (f t)).re ≤
        ‖f s * star (f t)‖ := Complex.re_le_norm _
    simpa [Complex.mul_re, norm_mul] using
      (mul_le_mul_of_nonneg_left hre (by positivity :
        0 ≤ (finiteFrequencyCoincidenceKernel frequency s t : ℝ)))
  have hschur := NCG.schur_test
    (fun s t : S =>
      (finiteFrequencyCoincidenceKernel frequency s t : ℝ))
    (fun _ : S => (1 : ℝ)) C
    (fun s t => by
      exact_mod_cast
        finiteFrequencyCoincidenceKernel_symmetric frequency s t)
    (fun s t => by positivity)
    (fun _ => by positivity)
    (fun s => by simpa using hrow s)
    (fun s : S => ‖f s‖)
  calc
    (∑ s, ∑ t,
        (finiteFrequencyCoincidenceKernel frequency s t : ℂ) *
          (f s * star (f t))).re
        = ∑ s, ∑ t,
            ((finiteFrequencyCoincidenceKernel frequency s t : ℂ) *
              (f s * star (f t))).re := by simp
    _ ≤ ∑ s, ∑ t,
        (finiteFrequencyCoincidenceKernel frequency s t : ℝ) *
          (‖f s‖ * ‖f t‖) :=
      Finset.sum_le_sum fun s _ =>
        Finset.sum_le_sum fun t _ => hterm s t
    _ = (fun s : S => ‖f s‖) ⬝ᵥ
          (Matrix.mulVec
            (fun s t : S =>
              (finiteFrequencyCoincidenceKernel frequency s t : ℝ))
            (fun s : S => ‖f s‖)) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ C * ((fun s : S => ‖f s‖) ⬝ᵥ
          (fun s : S => ‖f s‖)) := hschur
    _ = C * ∑ s, ‖f s‖ ^ 2 := by
      simp [dotProduct, pow_two]

theorem finiteFrequencyEnergy_re_eq_normSqIntegral
    {R S : Type*} [Fintype R] [Fintype S]
    (frequency : R → S → ℤ) (f : S → ℂ) :
    ((∫ θ in (0 : ℝ)..1,
      ∑ r, finiteFrequencyTransform frequency f θ r *
        star (finiteFrequencyTransform frequency f θ r))).re =
      ∫ θ in (0 : ℝ)..1,
        ∑ r, ‖finiteFrequencyTransform frequency f θ r‖ ^ 2 := by
  have hpoint : ∀ θ : ℝ,
      (∑ r, finiteFrequencyTransform frequency f θ r *
        star (finiteFrequencyTransform frequency f θ r)) =
        ((∑ r, ‖finiteFrequencyTransform frequency f θ r‖ ^ 2 : ℝ) : ℂ) := by
    intro θ
    push_cast
    apply Finset.sum_congr rfl
    intro r _
    rw [show star (finiteFrequencyTransform frequency f θ r) =
        (starRingEnd ℂ)
          (finiteFrequencyTransform frequency f θ r) from rfl,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [intervalIntegral.integral_congr fun θ _ => hpoint θ,
    intervalIntegral.integral_ofReal]
  simp

end
end FiniteFourierOverlapBessel
end NCG
