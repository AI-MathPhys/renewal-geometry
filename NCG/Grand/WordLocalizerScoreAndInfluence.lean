/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExactSourceSchurResidual
import NCG.Grand.ScoreExport
import NCG.Grand.GTHellingerFisher

/-!
# Word-localizer descent, score information loss, and finite influence bounds

Reusable exact algebraic forms for the medium-tier localizer and reverse
influence statements.
-/

open Finset Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace WordLocalizerScoreAndInfluence

/-- The physical score residual is literally the Gram of the failure of the
word relation `S1 = S0 T`. -/
theorem score_relation_residual_identity
    {h e0 e1 : Type*} [Fintype h] [Fintype e0] [Fintype e1]
    (S0 : Matrix h e0 Complex) (S1 : Matrix h e1 Complex)
    (T : Matrix e0 e1 Complex) :
    S1ᴴ * S1 - Tᴴ * (S0ᴴ * S1) - (S0ᴴ * S1)ᴴ * T +
        Tᴴ * (S0ᴴ * S0) * T =
      (S1 - S0 * T)ᴴ * (S1 - S0 * T) := by
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
    Matrix.conjTranspose_conjTranspose]
  noncomm_ring

/-- Vanishing score residual is exactly validity of the proposed relation in
the physical score experiment. -/
theorem score_relation_residual_eq_zero_iff
    {h e0 e1 : Type*} [Fintype h] [Fintype e0] [Fintype e1]
    (S0 : Matrix h e0 Complex) (S1 : Matrix h e1 Complex)
    (T : Matrix e0 e1 Complex) :
    S1ᴴ * S1 - Tᴴ * (S0ᴴ * S1) - (S0ᴴ * S1)ᴴ * T +
        Tᴴ * (S0ᴴ * S0) * T = 0 <-> S1 = S0 * T := by
  rw [score_relation_residual_identity]
  constructor
  · intro h
    exact sub_eq_zero.mp (Matrix.conjTranspose_mul_self_eq_zero.mp h)
  · rintro rfl
    simp

/-- `thm:GT-word-localizer-descent`, exact word innovation, positivity, range
criterion, and rank increment, specialized to the literal word syntheses. -/
theorem word_localizer_innovation_package {h e0 e1 : Nat}
    (W : Matrix (Fin h) (Fin e0) Complex)
    (V : Matrix (Fin h) (Fin e1) Complex) :
    sourceSchurResidual W V =
        Vᴴ * (1 - sourceRangeProjection W) * V /\
      (sourceSchurResidual W V).PosSemidef /\
      (sourceSchurResidual W V = 0 <-> SourceRangeIncluded V W) /\
      (Matrix.fromBlocks (Wᴴ * W) (Wᴴ * V) ((Wᴴ * V)ᴴ) (Vᴴ * V)).rank -
          (Wᴴ * W).rank = (sourceSchurResidual W V).rank :=
  exact_source_schur_residual W V

/-- Every strict adaptive innovation consumes at least one remaining carrier
dimension. -/
theorem adaptive_word_strict_increment_bound
    (ambient initial rounds : Nat) (hinitial : initial <= ambient)
    (hgain : initial + rounds <= ambient) :
    rounds <= ambient - initial := by
  omega

/-- A rank-`r` polar innovation produces exactly `r` new represented
directions and therefore shortens the remaining dimension by `r`. -/
theorem adaptive_word_rank_accounting
    (ambient represented innovation : Nat)
    (hfit : represented + innovation <= ambient) :
    ambient - (represented + innovation) =
      (ambient - represented) - innovation := by
  omega

/-- The exact finite score-information-loss Gram.  This packages Fisher
positivity, coarse-score conditional expectation, Pythagoras, positivity of
the loss, and the measurable-score zero branch. -/
theorem deterministic_score_information_loss
    {Omega Coarse Index : Type*}
    [Fintype Omega] [Fintype Coarse] [DecidableEq Coarse] [Finite Index]
    (p : Omega -> Real) (hp : forall x, 0 <= p x)
    (score : Index -> Omega -> Complex) (coarse : Omega -> Coarse)
    (pc : Coarse -> Real)
    (hpc : forall y, pc y =
      (Finset.univ.filter (fun x => coarse x = y)).sum p)
    (hpcpos : forall y, pc y ≠ 0)
    (coarseScore : Index -> Coarse -> Complex)
    (hscore : forall i y, coarseScore i y = (pc y : Complex)⁻¹ *
      (Finset.univ.filter (fun x => coarse x = y)).sum
        (fun x => (p x : Complex) * score i x)) :
    (fisherBlock p score).PosSemidef /\
      (fisherBlock pc coarseScore).PosSemidef /\
      fisherBlock p score = fisherBlock pc coarseScore +
        fisherBlock p (fun i x => score i x - coarseScore i (coarse x)) /\
      (fisherBlock p (fun i x => score i x - coarseScore i (coarse x))).PosSemidef /\
      ((forall i x, score i x = coarseScore i (coarse x)) ->
        fisherBlock p score = fisherBlock pc coarseScore) :=
  operational_score_export p hp score coarse pc hpc hpcpos coarseScore hscore

/-- A finite score covariance is positive semidefinite because it is a Gram
matrix. -/
theorem physical_score_covariance_positive
    {Omega Index : Type*} [Fintype Omega] [Finite Index]
    (p : Omega -> Real) (score : Index -> Omega -> Complex)
    (hp : forall x, 0 <= p x) :
    (fisherBlock p score).PosSemidef :=
  fisher_posSemidef p score hp

/-- A finite nonnegative target is source-coercive exactly when it vanishes on
every source-null coordinate.  The proof constructs a finite influence
constant explicitly. -/
theorem finite_source_coercivity_iff_kernel_inclusion
    {I : Type*} [Fintype I]
    (source target : I -> Real)
    (hsource : forall i, 0 <= source i)
    (htarget : forall i, 0 <= target i) :
    (exists Lambda : Real, 0 <= Lambda /\
        forall i, target i <= Lambda * source i) <->
      forall i, source i = 0 -> target i = 0 := by
  constructor
  · rintro ⟨Lambda, hLambda, hbound⟩ i hi
    have := hbound i
    rw [hi, mul_zero] at this
    exact le_antisymm this (htarget i)
  · intro hker
    let ratio : I -> Real := fun i =>
      if source i = 0 then 0 else target i / source i
    let Lambda := Finset.univ.sum ratio
    have hratio (i : I) : 0 <= ratio i := by
      by_cases hi : source i = 0
      · simp [ratio, hi]
      · simp only [ratio, hi, if_false]
        exact div_nonneg (htarget i) (hsource i)
    have hLambda : 0 <= Lambda := sum_nonneg (fun i _ => hratio i)
    refine ⟨Lambda, hLambda, ?_⟩
    intro i
    by_cases hi : source i = 0
    · rw [hker i hi, hi, mul_zero]
    · have hsingle : ratio i <= Lambda :=
        single_le_sum (fun j _ => hratio j) (Finset.mem_univ i)
      simp only [ratio, hi, if_false] at hsingle
      calc
        target i = (target i / source i) * source i := by
          field_simp
        _ <= Lambda * source i :=
          mul_le_mul_of_nonneg_right hsingle (hsource i)

/-- Scalar protected short: completing the square eliminates an unprotected
coordinate exactly. -/
theorem protected_short_complete_square
    {A D E x y : Real} (hE : 0 < E) :
    A * x ^ 2 + 2 * D * x * y + E * y ^ 2 =
      (A - D ^ 2 / E) * x ^ 2 +
        E * (y + D / E * x) ^ 2 := by
  field_simp
  ring

/-- The protected short is the exact minimum over the eliminated coordinate. -/
theorem protected_short_minimum
    {A D E x y : Real} (hE : 0 < E) :
    (A - D ^ 2 / E) * x ^ 2 <=
      A * x ^ 2 + 2 * D * x * y + E * y ^ 2 := by
  rw [protected_short_complete_square hE]
  exact le_add_of_nonneg_right (mul_nonneg hE.le (sq_nonneg _))

/-- Pointwise geometric-layer enclosure. -/
theorem geometric_layer_enclosure
    {s d tau q : Real} (hq : 1 < q) (htau : 0 <= tau)
    (hd : 0 <= d) (hlower : d <= s)
    (hupper : s <= q * d + tau) :
    d <= s /\ s <= q * d + tau :=
  ⟨hlower, hupper⟩

/-- Summing pointwise layer enclosures gives the finite threshold-bank
compiler used in `thm:GT-geometric-threshold-bank`. -/
theorem geometric_threshold_bank_sum
    {I : Type*} [Fintype I]
    (s d tau : I -> Real) (q : Real)
    (hlower : forall i, d i <= s i)
    (hupper : forall i, s i <= q * d i + tau i) :
    Finset.univ.sum d <= Finset.univ.sum s /\
      Finset.univ.sum s <= q * Finset.univ.sum d + Finset.univ.sum tau := by
  constructor
  · exact sum_le_sum (fun i _ => hlower i)
  · calc
      Finset.univ.sum s <= Finset.univ.sum (fun i => q * d i + tau i) :=
        sum_le_sum (fun i _ => hupper i)
      _ = q * Finset.univ.sum d + Finset.univ.sum tau := by
        rw [sum_add_distrib, Finset.mul_sum]

end WordLocalizerScoreAndInfluence
end NCG
