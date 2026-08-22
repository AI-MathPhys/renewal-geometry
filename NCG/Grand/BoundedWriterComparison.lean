/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Bounded-writer comparison and target sandwiches

Finite probability-space versions of the comparator and sandwich identities
used by the target-native Gran--Tensor read layer.
-/

open Finset

namespace NCG
namespace BoundedWriterComparison

/-- Integral of a real writer on a finite weighted event space. -/
def expectation {Omega : Type*} [Fintype Omega]
    (mu f : Omega -> Real) : Real :=
  Finset.univ.sum (fun omega => mu omega * f omega)

/-- Weighted `L1` norm on a finite event space. -/
noncomputable def weightedL1 {Omega : Type*} [Fintype Omega]
    (mu f : Omega -> Real) : Real :=
  Finset.univ.sum (fun omega => mu omega * abs (f omega))

/-- Weighted `L2` norm on a finite event space. -/
noncomputable def weightedL2 {Omega : Type*} [Fintype Omega]
    (mu f : Omega -> Real) : Real :=
  Real.sqrt (Finset.univ.sum (fun omega => mu omega * (f omega) ^ 2))

theorem abs_expectation_le_weightedL1 {Omega : Type*} [Fintype Omega]
    (mu f : Omega -> Real) (hmu : forall omega, 0 <= mu omega) :
    abs (expectation mu f) <= weightedL1 mu f := by
  unfold expectation weightedL1
  calc
    abs (Finset.univ.sum (fun omega => mu omega * f omega))
        <= Finset.univ.sum (fun omega => abs (mu omega * f omega)) :=
          abs_sum_le_sum_abs _ _
    _ = Finset.univ.sum (fun omega => mu omega * abs (f omega)) := by
      apply sum_congr rfl
      intro omega _
      rw [abs_mul, abs_of_nonneg (hmu omega)]

/-- Cauchy--Schwarz against a probability row, proved by expanding the
nonnegative variance. -/
theorem abs_expectation_le_weightedL2 {Omega : Type*} [Fintype Omega]
    (mu f : Omega -> Real) (hmu : forall omega, 0 <= mu omega)
    (hmass : Finset.univ.sum mu = 1) :
    abs (expectation mu f) <= weightedL2 mu f := by
  let q := Finset.univ.sum (fun omega => mu omega * (f omega) ^ 2)
  have hq : 0 <= q :=
    sum_nonneg (fun omega _ => mul_nonneg (hmu omega) (sq_nonneg _))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun omega => Real.sqrt (mu omega))
    (fun omega => Real.sqrt (mu omega) * f omega)
  have hleft : Finset.univ.sum (fun omega =>
      Real.sqrt (mu omega) * (Real.sqrt (mu omega) * f omega)) =
      expectation mu f := by
    unfold expectation
    apply sum_congr rfl
    intro omega _
    rw [← mul_assoc, Real.mul_self_sqrt (hmu omega)]
  have hfirst : Finset.univ.sum (fun omega => (Real.sqrt (mu omega)) ^ 2) = 1 := by
    simpa [Real.sq_sqrt (hmu _)] using hmass
  have hsecond : Finset.univ.sum (fun omega =>
      (Real.sqrt (mu omega) * f omega) ^ 2) = q := by
    apply sum_congr rfl
    intro omega _
    rw [mul_pow, Real.sq_sqrt (hmu omega)]
  rw [hleft, hfirst, hsecond, one_mul] at hcs
  rw [weightedL2]
  change abs (expectation mu f) <= Real.sqrt q
  have hsqrt : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  have hsqrt_nonneg := Real.sqrt_nonneg q
  nlinarith [sq_abs (expectation mu f)]
theorem expectation_sub {Omega : Type*} [Fintype Omega]
    (mu f g : Omega -> Real) :
    expectation mu (fun omega => f omega - g omega) =
      expectation mu f - expectation mu g := by
  simp [expectation, mul_sub, sum_sub_distrib]

theorem affine_writer_expectation {Omega : Type*} [Fintype Omega]
    (mu q : Omega -> Real) (a b : Real) (hmass : Finset.univ.sum mu = 1) :
    expectation mu (fun omega => a + (b - a) * q omega) =
      a + (b - a) * expectation mu q := by
  unfold expectation
  calc
    Finset.univ.sum (fun omega => mu omega * (a + (b - a) * q omega)) =
        Finset.univ.sum (fun omega =>
          a * mu omega + (b - a) * (mu omega * q omega)) := by
      apply sum_congr rfl
      intro omega _
      ring
    _ = a * Finset.univ.sum mu +
        (b - a) * Finset.univ.sum (fun omega => mu omega * q omega) := by
      rw [sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = a + (b - a) * Finset.univ.sum (fun omega => mu omega * q omega) := by
      rw [hmass]
      ring

/-- `cor:GT-threshold-read`: exact comparator decomposition and the displayed
two-error bound.  `thresholdMean` is the conditional threshold probability;
`ideal` is the ideal same-event threshold bit. -/
theorem universal_bounded_writer_comparator
    {Omega U : Type*} [Fintype Omega] [Fintype U]
    (mu : Omega -> Real) (lambda : Omega -> U -> Real)
    (q thresholdMean : Omega -> Real) (kernel ideal : Omega -> U -> Real)
    (a b : Real)
    (hmu : forall omega, 0 <= mu omega)
    (hlambda : forall omega u, 0 <= lambda omega u)
    (hmass : Finset.univ.sum mu = 1)
    (hlambdaMass : Finset.univ.sum (fun p : Omega × U => lambda p.1 p.2) = 1)
    (hideal : expectation mu thresholdMean =
      Finset.univ.sum (fun p : Omega × U => lambda p.1 p.2 * ideal p.1 p.2)) :
    let EB := Finset.univ.sum (fun p : Omega × U => lambda p.1 p.2 * kernel p.1 p.2)
    let Eq := expectation mu q
    let comparatorError := weightedL2
      (fun p : Omega × U => lambda p.1 p.2)
      (fun p => kernel p.1 p.2 - ideal p.1 p.2)
    let thresholdError := weightedL2 mu (fun omega => thresholdMean omega - q omega)
    (EB - Eq =
        Finset.univ.sum (fun p : Omega × U =>
          lambda p.1 p.2 * (kernel p.1 p.2 - ideal p.1 p.2)) +
        expectation mu (fun omega => thresholdMean omega - q omega)) /\
      abs (a + (b - a) * EB -
        expectation mu (fun omega => a + (b - a) * q omega)) <=
        abs (b - a) * (comparatorError + thresholdError) := by
  dsimp only
  have hdecomp :
      Finset.univ.sum (fun p : Omega × U => lambda p.1 p.2 * kernel p.1 p.2) -
          expectation mu q =
        Finset.univ.sum (fun p : Omega × U =>
          lambda p.1 p.2 * (kernel p.1 p.2 - ideal p.1 p.2)) +
        expectation mu (fun omega => thresholdMean omega - q omega) := by
    rw [expectation_sub, hideal]
    simp only [mul_sub, sum_sub_distrib]
    ring
  constructor
  · exact hdecomp
  · rw [affine_writer_expectation mu q a b hmass]
    have hcmp := abs_expectation_le_weightedL2
      (fun p : Omega × U => lambda p.1 p.2)
      (fun p => kernel p.1 p.2 - ideal p.1 p.2)
      (fun p => hlambda p.1 p.2) hlambdaMass
    have hcmp' : abs (Finset.univ.sum (fun p : Omega × U =>
        lambda p.1 p.2 * (kernel p.1 p.2 - ideal p.1 p.2))) <=
        weightedL2 (fun p : Omega × U => lambda p.1 p.2)
          (fun p => kernel p.1 p.2 - ideal p.1 p.2) := by
      simpa [expectation] using hcmp
    have hthr := abs_expectation_le_weightedL2 mu
      (fun omega => thresholdMean omega - q omega) hmu hmass
    calc
      abs (a + (b - a) *
          Finset.univ.sum (fun p : Omega × U => lambda p.1 p.2 * kernel p.1 p.2) -
          (a + (b - a) * expectation mu q)) =
          abs (b - a) * abs
            (Finset.univ.sum (fun p : Omega × U => lambda p.1 p.2 * kernel p.1 p.2) -
              expectation mu q) := by
            rw [show a + (b - a) *
                Finset.univ.sum (fun p : Omega × U =>
                  lambda p.1 p.2 * kernel p.1 p.2) -
                (a + (b - a) * expectation mu q) =
                (b - a) *
                  (Finset.univ.sum (fun p : Omega × U =>
                    lambda p.1 p.2 * kernel p.1 p.2) - expectation mu q) by ring,
              abs_mul]
      _ = abs (b - a) * abs
          (Finset.univ.sum (fun p : Omega × U =>
            lambda p.1 p.2 * (kernel p.1 p.2 - ideal p.1 p.2)) +
            expectation mu (fun omega => thresholdMean omega - q omega)) := by
          rw [hdecomp]
      _ <= abs (b - a) *
          (abs (Finset.univ.sum (fun p : Omega × U =>
              lambda p.1 p.2 * (kernel p.1 p.2 - ideal p.1 p.2))) +
            abs (expectation mu (fun omega => thresholdMean omega - q omega))) := by
          gcongr
          exact abs_add_le _ _
      _ <= abs (b - a) *
          (weightedL2 (fun p : Omega × U => lambda p.1 p.2)
              (fun p => kernel p.1 p.2 - ideal p.1 p.2) +
            weightedL2 mu (fun omega => thresholdMean omega - q omega)) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hcmp' hthr) (abs_nonneg _)

/-- The exact branch of the comparator theorem. -/
theorem exact_threshold_read
    {Omega : Type*} [Fintype Omega] (mu q : Omega -> Real)
    (a b EB : Real) (hmass : Finset.univ.sum mu = 1)
    (hexact : EB = expectation mu q) :
    expectation mu (fun omega => a + (b - a) * q omega) =
      a + (b - a) * EB := by
  rw [affine_writer_expectation mu q a b hmass, hexact]

/-- First, directly physical part of `thm:GT-target-sandwich`: two same-history
reads of lower and upper writers bound the selected target expectation with
their exact weighted `L1` calibration errors. -/
theorem target_sandwich
    {Omega : Type*} [Fintype Omega]
    (mu lower writer upper readLower readUpper : Omega -> Real)
    (hmu : forall omega, 0 <= mu omega)
    (hlower : forall omega, lower omega <= writer omega)
    (hupper : forall omega, writer omega <= upper omega) :
    expectation mu readLower - weightedL1 mu (fun omega => readLower omega - lower omega)
        <= expectation mu writer /\
      expectation mu writer <= expectation mu readUpper +
        weightedL1 mu (fun omega => readUpper omega - upper omega) := by
  have horderLower : expectation mu lower <= expectation mu writer := by
    unfold expectation
    exact sum_le_sum fun omega _ => mul_le_mul_of_nonneg_left (hlower omega) (hmu omega)
  have horderUpper : expectation mu writer <= expectation mu upper := by
    unfold expectation
    exact sum_le_sum fun omega _ => mul_le_mul_of_nonneg_left (hupper omega) (hmu omega)
  have hreadLower := abs_expectation_le_weightedL1 mu
    (fun omega => readLower omega - lower omega) hmu
  have hreadUpper := abs_expectation_le_weightedL1 mu
    (fun omega => readUpper omega - upper omega) hmu
  rw [expectation_sub] at hreadLower hreadUpper
  constructor
  · have := le_of_abs_le hreadLower
    linarith
  · have := neg_le_of_abs_le hreadUpper
    linarith

/-- If two branch writers are pullbacks of one common-history writer, their
weighted expectations agree with the common expectation. -/
theorem one_history_projection
    {History Branch : Type*} [Fintype History] [Fintype Branch]
    (weight : History -> Real) (projection : History -> Branch)
    (branchWriter : Branch -> Real) (commonWriter : History -> Real)
    (hcommon : forall history, branchWriter (projection history) = commonWriter history) :
    expectation weight (fun history => branchWriter (projection history)) =
      expectation weight commonWriter := by
  apply sum_congr rfl
  intro history _
  simp [hcommon]

end BoundedWriterComparison
end NCG
