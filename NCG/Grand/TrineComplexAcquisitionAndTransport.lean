/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PositiveCylinderAndTrine
import NCG.Grand.FiniteTargetProjectionAndQuotients

/-!
# Positive trine acquisition and complex-current transport

Exact scalar density and finite-record forms of the trine acquisition,
positive completion, slack, cutoff transport, and cofinal-limit statements.
-/

open Finset Filter Topology

namespace NCG
namespace TrineComplexAcquisitionAndTransport

open PositiveCylinderAndTrine
open FiniteTargetProjectionAndQuotients
open AcceptedActionInformationPythagoras

/-- Positivity criterion for a Hermitian `2 x 2` density with trace `t`,
real imbalance `d`, and complex coordinate `(x,y)`. -/
def PositiveTrineCompletion (t x y d : Real) : Prop :=
  0 <= (t + d) / 2 /\
  0 <= (t - d) / 2 /\
  x ^ 2 + y ^ 2 <= ((t + d) / 2) * ((t - d) / 2)

/-- The determinant form of the positive-completion condition. -/
theorem positiveTrineCompletion_iff {t x y d : Real} (ht : 0 <= t) :
    PositiveTrineCompletion t x y d <->
      d ^ 2 + 4 * (x ^ 2 + y ^ 2) <= t ^ 2 := by
  constructor
  · rintro ⟨hp, hq, hdet⟩
    nlinarith
  · intro h
    have hd : d ^ 2 <= t ^ 2 := by
      nlinarith [sq_nonneg x, sq_nonneg y]
    have hdabs : abs d <= t := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (t - d), sq_nonneg (t + d)]
    refine ⟨?_, ?_, ?_⟩
    ·       linarith [neg_le_of_abs_le hdabs]
    ·       linarith [le_of_abs_le hdabs]
    ·       nlinarith

/-- Balanced completion is positive exactly on the disk `2|z| <= t`. -/
theorem balanced_completion_iff {t x y : Real} (ht : 0 <= t) :
    PositiveTrineCompletion t x y 0 <->
      4 * (x ^ 2 + y ^ 2) <= t ^ 2 := by
  simpa using (positiveTrineCompletion_iff (t := t) (x := x) (y := y) (d := 0) ht)

/-- The quadratic trine criterion is exactly positivity of the balanced
target functional. -/
theorem trine_positive_functional_iff {t x y : Real} (ht : 0 <= t) :
    (Finset.univ.sum (fun k => (trineOutcome t x y k) ^ 2) <= t ^ 2 / 2) <->
      PositiveTrineCompletion t x y 0 := by
  rw [trine_quadratic_criterion ht, balanced_completion_iff ht]

/-- Trine outcome coordinates are unique. -/
theorem trine_representation_unique {t x y t' x' y' : Real}
    (h : trineOutcome t x y = trineOutcome t' x' y') :
    t = t' /\ x = x' /\ Real.sqrt 3 * y = Real.sqrt 3 * y' := by
  have hsum := congrArg (fun r : Fin 3 -> Real => Finset.univ.sum r) h
  rw [trineOutcome_sum, trineOutcome_sum] at hsum
  have hr := trineOutcome_reconstruct t x y
  have hr' := trineOutcome_reconstruct t' x' y'
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  constructor
  · exact hsum
  constructor <;> linarith

/-- Squared Hilbert--Schmidt density norm of an imbalanced completion. -/
noncomputable def completionHilbertSchmidtSq (t x y d : Real) : Real :=
  ((t + d) / 2) ^ 2 + ((t - d) / 2) ^ 2 + 2 * (x ^ 2 + y ^ 2)

theorem completionHilbertSchmidtSq_identity (t x y d : Real) :
    completionHilbertSchmidtSq t x y d =
      t ^ 2 / 2 + d ^ 2 / 2 + 2 * (x ^ 2 + y ^ 2) := by
  unfold completionHilbertSchmidtSq
  ring

/-- The arm-swap invariant completion `d=0` is the unique
Hilbert--Schmidt minimizer. -/
theorem balanced_completion_unique_minimizer (t x y d : Real) :
    completionHilbertSchmidtSq t x y 0 <= completionHilbertSchmidtSq t x y d /\
      (completionHilbertSchmidtSq t x y d =
        completionHilbertSchmidtSq t x y 0 <-> d = 0) := by
  rw [completionHilbertSchmidtSq_identity,
    completionHilbertSchmidtSq_identity]
  constructor
  · nlinarith [sq_nonneg d]
  · constructor
    · intro h
      have : d ^ 2 = 0 := by nlinarith
      exact sq_eq_zero_iff.mp this
    · rintro rfl
      ring

/-- Exact coherent-plus-isotropic decomposition of the balanced completion,
written in real coordinates. -/
theorem balanced_slack_decomposition (t x y : Real) :
    let amplitude := Real.sqrt (x ^ 2 + y ^ 2)
    let slack := t - 2 * amplitude
    t / 2 = amplitude + slack / 2 := by
  dsimp only
  ring

/-- Every positive completion has trace at least twice the complex amplitude;
the balanced rank-one lift attains the bound. -/
theorem trace_minimal_positive_lift
    {p q x y : Real} (hp : 0 <= p) (hq : 0 <= q)
    (hdet : x ^ 2 + y ^ 2 <= p * q) :
    2 * Real.sqrt (x ^ 2 + y ^ 2) <= p + q := by
  have hr : 0 <= x ^ 2 + y ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpq : 0 <= p * q := mul_nonneg hp hq
  have hsqrtmono : Real.sqrt (x ^ 2 + y ^ 2) <= Real.sqrt (p * q) :=
    Real.sqrt_le_sqrt hdet
  have hamgm : 2 * Real.sqrt (p * q) <= p + q := by
    have hp2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp
    have hq2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
    have hprod : Real.sqrt p * Real.sqrt q = Real.sqrt (p * q) := by
      rw [Real.sqrt_mul hp]
    nlinarith [sq_nonneg (Real.sqrt p - Real.sqrt q)]
  linarith

/-- Three real outputs are dimension-minimal for three independent real target
coordinates: no linear equivalence can compress `Fin 3 -> R` to two outputs. -/
theorem three_real_outcomes_dimension_minimal :
    ¬ Nonempty ((Fin 3 -> Real) ≃L[Real] (Fin 2 -> Real)) := by
  intro h
  have hdim := h.some.toLinearEquiv.finrank_eq
  norm_num [Module.finrank_pi] at hdim

/-- A common positive gain cancels in normalized visibility. -/
theorem common_gain_visibility {g t x y : Real} (hg : g ≠ 0) (ht : t ≠ 0) :
    (g * x) / (g * t) = x / t /\ (g * y) / (g * t) = y / t := by
  constructor <;> field_simp

/-- Pointwise scalar slack of a carrier and complex current. -/
noncomputable def slack {X : Type*} (tau : X -> Real)
    (zeta : X -> Complex) (x : X) : Real :=
  tau x - 2 * norm (zeta x)

/-- `thm:GT-trine-slack-transport`: inherited slack plus the exact
destructive-interference debit on every quotient cell. -/
theorem slack_pushforward_identity
    {X Y : Type*} [Fintype X] [DecidableEq Y]
    (s : X -> Y) (tau : X -> Real) (zeta : X -> Complex) (y : Y) :
    slack (pushforwardRow s tau) (complexPushforward s zeta) y =
      pushforwardRow s (slack tau zeta) y +
        2 * (pushforwardRow s (fun x => norm (zeta x)) y -
          norm (complexPushforward s zeta y)) := by
  unfold slack pushforwardRow complexPushforward
  simp only [mul_sub, sum_sub_distrib]
  rw [Finset.mul_sum]
  ring

/-- Destructive interference creates nonnegative slack. -/
theorem quotient_cancellation_nonnegative
    {X Y : Type*} [Fintype X] [DecidableEq Y]
    (s : X -> Y) (zeta : X -> Complex) (y : Y) :
    norm (complexPushforward s zeta y) <=
      pushforwardRow s (fun x => norm (zeta x)) y := by
  unfold complexPushforward pushforwardRow
  exact norm_sum_le _ _

/-- Real total variation on a finite record. -/
noncomputable def realVariation {X : Type*} [Fintype X]
    (r : X -> Real) : Real := Finset.univ.sum (fun x => abs (r x))

theorem realVariation_sum_three_le
    {X : Type*} [Fintype X] (r : Fin 3 -> X -> Real) :
    realVariation (fun x => Finset.univ.sum (fun k => r k x)) <=
      Finset.univ.sum (fun k => realVariation (r k)) := by
  unfold realVariation
  calc
    Finset.univ.sum (fun x => abs (Finset.univ.sum (fun k => r k x))) <=
        Finset.univ.sum (fun x => Finset.univ.sum (fun k => abs (r k x))) := by
      apply sum_le_sum
      intro x _
      exact abs_sum_le_sum_abs _ _
    _ = Finset.univ.sum (fun k => Finset.univ.sum (fun x => abs (r k x))) := by
      rw [Finset.sum_comm]

/-- Complex total variation of a unit-phase trine combination is bounded by
the sum of the three positive-outcome variations. -/
theorem complexVariation_trine_le
    {X : Type*} [Fintype X] (phase : Fin 3 -> Complex)
    (hphase : forall k, norm (phase k) = 1) (r : Fin 3 -> X -> Real) :
    complexVariation (fun x => Finset.univ.sum (fun k =>
      phase k * (r k x : Complex))) <=
      Finset.univ.sum (fun k => realVariation (r k)) := by
  unfold complexVariation realVariation
  calc
    Finset.univ.sum (fun x => norm (Finset.univ.sum (fun k =>
        phase k * (r k x : Complex)))) <=
        Finset.univ.sum (fun x => Finset.univ.sum (fun k =>
          norm (phase k * (r k x : Complex)))) := by
      apply sum_le_sum
      intro x _
      exact norm_sum_le _ _
    _ = Finset.univ.sum (fun x => Finset.univ.sum (fun k => abs (r k x))) := by
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro k _
      rw [norm_mul, hphase, one_mul, Complex.norm_real, Real.norm_eq_abs]
    _ = Finset.univ.sum (fun k => Finset.univ.sum (fun x => abs (r k x))) := by
      rw [Finset.sum_comm]

/-- Quantitative transported slack bound from the two variation controls.
This is the scalar inequality behind the manuscript's factor `3`. -/
theorem slack_transport_three
    {X : Type*} [Fintype X]
    (tauX tauY : X -> Real) (zetaX zetaY : X -> Complex) (epsilon : Real)
    (htau : realVariation (fun x => tauX x - tauY x) <= epsilon)
    (hzeta : complexVariation (fun x => zetaX x - zetaY x) <= epsilon) :
    realVariation (fun x => slack tauX zetaX x - slack tauY zetaY x) <=
      3 * epsilon := by
  unfold realVariation at htau ⊢
  unfold FiniteTargetProjectionAndQuotients.complexVariation at hzeta
  unfold slack
  calc
    Finset.univ.sum (fun x => abs
        ((tauX x - 2 * norm (zetaX x)) - (tauY x - 2 * norm (zetaY x)))) <=
      Finset.univ.sum (fun x =>
        abs (tauX x - tauY x) + 2 * norm (zetaX x - zetaY x)) := by
      apply sum_le_sum
      intro x _
      calc
        abs ((tauX x - 2 * norm (zetaX x)) - (tauY x - 2 * norm (zetaY x))) =
            abs ((tauX x - tauY x) - 2 * (norm (zetaX x) - norm (zetaY x))) := by ring
        _ <= abs (tauX x - tauY x) +
            abs (2 * (norm (zetaX x) - norm (zetaY x))) := abs_sub _ _
        _ <= abs (tauX x - tauY x) + 2 * norm (zetaX x - zetaY x) := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
          gcongr
          exact abs_norm_sub_norm_le _ _
    _ = Finset.univ.sum (fun x => abs (tauX x - tauY x)) +
        2 * Finset.univ.sum (fun x => norm (zetaX x - zetaY x)) := by
      rw [sum_add_distrib, Finset.mul_sum]
    _ <= 3 * epsilon := by linarith

/-- `thm:GT-trine-cofinal`: a summable adjacent trine transport error makes
every positive outcome converge on a fixed finite screen. -/
theorem trine_positive_outcome_cofinal
    {X : Type*} [Fintype X]
    (rho : Fin 3 -> Nat -> (X -> Real)) (epsilon : Nat -> Real)
    (hstep : forall k n, dist (rho k n) (rho k (n + 1)) <= epsilon n)
    (hsum : Summable epsilon) :
    forall k, exists limit : X -> Real,
      Tendsto (rho k) atTop (nhds limit) := by
  intro k
  have hc : CauchySeq (rho k) :=
    cauchySeq_of_dist_le_of_summable epsilon (hstep k) hsum
  exact cauchySeq_tendsto_of_complete hc

/-- Linear carrier and complex-current combinations of cofinally convergent
positive outcomes converge as well. -/
theorem trine_linear_outputs_converge
    {X : Type*} [Fintype X]
    (rho : Fin 3 -> Nat -> (X -> Real))
    (limit : Fin 3 -> X -> Real)
    (hrho : forall k, Tendsto (rho k) atTop (nhds (limit k)))
    (phase : Fin 3 -> Complex) :
    forall x,
      Tendsto (fun n => Finset.univ.sum (fun k => rho k n x)) atTop
          (nhds (Finset.univ.sum (fun k => limit k x))) /\
        Tendsto (fun n => Finset.univ.sum (fun k =>
          phase k * (rho k n x : Complex))) atTop
          (nhds (Finset.univ.sum (fun k =>
            phase k * (limit k x : Complex)))) := by
  intro x
  have hcoord (k : Fin 3) :
      Tendsto (fun n => rho k n x) atTop (nhds (limit k x)) :=
    tendsto_pi_nhds.mp (hrho k) x
  constructor
  · exact tendsto_finsetSum Finset.univ (fun k _ => hcoord k)
  · apply tendsto_finsetSum
    intro k _
    exact tendsto_const_nhds.mul
      ((Complex.continuous_ofReal.tendsto (limit k x)).comp (hcoord k))
end TrineComplexAcquisitionAndTransport
end NCG
