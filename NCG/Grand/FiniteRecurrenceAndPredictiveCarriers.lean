/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SchurAssociativityMatrix
import NCG.Grand.IndependentExponentialCompletionTime

/-!
# Finite recurrence ranks and predictive--action carriers

Exact finite quotient, amortization, summability, projection-curvature, and
stopping-front lemmas used by the recurrence and predictive-action statements.
-/

open Finset Filter Topology Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace FiniteRecurrenceAndPredictiveCarriers

/-- Canonical future-signature quotient. -/
abbrev FutureSignatureQuotient {State Signature : Type*}
    (signature : State -> Signature) := Set.range signature

def futureSignatureMap {State Signature : Type*}
    (signature : State -> Signature) :
    State -> FutureSignatureQuotient signature :=
  fun state => ⟨signature state, state, rfl⟩

theorem futureSignatureMap_surjective {State Signature : Type*}
    (signature : State -> Signature) :
    Function.Surjective (futureSignatureMap signature) := by
  rintro ⟨value, state, rfl⟩
  exact ⟨state, rfl⟩

/-- The future-signature quotient is the unique coarsest deterministic record
sufficient for all declared signatures. -/
theorem future_signature_coarsest
    {State Signature Record : Type*}
    (signature : State -> Signature) (record : State -> Record)
    (decoder : Record -> Signature)
    (hsufficient : forall state, decoder (record state) = signature state) :
    exists descend : Set.range record -> FutureSignatureQuotient signature,
      Function.Surjective descend /\
      forall state, descend (⟨record state, state, rfl⟩) =
        futureSignatureMap signature state := by
  let descend : Set.range record -> FutureSignatureQuotient signature :=
    fun value =>
      let state := Classical.choose value.property
      ⟨decoder value.1, state, by
        have hrecord : record state = value.1 :=
          Classical.choose_spec value.property
        calc
          signature state = decoder (record state) := (hsufficient state).symm
          _ = decoder value.1 := congrArg decoder hrecord⟩
  refine ⟨descend, ?_, ?_⟩
  · rintro ⟨value, state, rfl⟩
    refine ⟨⟨record state, state, rfl⟩, ?_⟩
    apply Subtype.ext
    exact hsufficient state
  · intro state
    apply Subtype.ext
    exact hsufficient state

/-- Unread refinements do not enlarge the canonical future quotient. -/
theorem unread_refinement_same_future_quotient
    {State Signature Refinement : Type*}
    (signature : State -> Signature) (refinement : State -> Refinement)
    (decoder : Refinement -> Signature)
    (h : forall state, decoder (refinement state) = signature state) :
    exists descend : Set.range refinement -> FutureSignatureQuotient signature,
      forall state, descend (⟨refinement state, state, rfl⟩) =
        futureSignatureMap signature state := by
  obtain ⟨descend, _, hdescend⟩ :=
    future_signature_coarsest signature refinement decoder h
  exact ⟨descend, hdescend⟩

/-- `thm:GT-Bellman-action-rank`: the action plus Bellman potential decreases
by at least the certified cycle margin at every retained transition. -/
theorem bellman_amortized_descent
    {action actionNext cost potentialSource potentialTarget eta : Real}
    (haction : actionNext <= action - cost)
    (hbellman : eta <= cost + potentialSource - potentialTarget) :
    actionNext + potentialTarget <= action + potentialSource - eta := by
  linarith

/-- A positive amortized margin gives a strict integer rank whenever the
potential is already integer-scaled. -/
theorem bellman_natural_rank_strict
    {rank rankNext : Nat} {eta : Nat} (heta : 0 < eta)
    (hstep : rankNext + eta <= rank) : rankNext < rank := by
  omega

/-- Pointwise paid-process comparison: summable stock inflow, repair, and
comparison errors force summable declared recurrence cost. -/
theorem process_paid_recurrence
    (cost inflow repair error : Nat -> Real)
    (hcost : forall n, 0 <= cost n)
    (hpaid : forall n, cost n <= inflow n + repair n + error n)
    (hinflow : Summable inflow) (hrepair : Summable repair)
    (herror : Summable error) : Summable cost := by
  apply Summable.of_nonneg_of_le hcost hpaid
  exact (hinflow.add hrepair).add herror

/-- A summable paid cost cannot dominate a nonsummable nonnegative debit. -/
theorem process_paid_excludes_cofinal
    (cost debit : Nat -> Real)
    (hcost : Summable cost)
    (hdebitNonneg : forall n, 0 <= debit n)
    (hle : forall n, debit n <= cost n) : Summable debit :=
  Summable.of_nonneg_of_le hdebitNonneg hle hcost

/-- Source-anchored finite crossing bound: once accumulated margins exceed the
available action budget, that screen cannot be crossed. -/
theorem source_anchored_crossing_bound
    {H : Nat} (delta : Nat -> Real) (budget : Real)
    (hcross : forall h, h <= H -> (Finset.range (h + 1)).sum delta <= budget)
    (hexceed : budget < (Finset.range (H + 1)).sum delta) : False := by
  exact (not_le_of_gt hexceed) (hcross H le_rfl)

/-- The adjoint/action innovation is a literal Gram and is therefore positive.
It vanishes exactly when the adjoint preserves the predictive carrier. -/
theorem predictive_action_innovation
    {n : Type*} [Fintype n] [DecidableEq n]
    (P U : Matrix n n Complex) (hPH : Pᴴ = P) (hP2 : P * P = P) :
    let X := (1 - P) * Uᴴ * P
    P * U * (1 - P) * Uᴴ * P = Xᴴ * X /\
      (P * U * (1 - P) * Uᴴ * P).PosSemidef /\
      (P * U * (1 - P) * Uᴴ * P = 0 <-> (1 - P) * Uᴴ * P = 0) := by
  dsimp only
  have hQH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hP2]
    abel
  have hgram : P * U * (1 - P) * Uᴴ * P =
      ((1 - P) * Uᴴ * P)ᴴ * ((1 - P) * Uᴴ * P) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hPH, Matrix.conjTranspose_conjTranspose, hQH]
    simp only [Matrix.mul_assoc]
    rw [show (1 - P) * ((1 - P) * (Uᴴ * P)) =
        (1 - P) * (Uᴴ * P) by
      rw [← Matrix.mul_assoc, hQ2]]
  refine ⟨hgram, ?_, ?_⟩
  · rw [hgram]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · rw [hgram]
    exact Matrix.conjTranspose_mul_self_eq_zero

/-- The signed difference of the two reveal-order ledgers is the weight
difference times the interchange secant. -/
theorem reveal_order_ledger_difference
    {A : Type*} [AddCommGroup A] [Module Real A]
    (future context base joint : A) (alpha beta : Real) :
    alpha • (future - base) + beta • (joint - future) -
        (beta • (context - base) + alpha • (joint - context)) =
      (alpha - beta) • (future + context - base - joint) := by
  module

/-- Rectangular curvature is a commutator Gram; it is positive and vanishes
exactly on the commuting branch. -/
theorem rectangular_curvature
    {n : Type*} [Fintype n]
    (P Q : Matrix n n Complex) :
    let commutator := P * Q - Q * P
    (commutatorᴴ * commutator).PosSemidef /\
      (commutatorᴴ * commutator = 0 <-> P * Q = Q * P) := by
  dsimp only
  constructor
  · exact Matrix.posSemidef_conjTranspose_mul_self _
  · rw [Matrix.conjTranspose_mul_self_eq_zero, sub_eq_zero]

/-- Finite stopping-front tail estimate. -/
theorem weighted_stopping_front_tail
    (weight mass : Nat -> Real) (N R : Nat) (C : Real)
    (hR : R + 1 < N)
    (hmass : forall n, 0 <= mass n)
    (hweightNonneg : forall n, 0 <= weight n)
    (hweight : forall n, R < n -> n < N -> weight (R + 1) <= weight n)
    (hweighted : (Finset.range N).sum (fun n => weight n * mass n) <= C)
    (hweightPos : 0 < weight (R + 1)) :
    ((Finset.range N).filter (fun n => R < n)).sum mass <=
      C / weight (R + 1) := by
  let tail := (Finset.range N).filter (fun n => R < n)
  have htail : weight (R + 1) * tail.sum mass <= C := by
    calc
      weight (R + 1) * tail.sum mass =
          tail.sum (fun n => weight (R + 1) * mass n) := by
        rw [Finset.mul_sum]
      _ <= tail.sum (fun n => weight n * mass n) := by
        apply sum_le_sum
        intro n hn
        have hn' := Finset.mem_filter.mp hn
        exact mul_le_mul_of_nonneg_right
          (hweight n hn'.2 (Finset.mem_range.mp hn'.1)) (hmass n)
      _ <= (Finset.range N).sum (fun n => weight n * mass n) := by
        apply sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro n _ _
        exact mul_nonneg (hweightNonneg n) (hmass n)
      _ <= C := hweighted
  exact (le_div_iff₀ hweightPos).2 (by simpa [mul_comm] using htail)
end FiniteRecurrenceAndPredictiveCarriers
end NCG
