/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCPathLikelihoodExact
import NCG.Grand.QuantumCylinderInverseLimitExact
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Genuine jump-sequence law of a finite continuous-time Markov chain

For a finite generator whose escape rates are positive, this file constructs
the embedded jump chain, couples each destination with an independent
exponential holding time, and iterates the resulting Markov kernel by the
Ionescu--Tulcea theorem.  The output is a genuine probability measure on
infinite holding-time/state sequences.
-/

open MeasureTheory ProbabilityTheory Finset Set Preorder
open ProbabilityTheory.Kernel
open scoped ENNReal

noncomputable section

namespace NCG.FiniteCTMCJumpSequenceLaw

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

open NCG.DrivenProcess
open NCG.DrivenProcess.FinitePath
open NCG.QuantumCylinderInverseLimit

/-- Conditional destination probability of the embedded jump chain. -/
def destinationProbability (L : Matrix S S ℝ) (x y : S) : ℝ :=
  if y = x then 0 else L x y / escapeRate L x

/-- Embedded jump probabilities are nonnegative. -/
theorem destinationProbability_nonnegative
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) (x y : S) :
    0 ≤ destinationProbability L x y := by
  unfold destinationProbability
  split_ifs with hyx
  · exact le_rfl
  · exact div_nonneg (hL.offDiag_nonneg x y (Ne.symm hyx)) (hescape x).le

/-- The embedded destination probabilities sum to one. -/
theorem sum_destinationProbability
    (L : Matrix S S ℝ) (hescape : ∀ x, 0 < escapeRate L x) (x : S) :
    ∑ y, destinationProbability L x y = 1 := by
  unfold destinationProbability
  calc
    (∑ y, if y = x then 0 else L x y / escapeRate L x) =
        (Finset.univ.erase x).sum
          (fun y => L x y / escapeRate L x) := by
      rw [← Finset.sum_erase (s := Finset.univ) (a := x)
        (f := fun y => if y = x then 0 else L x y / escapeRate L x)
        (by simp)]
      apply Finset.sum_congr rfl
      intro y hy
      simp only [ite_eq_right_iff]
      intro h
      exact (Finset.ne_of_mem_erase hy h).elim
    _ = (Finset.univ.erase x).sum (fun y => L x y) /
        escapeRate L x := by
      rw [Finset.sum_div]
    _ = 1 := by
      unfold escapeRate
      exact div_self (by
        have := (hescape x).ne'
        simpa [escapeRate] using this)

/-- Discrete law of the destination selected after leaving `x`. -/
def destinationMeasure (L : Matrix S S ℝ) (x : S) : Measure S :=
  discrete (destinationProbability L x)

/-- The destination law is a probability measure. -/
theorem destinationMeasure_isProbabilityMeasure
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) (x : S) :
    IsProbabilityMeasure (destinationMeasure L x) := by
  unfold destinationMeasure
  exact isProbabilityMeasure_discrete
    (destinationProbability_nonnegative L hL hescape x)
    (sum_destinationProbability L hescape x)

/-- One CTMC jump step: an exponential holding time paired with the next
embedded-chain state. -/
def holdingDestinationMeasure (L : Matrix S S ℝ) (x : S) :
    Measure (ℝ × S) :=
  (ProbabilityTheory.expMeasure (escapeRate L x)).prod
    (destinationMeasure L x)

/-- Each holding-time/destination step has total mass one. -/
theorem holdingDestinationMeasure_isProbabilityMeasure
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) (x : S) :
    IsProbabilityMeasure (holdingDestinationMeasure L x) := by
  letI : IsProbabilityMeasure
      (ProbabilityTheory.expMeasure (escapeRate L x)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (hescape x)
  letI : IsProbabilityMeasure (destinationMeasure L x) :=
    destinationMeasure_isProbabilityMeasure L hL hescape x
  unfold holdingDestinationMeasure
  infer_instance

/-- Exact one-step rectangle probability: exponential holding-time mass
times the embedded destination weight. -/
theorem holdingDestinationMeasure_apply_prod_singleton
    (L : Matrix S S ℝ) (x y : S) (A : Set ℝ) :
    holdingDestinationMeasure L x (A ×ˢ ({y} : Set S)) =
      ProbabilityTheory.expMeasure (escapeRate L x) A *
        ENNReal.ofReal (destinationProbability L x y) := by
  unfold holdingDestinationMeasure destinationMeasure
  rw [Measure.prod_prod, discrete_singleton]

/-- On a genuine jump, the embedded destination weight is the generator
rate divided by the escape rate. -/
theorem destinationProbability_of_ne
    (L : Matrix S S ℝ) {x y : S} (hxy : y ≠ x) :
    destinationProbability L x y = L x y / escapeRate L x := by
  simp [destinationProbability, hxy]

/-- Markov kernel that samples the next holding time and destination from the
current finite state. -/
def jumpKernel (L : Matrix S S ℝ) : Kernel S (ℝ × S) :=
  Kernel.ofFunOfCountable (holdingDestinationMeasure L)

/-- The one-jump kernel is Markov. -/
theorem jumpKernel_isMarkov
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) :
    IsMarkovKernel (jumpKernel L) :=
  ⟨fun x => holdingDestinationMeasure_isProbabilityMeasure L hL hescape x⟩

/-- Current state extracted from a finite holding-time/state history. -/
def currentState (n : ℕ) (history : Π _ : Finset.Iic n, ℝ × S) : S :=
  (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2

/-- Current-state extraction is measurable. -/
theorem measurable_currentState (n : ℕ) :
    Measurable (currentState (S := S) n) := by
  unfold currentState
  exact measurable_snd.comp (measurable_pi_apply _)

/-- History-dependent kernel required by Ionescu--Tulcea; it depends only on
the most recent state. -/
def historyJumpKernel (L : Matrix S S ℝ) (n : ℕ) :
    Kernel (Π _ : Finset.Iic n, ℝ × S) (ℝ × S) :=
  (jumpKernel L).comap (currentState n) (measurable_currentState n)

/-- Every history kernel is Markov. -/
theorem historyJumpKernel_isMarkov
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) (n : ℕ) :
    IsMarkovKernel (historyJumpKernel L n) := by
  letI : IsMarkovKernel (jumpKernel L) := jumpKernel_isMarkov L hL hescape
  unfold historyJumpKernel
  infer_instance

/-- Initial dummy holding time zero paired with the initial-state law. -/
def initialHoldingStateMeasure (p : S → ℝ) : Measure (ℝ × S) :=
  (Measure.dirac (0 : ℝ)).prod (discrete p)

/-- A probability vector gives a probability law for the initial pair. -/
theorem initialHoldingStateMeasure_isProbabilityMeasure
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    IsProbabilityMeasure (initialHoldingStateMeasure p) := by
  letI : IsProbabilityMeasure (discrete p) :=
    isProbabilityMeasure_discrete hp hp1
  unfold initialHoldingStateMeasure
  infer_instance

/-- Genuine infinite jump-sequence law obtained by Ionescu--Tulcea.  Index
zero stores `(0, X₀)`; index `n+1` stores the holding time after `Xₙ` and the
new state `Xₙ₊₁`. -/
def jumpSequenceLaw
    (p : S → ℝ) (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) : Measure (ℕ → ℝ × S) := by
  letI : ∀ n, IsMarkovKernel (historyJumpKernel L n) :=
    fun n => historyJumpKernel_isMarkov L hL hescape n
  exact Kernel.trajMeasure (initialHoldingStateMeasure p) (historyJumpKernel L)

/-- The constructed jump-sequence law is a probability measure. -/
theorem jumpSequenceLaw_isProbabilityMeasure
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) :
    IsProbabilityMeasure (jumpSequenceLaw p L hL hescape) := by
  letI : IsProbabilityMeasure (initialHoldingStateMeasure p) :=
    initialHoldingStateMeasure_isProbabilityMeasure p hp hp1
  letI : ∀ n, IsMarkovKernel (historyJumpKernel L n) :=
    fun n => historyJumpKernel_isMarkov L hL hescape n
  unfold jumpSequenceLaw
  infer_instance

/-- Finite-prefix marginal of the infinite jump sequence. -/
def jumpPrefixLaw
    (p : S → ℝ) (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) (n : ℕ) :
    Measure (Π _ : Finset.Iic n, ℝ × S) :=
  (jumpSequenceLaw p L hL hescape).map (frestrictLe n)

/-- Every finite prefix is itself a probability measure. -/
theorem jumpPrefixLaw_isProbabilityMeasure
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) (n : ℕ) :
    IsProbabilityMeasure (jumpPrefixLaw p L hL hescape n) := by
  letI : IsProbabilityMeasure (jumpSequenceLaw p L hL hescape) :=
    jumpSequenceLaw_isProbabilityMeasure p hp hp1 L hL hescape
  unfold jumpPrefixLaw
  have hm : Measurable
      (frestrictLe (π := fun _ : ℕ => ℝ × S) n) := by fun_prop
  exact Measure.isProbabilityMeasure_map hm.aemeasurable

/-- The regular conditional law of the next holding-time/state pair, given
the finite history, is exactly the CTMC history kernel. -/
theorem condDistrib_jumpSequenceLaw
    [Nonempty S]
    (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (L : Matrix S S ℝ) (hL : IsGenerator L)
    (hescape : ∀ x, 0 < escapeRate L x) (a : ℕ) :
    letI : IsProbabilityMeasure (jumpSequenceLaw p L hL hescape) :=
      jumpSequenceLaw_isProbabilityMeasure p hp hp1 L hL hescape
    ProbabilityTheory.condDistrib (fun x : ℕ → ℝ × S => x (a + 1))
        (frestrictLe a) (jumpSequenceLaw p L hL hescape) =ᵐ[
          (jumpSequenceLaw p L hL hescape).map (frestrictLe a)]
      historyJumpKernel L a := by
  letI : IsProbabilityMeasure (initialHoldingStateMeasure p) :=
    initialHoldingStateMeasure_isProbabilityMeasure p hp hp1
  letI : ∀ n, IsMarkovKernel (historyJumpKernel L n) :=
    fun n => historyJumpKernel_isMarkov L hL hescape n
  unfold jumpSequenceLaw
  exact ProbabilityTheory.Kernel.condDistrib_trajMeasure

end NCG.FiniteCTMCJumpSequenceLaw
