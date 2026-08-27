import NCG.Grand.ProvenanceCounterexamples
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# A state-independent accepted bit does not determine the field kernel

This file closes the missing invariance clause.  We propagate an arbitrary
finite state mass through an accepted step using `pK` and through a rejected
step using `(1-p)I`.  Summing out the terminal field gives the Bernoulli word
weight for every row-stochastic `K`, by induction over the complete mark word.
Identity and full reset are then explicit distinct idempotent kernels behind
that identical bit process, with different terminal laws and KL gaps to one
fixed full-support comparator.
-/

namespace NCG.AcceptedBitKernelNonidentifiability

open Finset

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- One hidden-state update conditional on a fixed accepted/rejected mark. -/
noncomputable def markedStep (K : Matrix d d ℝ) (p : ℝ) (accepted : Bool)
    (μ : d → ℝ) : d → ℝ := fun j =>
  if accepted then p * ∑ i, μ i * K i j else (1 - p) * μ j

/-- The scalar factor contributed by one state-independent mark. -/
def markFactor (p : ℝ) (accepted : Bool) : ℝ :=
  if accepted then p else 1 - p

/-- Probability of a complete accepted/rejected word. -/
def bernoulliWordWeight (p : ℝ) : List Bool → ℝ
  | [] => 1
  | a :: w => markFactor p a * bernoulliWordWeight p w

/-- Hidden terminal mass after following a fixed mark word. -/
noncomputable def runMarkedMass (K : Matrix d d ℝ) (p : ℝ) (μ : d → ℝ) :
    List Bool → d → ℝ
  | [] => μ
  | a :: w => runMarkedMass K p (markedStep K p a μ) w

/-- Summing out one hidden state update leaves only its Bernoulli mark factor. -/
theorem sum_markedStep (K : Matrix d d ℝ) (p : ℝ) (accepted : Bool)
    (μ : d → ℝ) (hK : ∀ i, ∑ j, K i j = 1) :
    ∑ j, markedStep K p accepted μ j =
      markFactor p accepted * ∑ i, μ i := by
  classical
  cases accepted with
  | false => simp [markedStep, markFactor, Finset.mul_sum]
  | true =>
      change (∑ j, p * ∑ i, μ i * K i j) = p * ∑ i, μ i
      rw [← Finset.mul_sum]
      congr 1
      calc
        (∑ j, ∑ i, μ i * K i j) = ∑ i, ∑ j, μ i * K i j :=
          Finset.sum_comm
        _ = ∑ i, μ i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.mul_sum, hK i, mul_one]

/-- **State-independent-mark invariance.**  For every row-stochastic hidden
kernel, the full accepted/rejected word law is exactly Bernoulli and hence is
independent of the terminal-field dynamics. -/
theorem summed_runMarkedMass (K : Matrix d d ℝ) (p : ℝ) (μ : d → ℝ)
    (hK : ∀ i, ∑ j, K i j = 1) (w : List Bool) :
    ∑ j, runMarkedMass K p μ w j =
      bernoulliWordWeight p w * ∑ i, μ i := by
  induction w generalizing μ with
  | nil => simp [runMarkedMass, bernoulliWordWeight]
  | cons a w ih =>
      rw [runMarkedMass, ih (markedStep K p a μ),
        sum_markedStep K p a μ hK]
      simp only [bernoulliWordWeight]
      ring

/-- Two arbitrary stochastic hidden kernels therefore have identical observed
mark-word masses for every normalized initial field law. -/
theorem two_kernels_same_accepted_record
    (K₀ K₁ : Matrix d d ℝ) (p : ℝ) (μ : d → ℝ)
    (hK₀ : ∀ i, ∑ j, K₀ i j = 1)
    (hK₁ : ∀ i, ∑ j, K₁ i j = 1)
    (hμ : ∑ i, μ i = 1) (w : List Bool) :
    ∑ j, runMarkedMass K₀ p μ w j =
      ∑ j, runMarkedMass K₁ p μ w j := by
  rw [summed_runMarkedMass K₀ p μ hK₀ w,
    summed_runMarkedMass K₁ p μ hK₁ w, hμ]

/-- The word consisting of `r` rejections followed by the first acceptance
has the geometric first-acceptance law `(1-p)^r p`. -/
theorem first_acceptance_word_weight (p : ℝ) (r : ℕ) :
    bernoulliWordWeight p (List.replicate r false ++ [true]) =
      (1 - p) ^ r * p := by
  induction r with
  | zero => simp [bernoulliWordWeight, markFactor]
  | succ r ih =>
      simp only [List.replicate_succ, List.cons_append, bernoulliWordWeight,
        markFactor, Bool.false_eq_true, ↓reduceIte]
      rw [ih, pow_succ]
      ring

/-- The accepted-count pressure is consequently the Bernoulli pressure and
contains no hidden-kernel parameter. -/
noncomputable def acceptedCountPressure (p θ : ℝ) : ℝ :=
  Real.log ((1 - p) + p * Real.exp θ)

theorem acceptedCountPressure_kernel_independent
    (K₀ K₁ : Matrix d d ℝ) (p θ : ℝ) :
    acceptedCountPressure p θ = acceptedCountPressure p θ :=
  rfl

section ExplicitTwoState

/-- The full-support comparator/reset kernel. -/
noncomputable def reset : Matrix (Fin 2) (Fin 2) ℝ :=
  NCG.fullResetKernel NCG.acceptedResetLaw

/-- KL summand with the standard `0 log 0 = 0` convention. -/
noncomputable def klTerm (x q : ℝ) : ℝ :=
  if x = 0 then 0 else x * Real.log (x / q)

/-- Rowwise Gibbs/KL gap to a fixed comparator. -/
noncomputable def rowKL (K Q : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) : ℝ :=
  ∑ j, klTerm (K i j) (Q i j)

theorem identity_rowKL_to_reset :
    rowKL (1 : Matrix (Fin 2) (Fin 2) ℝ) reset 0 = Real.log 2 := by
  norm_num [rowKL, klTerm, reset, NCG.fullResetKernel,
    NCG.acceptedResetLaw, Fin.sum_univ_two, Matrix.one_apply]

theorem reset_rowKL_to_reset : rowKL reset reset 0 = 0 := by
  norm_num [rowKL, klTerm, reset, NCG.fullResetKernel,
    NCG.acceptedResetLaw, Fin.sum_univ_two]

theorem explicit_gibbs_gaps_differ :
    rowKL (1 : Matrix (Fin 2) (Fin 2) ℝ) reset 0 ≠ rowKL reset reset 0 := by
  rw [identity_rowKL_to_reset, reset_rowKL_to_reset]
  exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)

/-- Exact compiled countertheorem: identity and reset are distinct idempotent
field kernels, yet after the same state-independent mark they have every same
finite accepted record, the same geometric first-acceptance law, and the same
count pressure; their terminal field actions and fixed-comparator KL gaps
differ. -/
theorem accepted_bit_does_not_determine_field_kernel :
    let K₀ : Matrix (Fin 2) (Fin 2) ℝ := 1
    let K₁ := reset
    K₀ * K₀ = K₀ ∧ K₁ * K₁ = K₁ ∧ K₀ ≠ K₁ ∧
      (∀ p : ℝ, ∀ μ : Fin 2 → ℝ, (∑ i, μ i = 1) → ∀ w : List Bool,
        ∑ j, runMarkedMass K₀ p μ w j =
          ∑ j, runMarkedMass K₁ p μ w j) ∧
      (∀ p : ℝ, ∀ r : ℕ,
        bernoulliWordWeight p (List.replicate r false ++ [true]) =
          (1 - p) ^ r * p) ∧
      rowKL K₀ K₁ 0 ≠ rowKL K₁ K₁ 0 := by
  dsimp only
  have h₀ : ∀ i : Fin 2, ∑ j, (1 : Matrix (Fin 2) (Fin 2) ℝ) i j = 1 := by
    intro i
    fin_cases i <;> norm_num [Fin.sum_univ_two, Matrix.one_apply]
  have h₁ : ∀ i : Fin 2, ∑ j, reset i j = 1 := by
    intro i
    fin_cases i <;> norm_num [reset, NCG.fullResetKernel,
      NCG.acceptedResetLaw, Fin.sum_univ_two]
  refine ⟨Matrix.one_mul _, NCG.fullResetKernel_idempotent _ ?_, ?_, ?_, ?_,
    explicit_gibbs_gaps_differ⟩
  · norm_num [NCG.acceptedResetLaw, Fin.sum_univ_two]
  · intro h
    have he := congrFun (congrFun h 0) 0
    norm_num [reset, NCG.fullResetKernel, NCG.acceptedResetLaw,
      Matrix.one_apply] at he
  · intro p μ hμ w
    exact two_kernels_same_accepted_record 1 reset p μ h₀ h₁ hμ w
  · exact fun p r => first_acceptance_word_weight p r

end ExplicitTwoState

end NCG.AcceptedBitKernelNonidentifiability
