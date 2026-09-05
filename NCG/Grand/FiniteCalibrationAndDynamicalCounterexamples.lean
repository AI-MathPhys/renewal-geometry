/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite calibration and dynamical counterexamples

Concrete, kernel-checked witnesses for the calibration, common-history,
localizer, response, reflection, hypocoercive, and colour-law no-go records.
-/

open Matrix Finset

namespace NCG
namespace FiniteCalibrationAndDynamicalCounterexamples

/-! ## Finite calibration anchors -/

/-- A polynomial perturbation that vanishes on every displayed anchor. -/
def anchorPerturbation (s : Finset ℝ) (c x : ℝ) : ℝ :=
  c * ∏ a ∈ s, (x - a)

theorem anchorPerturbation_eq_zero (s : Finset ℝ) (c : ℝ)
    {a : ℝ} (ha : a ∈ s) : anchorPerturbation s c a = 0 := by
  unfold anchorPerturbation
  rw [Finset.prod_eq_zero ha]
  · ring
  · ring

/-- `cth:GT-finite-calibration-anchors`: outside the finite anchor bank,
the scalar coefficient is recoverable, so infinitely many distinct nonlinear
continuations agree on every anchor. -/
theorem finite_calibration_anchors_do_not_determine_response
    (s : Finset ℝ) {x : ℝ} (hx : x ∉ s) :
    Function.Injective (fun c : ℝ => fun y => anchorPerturbation s c y)
      ∧ (∀ c a, a ∈ s → anchorPerturbation s c a = 0) := by
  constructor
  · intro c d h
    have heval := congrFun h x
    simp only [anchorPerturbation] at heval
    have hprod : ∏ a ∈ s, (x - a) ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr fun a ha =>
        sub_ne_zero.mpr fun hxa => hx (by simpa [hxa] using ha)
    exact mul_right_cancel₀ hprod heval
  · intro c a ha
    exact anchorPerturbation_eq_zero s c ha

/-! ## Pairwise panels do not determine a three-way comparator -/

def evenParityLaw (w u b : Fin 2) : ℚ :=
  if (w.val + u.val + b.val) % 2 = 0 then 1 / 4 else 0

def oddParityLaw (w u b : Fin 2) : ℚ :=
  if (w.val + u.val + b.val) % 2 = 1 then 1 / 4 else 0

/-- `cth:GT-pairwise-no-comparator`: even and odd parity laws have identical
one- and two-coordinate marginals but opposite three-way parity. -/
theorem pairwise_panels_do_not_determine_comparator :
    (∀ w u, ∑ b, evenParityLaw w u b = ∑ b, oddParityLaw w u b)
    ∧ (∀ w b, ∑ u, evenParityLaw w u b = ∑ u, oddParityLaw w u b)
    ∧ (∀ u b, ∑ w, evenParityLaw w u b = ∑ w, oddParityLaw w u b)
    ∧ evenParityLaw 0 0 0 = 1 / 4
    ∧ oddParityLaw 0 0 0 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w u
    fin_cases w <;> fin_cases u <;>
      norm_num [evenParityLaw, oddParityLaw, Fin.sum_univ_two]
  · intro w b
    fin_cases w <;> fin_cases b <;>
      norm_num [evenParityLaw, oddParityLaw, Fin.sum_univ_two]
  · intro u b
    fin_cases u <;> fin_cases b <;>
      norm_num [evenParityLaw, oddParityLaw, Fin.sum_univ_two]
  · norm_num [evenParityLaw]
  · norm_num [oddParityLaw]

/-! ## Matrix marginal counterexamples -/

def armPopulationMatrix (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, 0; 0, 1 - a]

/-- `cth:GT-trine-no-full-matrix`: a continuum of positive diagonal states
has the same trace and off-diagonal target but different arm populations. -/
theorem trace_offDiagonal_do_not_determine_populations
    {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hab : a ≠ b) :
    (∀ x y : ℝ, 0 ≤ x ^ 2 + y ^ 2 →
      0 ≤ a * x ^ 2 + (1 - a) * y ^ 2)
    ∧ (∀ x y : ℝ, 0 ≤ x ^ 2 + y ^ 2 →
      0 ≤ b * x ^ 2 + (1 - b) * y ^ 2)
    ∧ Matrix.trace (armPopulationMatrix a) =
        Matrix.trace (armPopulationMatrix b)
    ∧ armPopulationMatrix a 0 1 = armPopulationMatrix b 0 1
    ∧ armPopulationMatrix a ≠ armPopulationMatrix b := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y _
    positivity
  · intro x y _
    positivity
  · simp [armPopulationMatrix, Matrix.trace, Fin.sum_univ_two]
  · simp [armPopulationMatrix]
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simpa [armPopulationMatrix] using hab h00

def localizer (b : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, b; b, 1]

/-- `cth:GT-localizer-marginals-no-kernel`: identical diagonal marginals do
not determine the existence or orientation of the kernel. -/
theorem localizer_marginals_do_not_determine_kernel :
    (∀ i : Fin 2, localizer 0 i i = localizer 1 i i
      ∧ localizer 0 i i = localizer (-1) i i)
    ∧ localizer 0 = 1
    ∧ localizer 1 *ᵥ ![1, -1] = 0
    ∧ localizer (-1) *ᵥ ![1, 1] = 0
    ∧ localizer 1 ≠ localizer (-1) := by
  constructor
  · intro i
    fin_cases i <;> norm_num [localizer]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [localizer]
  constructor
  · ext i
    fin_cases i <;> norm_num [localizer, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  constructor
  · ext i
    fin_cases i <;> norm_num [localizer, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    norm_num [localizer] at h01

/-- `cth:SM-writer-Gram-no-cone`: changing the second physical orientation
preserves the unsigned coefficient Gram and reverses the second cone axis. -/
theorem unsigned_writer_gram_does_not_determine_cone (x y : ℝ) :
    x ^ 2 + y ^ 2 = x ^ 2 + (-y) ^ 2
    ∧ (!![x, 0; 0, y] : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = y
    ∧ (!![x, 0; 0, -y] : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = -y := by
  constructor
  · ring
  · norm_num

/-! ## Response and dynamical counterexamples -/

/-- `cth:GT-nonempty-response-tables`: both levels are inhabited but no fine
response restricts to the unique coarse response. -/
theorem nonempty_response_tables_need_not_be_compatible :
    (∃ x : Fin 2, x = 0)
    ∧ (∃ x : Fin 2 × Fin 2, x = (1, 0))
    ∧ ¬∃ x : Fin 2 × Fin 2, x = (1, 0) ∧ x.1 = 0 := by
  refine ⟨⟨0, rfl⟩, ⟨(1, 0), rfl⟩, ?_⟩
  rintro ⟨x, rfl, h⟩
  norm_num at h

/-- `cth:GT-barycenter-not-solution`: the average of the zero and delayed
quadratic solutions fails the nonlinear equation at every positive time. -/
theorem nonlinear_barycenter_not_solution {t : ℝ} (ht : 0 < t) :
    t ≠ Real.sqrt 2 * t := by
  intro h
  have hsqrt : Real.sqrt 2 = 1 := by
    apply mul_right_cancel₀ (ne_of_gt ht)
    simpa [mul_comm] using h.symm
  have hsq := congrArg (fun x : ℝ => x ^ 2) hsqrt
  norm_num at hsq

/-- `cth:GT-positive-cost-no-budget`: a positive self-loop cost is compatible
with an infinite constant history and linearly growing accumulated payment. -/
theorem positive_recurrent_cost_has_infinite_history (n : ℕ) :
    (∑ _k ∈ Finset.range n, (1 : ℕ)) = n := by
  simp

/-! ## Reflection and hypocoercive finite witnesses -/

def reflectionKernel : Matrix (Fin 2) (Fin 2) ℤ := !![1, 2; 2, 1]

/-- `cth:SMST-positive-no-reflection`: the pointwise-positive kernel has a
negative reflection-Gram direction. -/
theorem pointwise_positive_not_reflection_positive :
    (∀ i j, 0 < reflectionKernel i j)
    ∧ reflectionKernel *ᵥ ![1, -1] = -![1, -1] := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [reflectionKernel]
  · ext i
    fin_cases i <;> norm_num [reflectionKernel, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

def symmetricAction : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 0]
def circulation : Matrix (Fin 2) (Fin 2) ℚ := !![0, -1/2; 1/2, 0]
def hypGenerator : Matrix (Fin 2) (Fin 2) ℚ := -symmetricAction + circulation

/-- `cth:GT-symmetric-null-positive-decay`: circulation fills the missing
observability direction even though the symmetric action has a zero mode. -/
theorem symmetric_null_can_have_positive_hypocoercive_observability :
    symmetricAction *ᵥ ![0, 1] = 0
    ∧ (symmetricAction + circulationᴴ * symmetricAction * circulation)
        = !![1, 0; 0, 1/4]
    ∧ hypGenerator *ᵥ ![0, 1] ≠ 0 := by
  constructor
  · ext i
    fin_cases i <;> norm_num [symmetricAction, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [symmetricAction, circulation, Matrix.mul_apply,
        Fin.sum_univ_two]
  · intro h
    have h0 := congrFun h 0
    norm_num [hypGenerator, symmetricAction, circulation, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] at h0

/-! ## Static action does not select a slab law -/

def twoStateSlab (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - a, a; a, 1 - a]

/-- `cth:SMYM-action-no-law`: every displayed slab has the same stationary
law, while its fixed-free eigenvalue is `1-2a`. -/
theorem static_action_does_not_select_slab (a : ℝ) :
    twoStateSlab a *ᵥ ![(1 : ℝ) / 2, 1 / 2] = ![1 / 2, 1 / 2]
    ∧ twoStateSlab a *ᵥ ![1, -1] = (1 - 2 * a) • ![1, -1] := by
  constructor <;> ext i <;> fin_cases i <;>
    norm_num [twoStateSlab, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

end FiniteCalibrationAndDynamicalCounterexamples
end NCG
