/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Positive cylinders, likelihood gauges, and trine reconstruction

Exact finite forms of the positive-cylinder and scalar complex-history
statements introduced in Gran-Tensor V047.
-/

open Finset

namespace NCG
namespace PositiveCylinderAndTrine

def cylinderMass {Ω : Type*} [Fintype Ω] (Λ : Ω → ℝ) : ℝ :=
  ∑ ω, Λ ω

noncomputable def normalizedCylinder {Ω : Type*} [Fintype Ω]
    (Λ : Ω → ℝ) : Ω → ℝ :=
  fun ω => Λ ω / cylinderMass Λ

noncomputable def likelihoodGauge {Ω : Type*} [Fintype Ω]
    (Λ ν : Ω → ℝ) : Ω → ℝ :=
  fun ω => Λ ω / (cylinderMass Λ * ν ω)

/-- `thm:GT-positive-cylinder-gauge`: every full-support reference law gives
the same normalized positive cylinder and the likelihood has mean one. -/
theorem positive_cylinder_reference_gauge {Ω : Type*} [Fintype Ω]
    (Λ ν A : Ω → ℝ) (hZ : cylinderMass Λ ≠ 0)
    (hν : ∀ ω, ν ω ≠ 0) (hνsum : ∑ ω, ν ω = 1) :
    (∑ ω, ν ω * likelihoodGauge Λ ν ω = 1)
      ∧ (∑ ω, normalizedCylinder Λ ω * A ω
        = ∑ ω, ν ω * (likelihoodGauge Λ ν ω * A ω)) := by
  constructor
  · calc
      ∑ ω, ν ω * likelihoodGauge Λ ν ω
          = ∑ ω, Λ ω / cylinderMass Λ := by
              apply sum_congr rfl
              intro ω _
              simp only [likelihoodGauge]
              field_simp [hν ω]
      _ = cylinderMass Λ / cylinderMass Λ := by
            rw [cylinderMass, sum_div]
      _ = 1 := div_self hZ
  · apply sum_congr rfl
    intro ω _
    simp only [normalizedCylinder, likelihoodGauge]
    field_simp [hν ω]

/-- Reweighting the sampling reference and compensating the likelihood leaves
the unnormalized cylinder pointwise unchanged. -/
theorem likelihood_reweighting_is_gauge {Ω : Type*} [Fintype Ω]
    (ν W h : Ω → ℝ) (Eh : ℝ) (hEh : Eh ≠ 0)
    (hh : ∀ ω, h ω ≠ 0) :
    ∀ ω, (h ω * ν ω / Eh) * (W ω * Eh / h ω) = ν ω * W ω := by
  intro ω
  field_simp [hEh, hh ω]

/-- Finite exponential deformation has the expected source derivative. -/
theorem cylinder_deformation_hasDerivAt {Ω : Type*} [Fintype Ω]
    (Λ J : Ω → ℝ) :
    HasDerivAt (fun θ => ∑ ω, Λ ω * Real.exp (θ * J ω))
      (∑ ω, Λ ω * J ω) 0 := by
  have hterm : ∀ ω, HasDerivAt
      (fun θ => Λ ω * Real.exp (θ * J ω)) (Λ ω * J ω) 0 := by
    intro ω
    have hlin : HasDerivAt (fun θ : ℝ => θ * J ω) (J ω) 0 := by
      simpa using (hasDerivAt_id 0).mul_const (J ω)
    simpa only [zero_mul, Real.exp_zero, one_mul] using
      hlin.exp.const_mul (Λ ω)
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun ω _ => hterm ω)
  have hfun : (∑ ω ∈ Finset.univ,
      fun θ => Λ ω * Real.exp (θ * J ω)) =
      fun θ => ∑ ω, Λ ω * Real.exp (θ * J ω) := by
    funext θ
    simp [Finset.sum_apply]
  rw [hfun] at hsum
  exact hsum

/-- The derivative of log partition is the cylinder-normalized source mean. -/
theorem log_partition_derivative {Ω : Type*} [Fintype Ω]
    (Λ J : Ω → ℝ) (hZ : cylinderMass Λ ≠ 0) :
    HasDerivAt
      (fun θ => Real.log (∑ ω, Λ ω * Real.exp (θ * J ω)))
      (∑ ω, normalizedCylinder Λ ω * J ω) 0 := by
  have hbase : (∑ ω, Λ ω * Real.exp ((0 : ℝ) * J ω))
      = cylinderMass Λ := by simp [cylinderMass]
  have h := (cylinder_deformation_hasDerivAt Λ J).log (by simpa [hbase])
  have hcoef : (∑ ω, normalizedCylinder Λ ω * J ω)
      = (∑ ω, Λ ω * J ω) / cylinderMass Λ := by
    calc
      ∑ ω, normalizedCylinder Λ ω * J ω
          = ∑ ω, (Λ ω * J ω) / cylinderMass Λ := by
              apply sum_congr rfl
              intro ω _
              simp [normalizedCylinder]
              ring
      _ = (∑ ω, Λ ω * J ω) / cylinderMass Λ := by
            rw [sum_div]
  rw [hcoef]
  simpa only [hbase] using h

/-- `cor:accepted-cylinder-before-LR`: the intrinsic expectation is invariant
under every full-support likelihood representation. -/
theorem accepted_cylinder_before_likelihood {Ω : Type*} [Fintype Ω]
    (Λ ν A : Ω → ℝ) (hZ : cylinderMass Λ ≠ 0)
    (hν : ∀ ω, ν ω ≠ 0) (hνsum : ∑ ω, ν ω = 1) :
    ∑ ω, normalizedCylinder Λ ω * A ω
      = ∑ ω, ν ω * (likelihoodGauge Λ ν ω * A ω) :=
  (positive_cylinder_reference_gauge Λ ν A hZ hν hνsum).2

/-! ## Scalar trine -/

noncomputable def trineOutcome (t x y : ℝ) : Fin 3 → ℝ
  | 0 => (t + 2 * x) / 3
  | 1 => (t - x - Real.sqrt 3 * y) / 3
  | 2 => (t - x + Real.sqrt 3 * y) / 3

/-- The three trine outcomes reconstruct the total mass. -/
theorem trineOutcome_sum (t x y : ℝ) :
    ∑ k, trineOutcome t x y k = t := by
  rw [Fin.sum_univ_three]
  simp [trineOutcome]
  ring

/-- The scalar complex coordinate is reconstructed from the trine outcomes in
real coordinates. -/
theorem trineOutcome_reconstruct (t x y : ℝ) :
    x = trineOutcome t x y 0
        - (trineOutcome t x y 1 + trineOutcome t x y 2) / 2
    ∧ Real.sqrt 3 * y =
        3 * (trineOutcome t x y 2 - trineOutcome t x y 1) / 2 := by
  constructor <;> simp [trineOutcome] <;> ring

/-- Exact quadratic trine identity. -/
theorem trineOutcome_square_sum (t x y : ℝ) :
    ∑ k, (trineOutcome t x y k) ^ 2
      = t ^ 2 / 3 + 2 * (x ^ 2 + y ^ 2) / 3 := by
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [Fin.sum_univ_three]
  simp only [trineOutcome]
  nlinarith

/-- `cor:canonical-trine-history`: the displayed quadratic criterion is
equivalent to the scalar disk condition `2|z| ≤ t`. -/
theorem trine_quadratic_criterion {t x y : ℝ} (ht : 0 ≤ t) :
    (∑ k, (trineOutcome t x y k) ^ 2 ≤ t ^ 2 / 2)
      ↔ 4 * (x ^ 2 + y ^ 2) ≤ t ^ 2 := by
  rw [trineOutcome_square_sum]
  constructor <;> intro h <;> nlinarith

/-- `cor:GT-trine-heldout`: every retained analyzer is positive whenever the
isotropic slack dominates the complex amplitude. -/
theorem heldout_analyzer_positive {t x y c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1)
    (hslack : 4 * (x ^ 2 + y ^ 2) ≤ t ^ 2) (ht : 0 ≤ t) :
    0 ≤ t / 2 + (c * x - s * y) := by
  have hdot : (c * x - s * y) ^ 2 ≤ x ^ 2 + y ^ 2 := by
    nlinarith [sq_nonneg (s * x + c * y)]
  nlinarith [sq_nonneg (t / 2 + (c * x - s * y))]

end PositiveCylinderAndTrine
end NCG
