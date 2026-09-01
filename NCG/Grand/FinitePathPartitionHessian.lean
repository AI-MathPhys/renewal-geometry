/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ScorePressureMatrixPolarization
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Finite path-partition Hessians

This file supplies the finite protected-screen content of
`thm:SMFS-full-Hessian`.  A twice-written log weight is represented by its
value, first writers, and symmetric direct second writers.  On every parameter
line the second derivative of the log partition is exactly the expectation of
the direct writer plus the covariance of the first writers.  The covariance
matrix is a Gram matrix and hence positive semidefinite; no sign is imposed on
the direct block.

The last lemmas record the uniform finite-moment estimate used on a protected
screen: a writer bounded by `M` has every natural moment bounded by `M ^ p`,
uniformly over every member of a family of probability laws.
-/

open Finset Matrix

namespace NCG
namespace FinitePathPartitionHessian

variable {I Ω : Type*} [Fintype I] [DecidableEq I]
  [Fintype Ω] [Nonempty Ω]

/-- The exact quadratic log-weight chart determined by its value, first
writers, and direct second writers. -/
noncomputable def logWeightChart (c : Ω → ℝ) (a : I → Ω → ℝ)
    (b : I → I → Ω → ℝ) (θ : I → ℝ) (ω : Ω) : ℝ :=
  c ω + ∑ i, θ i * a i ω +
    (2 : ℝ)⁻¹ * ∑ i, ∑ j, θ i * θ j * b i j ω

/-- The first writer along the line `θ = t x`. -/
def lineFirstWriter (a : I → Ω → ℝ) (b : I → I → Ω → ℝ)
    (x : I → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (∑ i, x i * a i ω) + t * ∑ i, ∑ j, x i * x j * b i j ω

/-- The direct second writer along the line `θ = t x`. -/
def lineSecondWriter (b : I → I → Ω → ℝ)
    (x : I → ℝ) (_t : ℝ) (ω : Ω) : ℝ :=
  ∑ i, ∑ j, x i * x j * b i j ω

/-- The same chart restricted to one parameter line, written in collected
scalar-polynomial form. -/
noncomputable def lineLogWeight (c : Ω → ℝ) (a : I → Ω → ℝ)
    (b : I → I → Ω → ℝ) (x : I → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  c ω + t * (∑ i, x i * a i ω) +
    (2 : ℝ)⁻¹ * t ^ 2 * (∑ i, ∑ j, x i * x j * b i j ω)

theorem hasDerivAt_lineLogWeight
    (c : Ω → ℝ) (a : I → Ω → ℝ) (b : I → I → Ω → ℝ)
    (x : I → ℝ) (ω : Ω) (t : ℝ) :
    HasDerivAt (fun s : ℝ => lineLogWeight c a b x s ω)
      (lineFirstWriter a b x t ω) t := by
  let A : ℝ := ∑ i, x i * a i ω
  let B : ℝ := ∑ i, ∑ j, x i * x j * b i j ω
  have h := ((hasDerivAt_const (x := t) (c ω)).add
    ((hasDerivAt_id t).mul_const A)).add
    ((hasDerivAt_pow 2 t).mul_const ((2 : ℝ)⁻¹ * B))
  let f : ℝ → ℝ := ((fun _ => c ω) + fun s => s * A) +
    fun s => s ^ 2 * ((2 : ℝ)⁻¹ * B)
  have hf : (fun s : ℝ => lineLogWeight c a b x s ω) = f := by
    funext s
    simp only [lineLogWeight, f, Pi.add_apply]
    dsimp only [A, B]
    ring
  have hd : 0 + 1 * A + (2 : ℝ) * t ^ (2 - 1) * ((2 : ℝ)⁻¹ * B) =
      A + t * B := by
    norm_num
    ring
  rw [hf]
  change HasDerivAt f (A + t * B) t
  rw [← hd]
  exact h

theorem hasDerivAt_lineFirstWriter
    (a : I → Ω → ℝ) (b : I → I → Ω → ℝ)
    (x : I → ℝ) (ω : Ω) (t : ℝ) :
    HasDerivAt (fun s : ℝ => lineFirstWriter a b x s ω)
      (lineSecondWriter b x t ω) t := by
  let A : ℝ := ∑ i, x i * a i ω
  let B : ℝ := ∑ i, ∑ j, x i * x j * b i j ω
  have h := (hasDerivAt_const (x := t) A).add
    ((hasDerivAt_id t).mul_const B)
  let f : ℝ → ℝ := (fun _ => A) + fun s => s * B
  have hf : (fun s : ℝ => lineFirstWriter a b x s ω) = f := by
    funext s
    simp only [lineFirstWriter, f, Pi.add_apply]
    rfl
  have hd : 0 + 1 * B = B := by ring
  rw [hf]
  change HasDerivAt f B t
  rw [← hd]
  exact h

/-- Exact first and second log-partition derivatives in every parameter
direction.  This is the directional form of (FS.34), with no differentiation
under an infinite integral left as an interface. -/
theorem logPartition_line_hessian
    (c : Ω → ℝ) (a : I → Ω → ℝ) (b : I → I → Ω → ℝ)
    (x : I → ℝ) (t : ℝ) :
    let φ := lineLogWeight c a b x
    HasDerivAt (fun s => Real.log (ScorePressure.partition φ s))
        (ScorePressure.expect φ t (lineFirstWriter a b x t)) t ∧
      HasDerivAt
        (fun s => ScorePressure.expect φ s (lineFirstWriter a b x s))
        (ScorePressure.expect φ t (lineSecondWriter b x t) +
          ScorePressure.variance φ t (lineFirstWriter a b x t)) t := by
  dsimp only
  exact ScorePressure.log_partition_derivatives
    (lineLogWeight c a b x)
    (lineFirstWriter a b x) (lineSecondWriter b x)
    (fun ω t => hasDerivAt_lineLogWeight c a b x ω t)
    (fun ω t => hasDerivAt_lineFirstWriter a b x ω t) t

/-- At the base point, the normalized finite path law. -/
noncomputable def baseLaw (c : Ω → ℝ) : Ω → ℝ :=
  ScorePressure.law (fun _ ω => c ω) 0

theorem baseLaw_nonneg (c : Ω → ℝ) (ω : Ω) : 0 ≤ baseLaw c ω :=
  ScorePressure.law_nonneg _ _ _

theorem baseLaw_sum (c : Ω → ℝ) : ∑ ω, baseLaw c ω = 1 :=
  ScorePressure.law_sum _ _

/-- The exact matrix occurring in the partition Hessian. -/
noncomputable def partitionHessian (c : Ω → ℝ) (a : I → Ω → ℝ)
    (b : I → I → Ω → ℝ) : Matrix I I ℝ :=
  fun i j => (∑ ω, baseLaw c ω * b i j ω) +
    ScorePressure.scoreCovarianceMatrix (baseLaw c) a i j

/-- The covariance block in (FS.34) is positive semidefinite because it is
literally the Gram matrix of the square-root-weighted centered writers. -/
theorem covarianceBlock_posSemidef (c : Ω → ℝ) (a : I → Ω → ℝ) :
    (ScorePressure.scoreCovarianceMatrix (baseLaw c) a).PosSemidef :=
  ScorePressure.scoreCovarianceMatrix_posSemidef
    (baseLaw c) (baseLaw_nonneg c) a

/-- The direct block is genuinely independent: even a one-point finite path
space realizes an arbitrary scalar sign while the covariance block vanishes. -/
theorem directBlock_has_either_sign :
    let c : Fin 1 → ℝ := fun _ => 0
    let a : Fin 1 → Fin 1 → ℝ := fun _ _ => 0
    let bPos : Fin 1 → Fin 1 → Fin 1 → ℝ := fun _ _ _ => 1
    let bNeg : Fin 1 → Fin 1 → Fin 1 → ℝ := fun _ _ _ => -1
    partitionHessian c a bPos 0 0 = 1 ∧
      partitionHessian c a bNeg 0 0 = -1 := by
  norm_num [partitionHessian, baseLaw, ScorePressure.law,
    ScorePressure.partition, ScorePressure.scoreCovarianceMatrix,
    ScorePressure.centeredCoordinate]

/-- A finite probability law and a uniform pointwise writer bound give every
natural moment with the same regulator-independent bound. -/
theorem finiteMoment_le_pow
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1)
    (f : Ω → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ ω, |f ω| ≤ M)
    (r : ℕ) :
    ∑ ω, p ω * |f ω| ^ r ≤ M ^ r := by
  calc
    ∑ ω, p ω * |f ω| ^ r ≤ ∑ ω, p ω * M ^ r := by
      refine Finset.sum_le_sum fun ω _ => ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hf ω) r) (hp ω)
    _ = (∑ ω, p ω) * M ^ r := by rw [Finset.sum_mul]
    _ = M ^ r := by rw [hsum, one_mul]

/-- Uniform protected-screen version of the preceding moment estimate. -/
theorem uniform_finiteMoments
    {N : Type*} (p : N → Ω → ℝ)
    (hp : ∀ n ω, 0 ≤ p n ω) (hsum : ∀ n, ∑ ω, p n ω = 1)
    (f : N → Ω → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ n ω, |f n ω| ≤ M) (r : ℕ) :
    ∀ n, ∑ ω, p n ω * |f n ω| ^ r ≤ M ^ r := by
  intro n
  exact finiteMoment_le_pow (p n) (hp n) (hsum n) (f n) M hM (hf n) r

/-- Every raw count moment of a Poisson law is summable.  This is the
integrability input for finite-time jump writers: polynomial count growth is
dominated by an exponential tilt, whose Poisson series is again an exponential
series. -/
theorem poisson_raw_moments_summable (lam : NNReal) (r : ℕ) :
    Summable fun n : ℕ =>
      (n : ℝ) ^ r * ProbabilityTheory.poissonPMFReal lam n := by
  let C : ℝ := Real.exp (-(lam : ℝ)) * (r.factorial : ℝ)
  let q : ℝ := Real.exp 1 * (lam : ℝ)
  have hs : Summable fun n : ℕ => C * (q ^ n / (n.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial q).mul_left C
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg (Nat.cast_nonneg n) r)
      ProbabilityTheory.poissonPMFReal_nonneg) _ hs
  intro n
  have hfac : (0 : ℝ) < (r.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos r
  have hpoly := Real.pow_div_factorial_le_exp
    (x := (n : ℝ)) (Nat.cast_nonneg n) r
  rw [div_le_iff₀ hfac] at hpoly
  calc
    (n : ℝ) ^ r * ProbabilityTheory.poissonPMFReal lam n
        ≤ ((r.factorial : ℝ) * Real.exp (n : ℝ)) *
            ProbabilityTheory.poissonPMFReal lam n := by
          exact mul_le_mul_of_nonneg_right
            (by simpa [mul_comm] using hpoly)
            ProbabilityTheory.poissonPMFReal_nonneg
    _ = C * (q ^ n / (n.factorial : ℝ)) := by
      rw [ProbabilityTheory.poissonPMFReal]
      simp only [C, q, NNReal.coe_pow, mul_pow]
      rw [show Real.exp (n : ℝ) = (Real.exp 1) ^ n by
        rw [show (n : ℝ) = (n : ℝ) * 1 by ring, Real.exp_nat_mul]]
      ring

/-- Pointwise exponential-series dominator for a compensated Poisson count. -/
theorem poisson_compensated_moment_le (lam : NNReal) (r n : ℕ) :
    |(n : ℝ) - (lam : ℝ)| ^ r *
        ProbabilityTheory.poissonPMFReal lam n ≤
      (r.factorial : ℝ) *
        ((Real.exp 1 * (lam : ℝ)) ^ n / (n.factorial : ℝ)) := by
  have hsum0 : 0 ≤ (n : ℝ) + (lam : ℝ) := by positivity
  have habs : |(n : ℝ) - (lam : ℝ)| ≤ (n : ℝ) + (lam : ℝ) := by
    calc
      |(n : ℝ) - (lam : ℝ)| ≤ |(n : ℝ)| + |(lam : ℝ)| := abs_sub _ _
      _ = (n : ℝ) + (lam : ℝ) := by
        rw [abs_of_nonneg (Nat.cast_nonneg n), abs_of_nonneg lam.coe_nonneg]
  have hpow : |(n : ℝ) - (lam : ℝ)| ^ r ≤
      ((n : ℝ) + (lam : ℝ)) ^ r :=
    pow_le_pow_left₀ (abs_nonneg _) habs r
  have hfac : (0 : ℝ) < (r.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos r
  have hpoly := Real.pow_div_factorial_le_exp
    (x := (n : ℝ) + (lam : ℝ)) hsum0 r
  rw [div_le_iff₀ hfac] at hpoly
  have hgrowth : |(n : ℝ) - (lam : ℝ)| ^ r ≤
      (r.factorial : ℝ) * Real.exp ((n : ℝ) + (lam : ℝ)) := by
    exact hpow.trans (by simpa [mul_comm] using hpoly)
  calc
    |(n : ℝ) - (lam : ℝ)| ^ r *
        ProbabilityTheory.poissonPMFReal lam n
        ≤ ((r.factorial : ℝ) * Real.exp ((n : ℝ) + (lam : ℝ))) *
            ProbabilityTheory.poissonPMFReal lam n := by
          exact mul_le_mul_of_nonneg_right hgrowth
            ProbabilityTheory.poissonPMFReal_nonneg
    _ = (r.factorial : ℝ) *
        ((Real.exp 1 * (lam : ℝ)) ^ n / (n.factorial : ℝ)) := by
      rw [ProbabilityTheory.poissonPMFReal, Real.exp_add]
      simp only [mul_pow]
      rw [show Real.exp (n : ℝ) = (Real.exp 1) ^ n by
        rw [show (n : ℝ) = (n : ℝ) * 1 by ring, Real.exp_nat_mul]]
      have hc : Real.exp (lam : ℝ) * Real.exp (-(lam : ℝ)) = 1 := by
        rw [← Real.exp_add]
        simp
      calc
        _ = (Real.exp (lam : ℝ) * Real.exp (-(lam : ℝ))) *
            ((r.factorial : ℝ) * (Real.exp 1) ^ n * (lam : ℝ) ^ n /
              (n.factorial : ℝ)) := by ring
        _ = _ := by rw [hc, one_mul]; ring

/-- Compensated Poisson counts have moments of every natural order. -/
theorem poisson_compensated_moments_summable (lam : NNReal) (r : ℕ) :
    Summable fun n : ℕ =>
      |(n : ℝ) - (lam : ℝ)| ^ r *
        ProbabilityTheory.poissonPMFReal lam n := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg (abs_nonneg _) r)
      ProbabilityTheory.poissonPMFReal_nonneg)
    (fun n => poisson_compensated_moment_le lam r n)
  exact (Real.summable_pow_div_factorial
    (Real.exp 1 * (lam : ℝ))).mul_left (r.factorial : ℝ)

/-- A uniform intensity ceiling gives one common summable dominator for all
compensated-count moments.  Consequently all fixed-order jump-writer moments
are bounded uniformly over a protected cutoff family. -/
theorem poisson_compensated_moments_uniform_dominator
    (L : NNReal) (r : ℕ) :
    Summable (fun n : ℕ => (r.factorial : ℝ) *
        ((Real.exp 1 * (L : ℝ)) ^ n / (n.factorial : ℝ))) ∧
      ∀ lam : NNReal, lam ≤ L → ∀ n : ℕ,
        |(n : ℝ) - (lam : ℝ)| ^ r *
            ProbabilityTheory.poissonPMFReal lam n ≤
          (r.factorial : ℝ) *
            ((Real.exp 1 * (L : ℝ)) ^ n / (n.factorial : ℝ)) := by
  constructor
  · exact (Real.summable_pow_div_factorial
      (Real.exp 1 * (L : ℝ))).mul_left (r.factorial : ℝ)
  · intro lam hlam n
    refine (poisson_compensated_moment_le lam r n).trans ?_
    have hbase : Real.exp 1 * (lam : ℝ) ≤ Real.exp 1 * (L : ℝ) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlam) (Real.exp_pos 1).le
    have hpow := pow_le_pow_left₀ (by positivity) hbase n
    have hfac : 0 ≤ (r.factorial : ℝ) := by positivity
    have hden : 0 ≤ (n.factorial : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hpow hden) hfac

/-- Bundle for the finite protected-screen content of
`thm:SMFS-full-Hessian`: exact Hessian, positive covariance, independent
direct block, and uniform moments of all natural orders. -/
theorem finite_path_partition_full_hessian
    (c : Ω → ℝ) (a : I → Ω → ℝ) (b : I → I → Ω → ℝ)
    (hb : ∀ i j ω, b j i ω = b i j ω) :
    (partitionHessian c a b)ᵀ = partitionHessian c a b ∧
      (ScorePressure.scoreCovarianceMatrix (baseLaw c) a).PosSemidef ∧
      (∀ x : I → ℝ,
        let φ := lineLogWeight c a b x
        HasDerivAt
          (fun s => ScorePressure.expect φ s (lineFirstWriter a b x s))
          (ScorePressure.expect φ 0 (lineSecondWriter b x 0) +
            ScorePressure.variance φ 0 (lineFirstWriter a b x 0)) 0) := by
  refine ⟨?_, covarianceBlock_posSemidef c a, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, partitionHessian]
    congr 1
    · apply Finset.sum_congr rfl
      intro ω _
      rw [hb i j ω]
    · have h := congrFun (congrFun
        (ScorePressure.scoreCovarianceMatrix_symmetric (baseLaw c) a) i) j
      simpa only [Matrix.transpose_apply] using h
  · intro x
    exact (logPartition_line_hessian c a b x 0).2

end FinitePathPartitionHessian
end NCG
