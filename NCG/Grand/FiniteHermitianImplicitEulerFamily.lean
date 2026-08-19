/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianImplicitEulerResolvent
import NCG.Grand.UniformEulerApproximationFromOperatorNorm

/-!
# Cutoff-family implicit-Euler approximation for finite Hermitian generators

This file bundles the finite matrix estimate as continuous operators on Euclidean spaces and then
feeds its explicit dimension-free rate into the varying-Hilbert operator-norm compiler.  The
matrix size may vary arbitrarily with the cutoff.
-/

open Filter Topology Matrix
open scoped ComplexOrder Norms.L2Operator

noncomputable section

namespace NCG.ImplicitEuler

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The finite Hermitian heat multiplier as a continuous operator on Euclidean space. -/
def finiteHermitianHeatOperator {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (t : ℝ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (finiteHermitianHeat hA t)

/-- The literal finite implicit-Euler resolvent power as a continuous Euclidean operator. -/
def finiteHermitianEulerResolventOperator (A : Matrix ι ι ℂ) (t : ℝ) (k : ℕ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
    (((1 : Matrix ι ι ℂ) + (((t / (k : ℝ) : ℝ) : ℂ) • A))⁻¹ ^ k)

/-- The dimension-free matrix estimate, bundled as a continuous-operator norm bound. -/
theorem norm_finiteHermitianEulerResolventOperator_sub_heat_le_inv_sqrt
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (t : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hk : 0 < k) :
    ‖finiteHermitianEulerResolventOperator A t k -
        finiteHermitianHeatOperator hA.1 t‖ ≤ (Real.sqrt (k : ℝ))⁻¹ := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
      (((1 : Matrix ι ι ℂ) + (((t / (k : ℝ) : ℝ) : ℂ) • A))⁻¹ ^ k) -
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (finiteHermitianHeat hA.1 t)‖ ≤ _
  rw [← map_sub]
  change ‖((1 : Matrix ι ι ℂ) + (((t / (k : ℝ) : ℝ) : ℂ) • A))⁻¹ ^ k -
      finiteHermitianHeat hA.1 t‖ ≤ _
  exact norm_inv_one_add_smul_pow_sub_finiteHermitianHeat_le_inv_sqrt hA t k ht hk

/-- Zero-indexed continuous-operator estimate with the convergence-ready error rate. -/
theorem norm_finiteHermitianEulerResolventOperator_succ_sub_heat_le_errorRate
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (t : ℝ) (m : ℕ) (ht : 0 ≤ t) :
    ‖finiteHermitianEulerResolventOperator A t (m + 1) -
        finiteHermitianHeatOperator hA.1 t‖ ≤ errorRate m := by
  simpa only [errorRate, Nat.cast_add, Nat.cast_one] using
    norm_finiteHermitianEulerResolventOperator_sub_heat_le_inv_sqrt
      hA t (m + 1) ht (Nat.succ_pos m)

end NCG.ImplicitEuler

namespace NCG.VaryingHilbert.System

universe u v

variable {ι : ℕ → Type u}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Across an arbitrary family of finite cutoffs, the literal Euler powers approximate the
canonical spectral heat operators uniformly on every set of nonnegative times, with a rate that
does not depend on the cutoff dimension or spectral radius. -/
theorem eventually_uniform_finiteHermitianEuler_operatorNorm_error
    (A : ∀ n, Matrix (ι n) (ι n) ℂ) (hA : ∀ n, (A n).PosSemidef)
    (s : Set ℝ) (hs : ∀ t ∈ s, 0 ≤ t) :
    ∀ m, ∀ᶠ n in atTop, ∀ t ∈ s,
      ‖NCG.ImplicitEuler.finiteHermitianHeatOperator (hA n).1 t -
          NCG.ImplicitEuler.finiteHermitianEulerResolventOperator (A n) t (m + 1)‖ ≤
        NCG.ImplicitEuler.errorRate m := by
  intro m
  filter_upwards [] with n
  intro t ht
  rw [norm_sub_rev]
  exact NCG.ImplicitEuler.norm_finiteHermitianEulerResolventOperator_succ_sub_heat_le_errorRate
    (hA n) t m (hs t ht)

/-- The explicit finite Hermitian estimate supplies the vectorwise approximation premise required
by the varying-Hilbert Euler/semigroup convergence machinery. -/
theorem eventually_uniform_finiteHermitianEuler_apply_dist
    (J : System (K := ℂ) (H := H) (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (A : ∀ n, Matrix (ι n) (ι n) ℂ) (hA : ∀ n, (A n).PosSemidef)
    (s : Set ℝ) (hs : ∀ t ∈ s, 0 ≤ t)
    (x : ∀ n, EuclideanSpace ℂ (ι n)) (xlim : H)
    (hx : J.StronglyConverges x xlim) :
    ∀ ε > 0, ∀ᶠ m in atTop, ∀ᶠ n in atTop, ∀ t ∈ s,
      dist
        (J.embedding n
          (NCG.ImplicitEuler.finiteHermitianHeatOperator (hA n).1 t (x n)))
        (J.embedding n
          (NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
            (A n) t (m + 1) (x n))) < ε := by
  exact eventually_uniform_apply_dist_of_operatorNorm_error J
    (fun n t ↦ NCG.ImplicitEuler.finiteHermitianHeatOperator (hA n).1 t)
    (fun m n t ↦ NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
      (A n) t (m + 1))
    NCG.ImplicitEuler.errorRate s
    NCG.ImplicitEuler.errorRate_tendsto_zero
    NCG.ImplicitEuler.errorRate_nonneg
    (eventually_uniform_finiteHermitianEuler_operatorNorm_error A hA s hs)
    x xlim hx

end NCG.VaryingHilbert.System
