/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianSemigroupLaplaceResolvent
import NCG.Grand.FiniteHermitianSemigroupEndpoint
import NCG.Grand.VaryingHilbertSemigroupLaplaceConvergence

/-!
# Strong resolvent convergence from finite Hermitian semigroups

Compact-uniform positive-time convergence of finite Hermitian contraction
semigroups implies strong convergence of their resolvents whenever the limit
semigroup has the expected Laplace transform.  This is the reverse
semigroup-to-resolvent direction used in the Grand-Tensor Mosco equivalence.
-/

open Filter Matrix MeasureTheory Set Topology
open scoped ComplexOrder Norms.L2Operator

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {iota : ℕ → Type u}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H] [CompleteSpace H]

/-- Uniform positive-time convergence of finite Hermitian heat semigroups
passes to strong resolvent convergence through the Laplace representation of
the candidate limit family. -/
theorem StrongOperatorConverges.of_finiteHermitianSemigroups
    (J : System (K := ℂ) (H := H)
      (Hn := fun n ↦ EuclideanSpace ℂ (iota n)))
    (G : ∀ n, Matrix (iota n) (iota n) ℂ)
    (hG : ∀ n, (G n).PosSemidef)
    (S : ℝ → H →L[ℂ] H)
    (R : ℝ → H →L[ℂ] H)
    (hsemigroup : ∀ s : Set ℝ, IsCompact s → (∀ t ∈ s, 0 < t) →
      J.StrongOperatorConvergesUniformlyOn
        (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
          Matrix.toEuclideanCLM (n := iota n) (𝕜 := ℂ) (G n)))
        S s)
    (hlimitLaplace : ∀ lam, 0 < lam → ∀ x : H,
      (∫ t : ℝ in Ioi 0,
          ((Real.exp (-lam * t) : ℝ) : ℂ) • S t x) =
        R lam x) :
    ∀ lam, 0 < lam →
      J.StrongOperatorConverges J
        (fun n ↦ NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
          (G n) lam)
        (R lam) := by
  intro lam hlam x xlim hx
  let Sn : ∀ n, ℝ →
      EuclideanSpace ℂ (iota n) →L[ℂ] EuclideanSpace ℂ (iota n) :=
    fun n t ↦ NormedSpace.exp ((-(t : ℂ)) •
      Matrix.toEuclideanCLM (n := iota n) (𝕜 := ℂ) (G n))
  have hcontinuous : ∀ n (y : EuclideanSpace ℂ (iota n)),
      Continuous (fun t ↦ Sn n t y) := by
    intro n y
    exact NCG.ImplicitEuler.continuous_finiteHermitian_exp_neg_apply
      (G n) y
  have hlaplace :=
    StrongOperatorConvergesUniformlyOn.tendsto_laplace_integrals
      J Sn S hsemigroup hcontinuous
      (fun n t ht ↦
        NCG.ImplicitEuler.norm_finiteHermitian_exp_neg_le_one
          (G n) (hG n) t ht)
      x xlim hx lam hlam
  have hstageIntegral : ∀ n,
      (∫ t : ℝ in Ioi 0,
          ((Real.exp (-lam * t) : ℝ) : ℂ) •
            J.embedding n (Sn n t (x n))) =
        J.embedding n
          (NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
            (G n) lam (x n)) := by
    intro n
    have hint :=
      NCG.ImplicitEuler.integrableOn_weighted_finiteHermitianHeat_apply
        (G n) (hG n) lam hlam (x n)
    have hcomm :=
      (J.embedding n).toContinuousLinearMap.integral_comp_comm hint
    rw [NCG.ImplicitEuler.integral_weighted_finiteHermitianHeat_apply_eq_shiftedResolvent
      (G n) (hG n) lam hlam (x n)] at hcomm
    simpa [Sn] using hcomm
  change Tendsto
    (fun n ↦ J.embedding n
      (NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator
        (G n) lam (x n)))
    atTop (𝓝 (R lam xlim))
  convert hlaplace using 1
  · funext n
    exact (hstageIntegral n).symm
  · exact congrArg 𝓝 (hlimitLaplace lam hlam xlim).symm

end NCG.VaryingHilbert.System
