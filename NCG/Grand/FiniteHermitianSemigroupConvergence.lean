/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianHeatSemigroup
import NCG.Grand.CompactEquicontinuousUniformConvergence

/-!
# Varying-cutoff convergence of finite Hermitian semigroups

This file compiles convergence of fixed one-step Euler resolvents into uniform strong convergence
of the literal finite exponential semigroups.  The cutoff approximation is automatic and
dimension free; the only limit-side input left visible is convergence of the limit Euler scheme.
-/

open Filter Topology Matrix
open scoped ComplexOrder Norms.L2Operator

noncomputable section

namespace NCG.ImplicitEuler

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The one-step Euler resolvent, indexed so that stage `m` uses order `m + 1`. -/
def finiteHermitianEulerRootOperator (A : Matrix ι ι ℂ) (t : ℝ) (m : ℕ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
    (((1 : Matrix ι ι ℂ) +
      (((t / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) • A))⁻¹)

/-- The previously defined literal Euler operator is exactly the corresponding root power. -/
theorem finiteHermitianEulerResolventOperator_succ_eq_root_pow
    (A : Matrix ι ι ℂ) (t : ℝ) (m : ℕ) :
    finiteHermitianEulerResolventOperator A t (m + 1) =
      finiteHermitianEulerRootOperator A t m ^ (m + 1) := by
  unfold finiteHermitianEulerResolventOperator finiteHermitianEulerRootOperator
  exact map_pow (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) _ (m + 1)

end NCG.ImplicitEuler

namespace NCG.VaryingHilbert.System

universe u v

variable {ι : ℕ → Type u}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Fixed-order convergence of the one-step cutoff Euler resolvents, convergence of the
limit-space Euler scheme, and time equicontinuity imply uniform strong convergence of the literal
finite exponential semigroups.

The dimension-free cutoff approximation is discharged internally by the finite Hermitian spectral
calculus. -/
theorem StrongOperatorConvergesUniformlyOn.of_finiteHermitianEulerRoots
    (J : System (K := ℂ) (H := H) (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (A : ∀ n, Matrix (ι n) (ι n) ℂ) (hA : ∀ n, (A n).PosSemidef)
    (S : ℝ → H →L[ℂ] H)
    (R : ℕ → ℝ → H →L[ℂ] H) (s : Set ℝ)
    (hs : IsCompact s) (hsNonneg : ∀ t ∈ s, 0 ≤ t)
    (hR : ∀ m, ∀ t ∈ s,
      J.StrongOperatorConverges J
        (fun n ↦ NCG.ImplicitEuler.finiteHermitianEulerRootOperator (A n) t m)
        (R m t))
    (hfixedEq : ∀ m, ∀ (x : ∀ n, EuclideanSpace ℂ (ι n)) (xlim : H),
      J.StronglyConverges x xlim →
        EquicontinuousOn
          (fun n t ↦ J.embedding n
            (NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
              (A n) t (m + 1) (x n))) s)
    (hEulerLimit : ∀ x : H,
      TendstoUniformlyOn
        (fun m t ↦ (R m t ^ (m + 1)) x)
        (fun t ↦ S t x) atTop s) :
    J.StrongOperatorConvergesUniformlyOn
      (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (A n))) S s := by
  apply StrongOperatorConvergesUniformlyOn.of_approximants J
    (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
      Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (A n))) S
    (fun m n (t : ℝ) ↦ NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
      (A n) t (m + 1))
    (fun m (t : ℝ) ↦ R m t ^ (m + 1)) s
  · intro m
    apply StrongOperatorConvergesUniformlyOn.of_compact_of_equicontinuousOn
      J _ _ s hs
    · intro t ht
      simpa only [
        NCG.ImplicitEuler.finiteHermitianEulerResolventOperator_succ_eq_root_pow] using
        NCG.VaryingHilbert.StrongOperatorConverges.pow J (hR m t ht) (m + 1)
    · exact hfixedEq m
  · exact hEulerLimit
  · intro x xlim hx
    exact eventually_uniform_finiteHermitianEuler_exp_apply_dist
      J A hA s hsNonneg x xlim hx


/-- Fixed-time version of the finite Hermitian Euler-root compiler.  No time-equicontinuity
hypothesis is needed. -/
theorem StrongOperatorConverges.of_finiteHermitianEulerRoots
    (J : System (K := ℂ) (H := H) (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (A : ∀ n, Matrix (ι n) (ι n) ℂ) (hA : ∀ n, (A n).PosSemidef)
    (t : ℝ) (ht : 0 ≤ t) (S : H →L[ℂ] H) (R : ℕ → H →L[ℂ] H)
    (hR : ∀ m, J.StrongOperatorConverges J
      (fun n ↦ NCG.ImplicitEuler.finiteHermitianEulerRootOperator (A n) t m)
      (R m))
    (hEulerLimit : ∀ x : H,
      Tendsto (fun m ↦ (R m ^ (m + 1)) x) atTop (𝓝 (S x))) :
    J.StrongOperatorConverges J
      (fun n ↦ NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (A n))) S := by
  apply StrongOperatorConverges.of_approximants J
    (fun n ↦ NormedSpace.exp ((-(t : ℂ)) •
      Matrix.toEuclideanCLM (n := ι n) (𝕜 := ℂ) (A n))) S
    (fun m n ↦ NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
      (A n) t (m + 1))
    (fun m ↦ R m ^ (m + 1))
  · intro m
    simpa only [
      NCG.ImplicitEuler.finiteHermitianEulerResolventOperator_succ_eq_root_pow] using
      NCG.VaryingHilbert.StrongOperatorConverges.pow J (hR m) (m + 1)
  · exact hEulerLimit
  · intro x xlim hx
    have happ := eventually_uniform_finiteHermitianEuler_exp_apply_dist
      J A hA ({t} : Set ℝ) (by simpa using ht) x xlim hx
    intro ε hε
    have h := happ ε hε
    simpa only [Set.mem_singleton_iff, forall_eq] using h
end NCG.VaryingHilbert.System
