/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ConnectedResidual
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Parameterized connected residual factorization

This file gives the multivariable Taylor-coefficient form of
`thm:connected-residual-factorization`.  Exact tensor factorization makes the
vacuum-relative residual depend only on the parameter block containing the
source.  Consequently every iterated Fréchet derivative vanishes when any
differentiated direction is supported purely in a disconnected spectator
block.
-/

open Matrix
open scoped Kronecker Norms.L2Operator

namespace NCG

/-- An iterated Fréchet derivative of a function pulled back through the first
projection vanishes whenever one of its directions is purely in the second
factor. -/
theorem iteratedFDeriv_fst_vanishes
    {EA EB V : Type*}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA]
    [NormedAddCommGroup EB] [NormedSpace ℝ EB]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (f : EA → V) (hf : ContDiff ℝ m f)
    (x : EA × EB) (directions : Fin m → EA × EB)
    (j : Fin m) (hj : (directions j).1 = 0) :
    iteratedFDeriv ℝ m (fun z : EA × EB ↦ f z.1) x directions = 0 := by
  let L : EA × EB →L[ℝ] EA := ContinuousLinearMap.fst ℝ EA EB
  have hderiv := L.iteratedFDeriv_comp_right hf x (i := m) le_rfl
  have hfun : (f ∘ L) = fun z : EA × EB ↦ f z.1 := rfl
  rw [← hfun, hderiv]
  exact (iteratedFDeriv ℝ m f (L x)).map_coord_zero j (by
    simpa [L] using hj)

/-- Exact tensor factorization for arbitrary source and spectator parameter
spaces. -/
theorem parameterized_tensor_residual_factorization
    {ThetaA ThetaB dA dB : Type*}
    [Fintype dA] [Fintype dB]
    (G : ThetaA → Matrix dA dA ℂ)
    (H : ThetaB → Matrix dB dB ℂ)
    (X : Matrix dA dA ℂ) (c : ℂ)
    (htr : ∀ thetaB, (H thetaB).trace = c) :
    ∀ thetaA thetaB,
      partialTraceRight ((G thetaA * X) ⊗ₖ H thetaB) =
        c • (G thetaA * X) := by
  have hcollapse : ∀ (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ),
      partialTraceRight (A ⊗ₖ B) = B.trace • A :=
    (renewal_spectator_product LinearMap.id LinearMap.id
      (fun _ ↦ rfl)).1
  intro thetaA thetaB
  rw [hcollapse, htr]

/-- Full multivariable form of `thm:connected-residual-factorization`:
factorization, spectator-parameter independence, and vanishing of every mixed
Taylor coefficient containing a disconnected spectator direction. -/
theorem connected_residual_mixedTaylor_vanishes
    {ThetaA ThetaB dA dB : Type*}
    [NormedAddCommGroup ThetaA] [NormedSpace ℝ ThetaA]
    [NormedAddCommGroup ThetaB] [NormedSpace ℝ ThetaB]
    [Fintype dA] [DecidableEq dA] [Fintype dB]
    (m : ℕ)
    (G : ThetaA → Matrix dA dA ℂ)
    (H : ThetaB → Matrix dB dB ℂ)
    (X : Matrix dA dA ℂ) (c : ℂ)
    (htr : ∀ thetaB, (H thetaB).trace = c)
    (hsmooth : ContDiff ℝ m (fun thetaA ↦ c • (G thetaA * X))) :
    (∀ thetaA thetaB,
      partialTraceRight ((G thetaA * X) ⊗ₖ H thetaB) =
        c • (G thetaA * X)) ∧
    (∀ thetaA thetaB₁ thetaB₂,
      partialTraceRight ((G thetaA * X) ⊗ₖ H thetaB₁) =
        partialTraceRight ((G thetaA * X) ⊗ₖ H thetaB₂)) ∧
    (∀ (base : ThetaA × ThetaB)
      (directions : Fin m → ThetaA × ThetaB)
      (j : Fin m),
      (directions j).1 = 0 →
      iteratedFDeriv ℝ m
        (fun theta : ThetaA × ThetaB ↦
          partialTraceRight ((G theta.1 * X) ⊗ₖ H theta.2))
        base directions = 0) := by
  have hfactor := parameterized_tensor_residual_factorization G H X c htr
  refine ⟨hfactor, ?_, ?_⟩
  · intro thetaA thetaB₁ thetaB₂
    rw [hfactor, hfactor]
  · intro base directions j hj
    have hfun :
        (fun theta : ThetaA × ThetaB ↦
          partialTraceRight ((G theta.1 * X) ⊗ₖ H theta.2)) =
        (fun theta : ThetaA × ThetaB ↦ c • (G theta.1 * X)) := by
      funext theta
      exact hfactor theta.1 theta.2
    rw [hfun]
    exact iteratedFDeriv_fst_vanishes m
      (fun thetaA ↦ c • (G thetaA * X)) hsmooth base directions j hj

end NCG
