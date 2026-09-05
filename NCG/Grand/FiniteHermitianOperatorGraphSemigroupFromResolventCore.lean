/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianOperatorGraphSemigroupConvergence
import NCG.Grand.OperatorGraphResolventDenseRange

/-!
# Graph-Mosco semigroup convergence from a resolvent-generated core

The range of any one positive-shift limit resolvent is automatically dense when the limit graph
domain is dense.  It therefore provides a canonical Euler core for the graph-Mosco semigroup
compiler, eliminating a separately chosen core and its density proof.
-/

open Filter Set Topology Matrix
open scoped ComplexOrder ENNReal Norms.L2Operator

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v x z

variable {iota : ℕ → Type u}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [InnerProductSpace ℝ H] [IsScalarTower ℝ ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {F : Type x} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
variable {Fn : ℕ → Type z}
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace ℂ (Fn n)]
  [∀ n, NormedSpace ℝ (Fn n)] [∀ n, IsScalarTower ℝ ℂ (Fn n)]

/-- The range of one positive-shift limit resolvent is a canonical dense Euler core.  Hence a
dense graph domain and the Euler formula only on resolvent-generated vectors suffice for uniform
positive-time semigroup convergence. -/
theorem
StrongOperatorConvergesUniformlyOn.of_finiteHermitianOperatorGraphMosco_resolventRangeEulerCore
    (J : System (K := ℂ) (H := H)
      (Hn := fun n ↦ EuclideanSpace ℂ (iota n)))
    (G : ∀ n, Matrix (iota n) (iota n) ℂ) (hG : ∀ n, (G n).PosSemidef)
    (Dn : ∀ n, Submodule ℂ (EuclideanSpace ℂ (iota n)))
    (An : ∀ n, Dn n →ₗ[ℂ] Fn n)
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] F)
    (hD : Dense (D : Set H))
    (R : ℝ → H →L[ℂ] H)
    (hmosco : J.CofinalMoscoConverges
      (fun n ↦ ennrealOperatorGraphEnergy (Dn n) (An n))
      (ennrealOperatorGraphEnergy D A))
    (hstageEquation : ∀ lam, 0 < lam → ∀ n (f : EuclideanSpace ℂ (iota n)),
      OperatorGraphResolventEquation (Dn n) (An n) lam f
        (NCG.ImplicitEuler.finiteHermitianShiftedResolventOperator (G n) lam f))
    (hlimitEquation : ∀ lam, 0 < lam → ∀ f : H,
      OperatorGraphResolventEquation D A lam f (R lam f))
    (b : ℝ) (hb : 0 < b)
    (S : ℝ → H →L[ℂ] H)
    (s : Set ℝ) (hs : IsCompact s) (hsPos : ∀ t ∈ s, 0 < t)
    (hEulerRange : ∀ f : H, ∀ t ∈ s,
      Tendsto
        (fun m ↦
          (((((((m + 1 : ℕ) : ℝ) / t : ℝ) : ℂ)) •
            R (((m + 1 : ℕ) : ℝ) / t)) ^ (m + 1)) (R b f))
        atTop (𝓝 (S t (R b f)))) :
    J.StrongOperatorConvergesUniformlyOn
      (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := iota n) (𝕜 := ℂ) (G n))) S s := by
  have hdenseRange : DenseRange (R b) :=
    operatorGraphResolvent_denseRange D A b (R b) hD
      (hlimitEquation b hb)
  apply
    StrongOperatorConvergesUniformlyOn.of_finiteHermitianOperatorGraphMosco_denseEulerCore
      J G hG Dn An D A R hmosco hstageEquation hlimitEquation S s hs hsPos
      (Set.range (R b))
  · exact hdenseRange
  · intro d hd t ht
    obtain ⟨f, rfl⟩ := hd
    exact hEulerRange f t ht

end NCG.VaryingHilbert.System
