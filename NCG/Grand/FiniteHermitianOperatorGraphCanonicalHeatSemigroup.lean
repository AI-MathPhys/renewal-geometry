/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianOperatorGraphSemigroupFromResolventCore
import NCG.Grand.OperatorGraphResolventEulerFunctionalCalculus

/-!
# Graph-Mosco convergence to the canonical one-resolvent heat semigroup

For a dense nonnegative operator graph, the weak resolvent equations determine every positive
shift from one reference resolvent.  Their actual implicit-Euler powers converge in operator norm
to the canonical heat functional calculus.  This discharges the last limit-side Euler hypothesis
in the finite Hermitian graph-Mosco semigroup compiler.
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

/-- Finite Hermitian graph-Mosco convergence implies uniform positive-time strong convergence to
the canonical heat semigroup constructed from any one positive-shift limit resolvent.  No
separate Euler core, density proof, candidate limit semigroup, or limit Euler formula is needed. -/
theorem
StrongOperatorConvergesUniformlyOn.of_finiteHermitianOperatorGraphMosco_canonicalResolventHeat
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
    (s : Set ℝ) (hs : IsCompact s) (hsPos : ∀ t ∈ s, 0 < t) :
    J.StrongOperatorConvergesUniformlyOn
      (fun n (t : ℝ) ↦ NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := iota n) (𝕜 := ℂ) (G n)))
      (fun t ↦ operatorGraphResolventHeat (R b) b t) s := by
  apply
    StrongOperatorConvergesUniformlyOn.of_finiteHermitianOperatorGraphMosco_resolventRangeEulerCore
      J G hG Dn An D A hD R hmosco hstageEquation hlimitEquation b hb
      (fun t ↦ operatorGraphResolventHeat (R b) b t) s hs hsPos
  intro f t ht
  exact tendsto_scaled_operatorGraphResolvent_succ_pow_apply_heat
    D A R hlimitEquation b t hb (hsPos t ht) (R b f)

end NCG.VaryingHilbert.System
