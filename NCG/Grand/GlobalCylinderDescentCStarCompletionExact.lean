/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AFInductiveLimitState
import NCG.Grand.CylinderDescentLimitExact

/-!
# C-star completion of global cylinder descent

This file closes the analytic remainder of
'thm:global-cylinder-descent'.  The finite compression, polar, rank,
stabilization, contextual-annihilator, and source-innovation clauses live in
the three CylinderDescent exact modules.  Here a compatible family of
positive normalized finite-cylinder functionals is descended to the
algebraic direct limit and extended uniquely to its C-star completion.

The converse failure statement is also made literal: failure of compatibility
is witnessed by one pair of finite cutoffs and one finite tester.
-/

open scoped ComplexOrder

noncomputable section

namespace NCG.GlobalCylinderDescent

universe u v

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A : ι → Type v}
variable [∀ i, NormedRing (A i)] [∀ i, StarRing (A i)]
variable [∀ i, CStarRing (A i)] [∀ i, NormedAlgebra ℂ (A i)]
variable [∀ i, StarModule ℂ (A i)]
variable {f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j}
variable [DirectedSystem A (fun i j hij => f i j hij)]
variable [NCG.PreCStarDirectLimit.IsometricSystem f]

/-- **(G7), completed form.**  Compatible finite-cylinder states are the
exact restrictions of a unique state on the AF/quasilocal C-star limit. -/
theorem completedCylinderState_existsUnique
    (omega : NCG.PreCStarDirectLimit.CompatibleState f) :
    ∃! Omega : NCG.PreCStarDirectLimit.Completion f →ₚ[ℂ] ℂ,
      ∀ i (a : A i),
        Omega (NCG.PreCStarDirectLimit.completionOf f i a) = omega.state i a := by
  refine ⟨omega.completionPositiveLinearMap,
    fun i a => omega.completionPositiveLinearMap_of i a, ?_⟩
  intro Omega hOmega
  exact omega.completionPositiveLinearMap_unique Omega hOmega

/-- The GNS representation produced by the completed cylinder state is
contractive in the C-star norm. -/
theorem completedCylinderGNS_contract
    (omega : NCG.PreCStarDirectLimit.CompatibleState f)
    (a : NCG.PreCStarDirectLimit.Completion f) :
    ‖omega.completionGNSRepresentation a‖ ≤ ‖a‖ :=
  omega.norm_completionGNSRepresentation_apply_le a

section AlgebraicConverse

variable {G : ℕ → Type*} [∀ n, AddCommGroup (G n)]
variable [∀ n, Module ℂ (G n)]
variable (g : ∀ i j : ℕ, i ≤ j → G i →ₗ[ℂ] G j)

/-- The algebraic cylinder state exists uniquely before completion. -/
theorem algebraicCylinderState_existsUnique
    (phi : ∀ n, G n →ₗ[ℂ] ℂ)
    (hphi : ∀ i j hij x, phi j (g i j hij x) = phi i x) :
    ∃! Phi : Module.DirectLimit G g →ₗ[ℂ] ℂ,
      ∀ n x, Phi (Module.DirectLimit.of ℂ ℕ G g n x) = phi n x :=
  NCG.CylinderDescentLimit.limit_state_existsUnique g phi hphi

/-- **Converse finite witness.**  If a purported cylinder family is not
compatible, one concrete finite tester at two finite cutoffs witnesses the
failure. -/
theorem incompatibleFiniteFamily_has_tester
    (phi : ∀ n, G n →ₗ[ℂ] ℂ)
    (hphi : ¬ ∀ i j (hij : i ≤ j) (x : G i),
      phi j (g i j hij x) = phi i x) :
    ∃ i j, ∃ hij : i ≤ j, ∃ x : G i,
      phi j (g i j hij x) ≠ phi i x := by
  push_neg at hphi
  exact hphi

/-- Two distinct global algebraic cylinder functionals are separated by a
single finite tester. -/
theorem distinctGlobalStates_have_finite_tester
    {Phi Psi : Module.DirectLimit G g →ₗ[ℂ] ℂ} (hne : Phi ≠ Psi) :
    ∃ n x, Phi (Module.DirectLimit.of ℂ ℕ G g n x) ≠
      Psi (Module.DirectLimit.of ℂ ℕ G g n x) :=
  NCG.CylinderDescentLimit.exists_separating_tester g hne

end AlgebraicConverse

end NCG.GlobalCylinderDescent
