/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BoundedOperatorGraphKernel
import NCG.Grand.JointCommutatorResolventFamily
import NCG.Grand.OperatorGraphResolventEigenspace
import NCG.Grand.VaryingHilbertCompressedEigenspace

/-!
# Kernel eigenspace of a compressed joint-commutator resolvent

The reciprocal-shift eigenspace of the common-carrier compression of a finite
joint-commutator resolvent is precisely the embedded finite commutant kernel.
-/

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The distinguished eigenspace of a compressed canonical finite resolver is
the embedded kernel of the finite joint commutator. -/
theorem eigenspace_compressed_jointCommutatorResolventFamily
    {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (b : ℝ) (hb : 0 < b) (cutoff : ℕ) :
    Module.End.eigenspace
        (J.compressedOperator (NCG.jointCommutatorResolventFamily c b)
          cutoff).toLinearMap (((b : ℝ) : ℂ)⁻¹) =
      (LinearMap.ker (NCG.jointCommutatorCLM (c cutoff)).toLinearMap).map
        (J.embedding cutoff).toLinearMap := by
  rw [J.eigenspace_compressedOperator_eq_map
    (NCG.jointCommutatorResolventFamily c b) cutoff (((b : ℝ) : ℂ)⁻¹)
    (inv_ne_zero (by exact_mod_cast hb.ne'))]
  congr 1
  rw [← operatorGraphKernel_top_boundedOperatorGraphMap]
  exact (operatorGraphKernel_eq_resolventEigenspace
    (⊤ : Submodule ℂ (EuclideanSpace ℂ (d cutoff × d cutoff)))
    (boundedOperatorGraphMap (NCG.jointCommutatorCLM (c cutoff)))
    b hb (NCG.jointCommutatorResolventFamily c b cutoff)
    (NCG.jointCommutatorResolventFamily_resolventEquation c b hb cutoff)).symm

end NCG.VaryingHilbert.System
