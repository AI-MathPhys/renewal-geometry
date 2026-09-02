/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorContinuousOperator

/-!
# Embedded joint-commutator kernels are the screened commutants

The continuum Howe compilers transport finite Hilbert--Schmidt kernels into a
common Hilbert carrier.  This file records the generator-identification bridge:
an embedded matrix belongs to the transported kernel exactly when it commutes
with every member of the screened generating tuple.  Isometry of the stage
embedding prevents the transport from introducing spurious kernel vectors.
-/

open Filter

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {d : ℕ → Type u} [∀ cutoff, Fintype (d cutoff)] {s : ℕ}

/-- The transported kernel of the finite joint commutator is exactly the
transported matrix commutant. -/
theorem embeddedMatrix_mem_mappedJointCommutatorKernel_iff
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : NCG.VaryingHilbert.System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (cutoff : ℕ) (X : Matrix (d cutoff) (d cutoff) ℂ) :
    J.embedding cutoff (NCG.matrixL2 X) ∈
        (LinearMap.ker (NCG.jointCommutatorCLM (c cutoff)).toLinearMap).map
          (J.embedding cutoff).toLinearMap ↔
      ∀ j, c cutoff j * X = X * c cutoff j := by
  constructor
  · rintro ⟨y, hy, hembed⟩
    have hyX : y = NCG.matrixL2 X :=
      (J.embedding cutoff).injective hembed
    apply (NCG.matrixL2_mem_jointCommutatorCLM_ker_iff (c cutoff) X).mp
    simpa [hyX] using hy
  · intro hcomm
    refine ⟨NCG.matrixL2 X,
      (NCG.matrixL2_mem_jointCommutatorCLM_ker_iff (c cutoff) X).mpr hcomm, rfl⟩

/-- Once protected ranges lock to the transported joint-commutator kernels,
membership in the protected multiplicity space is exactly simultaneous
commutation with the screened generators. -/
theorem eventually_embeddedMatrix_mem_protectedRange_iff_commutes
    (c : ∀ cutoff, Fin s → Matrix (d cutoff) (d cutoff) ℂ)
    (J : NCG.VaryingHilbert.System (K := ℂ) (H := H)
      (Hn := fun cutoff ↦ EuclideanSpace ℂ (d cutoff × d cutoff)))
    (P : ℕ → H →L[ℂ] H)
    (hkernel : ∀ᶠ cutoff in atTop,
      LinearMap.range (P cutoff).toLinearMap =
        (LinearMap.ker (NCG.jointCommutatorCLM (c cutoff)).toLinearMap).map
          (J.embedding cutoff).toLinearMap) :
    ∀ᶠ cutoff in atTop, ∀ X : Matrix (d cutoff) (d cutoff) ℂ,
      J.embedding cutoff (NCG.matrixL2 X) ∈
          LinearMap.range (P cutoff).toLinearMap ↔
        ∀ j, c cutoff j * X = X * c cutoff j := by
  filter_upwards [hkernel] with cutoff hcutoff
  intro X
  rw [hcutoff]
  exact embeddedMatrix_mem_mappedJointCommutatorKernel_iff c J cutoff X

end NCG.VaryingHilbert.System
