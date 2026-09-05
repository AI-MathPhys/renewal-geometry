/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Eigenspaces of finite-dimensional normal operators

Mathlib supplies simultaneous diagonalization for commuting symmetric operators.  Applying it to
the real and imaginary parts of a normal complex operator proves that its eigenspaces span the
whole finite-dimensional Hilbert space.  This is the finite-dimensional normal spectral input
needed in the compact-normal decomposition.
-/

open Complex Module End
open scoped ComplexStarModule

noncomputable section

namespace NCG.NormalSpectrum

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]

/-- The eigenspaces of a normal operator on a finite-dimensional complex Hilbert space span the
whole space. -/
theorem iSup_eigenspaces_eq_top_of_isStarNormal
    (T : E →L[ℂ] E) (hnormal : IsStarNormal T) :
    (⨆ μ, eigenspace T.toLinearMap μ) = ⊤ := by
  let R : E →L[ℂ] E := (ℜ T : E →L[ℂ] E)
  let Iop : E →L[ℂ] E := (ℑ T : E →L[ℂ] E)
  have hRself : IsSelfAdjoint R := by
    simp [R]
  have hIself : IsSelfAdjoint Iop := by
    simp [Iop]
  have hcommCLM : Commute R Iop := by
    simpa [R, Iop] using
      (isStarNormal_iff_commute_realPart_imaginaryPart.mp hnormal)
  have hcomm : Commute R.toLinearMap Iop.toLinearMap := by
    rw [commute_iff_eq] at hcommCLM ⊢
    simpa only [ContinuousLinearMap.toLinearMap_mul] using
      congrArg ContinuousLinearMap.toLinearMap hcommCLM
  have hjoint :
      (⨆ α, ⨆ γ,
        eigenspace R.toLinearMap α ⊓ eigenspace Iop.toLinearMap γ) = ⊤ :=
    LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute
      hRself.isSymmetric hIself.isSymmetric hcomm
  apply top_unique
  rw [← hjoint]
  refine iSup_le fun α ↦ iSup_le fun γ ↦ ?_
  intro x hx
  have hxR : R x = α • x := mem_eigenspace_iff.mp hx.1
  have hxI : Iop x = γ • x := mem_eigenspace_iff.mp hx.2
  apply le_iSup (fun μ ↦ eigenspace T.toLinearMap μ) (α + Complex.I * γ)
  rw [mem_eigenspace_iff]
  have hdecomp : R + Complex.I • Iop = T := by
    simpa [R, Iop] using realPart_add_I_smul_imaginaryPart T
  calc
    T x = R x + Complex.I • Iop x := by
      rw [← hdecomp]
      rfl
    _ = α • x + Complex.I • (γ • x) := by rw [hxR, hxI]
    _ = (α + Complex.I * γ) • x := by
      rw [add_smul, smul_smul]

/-- Equivalently, the algebraic sum of all eigenspaces of a finite-dimensional normal operator is
dense. -/
theorem dense_iSup_eigenspaces_of_isStarNormal
    (T : E →L[ℂ] E) (hnormal : IsStarNormal T) :
    Dense ((((⨆ μ, eigenspace T.toLinearMap μ) : Submodule ℂ E) : Set E)) := by
  rw [iSup_eigenspaces_eq_top_of_isStarNormal T hnormal]
  exact dense_univ

end NCG.NormalSpectrum
