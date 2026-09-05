/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertFiniteStageCompression
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-!
# Eigenspaces of compressed stage operators

At a nonzero eigenvalue, compression through an isometric stage embedding introduces
no spurious eigenvectors: the common-carrier eigenspace is exactly the image of the
stage eigenspace.  The nonzero hypothesis is essential because compression vanishes
on the orthogonal complement of the stage range.
-/

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, CompleteSpace (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- A nonzero eigenspace of a common-carrier compression is the embedded stage
eigenspace. -/
theorem eigenspace_compressedOperator_eq_map
    (Tn : ∀ n, Hn n →L[K] Hn n) (n : ℕ) (μ : K) (hμ : μ ≠ 0) :
    Module.End.eigenspace (J.compressedOperator Tn n).toLinearMap μ =
      (Module.End.eigenspace (Tn n).toLinearMap μ).map
        (J.embedding n).toLinearMap := by
  apply le_antisymm
  · intro x hx
    have heigen : J.compressedOperator Tn n x = μ • x :=
      Module.End.mem_eigenspace_iff.mp hx
    let y : Hn n := μ⁻¹ • Tn n (J.adjointLift n x)
    have hxy : J.embedding n y = x := by
      calc
        J.embedding n y = μ⁻¹ • J.embedding n (Tn n (J.adjointLift n x)) := by
          simp only [y, map_smul]
        _ = μ⁻¹ • J.compressedOperator Tn n x := by
          rfl
        _ = μ⁻¹ • (μ • x) := congrArg (fun z ↦ μ⁻¹ • z) heigen
        _ = x := inv_smul_smul₀ hμ x
    have hy : y ∈ Module.End.eigenspace (Tn n).toLinearMap μ := by
      rw [Module.End.mem_eigenspace_iff]
      apply (J.embedding n).injective
      calc
        J.embedding n ((Tn n).toLinearMap y) =
            J.compressedOperator Tn n (J.embedding n y) :=
          (J.compressedOperator_embedding Tn n y).symm
        _ = μ • J.embedding n y := by rw [hxy, heigen]
        _ = J.embedding n (μ • y) := (map_smul (J.embedding n) μ y).symm
    exact Submodule.mem_map.mpr ⟨y, hy, hxy⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    rw [Module.End.mem_eigenspace_iff] at hy ⊢
    change J.compressedOperator Tn n (J.embedding n y) = μ • J.embedding n y
    calc
      J.compressedOperator Tn n (J.embedding n y) = J.embedding n (Tn n y) :=
        J.compressedOperator_embedding Tn n y
      _ = J.embedding n (μ • y) := congrArg (fun z ↦ J.embedding n z) hy
      _ = μ • J.embedding n y := map_smul (J.embedding n) μ y

end NCG.VaryingHilbert.System
