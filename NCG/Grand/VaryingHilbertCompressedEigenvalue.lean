/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCompressedEigenspace

/-!
# Nonzero eigenvalues of compressed stage operators

Compression through an isometric stage embedding preserves and reflects every nonzero
eigenvalue. This is the proposition-level companion to the exact eigenspace map theorem.
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

/-- At every nonzero scalar, a literal common-carrier compression has an eigenvalue exactly when
the original stage operator does. -/
theorem hasEigenvalue_compressedOperator_iff
    (J : System (K := K) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[K] Hn n) (n : ℕ) (μ : K) (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (J.compressedOperator Tn n).toLinearMap μ ↔
      Module.End.HasEigenvalue (Tn n).toLinearMap μ := by
  constructor
  · intro hcompressed
    obtain ⟨x, hx⟩ := hcompressed.exists_hasEigenvector
    have hxmem : x ∈ Module.End.eigenspace
        (J.compressedOperator Tn n).toLinearMap μ := hx.1
    rw [J.eigenspace_compressedOperator_eq_map Tn n μ hμ] at hxmem
    obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp hxmem
    have hy0 : y ≠ 0 := by
      intro hyzero
      apply hx.2
      rw [← hxy, hyzero]
      simp
    exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hy, hy0⟩
  · intro hstage
    obtain ⟨y, hy⟩ := hstage.exists_hasEigenvector
    have hxmem : J.embedding n y ∈ Module.End.eigenspace
        (J.compressedOperator Tn n).toLinearMap μ := by
      rw [J.eigenspace_compressedOperator_eq_map Tn n μ hμ]
      exact Submodule.mem_map.mpr ⟨y, hy.1, rfl⟩
    have hx0 : J.embedding n y ≠ 0 := by
      simpa using (J.embedding n).injective.ne hy.2
    exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hxmem, hx0⟩

end NCG.VaryingHilbert.System
