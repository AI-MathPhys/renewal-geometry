/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.InterfaceBlockResolvent
import NCG.Grand.ProvenanceBlockAggregation

/-!
# Exact interface-network coercivity

This closes the second display of `thm:interface-coercivity` without assuming
either the Feshbach decomposition or the graph-map norm estimate.  Both are
derived from the concrete exterior/interior block matrix.  The hypothesis
that the interior inverse is Hermitian is the manuscript's real pole-free
condition.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Norms.L2Operator

namespace NCG

variable {e i : Type*} [Fintype e] [Fintype i]
  [DecidableEq e] [DecidableEq i] [Nonempty e]

/-- The exterior Schur response of the block interface matrix. -/
noncomputable abbrev interfaceSchur
    (C : Matrix e e ℂ) (B : Matrix i e ℂ) (D : Matrix i i ℂ)
    [Invertible D] : Matrix e e ℂ :=
  C - Bᴴ * ⅟D * B

/-- The solution (or graph) map `x ↦ (x,-D⁻¹Bx)`. -/
noncomputable def interfaceSolutionMap
    (B : Matrix i e ℂ) (D : Matrix i i ℂ) [Invertible D] :
    Matrix (e ⊕ i) e ℂ :=
  Matrix.fromRows 1 (-(⅟D * B))

/-- The interior resolvent embedded in the full direct sum. -/
noncomputable def interfaceInteriorEmbed
    (D : Matrix i i ℂ) [Invertible D] : Matrix (e ⊕ i) (e ⊕ i) ℂ :=
  Matrix.fromBlocks 0 0 0 (⅟D)

/-- The embedded interior inverse costs no more operator norm than the
interior inverse itself. -/
theorem interfaceInteriorEmbed_norm_le
    (D : Matrix i i ℂ) [Invertible D] :
    ‖interfaceInteriorEmbed (e := e) D‖ ≤ ‖⅟D‖ := by
  simpa [interfaceInteriorEmbed] using
    (l2_opNorm_fromBlocks_oneway_le
      (0 : Matrix e e ℂ) (0 : Matrix i e ℂ) (⅟D))

/-- The exact Gram matrix of the interface solution map. -/
theorem interfaceSolutionMap_gram
    (B : Matrix i e ℂ) (D : Matrix i i ℂ) [Invertible D] :
    (interfaceSolutionMap B D)ᴴ * interfaceSolutionMap B D =
      1 + (⅟D * B)ᴴ * (⅟D * B) := by
  simp only [interfaceSolutionMap,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromRows]
  simp

/-- The graph-map factor in the network resolvent estimate follows from the
two concrete operator-norm bounds. -/
theorem interfaceSolutionMap_norm_product_le
    (B : Matrix i e ℂ) (D : Matrix i i ℂ) [Invertible D]
    (MD MB : ℝ) (hMD : 0 ≤ MD) (hMB : 0 ≤ MB)
    (hD : ‖⅟D‖ ≤ MD) (hB : ‖B‖ ≤ MB) :
    ‖interfaceSolutionMap B D‖ * ‖(interfaceSolutionMap B D)ᴴ‖ ≤
      1 + MD ^ 2 * MB ^ 2 := by
  let X : Matrix i e ℂ := ⅟D * B
  have hX : ‖X‖ ≤ MD * MB := by
    calc
      ‖X‖ ≤ ‖⅟D‖ * ‖B‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ MD * MB := mul_le_mul hD hB (norm_nonneg _) hMD
  rw [Matrix.l2_opNorm_conjTranspose]
  rw [← Matrix.l2_opNorm_conjTranspose_mul_self]
  rw [interfaceSolutionMap_gram]
  calc
    ‖1 + Xᴴ * X‖ ≤ ‖(1 : Matrix e e ℂ)‖ + ‖Xᴴ * X‖ := norm_add_le _ _
    _ ≤ 1 + ‖X‖ * ‖X‖ := by
      rw [Matrix.l2_opNorm_conjTranspose_mul_self]
      gcongr
      simp
    _ ≤ 1 + (MD * MB) * (MD * MB) := by
      gcongr
    _ = 1 + MD ^ 2 * MB ^ 2 := by ring

/-- The exact Feshbach inverse decomposition for the concrete interface
matrix.  It is no longer an input hypothesis. -/
theorem interface_feshbach_decomposition
    (C : Matrix e e ℂ) (B : Matrix i e ℂ) (D : Matrix i i ℂ)
    [Invertible D] [Invertible (C - Bᴴ * ⅟D * B)]
    (hDstar : (⅟D)ᴴ = ⅟D) :
    (Matrix.fromBlocks C Bᴴ B D)⁻¹ =
      interfaceInteriorEmbed (e := e) D +
        interfaceSolutionMap B D * ⅟(interfaceSchur C B D) *
          (interfaceSolutionMap B D)ᴴ := by
  letI : Invertible (Matrix.fromBlocks C Bᴴ B D) :=
    Matrix.fromBlocks₂₂Invertible C Bᴴ B D
  have hDstar' : D⁻¹ᴴ = D⁻¹ := by
    simpa only [Matrix.invOf_eq_nonsing_inv] using hDstar
  rw [← Matrix.invOf_eq_nonsing_inv]
  rw [Matrix.invOf_fromBlocks₂₂_eq]
  simp only [interfaceSchur, interfaceInteriorEmbed, interfaceSolutionMap,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose]
  rw [Matrix.fromRows_mul]
  rw [Matrix.fromRows_mul_fromCols]
  rw [Matrix.fromBlocks_add]
  simp [hDstar', Matrix.mul_assoc]

/-- `thm:interface-coercivity`, second display, derived directly from the
block matrix at a real pole-free point. -/
theorem interface_block_resolvent_exact
    (C : Matrix e e ℂ) (B : Matrix i e ℂ) (D : Matrix i i ℂ)
    [Invertible D] [Invertible (C - Bᴴ * ⅟D * B)]
    (MD MB δE : ℝ) (hMD : 0 ≤ MD) (hMB : 0 ≤ MB) (hδE : 0 < δE)
    (hDstar : (⅟D)ᴴ = ⅟D)
    (hD : ‖⅟D‖ ≤ MD) (hB : ‖B‖ ≤ MB)
    (hL : ‖⅟(interfaceSchur C B D)‖ ≤ 1 / δE) :
    ‖(Matrix.fromBlocks C Bᴴ B D)⁻¹‖ ≤
      MD + (1 + MD ^ 2 * MB ^ 2) / δE := by
  letI : Invertible (Matrix.fromBlocks C Bᴴ B D) :=
    Matrix.fromBlocks₂₂Invertible C Bᴴ B D
  have hEmbed : ‖interfaceInteriorEmbed (e := e) D‖ ≤ MD :=
    (interfaceInteriorEmbed_norm_le D).trans hD
  have hγ : ‖interfaceSolutionMap B D‖ *
      ‖(interfaceSolutionMap B D)ᴴ‖ ≤ 1 + MD ^ 2 * MB ^ 2 :=
    interfaceSolutionMap_norm_product_le B D MD MB hMD hMB hD hB
  have hfac : 0 ≤ 1 + MD ^ 2 * MB ^ 2 := by positivity
  have htriple :
      ‖interfaceSolutionMap B D * ⅟(interfaceSchur C B D) *
        (interfaceSolutionMap B D)ᴴ‖ ≤
          (1 + MD ^ 2 * MB ^ 2) * (1 / δE) := by
    calc
      ‖interfaceSolutionMap B D * ⅟(interfaceSchur C B D) *
          (interfaceSolutionMap B D)ᴴ‖
          ≤ ‖interfaceSolutionMap B D * ⅟(interfaceSchur C B D)‖ *
              ‖(interfaceSolutionMap B D)ᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖interfaceSolutionMap B D‖ *
              ‖⅟(interfaceSchur C B D)‖) *
              ‖(interfaceSolutionMap B D)ᴴ‖ := by
            gcongr
            exact Matrix.l2_opNorm_mul _ _
      _ = (‖interfaceSolutionMap B D‖ *
              ‖(interfaceSolutionMap B D)ᴴ‖) *
              ‖⅟(interfaceSchur C B D)‖ := by ring
      _ ≤ (1 + MD ^ 2 * MB ^ 2) * (1 / δE) :=
        mul_le_mul hγ hL (norm_nonneg _) hfac
  rw [interface_feshbach_decomposition C B D hDstar]
  calc
    ‖interfaceInteriorEmbed (e := e) D +
        interfaceSolutionMap B D * ⅟(interfaceSchur C B D) *
          (interfaceSolutionMap B D)ᴴ‖
      ≤ ‖interfaceInteriorEmbed (e := e) D‖ +
          ‖interfaceSolutionMap B D * ⅟(interfaceSchur C B D) *
            (interfaceSolutionMap B D)ᴴ‖ := norm_add_le _ _
    _ ≤ MD + (1 + MD ^ 2 * MB ^ 2) * (1 / δE) :=
      add_le_add hEmbed htriple
    _ = MD + (1 + MD ^ 2 * MB ^ 2) / δE := by
      simp [div_eq_mul_inv]

end NCG
