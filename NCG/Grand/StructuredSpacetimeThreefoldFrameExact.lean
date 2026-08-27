/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PositiveSpectralFloorCharacterization

/-!
# Finite structured spacetime frames and threefold determinant sources

This closes the finite-family, threefold tensor, and explicit collapsing-source clauses of
`thm:SMST-spacetime-frame`.
-/

open Matrix Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology

namespace NCG

/-- Orthogonally summing any finite family of block lower-frame inequalities preserves the
common lower bound. -/
theorem finiteOrthogonalBlocks_frameFloor
    {ι : Type*} [Fintype ι] (q normSq : ι → ℝ) (c : ℝ)
    (hfloor : ∀ i, c * normSq i ≤ q i) :
    c * ∑ i, normSq i ≤ ∑ i, q i := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hfloor i

/-- The product of three positive blocks with common least-positive-eigenvalue floor `c` has
the exact order certificate with floor `c³`. -/
theorem threefoldDeterminantSource_frameFloor
    {a b d : ℕ}
    (A : Matrix (Fin a) (Fin a) ℂ)
    (B : Matrix (Fin b) (Fin b) ℂ)
    (C : Matrix (Fin d) (Fin d) ℂ)
    (c : ℝ) (hc : 0 ≤ c)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (hAspec : ∀ i, hA.1.eigenvalues i = 0 ∨ c ≤ hA.1.eigenvalues i)
    (hBspec : ∀ i, hB.1.eigenvalues i = 0 ∨ c ≤ hB.1.eigenvalues i)
    (hCspec : ∀ i, hC.1.eigenvalues i = 0 ∨ c ≤ hC.1.eigenvalues i) :
    ((((A ⊗ₖ B) ⊗ₖ C) * ((A ⊗ₖ B) ⊗ₖ C))
      - ((c ^ 3 : ℝ) : ℂ) • ((A ⊗ₖ B) ⊗ₖ C)).PosSemidef := by
  have hAf := leastPositiveEigenvalueBound_implies_sourceFrameFloor A c hA hAspec
  have hBf := leastPositiveEigenvalueBound_implies_sourceFrameFloor B c hB hBspec
  have hCf := leastPositiveEigenvalueBound_implies_sourceFrameFloor C c hC hCspec
  have hABfloor := (smst_spacetime_frame A B c c hA hB hc hAf hBf).2.1
  have hAB : (A ⊗ₖ B).PosSemidef := hA.kronecker hB
  have hcc : 0 ≤ c * c := mul_nonneg hc hc
  have hABC :=
    (smst_spacetime_frame (A ⊗ₖ B) C (c * c) c hAB hC hcc hABfloor hCf).2.1
  simpa [pow_three, mul_assoc] using hABC

/-- Physical norm of a coefficient direction measured by a positive source block. -/
noncomputable def spacetimeSourceNorm {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (v : n → ℂ) : ℝ :=
  Real.sqrt (star v ⬝ᵥ (A *ᵥ v)).re

/-- A normalized eigenvector has source norm exactly the square root of its positive
eigenvalue; hence eigenvalues tending to zero give explicit collapsing source directions. -/
theorem normalizedEigenvectors_explicit_sourceCollapse
    {n : Type*} [Fintype n]
    (A : ℕ → Matrix n n ℂ) (v : ℕ → n → ℂ) (μ : ℕ → ℝ)
    (hunit : ∀ k, star (v k) ⬝ᵥ v k = 1)
    (heigen : ∀ k, A k *ᵥ v k = (μ k : ℂ) • v k)
    (hμ : Tendsto μ atTop (𝓝 0)) :
    (∀ k, spacetimeSourceNorm (A k) (v k) = Real.sqrt (μ k))
      ∧ Tendsto (fun k => spacetimeSourceNorm (A k) (v k)) atTop (𝓝 0) := by
  have hnorm : ∀ k, spacetimeSourceNorm (A k) (v k) = Real.sqrt (μ k) := by
    intro k
    simp [spacetimeSourceNorm, heigen k, dotProduct_smul, hunit k]
  refine ⟨hnorm, ?_⟩
  have hsqrt : Tendsto (fun k => Real.sqrt (μ k)) atTop (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hμ
  simpa [hnorm] using hsqrt

/-- **Structured spacetime source-frame noncollapse (`thm:SMST-spacetime-frame`).**  The finite
orthogonal block floor, exact threefold `c³` determinant floor, and normalized collapsing
eigenvector mechanism hold simultaneously. -/
theorem structuredSpacetimeSourceFrame_noncollapse_exact
    {ι : Type*} [Fintype ι] (q normSq : ι → ℝ)
    (c : ℝ) (hblocks : ∀ i, c * normSq i ≤ q i)
    {a b d : ℕ}
    (A : Matrix (Fin a) (Fin a) ℂ)
    (B : Matrix (Fin b) (Fin b) ℂ)
    (C : Matrix (Fin d) (Fin d) ℂ)
    (hc : 0 ≤ c)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (hAspec : ∀ i, hA.1.eigenvalues i = 0 ∨ c ≤ hA.1.eigenvalues i)
    (hBspec : ∀ i, hB.1.eigenvalues i = 0 ∨ c ≤ hB.1.eigenvalues i)
    (hCspec : ∀ i, hC.1.eigenvalues i = 0 ∨ c ≤ hC.1.eigenvalues i) :
    c * ∑ i, normSq i ≤ ∑ i, q i
    ∧ ((((A ⊗ₖ B) ⊗ₖ C) * ((A ⊗ₖ B) ⊗ₖ C))
      - ((c ^ 3 : ℝ) : ℂ) • ((A ⊗ₖ B) ⊗ₖ C)).PosSemidef := by
  exact ⟨finiteOrthogonalBlocks_frameFloor q normSq c hblocks,
    threefoldDeterminantSource_frameFloor A B C c hc hA hB hC hAspec hBspec hCspec⟩

end NCG
