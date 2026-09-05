/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteVariationComplexExactness

/-!
# Canonical finite Hodge decomposition for common-action exactness

This derives the exact/harmonic/coexact decomposition used by the quantitative clause of
`thm:common-action-exactness`; it is no longer supplied as a theorem hypothesis.
-/

open scoped InnerProductSpace

namespace NCG

/-- Every one-cochain in a finite Hilbert complex has a canonical orthogonal decomposition into
an exact term, a harmonic closed term, and a coexact term in the adjoint two-cell range. -/
theorem finiteVariationComplex_canonicalHodgeDecomposition
    {C₀ C₁ C₂ : Type*}
    [NormedAddCommGroup C₀] [InnerProductSpace ℝ C₀]
    [NormedAddCommGroup C₁] [InnerProductSpace ℝ C₁]
    [NormedAddCommGroup C₂] [InnerProductSpace ℝ C₂]
    [FiniteDimensional ℝ C₀] [FiniteDimensional ℝ C₁]
    [FiniteDimensional ℝ C₂]
    (d₀ : C₀ →ₗ[ℝ] C₁) (d₁ : C₁ →ₗ[ℝ] C₂)
    (hcomplex : d₁ ∘ₗ d₀ = 0) (α : C₁) :
    ∃ S : C₀, ∃ har coex : C₁,
      α = d₀ S + har + coex
      ∧ d₁ har = 0
      ∧ coex ∈ d₁.adjoint.range
      ∧ ⟪har, coex⟫_ℝ = 0
      ∧ d₁ (d₀ S) = 0 := by
  obtain ⟨ex, hex, rem, hrem, hα⟩ := d₀.range.exists_add_mem_mem_orthogonal α
  obtain ⟨S, rfl⟩ := hex
  obtain ⟨har, hhar, coex, hcoex, hremSplit⟩ :=
    d₁.ker.exists_add_mem_mem_orthogonal rem
  have hcoexRange : coex ∈ d₁.adjoint.range := by
    rw [← LinearMap.orthogonal_ker]
    exact hcoex
  have hcurlExact : d₁ (d₀ S) = 0 := by
    have h := LinearMap.congr_fun hcomplex S
    simpa using h
  refine ⟨S, har, coex, ?_, LinearMap.mem_ker.mp hhar, hcoexRange, ?_, hcurlExact⟩
  · rw [hα, hremSplit]
    abel
  · exact Submodule.inner_right_of_mem_orthogonal hhar hcoex

/-- **Finite common-action exactness (`thm:common-action-exactness`), canonical Hodge form.**
The face/period criterion is paired with a quantitatively controlled canonical Hodge
decomposition; only the manuscript's coexact singular-value floor remains an input. -/
theorem finiteCommonActionExactness_canonicalHodge
    {C₀ C₁ C₂ : Type*}
    [NormedAddCommGroup C₀] [InnerProductSpace ℝ C₀]
    [NormedAddCommGroup C₁] [InnerProductSpace ℝ C₁]
    [NormedAddCommGroup C₂] [InnerProductSpace ℝ C₂]
    [FiniteDimensional ℝ C₀] [FiniteDimensional ℝ C₁]
    [FiniteDimensional ℝ C₂]
    (d₀ : C₀ →ₗ[ℝ] C₁) (d₁ : C₁ →ₗ[ℝ] C₂)
    (hcomplex : d₁ ∘ₗ d₀ = 0)
    (H : FirstHomologyRepresentativeCertificate C₀ C₁ C₂ d₀ d₁)
    (α : C₁) (σ : ℝ) (hσ : 0 < σ)
    (hcoexactFloor : ∀ x ∈ d₁.adjoint.range, σ * ‖x‖ ≤ ‖d₁ x‖) :
    ((∃ S : C₀, d₀ S = α) ↔
      d₁ α = 0 ∧ ∀ b : H.index, ⟪H.representative b, α⟫_ℝ = 0)
    ∧ ∃ S : C₀, ∃ har coex : C₁,
      α = d₀ S + har + coex
      ∧ d₁ har = 0
      ∧ coex ∈ d₁.adjoint.range
      ∧ ⟪har, coex⟫_ℝ = 0
      ∧ Metric.infDist α (d₀.range : Set C₁) ^ 2 ≤
        ‖har‖ ^ 2 + σ⁻¹ ^ 2 * ‖d₁ α‖ ^ 2 := by
  refine ⟨finiteVariationComplex_commonAction_exactness d₀ d₁ hcomplex H α, ?_⟩
  obtain ⟨S, har, coex, hdecomp, hcurlHar, hcoex, hhc, hcurlExact⟩ :=
    finiteVariationComplex_canonicalHodgeDecomposition d₀ d₁ hcomplex α
  refine ⟨S, har, coex, hdecomp, hcurlHar, hcoex, hhc, ?_⟩
  exact finiteVariationComplex_hodge_distance_bound d₀ d₁ α S har coex σ
    hdecomp hhc hcurlExact hcurlHar hσ (hcoexactFloor coex hcoex)

end NCG
