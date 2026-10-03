/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Action.FiniteVariationCanonicalHodgeExact
/-!
# Common-action obstruction with the harmonic projection (`thm:main-common-action`,
  `eq:main-common-action-obstruction`, emergent-spacetime manuscript)

For a finite Hilbert complex `C₀ →d₀ C₁ →d₁ C₂` (`d₁ ∘ d₀ = 0`):

* `harmonicSpace d₀ d₁ = Ker d₁ ⊓ (Ran d₀)ᗮ` is the harmonic space, and
  `harmonicProjection d₀ d₁ = P_har` its orthogonal projection (`Submodule.starProjection`).
* `finiteVariationComplex_hodgeDecomposition_harmonicProjection`: every `α` splits as
  `α = d₀ S + har + coex` with `d₁ har = 0`, `coex ∈ Ran d₁*`, `⟪har, coex⟫ = 0`,
  `⟪har, d₀ x⟫ = 0` for all `x` (the harmonic part is orthogonal to `Ran d₀`), and
  `har = P_har α`.
* `exists_coexact_floor`: `d₁` has a positive lower bound `σ ‖x‖ ≤ ‖d₁ x‖` on the coexact
  range (so the least singular value `σ_coex` of `d₁` there is positive).
* `finiteCommonActionExactness_harmonicProjection` (**`thm:main-common-action`**, exactness and
  obstruction clauses): `α ∈ Ran d₀` iff `d₁ α = 0` and the periods on the certified homology
  representatives vanish; and for every `σ > 0` below `d₁` on the coexact range (in particular
  `σ = σ_coex`),
  `dist(α, Ran d₀)² ≤ ‖P_har α‖² + σ⁻² ‖d₁ α‖²`; moreover `α ∈ Ran d₀` iff
  `P_har α = 0` and `d₁ α = 0`.
-/

open scoped InnerProductSpace

namespace RenewalGeometry

section HarmonicProjection

variable {C₀ C₁ C₂ : Type*}
    [NormedAddCommGroup C₀] [InnerProductSpace ℝ C₀]
    [NormedAddCommGroup C₁] [InnerProductSpace ℝ C₁]
    [NormedAddCommGroup C₂] [InnerProductSpace ℝ C₂]
    [FiniteDimensional ℝ C₀] [FiniteDimensional ℝ C₁] [FiniteDimensional ℝ C₂]

/-- The harmonic space `Ker d₁ ⊓ (Ran d₀)ᗮ` of a finite Hilbert complex. -/
noncomputable def harmonicSpace (d₀ : C₀ →ₗ[ℝ] C₁) (d₁ : C₁ →ₗ[ℝ] C₂) : Submodule ℝ C₁ :=
  LinearMap.ker d₁ ⊓ (LinearMap.range d₀)ᗮ

/-- The harmonic projection `P_har`. -/
noncomputable def harmonicProjection (d₀ : C₀ →ₗ[ℝ] C₁) (d₁ : C₁ →ₗ[ℝ] C₂) : C₁ →L[ℝ] C₁ :=
  (harmonicSpace d₀ d₁).starProjection

/-- Canonical Hodge decomposition whose harmonic part is orthogonal to `Ran d₀` and equals the
harmonic projection `P_har α`. -/
theorem finiteVariationComplex_hodgeDecomposition_harmonicProjection
    (d₀ : C₀ →ₗ[ℝ] C₁) (d₁ : C₁ →ₗ[ℝ] C₂) (hcomplex : d₁ ∘ₗ d₀ = 0) (α : C₁) :
    ∃ S : C₀, ∃ har coex : C₁,
      α = d₀ S + har + coex
      ∧ d₁ har = 0
      ∧ coex ∈ LinearMap.range d₁.adjoint
      ∧ ⟪har, coex⟫_ℝ = 0
      ∧ d₁ (d₀ S) = 0
      ∧ (∀ x : C₀, ⟪har, d₀ x⟫_ℝ = 0)
      ∧ har = harmonicProjection d₀ d₁ α := by
  obtain ⟨ex, hex, rem, hrem, hα⟩ := (LinearMap.range d₀).exists_add_mem_mem_orthogonal α
  obtain ⟨S, rfl⟩ := hex
  obtain ⟨har, hhar, coex, hcoex, hremSplit⟩ :=
    (LinearMap.ker d₁).exists_add_mem_mem_orthogonal rem
  have hcoexRange : coex ∈ LinearMap.range d₁.adjoint := by
    rw [← LinearMap.orthogonal_ker]
    exact hcoex
  have hd₀ker : ∀ x : C₀, d₀ x ∈ LinearMap.ker d₁ := fun x => by
    have h := LinearMap.congr_fun hcomplex x
    simpa using h
  have hharOrth : ∀ x : C₀, ⟪har, d₀ x⟫_ℝ = 0 := by
    intro x
    have h1 : ⟪rem, d₀ x⟫_ℝ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self d₀ x) hrem
    have h2 : ⟪coex, d₀ x⟫_ℝ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (hd₀ker x) hcoex
    have : har = rem - coex := by rw [hremSplit]; abel
    rw [this, inner_sub_left, h1, h2, sub_zero]
  have hharMem : har ∈ harmonicSpace d₀ d₁ := by
    refine ⟨hhar, ?_⟩
    show har ∈ (LinearMap.range d₀)ᗮ
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨x, rfl⟩
    rw [real_inner_comm]
    exact hharOrth x
  have hdecomp : α = d₀ S + har + coex := by rw [hα, hremSplit]; abel
  refine ⟨S, har, coex, hdecomp, LinearMap.mem_ker.mp hhar, hcoexRange,
    Submodule.inner_right_of_mem_orthogonal hhar hcoex, hd₀ker S, hharOrth, ?_⟩
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hharMem
  intro w hw
  have hdiff : α - har = d₀ S + coex := by rw [hdecomp]; abel
  rw [hdiff, inner_add_left]
  have h1 : ⟪d₀ S, w⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self d₀ S) hw.2
  have h2 : ⟪coex, w⟫_ℝ = 0 :=
    Submodule.inner_left_of_mem_orthogonal hw.1 hcoex
  rw [h1, h2, add_zero]

/-- `d₁` is bounded below on the coexact range: there is `σ > 0` with `σ ‖x‖ ≤ ‖d₁ x‖` for
every `x ∈ Ran d₁*` (the least singular value of `d₁` on the coexact range is positive). -/
theorem exists_coexact_floor (d₁ : C₁ →ₗ[ℝ] C₂) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ x ∈ LinearMap.range d₁.adjoint, σ * ‖x‖ ≤ ‖d₁ x‖ := by
  set U := LinearMap.range d₁.adjoint
  let f : U →ₗ[ℝ] C₂ := d₁.domRestrict U
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have hx0 : d₁ (x : C₁) = 0 := LinearMap.mem_ker.mp hx
    have hxker : (x : C₁) ∈ LinearMap.ker d₁ := hx0
    have hxperp : (x : C₁) ∈ (LinearMap.ker d₁)ᗮ := by
      rw [LinearMap.orthogonal_ker]; exact x.2
    have : (x : C₁) = 0 := by
      have h := Submodule.inner_right_of_mem_orthogonal hxker hxperp
      simpa using h
    rw [Submodule.mem_bot]
    exact Subtype.ext this
  let e := (LinearEquiv.ofInjective f hf).toContinuousLinearEquiv
  refine ⟨(‖(e.symm : LinearMap.range f →L[ℝ] U)‖ + 1)⁻¹, by positivity, ?_⟩
  intro x hx
  have hle : ‖(⟨x, hx⟩ : U)‖ ≤ ‖(e.symm : LinearMap.range f →L[ℝ] U)‖ * ‖e ⟨x, hx⟩‖ := by
    have := (e.symm : LinearMap.range f →L[ℝ] U).le_opNorm (e ⟨x, hx⟩)
    simpa using this
  have hnorm : ‖e ⟨x, hx⟩‖ = ‖d₁ x‖ := rfl
  have hnx : ‖(⟨x, hx⟩ : U)‖ = ‖x‖ := rfl
  rw [hnorm, hnx] at hle
  have hpos : 0 < ‖(e.symm : LinearMap.range f →L[ℝ] U)‖ + 1 := by positivity
  rw [inv_mul_le_iff₀ hpos]
  nlinarith [norm_nonneg (d₁ x)]

/-- **`thm:main-common-action`** (exactness criterion and `eq:main-common-action-obstruction`
with the harmonic projection). -/
theorem finiteCommonActionExactness_harmonicProjection
    (d₀ : C₀ →ₗ[ℝ] C₁) (d₁ : C₁ →ₗ[ℝ] C₂) (hcomplex : d₁ ∘ₗ d₀ = 0)
    (H : FirstHomologyRepresentativeCertificate C₀ C₁ C₂ d₀ d₁)
    (α : C₁) (σ : ℝ) (hσ : 0 < σ)
    (hcoexactFloor : ∀ x ∈ LinearMap.range d₁.adjoint, σ * ‖x‖ ≤ ‖d₁ x‖) :
    ((∃ S : C₀, d₀ S = α) ↔
      d₁ α = 0 ∧ ∀ b : H.index, ⟪H.representative b, α⟫_ℝ = 0)
    ∧ Metric.infDist α (LinearMap.range d₀ : Set C₁) ^ 2 ≤
        ‖harmonicProjection d₀ d₁ α‖ ^ 2 + σ⁻¹ ^ 2 * ‖d₁ α‖ ^ 2
    ∧ ((∃ S : C₀, d₀ S = α) ↔ harmonicProjection d₀ d₁ α = 0 ∧ d₁ α = 0) := by
  obtain ⟨S, har, coex, hdecomp, hcurlHar, hcoex, hhc, hcurlExact, -, hP⟩ :=
    finiteVariationComplex_hodgeDecomposition_harmonicProjection d₀ d₁ hcomplex α
  have hbound := finiteVariationComplex_hodge_distance_bound d₀ d₁ α S har coex σ
    hdecomp hhc hcurlExact hcurlHar hσ (hcoexactFloor coex hcoex)
  refine ⟨finiteVariationComplex_commonAction_exactness d₀ d₁ hcomplex H α, ?_, ?_⟩
  · rw [← hP]; exact hbound
  · constructor
    · rintro ⟨T, rfl⟩
      have hcurl : d₁ (d₀ T) = 0 := by
        have h := LinearMap.congr_fun hcomplex T
        simpa using h
      refine ⟨?_, hcurl⟩
      apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
      intro w hw
      rw [sub_zero]
      exact Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self d₀ T) hw.2
    · rintro ⟨hPα, hcurl⟩
      have hhar0 : har = 0 := by rw [hP, hPα]
      have hcurlcoex : d₁ coex = 0 := by
        rw [hdecomp, map_add, map_add, hcurlExact, hcurlHar, zero_add, zero_add] at hcurl
        exact hcurl
      have hcoex0 : coex = 0 := by
        have h := hcoexactFloor coex hcoex
        rw [hcurlcoex, norm_zero] at h
        have : ‖coex‖ ≤ 0 := by nlinarith [norm_nonneg coex]
        exact norm_le_zero_iff.mp this
      exact ⟨S, by rw [hdecomp, hhar0, hcoex0, add_zero, add_zero]⟩

/-- The floor hypothesis is always satisfiable (`exists_coexact_floor`), so the obstruction
bound holds unconditionally with some positive `σ`. -/
theorem finiteCommonActionExactness_harmonicProjection_exists_floor
    (d₀ : C₀ →ₗ[ℝ] C₁) (d₁ : C₁ →ₗ[ℝ] C₂) (hcomplex : d₁ ∘ₗ d₀ = 0) (α : C₁) :
    ∃ σ : ℝ, 0 < σ ∧ (∀ x ∈ LinearMap.range d₁.adjoint, σ * ‖x‖ ≤ ‖d₁ x‖) ∧
      Metric.infDist α (LinearMap.range d₀ : Set C₁) ^ 2 ≤
        ‖harmonicProjection d₀ d₁ α‖ ^ 2 + σ⁻¹ ^ 2 * ‖d₁ α‖ ^ 2 := by
  obtain ⟨σ, hσ, hfloor⟩ := exists_coexact_floor d₁
  obtain ⟨S, har, coex, hdecomp, hcurlHar, hcoex, hhc, hcurlExact, -, hP⟩ :=
    finiteVariationComplex_hodgeDecomposition_harmonicProjection d₀ d₁ hcomplex α
  refine ⟨σ, hσ, hfloor, ?_⟩
  rw [← hP]
  exact finiteVariationComplex_hodge_distance_bound d₀ d₁ α S har coex σ
    hdecomp hhc hcurlExact hcurlHar hσ (hfloor coex hcoex)

end HarmonicProjection

end RenewalGeometry
