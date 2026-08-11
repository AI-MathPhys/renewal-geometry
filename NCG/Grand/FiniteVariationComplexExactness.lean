/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite variation-complex exactness

This file proves the common-action criterion on an honest finite Hilbert
cochain complex.  A finite family of cycle representatives is required to
span cycles modulo the boundaries of the declared two-cells.  Thus vanishing
face curls and vanishing periods on those representatives imply exactness;
the converse follows from the cochain relation.  A separate Hodge theorem
proves the manuscript's quantitative distance bound.
-/

open scoped InnerProductSpace

namespace NCG

/-- Certificate that the declared representatives span first homology: every
cycle is a two-cell boundary plus a linear combination of the representatives. -/
structure FirstHomologyRepresentativeCertificate
    (C₀ C₁ C₂ : Type*) [NormedAddCommGroup C₀] [InnerProductSpace ℝ C₀]
    [NormedAddCommGroup C₁] [InnerProductSpace ℝ C₁]
    [NormedAddCommGroup C₂] [InnerProductSpace ℝ C₂]
    [FiniteDimensional ℝ C₀] [FiniteDimensional ℝ C₁]
    [FiniteDimensional ℝ C₂]
    (d₀ : C₀ →ₗ[ℝ] C₁) (d₁ : C₁ →ₗ[ℝ] C₂) where
  index : Type*
  indexFintype : Fintype index
  representative : index → C₁
  representative_cycle : ∀ b, d₀.adjoint (representative b) = 0
  spans_cycles_mod_boundaries : ∀ z : C₁, d₀.adjoint z = 0 →
    ∃ face : C₂, ∃ coefficient : index → ℝ,
      z = d₁.adjoint face + ∑ b, coefficient b • representative b

attribute [instance]
  FirstHomologyRepresentativeCertificate.indexFintype

/-- Exact finite common-action criterion: a protected one-cochain is a
coboundary iff its two-cell curl and all periods on a first-homology basis
vanish. -/
theorem finiteVariationComplex_commonAction_exactness
    {C₀ C₁ C₂ : Type*}
    [NormedAddCommGroup C₀] [InnerProductSpace ℝ C₀]
    [NormedAddCommGroup C₁] [InnerProductSpace ℝ C₁]
    [NormedAddCommGroup C₂] [InnerProductSpace ℝ C₂]
    [FiniteDimensional ℝ C₀] [FiniteDimensional ℝ C₁]
    [FiniteDimensional ℝ C₂]
    (d₀ : C₀ →ₗ[ℝ] C₁) (d₁ : C₁ →ₗ[ℝ] C₂)
    (hcomplex : d₁ ∘ₗ d₀ = 0)
    (H : FirstHomologyRepresentativeCertificate C₀ C₁ C₂ d₀ d₁)
    (α : C₁) :
    (∃ S : C₀, d₀ S = α) ↔
      d₁ α = 0 ∧ ∀ b : H.index, ⟪H.representative b, α⟫_ℝ = 0 := by
  constructor
  · rintro ⟨S, rfl⟩
    constructor
    · have hs := LinearMap.congr_fun hcomplex S
      simpa using hs
    · intro b
      rw [← LinearMap.adjoint_inner_left]
      rw [H.representative_cycle]
      simp
  · rintro ⟨hcurl, hperiod⟩
    have haorth : α ∈ d₀.adjoint.kerᗮ := by
      rw [Submodule.mem_orthogonal]
      intro z hz
      change d₀.adjoint z = 0 at hz
      obtain ⟨face, coefficient, hzdecomp⟩ :=
        H.spans_cycles_mod_boundaries z hz
      rw [hzdecomp, inner_add_left, LinearMap.adjoint_inner_left,
        hcurl]
      simp only [inner_zero_right, zero_add, sum_inner]
      apply Finset.sum_eq_zero
      intro b _
      rw [inner_smul_left, hperiod]
      simp
    have harange : α ∈ d₀.range := by
      rw [LinearMap.orthogonal_ker, LinearMap.adjoint_adjoint] at haorth
      exact haorth
    exact harange

/-- Endpoint reached by a finite vertex path encoded by its successive
vertices after the starting point. -/
def finitePathEndpoint {V : Type*} (start : V) : List V → V
  | [] => start
  | next :: rest => finitePathEndpoint next rest

/-- Integral of an oriented edge increment along the same finite path. -/
def finitePathIntegral {V : Type*} (increment : V → V → ℝ)
    (start : V) : List V → ℝ
  | [] => 0
  | next :: rest => increment start next +
      finitePathIntegral increment next rest

/-- A common action reconstructs every path integral by telescoping. -/
theorem finitePathIntegral_coboundary
    {V : Type*} (S : V → ℝ) (start : V) (path : List V) :
    finitePathIntegral (fun x y => S y - S x) start path =
      S (finitePathEndpoint start path) - S start := by
  induction path generalizing start with
  | nil => simp [finitePathIntegral, finitePathEndpoint]
  | cons next rest ih =>
      simp only [finitePathIntegral, finitePathEndpoint]
      rw [ih]
      ring

/-- On a connected variation complex, expressed by saying that the kernel of
`d₀` consists of constants, fixing one vertex anchor makes the common action
unique. -/
theorem finiteVariationComplex_commonAction_anchor_unique
    {V C₁ : Type*}
    [AddCommGroup C₁] [Module ℝ C₁]
    (d₀ : (V → ℝ) →ₗ[ℝ] C₁)
    (hconnected : ∀ f : V → ℝ, d₀ f = 0 →
      ∃ c : ℝ, f = fun _ => c)
    (α : C₁) (S T : V → ℝ) (anchor : V)
    (hS : d₀ S = α) (hT : d₀ T = α)
    (hanchor : S anchor = T anchor) : S = T := by
  have hzero : d₀ (S - T) = 0 := by
    rw [map_sub, hS, hT, sub_self]
  obtain ⟨c, hc⟩ := hconnected (S - T) hzero
  funext v
  have hv := congrFun hc v
  have ha := congrFun hc anchor
  simp only [Pi.sub_apply] at hv ha
  linarith

/-- Quantitative finite Hodge obstruction.  The exact component supplies a
competitor in `Ran d₀`; orthogonality gives Pythagoras, and the coexact
singular-value floor controls the remaining component by the measured curl. -/
theorem finiteVariationComplex_hodge_distance_bound
    {C₀ C₁ C₂ : Type*}
    [NormedAddCommGroup C₀] [InnerProductSpace ℝ C₀]
    [NormedAddCommGroup C₁] [InnerProductSpace ℝ C₁]
    [NormedAddCommGroup C₂] [InnerProductSpace ℝ C₂]
    (d₀ : C₀ →ₗ[ℝ] C₁) (d₁ : C₁ →ₗ[ℝ] C₂)
    (α : C₁) (S : C₀) (har coex : C₁) (σ : ℝ)
    (hdecomp : α = d₀ S + har + coex)
    (hhc : ⟪har, coex⟫_ℝ = 0)
    (hcurlExact : d₁ (d₀ S) = 0) (hcurlHar : d₁ har = 0)
    (hσ : 0 < σ) (hfloor : σ * ‖coex‖ ≤ ‖d₁ coex‖) :
    Metric.infDist α (d₀.range : Set C₁) ^ 2 ≤
      ‖har‖ ^ 2 + σ⁻¹ ^ 2 * ‖d₁ α‖ ^ 2 := by
  have hcurl : d₁ α = d₁ coex := by
    rw [hdecomp, map_add, map_add, hcurlExact, hcurlHar, zero_add, zero_add]
  have hdist : Metric.infDist α (d₀.range : Set C₁) ≤ ‖har + coex‖ := by
    have hmem : d₀ S ∈ d₀.range := ⟨S, rfl⟩
    calc
      Metric.infDist α (d₀.range : Set C₁)
          ≤ dist α (d₀ S) := Metric.infDist_le_dist_of_mem hmem
      _ = ‖har + coex‖ := by
        rw [dist_eq_norm, hdecomp]
        congr 1
        abel
  have hdist_nonneg : 0 ≤ Metric.infDist α (d₀.range : Set C₁) :=
    Metric.infDist_nonneg
  have hnorm : ‖har + coex‖ ^ 2 = ‖har‖ ^ 2 + ‖coex‖ ^ 2 := by
    rw [norm_add_sq_real, hhc]
    ring
  have hcoex : ‖coex‖ ≤ σ⁻¹ * ‖d₁ α‖ := by
    rw [hcurl]
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hσ).2 (by simpa [mul_comm] using hfloor)
  have hcoex_nonneg : 0 ≤ ‖coex‖ := norm_nonneg _
  have hrhs_nonneg : 0 ≤ σ⁻¹ * ‖d₁ α‖ := mul_nonneg (by positivity) (norm_nonneg _)
  have hcoex_sq : ‖coex‖ ^ 2 ≤ (σ⁻¹ * ‖d₁ α‖) ^ 2 := by nlinarith
  have hdist_sq : Metric.infDist α (d₀.range : Set C₁) ^ 2 ≤
      ‖har + coex‖ ^ 2 := by
    nlinarith [norm_nonneg (har + coex)]
  rw [hnorm] at hdist_sq
  calc
    Metric.infDist α (d₀.range : Set C₁) ^ 2
        ≤ ‖har‖ ^ 2 + ‖coex‖ ^ 2 := hdist_sq
    _ ≤ ‖har‖ ^ 2 + (σ⁻¹ * ‖d₁ α‖) ^ 2 := by linarith
    _ = ‖har‖ ^ 2 + σ⁻¹ ^ 2 * ‖d₁ α‖ ^ 2 := by ring

end NCG
