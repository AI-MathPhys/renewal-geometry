/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.CellularModularHodgeExact
/-!
# Normalised potentials in the cellular modular Hodge decomposition

This file completes `thm:supp-modular-Hodge` of `papers/predictive_spectral_geometry` by the
sentence on potentials: in the decomposition `a = d₀ φ + h_a + d₁* ψ` of a finite real Hilbert
complex `C⁰ →d₀ C¹ →d₁ C² →d₂ C³`, the three orthogonal components are unique, while the
potentials `φ, ψ` are unique only after requiring `φ ⊥ ker d₀` and `ψ ⊥ ker d₁*`.

* `exists_normalized_hodge_decomposition`: normalised potentials exist;
* `normalized_potentials_unique`: normalised potentials are unique;
* `potentials_not_unique_of_ker_ne_bot` / `coexact_potentials_not_unique_of_ker_ne_bot`:
  without the normalisation the potentials are not unique as soon as `ker d₀ ≠ ⊥`
  (resp. `ker d₁* ≠ ⊥`);
* `cellular_modular_hodge_normalized`: the full proposition, i.e. `cellular_modular_hodge`
  together with existence and uniqueness of the normalised potentials.
-/

open scoped InnerProductSpace

namespace RenewalGeometry
namespace CellularModularHodge

variable {C₀ C₁ C₂ C₃ : Type*}
  [NormedAddCommGroup C₀] [InnerProductSpace ℝ C₀] [FiniteDimensional ℝ C₀]
  [NormedAddCommGroup C₁] [InnerProductSpace ℝ C₁] [FiniteDimensional ℝ C₁]
  [NormedAddCommGroup C₂] [InnerProductSpace ℝ C₂] [FiniteDimensional ℝ C₂]
  [NormedAddCommGroup C₃] [InnerProductSpace ℝ C₃] [FiniteDimensional ℝ C₃]

variable {d₀ : C₀ →ₗ[ℝ] C₁} {d₁ : C₁ →ₗ[ℝ] C₂}

/-- Every vector `x` of a finite-dimensional inner product space can be replaced by a vector in
`(ker T)ᗮ` with the same image under `T`. -/
theorem exists_mem_orthogonal_ker_map_eq {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] (T : E →ₗ[ℝ] F) (x : E) :
    ∃ y ∈ (LinearMap.ker T)ᗮ, T y = T x := by
  obtain ⟨k, hk, y, hy, hxy⟩ := (LinearMap.ker T).exists_add_mem_mem_orthogonal x
  refine ⟨y, hy, ?_⟩
  rw [hxy, map_add, LinearMap.mem_ker.mp hk, zero_add]

/-- A linear map is injective on `(ker T)ᗮ`. -/
theorem eq_of_mem_orthogonal_ker_of_map_eq {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] (T : E →ₗ[ℝ] F) {x y : E}
    (hx : x ∈ (LinearMap.ker T)ᗮ) (hy : y ∈ (LinearMap.ker T)ᗮ) (h : T x = T y) : x = y := by
  have hk : x - y ∈ LinearMap.ker T := by
    rw [LinearMap.mem_ker, map_sub, h, sub_self]
  have ho : x - y ∈ (LinearMap.ker T)ᗮ := Submodule.sub_mem _ hx hy
  have : x - y ∈ LinearMap.ker T ⊓ (LinearMap.ker T)ᗮ := ⟨hk, ho⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at this
  exact this

/-- `thm:supp-modular-Hodge`, existence of normalised potentials: every `a ∈ C¹` decomposes as
`a = d₀ φ + h_a + d₁* ψ` with `φ ⊥ ker d₀` and `ψ ⊥ ker d₁*`. -/
theorem exists_normalized_hodge_decomposition (hc : d₁ ∘ₗ d₀ = 0) (a : C₁) :
    ∃ (φ : C₀) (ψ : C₂), φ ∈ (LinearMap.ker d₀)ᗮ ∧
      ψ ∈ (LinearMap.ker (LinearMap.adjoint d₁))ᗮ ∧
      a = d₀ φ + harmonicPart d₀ d₁ a + LinearMap.adjoint d₁ ψ := by
  obtain ⟨φ, ψ, ha⟩ := exists_hodge_decomposition hc a
  obtain ⟨φ', hφ', e₀⟩ := exists_mem_orthogonal_ker_map_eq d₀ φ
  obtain ⟨ψ', hψ', e₁⟩ := exists_mem_orthogonal_ker_map_eq (LinearMap.adjoint d₁) ψ
  exact ⟨φ', ψ', hφ', hψ', by rw [e₀, e₁]; exact ha⟩

/-- `thm:supp-modular-Hodge`, uniqueness of normalised potentials: if
`d₀ φ + h + d₁* ψ = d₀ φ' + h' + d₁* ψ'` with `h, h'` harmonic, `φ, φ' ⊥ ker d₀` and
`ψ, ψ' ⊥ ker d₁*`, then `φ = φ'`, `h = h'` and `ψ = ψ'`. -/
theorem normalized_potentials_unique (hc : d₁ ∘ₗ d₀ = 0) {φ φ' : C₀} {h h' : C₁} {ψ ψ' : C₂}
    (hh : h ∈ harmonicSpace d₀ d₁) (hh' : h' ∈ harmonicSpace d₀ d₁)
    (hφ : φ ∈ (LinearMap.ker d₀)ᗮ) (hφ' : φ' ∈ (LinearMap.ker d₀)ᗮ)
    (hψ : ψ ∈ (LinearMap.ker (LinearMap.adjoint d₁))ᗮ)
    (hψ' : ψ' ∈ (LinearMap.ker (LinearMap.adjoint d₁))ᗮ)
    (e : d₀ φ + h + LinearMap.adjoint d₁ ψ = d₀ φ' + h' + LinearMap.adjoint d₁ ψ') :
    φ = φ' ∧ h = h' ∧ ψ = ψ' := by
  obtain ⟨e₀, eh, e₁⟩ := hodge_decomposition_unique hc hh hh' e
  exact ⟨eq_of_mem_orthogonal_ker_of_map_eq d₀ hφ hφ' e₀, eh,
    eq_of_mem_orthogonal_ker_of_map_eq _ hψ hψ' e₁⟩

/-- Without the normalisation the exact potential is not unique: if `ker d₀ ≠ ⊥`, every
decomposition `a = d₀ φ + h + d₁* ψ` admits a second one with a different `φ`. -/
theorem potentials_not_unique_of_ker_ne_bot (hk : LinearMap.ker d₀ ≠ ⊥)
    {a h : C₁} {φ : C₀} {ψ : C₂} (ha : a = d₀ φ + h + LinearMap.adjoint d₁ ψ) :
    ∃ φ' : C₀, φ' ≠ φ ∧ a = d₀ φ' + h + LinearMap.adjoint d₁ ψ := by
  obtain ⟨k, hk, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  refine ⟨φ + k, by simpa using hk0, ?_⟩
  rw [map_add, LinearMap.mem_ker.mp hk, add_zero]
  exact ha

/-- Without the normalisation the coexact potential is not unique: if `ker d₁* ≠ ⊥`, every
decomposition `a = d₀ φ + h + d₁* ψ` admits a second one with a different `ψ`. -/
theorem coexact_potentials_not_unique_of_ker_ne_bot
    (hk : LinearMap.ker (LinearMap.adjoint d₁) ≠ ⊥)
    {a h : C₁} {φ : C₀} {ψ : C₂} (ha : a = d₀ φ + h + LinearMap.adjoint d₁ ψ) :
    ∃ ψ' : C₂, ψ' ≠ ψ ∧ a = d₀ φ + h + LinearMap.adjoint d₁ ψ' := by
  obtain ⟨k, hk, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  refine ⟨ψ + k, by simpa using hk0, ?_⟩
  rw [map_add, LinearMap.mem_ker.mp hk, add_zero]
  exact ha

/-- `thm:supp-modular-Hodge` in full: the conclusions of `cellular_modular_hodge` (existence
of the orthogonal decomposition with the coexact reconstruction and the norm identity,
uniqueness of the three components, `P_{Ran d₁*} a = d₁* G F_a`, injectivity and surjectivity
of the gauge map with canonical representative, Bianchi identity) together with existence
and uniqueness of the potentials normalised by `φ ⊥ ker d₀`, `ψ ⊥ ker d₁*`. -/
theorem cellular_modular_hodge_normalized (d₂ : C₂ →ₗ[ℝ] C₃) (hc : d₁ ∘ₗ d₀ = 0)
    (hc₂ : d₂ ∘ₗ d₁ = 0)
    {G : C₂ →ₗ[ℝ] C₂} (hG : edgeLaplacian d₁ ∘ₗ G ∘ₗ edgeLaplacian d₁ = edgeLaplacian d₁) :
    ((∀ a : C₁, ∃ (φ : C₀) (ψ : C₂),
      a = d₀ φ + harmonicPart d₀ d₁ a + LinearMap.adjoint d₁ ψ ∧
      LinearMap.adjoint d₁ ψ = LinearMap.adjoint d₁ (G (curvature d₁ a)) ∧
      ‖a‖ ^ 2 = ‖d₀ φ‖ ^ 2 + ‖harmonicPart d₀ d₁ a‖ ^ 2 +
        ⟪curvature d₁ a, G (curvature d₁ a)⟫_ℝ) ∧
    (∀ {φ φ' : C₀} {h h' : C₁} {ψ ψ' : C₂}, h ∈ harmonicSpace d₀ d₁ → h' ∈ harmonicSpace d₀ d₁ →
      d₀ φ + h + LinearMap.adjoint d₁ ψ = d₀ φ' + h' + LinearMap.adjoint d₁ ψ' →
      d₀ φ = d₀ φ' ∧ h = h' ∧ LinearMap.adjoint d₁ ψ = LinearMap.adjoint d₁ ψ') ∧
    (∀ a : C₁, (LinearMap.range (LinearMap.adjoint d₁)).starProjection a =
      LinearMap.adjoint d₁ (G (curvature d₁ a))) ∧
    (∀ a b : C₁, harmonicPart d₀ d₁ a = harmonicPart d₀ d₁ b → curvature d₁ a = curvature d₁ b →
      a - b ∈ LinearMap.range d₀) ∧
    (∀ h ∈ harmonicSpace d₀ d₁, ∀ F ∈ LinearMap.range d₁,
      harmonicPart d₀ d₁ (canonicalRepresentative d₁ G h F) = h ∧
      curvature d₁ (canonicalRepresentative d₁ G h F) = F) ∧
    (∀ a : C₁, d₂ (curvature d₁ a) = 0)) ∧
    (∀ a : C₁, ∃ (φ : C₀) (ψ : C₂), φ ∈ (LinearMap.ker d₀)ᗮ ∧
      ψ ∈ (LinearMap.ker (LinearMap.adjoint d₁))ᗮ ∧
      a = d₀ φ + harmonicPart d₀ d₁ a + LinearMap.adjoint d₁ ψ) ∧
    (∀ {φ φ' : C₀} {h h' : C₁} {ψ ψ' : C₂}, h ∈ harmonicSpace d₀ d₁ → h' ∈ harmonicSpace d₀ d₁ →
      φ ∈ (LinearMap.ker d₀)ᗮ → φ' ∈ (LinearMap.ker d₀)ᗮ →
      ψ ∈ (LinearMap.ker (LinearMap.adjoint d₁))ᗮ →
      ψ' ∈ (LinearMap.ker (LinearMap.adjoint d₁))ᗮ →
      d₀ φ + h + LinearMap.adjoint d₁ ψ = d₀ φ' + h' + LinearMap.adjoint d₁ ψ' →
      φ = φ' ∧ h = h' ∧ ψ = ψ') :=
  ⟨cellular_modular_hodge d₂ hc hc₂ hG, exists_normalized_hodge_decomposition hc,
    fun hh hh' hφ hφ' hψ hψ' e => normalized_potentials_unique hc hh hh' hφ hφ' hψ hψ' e⟩

end CellularModularHodge
end RenewalGeometry
