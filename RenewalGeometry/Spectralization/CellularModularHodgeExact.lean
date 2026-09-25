/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
/-!
# Cellular modular Hodge reconstruction

This file covers `thm:supp-modular-Hodge` and the case-split clauses (M1)–(M3) of
`cor:supp-modular-trichotomy` of `papers/predictive_spectral_geometry`.

Let `C⁰ →d₀ C¹ →d₁ C² →d₂ C³` be a finite real Hilbert complex and
`ℋ¹ = ker d₁ ⊓ ker d₀*` its harmonic one-cochains.  For `a ∈ C¹` put
`h_a = P_{ℋ¹} a` and `F_a = d₁ a`.  We prove

* the orthogonal decomposition `a = d₀ φ + h_a + d₁* ψ` and its uniqueness
  (`exists_hodge_decomposition`, `hodge_decomposition_unique`);
* the coexact reconstruction `P_{Ran d₁*} a = d₁* G F_a` for every generalised
  inverse `G` of `d₁ d₁*` (`T G T = T`, which the Moore–Penrose inverse satisfies);
  a spectral generalised inverse is constructed (`spectralGeneralizedInverse`);
* injectivity of `[a]_gauge ↦ (h_a, F_a)` and surjectivity onto `ℋ¹ ⊕ Ran d₁` with
  the canonical representative `a_{h,F} = h + d₁* G F`;
* the Bianchi identity `d₂ F_a = 0` and the norm identity
  `‖a‖² = ‖d₀ φ‖² + ‖h_a‖² + ⟪F_a, G F_a⟫`.

The packaged statement is `cellular_modular_hodge`; the trichotomy case split is
`modular_trichotomy`.
-/

open scoped InnerProductSpace
open Finset

namespace RenewalGeometry
namespace CellularModularHodge

/-! ## Generalised inverses of symmetric endomorphisms -/

section GeneralizedInverse

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- Reciprocal on the support: `μ⁻¹` for `μ ≠ 0` and `0` for `μ = 0`. -/
noncomputable def reciprocalOnSupport (μ : ℝ) : ℝ := if μ = 0 then 0 else μ⁻¹

theorem reciprocalOnSupport_mul_mul (μ : ℝ) : reciprocalOnSupport μ * μ * μ = μ := by
  unfold reciprocalOnSupport
  split_ifs with h
  · simp [h]
  · field_simp

/-- The spectral generalised inverse of a symmetric endomorphism: invert the nonzero
eigenvalues in an orthonormal eigenbasis (the Moore–Penrose inverse). -/
noncomputable def spectralGeneralizedInverse {T : W →ₗ[ℝ] W} (hT : T.IsSymmetric) :
    W →ₗ[ℝ] W where
  toFun x := ∑ i, (reciprocalOnSupport (hT.eigenvalues (n := Module.finrank ℝ W) rfl i) *
    ⟪hT.eigenvectorBasis (n := Module.finrank ℝ W) rfl i, x⟫_ℝ) •
      hT.eigenvectorBasis (n := Module.finrank ℝ W) rfl i
  map_add' x y := by
    simp only [inner_add_right, mul_add, add_smul, sum_add_distrib]
  map_smul' t x := by
    simp only [inner_smul_right, RingHom.id_apply, smul_sum, smul_smul]
    refine sum_congr rfl fun i _ => ?_
    congr 1
    ring

/-- `T G T = T` for the spectral generalised inverse. -/
theorem spectralGeneralizedInverse_comp {T : W →ₗ[ℝ] W} (hT : T.IsSymmetric) :
    T ∘ₗ spectralGeneralizedInverse hT ∘ₗ T = T := by
  set b := hT.eigenvectorBasis (n := Module.finrank ℝ W) rfl with hb
  set μ := hT.eigenvalues (n := Module.finrank ℝ W) rfl with hμ
  have hTb : ∀ i, T (b i) = μ i • b i := fun i => by
    have := hT.apply_eigenvectorBasis (n := Module.finrank ℝ W) rfl i
    simpa [hb, hμ] using this
  ext x
  simp only [LinearMap.comp_apply]
  have hG : spectralGeneralizedInverse hT (T x) =
      ∑ i, (reciprocalOnSupport (μ i) * (μ i * ⟪b i, x⟫_ℝ)) • b i := by
    change ∑ i : Fin (Module.finrank ℝ W), _ = _
    refine sum_congr rfl fun i _ => ?_
    congr 2
    rw [← hT (b i) x, hTb i, real_inner_smul_left]
  conv_rhs => rw [← b.sum_repr' x]
  rw [hG, map_sum, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, hTb i, smul_smul, smul_smul]
  congr 1
  have := reciprocalOnSupport_mul_mul (μ i)
  linear_combination (⟪b i, x⟫_ℝ) * this

/-- Every symmetric endomorphism of a finite-dimensional real inner product space has a
generalised inverse `G` with `T G T = T`. -/
theorem exists_generalizedInverse {T : W →ₗ[ℝ] W} (hT : T.IsSymmetric) :
    ∃ G : W →ₗ[ℝ] W, T ∘ₗ G ∘ₗ T = T :=
  ⟨spectralGeneralizedInverse hT, spectralGeneralizedInverse_comp hT⟩

end GeneralizedInverse

/-! ## The finite real Hilbert complex -/

variable {C₀ C₁ C₂ C₃ : Type*}
  [NormedAddCommGroup C₀] [InnerProductSpace ℝ C₀] [FiniteDimensional ℝ C₀]
  [NormedAddCommGroup C₁] [InnerProductSpace ℝ C₁] [FiniteDimensional ℝ C₁]
  [NormedAddCommGroup C₂] [InnerProductSpace ℝ C₂] [FiniteDimensional ℝ C₂]
  [NormedAddCommGroup C₃] [InnerProductSpace ℝ C₃] [FiniteDimensional ℝ C₃]

variable (d₀ : C₀ →ₗ[ℝ] C₁) (d₁ : C₁ →ₗ[ℝ] C₂)

/-- The harmonic one-cochains `ℋ¹ = ker d₁ ⊓ ker d₀*`. -/
noncomputable def harmonicSpace : Submodule ℝ C₁ :=
  LinearMap.ker d₁ ⊓ LinearMap.ker (LinearMap.adjoint d₀)

/-- The harmonic part `h_a = P_{ℋ¹} a` (eq:supp-modular-hF). -/
noncomputable def harmonicPart (a : C₁) : C₁ :=
  (harmonicSpace d₀ d₁).starProjection a

/-- The curvature `F_a = d₁ a` (eq:supp-modular-hF). -/
noncomputable def curvature (a : C₁) : C₂ := d₁ a

/-- The Laplace-type operator `d₁ d₁*` on two-cochains. -/
noncomputable def edgeLaplacian : C₂ →ₗ[ℝ] C₂ := d₁ ∘ₗ LinearMap.adjoint d₁

/-- The canonical representative `a_{h,F} = h + d₁* G F` (eq:supp-modular-representative). -/
noncomputable def canonicalRepresentative (G : C₂ →ₗ[ℝ] C₂) (h : C₁) (F : C₂) : C₁ :=
  h + LinearMap.adjoint d₁ (G F)

variable {d₀ d₁}

theorem mem_harmonicSpace_iff {h : C₁} :
    h ∈ harmonicSpace d₀ d₁ ↔ d₁ h = 0 ∧ LinearMap.adjoint d₀ h = 0 := by
  simp [harmonicSpace, Submodule.mem_inf, LinearMap.mem_ker]

theorem harmonicPart_mem (a : C₁) : harmonicPart d₀ d₁ a ∈ harmonicSpace d₀ d₁ :=
  Submodule.starProjection_apply_mem _ a

theorem edgeLaplacian_isSymmetric : (edgeLaplacian d₁).IsSymmetric :=
  LinearMap.isSymmetric_self_comp_adjoint d₁

/-! ### Orthogonality relations -/

/-- `⟪d₀ φ, h⟫ = 0` for harmonic `h`. -/
theorem inner_d₀_harmonic {h : C₁} (hh : h ∈ harmonicSpace d₀ d₁) (φ : C₀) :
    ⟪d₀ φ, h⟫_ℝ = 0 := by
  rw [← LinearMap.adjoint_inner_right, (mem_harmonicSpace_iff.mp hh).2, inner_zero_right]

/-- `⟪h, d₁* ψ⟫ = 0` for harmonic `h`. -/
theorem inner_harmonic_adjoint_d₁ {h : C₁} (hh : h ∈ harmonicSpace d₀ d₁) (ψ : C₂) :
    ⟪h, LinearMap.adjoint d₁ ψ⟫_ℝ = 0 := by
  rw [LinearMap.adjoint_inner_right, (mem_harmonicSpace_iff.mp hh).1, inner_zero_left]

/-- `⟪d₀ φ, d₁* ψ⟫ = 0` when `d₁ d₀ = 0`. -/
theorem inner_d₀_adjoint_d₁ (hc : d₁ ∘ₗ d₀ = 0) (φ : C₀) (ψ : C₂) :
    ⟪d₀ φ, LinearMap.adjoint d₁ ψ⟫_ℝ = 0 := by
  rw [LinearMap.adjoint_inner_right]
  have : d₁ (d₀ φ) = 0 := by
    have := LinearMap.congr_fun hc φ
    simpa using this
  rw [this, inner_zero_left]

/-- `d₀* d₁* = 0` when `d₁ d₀ = 0`. -/
theorem adjoint_d₀_adjoint_d₁ (hc : d₁ ∘ₗ d₀ = 0) (ψ : C₂) :
    LinearMap.adjoint d₀ (LinearMap.adjoint d₁ ψ) = 0 := by
  have h := LinearMap.adjoint_comp d₁ d₀
  rw [hc, map_zero] at h
  have := LinearMap.congr_fun h ψ
  simpa using this.symm

/-- `d₁ d₁* x = 0` forces `d₁* x = 0`. -/
theorem adjoint_d₁_eq_zero_of_d₁_adjoint_eq_zero {x : C₂}
    (hx : d₁ (LinearMap.adjoint d₁ x) = 0) : LinearMap.adjoint d₁ x = 0 := by
  have : ⟪LinearMap.adjoint d₁ x, LinearMap.adjoint d₁ x⟫_ℝ = 0 := by
    rw [LinearMap.adjoint_inner_left, hx, inner_zero_right]
  exact inner_self_eq_zero.mp this

/-- `d₀ φ + d₁* ψ ⊥ ℋ¹`. -/
theorem d₀_add_adjoint_d₁_mem_orthogonal (φ : C₀) (ψ : C₂) :
    d₀ φ + LinearMap.adjoint d₁ ψ ∈ (harmonicSpace d₀ d₁)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro h hh
  rw [inner_add_right, real_inner_comm, inner_d₀_harmonic hh, inner_harmonic_adjoint_d₁ hh,
    add_zero]

/-- `d₀ φ + h ⊥ Ran d₁*` for harmonic `h`. -/
theorem d₀_add_harmonic_mem_orthogonal_range (hc : d₁ ∘ₗ d₀ = 0) (φ : C₀) {h : C₁}
    (hh : h ∈ harmonicSpace d₀ d₁) :
    d₀ φ + h ∈ (LinearMap.range (LinearMap.adjoint d₁))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  obtain ⟨ψ, rfl⟩ := LinearMap.mem_range.mp hu
  rw [inner_add_right, real_inner_comm, inner_d₀_adjoint_d₁ hc, real_inner_comm,
    inner_harmonic_adjoint_d₁ hh, add_zero]

/-! ### The Hodge decomposition -/

/-- Any decomposition `a = d₀ φ + h + d₁* ψ` with harmonic `h` has `h = h_a`. -/
theorem harmonicPart_eq_of_decomposition {a h : C₁} {φ : C₀} {ψ : C₂}
    (hh : h ∈ harmonicSpace d₀ d₁) (ha : a = d₀ φ + h + LinearMap.adjoint d₁ ψ) :
    harmonicPart d₀ d₁ a = h :=
  Submodule.eq_starProjection_of_mem_orthogonal' hh (d₀_add_adjoint_d₁_mem_orthogonal φ ψ)
    (by rw [ha]; abel)

/-- Existence of the Hodge decomposition `a = d₀ φ + h_a + d₁* ψ`
(eq:supp-modular-Hodge). -/
theorem exists_hodge_decomposition (hc : d₁ ∘ₗ d₀ = 0) (a : C₁) :
    ∃ (φ : C₀) (ψ : C₂), a = d₀ φ + harmonicPart d₀ d₁ a + LinearMap.adjoint d₁ ψ := by
  obtain ⟨y, hy, r, hr, hyr⟩ := (LinearMap.range d₀).exists_add_mem_mem_orthogonal a
  obtain ⟨φ, rfl⟩ := LinearMap.mem_range.mp hy
  obtain ⟨k, hk, s, hs, hks⟩ := (LinearMap.ker d₁).exists_add_mem_mem_orthogonal r
  rw [LinearMap.orthogonal_ker] at hs
  obtain ⟨ψ, rfl⟩ := LinearMap.mem_range.mp hs
  have hr0 : LinearMap.adjoint d₀ r = 0 := by
    have : ⟪LinearMap.adjoint d₀ r, LinearMap.adjoint d₀ r⟫_ℝ = 0 := by
      rw [LinearMap.adjoint_inner_left, real_inner_comm]
      exact Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self d₀ _) hr
    exact inner_self_eq_zero.mp this
  have hkh : k ∈ harmonicSpace d₀ d₁ := by
    rw [mem_harmonicSpace_iff]
    refine ⟨LinearMap.mem_ker.mp hk, ?_⟩
    have hk' : k = r - LinearMap.adjoint d₁ ψ := by rw [hks]; abel
    rw [hk', map_sub, hr0, adjoint_d₀_adjoint_d₁ hc, sub_zero]
  have ha : a = d₀ φ + k + LinearMap.adjoint d₁ ψ := by rw [hyr, hks]; abel
  refine ⟨φ, ψ, ?_⟩
  rw [harmonicPart_eq_of_decomposition hkh ha]
  exact ha

/-- Uniqueness of the Hodge decomposition: the exact, harmonic and coexact summands are
determined by `a`. -/
theorem hodge_decomposition_unique (hc : d₁ ∘ₗ d₀ = 0) {φ φ' : C₀} {h h' : C₁} {ψ ψ' : C₂}
    (hh : h ∈ harmonicSpace d₀ d₁) (hh' : h' ∈ harmonicSpace d₀ d₁)
    (e : d₀ φ + h + LinearMap.adjoint d₁ ψ = d₀ φ' + h' + LinearMap.adjoint d₁ ψ') :
    d₀ φ = d₀ φ' ∧ h = h' ∧ LinearMap.adjoint d₁ ψ = LinearMap.adjoint d₁ ψ' := by
  have hhh : h = h' := by
    rw [← harmonicPart_eq_of_decomposition hh rfl, e, harmonicPart_eq_of_decomposition hh' rfl]
  subst hhh
  have hv : d₀ (φ - φ') = LinearMap.adjoint d₁ (ψ' - ψ) := by
    rw [map_sub, map_sub, sub_eq_sub_iff_add_eq_add]
    calc d₀ φ + LinearMap.adjoint d₁ ψ = (d₀ φ + h + LinearMap.adjoint d₁ ψ) - h := by abel
      _ = (d₀ φ' + h + LinearMap.adjoint d₁ ψ') - h := by rw [e]
      _ = LinearMap.adjoint d₁ ψ' + d₀ φ' := by abel
  have hv0 : d₀ (φ - φ') = 0 := by
    have : ⟪d₀ (φ - φ'), d₀ (φ - φ')⟫_ℝ = 0 := by
      have := inner_d₀_adjoint_d₁ hc (φ - φ') (ψ' - ψ)
      rwa [← hv] at this
    exact inner_self_eq_zero.mp this
  refine ⟨?_, rfl, ?_⟩
  · rw [map_sub, sub_eq_zero] at hv0; exact hv0
  · rw [hv0, map_sub, eq_comm, sub_eq_zero] at hv; exact hv.symm

/-! ### Coexact reconstruction from the curvature -/

/-- The curvature of a decomposed cochain is `F_a = d₁ d₁* ψ`. -/
theorem curvature_eq_edgeLaplacian (hc : d₁ ∘ₗ d₀ = 0) {a h : C₁} {φ : C₀} {ψ : C₂}
    (hh : h ∈ harmonicSpace d₀ d₁) (ha : a = d₀ φ + h + LinearMap.adjoint d₁ ψ) :
    curvature d₁ a = edgeLaplacian d₁ ψ := by
  have h1 : d₁ (d₀ φ) = 0 := by
    have := LinearMap.congr_fun hc φ
    simpa using this
  simp only [curvature, edgeLaplacian, LinearMap.comp_apply, ha, map_add, h1,
    (mem_harmonicSpace_iff.mp hh).1, zero_add]

/-- Coexact reconstruction (eq:supp-modular-coexact), summand form: for any generalised
inverse `G` of `d₁ d₁*`, the coexact summand of the decomposition is `d₁* G F_a`. -/
theorem adjoint_d₁_eq_adjoint_d₁_generalizedInverse_curvature (hc : d₁ ∘ₗ d₀ = 0)
    {G : C₂ →ₗ[ℝ] C₂} (hG : edgeLaplacian d₁ ∘ₗ G ∘ₗ edgeLaplacian d₁ = edgeLaplacian d₁)
    {a h : C₁} {φ : C₀} {ψ : C₂} (hh : h ∈ harmonicSpace d₀ d₁)
    (ha : a = d₀ φ + h + LinearMap.adjoint d₁ ψ) :
    LinearMap.adjoint d₁ ψ = LinearMap.adjoint d₁ (G (curvature d₁ a)) := by
  rw [curvature_eq_edgeLaplacian hc hh ha]
  have hT := LinearMap.congr_fun hG ψ
  simp only [LinearMap.comp_apply] at hT
  have h0 : d₁ (LinearMap.adjoint d₁ (G (edgeLaplacian d₁ ψ) - ψ)) = 0 := by
    rw [map_sub, map_sub]
    change edgeLaplacian d₁ (G (edgeLaplacian d₁ ψ)) - edgeLaplacian d₁ ψ = 0
    rw [hT, sub_self]
  have := adjoint_d₁_eq_zero_of_d₁_adjoint_eq_zero h0
  rw [map_sub, sub_eq_zero] at this
  exact this.symm

/-- Coexact reconstruction (eq:supp-modular-coexact), projection form:
`P_{Ran d₁*} a = d₁* G F_a`. -/
theorem starProjection_range_adjoint_eq (hc : d₁ ∘ₗ d₀ = 0)
    {G : C₂ →ₗ[ℝ] C₂} (hG : edgeLaplacian d₁ ∘ₗ G ∘ₗ edgeLaplacian d₁ = edgeLaplacian d₁)
    (a : C₁) :
    (LinearMap.range (LinearMap.adjoint d₁)).starProjection a =
      LinearMap.adjoint d₁ (G (curvature d₁ a)) := by
  obtain ⟨φ, ψ, ha⟩ := exists_hodge_decomposition hc a
  rw [← adjoint_d₁_eq_adjoint_d₁_generalizedInverse_curvature hc hG (harmonicPart_mem a) ha]
  exact Submodule.eq_starProjection_of_mem_orthogonal' (LinearMap.mem_range_self _ ψ)
    (d₀_add_harmonic_mem_orthogonal_range hc φ (harmonicPart_mem a)) (ha.trans (by abel))

/-! ### The gauge map `[a] ↦ (h_a, F_a)` -/

/-- Injectivity (eq:supp-modular-gauge-map): equal harmonic parts and curvatures force
`a - b ∈ Ran d₀`. -/
theorem sub_mem_range_d₀_of_harmonicPart_eq_of_curvature_eq (hc : d₁ ∘ₗ d₀ = 0) {a b : C₁}
    (hh : harmonicPart d₀ d₁ a = harmonicPart d₀ d₁ b) (hF : curvature d₁ a = curvature d₁ b) :
    a - b ∈ LinearMap.range d₀ := by
  obtain ⟨φ, ψ, ha⟩ := exists_hodge_decomposition hc a
  obtain ⟨φ', ψ', hb⟩ := exists_hodge_decomposition hc b
  have hcoex : LinearMap.adjoint d₁ (ψ - ψ') = 0 := by
    apply adjoint_d₁_eq_zero_of_d₁_adjoint_eq_zero
    have e1 := curvature_eq_edgeLaplacian hc (harmonicPart_mem a) ha
    have e2 := curvature_eq_edgeLaplacian hc (harmonicPart_mem b) hb
    change edgeLaplacian d₁ (ψ - ψ') = 0
    rw [map_sub, ← e1, ← e2, hF, sub_self]
  refine ⟨φ - φ', ?_⟩
  rw [map_sub] at hcoex ⊢
  rw [sub_eq_zero] at hcoex
  rw [ha, hb, hh, hcoex]
  abel

/-- The canonical representative has harmonic part `h`. -/
theorem harmonicPart_canonicalRepresentative (G : C₂ →ₗ[ℝ] C₂) {h : C₁}
    (hh : h ∈ harmonicSpace d₀ d₁) (F : C₂) :
    harmonicPart d₀ d₁ (canonicalRepresentative d₁ G h F) = h := by
  refine Submodule.eq_starProjection_of_mem_orthogonal' hh ?_ rfl
  rw [Submodule.mem_orthogonal]
  intro k hk
  exact inner_harmonic_adjoint_d₁ hk _

/-- The canonical representative has curvature `F` for every `F ∈ Ran d₁`
(surjectivity in eq:supp-modular-gauge-map). -/
theorem curvature_canonicalRepresentative (hc : d₁ ∘ₗ d₀ = 0)
    {G : C₂ →ₗ[ℝ] C₂} (hG : edgeLaplacian d₁ ∘ₗ G ∘ₗ edgeLaplacian d₁ = edgeLaplacian d₁)
    {h : C₁} (hh : h ∈ harmonicSpace d₀ d₁) {F : C₂} (hF : F ∈ LinearMap.range d₁) :
    curvature d₁ (canonicalRepresentative d₁ G h F) = F := by
  obtain ⟨b, rfl⟩ := LinearMap.mem_range.mp hF
  obtain ⟨φ, ψ, hb⟩ := exists_hodge_decomposition hc b
  have hFb : d₁ b = edgeLaplacian d₁ ψ := curvature_eq_edgeLaplacian hc (harmonicPart_mem b) hb
  simp only [curvature, canonicalRepresentative, map_add, (mem_harmonicSpace_iff.mp hh).1,
    zero_add]
  change edgeLaplacian d₁ (G (d₁ b)) = d₁ b
  rw [hFb]
  have := LinearMap.congr_fun hG ψ
  simpa using this

/-! ### Bianchi identity and the norm identity -/

/-- Bianchi identity `d₂ F_a = 0`. -/
theorem d₂_curvature (d₂ : C₂ →ₗ[ℝ] C₃) (hc₂ : d₂ ∘ₗ d₁ = 0) (a : C₁) :
    d₂ (curvature d₁ a) = 0 := by
  have := LinearMap.congr_fun hc₂ a
  simpa [curvature] using this

/-- `⟪F_a, G F_a⟫ = ‖d₁* ψ‖²` for the coexact summand. -/
theorem inner_curvature_generalizedInverse (hc : d₁ ∘ₗ d₀ = 0)
    {G : C₂ →ₗ[ℝ] C₂} (hG : edgeLaplacian d₁ ∘ₗ G ∘ₗ edgeLaplacian d₁ = edgeLaplacian d₁)
    {a h : C₁} {φ : C₀} {ψ : C₂} (hh : h ∈ harmonicSpace d₀ d₁)
    (ha : a = d₀ φ + h + LinearMap.adjoint d₁ ψ) :
    ⟪curvature d₁ a, G (curvature d₁ a)⟫_ℝ = ‖LinearMap.adjoint d₁ ψ‖ ^ 2 := by
  rw [curvature_eq_edgeLaplacian hc hh ha, edgeLaplacian_isSymmetric ψ]
  have hT := LinearMap.congr_fun hG ψ
  simp only [LinearMap.comp_apply] at hT
  rw [hT]
  change ⟪ψ, d₁ (LinearMap.adjoint d₁ ψ)⟫_ℝ = _
  rw [← LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]

/-- The norm identity (eq:supp-modular-norm):
`‖a‖² = ‖d₀ φ‖² + ‖h_a‖² + ⟪F_a, G F_a⟫`. -/
theorem norm_sq_eq (hc : d₁ ∘ₗ d₀ = 0)
    {G : C₂ →ₗ[ℝ] C₂} (hG : edgeLaplacian d₁ ∘ₗ G ∘ₗ edgeLaplacian d₁ = edgeLaplacian d₁)
    {a h : C₁} {φ : C₀} {ψ : C₂} (hh : h ∈ harmonicSpace d₀ d₁)
    (ha : a = d₀ φ + h + LinearMap.adjoint d₁ ψ) :
    ‖a‖ ^ 2 = ‖d₀ φ‖ ^ 2 + ‖h‖ ^ 2 + ⟪curvature d₁ a, G (curvature d₁ a)⟫_ℝ := by
  rw [inner_curvature_generalizedInverse hc hG hh ha, ha]
  have h1 : ⟪d₀ φ + h, LinearMap.adjoint d₁ ψ⟫_ℝ = 0 := by
    rw [inner_add_left, inner_d₀_adjoint_d₁ hc, inner_harmonic_adjoint_d₁ hh, add_zero]
  rw [norm_add_sq_real, h1, norm_add_sq_real, inner_d₀_harmonic hh φ]
  ring

/-! ## Packaged statements -/

/-- **`thm:supp-modular-Hodge` (Cellular modular Hodge reconstruction).**  For a finite
real Hilbert complex `d₀, d₁, d₂` with `d₁ d₀ = 0`, `d₂ d₁ = 0`, and any generalised
inverse `G` of `d₁ d₁*` (`T G T = T`; e.g. the Moore–Penrose inverse
`spectralGeneralizedInverse`): every `a ∈ C¹` decomposes as `a = d₀ φ + h_a + d₁* ψ` with
the three summands unique; `P_{Ran d₁*} a = d₁* G F_a`; the gauge map
`[a] ↦ (h_a, F_a)` is injective and surjective onto `ℋ¹ ⊕ Ran d₁` with canonical
representative `a_{h,F} = h + d₁* G F`; `d₂ F_a = 0`; and
`‖a‖² = ‖d₀ φ‖² + ‖h_a‖² + ⟪F_a, G F_a⟫`. -/
theorem cellular_modular_hodge (d₂ : C₂ →ₗ[ℝ] C₃) (hc : d₁ ∘ₗ d₀ = 0) (hc₂ : d₂ ∘ₗ d₁ = 0)
    {G : C₂ →ₗ[ℝ] C₂} (hG : edgeLaplacian d₁ ∘ₗ G ∘ₗ edgeLaplacian d₁ = edgeLaplacian d₁) :
    (∀ a : C₁, ∃ (φ : C₀) (ψ : C₂),
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
    (∀ a : C₁, d₂ (curvature d₁ a) = 0) := by
  refine ⟨fun a => ?_, fun hh hh' e => hodge_decomposition_unique hc hh hh' e,
    starProjection_range_adjoint_eq hc hG,
    fun a b hh hF => sub_mem_range_d₀_of_harmonicPart_eq_of_curvature_eq hc hh hF,
    fun h hh F hF => ⟨harmonicPart_canonicalRepresentative G hh F,
      curvature_canonicalRepresentative hc hG hh hF⟩,
    d₂_curvature d₂ hc₂⟩
  obtain ⟨φ, ψ, ha⟩ := exists_hodge_decomposition hc a
  exact ⟨φ, ψ, ha,
    adjoint_d₁_eq_adjoint_d₁_generalizedInverse_curvature hc hG (harmonicPart_mem a) ha,
    norm_sq_eq hc hG (harmonicPart_mem a) ha⟩

/-- `cor:supp-modular-trichotomy`, clauses (M1)–(M3): for a cellular affinity `a`, either
`F_a ≠ 0` (local face curvature), or `F_a = 0` and `h_a ≠ 0` (flat with nontrivial global
holonomy), or `F_a = h_a = 0`, in which case `a = d₀ φ` is removed by a vertex gauge. -/
theorem modular_trichotomy (hc : d₁ ∘ₗ d₀ = 0) (a : C₁) :
    curvature d₁ a ≠ 0 ∨
    (curvature d₁ a = 0 ∧ harmonicPart d₀ d₁ a ≠ 0) ∨
    (curvature d₁ a = 0 ∧ harmonicPart d₀ d₁ a = 0 ∧ ∃ φ : C₀, a = d₀ φ) := by
  by_cases hF : curvature d₁ a = 0
  · by_cases hh : harmonicPart d₀ d₁ a = 0
    · refine Or.inr (Or.inr ⟨hF, hh, ?_⟩)
      have hmem := sub_mem_range_d₀_of_harmonicPart_eq_of_curvature_eq hc (a := a) (b := 0)
        (by rw [hh, harmonicPart, map_zero]) (by rw [hF, curvature, map_zero])
      obtain ⟨φ, hφ⟩ := LinearMap.mem_range.mp hmem
      exact ⟨φ, by rw [hφ, sub_zero]⟩
    · exact Or.inr (Or.inl ⟨hF, hh⟩)
  · exact Or.inl hF

end CellularModularHodge
end RenewalGeometry
