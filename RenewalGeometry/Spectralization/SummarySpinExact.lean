/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.OperatorLimits.FlatTorusSpinAtlas
import RenewalGeometry.Spectralization.DensitySymmetricSpinDiracExact

/-!
# Additional spin continuum results (assembly)

Paper `predictive_spectral_geometry`, label `thm:summary-spin`, assembled from its component
records.

* (i) the covariant Wilson construction has one low-energy species (the frozen symbol vanishes
  only at `θ = 0` on the Brillouin torus, `FrozenWilsonSymbol.frozenSymbol_eq_zero_iff`) and
  satisfies the local uniform graph estimate `eq:supp-general-Garding` for the operator with
  variable coefficients and spin links (`CovariantWilsonGarding.covariant_garding`,
  `thm:supp-general-Wilson-ellipticity`).
* (ii) on the flat periodic spin torus with constant metric and the periodic spin structure
  the uniform covariant Wilson discretization satisfies the global stability and
  core-consistency conditions (`FlatTorusSpinAtlas.atlas`, an instance of the compatible stable
  atlas) and converges in generalized norm-resolvent sense to the doubled Dirac operator
  (`FlatTorusSpinAtlas.flatTorusSpin_norm_resolvent`, `cor:supp-flat-torus-spin`).
* (iii) for a compatible stable spin discretization (`def:stable-spin-atlas`, the atlas
  `CompatibleStableAtlas`), `‖W_h (D_h - z)⁻¹ W_h^* - (D̂ - z)⁻¹‖ → 0` for every non-real `z`
  (`eq:summary-spin-resolvent`, `CompatibleStableAtlas.compactSpinMain_norm_resolvent`).

Inherited renderings: in (iii) the closed spin manifold enters only through the abstract atlas
of `def:stable-spin-atlas` (a Hilbert space with a self-adjoint operator given by resolvent data,
a compact Sobolev embedding and finite stages), exactly as in that record; in (ii) the space
`L²(𝕋ᵈ; ℂ^K)` is realised componentwise as `⊕_{a<K} L²(𝕋ᵈ)`.
-/

open Filter Topology Matrix
open scoped lp
open RenewalGeometry.FrozenWilsonSymbol RenewalGeometry.FrozenWilsonGarding
  RenewalGeometry.VariableWilsonGarding RenewalGeometry.CovariantWilsonGarding
  RenewalGeometry.LatticeTorusPlancherel RenewalGeometry.FlatTorusSpinAtlas

namespace RenewalGeometry.SummarySpin

universe u v w

/-- **`thm:summary-spin` (Additional spin continuum results)**, assembled from its component
records; see the module docstring for the clause-by-clause correspondence. -/
theorem summary_spin :
    -- (i) one low-energy species and the local uniform graph estimate of the covariant
    -- (spin-link) Wilson operator
    (∀ {d N : ℕ} (h ϖ : ℝ), h ≠ 0 → ϖ ≠ 0 → ∀ [NeZero N]
      (c : Fin d → Matrix (Fin N) (Fin N) ℂ) (Γ : Matrix (Fin N) (Fin N) ℂ)
      (g : Matrix (Fin d) (Fin d) ℝ), DoubledCliffordData c Γ g →
      (∀ ξ : Fin d → ℝ, 0 ≤ ∑ j, ∑ k, g j k * (ξ j * ξ k)) → ∀ (θ : Fin d → ℝ),
      frozenSymbol h ϖ c Γ θ = 0 ↔ ∀ j, ∃ n : ℤ, θ j = n * (2 * Real.pi)) ∧
    (∀ {d n N : ℕ} [NeZero n] (h ϖ lam Lam : ℝ), 0 < h → 0 < lam → ϖ ≠ 0 → 0 ≤ Lam →
      ∀ (c : CoefficientField d n N) (U : TorusLinks d n N) (Γ : Matrix (Fin N) (Fin N) ℂ),
      Γᴴ = Γ →
      ∀ {m : ℕ} (χ : Fin m → Grid d n → ℝ), (∀ x, ∑ α, χ α x ^ 2 = 1) →
      ∀ (x₀ : Fin m → Grid d n), (∀ α, UniformlyElliptic (c (x₀ α)) Γ lam Lam) →
      ∀ {ω K L B G CU : ℝ}, 0 ≤ ω → 0 ≤ K → 0 ≤ L → 0 ≤ B → 0 ≤ G → 0 ≤ CU →
      (∀ α (j : Fin d) x, |χ α (x + Pi.single j 1) - χ α x| ≤ h * K) →
      (∀ x j w, euclNormSq (c x j *ᵥ w) ≤ B ^ 2 * euclNormSq w) →
      (∀ w, euclNormSq (Γ *ᵥ w) ≤ G ^ 2 * euclNormSq w) →
      (∀ α (j : Fin d) x, NearSupport (χ α) j x →
        ∀ w, euclNormSq ((c x j - c (x₀ α) j) *ᵥ w) ≤ ω ^ 2 * euclNormSq w) →
      (∀ (j : Fin d) x w,
        euclNormSq ((c (x + Pi.single j 1) j - c x j) *ᵥ w) ≤ (h * L) ^ 2 * euclNormSq w) →
      4 * d * ω ^ 2 * frozenConstant lam ϖ ≤ 1 → LinkBound h U CU →
      ∀ (u : TorusSection d n N),
      h1NormSq h u ≤ covariantGardingConstant d m lam ϖ K L B G CU *
        (gridNormSq h (covVarWilson h ϖ c U Γ u) + gridNormSq h u)) ∧
    -- (ii) the flat periodic spin torus: the uniform covariant Wilson discretization satisfies
    -- the global stability and core-consistency conditions (it is a compatible stable atlas) ...
    (∀ {d K : ℕ} (D : DoubledFlatData d K),
      ∃ A : CompatibleStableAtlas (SpinorL2 d K) ℓ²(Idx d K, ℂ) (fun n => Stage d K (n + 1)),
        (∀ n, A.stage n = stage d K (n + 1) D.ϖ D.c D.Γ) ∧ (∀ n, A.embed n = embed d K (n + 1)) ∧
        A.limit = dirac D.herm) ∧
    -- ... and converges in generalized norm-resolvent sense to the doubled Dirac operator
    (∀ {d M : ℕ} (c₀ : Fin d → Matrix (Fin M) (Fin M) ℂ) (g : Matrix (Fin d) (Fin d) ℝ)
      (hherm : ∀ j, (c₀ j)ᴴ = c₀ j)
      (hcl : ∀ j k, c₀ j * c₀ k + c₀ k * c₀ j =
        ((2 * g j k : ℝ) : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))
      (hg : g.PosDef) (ϖ : ℝ) (hϖ : 0 < ϖ) {z : ℂ} (hz : z.im ≠ 0),
      Tendsto (fun n : ℕ =>
        ‖(embed d (M * 2) (n + 1)).toContinuousLinearMap ∘L
            Ring.inverse (stage d (M * 2) (n + 1) ϖ (fun j => dbl (c₀ j) σ₁) (dbl 1 σ₂) -
              z • (1 : Stage d (M * 2) (n + 1) →L[ℂ] _)) ∘L
            ContinuousLinearMap.adjoint (embed d (M * 2) (n + 1)).toContinuousLinearMap -
          (dirac (ofUndoubled c₀ g hherm hcl hg ϖ hϖ).herm).resolvent z hz‖) atTop (𝓝 0)) ∧
    -- (iii) norm-resolvent convergence for compatible stable spin discretizations
    (∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
      {Hn : ℕ → Type w} [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
      [∀ n, CompleteSpace (Hn n)] [∀ n, FiniteDimensional ℂ (Hn n)]
      (A : CompatibleStableAtlas H V Hn) (z : ℂ) (hz : z.im ≠ 0),
      Tendsto (fun n => ‖A.embeddedResolvent z hz n - A.limit.resolvent z hz‖) atTop (𝓝 0)) :=
  ⟨fun h ϖ hh hϖ => fun c Γ g hc hg θ => frozenSymbol_eq_zero_iff h ϖ hh hϖ c Γ g hc hg θ,
    fun h ϖ lam Lam hh hlam hϖ hLam c U Γ hΓ => fun χ hpart x₀ hell =>
      fun hω hK hL hB hG hCU hgrad hc hΓb hfreeze hLip habs hU u =>
        covariant_garding h ϖ lam Lam hh hlam hϖ hLam c U Γ hΓ χ hpart x₀ hell hω hK hL hB hG
          hCU hgrad hc hΓb hfreeze hLip habs hU u,
    fun D => ⟨atlas D, fun _ => rfl, fun _ => rfl, rfl⟩,
    fun c₀ g hherm hcl hg ϖ hϖ _ hz => flatTorusSpin_norm_resolvent c₀ g hherm hcl hg ϖ hϖ hz,
    fun A z hz => A.compactSpinMain_norm_resolvent z hz⟩

/-! ### The flat torus from a constant oriented frame -/

section frame

open RenewalGeometry.DensitySymmetricSpinDirac

variable {d M : ℕ}

/-- The Clifford coefficients `c^k = E_a^k γ_a` of Hermitian Clifford matrices are Hermitian. -/
theorem cliffordCoeff_conjTranspose (E : Matrix (Fin d) (Fin d) ℝ)
    (γ : Fin d → Matrix (Fin M) (Fin M) ℂ) (hγh : ∀ a, (γ a)ᴴ = γ a) (k : Fin d) :
    (cliffordCoeff E γ k)ᴴ = cliffordCoeff E γ k := by
  simp only [cliffordCoeff, cliffordMap, conjTranspose_sum, conjTranspose_smul, hγh,
    Complex.star_def, Complex.conj_ofReal]

/-- The inverse metric `g = Eᵀ E` of an invertible constant frame is positive definite. -/
theorem ginv_posDef (E e : Matrix (Fin d) (Fin d) ℝ) (hEe : E * e = 1) : (ginv E).PosDef := by
  have heE : e * E = 1 := mul_eq_one_comm.mp hEe
  have hinj : Function.Injective E.mulVec := by
    intro v w hvw
    have := congrArg (fun u => e *ᵥ u) hvw
    simpa only [mulVec_mulVec, heE, one_mulVec] using this
  have := Matrix.PosDef.conjTranspose_mul_self E hinj
  rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- **`cor:supp-flat-torus-spin` from a constant frame**: for a constant invertible frame
`E_a^j` (coframe `e`, `E e = I`) and Hermitian Clifford matrices `γ_a`, the Clifford
coefficients `c^j = E_a^j γ_a` and the flat metric `g = Eᵀ E` satisfy the hypotheses of
`flatTorusSpin_norm_resolvent`, so the uniform covariant Wilson discretization converges in
generalized norm-resolvent sense to `D̂ = Σ_j (c^j ⊗ σ₁)(-i∂_j)` on `L²(𝕋ᵈ; ℂ^M ⊗ ℂ²)`. -/
theorem flatTorusSpin_norm_resolvent_ofFrame (E e : Matrix (Fin d) (Fin d) ℝ) (hEe : E * e = 1)
    (γ : Fin d → Matrix (Fin M) (Fin M) ℂ) (hγ : IsClifford γ) (hγh : ∀ a, (γ a)ᴴ = γ a)
    (ϖ : ℝ) (hϖ : 0 < ϖ) {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun n : ℕ =>
      ‖(embed d (M * 2) (n + 1)).toContinuousLinearMap ∘L
          Ring.inverse (stage d (M * 2) (n + 1) ϖ (fun j => dbl (cliffordCoeff E γ j) σ₁)
            (dbl 1 σ₂) - z • (1 : Stage d (M * 2) (n + 1) →L[ℂ] _)) ∘L
          ContinuousLinearMap.adjoint (embed d (M * 2) (n + 1)).toContinuousLinearMap -
        (dirac (ofUndoubled (fun j => cliffordCoeff E γ j) (ginv E)
          (cliffordCoeff_conjTranspose E γ hγh) (cliffordCoeff_anticomm (E := E) hγ)
          (ginv_posDef E e hEe) ϖ hϖ).herm).resolvent z hz‖) atTop (𝓝 0) :=
  flatTorusSpin_norm_resolvent _ _ _ _ _ ϖ hϖ hz

end frame

end RenewalGeometry.SummarySpin
