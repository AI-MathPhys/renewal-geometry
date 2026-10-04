/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.OperatorLimits.VariableTorusDiracConsistency
import RenewalGeometry.OperatorLimits.CompatibleStableAtlasSpectralProjections
import RenewalGeometry.Spectralization.StableSpinAtlasRealGradingExact

/-!
# Norm-resolvent convergence for compatible stable atlases and the periodic extension

Paper `predictive_spectral_geometry`, `thm:supp-compact-spin-resolvent`, assembled:

* `eq:supp-global-norm-resolvent` for a compatible stable spin discretization
  (`CompatibleStableAtlas.tendsto_norm_embeddedResolvent_sub`), with the spectral-projection
  clause (`CompatibleStableAtlas.tendsto_norm_embeddedSpectralProjection_sub`);
* retention of compatible real and grading structures
  (`StableSpinAtlasRealGrading.AtlasRealGrading.tendsto_embed_stageReal_adjoint`,
  `tendsto_embed_stageGrading_adjoint`);
* `eq:supp-local-norm-resolvent` on the fixed smooth periodic coordinate extension, with
  genuinely variable coefficients, exact transport links and the covariant Wilson operator
  (`VariableTorusDirac.Coeffs.supp_local_norm_resolvent`), including the self-adjoint
  realisation `D̂_g` with domain `H¹` and the spectral projections.
-/

open Filter Topology Matrix
open scoped InnerProductSpace lp

noncomputable section

namespace RenewalGeometry.StableSpinNormResolvent

open VariableTorusDirac FlatTorusSpinAtlas CovariantWilsonGarding VariableWilsonGarding
  StableSpinAtlasRealGrading

universe u v w

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {Hn : ℕ → Type w} [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)] [∀ n, FiniteDimensional ℂ (Hn n)]

/-- **`thm:supp-compact-spin-resolvent`** (assembled).  For a compatible stable spin
discretization `A` (`def:stable-spin-atlas`) with compatible real and grading structures `S`,
and for the fixed smooth periodic coordinate extension `C` (variable continuous Hermitian `ĉ^j`
with continuous `∂_j ĉ^j`, continuous skew-Hermitian connection commuting with `Γ_⊥`, uniformly
elliptic doubled Clifford data, `ϖ ≠ 0`, exact transport links `U`) with its covariant Wilson
discretization:
1. `‖W_h (D_h - z)⁻¹ W_h^* - (D̂ - z)⁻¹‖ → 0` for every `z ∉ ℝ` (`eq:supp-global-norm-resolvent`);
2. isolated bounded-energy spectral projections converge in norm;
3. the finite real structures and gradings converge to the declared continuum actions;
4. on the periodic extension: `D̂_g` (the self-adjoint realisation of
   `-(i/2) Σ_j (ĉ^j ∇_j + ∇_j ĉ^j)` with domain `H¹`) satisfies
   `‖𝒥⁰_h (D^W_{g,h} - z)⁻¹ (𝒥⁰_h)^* - (D̂_g - z)⁻¹‖ → 0` (`eq:supp-local-norm-resolvent`), and its
   isolated bounded-energy spectral projections are the norm limits of the discrete ones. -/
theorem supp_compact_spin_resolvent (A : CompatibleStableAtlas H V Hn) (S : AtlasRealGrading A)
    {d K : ℕ} (C : VariableTorusDirac.Coeffs d K) (Γ : Matrix (Fin K) (Fin K) ℂ) (hΓ : Γᴴ = Γ)
    (hΓΩ : ∀ j y, Γ * C.Ω j y = C.Ω j y * Γ) (ϖ : ℝ) (hϖ : ϖ ≠ 0) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : 0 ≤ Lam) (hell : ∀ y, UniformlyElliptic (fun j => C.c j y) Γ lam Lam)
    (U : ∀ n, TorusLinks d (n + 1) K) (hU : ∀ n, C.IsTransportLinks (n + 1) (U n))
    {c₀ : Fin d → Matrix (Fin K) (Fin K) ℂ} (hc₀ : ∀ j, (c₀ j)ᴴ = c₀ j) :
    (∀ {z : ℂ} (hz : z.im ≠ 0),
      Tendsto (fun n => ‖A.embeddedResolvent z hz n - A.limit.resolvent z hz‖) atTop (𝓝 0)) ∧
    (∀ {a b : ℝ}, a < b → A.limit.opEigenspace (a : ℂ) = ⊥ → A.limit.opEigenspace (b : ℂ) = ⊥ →
      Tendsto (fun n => ‖A.embeddedSpectralProjection a b n - A.limit.spectralProjection a b‖)
        atTop (𝓝 0)) ∧
    (∀ f : H, Tendsto (fun n => A.embed n (S.stageReal n
      (ContinuousLinearMap.adjoint (A.embed n).toContinuousLinearMap f))) atTop
        (𝓝 (S.realJ f))) ∧
    (∀ f : H, Tendsto (fun n => A.embed n (S.stageGrading n
      (ContinuousLinearMap.adjoint (A.embed n).toContinuousLinearMap f))) atTop
        (𝓝 (S.grading f))) ∧
    (((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).dirac hc₀).op.domain =
        LinearMap.range (sobolev hc₀).toLinearMap ∧
      IsSelfAdjoint ((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).dirac hc₀).op ∧
      (∀ {z : ℂ} (hz : z.im ≠ 0), Tendsto (fun n =>
        ‖(embed d K (n + 1)).toContinuousLinearMap ∘L
          ((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).toStable hc₀).stageRes n
            hz ∘L
          ContinuousLinearMap.adjoint (embed d K (n + 1)).toContinuousLinearMap -
          ((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).dirac hc₀).resolvent z hz‖)
        atTop (𝓝 0)) ∧
      (∀ {a b : ℝ}, a < b →
        ((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).dirac hc₀).opEigenspace
          (a : ℂ) = ⊥ →
        ((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).dirac hc₀).opEigenspace
          (b : ℂ) = ⊥ →
        Tendsto (fun n =>
          ‖((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).toStable
              hc₀).toAtlas.embeddedSpectralProjection a b n -
            ((C.wilsonDiscretization Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU).dirac
              hc₀).spectralProjection a b‖) atTop (𝓝 0))) := by
  obtain ⟨-, -, hdom, hsa, -, hres, hspec⟩ :=
    C.supp_local_norm_resolvent hc₀ Γ hΓ hΓΩ ϖ hϖ hlam hLam hell U hU
  exact ⟨fun hz => A.tendsto_norm_embeddedResolvent_sub hz,
    fun hab ha hb => A.tendsto_norm_embeddedSpectralProjection_sub hab ha hb,
    S.tendsto_embed_stageReal_adjoint, S.tendsto_embed_stageGrading_adjoint,
    hdom, hsa, hres, hspec⟩

end RenewalGeometry.StableSpinNormResolvent
