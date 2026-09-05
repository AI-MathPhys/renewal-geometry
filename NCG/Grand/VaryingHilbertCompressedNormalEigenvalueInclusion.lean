/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCompressedNormalSpectralSubspacesSmallCircle

/-!
# Spectral inclusion for compressed normal varying-Hilbert operators

Every nonzero eigenvalue of the compact normal limit is approximated by eigenvalues of all
sufficiently late compressed stages. The proof uses arbitrarily small exact Riesz clusters and
stable total multiplicity.
-/

open Complex Filter Topology Module End

noncomputable section

namespace NCG.VaryingHilbert.System

universe v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
  [∀ n, CompleteSpace (Hn n)]

/-- Every nonzero eigenvalue of the compact normal limit is approximated by an eigenvalue of each
sufficiently late literal compressed stage. -/
theorem compressedOperator_eventually_exists_eigenvalue_near_of_isStarNormal
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (center : ℂ) (hcenter : center ≠ 0)
    (hcenterEigen : HasEigenvalue T.toLinearMap center)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∃ μ : ℂ,
      HasEigenvalue (J.compressedOperator Tn n).toLinearMap μ ∧
        dist μ center < δ := by
  classical
  have hTcompact : IsCompactOperator T :=
    (J.compressedOperator_tendsto_operatorNorm_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal).1
  let E : Submodule ℂ H := eigenspace T.toLinearMap center
  letI : FiniteDimensional ℂ E := by
    dsimp [E]
    exact T.finite_dimensional_eigenspace hTcompact center hcenter
  obtain ⟨y, hy⟩ := hcenterEigen.exists_hasEigenvector
  let yE : E := ⟨y, mem_eigenspace_iff.mpr hy.apply_eq_smul⟩
  have hyE : yE ≠ 0 := by
    intro hzero
    exact hy.2 (congrArg Subtype.val hzero)
  letI : Nontrivial E := ⟨⟨yE, 0, hyE⟩⟩
  have hEpos : 0 < Module.finrank ℂ E := Module.finrank_pos
  obtain ⟨radius, hR, hRδ, hzero, hcontour, hrange, hstage⟩ :=
    J.compressedOperator_spectralSubspaces_smallCircle_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal
      center hcenter δ hδ
  filter_upwards [hstage] with n hn
  let Sn : Submodule ℂ H :=
    ⨆ μ : ℂ, ⨆ (_ : μ ∈ Metric.ball center radius),
      eigenspace (J.compressedOperator Tn n).toLinearMap μ
  have hSnPos : 0 < Module.finrank ℂ Sn := by
    have hdim : Module.finrank ℂ Sn = Module.finrank ℂ E := by
      simpa [Sn, E] using hn.2
    rw [hdim]
    exact hEpos
  have hexistsBall : ∃ μ : ℂ, μ ∈ Metric.ball center radius ∧
      HasEigenvalue (J.compressedOperator Tn n).toLinearMap μ := by
    by_contra hnone
    push Not at hnone
    have heigenspaceBot : ∀ μ : ℂ, μ ∈ Metric.ball center radius →
        eigenspace (J.compressedOperator Tn n).toLinearMap μ = ⊥ := by
      intro μ hμ
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      by_contra hx0
      exact hnone μ hμ (hasEigenvalue_of_hasEigenvector ⟨hx, hx0⟩)
    have hSnBot : Sn = ⊥ := by
      dsimp [Sn]
      rw [eq_bot_iff]
      apply iSup_le
      intro μ
      apply iSup_le
      intro hμ
      exact (heigenspaceBot μ hμ).le
    have hzeroFinrank : Module.finrank ℂ Sn = 0 := by
      rw [hSnBot]
      simp
    omega
  obtain ⟨μ, hμball, hμEigen⟩ := hexistsBall
  exact ⟨μ, hμEigen, (Metric.mem_ball.mp hμball).trans hRδ⟩

end NCG.VaryingHilbert.System
