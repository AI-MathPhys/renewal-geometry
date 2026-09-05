/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCompressedEigenvalue
import NCG.Grand.VaryingHilbertCompressedNormalEigenvalueInclusion
import NCG.Grand.VaryingHilbertCompressedNormalSpectralPollution

/-!
# Nonzero spectral exactness for normal varying-Hilbert operators

Collective compactness and normal varying-space convergence give both halves of nonzero spectral
exactness for the original stage operators: every nonzero limiting eigenvalue is approximated by
late stage eigenvalues, and every convergent nonzero stage eigenvalue sequence has a genuine
limiting eigenvalue.
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

/-- Every nonzero eigenvalue of the compact normal limit is approximated by eigenvalues of all
sufficiently late original stage operators. -/
theorem eventually_exists_stage_eigenvalue_near_of_isStarNormal
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
      HasEigenvalue (Tn n).toLinearMap μ ∧ dist μ center < δ := by
  let δ' : ℝ := min δ (dist (0 : ℂ) center / 2)
  have hdist : 0 < dist (0 : ℂ) center := dist_pos.mpr (Ne.symm hcenter)
  have hδ' : 0 < δ' := by
    dsimp [δ']
    exact lt_min hδ (by linarith)
  have hcompressed :=
    J.compressedOperator_eventually_exists_eigenvalue_near_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal
      center hcenter hcenterEigen δ' hδ'
  filter_upwards [hcompressed] with n hn
  obtain ⟨μ, hμCompressed, hμNear⟩ := hn
  have hμ0 : μ ≠ 0 := by
    intro hzero
    subst μ
    have hsmall : dist (0 : ℂ) center < dist (0 : ℂ) center / 2 :=
      hμNear.trans_le (by
        dsimp [δ']
        exact min_le_right _ _)
    linarith
  have hμStage : HasEigenvalue (Tn n).toLinearMap μ :=
    (J.hasEigenvalue_compressedOperator_iff Tn n μ hμ0).mp hμCompressed
  exact ⟨μ, hμStage, hμNear.trans_le (by
    dsimp [δ']
    exact min_le_left _ _)⟩

/-- A convergent nonzero sequence of eigenvalues of the original normal stage operators cannot be
spectral pollution: its limit is an eigenvalue of the limiting operator. -/
theorem hasEigenvalue_of_tendsto_stage_eigenvalues_of_isStarNormal
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (μn : ℕ → ℂ) (μ : ℂ) (hμ : Tendsto μn atTop (𝓝 μ)) (hμ0 : μ ≠ 0)
    (x : ∀ n, Hn n) (hxnorm : ∀ n, ‖x n‖ = 1)
    (hxeigen : ∀ n, Tn n (x n) = μn n • x n) :
    HasEigenvalue T.toLinearMap μ := by
  let xEmbedded : ℕ → H := fun n ↦ J.embedding n (x n)
  have hxEmbeddedNorm : ∀ n, ‖xEmbedded n‖ = 1 := by
    intro n
    simp [xEmbedded, hxnorm n]
  have hxEmbeddedEigen : ∀ n,
      J.compressedOperator Tn n (xEmbedded n) = μn n • xEmbedded n := by
    intro n
    dsimp [xEmbedded]
    rw [J.compressedOperator_embedding, hxeigen, map_smul]
  exact J.compressedOperator_hasEigenvalue_of_tendsto_nonzero_eigenvalues_of_isStarNormal
    Tn T hdense hstrong hcompact hnormal hlimNormal
    μn μ hμ hμ0 xEmbedded hxEmbeddedNorm hxEmbeddedEigen

end NCG.VaryingHilbert.System
