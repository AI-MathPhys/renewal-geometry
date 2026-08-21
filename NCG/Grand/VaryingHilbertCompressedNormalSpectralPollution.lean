/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteSourceGramConvergence
import NCG.Grand.VaryingHilbertCompressedNormalRieszConvergence

/-!
# Exclusion of nonzero spectral pollution for compressed normal operators

Collective compactness turns normalized stage eigenvectors with a convergent nonzero eigenvalue
into a convergent subsequence. Operator-norm convergence then identifies its nonzero limit as a
genuine eigenvector of the limiting compact normal operator.
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

/-- A convergent nonzero sequence of eigenvalues of the literal compressed normal stages cannot
be spectral pollution: its limit is an eigenvalue of the limiting operator. -/
theorem compressedOperator_hasEigenvalue_of_tendsto_nonzero_eigenvalues_of_isStarNormal
    (J : System (K := ℂ) (H := H) (Hn := Hn))
    (Tn : ∀ n, Hn n →L[ℂ] Hn n) (T : H →L[ℂ] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Tn T)
    (hcompact : J.CollectivelyCompact Tn)
    (hnormal : ∀ n, IsStarNormal (Tn n))
    (hlimNormal : IsStarNormal T)
    (μn : ℕ → ℂ) (μ : ℂ) (hμ : Tendsto μn atTop (𝓝 μ)) (hμ0 : μ ≠ 0)
    (x : ℕ → H) (hxnorm : ∀ n, ‖x n‖ = 1)
    (hxeigen : ∀ n,
      J.compressedOperator Tn n (x n) = μn n • x n) :
    HasEigenvalue T.toLinearMap μ := by
  obtain ⟨_, hop⟩ :=
    J.compressedOperator_tendsto_operatorNorm_of_isStarNormal
      Tn T hdense hstrong hcompact hnormal hlimNormal
  have hcompressedCollective := hcompact.compressedOperator J Tn
  obtain ⟨y, φ, hφ, hout⟩ :=
    CollectivelyCompact.tendsto_output_subseq
      (L := constantSystem ℂ H) hcompressedCollective x
      (fun n ↦ (hxnorm n).le)
  have hout' : Tendsto
      (fun k ↦ J.compressedOperator Tn (φ k) (x (φ k)))
      atTop (𝓝 y) := by
    simpa [constantSystem] using hout
  have hφTop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hμsub : Tendsto (fun k ↦ μn (φ k)) atTop (𝓝 μ) := hμ.comp hφTop
  have hinv : Tendsto (fun k ↦ (μn (φ k))⁻¹) atTop (𝓝 μ⁻¹) :=
    hμsub.inv₀ hμ0
  have hμne : ∀ᶠ k in atTop, μn (φ k) ≠ 0 := by
    exact hμsub.eventually (isOpen_compl_singleton.mem_nhds hμ0)
  let xlim : H := μ⁻¹ • y
  have hxsub : Tendsto (fun k ↦ x (φ k)) atTop (𝓝 xlim) := by
    have hscaled : Tendsto
        (fun k ↦ (μn (φ k))⁻¹ •
          J.compressedOperator Tn (φ k) (x (φ k)))
        atTop (𝓝 xlim) := by
      simpa [xlim] using hinv.smul hout'
    apply hscaled.congr'
    filter_upwards [hμne] with k hk
    rw [hxeigen]
    simp [hk]
  have hxlimNorm : ‖xlim‖ = 1 := by
    have hnormSub : Tendsto (fun k ↦ ‖x (φ k)‖) atTop (𝓝 ‖xlim‖) := hxsub.norm
    have hnormOne : Tendsto (fun k : ℕ ↦ ‖x (φ k)‖) atTop (𝓝 1) := by
      simpa only [hxnorm] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
    exact tendsto_nhds_unique hnormSub hnormOne
  have hxlim0 : xlim ≠ 0 := by
    intro hx0
    have : ‖xlim‖ = 0 := by simp [hx0]
    linarith
  have hopSub : Tendsto
      (fun k ↦ J.compressedOperator Tn (φ k)) atTop (𝓝 T) := hop.comp hφTop
  have happly : Tendsto
      (fun k ↦ J.compressedOperator Tn (φ k) (x (φ k)))
      atTop (𝓝 (T xlim)) :=
    NCG.SpectralApproximation.apply_tendsto_of_operatorNorm_tendsto hopSub hxsub
  have hTx : T xlim = y := tendsto_nhds_unique happly hout'
  have hscalar : Tendsto
      (fun k ↦ μn (φ k) • x (φ k)) atTop (𝓝 (μ • xlim)) :=
    hμsub.smul hxsub
  have houtEigen : Tendsto
      (fun k ↦ J.compressedOperator Tn (φ k) (x (φ k)))
      atTop (𝓝 (μ • xlim)) := by
    apply hscalar.congr'
    exact Eventually.of_forall fun k ↦ (hxeigen (φ k)).symm
  have hyEigen : y = μ • xlim := tendsto_nhds_unique hout' houtEigen
  exact hasEigenvalue_of_hasEigenvector
    ⟨mem_eigenspace_iff.mpr (hTx.trans hyEigen), hxlim0⟩

end NCG.VaryingHilbert.System
