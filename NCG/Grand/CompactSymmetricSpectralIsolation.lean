/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Isolation of the nonzero spectrum of a compact symmetric operator

For a compact symmetric operator, every nonzero point has a neighborhood containing no spectral
point other than itself.  The proof restricts the operator to the orthogonal complement of the
chosen eigenspace.  Symmetry makes this complement invariant, the restricted operator has no
chosen eigenvalue, and the Fredholm alternative puts that value in the restricted resolvent set.
-/

open Complex Set Module End

noncomputable section

namespace NCG.ResolventStability

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

set_option maxHeartbeats 800000 in
-- The compact restriction and Fredholm instances require additional elaboration heartbeats.
/-- The nonzero spectrum of a compact symmetric operator is discrete.  The statement also covers
nonzero resolvent points: their isolating ball simply contains no spectrum at all. -/
theorem exists_isolatedInBall_of_compact_of_isSymmetric
    (T : H →L[ℂ] H) (hcompact : IsCompactOperator T)
    (hsymm : LinearMap.IsSymmetric T.toLinearMap)
    (μ : ℂ) (hμ : μ ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z ∈ spectrum ℂ T, dist z μ < ε → z = μ := by
  let p : Submodule ℂ H := (eigenspace T.toLinearMap μ)ᗮ
  letI : CompleteSpace p := by
    dsimp [p]
    infer_instance
  have hinv : ∀ x : H, x ∈ p → T x ∈ p := by
    simpa [p] using hsymm.invariant_orthogonalComplement_eigenspace μ
  let S : p →L[ℂ] p := T.restrict hinv
  have hcompactS : IsCompactOperator S := hcompact.restrict' hinv
  have heigBot : eigenspace S.toLinearMap μ = ⊥ := by
    simpa [S, p] using
      eigenspace_restrict_eq_bot (f := T.toLinearMap) hinv
        (eigenspace T.toLinearMap μ).orthogonal_disjoint
  have hnoEigen : ¬ HasEigenvalue S.toLinearMap μ := by
    intro heig
    exact heig heigBot
  have hμResolvent : μ ∈ resolventSet ℂ S :=
    (hcompactS.hasEigenvalue_or_mem_resolventSet hμ).resolve_left hnoEigen
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp (spectrum.isOpen_resolventSet S) μ hμResolvent
  let δ : ℝ := min ε (dist 0 μ)
  have hdistPos : 0 < dist (0 : ℂ) μ := dist_pos.mpr (Ne.symm hμ)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hε hdistPos
  refine ⟨δ, hδ, ?_⟩
  intro z hzSpectrum hzNear
  by_contra hzμ
  have hz : z ≠ 0 := by
    intro hz0
    subst z
    have hδLe : δ ≤ dist (0 : ℂ) μ := by
      dsimp [δ]
      exact min_le_right _ _
    linarith
  have hzNearε : dist z μ < ε :=
    hzNear.trans_le (by
      dsimp [δ]
      exact min_le_left _ _)
  have hzResolventS : z ∈ resolventSet ℂ S :=
    hball (Metric.mem_ball.mpr hzNearε)
  have hzEigen : HasEigenvalue T.toLinearMap z :=
    (hcompact.hasEigenvalue_iff_mem_spectrum hz).mpr hzSpectrum
  obtain ⟨x, hxEigen⟩ := hzEigen.exists_hasEigenvector
  have hxP : x ∈ p := by
    intro y hy
    exact hsymm.orthogonalFamily_eigenspaces (Ne.symm hzμ)
      ⟨y, hy⟩
      ⟨x, mem_eigenspace_iff.mpr hxEigen.apply_eq_smul⟩
  let xp : p := ⟨x, hxP⟩
  have hxp : xp ≠ 0 := by
    intro hxp0
    exact hxEigen.2 (congrArg Subtype.val hxp0)
  have hSxp : S xp = z • xp := by
    apply Subtype.ext
    simpa [S, xp] using hxEigen.apply_eq_smul
  have hzEigenS : HasEigenvalue S.toLinearMap z :=
    hasEigenvalue_of_hasEigenvector
      ⟨mem_eigenspace_iff.mpr hSxp, hxp⟩
  have hzSpectrumS : z ∈ spectrum ℂ S :=
    (hcompactS.hasEigenvalue_iff_mem_spectrum hz).mp hzEigenS
  exact hzSpectrumS hzResolventS

end NCG.ResolventStability
