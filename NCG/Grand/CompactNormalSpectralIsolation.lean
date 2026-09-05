/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.NormalOperatorEigenspaceOrthogonality
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Isolation of the nonzero spectrum of compact normal operators

For a compact normal operator, every nonzero spectral point is isolated.  The proof restricts to
the orthogonal complement of the chosen eigenspace.  Normality makes this complement reducing,
the restricted operator remains compact and normal, and the Fredholm alternative excludes the
chosen eigenvalue from the restricted spectrum.
-/

open Complex Set Module End

noncomputable section

namespace NCG.ResolventStability

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

set_option maxHeartbeats 800000 in
-- The compact restriction, adjoint identification, and Fredholm instances require extra time.
/-- The nonzero spectrum of a compact normal operator is discrete.  The statement also covers
nonzero resolvent points, whose isolating ball contains no spectral point. -/
theorem exists_isolatedInBall_of_compact_of_isStarNormal
    (T : H →L[ℂ] H) (hcompact : IsCompactOperator (T : H → H))
    (hnormal : IsStarNormal T)
    (μ : ℂ) (hμ : μ ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z ∈ spectrum ℂ T, dist z μ < ε → z = μ := by
  let p : Submodule ℂ H := (eigenspace T.toLinearMap μ)ᗮ
  letI : CompleteSpace p := by
    dsimp [p]
    infer_instance
  have hinv : ∀ x : H, x ∈ p → T x ∈ p := by
    simpa [p] using
      NCG.NormalSpectrum.invariant_orthogonalComplement_eigenspace_of_isStarNormal
        T hnormal μ
  have hinvAdj : ∀ x : H, x ∈ p → ContinuousLinearMap.adjoint T x ∈ p := by
    intro x hx
    change x ∈ (eigenspace T.toLinearMap μ)ᗮ at hx
    change ContinuousLinearMap.adjoint T x ∈ (eigenspace T.toLinearMap μ)ᗮ
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro y hy
    calc
      inner ℂ y (ContinuousLinearMap.adjoint T x) = inner ℂ (T y) x :=
        T.adjoint_inner_right y x
      _ = inner ℂ (μ • y) x :=
        congrArg (fun z ↦ inner ℂ z x) (mem_eigenspace_iff.mp hy)
      _ = 0 := by rw [inner_smul_left, hx y hy, mul_zero]
  let S : p →L[ℂ] p := T.restrict hinv
  let Sadj : p →L[ℂ] p :=
    (ContinuousLinearMap.adjoint T).restrict hinvAdj
  have hadjS : ContinuousLinearMap.adjoint S = Sadj := by
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff Sadj S).mpr
    intro x y
    simpa [S, Sadj] using T.adjoint_inner_left (y : H) (x : H)
  have hnormalS : IsStarNormal S := by
    apply ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mpr
    intro x
    rw [hadjS]
    simpa [S, Sadj] using
      (ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mp hnormal (x : H))
  have hcompactS : IsCompactOperator (S : p → p) := hcompact.restrict' hinv
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
    rw [show p = (eigenspace T.toLinearMap μ)ᗮ from rfl,
      Submodule.mem_orthogonal]
    intro y hy
    exact NCG.NormalSpectrum.inner_eq_zero_of_isStarNormal_of_eigenvectors
      T hnormal (Ne.symm hzμ) (mem_eigenspace_iff.mp hy)
        hxEigen.apply_eq_smul
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
