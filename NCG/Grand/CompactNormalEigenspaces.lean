/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteDimensionalNormalEigenspaces
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Eigenspaces of compact normal operators

For a compact normal operator `T`, the positive self-adjoint operator `T†T` is compact.  Its
nonzero eigenspaces are finite-dimensional and invariant under both `T` and `T†`; the restriction
of `T` to each such space is normal and hence diagonalizable.  The zero eigenspace of `T†T` is
exactly `ker T`.  Combining these facts with the compact self-adjoint spectral theorem proves
that the eigenspaces of `T` have dense algebraic sum.
-/

open Complex Set Module End

noncomputable section

namespace NCG.NormalSpectrum

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The eigenspaces of a compact normal operator have dense algebraic sum. -/
theorem dense_iSup_eigenspaces_of_compact_of_isStarNormal
    (T : E →L[ℂ] E) (hcompact : IsCompactOperator (T : E → E))
    (hnormal : IsStarNormal T) :
    Dense ((((⨆ μ, eigenspace T.toLinearMap μ) : Submodule ℂ E) : Set E)) := by
  let S : E →L[ℂ] E := ContinuousLinearMap.adjoint T * T
  let G : Submodule ℂ E := ⨆ μ, eigenspace T.toLinearMap μ
  have hnormalEq : ContinuousLinearMap.adjoint T * T =
      T * ContinuousLinearMap.adjoint T := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact ((isStarNormal_iff T).mp hnormal).eq
  have hST : Commute S T := by
    rw [commute_iff_eq]
    dsimp [S]
    rw [← mul_assoc, ← hnormalEq]
  have hSadj : Commute S (ContinuousLinearMap.adjoint T) := by
    rw [commute_iff_eq]
    dsimp [S]
    rw [mul_assoc, hnormalEq]
  have hcompactS : IsCompactOperator (S : E → E) := by
    have hc := hcompact.clm_comp (ContinuousLinearMap.adjoint T)
    have heqfun : (S : E → E) =
        fun x ↦ ContinuousLinearMap.adjoint T (T x) := by
      rfl
    exact heqfun.symm ▸ hc
  have hSsymm : LinearMap.IsSymmetric S.toLinearMap := by
    have hself : IsSelfAdjoint S := by
      dsimp [S]
      exact IsSelfAdjoint.star_mul_self T
    exact hself.isSymmetric
  have hSG : (⨆ μ, eigenspace S.toLinearMap μ) ≤ G := by
    refine iSup_le fun μ ↦ ?_
    by_cases hμ : μ = 0
    · subst μ
      intro x hx
      have hSx : S x = 0 := by
        simpa using (mem_eigenspace_iff.mp hx)
      have hxkerS : x ∈ S.ker := hSx
      have hxkerT : x ∈ T.ker := by
        rw [← ContinuousLinearMap.ker_adjoint_comp_self T]
        simpa [S, ContinuousLinearMap.mul_def] using hxkerS
      apply le_iSup (fun ν ↦ eigenspace T.toLinearMap ν) 0
      simpa [mem_eigenspace_iff] using hxkerT
    · let V : Submodule ℂ E := eigenspace S.toLinearMap μ
      letI : FiniteDimensional ℂ V :=
        ContinuousLinearMap.finite_dimensional_eigenspace hcompactS μ hμ
      have hTinvariant : ∀ x : E, x ∈ V → T x ∈ V := by
        intro x hx
        rw [show V = eigenspace S.toLinearMap μ from rfl,
          mem_eigenspace_iff] at hx ⊢
        calc
          S (T x) = T (S x) := by
            have heq := hST.eq
            exact congrArg (fun A : E →L[ℂ] E ↦ A x) heq
          _ = T (μ • x) := congrArg T hx
          _ = μ • T x := by rw [map_smul]
      have hAdjInvariant : ∀ x : E, x ∈ V →
          ContinuousLinearMap.adjoint T x ∈ V := by
        intro x hx
        rw [show V = eigenspace S.toLinearMap μ from rfl,
          mem_eigenspace_iff] at hx ⊢
        calc
          S (ContinuousLinearMap.adjoint T x) =
              ContinuousLinearMap.adjoint T (S x) := by
            have heq := hSadj.eq
            exact congrArg (fun A : E →L[ℂ] E ↦ A x) heq
          _ = ContinuousLinearMap.adjoint T (μ • x) :=
            congrArg (ContinuousLinearMap.adjoint T) hx
          _ = μ • ContinuousLinearMap.adjoint T x := by rw [map_smul]
      let TV : V →L[ℂ] V := T.restrict hTinvariant
      let TadjV : V →L[ℂ] V :=
        (ContinuousLinearMap.adjoint T).restrict hAdjInvariant
      have hadjTV : ContinuousLinearMap.adjoint TV = TadjV := by
        symm
        apply (ContinuousLinearMap.eq_adjoint_iff TadjV TV).mpr
        intro x y
        simpa [TadjV, TV] using
          (T.adjoint_inner_left (y : E) (x : E))
      have hTVnormal : IsStarNormal TV := by
        apply ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mpr
        intro x
        rw [hadjTV]
        simpa [TV, TadjV] using
          (ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mp hnormal (x : E))
      have hspanV := iSup_eigenspaces_eq_top_of_isStarNormal TV hTVnormal
      intro x hx
      let xv : V := ⟨x, hx⟩
      have hxspan : xv ∈ ⨆ ν, eigenspace TV.toLinearMap ν := by
        rw [hspanV]
        trivial
      refine Submodule.iSup_induction
        (motive := fun y : V ↦ (y : E) ∈ G)
        (fun ν ↦ eigenspace TV.toLinearMap ν) hxspan ?_ ?_ ?_
      · intro ν y hy
        apply le_iSup (fun ξ ↦ eigenspace T.toLinearMap ξ) ν
        rw [mem_eigenspace_iff]
        have hTVy := mem_eigenspace_iff.mp hy
        have hval := congrArg Subtype.val hTVy
        simpa [TV] using hval
      · exact G.zero_mem
      · intro y z hy hz
        exact G.add_mem hy hz
  have horth : (⨆ μ, eigenspace S.toLinearMap μ)ᗮ = ⊥ :=
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
      hcompactS hSsymm
  have hclosure :
      (⨆ μ, eigenspace S.toLinearMap μ : Submodule ℂ E).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, horth]
    exact Submodule.bot_orthogonal_eq_top
  have hdenseS : Dense
      ((((⨆ μ, eigenspace S.toLinearMap μ) : Submodule ℂ E) : Set E)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hclosure
  exact hdenseS.mono hSG

end NCG.NormalSpectrum
